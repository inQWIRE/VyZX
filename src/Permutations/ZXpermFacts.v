Require Import ZXCore.
Require Import StackComposeRules.
Require Import CastRules.
Require Export ZXperm.
Require Export ZXpermSemantics.
Require Import PermutationAutomation.
Require Export PermutationFacts.
Require Export PermutationInstances. 

(* In this file, we develop some tools for showing things are ZXperms and
   prove some specific values of perm_of_zx *)



(* Section on very general ZXperm facts *)

Local Open Scope nat.

Lemma zxperm_iff_cast {n0 n1 m0 m1} {zx} (Hn : n1 = n0) (Hm : m1 = m0) :
	ZXperm n1 m1 (cast _ _ Hn Hm zx) <-> ZXperm n0 m0 zx.
Proof.
	split; intros; subst; easy.
Qed.

Global Hint Resolve <- zxperm_iff_cast : zxperm_db.

Lemma cast_stack_zxperm {n0 n1 m0 m1 o p} {zx0} {zx1}
	(H0 : ZXperm n0 m0 zx0) (H1 : ZXperm n1 m1 zx1) 
	(Hn : o = n0 + n1) (Hm : p = m0 + m1) :
	ZXperm o p (cast _ _ Hn Hm (zx0 ↕ zx1)).
Proof.
  auto with zxperm_db.
Qed.

Global Hint Resolve cast_stack_zxperm : zxperm_db.

Lemma transpose_zxperm {n m} {zx} (H : ZXperm n m zx) :
	ZXperm m n (zx ⊤).
Proof.
	induction H; simpl; constructor; try easy.
Qed.

Global Hint Resolve transpose_zxperm : zxperm_db.



(* Section on core ZXperms *)
Lemma n_wire_zxperm {n} : 
	ZXperm n n (n_wire n).
Proof.
	induction n.
	- constructor.
	- simpl.
    apply (PermStack PermWire IHn).
Qed.

Global Hint Resolve n_wire_zxperm : zxperm_db.

Lemma n_compose_zxperm {n} {zx} (H : ZXperm n n zx) k :
	ZXperm _ _ (n_compose k zx).
Proof.
	induction k; simpl; auto with zxperm_db.
Qed.

Global Hint Resolve n_compose_zxperm : zxperm_db.



(* Section on specific ZXperms *)
Lemma top_to_bottom_helper_zxperm n :
	ZXperm (S n) (S n) (top_to_bottom_helper n).
Proof.
	induction n.
	- constructor.
	- simpl.
	  constructor.
	  + apply (PermStack PermSwap n_wire_zxperm).
	  + apply (PermStack PermWire IHn).
Qed.

Global Hint Resolve top_to_bottom_helper_zxperm : zxperm_db.

Lemma top_to_bottom_zxperm {n} :
	ZXperm n n (top_to_bottom n).
Proof.
	destruct n; simpl; auto with zxperm_db.
Qed.

Lemma bottom_to_top_zxperm {n} :
	ZXperm n n (bottom_to_top n).
Proof.
	apply transpose_zxperm.
	apply top_to_bottom_zxperm.
Qed.

Global Hint Resolve top_to_bottom_zxperm bottom_to_top_zxperm : zxperm_db.


















(* Section on rules for perm_of_zx *)
Lemma perm_of_zx_WF {n m} {zx} (H : ZXperm n m zx) : forall k, 
	n <= k -> (perm_of_zx zx) k = k.
Proof.
	induction H; intros k Hk; try easy.
	- simpl.
	  destruct k; [|destruct k]; cbn; lia.
	- simpl. 
	  rewrite stack_perms_high; easy.
	- simpl.
	  unfold compose.
	  pose proof (zxperm_square H).
	  rewrite IHZXperm1; rewrite IHZXperm2; lia.
	Qed.

Global Hint Resolve perm_of_zx_WF : perm_WF_db.

Lemma stack_perms_zx_idn {n0 m0 n1} {zx} (H : ZXperm n0 m0 zx) :
	stack_perms n0 n1 (perm_of_zx zx) idn = 
	perm_of_zx zx.
Proof.
	apply stack_perms_WF_idn.
  auto with perm_WF_db.
Qed.

#[export] Hint Rewrite @stack_perms_zx_idn : perm_of_zx_cleanup_db.

Lemma stack_perms_idn_zx {n0 n1 m1} {zx} (H : ZXperm n1 m1 zx) :
	stack_perms n0 n1 idn (perm_of_zx zx) = 
	fun k => if k <? n0 then k else (perm_of_zx zx (k - n0)) + n0.
Proof.
	solve_stack_perm n0 n1.
	rewrite perm_of_zx_WF; [lia|easy|lia].
Qed.

Lemma perm_of_zx_compose_spec {n m o} {zx0 : ZX n m} {zx1 : ZX m o} :
	perm_of_zx (zx0 ⟷ zx1) = 
	(perm_of_zx zx0 ∘ perm_of_zx zx1)%prg.
Proof. easy. Qed.

Lemma perm_of_zx_stack_spec {n m o p} {zx0 : ZX n m} {zx1 : ZX o p} :
	perm_of_zx (zx0 ↕ zx1) = 
	stack_perms n o (perm_of_zx zx0) (perm_of_zx zx1).
Proof. easy. Qed.

Lemma perm_of_zx_cast {n m n' m'} {zx : ZX n' m'} 
  (Hn : n = n') (Hm : m = m') :
  perm_of_zx (cast _ _ Hn Hm zx) = perm_of_zx zx.
Proof. subst. easy. Qed.

#[export] Hint Rewrite 
  @perm_of_zx_compose_spec
  @perm_of_zx_stack_spec
  @perm_of_zx_cast : perm_of_zx_cleanup_db.

Lemma perm_of_transpose_is_rinv {n m} {zx} (H : ZXperm n m zx) :
	(perm_of_zx zx ∘ perm_of_zx zx⊤)%prg = idn.
Proof.
	rewrite <- perm_of_zx_compose_spec.
	induction H; apply functional_extensionality; intros k; try easy.
	- cbn. 
	  destruct k; [easy|destruct k; [easy|]].
	  rewrite swap_2_perm_WF; rewrite swap_2_perm_WF; lia.
	- simpl.
    pose proof (zxperm_square H).
    pose proof (zxperm_square H0).
    subst.
	  rewrite stack_perms_compose.
	  2,3: auto with perm_db zxperm_db.
	  rewrite <- 2!perm_of_zx_compose_spec.
	  rewrite IHZXperm1, IHZXperm2; cleanup_perm.
    easy.
	- rewrite 2!perm_of_zx_compose_spec.
	  simpl.
	  rewrite <- Combinators.compose_assoc,
	  	(Combinators.compose_assoc _ _ _ _ (perm_of_zx zx1 ⊤)).
	  rewrite <- perm_of_zx_compose_spec, IHZXperm2, compose_idn_r.
	  rewrite <- perm_of_zx_compose_spec, IHZXperm1.
	  easy.
Qed.

Lemma perm_of_transpose_is_linv {n m} {zx} (H : ZXperm n m zx) :
	(perm_of_zx zx⊤ ∘ perm_of_zx zx)%prg = idn.
Proof.
	pose proof (perm_of_transpose_is_rinv (transpose_zxperm H)) as Hinv.
	rewrite <- transpose_involutive_eq in Hinv.
	easy.
Qed.

#[export] Hint Rewrite 
  @perm_of_transpose_is_rinv 
  @perm_of_transpose_is_linv : perm_of_zx_cleanup_db.



(* Section on specific values of perm_of_zx *)

Lemma perm_of_n_wire n :
	perm_of_zx (n_wire n) = idn.
Proof.
	induction n.
	- easy.
	- simpl.
	  rewrite IHn.
	  rewrite stack_perms_idn_idn.
	  easy.
Qed.

#[export] Hint Rewrite perm_of_n_wire : perm_of_zx_cleanup_db.

Lemma perm_of_zx_stack_n_wire {n0 m0} {zx} (H : ZXperm n0 m0 zx) {n1} :
	perm_of_zx (zx ↕ (n_wire n1)) = perm_of_zx zx.
Proof.
	simpl.
	rewrite perm_of_n_wire.
	rewrite (stack_perms_zx_idn H).
	easy. 
Qed.

#[export] Hint Rewrite @perm_of_zx_stack_n_wire : perm_of_zx_cleanup_db.

Lemma perm_of_top_to_bottom_helper_eq {n} :
	perm_of_zx (top_to_bottom_helper n) = top_to_bottom_perm (S n).
Proof.
	strong induction n; 
	apply functional_extensionality; intros k.
	destruct n; [destruct k; easy|].
	simpl.
	rewrite perm_of_n_wire.
	rewrite stack_perms_WF_idn; [|apply swap_2_perm_WF].
	rewrite stack_perms_idn_zx; [|apply top_to_bottom_helper_zxperm].
	rewrite H; [|auto].
	unfold compose.
	bdestruct (k <? 1). 
	- replace k with 0 by lia. easy.
	- destruct n.
	  1: destruct k; [easy|];
	     destruct k; [easy|];
		   cbn; destruct (k + 1) eqn:e; 
       unfold swap_2_perm; destruct_if_solve.
	  destruct k; [lia|].
	  replace (S k - 1) with k by lia.
	  unfold top_to_bottom_perm.
	  replace (S (S (S n)) <=? S k) with (S (S n) <=? k) by bdestshoweq.
	  replace (S k =? S (S (S n)) - 1) with (k =? S (S n) - 1) by bdestshoweq.
	  bdestruct (S (S n) <=? k).
	  + rewrite swap_2_perm_WF; lia.
	  + bdestruct (k =? S (S n) - 1); [easy|].
	    rewrite swap_2_perm_WF; lia.
Qed.

#[export] Hint Rewrite @perm_of_top_to_bottom_helper_eq : perm_of_zx_cleanup_db.

Lemma perm_of_top_to_bottom_eq {n} :
	perm_of_zx (top_to_bottom n) = top_to_bottom_perm n.
Proof.
	destruct n.
	- apply functional_extensionality; intros k.
	  easy.
	- simpl.
	  rewrite perm_of_top_to_bottom_helper_eq.
	  easy.
Qed.

#[export] Hint Rewrite @perm_of_top_to_bottom_eq : perm_of_zx_cleanup_db.

Lemma perm_of_bottom_to_top_eq n :
	perm_of_zx (bottom_to_top n) = bottom_to_top_perm n.
Proof.
  by_inverse_injective (top_to_bottom_perm n) n.
  rewrite <- perm_of_top_to_bottom_eq.
	unfold bottom_to_top.
  apply perm_of_transpose_is_linv; auto with zxperm_db.
Qed.

#[export] Hint Rewrite perm_of_bottom_to_top_eq : perm_of_zx_cleanup_db.

Lemma perm_of_kcompose_top_to_bot_eq_rotr n k :
	perm_of_zx (n_compose k (top_to_bottom n)) =
	rotr n k.
Proof.
	induction k; simpl; try rewrite IHk; cleanup_perm_of_zx; easy.
Qed.

Lemma perm_of_kcompose_bot_to_top_eq_rotl n k :
	perm_of_zx (n_compose k (bottom_to_top n)) =
	rotl n k.
Proof.
	induction k; simpl; try rewrite IHk; cleanup_perm_of_zx; easy.
Qed.

#[export] Hint Rewrite 
  perm_of_kcompose_top_to_bot_eq_rotr
  perm_of_kcompose_bot_to_top_eq_rotl : perm_of_zx_cleanup_db.

(* We can prove the rest (and really, whatever we want) easily. 
   The main results are secitoned here so they don't overlap 
   with the (same) proofs in SwapRules.v *)

Lemma perm_of_top_to_bottom_1 n :
	perm_of_zx (top_to_bottom (S n)) = perm_of_zx (n_compose n (bottom_to_top (S n))).
Proof.
  cleanup_perm_of_zx.
	destruct n; [rewrite rotr_n, rotl_0_r; easy|].
	rewrite rotr_eq_rotl_sub.
	rewrite Nat.mod_small; [f_equal|]; lia.
Qed.

Lemma perm_of_n_compose_n_top_to_bottom n :
	perm_of_zx (n_compose n (top_to_bottom n)) = perm_of_zx (n_wire n).
Proof.
	cleanup_perm_of_zx.
	easy.
Qed.

#[export] Hint Rewrite perm_of_n_compose_n_top_to_bottom : perm_of_zx_cleanup_db.

Local Close Scope nat.
