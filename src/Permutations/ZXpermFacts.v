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

(* FIXME: Temporary for working only *)
Definition a_perm (n : nat) : nat -> nat :=
  swap_perm 0 (n-1) n.

Lemma a_swap_zxperm n : 
	ZXperm n n (bottom_to_top n).
Proof.
	induction n; auto with zxperm_db.
Qed.
















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



(* FIXME: This doesn't go here: *)
(* Definition n_top_to_bottom (n m : nat) : ZX (n + m) (n + m) :=
  n_compose n (top_to_bottom (n + m)). *)

Lemma mod_add_n_r : forall m n, 
	(m + n) mod n = m mod n.
Proof.
	intros m n.
	replace (m + n) with (m + 1 * n) by lia.
	destruct n.
	- cbn; easy.
	- rewrite Nat.mod_add;
		lia.
Qed.

Lemma mod_eq_sub : forall m n,
	m mod n = m - n * (m / n).
Proof.
	intros m n.
	destruct n.
	- cbn; lia.
	- assert (H: S n <> 0) by easy.
		pose proof (Nat.div_mod m (S n) H) as Heq.
		lia.
Qed.

Lemma mod_of_scale : forall m n q, 
	n * q <= m < n * S q -> m mod n = m - q * n.
Proof.
	intros m n q [Hmq HmSq].
	rewrite mod_eq_sub.
	replace (m/n) with q; [lia|].
	apply Nat.le_antisymm.
	- apply Nat.div_le_lower_bound; lia. 
	- epose proof (Nat.div_lt_upper_bound m n (S q) _ _).
		lia.
		Unshelve.
		all: lia.
Qed.

Lemma mod_n_to_2n : forall m n, 
	n <= m < 2 * n -> m mod n = m - n.
Proof.
	intros.
	epose proof (mod_of_scale m n 1 _).
	lia.
	Unshelve.
	lia.
Qed.

Lemma mod_n_to_n_plus_n : forall m n, 
	n <= m < n + n -> m mod n = m - n.
Proof.
	intros.
	apply mod_n_to_2n; lia.
Qed.

Ltac fail_if_has_mods a :=
	match a with
	| context[_ mod _] => fail 1
	| _ => idtac
	end.

Ltac simplify_mods_of a b :=
	first [
		rewrite (Nat.mod_small a b) in * by lia
	| rewrite (mod_n_to_2n a b) in * by lia
	].

Ltac solve_simple_mod_eqns :=
	match goal with
	| |- context[if _ then _ else _] => fail 1 "Cannot solve equation with if"
	| _ =>
		repeat first [
			lia
		|	match goal with 
			| |- context[?a mod ?b] => fail_if_has_mods a; fail_if_has_mods b; 
					simplify_mods_of a b
			| H: context[?a mod ?b] |- _ => fail_if_has_mods a; fail_if_has_mods b; 
					simplify_mods_of a b
			end 
		| match goal with
			| |- context[?a mod ?b] => (* idtac a b; *) bdestruct (a <? b);
					[rewrite (Nat.mod_small a b) by lia 
					| try rewrite (mod_n_to_2n a b) by lia]
			end
		]
	end.

Lemma hexagon_lemma_1_helper : forall {n m o o'} prf1 prf2 prf3 prf4,
	n_top_to_bottom n m ↕ n_wire o 
	⟷ cast (n + m + o) o' prf1 prf2 (n_wire m ↕ n_top_to_bottom n o)
	∝ cast (n + m + o) o' prf3 prf4 (n_top_to_bottom n (m + o)).
Proof.
	intros. unfold n_top_to_bottom. subst.
	apply prop_of_equal_perm.
	all: auto with zxperm_db.
	cleanup_perm_of_zx; auto with zxperm_db.
	rewrite stack_perms_idn_f.
	unfold compose, rotr.
	apply functional_extensionality; intros k.
	bdestruct_all; simpl in *; try lia.
	all: solve_simple_mod_eqns.
Qed.



Lemma perm_of_a_swap n : 
	perm_of_zx (a_swap n) = a_perm n.
Proof.
	destruct n; [cleanup_perm; easy|].
	simpl.
	cleanup_perm_of_zx.
	unfold compose, a_perm.
	replace (S n - 1) with n by lia.
	unfold swap_perm.
	apply functional_extensionality.
	intros k.
	bdestruct_all.
	- rewrite stack_perms_WF; [|lia].
		auto with perm_WF_db.
	- rewrite stack_perms_left; [|lia].
		unfold rotl.
		bdestruct_all; solve_simple_mod_eqns.
	- subst.
		rewrite stack_perms_right; [|lia].
		unfold rotr, rotl.
		bdestruct_all; solve_simple_mod_eqns.
	- rewrite stack_perms_right; [|lia].
		unfold rotr, rotl.
		bdestruct_all; solve_simple_mod_eqns.
Qed.


Local Close Scope nat.
