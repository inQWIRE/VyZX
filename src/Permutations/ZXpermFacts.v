Require Import ZXCore.
Require Import StackComposeRules.
Require Import CastRules.
Require Export ZXperm.
Require Import PermutationAutomation.
Require Import PermutationSemantics. 
Require Export PermutationInstances. 
Require Export PermutationFacts.
Require Export ZXpermSemantics.

(* In this file, we develop some tools for showing things are ZXperms and
   prove some specific values of perm_of_zx *)

(* Now that we have facts about insertion_sort_list, we can define: *)

Definition zx_of_perm n f :=
	cast n n 
		(eq_sym (length_insertion_sort_list n (perm_inv n f))) 
		(eq_sym (length_insertion_sort_list n (perm_inv n f)))
	(zx_of_perm_uncast n f).

(* Section on very general ZXperm facts *)

Local Open Scope nat.
Local Open Scope ZX_scope.

Lemma zxperm_iff_cast {n0 n1} {zx} (Hn Hn' : n1 = n0) :
	ZXperm n1 (cast _ _ Hn Hn' zx) <-> ZXperm n0 zx.
Proof.
	split; intros; subst;
	rewrite cast_id_eq in *; easy.
Qed.

#[export] Hint Resolve <- zxperm_iff_cast : zxperm_db.

Lemma cast_stack_zxperm {n0 n1 o} {zx0} {zx1}
	(H0 : ZXperm n0 zx0) (H1 : ZXperm n1 zx1) 
	(Hn Hn' : o = n0 + n1) :
	ZXperm o (cast _ _ Hn Hn' (zx0 ↕ zx1)).
Proof.
  auto with zxperm_db.
Qed.

#[export] Hint Resolve cast_stack_zxperm : zxperm_db.

Lemma conjugate_zxperm {n} {zx} (H : ZXperm n zx) :
  ZXperm n (zx ⊼).
Proof.
	induction H; simpl; constructor; easy.
Qed.

#[export] Hint Resolve conjugate_zxperm : zxperm_db.

Lemma transpose_zxperm {n} {zx} (H : ZXperm n zx) :
	ZXperm n (zx ⊤).
Proof.
	induction H; simpl; constructor; easy.
Qed.

#[export] Hint Resolve transpose_zxperm : zxperm_db.

Lemma adjoint_zxperm {n} {zx} (H : ZXperm n zx) :
	ZXperm n (zx †).
Proof.
	induction H; simpl; constructor; easy.
Qed.

#[export] Hint Resolve adjoint_zxperm : zxperm_db.

Lemma colorswap_zxperm {n} {zx} (H : ZXperm n zx) :
	ZXperm n (⊙ zx).
Proof.
	induction H; simpl; constructor; easy.
Qed.

#[export] Hint Resolve colorswap_zxperm : zxperm_db.

(* Section on core ZXperms *)
Lemma n_wire_zxperm {n} : 
	ZXperm n (n_wire n).
Proof.
	induction n; simpl; auto with zxperm_db.
Qed.

#[export] Hint Resolve n_wire_zxperm : zxperm_db.

(* Lemma n_compose_zxperm {n} {zx} (H : ZXperm n zx) k :
	ZXperm _ (n_compose k zx).
Proof.
	induction k; simpl; auto with zxperm_db.
Qed.

#[export] Hint Resolve n_compose_zxperm : zxperm_db. *)



(* Section on specific ZXperms *)
Lemma top_to_bottom_helper_zxperm n :
	ZXperm (S n) (top_to_bottom_helper n).
Proof.
	induction n.
	- constructor.
	- simpl.
	  constructor.
	  + apply (PermStack PermSwap n_wire_zxperm).
	  + apply (PermStack PermWire IHn).
Qed.

#[export] Hint Resolve top_to_bottom_helper_zxperm : zxperm_db.

Lemma top_to_bottom_zxperm {n} :
	ZXperm n (top_to_bottom n).
Proof.
	destruct n; simpl; auto with zxperm_db.
Qed.

Lemma bottom_to_top_zxperm {n} :
	ZXperm n (bottom_to_top n).
Proof.
	apply transpose_zxperm.
	apply top_to_bottom_zxperm.
Qed.

#[export] Hint Resolve top_to_bottom_zxperm bottom_to_top_zxperm : zxperm_db.

(* Lemma n_top_to_bottom_zxperm : forall n m,
    ZXperm _ (n_top_to_bottom n m).
Proof.
    unfold n_top_to_bottom.
    auto with zxperm_db.
Qed.

Lemma n_bottom_to_top_zxperm : forall n m,
    ZXperm _ (n_bottom_to_top n m).
Proof.
    unfold n_bottom_to_top.
    auto with zxperm_db.
Qed.

#[export] Hint Resolve n_top_to_bottom_zxperm n_bottom_to_top_zxperm : zxperm_db. *)

Lemma a_swap_zxperm n : 
	ZXperm n (a_swap n).
Proof.
	induction n; simpl; auto with zxperm_db.
Qed.

#[export] Hint Resolve a_swap_zxperm : zxperm_db.







(* Section on rules for perm_of_zx *)
Lemma perm_of_zx_WF {n} {zx} (H : ZXperm n zx) : 
	WF_Perm n (perm_of_zx zx).
Proof.
	induction H; intros k Hk; try easy.
	- simpl.
	  destruct k; [|destruct k]; cbn; lia.
	- simpl. 
	  rewrite stack_perms_high; easy.
	- simpl.
	  unfold compose.
	  rewrite IHZXperm1; rewrite IHZXperm2; lia.
Qed.

#[export] Hint Resolve perm_of_zx_WF : WF_Perm_db.

Lemma stack_perms_zx_idn {n0 n1} {zx} (H : ZXperm n0 zx) :
	stack_perms n0 n1 (perm_of_zx zx) idn = 
	perm_of_zx zx.
Proof.
	apply stack_perms_WF_idn.
  auto with WF_Perm_db.
Qed.

#[export] Hint Rewrite @stack_perms_zx_idn using (auto with zxperm_db) : perm_of_zx_cleanup_db.

Lemma stack_perms_idn_zx {n0 n1} {zx} (H : ZXperm n1 zx) :
	stack_perms n0 n1 idn (perm_of_zx zx) = 
	fun k => if k <? n0 then k else (perm_of_zx zx (k - n0)) + n0.
Proof.
	solve_modular_permutation_equalities.
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

Lemma perm_of_zx_transpose {n} {zx} (Hzx : ZXperm n zx) :
	perm_of_zx (zx ⊤) = perm_inv' n (perm_of_zx zx).
Proof.
	induction Hzx; [simpl; cleanup_perm_inv..| |];
	simpl;
	cleanup_perm_inv;
	now f_equal.
Qed.

#[export] Hint Rewrite @perm_of_zx_transpose 
	using auto with zxperm_db : perm_of_zx_cleanup_db.





Lemma perm_of_transpose_is_rinv {n} {zx} (H : ZXperm n zx) :
	(perm_of_zx zx ∘ perm_of_zx zx⊤)%prg = idn.
Proof.
	cleanup_perm_of_zx.
Qed.

Lemma perm_of_transpose_is_linv {n} {zx} (H : ZXperm n zx) :
	(perm_of_zx zx⊤ ∘ perm_of_zx zx)%prg = idn.
Proof.
	cleanup_perm_of_zx.
Qed.

#[export] Hint Rewrite 
  @perm_of_transpose_is_rinv 
  @perm_of_transpose_is_linv 
	using (auto with zxperm_db) : perm_of_zx_cleanup_db.

Lemma perm_of_conjugate {n m} (zx : ZX n m) :
	perm_of_zx (zx ⊼) = perm_of_zx zx.
Proof.
	induction zx; simpl; try easy.
	- rewrite IHzx1, IHzx2; easy.
	- rewrite IHzx1, IHzx2; easy.
Qed.

#[export] Hint Rewrite @perm_of_conjugate : perm_of_zx_cleanup_db.

Lemma perm_of_adjoint_eq_transpose {n} {zx} (H : ZXperm n zx) :
	perm_of_zx (zx †) = perm_of_zx (zx ⊤).
Proof.
	unfold adjoint.
	cleanup_perm_of_zx.
Qed.

Lemma perm_of_adjoint {n} {zx} (H : ZXperm n zx) :
	perm_of_zx (zx †) = perm_inv' n (perm_of_zx zx).
Proof.
	unfold adjoint.
	cleanup_perm_of_zx.
Qed.

#[export] Hint Rewrite @perm_of_adjoint 
	using (auto with zxperm_db) : perm_of_zx_cleanup_db.



(* Section on specific values of perm_of_zx *)

Lemma perm_of_n_wire n :
	perm_of_zx (n_wire n) = idn.
Proof.
	induction n; simpl; 
	rewrite ?IHn; cleanup_perm_of_zx.
Qed.

#[export] Hint Rewrite perm_of_n_wire : perm_of_zx_cleanup_db.

Lemma perm_of_zx_stack_n_wire_alt {n0} {zx} (H : ZXperm n0 zx) {n1} :
	perm_of_zx (zx ↕ (n_wire n1)) = perm_of_zx zx.
Proof.
	simpl.
	rewrite perm_of_n_wire.
	rewrite (stack_perms_zx_idn H).
	easy. 
Qed.

Lemma perm_of_zx_stack_n_wire {n0} {zx} (H : ZXperm n0 zx) {n1} :
	perm_of_zx (zx ↕ (n_wire n1)) = 
	stack_perms n0 n1 (perm_of_zx zx) (idn).
Proof.
	simpl.
	now rewrite perm_of_n_wire.
Qed.

#[export] Hint Rewrite @perm_of_zx_stack_n_wire 
	using (auto with zxperm_db) : perm_of_zx_cleanup_db.

Lemma perm_of_top_to_bottom_helper_eq {n} :
	perm_of_zx (top_to_bottom_helper n) = top_to_bottom_perm (S n).
Proof.
	induction n; 
	[eq_by_WF_perm_eq 1; intros []; easy |].
	simpl.
	cleanup_perm_of_zx.
	rewrite stack_perms_idn_zx by auto with zxperm_db.
	unfold swap_2_perm.
	rewrite IHn.
	solve_modular_permutation_equalities.
Qed.

#[export] Hint Rewrite @perm_of_top_to_bottom_helper_eq : perm_of_zx_cleanup_db.

Lemma perm_of_top_to_bottom_eq {n} :
	perm_of_zx (top_to_bottom n) = top_to_bottom_perm n.
Proof.
	destruct n; cleanup_perm_of_zx.
Qed.

#[export] Hint Rewrite @perm_of_top_to_bottom_eq : perm_of_zx_cleanup_db.

Lemma perm_of_bottom_to_top_eq n :
	perm_of_zx (bottom_to_top n) = bottom_to_top_perm n.
Proof.
  permutation_eq_by_WF_inv_inj (top_to_bottom_perm n) n.
  rewrite <- perm_of_top_to_bottom_eq.
	unfold bottom_to_top.
	cleanup_perm_of_zx.
Qed.

#[export] Hint Rewrite perm_of_bottom_to_top_eq : perm_of_zx_cleanup_db.

(* Lemma perm_of_kcompose_top_to_bot_eq_rotr n k :
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

Lemma perm_of_top_to_bottom_1 n :
	perm_of_zx (top_to_bottom (S n)) = perm_of_zx (n_compose n (bottom_to_top (S n))).
Proof.
  cleanup_perm_of_zx.
	destruct n; [rewrite rotr_n, rotl_0_r; easy|].
	rewrite rotr_eq_rotl_sub.
	rewrite Nat.mod_small; [f_equal|]; lia.
Qed.

Lemma perm_of_n_compose_top_to_bottom_n n :
	perm_of_zx (n_compose n (top_to_bottom n)) = perm_of_zx (n_wire n).
Proof.
	cleanup_perm_of_zx.
	easy.
Qed.

#[export] Hint Rewrite perm_of_n_compose_top_to_bottom_n : perm_of_zx_cleanup_db.

Lemma perm_of_n_top_to_bottom : forall n m,
    perm_of_zx (n_top_to_bottom n m) = rotr (n + m) n.
Proof.
    intros.
    unfold n_top_to_bottom.
    cleanup_perm_of_zx; easy.
Qed.

Lemma perm_of_n_bottom_to_top : forall n m,
    perm_of_zx (n_bottom_to_top n m) = rotl (m + n) n.
Proof.
    intros.
    unfold n_bottom_to_top.
    cleanup_perm_of_zx; easy.
Qed.

#[export] Hint Rewrite perm_of_n_top_to_bottom perm_of_n_bottom_to_top : perm_of_zx_cleanup_db. *)

(* Section on constructing ZX diagrams of arbitrary permutations *)

Lemma perm_of_a_swap n : 
	perm_of_zx (a_swap n) = swap_perm 0 (n - 1) n.
Proof.
	destruct n; [cleanup_perm; easy|].
	simpl.
	solve_modular_permutation_equalities.
Qed.

#[export] Hint Rewrite perm_of_a_swap : perm_of_zx_cleanup_db.

Lemma zx_to_bot_zxperm a n :
	ZXperm n (zx_to_bot a n).
Proof.
	unfold zx_to_bot.
	auto with zxperm_db.
Qed.

Lemma zx_to_bot'_zxperm a n H :
	ZXperm n (zx_to_bot' a n H).
Proof.
	unfold zx_to_bot'.
	auto with zxperm_db.
Qed.

#[export] Hint Resolve zx_to_bot_zxperm zx_to_bot'_zxperm : zxperm_db.

Lemma perm_of_zx_to_bot a n :
	perm_of_zx (zx_to_bot a n) = swap_perm (min a n) (min a n + (n - a - 1)) n.
Proof.
	unfold zx_to_bot.
	cleanup_perm_of_zx.
	solve_modular_permutation_equalities.
Qed.

Lemma perm_of_zx_to_bot' a n H :
	perm_of_zx (zx_to_bot' a n H) = swap_perm a (n - 1) n.
Proof.
	unfold zx_to_bot'.
	cleanup_perm_of_zx.
	solve_modular_permutation_equalities.
Qed.

#[export] Hint Rewrite perm_of_zx_to_bot' : perm_of_zx_cleanup_db.

Lemma perm_of_zx_to_bot_eq_zx_to_bot' a n (H: a < n) :
	perm_of_zx (zx_to_bot a n) = perm_of_zx (zx_to_bot' a n H).
Proof.
	cleanup_perm_of_zx; rewrite perm_of_zx_to_bot.
	solve_modular_permutation_equalities.
Qed.

(* #[export] Hint Rewrite perm_of_zx_to_bot_eq_zx_to_bot' : perm_of_zx_cleanup_db. *)

Lemma zx_to_bot_propto_zx_to_bot' {a n} H : 
	zx_to_bot a n ∝ zx_to_bot' a n H.
Proof.
	prop_perm_eq.
	rewrite (perm_of_zx_to_bot_eq_zx_to_bot' _ _ H).
	cleanup_perm_of_zx.
Qed.

Lemma zx_of_swap_list_zxperm l :
	ZXperm (length l) (zx_of_swap_list l).
Proof.
	induction l; simpl; auto with zxperm_db.
Qed.

#[export] Hint Resolve zx_of_swap_list_zxperm : zxperm_db.

Lemma perm_of_zx_of_swap_list l : swap_list_spec l = true ->
	perm_of_zx (zx_of_swap_list l) = perm_of_swap_list l.
Proof.
	induction l.
	- easy.
	- simpl swap_list_spec.
		rewrite andb_true_iff, Nat.ltb_lt.
		intros [Ha Hspec].
		specialize (IHl Hspec).
		simpl.
		f_equal.
		+ rewrite (perm_of_zx_to_bot_eq_zx_to_bot' _ _ Ha).
			cleanup_perm_of_zx.
			f_equal; lia.
		+ cleanup_perm_of_zx.
Qed.

#[export] Hint Rewrite perm_of_zx_of_swap_list 
	using auto with perm_db : perm_of_zx_cleanup_db.

Lemma perm_of_zx_uncast_of_perm_eq n f : permutation n f ->
	perm_eq n (perm_of_zx (zx_of_perm_uncast n f)) f.
Proof.
	intros Hperm.
	cleanup_perm_of_zx.
Qed.

#[export] Hint Resolve perm_of_zx_uncast_of_perm_eq : perm_inv_db.

Lemma perm_of_zx_uncast_of_perm_eq_WF n f : 
	permutation n f -> WF_Perm n f ->
	perm_of_zx (zx_of_perm_uncast n f) = f.
Proof.
	intros Hperm HWF.
	cleanup_perm_of_zx.
Qed.

#[export] Hint Rewrite perm_of_zx_uncast_of_perm_eq_WF
	using (solve [auto with perm_db WF_Perm_db]) : perm_of_zx_cleanup_db.

Lemma perm_of_zx_of_perm_eq n f : permutation n f -> 
	perm_eq n (perm_of_zx (zx_of_perm n f)) f.
Proof.
	intros Hperm.
	unfold zx_of_perm.
	cleanup_perm_of_zx.
Qed.

#[export] Hint Resolve perm_of_zx_of_perm_eq : perm_inv_db.

Lemma perm_of_zx_of_perm_eq_WF n f : 
	permutation n f -> WF_Perm n f ->
	perm_of_zx (zx_of_perm n f) = f.
Proof.
	intros Hperm HWF.
	unfold zx_of_perm.
	cleanup_perm_of_zx.
Qed.

#[export] Hint Rewrite perm_of_zx_of_perm_eq_WF
	using (solve [auto with perm_db WF_Perm_db]) : perm_of_zx_cleanup_db.

Lemma zx_of_perm_zxperm n f : 
	ZXperm n (zx_of_perm n f).
Proof.
	unfold zx_of_perm.
	auto with zxperm_db.
Qed.

#[export] Hint Resolve zx_of_perm_zxperm : zxperm_db.

Lemma zx_of_perm_of_zx {n zx} (H : ZXperm n zx) : 
	zx_of_perm n (perm_of_zx zx) ∝ zx.
Proof.
	by_perm_eq.
Qed.

#[export] Hint Rewrite @zx_of_perm_of_zx 
	using auto with zxperm_db : perm_of_zx_cleanup_db.

Lemma perm_of_zx_perm_eq_of_proportional {n} {zx0 zx1 : ZX n n} 
	(Hzx0 : ZXperm n zx0) (Hzx1 : ZXperm n zx1) : 
	zx0 ∝ zx1 ->
	perm_eq n (perm_of_zx zx0) (perm_of_zx zx1).
Proof.
	unfold proportional, proportional_general.
	rewrite (perm_of_zx_permutation_semantics Hzx0).
	rewrite (perm_of_zx_permutation_semantics Hzx1).
	intros H.
	apply perm_to_matrix_perm_eq_of_proportional; 
	cleanup_perm_inv.
Qed.

Lemma perm_of_zx_proper {n} {zx0 zx1 : ZX n n} 
	(Hzx0 : ZXperm n zx0) (Hzx1 : ZXperm n zx1) : 
	zx0 ∝ zx1 ->
	perm_of_zx zx0 = perm_of_zx zx1.
Proof.
	intros Hprop.
	eq_by_WF_perm_eq n.
	now apply perm_of_zx_perm_eq_of_proportional.
Qed.

Lemma perm_of_zx_prop_rw {n} {zx0 zx1} :
	zx0 ∝ zx1 ->
	ZXperm n zx0 -> ZXperm n zx1 ->
	perm_of_zx zx0 = perm_of_zx zx1.
Proof.
	intros; now apply perm_of_zx_proper.
Qed.

(* Import Setoid.

Add Parametric Morphism n : (@perm_of_zx n n) 
	with signature 
	(fun zx0 zx1 => zx0 ∝ zx1 /\ ZXperm n zx0 /\ ZXperm n zx1) ==>
	eq as perm_of_zx_proper_instance.
Proof.
	intros zx0 zx1 (? & ? & ?); now apply perm_of_zx_proper.
Qed.

#[export] Hint Extern 0 (_ ∝ _ /\ ZXperm _ _ /\ ZXperm _ _) =>
	split; [split|]; [|auto with zxperm_db..] : typeclasses_db. *)

(* Section on combining zx_of_perm *)

Lemma compose_zx_of_perm n f g 
	(Hf : permutation n f)
	(Hg : permutation n g) : 
	zx_of_perm n f ⟷ zx_of_perm n g ∝ zx_of_perm n (f ∘ g).
Proof.
	(* unfold zx_of_perm. *)
	by_perm_eq.
	apply (fun H => perm_eq_trans H (perm_eq_sym 
		(perm_of_zx_of_perm_eq n (f ∘ g) ltac:(auto with perm_db)))).
	apply perm_eq_compose_proper; cleanup_perm_of_zx.
Qed.

Lemma stack_zx_of_perm n m f g 
	(Hf : permutation n f)
	(Hg : permutation m g) : 
	zx_of_perm n f ↕ zx_of_perm m g ∝ 
	zx_of_perm (n + m) (stack_perms n m f g).
Proof.
	by_perm_eq.
Qed.

#[export] Hint Rewrite compose_zx_of_perm
	stack_zx_of_perm
	using auto with perm_db zxperm_db : perm_of_zx_cleanup_db.

(* TODO: Put somewhere proper *)
Lemma perm_inv_le_bounded_total n f : 
	forall k, 
	perm_inv n f k <= n.
Proof.
	intros k.
	induction n; [easy|].
	simpl.
	bdestructΩ'.
Qed.

#[export] Hint Resolve perm_inv_le_bounded_total : perm_bounded_db.

Lemma insertion_sort_list_eq_of_perm_eq n f g :
	perm_eq n f g -> 
	insertion_sort_list n f = insertion_sort_list n g.
Proof.
	intros Hfg.
	enough (forall k, k <= n -> 
		insertion_sort_list k f = insertion_sort_list k g) by auto with arith.
	intros k Hk.
	revert f g Hfg.
	induction k; [easy|].
	intros f g Hfg.
	simpl.
	rewrite Hfg by lia.
	rewrite (perm_inv_eq_of_perm_eq' n k f g Hfg) by lia.
	f_equal.
	apply IHk; [lia|].
	intros j Hj.
	unfold Bits.fswap.
	pose proof (Hfg k).
	pose proof (Hfg j). 
	pose proof (perm_inv_le_bounded_total k g k).
	pose proof (Hfg (perm_inv k g k) ltac:(lia)).
	bdestructΩ'.
Qed.

Lemma zx_of_perm_prop_of_perm_eq n f g : 
	perm_eq n f g -> 
	zx_of_perm n f ∝ zx_of_perm n g.
Proof.
	intros Hperm.
	unfold zx_of_perm.
	pose proof (insertion_sort_list_eq_of_perm_eq n _ _ 
		(perm_inv_eq_of_perm_eq n f g Hperm)) as Hkey.
	simpl_casts.
	unfold zx_of_perm_uncast.
	instantiate (1 := (f_equal (@length nat) (eq_sym Hkey))).
	instantiate (1 := (f_equal (@length nat) (eq_sym Hkey))).
	now case Hkey.
Qed.

Lemma zx_of_perm_eq_of_perm_eq n f g : 
	perm_eq n f g -> 
	zx_of_perm n f = zx_of_perm n g.
Proof.
	intros Hperm.
	unfold zx_of_perm.
	unfold zx_of_perm_uncast.
	pose proof (insertion_sort_list_eq_of_perm_eq n _ _ 
		(perm_inv_eq_of_perm_eq n f g Hperm)) as Hkey.
	rewrite (Peano_dec.UIP_nat _ _ _ (
		eq_trans (eq_sym (length_insertion_sort_list n (perm_inv n f)))
		(f_equal (@length nat) Hkey)
	)).
	now case Hkey.
Qed.

#[export] Hint Resolve zx_of_perm_eq_of_perm_eq 
	zx_of_perm_prop_of_perm_eq : perm_inv_db.

Lemma zx_of_perm_idn n : 
	zx_of_perm n idn ∝ n_wire n.
Proof.
	by_perm_eq.
Qed.

#[export] Hint Rewrite zx_of_perm_idn : perm_of_zx_cleanup_db.

#[export] Hint Extern 0 (perm_eq _ (perm_of_zx (zx_of_perm ?n ?f)) _) => 
	apply (perm_eq_trans (perm_of_zx_of_perm_eq n f 
		ltac:(auto with perm_db zxperm_db zarith))) : perm_inv_db.

#[export] Hint Extern 0 (perm_eq _ _ (perm_of_zx (zx_of_perm ?n ?f))) => 
	apply (fun G => perm_eq_trans G (perm_eq_sym (perm_of_zx_of_perm_eq n f 
		ltac:(auto with perm_db zxperm_db zarith)))) : perm_inv_db.

Lemma zx_of_perm_eq_idn n f : 
	perm_eq n f idn ->
	zx_of_perm n f = zx_of_perm n idn.
Proof.
	intros H.
	cleanup_perm_inv.
Qed.

#[export] Hint Rewrite zx_of_perm_eq_idn
  using (solve [cleanup_perm_inv]): perm_of_zx_cleanup_db.

Lemma zx_of_perm_eq_idn_prop n f : 
	perm_eq n f idn ->
	zx_of_perm n f ∝ zx_of_perm n idn.
Proof.
	intros H.
	now cleanup_perm_of_zx.
Qed.

Lemma cast_zx_of_perm n n' f (H H' : n = n') :
	cast _ _ H H' (zx_of_perm _ f) = zx_of_perm _ f.
Proof.
	subst.
	now rewrite (Peano_dec.UIP_nat _ _ H' eq_refl).
Qed.

#[export] Hint Rewrite cast_zx_of_perm : cast_simpl_db
	perm_of_zx_cleanup_db.

Lemma cast_zx_of_perm_natural_l n n' m' f H H' : 
	cast n' m' H H' (zx_of_perm n f) = 
	cast n' m' eq_refl (eq_trans H' (eq_sym H)) (zx_of_perm n' f).
Proof.
	now subst.
Qed.

Lemma cast_zx_of_perm_natural_r n n' m' f H H' : 
	cast n' m' H H' (zx_of_perm n f) = 
	cast n' m' (eq_trans H (eq_sym H')) eq_refl (zx_of_perm m' f).
Proof.
	now subst.
Qed.

(* Section on zx_of_perm naturalities *)

Lemma zx_of_perm_perm_eq_idn_removal_l {n m} f
	(zx : ZX n m) : perm_eq n f idn ->
	zx_of_perm n f ⟷ zx ∝ zx.
Proof.
	intros H.
	cleanup_perm_of_zx.
	now cleanup_zx.
Qed.

Lemma zx_of_perm_perm_eq_idn_removal_r {n m} f
	(zx : ZX n m) : perm_eq m f idn ->
	zx ⟷ zx_of_perm m f ∝ zx.
Proof.
	intros H.
	cleanup_perm_of_zx.
	now cleanup_zx.
Qed.

#[export] Hint Rewrite 
	@zx_of_perm_perm_eq_idn_removal_l 
	@zx_of_perm_perm_eq_idn_removal_r
	using (solve [cleanup_perm_inv]) : perm_of_zx_cleanup_db.

Lemma zx_of_perm_semantics n f : 
	permutation n f -> 
	⟦ zx_of_perm n f ⟧ = perm_to_matrix n f.
Proof.
	intros Hf.
	rewrite perm_of_zx_permutation_semantics by auto with zxperm_db.
	apply perm_to_matrix_eq_of_perm_eq.
	cleanup_perm_of_zx.
Qed.

#[export] Hint Rewrite zx_of_perm_semantics 
	using auto with perm_db : perm_of_zx_cleanup_db.

Lemma zx_of_perm_casted_semantics f n n' m' 
	(H : n' = n) (H' : m' = n) : 
	permutation n f -> 
	@eq (Matrix (2^m') (2^n'))
	(⟦ cast n' m' H H' (zx_of_perm n f) ⟧ )
	(perm_to_matrix n f).
Proof.
	intros Hf.
	simpl_cast_semantics.
	cleanup_perm_of_zx.
Qed.

#[export] Hint Rewrite zx_of_perm_casted_semantics
	using auto with perm_db : perm_of_zx_cleanup_db.

Ltac simpl_zx_of_perm_semantics :=
	match goal with 
	|- context[ ⟦cast ?n' ?m' ?H ?H' (zx_of_perm ?n ?f)⟧] =>
		rewrite (zx_of_perm_casted_semantics f n n' m' H H') by auto with perm_db;
		autorewrite with perm_inv_db
	end.

#[export] Hint Extern 5 (@eq (Matrix _ _) _ _)=> 
	(* idtac "HIT"; *)
	simpl_zx_of_perm_semantics : perm_inv_db perm_of_zx_cleanup_db.

(* #[export] Hint Extern 0 (@eq (Matrix _ _) ?A ?A) => 
	reflexivity : perm_inv_db perm_of_zx_cleanup_db. *)


Definition zx_comm p q : (ZX (p + q) (q + p)) :=
	cast (p+q) (q + p) eq_refl (Nat.add_comm q p)
		(zx_of_perm (p + q) (rotr (p + q) p)).

Lemma zx_comm_semantics p q : 
	⟦ zx_comm p q ⟧ = kron_comm (2^q) (2^p).
Proof.
	unfold zx_comm.
	cleanup_perm_of_zx.
	(* simpl_zx_of_perm_semantics.
	rewrite zx_of_perm_casted_semantics. *)
Qed.

#[export] Hint Rewrite zx_comm_semantics : perm_of_zx_cleanup_db.

Lemma zx_comm_cancel p q : 
	zx_comm p q ⟷ zx_comm q p ∝ n_wire _.
Proof.
	prop_exists_nonzero R1.
	rewrite Mscale_1_l.
	simpl.
	cleanup_perm_of_zx.
	rewrite n_wire_semantics.
	restore_dims.
	rewrite kron_comm_mul_inv.
	now unify_pows_two.
Qed.

#[export] Hint Rewrite zx_comm_cancel : perm_of_zx_cleanup_db.

Lemma zx_comm_commutes_l {n m p q} (zx0 : ZX n m) (zx1 : ZX p q) :
	zx_comm p n ⟷ (zx0 ↕ zx1) ∝
	(zx1 ↕ zx0) ⟷ zx_comm q m.
Proof.
	prop_exists_nonzero R1.
	rewrite Mscale_1_l.
	simpl.
	cleanup_perm_of_zx.
	restore_dims.
	apply (kron_comm_commutes_r _ _ _ _ (⟦zx0⟧) (⟦zx1⟧));
	auto with wf_db.
Qed.

Lemma zx_comm_commutes_r {n m p q} (zx0 : ZX n m) (zx1 : ZX p q) :
	(zx0 ↕ zx1) ⟷ zx_comm m q ∝
	zx_comm n p ⟷ (zx1 ↕ zx0).
Proof.
	prop_exists_nonzero R1.
	rewrite Mscale_1_l.
	simpl.
	cleanup_perm_of_zx.
	restore_dims.
	apply (kron_comm_commutes_l _ _ _ _ (⟦zx0⟧) (⟦zx1⟧));
	auto with wf_db.
Qed.

Lemma zx_comm_1_1_swap : 
	zx_comm 1 1 ∝ ⨉.
Proof.
	unfold zx_comm.
	simpl_permlike_zx.
	by_perm_eq.
	intros [| []]; easy.
Qed.

Lemma swap_pullthrough_l {n m} (zx0 : ZX n 1) (zx1 : ZX m 1) : 
	(zx0 ↕ zx1) ⟷ ⨉ ∝
	zx_comm n m ⟷ (zx1 ↕ zx0).
Proof.
	rewrite <- zx_comm_1_1_swap.
	now rewrite zx_comm_commutes_r.
Qed.

Lemma swap_pullthrough_r {n m} (zx0 : ZX 1 n) (zx1 : ZX 1 m) : 
	⨉ ⟷ (zx0 ↕ zx1) ∝
	(zx1 ↕ zx0) ⟷ zx_comm m n.
Proof.
	rewrite <- zx_comm_1_1_swap.
	now rewrite zx_comm_commutes_r.
Qed.

(* TODO: move *)
Lemma permutation_change_dims n m (H : n = m) f : 
	permutation n f <-> permutation m f.
Proof.
	now subst.
Qed.

Lemma rotr_add_n_l n k : 
	rotr n (n + k) = rotr n k.
Proof.
	rewrite rotr_eq_rotr_mod.
	rewrite Nat.add_comm, mod_add_n_r.
	now rewrite <- rotr_eq_rotr_mod.
Qed.

Lemma rotr_add_n_r n k : 
	rotr n (k + n) = rotr n k.
Proof.
	rewrite rotr_eq_rotr_mod.
	rewrite mod_add_n_r.
	now rewrite <- rotr_eq_rotr_mod.
Qed.

#[export] Hint Rewrite rotr_add_n_r rotr_add_n_l : perm_cleanup_db.

Lemma cast_compose_eq_mid_join n m o n' m' o' 
	(Hn : n' = n) (Hm Hm' : m' = m) (Ho : o' = o)
	(zx0 : ZX n m) (zx1 : ZX m o) : 
	cast n' m' Hn Hm zx0 ⟷ cast m' o' Hm' Ho zx1 =
	cast n' o' Hn Ho (zx0 ⟷ zx1).
Proof.
	subst.
	now rewrite (Peano_dec.UIP_nat _ _ Hm' eq_refl).
Qed.

#[export] Hint Rewrite cast_compose_eq_mid_join : cast_simpl_db.

Lemma zx_of_perm_compose_cast_r n n' m' Hn Hm f g 
	(Hf : permutation n f) (Hg : permutation n' g) :
	zx_of_perm n f ⟷ cast n m' Hn Hm (zx_of_perm n' g) ∝
	cast n m' Hn Hm (zx_of_perm n' (f ∘ g)).
Proof.
	subst.
	cleanup_perm_of_zx.
Qed.

Lemma zx_of_perm_compose_cast_l m n' m' Hn Hm f g 
	(Hf : permutation m' f) (Hg : permutation m g) :
	cast n' m Hn Hm (zx_of_perm m' f) ⟷ zx_of_perm m g ∝
	cast n' m Hn Hm (zx_of_perm m' (f ∘ g)).
Proof.
	subst.
	cleanup_perm_of_zx.
Qed.

Lemma zx_of_perm_compose_cast_cast n m n' m' o' Hn Hm Hm' Ho f g 
	(Hf : permutation n f) (Hg : permutation m g) :
	cast n' m' Hn Hm (zx_of_perm n f) ⟷ 
	cast m' o' Hm' Ho (zx_of_perm m g) ∝
	cast n' o' (eq_trans Hn (eq_trans (eq_sym Hm) Hm')) Ho
	(zx_of_perm m (f ∘ g)).
Proof.
	subst.
	cleanup_perm_of_zx.
Qed.

#[export] Hint Rewrite zx_of_perm_compose_cast_r
	zx_of_perm_compose_cast_l 
	zx_of_perm_compose_cast_cast
	using (first [auto with perm_db zxperm_db 
		| erewrite permutation_change_dims; auto with perm_db zarith ]) :
		perm_of_zx_cleanup_db.

Lemma zx_comm_twice_add_r_join n m o H : 
	zx_comm n (m + o) ⟷ cast _ _ H eq_refl (zx_comm m (o + n)) ∝
	cast _ _ (Nat.add_assoc _ _ _) (eq_sym (Nat.add_assoc _ _ _)) 
		 (zx_comm _ _).
Proof.
	unfold zx_comm.
	simpl_casts.
	rewrite zx_of_perm_compose_cast_cast by auto with perm_db.
	simpl_casts.
	apply zx_of_perm_prop_of_perm_eq.
	replace (n + m + o) with (n + (m + o)) by lia.
	replace (m + (o + n)) with (n + (m + o)) by lia.
	cleanup_perm.
Qed.


Lemma zx_comm_twice_add_l_join n m o H : 
	zx_comm (n + m) o ⟷ cast _ _ H eq_refl (zx_comm (o + n) m) ∝
	cast _ _ (eq_sym (Nat.add_assoc _ _ _)) (Nat.add_assoc _ _ _) 
		 (zx_comm n (m + o)).
Proof.
	unfold zx_comm.
	simpl_casts.
	rewrite zx_of_perm_compose_cast_cast by auto with perm_db.
	simpl_casts.
	apply zx_of_perm_prop_of_perm_eq.
	replace (n + m + o) with (n + (m + o)) by lia.
	replace (o + n + m) with (n + (m + o)) by lia.
	cleanup_perm.
	replace (n + m + (o + n)) with (n + (m + o) + n) by lia.
	cleanup_perm.
Qed.

Lemma zx_of_perm_rotr_to_zx_comm n m : 
	zx_of_perm (n + m) (rotr (n + m) n) ∝
	cast _ _ eq_refl (Nat.add_comm _ _)
	(zx_comm n m).
Proof.
	unfold zx_comm.
	simpl_casts.
Qed.

Lemma zx_of_perm_rotr_to_zx_comm_rev n m : 
	zx_of_perm (n + m) (rotr (n + m) m) ∝
	cast _ _ (Nat.add_comm _ _) eq_refl
	(zx_comm m n).
Proof.
	unfold zx_comm.
	simpl_casts.
	now rewrite (Nat.add_comm m n).
Qed.	

Definition zx_gap_comm p m q : (ZX (p + m + q) (q + m + p)) :=
	cast _ _ eq_refl (eq_sym (Nat.add_assoc _ _ _))
	(zx_comm (p + m) q ⟷ (n_wire q ↕ zx_comm p m)).

Lemma zx_gap_comm_defn p m q : 
	zx_gap_comm p m q ∝ 
	cast _ _ eq_refl (eq_sym zx_of_perm 

Import ComposeRules StackComposeRules CastRules.

Lemma zx_gap_comm_pullthrough_r {n m r s p q} 
	(zx0 : ZX n m) (zx1 : ZX r s) (zx2 : ZX p q) :
	zx0 ↕ zx1 ↕ zx2 ⟷ zx_gap_comm m s q ∝
	zx_gap_comm n r p ⟷ (zx2 ↕ zx1 ↕ zx0).
Proof.
	unfold zx_gap_comm at 1.
	rewrite cast_compose_distribute, cast_id, <- compose_assoc.
	rewrite zx_comm_commutes_r, compose_assoc.
	rewrite cast_compose_r, cast_id, <- stack_compose_distr.
	rewrite zx_comm_commutes_r, nwire_removal_r.
	rewrite <- (nwire_removal_l zx2) at 1.
	clean_eqns rewrite stack_compose_distr, stack_assoc_back.
	rewrite (cast_compose_r _ _ (_ ↕ _)).
	simpl_casts.
	rewrite <- compose_assoc.
	unfold zx_gap_comm.
	rewrite cast_compose_distribute, cast_id.
	auto using compose_simplify, cast_simplify, proportional_refl.
Qed.

Lemma zx_gap_comm_pullthrough_l {n m r s p q} 
	(zx0 : ZX n m) (zx1 : ZX r s) (zx2 : ZX p q) :
	zx_gap_comm n r p ⟷ (zx2 ↕ zx1 ↕ zx0) ∝
	zx0 ↕ zx1 ↕ zx2 ⟷ zx_gap_comm m s q.
Proof.
	symmetry. 
	apply zx_gap_comm_pullthrough_r.
Qed.

Lemma zx_gap_comm_1_m_1_a_swap m : 
	zx_gap_comm 1 m 1 ∝ a_swap (1 + m + 1).
Proof.
	unfold zx_gap_comm, zx_.
	by_perm_eq.