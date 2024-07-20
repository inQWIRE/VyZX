Require Import ZXCore.
Require Import CastRules.
Require Import PermutationFacts.
Require Import PermutationInstances.
Require Import ZXperm.
Require Import PermutationAuxiliary.
Require Import PermutationAutomation.
Require Import PermMatrixFacts.
Require Import PermutationSemantics.
Require Import CoreData.Proportional.


Local Open Scope nat. 

Lemma perm_of_zx_permutation n zx : 
  ZXperm n zx -> permutation n (perm_of_zx zx).
Proof. 
  intros H.
  induction H; show_permutation.
Qed.

#[export] Hint Resolve perm_of_zx_permutation : perm_db.
#[export] Hint Extern 4 (permutation _ (perm_of_zx _)) =>
  apply perm_of_zx_permutation;
  solve [auto with zxperm_db] : perm_db.

#[export] Hint Constructors ZXperm : zxperm_db.

(* TODO: Decide whether this goes here (it does) or somewhere else (it doesn't) *)
Lemma stack_perms_matrix_helper {n0 n1 i j} {f g} 
  (Hi : i < 2 ^ (n0 + n1)) (Hj: j < 2 ^ (n0 + n1)) :
  permutation n0 f -> permutation n1 g ->
  i =? qubit_perm_to_nat_perm (n0 + n1) (stack_perms n0 n1 f g) j = 
  (i / 2 ^ n1 =? qubit_perm_to_nat_perm n0 f (j / 2 ^ n1)) &&
  (i mod 2 ^ n1 =? qubit_perm_to_nat_perm n1 g (j mod 2 ^ n1)).
Proof.
  intros Hfperm Hgperm.
  rewrite qubit_perm_to_nat_perm_stack_perms by auto with perm_bounded_db.
  rewrite (eqb_iff_div_mod_eqb (2^n1)), andb_comm.
  do 2 f_equal; 
  unfold tensor_perms; 
  simplify_bools_moddy_lia_one_kernel.
  - rewrite Nat.div_add_l by show_nonzero.
    rewrite (Nat.div_small (_ _)) by auto with perm_bounded_db.
    lia.
  - now rewrite mod_add_l, Nat.mod_small by auto with perm_bounded_db.
Qed.

Lemma empty_permutation_semantics : ⟦ Empty ⟧ = zxperm_to_matrix 0 Empty.
Proof. lma'. Qed.

Lemma wire_permutation_semantics : ⟦ Wire ⟧ = zxperm_to_matrix 1 Wire.
Proof. lma'. Qed.

Lemma swap_2_perm_semantics : ⟦ Swap ⟧ = zxperm_to_matrix 2 Swap.
Proof. lma'. Qed.

Lemma if_dist2 {T1 T2 T3 : Type} (f : T1 -> T2 -> T3) 
  (b1 b2 : bool) x1 x2 x3 x4  :
  f (if b1 then x1 else x2) (if b2 then x3 else x4) = 
  if b1 && b2 then f x1 x3 else 
    (if b1 then f x1 x4 else 
    (if b2 then f x2 x3 else f x2 x4)).
Proof. 
  now destruct b1, b2. 
Qed.

Lemma stack_perms_semantics {n0 n1 m0 m1}
  {zx0 : ZX n0 m0} {zx1 : ZX n1 m1} (H0 : n0 = m0) (H1 : n1 = m1) 
  (Hzx0 : ⟦ zx0 ⟧ = zxperm_to_matrix n0 zx0) 
  (Hzx1 : ⟦ zx1 ⟧ = zxperm_to_matrix n1 zx1) 
  (Hzx0perm : permutation n0 (perm_of_zx zx0))
  (Hzx1perm : permutation n1 (perm_of_zx zx1)) : 
  ⟦ zx0 ↕ zx1 ⟧ = zxperm_to_matrix (n0 + n1) (zx0 ↕ zx1).
Proof.
  simpl.
  subst.
  rewrite perm_to_matrix_of_stack_perms by easy. 
  now f_equal.
Qed.

Lemma compose_permutation_semantics {n m o} {zx0 : ZX n m} {zx1 : ZX m o}
  (H0 : n = m)
  (Hzx0 : ⟦ zx0 ⟧ = zxperm_to_matrix n zx0)
  (Hzx1 : ⟦ zx1 ⟧ = zxperm_to_matrix m zx1) 
  (Hzx0perm : permutation n (perm_of_zx zx0))
  (Hzx1perm : permutation m (perm_of_zx zx1)) :
  ⟦ zx0 ⟷ zx1 ⟧ = zxperm_to_matrix n (zx0 ⟷ zx1).
Proof.
  simpl.
  subst.
  rewrite perm_to_matrix_compose by easy.
  now rewrite Hzx0, Hzx1.
Qed.

Lemma cast_permutations_semantics {n0 n1} {zx : ZX n0 n0} 
  (Hn : n1 = n0)
  (Hzx : ⟦ zx ⟧ = zxperm_to_matrix n1 zx) :
  ⟦ cast _ _ Hn Hn zx ⟧ = zxperm_to_matrix n1 (cast _ _ Hn Hn zx).
Proof. subst; easy. Qed.

Lemma perm_of_zx_permutation_semantics {n zx} : 
  ZXperm n zx -> ⟦ zx ⟧ = zxperm_to_matrix n zx.
Proof.
  intros H.
  induction H.
  - apply empty_permutation_semantics.
  - apply wire_permutation_semantics.
  - apply swap_2_perm_semantics.
  - eapply stack_perms_semantics; auto with perm_db.
  - apply compose_permutation_semantics; auto with perm_db.
Qed.

(* ... which enables the main result: *)

Lemma proportional_of_equal_perm {n} {zx0 zx1 : ZX n n}
	(Hzx0 : ZXperm n zx0) (Hzx1 : ZXperm n zx1)
	(Hperm : perm_of_zx zx0 = perm_of_zx zx1) :
	zx0 ∝ zx1.
Proof.
	prop_exists_nonzero (RtoC 1).
	rewrite Mscale_1_l.
	rewrite (perm_of_zx_permutation_semantics Hzx0),
		(perm_of_zx_permutation_semantics Hzx1).
	f_equal; easy.
Qed.

Lemma proportional_of_perm_eq {n} {zx0 zx1 : ZX n n}
	(Hzx0 : ZXperm n zx0) (Hzx1 : ZXperm n zx1)
	(Hperm : forall k, k < n -> perm_of_zx zx0 k = perm_of_zx zx1 k) :
	zx0 ∝ zx1.
Proof.
	prop_exists_nonzero (RtoC 1).
	rewrite Mscale_1_l.
	rewrite (perm_of_zx_permutation_semantics Hzx0),
		(perm_of_zx_permutation_semantics Hzx1).
  apply mat_equiv_eq; auto with wf_db.
  apply perm_to_matrix_perm_eq, Hperm.
Qed.

(* TODO: split intro prop_perm_eq and prop_perm_eqΩ *)

Ltac prop_perm_eq_nosimpl :=
  intros;
  simpl_casts;
  simpl_permlike_zx;
  __cast_prop_sides_to_square;
  (* Goal: zx0 ∝ zx1 *)
  apply proportional_of_equal_perm; [
  (* New goals: *)
    (*1: ZXperm _ zx0 *) auto 10 with zxperm_db |
    (*2: ZXperm _ zx1*) auto 10 with zxperm_db |
    (*3: perm_of_zx zx0 = perm_of_zx zx1*) 
  ].

Ltac prop_perm_eq :=
  intros;
  autounfold with zxperm_db;
  simpl_casts;
  simpl_permlike_zx;
  __cast_prop_sides_to_square;
  (* Goal: zx0 ∝ zx1 *)
  apply proportional_of_equal_perm; [
  (* New goals: *)
    (*1: ZXperm _ zx0 *) auto 10 with zxperm_db |
    (*2: ZXperm _ zx1*) auto 10 with zxperm_db |
    (*3: perm_of_zx zx0 = perm_of_zx zx1*) cleanup_perm_of_zx; try easy; try lia
  ].

(* TODO: switch all over to this: *)
Ltac by_perm_eq :=
  intros;
  autounfold with zxperm_db;
  simpl_casts;
  simpl_permlike_zx;
  __cast_prop_sides_to_square;
  (* Goal: zx0 ∝ zx1 *)
  apply proportional_of_perm_eq; [
  (* New goals: *)
    (*1: ZXperm _ zx0 *) auto 10 with zxperm_db |
    (*2: ZXperm _ zx1*) auto 10 with zxperm_db |
    (*3: forall k, k < n -> perm_of_zx zx0 k = perm_of_zx zx1 k *) 
    cleanup_perm_of_zx; try easy; try lia
  ].


