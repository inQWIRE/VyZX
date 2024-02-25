Require Import ZXCore.
Require Import CastRules.
Require Import PermutationFacts.
Require Import PermutationInstances.
Require Import ZXperm.
Require Import PermMatrix_temp. 
Require Import PermutationAutomation.
Require Import CoreData.Proportional.


Local Open Scope nat. 

Lemma zxperm_permutation n zx : 
  ZXperm n zx -> permutation n (perm_of_zx zx).
Proof. 
  intros H.
  induction H; show_permutation.
Qed.

#[export] Hint Resolve zxperm_permutation : perm_db.

#[export] Hint Constructors ZXperm : zxperm_db.

(* TODO: Decide whether this goes here (it does) or somewhere else (it doesn't) *)
Lemma stack_perms_matrix_helper {n0 n1 i j} {f g} (Hi : i < 2 ^ (n0 + n1)) (Hj: j < 2 ^ (n0 + n1)) :
  permutation n0 f -> permutation n1 g ->
  i =? qubit_perm_to_nat_perm (n0 + n1) (stack_perms n0 n1 f g) j = 
  (i / 2 ^ n1 =? qubit_perm_to_nat_perm n0 f (j / 2 ^ n1)) &&
  (i mod 2 ^ n1 =? qubit_perm_to_nat_perm n1 g (j mod 2 ^ n1)).
Proof.
  intros Hfperm Hgperm. 
  pose proof Hfperm as [finv Hf].
  pose proof Hgperm as [ginv Hg].
  pose proof (stack_perms_permutation Hfperm Hgperm) as Hstackperm.
  pose proof Hstackperm as [stackinv Hstack].
  unfold qubit_perm_to_nat_perm.
  rewrite eqb_iff, Bool.andb_true_iff, 3!Nat.eqb_eq.
  split.
  - intros Heq.
    split.
    + apply Nat.bits_inj.
      intros k.
      rewrite Heq, funbool_to_nat_div.
      rewrite 2!nat_to_funbool_eq.
      rewrite 2!testbit_funbool_to_nat.
      bdestruct (k <? n0); [|easy].
      unfold compose.
      assert (Hlt:n0 - S k < n0) by lia.
      replace (stack_perms n0 n1 f g (n0 - S k) <=? n0 + n1 - 1) with true by (
        assert (Hlt2: n0 - S k < n0 + n1) by lia;
        specialize (Hstack (n0 - S k) Hlt2);
        bdestruct (stack_perms n0 n1 f g (n0 - S k) <=? n0 + n1 - 1); lia
      ).
      replace (f (n0 - S k) <=? n0 - 1) with true by (
        specialize (Hf (n0 - S k) Hlt);
        bdestruct (f (n0 - S k) <=? n0 - 1); lia
      ).
      unfold stack_perms.
      replace (n0 - S k <? n0) with true by (bdestruct (n0 - S k <? n0); lia).
      rewrite Nat.div_pow2_bits.
      f_equal.
      assert (S (f (n0 - S k)) <= n0). {
        specialize (Hf (n0 - S k) Hlt).
        lia. }
      lia.
    + apply Nat.bits_inj.
      intros k.
      rewrite Heq, funbool_to_nat_mod.
      rewrite 2!nat_to_funbool_eq.
      rewrite 2!testbit_funbool_to_nat.
      bdestruct (k <? n1); [|easy].
      unfold compose.
      assert (Hlt:n1 - S k < n1) by lia.
      rewrite Nat.mod_pow2_bits_low; [|lia].
      unfold shift.
      replace (stack_perms n0 n1 f g (n1 - S k + n0) <=? n0 + n1 - 1) with true by (
        assert (Hlt2: n1 - S k + n0 < n0 + n1) by lia;
        specialize (Hstack _ Hlt2);
        bdestruct (stack_perms n0 n1 f g (n1 - S k + n0) <=? n0 + n1 - 1); lia
      ).
      replace (g (n1 - S k) <=? n1 - 1) with true by (
        specialize (Hg (n1 - S k) Hlt);
        bdestruct (g (n1 - S k) <=? n1 - 1); lia
      ).
      f_equal.
      unfold stack_perms.
      replace (n1 - S k + n0 <? n0) with false by (bdestruct (n1 - S k + n0 <? n0); lia).
      replace (n1 - S k + n0 <? n0 + n1) with true by (bdestruct (n1 - S k + n0 <? n0 + n1); lia).
      replace (n1 - S k + n0 - n0) with (n1 - S k) by lia.
      lia.
  - intros [Hdiv Hmod].
    apply (div_mod_inj (2^n1)); [pose proof (Nat.pow_nonzero 2 n1); lia|].
    split.
    + rewrite Hmod.
      rewrite funbool_to_nat_mod.
      apply funbool_to_nat_eq.
      intros k Hk.
      rewrite shift_simplify.
      unfold compose.
      rewrite (stack_perms_right_add Hk).
      
      apply nat_to_funbool_mod.
      specialize (Hg _ Hk); lia.
    + rewrite Hdiv.
      rewrite funbool_to_nat_div.
      apply funbool_to_nat_eq.
      intros k Hk.
      unfold compose.
      rewrite (stack_perms_left Hk).
      apply nat_to_funbool_div.
      specialize (Hf _ Hk); lia.
Qed.



Lemma empty_permutation_semantics : ⟦ Empty ⟧ = zxperm_to_matrix 0 Empty.
Proof. lma'. Qed.

Lemma wire_permutation_semantics : ⟦ Wire ⟧ = zxperm_to_matrix 1 Wire.
Proof. lma'. Qed.

Lemma swap_2_perm_semantics : ⟦ Swap ⟧ = zxperm_to_matrix 2 Swap.
Proof. lma'. Qed.

Lemma apply_if2 {T1 T2 T3 : Type} {b1 b2 : bool} {x1 x2} {x3 x4} (f : T1 -> T2 -> T3) :
  f (if b1 then x1 else x2) (if b2 then x3 else x4) = 
  if b1 && b2 then f x1 x3 else (if b1 then f x1 x4 else (if b2 then f x2 x3 else f x2 x4)).
Proof. destruct b1; destruct b2; easy. Qed.

Lemma stack_perms_matrix {n0 n1 : nat} {f g : nat -> nat} :
  permutation n0 f -> permutation n1 g ->
  perm_to_matrix (n0 + n1) (stack_perms n0 n1 f g) =
  (perm_to_matrix n0 f) ⊗ (perm_to_matrix n1 g).
Proof.
  intros Hf Hg.
  apply mat_equiv_eq.
  1,2:auto with wf_db.
  intros i j Hi Hj.
  
  unfold kron, perm_to_matrix, perm_mat.
  rewrite (proj2 (Nat.ltb_lt _ _) Hi), (proj2 (Nat.ltb_lt _ _) Hj).
  replace (i / 2 ^ n1 <? 2 ^ n0) with true.
  replace (j / 2 ^ n1 <? 2 ^ n0) with true.
  replace (i mod 2 ^ n1 <? 2 ^ n1) with true.
  replace (j mod 2 ^ n1 <? 2 ^ n1) with true.
  repeat rewrite andb_true_r.
  rewrite (apply_if2 Cmult), Cmult_0_l, Cmult_0_l, 
  Cmult_1_l, Cmult_1_l, Tauto.if_same, Tauto.if_same.
  rewrite (stack_perms_matrix_helper Hi Hj Hf Hg).
  easy.
  all: symmetry; rewrite Nat.ltb_lt.
  1,2: apply Nat.mod_upper_bound; apply Nat.pow_nonzero; easy.
  1,2: apply Nat.div_lt_upper_bound; try (apply Nat.pow_nonzero; easy).
  1,2: rewrite Nat.pow_add_r, Nat.mul_comm in Hi, Hj; easy.
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
  rewrite stack_perms_matrix; [|easy|easy].
  rewrite Hzx0, Hzx1.
  subst.
  easy.
Qed.

Lemma compose_permutation_semantics {n m o} {zx0 : ZX n m} {zx1 : ZX m o}
  (H0 : n = m)
  (Hzx0 : ⟦ zx0 ⟧ = zxperm_to_matrix n zx0)
  (Hzx1 : ⟦ zx1 ⟧ = zxperm_to_matrix m zx1) 
  (Hzx0perm : permutation n (perm_of_zx zx0))
  (Hzx1perm : permutation m (perm_of_zx zx1)) :
  ⟦ zx0 ⟷ zx1 ⟧ = zxperm_to_matrix n (zx0 ⟷ zx1).
Proof.
  cbn.
  unfold perm_to_matrix.
  rewrite <- qubit_perm_to_nat_perm_compose.
  - rewrite <- perm_mat_Mmult.
    + rewrite Hzx0, Hzx1.
      subst; easy.
    + apply qubit_perm_to_nat_perm_bij.
      easy.
  - subst; easy.
Qed.

Lemma cast_permutations_semantics {n0 n1} {zx : ZX n0 n0} 
  (Hn : n1 = n0)
  (Hzx : ⟦ zx ⟧ = zxperm_to_matrix n1 zx) :
  ⟦ cast _ _ Hn Hn zx ⟧ = zxperm_to_matrix n1 (cast _ _ Hn Hn zx).
Proof. subst; easy. Qed.

Lemma zxperm_permutation_semantics {n zx} : 
  ZXperm n zx -> ⟦ zx ⟧ = zxperm_to_matrix n zx.
Proof.
  intros H.
  induction H.
  - apply empty_permutation_semantics.
  - apply wire_permutation_semantics.
  - apply swap_2_perm_semantics.
  - eapply stack_perms_semantics; auto.
    all: apply zxperm_permutation; easy.
  - apply compose_permutation_semantics; auto.
    all: apply zxperm_permutation; easy. 
Qed.

(* ... which enables the main result: *)

Lemma proportional_of_equal_perm {n} {zx0 zx1 : ZX n n}
	(Hzx0 : ZXperm n zx0) (Hzx1 : ZXperm n zx1)
	(Hperm : perm_of_zx zx0 = perm_of_zx zx1) :
	zx0 ∝ zx1.
Proof.
	prop_exists_nonzero (RtoC 1).
	rewrite Mscale_1_l.
	rewrite (zxperm_permutation_semantics Hzx0),
		(zxperm_permutation_semantics Hzx1).
	f_equal; easy.
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

Local Close Scope nat. 