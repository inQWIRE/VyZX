Require Import CoreData.
Require Import CoreRules.

Definition bi_alg_Z_X := ((Z_Spider 1 2 0) ↕ (Z_Spider 1 2 0) ⟷ (— ↕ ⨉ ↕ —) ⟷ ((X_Spider 2 1 0) ↕ (X_Spider 2 1 0))).
Definition bi_alg_X_Z := ((X_Spider 1 2 0) ↕ (X_Spider 1 2 0) ⟷ (— ↕ ⨉ ↕ —) ⟷ ((Z_Spider 2 1 0) ↕ (Z_Spider 2 1 0))).

Theorem bi_algebra_rule_Z_X : 
 (X_Spider 2 1 0) ⟷ (Z_Spider 1 2 0) ∝[(√2)%R] bi_alg_Z_X.
Proof.
  Admitted.
  (* simpl.
  rewrite X_semantics_equiv, Z_semantics_equiv.
  unfold_dirac_spider.
  autorewrite with Cexp_db.
  Msimpl.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite kron_plus_distr_r.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mmult_plus_distr_r.
  repeat rewrite Mmult_plus_distr_l.
  assert (forall (ket0 : Matrix 2 1) (bra0 : Matrix 1 2) (ket1 : Matrix 2 1) (bra1 : Matrix 1 2), 
  WF_Matrix ket0 -> WF_Matrix ket1 ->
  ket0⊤ = bra0 -> ket1⊤ = bra1 ->
  (ket0 × (bra0 ⊗ bra0)) ⊗ (ket1 × (bra1 ⊗ bra1)) × (I 2 ⊗ swap ⊗ I 2) 
  = (ket0 × (bra0 ⊗ bra1) ⊗ (ket1 × (bra0 ⊗ bra1))))%M.
  {
    intros.
    subst bra0 bra1.
    rewrite kron_assoc; try auto with wf_db.
    rewrite <- 2 kron_mixed_product.
    rewrite Mmult_assoc.
    apply Mmult_simplify; [ easy | ].
    restore_dims.
    repeat rewrite kron_assoc by auto with wf_db.
    rewrite (kron_mixed_product (ket0⊤) (ket0⊤ ⊗ (ket1⊤ ⊗ ket1⊤)) (I 2) _)%M.
    Msimpl.
    apply kron_simplify; [ easy | ].
    rewrite <- 2 kron_assoc by auto with wf_db.
    rewrite (kron_mixed_product (ket0⊤ ⊗ ket1⊤) (ket1⊤) swap _)%M.
    Msimpl.
    apply kron_simplify; [ | easy].
    apply transpose_matrices.
    rewrite Mmult_transpose.
    rewrite swap_transpose.
    rewrite <- 2 kron_transpose.
    rewrite 2 Matrix.transpose_involutive.
    rewrite swap_spec by auto with wf_db.
    easy.
  }
  repeat rewrite <- Mmult_assoc.
  restore_dims.
  rewrite bra0_equiv, bra1_equiv, ket0_equiv, ket1_equiv.
  repeat rewrite H; try auto with wf_db.
  2-9: apply transpose_matrices; try rewrite braplus_transpose_ketplus; try rewrite braminus_transpose_ketminus; rewrite Matrix.transpose_involutive; easy.
  restore_dims.
  repeat rewrite (kron_mixed_product (xbasis_plus × (_ ⊗ _)) (xbasis_plus × (_ ⊗ _))  ((ket _ ⊗ ket _) × bra _) ((ket _ ⊗ ket _) × bra _)).
  repeat rewrite (kron_mixed_product (xbasis_minus × (_ ⊗ _)) (xbasis_minus × (_ ⊗ _))  ((ket _ ⊗ ket _) × bra _) ((ket _ ⊗ ket _) × bra _)).
  repeat rewrite Mmult_assoc. *)


Theorem bi_algebra_rule_X_Z : 
 (Z_Spider 2 1 0) ⟷ (X_Spider 1 2 0) ∝[(√2)%R] bi_alg_X_Z.
Proof.
  colorswap_of bi_algebra_rule_Z_X.
Qed.


Theorem hopf_rule_Z_X : 
  (Z_Spider 1 2 0) ⟷ (X_Spider 2 1 0) ∝[/C2] (Z_Spider 1 0 0) ⟷ (X_Spider 0 1 0).
Proof.
  split; [|apply nonzero_div_nonzero; nonzero].
  prep_matrix_equivalence.
  cbn.
  unfold X_semantics, Z_semantics.
  rewrite Cexp_0.
  cbn.
  rewrite kron_1_l by auto_wf.
  unfold kron, Mmult, scale; cbn.
  intros i j Hi Hj.
  Csimpl.
  group_radicals.
  autorewrite with C_db.
  destruct i as [|[]]; [..|lia];
  destruct j as [|[]]; [..|lia]; cbn;
  C_field.
Qed.

Theorem hopf_rule_X_Z : 
  (X_Spider 1 2 0) ⟷ (Z_Spider 2 1 0) ∝[/ 2] (X_Spider 1 0 0) ⟷ (Z_Spider 0 1 0).
Proof.
  colorswap_of hopf_rule_Z_X.
Qed.