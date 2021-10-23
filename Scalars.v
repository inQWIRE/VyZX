Require Import externals.QuantumLib.Quantum.
Require Export ZX.

Theorem Scalar_Z_general : forall α, (ZX_semantics (Z_Spider 0 0 α)) = (1 + Cexp(α)) .* I 1.
Proof.
  intros.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  simpl.
  rewrite Mmult_1_l; try auto with wf_db.
  rewrite Mscale_plus_distr_l.
  rewrite Mscale_1_l.
  reflexivity.
Qed.

Theorem Scalar_Z_0_2 : (ZX_semantics (Z_Spider 0 0 0)) = 2 .* I 1.
Proof.
  rewrite Scalar_Z_general.
  rewrite Cexp_0.
  solve_matrix.
Qed.

Theorem Scalar_Z_PI_0: (ZX_semantics (Z_Spider 0 0 PI)) = 0 .* I 1.
Proof.
  rewrite Scalar_Z_general.
  rewrite Cexp_PI.
  solve_matrix.
Qed.

Theorem Scalar_X_alpha_Z_0_sqrt_2 : forall α, (ZX_semantics (Compose (X_Spider 0 1 α) (Z_Spider 1 0 0))) = (√2) .* I 1.
Proof.
  intros.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  simpl.
  rewrite Cexp_0.
  repeat rewrite Mmult_1_l; try auto with wf_db.
  repeat rewrite kron_1_l; try auto with wf_db.
  repeat rewrite Mscale_1_l.
  repeat rewrite Mmult_1_r; try auto with wf_db.
  solve_matrix.
  C_field_simplify; try lca; try apply Csqrt2_neq_0.
Qed. 

Theorem Scalar_X_alpha_Z_PI_sqrt_2 : forall α, (ZX_semantics (Compose (X_Spider 0 1 α) (Z_Spider 1 0 PI))) = (√2 * Cexp(α)) .* I 1.
Proof.
  intros.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  simpl.
  rewrite Cexp_PI.
  repeat rewrite Mmult_1_l; try auto with wf_db.
  repeat rewrite kron_1_l; try auto with wf_db.
  repeat rewrite Mscale_1_l.
  repeat rewrite Mmult_1_r; try auto with wf_db.
  solve_matrix.
  C_field_simplify; try lca; try apply Csqrt2_neq_0.
Qed. 

