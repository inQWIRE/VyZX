Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.Dirac.
Require Export ZX.

Local Open Scope ZX_scope.

Definition Scalar_1_plus_Cexp_alpha α := Z_Spider 0 0 α.

Theorem Scalar_Z_general : forall α, (ZX_semantics (Scalar_1_plus_Cexp_alpha α)) = (1 + Cexp(α)) .* I 1.
Proof.
  intros.
  simpl.
  unfold_spider.
  rewrite Mscale_plus_distr_l.
  rewrite Mscale_1_l.
  reflexivity.
Qed.

Global Opaque Scalar_1_plus_Cexp_alpha.

Definition Scalar_2 := Scalar_1_plus_Cexp_alpha 0.

Theorem Scalar_Z_0_2 : (ZX_semantics Scalar_2) = 2 .* I 1.
Proof.
  unfold Scalar_2.
  rewrite Scalar_Z_general.
  autorewrite with Cexp_db.
  solve_matrix.
Qed.

Global Opaque Scalar_2.

Definition Scalar_0 := Scalar_1_plus_Cexp_alpha PI.

Theorem Scalar_Z_PI_0: (ZX_semantics Scalar_0) = 0 .* I 1.
Proof.
  unfold Scalar_0.
  rewrite Scalar_Z_general.
  autorewrite with Cexp_db.
  solve_matrix.
Qed.

Global Opaque Scalar_0.

Definition Scalar_sqrt_2 := Compose (X_Spider 0 1 0) (Z_Spider 1 0 0).

Theorem Scalar_X_alpha_Z_0_sqrt_2 : (ZX_semantics Scalar_sqrt_2) = (√2) .* I 1.
Proof.
  intros.
  simpl.
  unfold_spider.
  autorewrite with Cexp_db.
  repeat rewrite Mmult_1_l; try auto with wf_db.
  repeat rewrite kron_1_l; try auto with wf_db.
  repeat rewrite Mscale_1_l.
  repeat rewrite Mmult_1_r; try auto with wf_db.
  solve_matrix.
  C_field_simplify; try lca; try apply Csqrt2_neq_0.
Qed. 

Global Opaque Scalar_sqrt_2.

Definition Scalar_Cexp_alpha_times_sqrt_2 α := Compose (X_Spider 0 1 α) (Z_Spider 1 0 PI).

Theorem Scalar_X_alpha_Z_PI_sqrt_2 : forall α, (ZX_semantics (Scalar_Cexp_alpha_times_sqrt_2 α)) = (√2 * Cexp(α)) .* I 1.
Proof.
  intros.
  simpl.
  unfold_spider.
  autorewrite with Cexp_db.
  repeat rewrite Mmult_1_l; try auto with wf_db.
  repeat rewrite kron_1_l; try auto with wf_db.
  repeat rewrite Mscale_1_l.
  repeat rewrite Mmult_1_r; try auto with wf_db.
  solve_matrix.
  C_field_simplify; try lca; try apply Csqrt2_neq_0.
Qed. 

Global Opaque Scalar_Cexp_alpha_times_sqrt_2.

Definition Scalar_1_div_sqrt_2 := Compose (Z_Spider 0 3 0) (X_Spider 3 0 0).

Theorem Scalar_X_Z_triple_1_sqrt_2 : (ZX_semantics Scalar_1_div_sqrt_2) = (1 / √ 2) .* I 1.
Proof.
  intros.
  simpl.
  unfold_spider.
  solve_matrix.
  autorewrite with Cexp_db.
  rewrite Cmult_1_l.
  C_field_simplify; try lca; split; try apply Csqrt2_neq_0.
  apply C0_fst_neq.
  simpl.
  auto.
Qed.

Global Opaque Scalar_1_div_sqrt_2.

Theorem Scalar_n_stack : forall (zx : ZX 0 0) c n, ZX_semantics zx = c .* I 1 -> ZX_semantics (nStack n zx) = c ^ n .* I 1.
Proof.
  intros.
  induction n.
  - symmetry; apply Mscale_1_l.
  - simpl. rewrite IHn, H.
    rewrite Mscale_kron_dist_l.
    Msimpl; try restore_dims.
    + apply Mscale_assoc.
    + replace (I 1) with (I (2 ^ (n * 0))).
      * restore_dims.
        auto with wf_db.
      * rewrite mult_0_r.
        rewrite Nat.pow_0_r.
        reflexivity.
Qed.

Hint Rewrite Scalar_X_Z_triple_1_sqrt_2 Scalar_X_alpha_Z_PI_sqrt_2 Scalar_X_alpha_Z_0_sqrt_2 Scalar_Z_PI_0 Scalar_Z_0_2 Scalar_Z_general : zx_scalar_db.

Lemma Scalar_1_div_sqrt_2_sqrt_identity : ZX_semantics (Stack Scalar_1_div_sqrt_2 Scalar_sqrt_2) = ZX_semantics ⦰.
Proof.
  simpl.
  autorewrite with zx_scalar_db.
  rewrite Mscale_kron_dist_r.
  Msimpl.
  rewrite Mscale_assoc.
  solve_matrix.
Qed.

Lemma Scalar_kron : forall c c', (c .* (I 1)) ⊗ (c' .* (I 1)) = c * c' .* I 1.
Proof.
  intros.
  solve_matrix.
Qed.

Hint Rewrite Scalar_1_div_sqrt_2_sqrt_identity Scalar_kron : zx_scalar_db.

Local Close Scope ZX_scope.
