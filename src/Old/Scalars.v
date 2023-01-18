Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.VectorStates.
Require Import externals.QuantumLib.Matrix.
Require Export ZX.

Local Open Scope ZX_scope.

Lemma Scalar_general : forall (zx : ZX 0 0), ZX_semantics zx = ((ZX_semantics zx) 0%nat 0%nat) .* I 1.
Proof.
  intros.
  prep_matrix_equality.
  simpl.
  assert (Hgt : forall a : nat, (S a >= 1)%nat).
  { 
    intros.
    induction a.
    - auto.
    - constructor; assumption.
  }
  destruct x; destruct y.
    - unfold scale.
    unfold I.
    simpl.
    rewrite Cmult_1_r.
    reflexivity.
  - assert (HZX : ZX_semantics zx 0%nat (S y) = 0).
    {
      rewrite (WF_ZX _ _ zx 0%nat (S y)).
      + reflexivity.
      + right; apply Hgt.
    }
    assert (HI : I 1 0%nat (S y) = 0).
    {
      rewrite (WF_I _ 0%nat (S y)); try reflexivity.
      right; apply Hgt.
    }
    rewrite HZX; unfold scale; rewrite HI.
    rewrite Cmult_0_r.
    reflexivity.
  - assert (HZX : ZX_semantics zx (S x) 0%nat = 0).
    {
      rewrite (WF_ZX _ _ zx (S x) 0%nat).
      + reflexivity.
      + left; apply Hgt.
    }
    assert (HI : I 1 (S x) 0%nat = 0).
    {
      rewrite (WF_I _ (S x) 0%nat); try reflexivity.
      left; apply Hgt.
    }
    rewrite HZX; unfold scale; rewrite HI.
    rewrite Cmult_0_r.
    reflexivity.
  - assert (HZX : ZX_semantics zx (S x) (S y) = 0).
    {
      rewrite (WF_ZX _ _ zx (S x) (S y)).
      + reflexivity.
      + left; apply Hgt.
    }
    assert (HI : I 1 (S x) (S y) = 0).
    {
      rewrite (WF_I _ (S x) (S y)); try reflexivity.
      left; apply Hgt.
    }
    rewrite HZX; unfold scale; rewrite HI.
    rewrite Cmult_0_r.
    reflexivity.
Qed.

Ltac solve_scalar := intros; rewrite Scalar_general; apply Mscale_simplify; try reflexivity.

Definition Scalar_1_plus_Cexp_alpha α := Z_Spider 0 0 α.

Theorem Scalar_Z_general : forall α, (ZX_semantics (Scalar_1_plus_Cexp_alpha α)) = (1 + Cexp(α)) .* I 1.
Proof. solve_scalar. Qed.

Global Opaque Scalar_1_plus_Cexp_alpha.

Definition Scalar_2 := Scalar_1_plus_Cexp_alpha 0.

Theorem Scalar_Z_0_2 : (ZX_semantics Scalar_2) = 2 .* I 1.
Proof. 
  unfold Scalar_2.
  rewrite Scalar_Z_general. 
  rewrite Cexp_0.
  lma.
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
  solve_scalar.
  unfold Scalar_sqrt_2.
  simpl.
  unfold Mmult.
  simpl.
  rewrite Cplus_0_l.
  unfold Z_semantics.
  unfold X_semantics.
  simpl.
  rewrite Cexp_0.
  rewrite 2 Cmult_1_l.
  rewrite kron_1_l; try auto with wf_db.
  unfold Mmult; simpl.
  unfold I; simpl.
  unfold Z_semantics; simpl.
  repeat rewrite (Cplus_0_l).
  rewrite Cexp_0.
  repeat rewrite Cmult_1_r.
  rewrite Cplus_opp_r.
  rewrite Cplus_0_r.
  rewrite Cdiv_unfold.
  rewrite Cmult_1_l.
  rewrite <- Cdouble.
  rewrite <- Csqrt2_sqrt. 
  rewrite <- Cmult_assoc.
  rewrite Cinv_r; try nonzero.
  rewrite Cmult_1_r.
  reflexivity.
Qed. 

Global Opaque Scalar_sqrt_2.

Definition Scalar_Cexp_alpha_times_sqrt_2 α := Compose (X_Spider 0 1 α) (Z_Spider 1 0 PI).

Opaque Ropp.

Theorem Scalar_X_alpha_Z_PI_sqrt_2 : forall α, (ZX_semantics (Scalar_Cexp_alpha_times_sqrt_2 α)) = (√2 * Cexp(α)) .* I 1.
Proof.
  solve_scalar.
  unfold Scalar_Cexp_alpha_times_sqrt_2.
  simpl.
  unfold Mmult; simpl.
  autorewrite with Cexp_db.
  rewrite Cmult_1_l.
  rewrite Cplus_0_l.
  unfold X_semantics.
  unfold Mmult; simpl.
  repeat rewrite Cplus_0_l.
  rewrite kron_1_l; [ | auto with wf_db].
  unfold I; simpl.
  C_field_simplify; [ | nonzero].
  lca.
Qed.

Global Opaque Scalar_Cexp_alpha_times_sqrt_2.

Definition Scalar_1_div_sqrt_2 := Compose (Z_Spider 0 3 0) (X_Spider 3 0 0).


Theorem Scalar_X_Z_triple_1_sqrt_2 : (ZX_semantics Scalar_1_div_sqrt_2) = (1 / √ 2) .* I 1.
Proof.
  solve_scalar.
  unfold Scalar_1_div_sqrt_2.
  simpl.
  simpl.
  unfold Mmult; simpl.
  rewrite Cplus_0_l.
  unfold Z_semantics; simpl.
  repeat rewrite Cmult_0_r.
  repeat rewrite Cplus_0_r.
  rewrite Cexp_0.
  rewrite 2 Cmult_1_r.
  unfold X_semantics; simpl.
  unfold Mmult; simpl.
  repeat rewrite Cplus_0_l.
  rewrite kron_1_l; try auto with wf_db.
  unfold I; simpl.
  repeat rewrite Cmult_1_l.
  unfold kron; simpl.
  unfold hadamard; simpl.
  unfold Z_semantics; simpl.
  repeat rewrite Cmult_0_l.
  repeat rewrite Cplus_0_r.
  rewrite Cexp_0.
  repeat rewrite Cmult_1_l.
  rewrite <- Copp_mult_distr_l.
  rewrite <- 2 Copp_mult_distr_r.
  rewrite Copp_involutive.
  rewrite Cplus_opp_r.
  rewrite Cplus_0_r.
  repeat rewrite Cdiv_unfold.
  repeat rewrite Cmult_1_l.
  rewrite <- Cdouble.
  rewrite Cinv_sqrt2_sqrt.
  rewrite Cmult_assoc.
  rewrite Cinv_r; try nonzero.
  lca.
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
