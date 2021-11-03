Require Import externals.QuantumLib.Quantum.
Require Export ZX.
Require Export Scalars.

Local Open Scope ZX_scope.

Definition proportional {nIn nOut} (zx0 zx1 : ZX nIn nOut) :=
  exists c c' θ, ZX_semantics zx0 = ((√ 2) ^ c * (1 / ((√ 2) ^ c')))%R * Cexp θ .* ZX_semantics zx1.

Infix "∝" := proportional (at level 70).

Lemma proportional_refl : forall {nIn nOut} (zx : ZX nIn nOut), zx ∝ zx.
Proof.
  intros.
  unfold proportional.
  exists 0%nat.
  exists 0%nat.
  exists 0.
  simpl.
  rewrite Cexp_0.
  replace ((1 * (1 / 1))%R * C1) with C1 by lca.
  rewrite Mscale_1_l.
  reflexivity.
Qed.


Lemma sqrt2_pow_n_neq_0 : forall n : nat, (√ 2 ^ n <> 0)%R.
Proof.
  intro n; induction n.
  - apply R1_neq_R0.
  - replace (S n) with (1 + n)%nat by easy.
    rewrite pow_add.
    simpl.
    rewrite Rmult_1_r.
    apply Rmult_integral_contrapositive.
    split.
    + apply sqrt2_neq_0.
    + apply IHn.
Qed.

Lemma proportional_trans : forall {m n} (zx0 zx1 zx2 : ZX m n), 
  zx0 ∝ zx1 -> zx1 ∝ zx2 -> zx0 ∝ zx2.
Proof.
  intros.
  destruct H as [c01 H].
  destruct H as [c'01 H].
  destruct H as [θ01 H01].
  destruct H0 as [c12 H0].  destruct H0 as [c'12 H0].
  destruct H0 as [θ12 H12].
  unfold proportional.
  exists (c01 + c12)%nat.
  exists (c'01 + c'12)%nat.
  exists (θ01 + θ12)%R.
  rewrite pow_add.
  rewrite H01.
  rewrite H12.
  rewrite Mscale_assoc.
  apply Mscale_simplify; try easy.
  rewrite Cexp_add.
  rewrite pow_add.
  replace 1%R with (1 * 1)%R by lra.
  rewrite <- Rmult_div; try apply sqrt2_pow_n_neq_0.
  repeat rewrite RtoC_mult.
  repeat rewrite Cmult_assoc.
  repeat rewrite mult_assoc.
  lca. 
Qed.

Lemma proportional_symm : forall {nIn nOut} (zx0 zx1 : ZX nIn nOut), zx0 ∝ zx1 -> zx1 ∝ zx0.
Proof.
  intros.
  destruct H as [c H].
  destruct H as [c' H].
  destruct H as [θ H].
  unfold proportional.
  exists c'.
  exists c.
  exists (-θ)%R.
  rewrite H.
  replace (ZX_semantics zx1) with (1 .* ZX_semantics zx1) by apply Mscale_1_l.
  rewrite 2 Mscale_assoc.
  apply Mscale_simplify; try easy.
  repeat rewrite RtoC_mult.
  repeat rewrite Cmult_assoc.
  repeat rewrite mult_assoc.
  replace ((√ 2 ^ c')%R * (1 / √ 2 ^ c)%R * Cexp (- θ) * (√ 2 ^ c)%R * (1 / √ 2 ^ c')%R *
  Cexp θ * C1) with ((√ 2 ^ c')%R * (1 / √ 2 ^ c')%R * (1 / √ 2 ^ c)%R * (√ 2 ^ c)%R * Cexp (- θ) * 
  Cexp θ) by lca.
  rewrite <- RtoC_mult.
  replace (√ 2 ^ c' * (1 / √ 2 ^ c'))%R with (√ 2 ^ c' * / (√ 2 ^ c'))%R by lra.
  rewrite Rinv_r; try apply sqrt2_pow_n_neq_0.
  rewrite Cmult_1_l.
  rewrite <- RtoC_mult.
  replace (1 / √ 2 ^ c * √ 2 ^ c)%R with (√ 2 ^ c * / √ 2 ^ c )%R by lra.
  rewrite Rinv_r; try apply sqrt2_pow_n_neq_0.
  rewrite Cmult_1_l.
  rewrite Cexp_mul_neg_l.
  reflexivity.
Qed.

Add Parametric Relation (nIn nOut : nat) : (ZX nIn nOut ) (@proportional nIn nOut)
  reflexivity proved by proportional_refl
  symmetry proved by proportional_symm
  transitivity proved by proportional_trans
  as uc_equiv_rel.

Lemma proportional_C2 : forall nIn nOut (zx0 zx1 : ZX nIn nOut) c2 c12 csqrt2 c1sqrt2 θ, ZX_semantics zx0 = (2 ^ c2 * (1 / (2 ^ c12)) * (√ 2) ^ csqrt2 * (1 / ((√ 2) ^ c1sqrt2)))%R * Cexp θ .* ZX_semantics zx1 -> zx0 ∝ zx1.
Proof.
  intros.
  unfold proportional.
  exists (2 * c2 + csqrt2)%nat.
  exists (2 * c12 + c1sqrt2)%nat.
  exists θ.
  rewrite H.
  apply Mscale_simplify; try easy.
  apply Cmult_simplify; try easy.
  rewrite <- pow2_sqrt2.
  rewrite <- pow_mult.
  rewrite <- pow_mult.
  repeat rewrite pow2_sqrt2.
  replace (√ 2 ^ (2 * c2) * (1 / √ 2 ^ (2 * c12)) * √ 2 ^ csqrt2 * (1 / √ 2 ^ c1sqrt2))%R with (√ 2 ^ (2 * c2) * √ 2 ^ csqrt2 * (1 / √ 2 ^ (2 * c12)) *  (1 / √ 2 ^ c1sqrt2))%R by lra.
  rewrite <- Rdef_pow_add.
  rewrite Rmult_assoc.
  rewrite Rmult_div; try apply sqrt2_pow_n_neq_0.
  rewrite Rmult_1_l.
  rewrite <- Rdef_pow_add.
  reflexivity.
Qed.

Definition build_prop_constants c c' θ := (Stack (Stack (Scalar_Cexp_alpha_times_sqrt_2 θ) (Scalar_1_div_sqrt_2)) (Stack (nStack Scalar_sqrt_2 c) (nStack Scalar_1_div_sqrt_2 c'))).

Theorem ZX_prop_explicit_eq : forall {nIn nOut} (zx0 zx1 : ZX nIn nOut) c c' θ,  ZX_semantics zx0 = ((√ 2) ^ c * (1 / ((√ 2) ^ c')))%R * Cexp θ .* ZX_semantics zx1-> ZX_semantics zx0 = ZX_semantics (Stack (build_prop_constants c c' θ) zx1).
Proof.
  intros nIn nOut zx0 zx1 c c' θ H.
  unfold build_prop_constants.
  simpl.
  rewrite Scalar_X_alpha_Z_PI_sqrt_2.
  rewrite Scalar_X_Z_triple_1_sqrt_2.
  rewrite (Scalar_n_stack Scalar_sqrt_2 (√ 2) c); try exact Scalar_X_alpha_Z_0_sqrt_2.
  rewrite (Scalar_n_stack Scalar_1_div_sqrt_2 (C1 / √ 2) c'); try exact Scalar_X_Z_triple_1_sqrt_2.
  rewrite H.
  rewrite Scalar_kron.
  repeat rewrite Mscale_kron_dist_r.
  repeat rewrite Mscale_kron_dist_l.
  repeat rewrite Mscale_assoc.
  replace (2 ^ (c * 0 + c' * 0))%nat with 1%nat; try rewrite 2 mult_0_r; try rewrite plus_0_l; try repeat rewrite Nat.pow_0_r; try reflexivity. (* Magic to fix dims *)
  Msimpl.
  rewrite Scalar_kron.
  repeat rewrite Mscale_assoc.
  rewrite Mscale_kron_dist_l.
  Msimpl.
  repeat rewrite mult_1_l.
  apply Mscale_simplify; try reflexivity.
  C_field_simplify; try apply Csqrt2_neq_0.
  rewrite RtoC_mult.
  rewrite <- RtoC_pow.
  rewrite RtoC_div; try apply pow_nonzero; try apply sqrt2_neq_0.
  rewrite <- RtoC_pow.
  C_field_simplify; try apply Cpow_nonzero; try apply sqrt2_neq_0; try apply Csqrt2_neq_0.
  rewrite Cdiv_unfold.
  rewrite Cmult_1_l.
  replace (√ 2 ^ c * Cexp θ * √ 2 ^ c' * (/ √ 2) ^ c') with ((√ 2 ^ c * √ 2 ^ c' * (/ √ 2) ^ c') * Cexp θ) by lca.
  apply Cmult_simplify; try reflexivity.
  rewrite <- Cmult_assoc.
  replace (√ 2 ^ c' * (/ √ 2) ^ c') with C1.
  lca.
  rewrite Cpow_inv; try apply Csqrt2_neq_0; try intros; try apply Cpow_nonzero; try apply sqrt2_neq_0.
  rewrite Cinv_r; try apply Cpow_nonzero; try apply sqrt2_neq_0.
  reflexivity.
Qed.

Theorem ZX_prop_eq : forall {nIn nOut} (zx0 zx1 : ZX nIn nOut), zx0 ∝ zx1 -> exists (zxconst : ZX 0 0), ZX_semantics zx0 = ZX_semantics (Stack zxconst zx1).
Proof.
  intros nIn nOut zx0 zx1 H.
  unfold proportional in H.
  destruct H as [c H].
  destruct H as [c' H].
  destruct H as [θ H].
  replace 0%nat with (c * 0 + c' * 0)%nat by lia.
  exists (build_prop_constants c c' θ).
  apply ZX_prop_explicit_eq.
  assumption.
Qed.

Local Close Scope ZX_scope.