Require Import externals.QuantumLib.Quantum.
Require Export ZX.

Local Open Scope ZX_scope.

Definition proportional {nIn nOut} (zx0 zx1 : ZX nIn nOut) :=
  exists c c' θ, ZX_semantics zx0 = ((√2)^c* (1/((√2)^c')))%R * Cexp θ .* ZX_semantics zx1.

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
  destruct H0 as [c12 H0].
  destruct H0 as [c'12 H0].
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

Local Close Scope ZX_scope.

Local Close Scope ZX_scope.
