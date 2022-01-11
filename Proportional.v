Require Import externals.QuantumLib.Quantum.
Require Export ZX.
Require Export Scalars.
Require Import Setoid.

Local Open Scope ZX_scope.

Definition proportional_constructible {nIn nOut} (zx0 : ZX nIn nOut) (zx1 : ZX nIn nOut) :=
  exists c c' θ, ZX_semantics zx0 = ((√ 2) ^ c * (1 / ((√ 2) ^ c')))%R * Cexp θ .* ZX_semantics zx1.

Definition proportional_general {T n m} (eval : T -> (Matrix n m)) (t0 t1 : T) := 
  exists (c : C), eval t0 = c .* eval t1 /\ c <> 0.

Definition proportional {nIn nOut} (zx0 : ZX nIn nOut) (zx1 : ZX nIn nOut) :=
  proportional_general ZX_semantics zx0 zx1.

Ltac prop_exist_non_zero c := exists c; split; try apply nonzero_div_nonzero; try nonzero.

Infix "∝'" := proportional_constructible (at level 70).

Infix "∝" := proportional (at level 70).

Lemma proportional_general_refl : forall T n m eval (t : T), @proportional_general T n m eval t t.
Proof.
  prop_exist_non_zero 1.
  intros.
  lma.
Qed.

Lemma proportional_general_symm : forall T n m eval (t0 t1 : T), @proportional_general T n m eval t0 t1 -> @proportional_general T n m eval t1 t0.
Proof.
  intros.
  destruct H.
  exists (/x).
  intros.
  destruct H.
  split.
  - rewrite H.  
    rewrite Mscale_assoc.
    rewrite Cinv_l; try lma.
    apply H0.
  - apply nonzero_div_nonzero.
    apply H0.
Qed.

Lemma proportional_general_trans : forall T n m eval (t0 t1 t2 : T), 
    @proportional_general T n m eval t0 t1 -> @proportional_general T n m eval t1 t2 -> @proportional_general T n m eval t0 t2.
Proof.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  exists (x * x0).
  split.
  - rewrite <- Mscale_assoc.
    rewrite <- H0.
    rewrite <- H.
    reflexivity.
  - apply Cmult_neq_0; try assumption. 
Qed.

Lemma proportional_refl : forall {nIn nOut} (zx : ZX nIn nOut), zx ∝ zx.
Proof.
  intros.
  apply proportional_general_refl.
Qed.

Lemma proportional_symm : forall {nIn nOut} (zx0 zx1 : ZX nIn nOut),
  zx0 ∝ zx1 -> zx1 ∝ zx0.
Proof.
  intros.
  apply proportional_general_symm; assumption.
Qed.

Lemma proportional_trans : forall {nIn nOut} (zx0 zx1 zx2 : ZX nIn nOut),
  zx0 ∝ zx1 -> zx1 ∝ zx2 -> zx0 ∝ zx2.
Proof.
  intros.
  apply (proportional_general_trans _ _ _ ZX_semantics zx0 zx1 zx2); assumption.
Qed.

Add Parametric Relation (nIn nOut : nat) : (ZX nIn nOut) (@proportional nIn nOut)
  reflexivity proved by proportional_refl
  symmetry proved by proportional_symm
  transitivity proved by proportional_trans
  as zx_prop_equiv_rel.

Lemma stack_compat :
  forall nIn0 nOut0 nIn1 nOut1,
    forall zx0 zx1 : ZX nIn0 nOut0, zx0 ∝ zx1 ->
    forall zx2 zx3 : ZX nIn1 nOut1, zx2 ∝ zx3 ->
    zx0 ↕ zx2 ∝ zx1 ↕ zx3.
Proof.
  intros.
  destruct H; destruct H; destruct H0; destruct H0.
  exists (x * x0).
  split.
  - simpl; rewrite H; rewrite H0.
    lma.
  - apply Cmult_neq_0; try assumption.
Qed.

Add Parametric Morphism (nIn0 nOut0 nIn1 nOut1 : nat) : (@Stack nIn0 nIn1 nOut0 nOut1)
  with signature (@proportional nIn0 nOut0) ==> (@proportional nIn1 nOut1) ==> 
                 (@proportional (nIn0 + nIn1) (nOut0 + nOut1)) as stack_mor.
Proof. apply stack_compat; assumption. Qed.

Lemma nStack_compat :
  forall nIn nOut n,
    forall zx0 zx1 : ZX nIn nOut, zx0 ∝ zx1 ->
    n ⇑ zx0 ∝ n ⇑ zx1.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite H.
    reflexivity.
Qed.

Add Parametric Morphism (nIn nOut n : nat) : (nStack n)
  with signature (@proportional nIn nOut) ==> 
                 (@proportional (n * nIn) (n * nOut)) as nstack_mor.
Proof. apply nStack_compat. Qed.

Lemma nStack1_compat :
  forall n,
    forall zx0 zx1 : ZX 1 1, zx0 ∝ zx1 ->
    n ↑ zx0 ∝ n ↑ zx1.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite H.
    reflexivity.
Qed. 

Add Parametric Morphism (n : nat) : (nStack1 n)
  with signature (@proportional 1 1) ==> 
                 (@proportional n n) as nstack1_mor.
Proof. apply nStack1_compat. Qed. 

Lemma compose_compat :
  forall nIn nMid nOut,
    forall zx0 zx1 : ZX nIn  nMid, zx0 ∝ zx1 ->
    forall zx2 zx3 : ZX nMid nOut, zx2 ∝ zx3 ->
    zx0 ⟷ zx2 ∝ zx1 ⟷ zx3.
Proof.
  intros.
  destruct H; destruct H; destruct H0; destruct H0.
  exists (x * x0).
  split.
  - simpl; rewrite H; rewrite H0.
    rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    rewrite Mscale_assoc.
    reflexivity.
  - apply Cmult_neq_0; try assumption.
Qed.

Add Parametric Morphism (nIn nMid nOut : nat)  : (@Compose nIn nMid nOut)
  with signature (@proportional nIn nMid) ==> (@proportional nMid nOut) ==> 
                 (@proportional nIn nOut) as compose_mor.
Proof. apply compose_compat; assumption. Qed.

Lemma transpose_compat : 
  forall nIn nOut,
    forall zx0 zx1 : ZX nIn nOut, zx0 ∝ zx1 ->
    (zx0 ⊺) ∝ (zx1 ⊺).
Proof.
  intros.
  destruct H; destruct H; exists x; split; try assumption.
  rewrite 2 ZX_semantics_Transpose_comm.
  rewrite H.
  rewrite Mscale_trans.
  reflexivity.
Qed.

Add Parametric Morphism (nIn nOut : nat) : (@Transpose nIn nOut)
  with signature (@proportional nIn nOut) ==> (@proportional nOut nIn) as transpose_mor.
Proof. apply transpose_compat. Qed.

Lemma adjoint_compat : 
  forall nIn nOut,
    forall zx0 zx1 : ZX nIn nOut, zx0 ∝ zx1 ->
    (zx0 ‡) ∝ (zx1 ‡).
Proof.
  intros.
  destruct H; destruct H; exists (x^*); split.
  - rewrite 2 ZX_semantics_Adjoint_comm.
    rewrite H.
    rewrite Mscale_adj.
    reflexivity.
  - apply Cconj_neq_0.
    assumption. 
Qed.

Add Parametric Morphism (nIn nOut : nat) : (@Adjoint nIn nOut)
  with signature (@proportional nIn nOut) ==> (@proportional nOut nIn) as adj_mor.
Proof. apply adjoint_compat. Qed.

Lemma colorswap_compat :
  forall nIn nOut,
    forall zx0 zx1 : ZX nIn nOut, zx0 ∝ zx1 ->
    (⊙ zx0) ∝ (⊙ zx1).
Proof.
  intros.
  destruct H; destruct H; exists x; split; try assumption.
  rewrite 2 ZX_semantics_Colorswap_comm.
  rewrite H.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  reflexivity.
Qed.

Add Parametric Morphism (nIn nOut : nat) : (@ColorSwap nIn nOut)
  with signature (@proportional nIn nOut) ==> (@proportional nIn nOut) as colorswap_mor.
Proof. apply colorswap_compat. Qed.

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

Lemma sqrt2_pow_n_neq_0' : forall n : nat, (√ 2 ^ n)%R <> 0.
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

Lemma prop_c_to_prop : forall {nIn nOut} (zx0 zx1 : ZX nIn nOut),
  zx0 ∝' zx1 -> zx0 ∝ zx1.
Proof.
  intros.
  destruct H; destruct H; destruct H.
  exists ((√ 2 ^ x * (1 / √ 2 ^ x0))%R * Cexp x1).
  split.
  - assumption.
  - apply Cmult_neq_0; try apply Cexp_nonzero.
    apply C0_fst_neq.
    simpl.
    replace (1 / √ 2 ^ x0)%R with (/ √ 2 ^ x0)%R by lra.
    rewrite Rinv_pow; try apply sqrt2_neq_0.
    apply Rmult_integral_contrapositive_currified; 
      try apply pow_nonzero; try apply Rinv_neq_0_compat; apply sqrt2_neq_0.
Qed.

Lemma proportional_refl_c : forall {nIn nOut} (zx : ZX nIn nOut), zx ∝' zx.
Proof.
  intros.
  unfold proportional.
  exists 0%nat.
  exists 0%nat.
  exists 0.
  simpl.
  autorewrite with Cexp_db.
  replace ((1 * (1 / 1))%R * C1) with C1 by lca.
  rewrite Mscale_1_l.
  reflexivity.
Qed.

Lemma proportional_trans_c : forall {nIn nOut} (zx0 : ZX nIn nOut) (zx1 : ZX nIn nOut) (zx2 : ZX nIn nOut), 
  zx0 ∝' zx1 -> zx1 ∝' zx2 -> zx0 ∝' zx2.
Proof.
  intros.
  destruct H as [c01 H].
  destruct H as [c'01 H].
  destruct H as [θ01 H01].
  destruct H0 as [c12 H0]. 
  destruct H0 as [c'12 H0].
  destruct H0 as [θ12 H12].
  exists (c01 + c12)%nat.
  exists (c'01 + c'12)%nat.
  exists (θ01 + θ12)%R.
  rewrite pow_add.
  rewrite H01.
  rewrite H12.
  rewrite Mscale_assoc.
  apply Mscale_simplify; try easy.
  autorewrite with Cexp_db.
  rewrite pow_add.
  replace 1%R with (1 * 1)%R by lra.
  rewrite <- Rmult_div; try apply sqrt2_pow_n_neq_0.
  repeat rewrite RtoC_mult.
  repeat rewrite Cmult_assoc.
  repeat rewrite mult_assoc.
  lca. 
Qed.

Lemma proportional_symm_c : forall {nIn nOut} (zx0 : ZX nIn nOut) (zx1 : ZX nIn nOut), zx0 ∝' zx1 -> zx1 ∝' zx0.
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
  rewrite Mscale_assoc.
  apply Mscale_simplify; try easy
  repeat rewrite RtoC_mult.
  repeat rewrite Cmult_assoc.
  repeat rewrite mult_assoc.
  - lma.
  - replace ((√ 2 ^ c' * (1 / √ 2 ^ c))%R * Cexp (- θ) * ((√ 2 ^ c * (1 / √ 2 ^ c'))%R * Cexp θ)) with ((((√ 2 ^ c')%R * (1 / √ 2 ^ c')%R) * ((1 / √ 2 ^ c))%R * (√ 2 ^ c)%R) * Cexp (- θ) * Cexp θ) by lca.
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

Lemma proportional_C2 : forall nIn nOut (zx0 zx1 : ZX nIn nOut) c2 c12 csqrt2 c1sqrt2 θ, ZX_semantics zx0 = (2 ^ c2 * (1 / (2 ^ c12)) * (√ 2) ^ csqrt2 * (1 / ((√ 2) ^ c1sqrt2)))%R * Cexp θ .* ZX_semantics zx1 -> zx0 ∝' zx1.
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

Definition build_prop_constants c c' θ := (((Scalar_Cexp_alpha_times_sqrt_2 θ) ↕ (Scalar_1_div_sqrt_2)) ↕ ((c ⇑ Scalar_sqrt_2 ) ↕ (c' ⇑ Scalar_1_div_sqrt_2 ))).

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

Theorem ZX_c_prop_eq : forall {nIn nOut} (zx0 : ZX nIn nOut) (zx1 : ZX nIn nOut), zx0 ∝' zx1 -> exists (zxconst : ZX 0 0), ZX_semantics zx0 = ZX_semantics (Stack zxconst zx1).
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

Theorem ZX_eq_c_prop : forall {nIn nOut} (zx0 : ZX nIn nOut) (zx1 : ZX nIn nOut), ZX_semantics zx0 = (ZX_semantics zx1) -> zx0 ∝' zx1.
Proof.
  intros.
  unfold proportional.
  exists 0%nat.
  exists 0%nat.
  exists 0.
  rewrite H.
  autorewrite with Cexp_db.
  lma.
Qed.

Theorem ZX_eq_prop : forall {nIn nOut} (zx0 : ZX nIn nOut) (zx1 : ZX nIn nOut), ZX_semantics zx0 = (ZX_semantics zx1) -> zx0 ∝ zx1.
Proof.
  intros.
  apply prop_c_to_prop.
  apply ZX_eq_c_prop.
  assumption.
Qed.

Local Close Scope ZX_scope.