Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.Dirac.
Require Export ZX.
Require Export Gates.
Require Export GateRules.
Require Export Proportional.

Local Open Scope ZX_scope.

Lemma ZX_Compose_assoc : forall nIn nMid1 nMid2 nOut
                              (zx1 : ZX nIn nMid1) (zx2 : ZX nMid1 nMid2) (zx3 : ZX nMid2 nOut),
     (zx1 ⟷ zx2) ⟷ zx3 ∝ zx1 ⟷ (zx2 ⟷ zx3).
Proof.
  intros.
  simpl.
  prop_exist_non_zero 1.
  simpl.
  rewrite Mmult_assoc.
  lma.
Qed.

Lemma ZX_Stack_Empty_l : forall {nIn nOut} (zx : ZX nIn nOut),
  ⦰ ↕ zx ∝ zx.
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  rewrite kron_1_l; try auto with wf_db.
  lma.
Qed.

Global Hint Resolve Nat.add_0_r : test_db.

Global Hint Resolve Nat.add_assoc : test_db.
Obligation Tactic := auto with test_db.

Program Lemma ZX_Stack_assoc : 
  forall {nIn1 nIn2 nIn3 nOut1 nOut2 nOut3}
    (zx1 : ZX nIn1 nOut1) (zx2 : ZX nIn2 nOut2) (zx3 : ZX nIn3 nOut3),
    Stack (Stack zx1 zx2) zx3 ∝ Stack zx1 (Stack zx2 zx3).
Proof.
  intros.
  prop_exist_non_zero 1.
  destruct Nat.add_assoc.
  destruct Nat.add_assoc.
  simpl.
  rewrite Mscale_1_l.
  restore_dims.
  rewrite kron_assoc; try auto with wf_db.
Qed.

Program Lemma ZX_Stack_Empty_r : forall {nIn nOut : nat} (zx : ZX nIn nOut),
  Stack zx Empty ∝ zx.
Proof.
  intros.
  prop_exist_non_zero 1.
  Msimpl.
  destruct plus_n_O.
  destruct plus_n_O.
  apply kron_1_r.
Qed.

Lemma ZX_Compose_Empty_r : forall {nIn} (zx : ZX nIn 0),
  Compose zx Empty ∝ zx.
Proof. 
  intros.
  prop_exist_non_zero 1.
  simpl.
  Msimpl.
  reflexivity.
Qed.
  
Lemma ZX_Compose_Empty_l : forall {nOut} (zx : ZX 0 nOut),
  Compose Empty zx ∝ zx.
Proof. 
  intros.
  prop_exist_non_zero 1.
  simpl. 
  Msimpl.
  reflexivity.
Qed.

Ltac remove_empty := try repeat rewrite ZX_Compose_Empty_l;
                     try repeat rewrite ZX_Compose_Empty_r;
                     try repeat rewrite ZX_Stack_Empty_l;
                     try repeat rewrite ZX_Stack_Empty_r;
                     try clear_eq_ctx.

Lemma ZX_semantics_Compose : forall nIn nMid nOut
                                    (zx0 : ZX nIn nMid) (zx1 : ZX nMid nOut),
  ZX_semantics (Compose zx0 zx1) = ZX_semantics zx1 × (ZX_semantics zx0).
Proof. reflexivity. Qed.
   
Lemma ZX_semantics_Stack : forall nIn nMid nOut
                                    (zx0 : ZX nIn nMid) (zx1 : ZX nMid nOut),
  ZX_semantics (Stack zx0 zx1) = ZX_semantics zx0 ⊗ (ZX_semantics zx1).
Proof. reflexivity. Qed.

Lemma ZX_Stack_Compose_distr : 
  forall nIn1 nMid12 nIn3 nOut2 nMid34 nOut4 
    (zx1 : ZX nIn1 nMid12) (zx2 : ZX nMid12 nOut2) (zx3 : ZX nIn3 nMid34) (zx4 : ZX nMid34 nOut4),
    Stack (Compose zx1 zx2) (Compose zx3 zx4) ∝ Compose (Stack zx1 zx3) (Stack zx2 zx4).
Proof.
  intros.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  restore_dims.
  rewrite kron_mixed_product.
  reflexivity.
Qed.

Local Transparent nWire.
Lemma nwire_identity : forall n, ZX_semantics (nWire n) = I (2 ^ n).
Proof.
  intros.
  unfold nWire. 
  rewrite nStack1_n_kron.
  rewrite wire_identity_semantics.
  apply kron_n_I.
Qed.

Lemma nWire_1_Wire : nWire 1 ∝ Wire.
Proof.
  prop_exist_non_zero 1.
  rewrite nwire_identity.
  rewrite wire_identity_semantics.
  lma.
Qed.

Lemma nWire_Stack : forall n m, Stack (nWire n) (nWire m) ∝ nWire (n + m).
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  rewrite 3 nwire_identity.
  rewrite id_kron.
  rewrite Nat.pow_add_r.
  lma.
Qed.

Lemma nWire_2_Stack_wire : nWire 2 ∝ Stack Wire Wire.
Proof.
  rewrite <- nWire_1_Wire.
  symmetry.
  apply nWire_Stack.
Qed.

Lemma nWire_Compose : forall n, Compose (nWire n) (nWire n) ∝ (nWire n).
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  rewrite nwire_identity.
  rewrite Mmult_1_l; try auto with wf_db.
  lma.
Qed.

Lemma Wire_Compose : Compose Wire Wire ∝ Wire.
Proof.
  rewrite <- nWire_1_Wire.
  apply nWire_Compose.
Qed.

Lemma nStack1_compose : forall (zx0 zx1 : ZX 1 1) n, 
  nStack1 n (Compose zx0 zx1) ∝ Compose (nStack1 n zx0) (nStack1 n zx1).
Proof.
  intros.
  induction n.
  - unfold nStack1.
    symmetry.
    apply ZX_Compose_Empty_l.
  - simpl.
    rewrite <- (ZX_Stack_Compose_distr _ _ _ _ _ _ zx0 zx1).
    rewrite IHn.
    reflexivity.
Qed. 


Lemma nH_composition : forall n, 
  nH n ⟷ nH n ∝ nWire n.
Proof.
  intros.
  rewrite <- nStack1_compose.
  rewrite ZX_H_H_is_Wire.
  reflexivity.
Qed.

Local Opaque nWire.

Lemma wire_stack_identity : forall n, 
  ZX_semantics (n ⇑ —) = I (2 ^ n).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite wire_identity_semantics.
    restore_dims.
    rewrite id_kron.
    rewrite <- plus_n_O.
    rewrite double_mult.
    reflexivity.
Qed.

Lemma nwire_r : forall nIn nOut (zx : ZX nIn nOut), 
  zx ⟷ (nWire nOut) ∝ zx.
Proof.
  intros.
  simpl.
  prop_exist_non_zero 1.
  simpl.
  rewrite nwire_identity.
  Msimpl.
  reflexivity.
Qed.

Lemma nwire_l : forall nIn nOut (zx : ZX nIn nOut), 
  (nWire nIn) ⟷ zx ∝ zx.
Proof.
  intros.
  simpl.
  prop_exist_non_zero 1.
  simpl.
  rewrite nwire_identity.
  Msimpl.
  reflexivity.
Qed.

Lemma stack_wire_pad_l_r : 
  forall nIn0 nIn1 nOut0 nOut1 (zx0 : ZX nIn0 nOut0) (zx1 : ZX nIn1 nOut1), 
  Stack zx0 zx1 ∝ Stack (Compose (nWire nIn0) zx0) (Compose zx1 (nWire nOut1)).
Proof.
  intros.
  rewrite nwire_l.
  rewrite nwire_r.
  reflexivity.
Qed.

Lemma stack_wire_pad_r_l : forall nIn0 nIn1 nOut0 nOut1 (zx0 : ZX nIn0 nOut0) (zx1 : ZX nIn1 nOut1), 
  Stack zx0 zx1 ∝ Stack (Compose zx0 (nWire nOut0)) (Compose (nWire nIn1) zx1).
Proof.
  intros.
  rewrite nwire_l.
  rewrite nwire_r.
  reflexivity.
Qed.

Lemma hadamard_color_change_Z : forall nIn nOut α, 
  Compose (nH nIn) (Z_Spider nIn nOut α) ∝ Compose (X_Spider nIn nOut α) (nH nOut).
Proof.
  intros.
  prop_exist_non_zero (Cexp (PI / 4 * (INR nIn - INR nOut))).
  simpl.
  rewrite 2 nStack1_n_kron.
  unfold_spider.
  rewrite ZX_H_is_H.
  repeat rewrite Mscale_kron_n_distr_r.
  repeat rewrite Cexp_pow; simpl.
  rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_r.
  repeat rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  restore_dims.
  rewrite <- Cexp_add.
  rewrite <- Rmult_plus_distr_l.
  replace ((INR nIn - INR nOut + INR nOut))%R with (INR nIn) by lra.
  apply Mscale_simplify; try reflexivity.
  repeat rewrite Mmult_assoc.
  restore_dims.
  repeat rewrite kron_n_mult.
  rewrite Mmult_plus_distr_l.
  rewrite <- Mmult_assoc.
  repeat rewrite Mscale_mult_dist_r.
  rewrite <- Mmult_assoc.
  repeat rewrite kron_n_mult.
  repeat rewrite <- Mmult_assoc.
  rewrite MmultHH.
  Msimpl.
  apply Mplus_simplify;
    try (apply Mscale_simplify; try reflexivity);
    apply Mmult_simplify; try reflexivity;
                          try (rewrite hadamard_sa; unfold bra; reflexivity).
Qed.

Lemma hadamard_color_change_X : forall nIn nOut α, 
  Compose (nH nIn) (X_Spider nIn nOut α) ∝ Compose (Z_Spider nIn nOut α) (nH nOut).
Proof.
  intros.
  prop_exist_non_zero (Cexp (PI / 4 * (INR nIn - INR nOut))).
  simpl.
  rewrite 2 nStack1_n_kron.
  unfold_spider.
  rewrite ZX_H_is_H.
  repeat rewrite Mscale_kron_n_distr_r.
  repeat rewrite Cexp_pow; simpl.
  rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_r.
  repeat rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  restore_dims.
  rewrite <- Cexp_add.
  rewrite <- Rmult_plus_distr_l.
  replace ((INR nIn - INR nOut + INR nOut))%R with (INR nIn) by lra.
  apply Mscale_simplify; try reflexivity.
  repeat rewrite Mmult_assoc.
  restore_dims.
  repeat rewrite kron_n_mult.
  rewrite Mmult_plus_distr_l.
  rewrite <- Mmult_assoc.
  repeat rewrite Mscale_mult_dist_r.
  rewrite <- Mmult_assoc.
  repeat rewrite kron_n_mult.
  rewrite hadamard_sa.
  restore_dims.
  repeat rewrite Mmult_assoc.
  rewrite MmultHH.
  Msimpl.
  repeat rewrite <- Mmult_assoc.
  apply Mplus_simplify;
    try (apply Mscale_simplify; try reflexivity);
    apply Mmult_simplify; try reflexivity;
                          try (rewrite hadamard_sa; unfold bra; reflexivity).
Qed.

Lemma bi_hadamard_color_change_Z : forall nIn nOut α, 
  Compose (Compose (nH nIn) (Z_Spider nIn nOut α)) (nH nOut) ∝ 
  X_Spider nIn nOut α.
Proof.
  intros.
  rewrite hadamard_color_change_Z.
  rewrite ZX_Compose_assoc.
  rewrite nH_composition.
  rewrite nwire_r.
  reflexivity.
Qed.

Lemma bi_hadamard_color_change_X : forall nIn nOut α, 
  Compose (Compose (nH nIn) (X_Spider nIn nOut α)) (nH nOut) ∝ 
  Z_Spider nIn nOut α.
Proof.
  intros.
  rewrite hadamard_color_change_X.
  rewrite ZX_Compose_assoc.
  rewrite nH_composition.
  rewrite nwire_r.
  reflexivity.
Qed.

Lemma Z_spider_1_1_fusion : forall nIn nOut α β, 
  Compose (Z_Spider nIn 1 α) (Z_Spider 1 nOut β) ∝
  Z_Spider nIn nOut (α + β).
Proof.
  prop_exist_non_zero 1.
  intros.
  simpl.
  unfold_spider.
  rewrite Mmult_plus_distr_r, Mmult_plus_distr_l.
  rewrite <- Mmult_assoc.
  rewrite Mscale_mult_dist_r.
  rewrite Mmult_plus_distr_l.
  rewrite Mscale_mult_dist_r.
  restore_dims.
  Msimpl.
  rewrite <- Mplus_assoc.
  rewrite Mplus_comm.
  rewrite <- Mplus_assoc.
  restore_dims.
  Msimpl.
  rewrite Cexp_add.
  repeat rewrite <- Mmult_assoc.
  rewrite 2 Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  rewrite (Mplus_comm _ _ (nOut ⨂ (ket 0) × nIn ⨂ (bra 0)) _).
  repeat rewrite Mplus_assoc.
  apply Mplus_simplify.
  - apply Mscale_simplify; try reflexivity.
    rewrite 2 Mmult_assoc.
    apply Mmult_simplify; try reflexivity.
    rewrite <- Mmult_assoc.
    restore_dims.
    replace (bra 1 × (ket 1)) with (I 1) by solve_matrix.
    Msimpl.
    reflexivity.
  - rewrite <- Mplus_0_r.
    apply Mplus_simplify.
    + rewrite 2 Mmult_assoc.
      apply Mmult_simplify; try reflexivity.
      rewrite <- Mmult_assoc.
      restore_dims. 
      replace (bra 0 × (ket 0)) with (I 1) by solve_matrix.
      Msimpl.
      reflexivity.
    + restore_dims.
      replace ((nOut ⨂ (ket 0) × (bra 0) × (ket 1) × nIn ⨂ (bra 1))) with ((nOut ⨂ (ket 0) × ((bra 0) × (ket 1)) × nIn ⨂ (bra 1))).
      rewrite bra0ket1.
      rewrite Mmult_assoc.
      restore_dims.
      rewrite Mmult_0_l.
      restore_dims.
      rewrite Mmult_0_r.
      rewrite Mscale_0_r.
      rewrite Mplus_0_l.
      rewrite Mmult_assoc.
      rewrite Mscale_mult_dist_l.
      rewrite <- Mmult_assoc.
      restore_dims.
      replace ((nOut ⨂ (ket 1) × (bra 1) × (ket 0) × nIn ⨂ (bra 0))) with ((nOut ⨂ (ket 1) × ((bra 1) × (ket 0)) × nIn ⨂ (bra 0))).
      rewrite bra1ket0.
      restore_dims.
      rewrite Mmult_assoc.
      rewrite Mmult_0_l.
      restore_dims.
      rewrite Mmult_0_r.
      rewrite Mscale_0_r.
      reflexivity.
      rewrite 3 Mmult_assoc.
      apply Mmult_simplify; try reflexivity.
      restore_dims.
      rewrite Mmult_assoc.
      reflexivity.
      rewrite 3 Mmult_assoc.
      restore_dims.
      apply Mmult_simplify; try reflexivity.
      rewrite Mmult_assoc.
      reflexivity.
Qed.

Lemma Z_commutes_through_swap_t : forall α, 
  Compose (Stack (Z_Spider 1 1 α) Wire) ZX_SWAP ∝ 
  Compose ZX_SWAP (Stack Wire (Z_Spider 1 1 α)).
Proof.
  intros.
  prop_exist_non_zero 1.
  rewrite Mscale_1_l.
  simpl.
  unfold_spider.
  rewrite ZX_SWAP_is_swap.
  rewrite wire_identity_semantics.
  simpl.
  Msimpl.
  solve_matrix.
Qed.

Lemma Z_commutes_through_swap_b : forall α, 
  Compose (Stack Wire (Z_Spider 1 1 α)) ZX_SWAP ∝ 
  Compose ZX_SWAP (Stack (Z_Spider 1 1 α) Wire).
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  unfold_spider.
  rewrite ZX_SWAP_is_swap.
  rewrite wire_identity_semantics.
  simpl.
  Msimpl.
  solve_matrix.
Qed.

Lemma X_commutes_through_swap_b : forall α, 
  Compose (Stack Wire (X_Spider 1 1 α)) ZX_SWAP ∝ 
  Compose ZX_SWAP (Stack (X_Spider 1 1 α) Wire).
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  unfold_spider.
  rewrite ZX_SWAP_is_swap.
  rewrite wire_identity_semantics.
  simpl.
  Msimpl.
  solve_matrix.
Qed.

Lemma Spiders_commute_through_swap_b : forall (zx0 zx1 : ZX 1 1),
  (— ↕ zx0) ⟷ ⨉ ∝ ⨉ ⟷ (zx0 ↕ —) ->      
  (— ↕ zx1) ⟷ ⨉ ∝ ⨉ ⟷ (zx1 ↕ —) ->
  (— ↕ (zx0 ⟷ zx1)) ⟷ ⨉ ∝ ⨉ ⟷ ((zx0 ⟷ zx1) ↕ —).
Proof.
  intros.
  rewrite <- Wire_Compose.
  rewrite 2 ZX_Stack_Compose_distr.
  rewrite ZX_Compose_assoc.
  rewrite H0.
  rewrite <- ZX_Compose_assoc.
  rewrite H.
  rewrite <- ZX_Compose_assoc.
  reflexivity.
Qed.

Lemma Spiders_commute_through_swap_t : forall (zx0 zx1 : ZX 1 1),
  Compose (Stack zx0 Wire) ZX_SWAP ∝ Compose ZX_SWAP (Stack Wire zx0) ->      
  Compose (Stack zx1 Wire) ZX_SWAP ∝ Compose ZX_SWAP (Stack Wire zx1) ->
  Compose (Stack (Compose zx0 zx1) Wire) ZX_SWAP ∝ 
  Compose ZX_SWAP (Stack Wire (Compose zx0 zx1)).
Proof.
  intros.
  rewrite <- Wire_Compose.
  rewrite ZX_Stack_Compose_distr.
  rewrite ZX_Compose_assoc.
  rewrite H0.
  rewrite <- ZX_Compose_assoc.
  rewrite H.
  rewrite ZX_Compose_assoc.
  rewrite ZX_Stack_Compose_distr.
  reflexivity.
Qed.

Lemma Z_0_eq_X_0 : 
  Z_Spider 1 1 0 ∝ X_Spider 1 1 0.
Proof.
  prop_exist_non_zero 1.
  simpl.
  unfold_spider.
  rewrite Cexp_0.
  solve_matrix.
Qed.

Theorem identity_removal_Z : Z_Spider 1 1 0 ∝ Wire.
Proof.
  reflexivity.
Qed.

Theorem identity_removal_X : X_Spider 1 1 0 ∝ Wire.
Proof.
  rewrite <- Z_0_eq_X_0.
  reflexivity.
Qed.

Theorem trivial_cap_cup : 
  ⊂ ⟷ ⊃ ∝ Empty.
Proof. prop_exist_non_zero 2; solve_matrix. Qed.

Definition back_forth : ZX 1 1 := (— ↕ ⊂) ⟷ (⊃ ↕ —).

Theorem back_forth_is_wire : back_forth ∝ —.
Proof.
  prop_exist_non_zero 1.
  simpl. 
  rewrite wire_identity_semantics.
  solve_matrix.
Qed.

Definition forth_back : ZX 1 1 := Compose (Stack Cap Wire) (Stack Wire Cup).
Theorem forth_back_is_wire : back_forth ∝ —.
Proof.
  prop_exist_non_zero 1.
  simpl. 
  rewrite wire_identity_semantics.
  solve_matrix.
Qed.

Theorem inverse_angle_Z : forall  α nIn nOut, ZX_semantics(Compose (Z_Spider nIn 1 α) (Z_Spider 1 nOut (-α))) = ZX_semantics (Z_Spider nIn nOut 0).
Proof.
  intros.
Abort.

Theorem Hopf_rule_Z_X : 
  Compose (Z_Spider 1 2 0) (X_Spider 2 1 0) ∝ Compose (Z_Spider 1 0 0) (X_Spider 0 1 0).
Proof.
  prop_exist_non_zero (/C2).
  simpl.
  unfold_spider.
  rewrite Cexp_0.
  rewrite 4 Mscale_1_l.
  solve_matrix.
Qed.

Theorem Hopf_rule_X_Z : 
  Compose (X_Spider 1 2 0) (Z_Spider 2 1 0) ∝ Compose (X_Spider 1 0 0) (Z_Spider 0 1 0).
Proof.
  prop_exist_non_zero (/C2).
  simpl.
  unfold_spider.
  rewrite Cexp_0.
  rewrite 4 Mscale_1_l.
  solve_matrix.
Qed.

Local Definition Bi_Alg_X_Stack_2_1 : ZX 2 4 := Stack (X_Spider 1 2 0) (X_Spider 1 2 0).
Local Definition Bi_Alg_SWAP_Stack : ZX 4 4 := Stack Wire (Stack ZX_SWAP Wire).
Local Definition Bi_Alg_Z_Stack_1_2 : ZX 4 2 := Stack (Z_Spider 2 1 0) (Z_Spider 2 1 0).
Definition Bi_Alg_Z_X := Compose Bi_Alg_X_Stack_2_1 (Compose Bi_Alg_SWAP_Stack Bi_Alg_Z_Stack_1_2).

Theorem BiAlgebra_rule_Z_X : 
  Compose (Z_Spider 2 1 0) (X_Spider 1 2 0) ∝ Bi_Alg_Z_X.
Proof.
  prop_exist_non_zero 4.
  simpl.
  rewrite ZX_SWAP_is_swap, wire_identity_semantics.
  unfold_spider.
  autorewrite with Cexp_db.
  simpl.
  repeat rewrite kron_1_l; try auto with wf_db.
  repeat rewrite Mscale_1_l.
  repeat rewrite Mmult_adjoint.
  repeat rewrite hadamard_sa.
  solve_matrix;
  try repeat rewrite (Cmult_assoc C2 (/C2) _);
  try repeat rewrite Cinv_r;
  try repeat rewrite Cmult_1_l;
  try rewrite Cinv_sqrt2_sqrt;
  try rewrite 2 Cmult_assoc;
  try lca;
  try (
    apply C0_fst_neq;
    simpl;
    auto).
Qed.

Local Definition Bi_Alg_Z_Stack_2_1 : ZX 2 4 := Stack (Z_Spider 1 2 0) (Z_Spider 1 2 0).
Local Definition Bi_Alg_X_Stack_1_2 : ZX 4 2 := Stack (X_Spider 2 1 0) (X_Spider 2 1 0).
Definition Bi_Alg_X_Z := Compose Bi_Alg_Z_Stack_2_1 (Compose Bi_Alg_SWAP_Stack Bi_Alg_X_Stack_1_2).
Theorem BiAlgebra_rule_X_Z : ZX_semantics (Compose (X_Spider 2 1 0) (Z_Spider 1 2 0)) = (C2 * C2) .* ZX_semantics Bi_Alg_X_Z.
Proof.
  simpl.
  rewrite ZX_SWAP_is_swap, wire_identity_semantics.
  unfold_spider.
  autorewrite with Cexp_db.
  simpl.
  repeat rewrite kron_1_l; try auto with wf_db.
  repeat rewrite Mscale_1_l.
  repeat rewrite Mmult_adjoint.
  repeat rewrite hadamard_sa.
  solve_matrix;
  try repeat rewrite (Cmult_comm (/√2) (/C2));
  try repeat rewrite (Cmult_assoc C2 (/C2) _);
  try repeat rewrite Cinv_r;
  try repeat rewrite Cmult_1_l;
  try rewrite Cinv_sqrt2_sqrt;
  try rewrite 2 Cmult_assoc;
  try lca;
  try (
    apply C0_fst_neq;
    simpl;
    auto).
Qed.
Theorem inverse_Z_Spider : forall nIn nOut α, ZX_semantics (Z_Spider nIn nOut α) = (ZX_semantics (Z_Spider nOut nIn (-α)))†.
Proof.
  intros.
  simpl.
  unfold_spider.
  restore_dims.
  rewrite Mscale_adj.
  rewrite Mmult_adjoint.
  rewrite 3 kron_n_adjoint; try auto with wf_db.
  rewrite Cexp_conj_neg.
  rewrite Ropp_involutive.
  assert ((ket 0)† = bra 0) as Hket0 by reflexivity.
  assert ((ket 1)† = bra 1) as Hket1 by reflexivity.
  assert ((bra 0)† = ket 0) as Hbra0 by apply adjoint_involutive.
  assert ((bra 1)† = ket 1) as Hbra1 by apply adjoint_involutive.
  apply Mplus_simplify; (* We need to unfortunately split the proof here due to restore_dims not dealing with .* *)
    try apply Mscale_simplify; 
    try restore_dims;
    try rewrite kron_n_adjoint; try auto with wf_db;
    try rewrite Hket0;
    try rewrite Hket1;
    try rewrite Hbra0;
    try rewrite Hbra1;
    reflexivity.
Qed.

Theorem inverse_X_Spider : forall nIn nOut α, ZX_semantics (X_Spider nIn nOut α) = (ZX_semantics (X_Spider nOut nIn (-α)))†.
Proof.
  intros.
  simpl.
  unfold_spider.
  rewrite Mscale_adj.
  repeat rewrite Mmult_adjoint.
  repeat rewrite <- kron_n_mult.
  rewrite Cexp_conj_neg.
  rewrite Ropp_involutive.
  assert ((ket 0)† = bra 0) as Hket0 by reflexivity.
  assert ((ket 1)† = bra 1) as Hket1 by reflexivity.
  assert ((bra 0)† = ket 0) as Hbra0 by apply adjoint_involutive.
  assert ((bra 1)† = ket 1) as Hbra1 by apply adjoint_involutive.
  apply Mplus_simplify; (* We need to unfortunately split the proof here due to restore_dims not dealing with .* *)
    try apply Mscale_simplify; 
    try restore_dims;
    try repeat rewrite Mmult_adjoint;
    try repeat rewrite kron_n_adjoint; try auto with wf_db;
    try rewrite Hket0;
    try rewrite Hket1;
    try rewrite Hbra0;
    try rewrite Hbra1;
    try repeat rewrite hadamard_sa;
    reflexivity.
Qed.

Lemma ColorSwap_self_inverse : forall {nIn nOut} (zx : ZX nIn nOut),
  ColorSwap (ColorSwap zx) = zx.
Proof.
  intros; induction zx; try reflexivity.
  - simpl.
    rewrite IHzx1.
    rewrite IHzx2.
    reflexivity.
  - simpl.
    rewrite IHzx1.
    rewrite IHzx2.
    reflexivity.
Qed.

Definition BiHadamard {nIn nOut} (zx : ZX nIn nOut) : ZX nIn nOut := 
  Compose (Compose (nH nIn) zx) (nH nOut).
Transparent BiHadamard.

Lemma nH_Plus_Stack : forall {n0 n1 : nat},
    nH (n0 + n1)%nat ∝ Stack (nH n0) (nH n1).
Proof.
  induction n0; intros.
  - rewrite ZX_Stack_Empty_l; reflexivity.
  - simpl.
    destruct (IHn0 n1); destruct H.
    exists x; split; try assumption.
    simpl.
    rewrite H.
    simpl.
    rewrite Mscale_kron_dist_r.
    restore_dims.
    rewrite kron_assoc; try auto with wf_db.
Qed.

Lemma H_comm_cap : (Compose Cap (Stack ZX_H Wire)) ∝ (Compose Cap (Stack Wire ZX_H)).
Proof.
  unfold proportional.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  rewrite wire_identity_semantics.
  rewrite ZX_H_is_H.
  solve_matrix.
Qed.

Lemma H_comm_cup : (Compose (Stack ZX_H Wire) Cup) ∝ (Compose (Stack Wire ZX_H) Cup).
Proof.
  unfold proportional.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  rewrite wire_identity_semantics.
  rewrite ZX_H_is_H.
  solve_matrix.
Qed.

Lemma ColorSwap_isBiHadamard : forall {nIn nOut} (zx : ZX nIn nOut),
    ColorSwap zx ∝ BiHadamard zx.
Proof.
  intros; unfold BiHadamard.
  induction zx.
  - rewrite 2 ZX_Compose_Empty_l.
    reflexivity.
  - rewrite bi_hadamard_color_change_X.
    reflexivity.
  - rewrite bi_hadamard_color_change_Z.
    reflexivity.
  - rewrite ZX_Compose_Empty_l.
    simpl.
    rewrite ZX_Stack_Empty_r.
    clear_eq_ctx.
    rewrite stack_wire_pad_l_r.
    rewrite nWire_1_Wire.
    rewrite ZX_Stack_Compose_distr.
    rewrite <- ZX_Compose_assoc.
    rewrite <- H_comm_cap.
    rewrite ZX_Compose_assoc.
    rewrite  <- (ZX_Stack_Compose_distr _ _ _ _ _ _ ZX_H ZX_H).
    rewrite ZX_H_H_is_Wire.
    rewrite Wire_Compose.
    rewrite <- nWire_2_Stack_wire.
    rewrite nwire_r.
    reflexivity.
  - rewrite ZX_Compose_Empty_r.
    simpl.
    rewrite ZX_Stack_Empty_r.
    clear_eq_ctx.
    rewrite stack_wire_pad_l_r.
    rewrite nWire_1_Wire.
    rewrite ZX_Stack_Compose_distr.
    rewrite ZX_Compose_assoc.
    rewrite H_comm_cup.
    rewrite <- ZX_Compose_assoc.
    rewrite <- (ZX_Stack_Compose_distr _ _ _ _ _ _ Wire Wire).
    rewrite ZX_H_H_is_Wire.
    rewrite Wire_Compose.
    rewrite <- nWire_2_Stack_wire.
    rewrite nwire_l.
    reflexivity.
  - simpl.
    rewrite IHzx1.
    rewrite IHzx2.
    rewrite 2 nH_Plus_Stack.
    rewrite 2 ZX_Stack_Compose_distr.
    reflexivity.
  - simpl.
    rewrite IHzx1.
    rewrite IHzx2.
    rewrite 3 ZX_Compose_assoc.
    rewrite <- (ZX_Compose_assoc _ _ _ _ (nH nMid)).
    rewrite nH_composition.
    rewrite nwire_l.
    rewrite 2 ZX_Compose_assoc.
    reflexivity.
Qed.

Lemma ColorSwap_comp : forall nIn nOut,
  forall zx0 zx1 : ZX nIn nOut, zx0 ∝ zx1 ->
  ColorSwap zx0 ∝ ColorSwap zx1.
Proof.
  intros.
  rewrite 2 ColorSwap_isBiHadamard.
  unfold BiHadamard.
  rewrite H.
  reflexivity.
Qed.

Lemma ColorSwap_lift : forall nIn nOut (zx0 zx1 : ZX nIn nOut),
  ColorSwap zx0 ∝ ColorSwap zx1 -> zx0 ∝ zx1.
Proof.
  intros.
  rewrite <- ColorSwap_self_inverse with zx0.
  rewrite <- ColorSwap_self_inverse.
  rewrite ColorSwap_comp.
  - reflexivity.
  - assumption.
Qed.

Transparent Wire.
Lemma wire_colorswap : ColorSwap Wire ∝ Wire.
Proof.
  unfold Wire.
  simpl.
  rewrite Z_0_eq_X_0.
  reflexivity.
Qed.
Opaque Wire.


Lemma swap_colorswap : ColorSwap ZX_SWAP ∝ ZX_SWAP.
Proof.
  rewrite ColorSwap_isBiHadamard.
  prop_exist_non_zero (-1).
  unfold BiHadamard.
  simpl.
  rewrite kron_1_r.
  rewrite ZX_H_is_H.
  rewrite ZX_SWAP_is_swap.
  rewrite Mscale_kron_dist_l.
  rewrite Mscale_kron_dist_r.
  rewrite Mscale_assoc.
  rewrite <- Cexp_add.
  rewrite Mscale_mult_dist_l.
  rewrite 2 Mscale_mult_dist_r.
  rewrite Mscale_assoc.
  rewrite <- Cexp_add.
  replace (PI / 4 + PI / 4 + (PI / 4 + PI / 4))%R with (PI)%R by (field_simplify;
                                                                  unfold Rdiv;
                                                                  rewrite Rmult_assoc;
                                                                  rewrite Rmult_comm;
                                                                  rewrite Rmult_assoc;
                                                                  rewrite Rinv_l; try nonzero;
                                                                  rewrite Rmult_1_r;
                                                                  reflexivity).
  rewrite Cexp_PI.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_mult_dist_r.
  rewrite 2 Mscale_assoc.
  replace (hadamard ⊗ hadamard × (swap × (hadamard ⊗ hadamard))) with swap by solve_matrix.
  reflexivity.
Qed.

Ltac swap_colors := 
  apply ColorSwap_lift; simpl; try rewrite wire_colorswap; try rewrite swap_colorswap.

Ltac swap_colors_of proof := 
  intros; swap_colors; try apply proof.

Lemma ColorSwap_HadamardPass :forall {nIn nOut} (zx : ZX nIn nOut),
  Compose (nH nIn) zx ∝ Compose (ColorSwap zx) (nH nOut).
Proof.
  intros.
  rewrite ColorSwap_isBiHadamard.
  unfold BiHadamard.
  rewrite ZX_Compose_assoc.
  rewrite <- nStack1_compose.
  rewrite ZX_H_H_is_Wire.
  rewrite nwire_r.
  reflexivity.
Qed.

Lemma Z_1_1_Wire_Cup : forall α, 
  Compose (Stack Wire (Z_Spider 1 1 α)) Cup ∝
  Compose (Stack (Z_Spider 1 1 α) Wire) Cup.
Proof.
  intros.
  prop_exist_non_zero 1.
  rewrite Mscale_1_l.
  simpl.
  unfold_spider.
  rewrite wire_identity_semantics.
  solve_matrix.
Qed.

Lemma Z_1_1_Wire_Cap : forall α, 
  Compose Cap (Stack Wire (Z_Spider 1 1 α)) ∝
  Compose Cap (Stack (Z_Spider 1 1 α) Wire).
Proof.
  intros.
  prop_exist_non_zero 1.
  rewrite Mscale_1_l.
  simpl.
  unfold_spider.
  rewrite wire_identity_semantics.
  solve_matrix.
Qed.

Lemma X_1_1_Wire_Cup : forall α, 
  Compose (Stack Wire (X_Spider 1 1 α)) Cup ∝
  Compose (Stack (X_Spider 1 1 α) Wire) Cup.
Proof.
  swap_colors_of Z_1_1_Wire_Cup.
Qed.

Lemma X_1_1_Wire_Cap : forall α,
Compose Cap (Stack Wire (X_Spider 1 1 α)) ∝
Compose Cap (Stack (X_Spider 1 1 α) Wire).
Proof.
  swap_colors_of Z_1_1_Wire_Cap.
Qed.

Lemma X_spider_1_1_fusion : forall α β, 
  Compose (X_Spider 1 1 α) (X_Spider 1 1 β) ∝ X_Spider 1 1 (α + β).
Proof.
  swap_colors_of Z_spider_1_1_fusion.
Qed.


Local Close Scope ZX_scope.
