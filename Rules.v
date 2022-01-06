Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.Dirac.
Require Export ZX.
Require Export Gates.
Require Export GateRules.
Require Export Proportional.

Local Open Scope ZX_scope.

(* TODO: Move into quantum lib *)
Hint Rewrite Mscale_kron_dist_l Mscale_kron_dist_r Mscale_mult_dist_l Mscale_mult_dist_r Mscale_assoc : scalar_move_db.

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
    (zx1 ↕ zx2) ↕ zx3 ∝ zx1 ↕ (zx2 ↕ zx3).
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
  zx ↕ ⦰ ∝ zx.
Proof.
  intros.
  prop_exist_non_zero 1.
  Msimpl.
  destruct plus_n_O.
  destruct plus_n_O.
  apply kron_1_r.
Qed.

Lemma ZX_Compose_Empty_r : forall {nIn} (zx : ZX nIn 0),
  zx ⟷ ⦰ ∝ zx.
Proof. 
  intros.
  prop_exist_non_zero 1.
  simpl.
  Msimpl.
  reflexivity.
Qed.
  
Lemma ZX_Compose_Empty_l : forall {nOut} (zx : ZX 0 nOut),
  ⦰ ⟷ zx ∝ zx.
Proof. 
  intros.
  prop_exist_non_zero 1.
  simpl. 
  Msimpl.
  reflexivity.
Qed.

Lemma ZX_nStack_0_Empty_l : forall {nOut nIn' nOut'} (zx : ZX 0 nOut) (zx' : ZX nIn' nOut'),
  (0 ⇑ zx') ⟷ zx ∝ zx.
Proof.
  intros.
  simpl.
  rewrite ZX_Compose_Empty_l.
  reflexivity.
Qed.

Lemma ZX_nStack1_0_Empty_l : forall {nOut} (zx : ZX 0 nOut) (zx' : ZX 1 1),
  (0 ↑ zx') ⟷ zx ∝ zx.
Proof.
  intros.
  simpl.
  rewrite ZX_Compose_Empty_l.
  reflexivity.
Qed.

Lemma ZX_nStack_0_Empty_r : forall {nIn nIn' nOut'} (zx : ZX nIn 0) (zx' : ZX nIn' nOut'),
  zx ⟷ (0 ⇑ zx') ∝ zx.
Proof.
  intros.
  simpl.
  rewrite ZX_Compose_Empty_r; clear_eq_ctx.
  reflexivity.
Qed.

Lemma ZX_nStack1_0_Empty_r : forall {nIn} (zx : ZX nIn 0) (zx' : ZX 1 1),
  zx ⟷  (0 ↑ zx') ∝ zx.
Proof.
  intros.
  simpl.
  rewrite ZX_Compose_Empty_r; clear_eq_ctx.
  reflexivity.
Qed.

Ltac remove_empty := try repeat rewrite ZX_Compose_Empty_l;
                     try repeat rewrite ZX_Compose_Empty_r;
                     try repeat rewrite ZX_Stack_Empty_l;
                     try repeat rewrite ZX_nStack_0_Empty_l;
                     try repeat rewrite ZX_nStack_0_Empty_r;
                     try repeat rewrite ZX_nStack1_0_Empty_l;
                     try repeat rewrite ZX_nStack1_0_Empty_r;
                     try (repeat rewrite ZX_Stack_Empty_r; try clear_eq_ctx).

Lemma ZX_semantics_Compose : forall nIn nMid nOut
                                    (zx0 : ZX nIn nMid) (zx1 : ZX nMid nOut),
  ZX_semantics (zx0 ⟷ zx1) = ZX_semantics zx1 × (ZX_semantics zx0).
Proof. reflexivity. Qed.
   
Lemma ZX_semantics_Stack : forall nIn nMid nOut
                                    (zx0 : ZX nIn nMid) (zx1 : ZX nMid nOut),
  ZX_semantics (zx0 ↕ zx1) = ZX_semantics zx0 ⊗ (ZX_semantics zx1).
Proof. reflexivity. Qed.

Lemma ZX_Stack_Compose_distr : 
  forall nIn1 nMid12 nIn3 nOut2 nMid34 nOut4 
    (zx1 : ZX nIn1 nMid12) (zx2 : ZX nMid12 nOut2) (zx3 : ZX nIn3 nMid34) (zx4 : ZX nMid34 nOut4),
    (zx1 ⟷ zx2) ↕ (zx3 ⟷ zx4) ∝ (zx1 ↕ zx3) ⟷ (zx2 ↕ zx4).
Proof.
  intros.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  restore_dims.
  rewrite kron_mixed_product.
  reflexivity.
Qed.

Lemma nwire_identity : forall n, ZX_semantics (n ↑ —) = I (2 ^ n).
Proof.
  intros.
  rewrite nStack1_n_kron.
  rewrite wire_identity_semantics.
  apply kron_n_I.
Qed.

Lemma nWire_1_Wire : (1 ↑ —) ∝ Wire.
Proof.
  prop_exist_non_zero 1.
  rewrite nwire_identity.
  rewrite wire_identity_semantics.
  lma.
Qed.

Lemma nWire_2_Stack_Wire : (2 ↑ —) ∝ — ↕ Wire.
Proof.
  prop_exist_non_zero 1.
  simpl.
  rewrite wire_identity_semantics.
  rewrite kron_1_r.
  lma.
Qed.

Lemma nWire_Stack : forall n m, (n ↑ —) ↕ (m ↑ —) ∝ ((n + m) ↑ —).
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  rewrite 3 nwire_identity.
  rewrite Mscale_1_l.
  rewrite id_kron.
  rewrite Nat.pow_add_r.
  lma.
Qed.

Lemma nWire_Compose : forall n, (n ↑ —) ⟷ (n ↑ —) ∝ n ↑ —.
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  rewrite nwire_identity.
  rewrite Mmult_1_l; try auto with wf_db.
  lma.
Qed.

Lemma Wire_Compose : — ⟷ — ∝ —.
Proof.
  rewrite <- nWire_1_Wire.
  apply nWire_Compose.
Qed.

Global Hint Resolve Nat.mul_1_r : test_db.

Program Lemma nStack_1_nStack : forall n (zx : ZX 1 1), (n ↑ zx) ∝ (n ⇑ zx).
Proof.
  intros.
  unfold eq_rect.
  destruct (Nat.mul_1_r n).
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Program Lemma nStack_nStack_1 : forall n (zx : ZX 1 1), (n ⇑ zx) ∝ (n ↑ zx).
Proof.
  intros.
  symmetry.
  unfold eq_sym.
  unfold eq_rect.
  destruct (Nat.mul_1_r n).
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed. 

Lemma nStack1_compose : forall (zx0 zx1 : ZX 1 1) n, 
  n ↑ (zx0 ⟷ zx1) ∝ (n ↑ zx0) ⟷ (n ↑ zx1).
Proof.
  intros.
  induction n.
  - unfold nStack1.
    symmetry.
    remove_empty.
    reflexivity.
  - simpl.
    rewrite <- (ZX_Stack_Compose_distr _ _ _ _ _ _ zx0 zx1).
    rewrite IHn.
    reflexivity.
Qed. 

Lemma nH_composition : forall n, 
  (n ↑ □) ⟷ (n ↑ □) ∝ n ↑ —.
Proof.
  intros.
  rewrite <- nStack1_compose.
  rewrite ZX_H_H_is_Wire.
  reflexivity.
Qed.

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
  zx ⟷ (nOut ↑ —) ∝ zx.
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
  (nIn ↑ —) ⟷ zx ∝ zx.
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
  zx0 ↕ zx1 ∝ ((nIn0 ↑ —) ⟷ zx0) ↕ (zx1 ⟷ (nOut1 ↑ —)).
Proof.
  intros.
  rewrite nwire_l.
  rewrite nwire_r.
  reflexivity.
Qed.

Lemma stack_wire_pad_r_l : forall nIn0 nIn1 nOut0 nOut1 (zx0 : ZX nIn0 nOut0) (zx1 : ZX nIn1 nOut1), 
  zx0 ↕ zx1 ∝ (zx0 ⟷ (nOut0 ↑ —)) ↕ ((nIn1 ↑ —) ⟷ zx1).
Proof.
  intros.
  rewrite nwire_l.
  rewrite nwire_r.
  reflexivity.
Qed.

Lemma hadamard_color_change_Z : forall nIn nOut α, 
  (nIn ↑ □) ⟷ (Z_Spider nIn nOut α) ∝ (X_Spider nIn nOut α) ⟷ (nOut ↑ □).
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
  (nIn ↑ □) ⟷ (X_Spider nIn nOut α) ∝ (Z_Spider nIn nOut α) ⟷ (nOut ↑ □).
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
  (nIn ↑ □) ⟷ (Z_Spider nIn nOut α) ⟷ (nOut ↑ □) ∝ 
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
  (nIn ↑ □) ⟷ (X_Spider nIn nOut α) ⟷ (nOut ↑ □) ∝ 
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
  (Z_Spider nIn 1 α) ⟷ (Z_Spider 1 nOut β) ∝
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

Lemma Z_0_eq_X_0 : 
  Z_Spider 1 1 0 ∝ X_Spider 1 1 0.
Proof.
  prop_exist_non_zero 1.
  simpl.
  unfold_spider.
  rewrite Cexp_0.
  Msimpl.
  rewrite hadamard_sa.
  rewrite 2 Dirac.ket2bra.
  repeat rewrite Mmult_assoc.
  rewrite <- Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  rewrite <- Mmult_plus_distr_r.
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
  ⊂ ⟷ ⊃ ∝ ⦰.
Proof. prop_exist_non_zero 2; solve_matrix. Qed.

Definition back_forth : ZX 1 1 := (— ↕ ⊂) ⟷ (⊃ ↕ —).

Theorem back_forth_is_Wire : back_forth ∝ —.
Proof.
  prop_exist_non_zero 1.
  simpl. 
  rewrite wire_identity_semantics.
  solve_matrix.
Qed.

Definition forth_back : ZX 1 1 := (⊂ ↕ —) ⟷ (— ↕ ⊃).
Theorem forth_back_is_Wire : forth_back ∝ —.
Proof.
  prop_exist_non_zero 1.
  simpl. 
  rewrite wire_identity_semantics.
  solve_matrix.
Qed.

Theorem Hopf_rule_Z_X : 
  (Z_Spider 1 2 0) ⟷ (X_Spider 2 1 0) ∝ (Z_Spider 1 0 0) ⟷ (X_Spider 0 1 0).
Proof.
  prop_exist_non_zero (/C2).
  simpl.
  unfold_spider.
  rewrite Cexp_0.
  rewrite 4 Mscale_1_l.
  repeat rewrite Dirac.ket2bra.
  repeat rewrite hadamard_sa.
  solve_matrix.
Qed.

Local Definition Bi_Alg_X_Stack_2_1 : ZX 2 4 := (X_Spider 1 2 0) ↕ (X_Spider 1 2 0).
Local Definition Bi_Alg_SWAP_Stack : ZX 4 4 := — ↕ ⨉ ↕ —.
Local Definition Bi_Alg_Z_Stack_1_2 : ZX 4 2 := (Z_Spider 2 1 0) ↕ (Z_Spider 2 1 0).
Definition Bi_Alg_Z_X := Bi_Alg_X_Stack_2_1 ⟷ Bi_Alg_SWAP_Stack ⟷ Bi_Alg_Z_Stack_1_2.

Theorem BiAlgebra_rule_Z_X : 
  (Z_Spider 2 1 0) ⟷ (X_Spider 1 2 0) ∝ Bi_Alg_Z_X.
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
  repeat rewrite Dirac.ket2bra.
  autorewrite with scalar_move_db.
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

Lemma ColorSwap_involutive : forall {nIn nOut} (zx : ZX nIn nOut),
  ⊙ (⊙ zx) = zx. 
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
  (nIn ↑ □) ⟷ zx ⟷ (nOut ↑ □).
Transparent BiHadamard.

Lemma nH_Plus_Stack : forall {n0 n1 : nat},
    (n0 + n1)%nat ↑ □ ∝ (n0 ↑ □) ↕ (n1 ↑ □).
Proof.
  induction n0; intros.
  - remove_empty; reflexivity.
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

Lemma H_comm_cap : (⊂ ⟷ (□ ↕ —)) ∝ (⊂ ⟷ (— ↕ □)).
Proof.
  unfold proportional.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  rewrite wire_identity_semantics.
  rewrite ZX_H_is_H.
  autorewrite with scalar_move_db.
  apply Mscale_simplify; try reflexivity.
  solve_matrix.
Qed.

Lemma H_comm_cup : ((□ ↕ —) ⟷ ⊃) ∝ ((— ↕ □) ⟷ ⊃).
Proof.
  unfold proportional.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  rewrite wire_identity_semantics.
  rewrite ZX_H_is_H.
  autorewrite with scalar_move_db.
  apply Mscale_simplify; try reflexivity.
  solve_matrix.
Qed.

Lemma ColorSwap_X : forall nIn nOut α, X_Spider nIn nOut α ∝ ⊙ (Z_Spider nIn nOut α).
Proof. intros. reflexivity. Qed.

Lemma ColorSwap_Z : forall nIn nOut α, Z_Spider nIn nOut α ∝ ⊙ (X_Spider nIn nOut α).
Proof. intros. reflexivity. Qed.

Lemma ColorSwap_Compose : forall nIn nMid nOut (zx0 : ZX nIn nMid) (zx1 : ZX nMid nOut),
  (⊙ zx0 ⟷ ⊙ zx1) ∝ ⊙ (zx0 ⟷ zx1).
Proof. intros. reflexivity. Qed.

Lemma ColorSwap_Stack : forall nIn0 nIn1 nOut0 nOut1 (zx0 : ZX nIn0 nOut0) (zx1 : ZX nIn1 nOut1),
  (⊙ zx0 ↕ ⊙ zx1) ∝ ⊙ (zx0 ↕ zx1).
Proof. intros. reflexivity. Qed.

Lemma ColorSwap_isBiHadamard : forall {nIn nOut} (zx : ZX nIn nOut),
    ⊙ zx ∝ BiHadamard zx.
Proof.
  intros; unfold BiHadamard.
  induction zx.
  - remove_empty.
    reflexivity.
  - rewrite bi_hadamard_color_change_X.
    reflexivity.
  - rewrite bi_hadamard_color_change_Z.
    reflexivity.
  - remove_empty.
    simpl.
    remove_empty.
    rewrite stack_wire_pad_l_r.
    rewrite nWire_1_Wire.
    rewrite ZX_Stack_Compose_distr.
    rewrite <- ZX_Compose_assoc.
    rewrite <- H_comm_cap.
    rewrite ZX_Compose_assoc.
    rewrite  <- (ZX_Stack_Compose_distr _ _ _ _ _ _ ZX_H ZX_H).
    rewrite ZX_H_H_is_Wire.
    rewrite Wire_Compose.
    rewrite <- nWire_2_Stack_Wire.
    rewrite nwire_r.
    reflexivity.
  - remove_empty.
    simpl.
    remove_empty.
    rewrite stack_wire_pad_l_r.
    rewrite nWire_1_Wire.
    rewrite ZX_Stack_Compose_distr.
    rewrite ZX_Compose_assoc.
    rewrite H_comm_cup.
    rewrite <- ZX_Compose_assoc.
    rewrite <- (ZX_Stack_Compose_distr _ _ _ _ _ _ — —).
    rewrite ZX_H_H_is_Wire.
    rewrite Wire_Compose.
    rewrite <- nWire_2_Stack_Wire.
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
    rewrite <- (ZX_Compose_assoc _ _ _ _ (nMid ↑ □)).
    rewrite nH_composition.
    rewrite nwire_l.
    rewrite 2 ZX_Compose_assoc.
    reflexivity.
Qed.

Lemma ColorSwap_comp : forall nIn nOut,
  forall zx0 zx1 : ZX nIn nOut, zx0 ∝ zx1 ->
  ⊙ zx0 ∝ ⊙ zx1.
Proof.
  intros.
  rewrite 2 ColorSwap_isBiHadamard.
  unfold BiHadamard.
  rewrite H.
  reflexivity.
Qed.

Lemma ColorSwap_lift : forall nIn nOut (zx0 zx1 : ZX nIn nOut),
  ⊙ zx0 ∝ ⊙ zx1 -> zx0 ∝ zx1.
Proof.
  intros.
  rewrite <- ColorSwap_involutive with zx0.
  rewrite <- ColorSwap_involutive.
  rewrite ColorSwap_comp.
  - reflexivity.
  - assumption.
Qed.

Transparent Wire.
Lemma wire_colorswap : ⊙ — ∝ —.
Proof.
  unfold Wire.
  simpl.
  rewrite Z_0_eq_X_0.
  reflexivity.
Qed.
Opaque Wire.

Lemma empty_colorswap : ⊙ ⦰ ∝ ⦰.
Proof.
  reflexivity.
Qed.

Lemma colorswap_eq_n_Stack : forall nIn nOut (zx : ZX nIn nOut) n, ⊙ zx ∝ zx -> ⊙ (n ⇑ zx) ∝ (n ⇑ zx).
Proof.
  intros.
  induction n; simpl; try exact empty_colorswap.
  rewrite IHn.
  rewrite H.
  reflexivity.
Qed.

Lemma colorswap_eq_n_Stack_1 : forall zx n, ⊙ zx ∝ zx -> ⊙ (n ↑ zx) ∝ (n ↑ zx).
Proof.
  intros.
  induction n; simpl; try exact empty_colorswap.
  rewrite IHn.
  rewrite H.
  reflexivity.
Qed.

Lemma nWire_colorswap : forall n, ⊙ (n ↑ —) ∝ (n ↑ —).
Proof.
  intros.
  apply colorswap_eq_n_Stack_1.
  exact wire_colorswap.
Qed.

Lemma H_colorswap : ⊙ □ ∝ □.
Proof.
  rewrite ColorSwap_isBiHadamard.
  unfold BiHadamard.
  simpl.
  remove_empty.
  rewrite ZX_H_H_is_Wire.
  rewrite <- nWire_1_Wire.
  rewrite nwire_l.
  reflexivity.
Qed.

Local Transparent ZX_X ZX_Z ZX_Y.
Lemma Z_colorswap_X : ⊙ ZX_X ∝ ZX_Z.
Proof.
  unfold ZX_X, ZX_Z.
  reflexivity.
Qed.

Lemma X_colorswap_Z : ⊙ ZX_Z ∝ ZX_X.
Proof.
  unfold ZX_X, ZX_Z.
  reflexivity.
Qed.
Local Opaque ZX_X ZX_Z.

Lemma Y_colorswap : ⊙ ZX_Y ∝ ZX_Y.
Proof.
  unfold ZX_Y.
  simpl.
  rewrite X_colorswap_Z, Z_colorswap_X.
Local Transparent ZX_X ZX_Z.
  prop_exist_non_zero (-1).
  unfold ZX_X, ZX_Z.
  simpl.
  unfold_spider.
  autorewrite with Cexp_db.
  Msimpl.
  repeat rewrite Dirac.ket2bra.
  repeat rewrite hadamard_sa.
  solve_matrix.
Qed.
Local Opaque ZX_X ZX_Z ZX_Y.

Lemma nH_colorswap : forall n, ⊙ (n ↑ □) ∝ (n ↑ □).
Proof.
  intros.
  apply colorswap_eq_n_Stack_1.
  exact H_colorswap.
Qed.

Lemma compose_colorswap : forall nIn nMid nOut (zx0 : ZX nIn nMid) (zx1 : ZX nMid nOut),
  ⊙ zx0 ∝ zx0 -> ⊙ zx1 ∝ zx1 -> ⊙ (zx0 ⟷ zx1) ∝ (zx0 ⟷ zx1).
Proof.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma stack_colorswap : forall nIn nMid nOut (zx0 : ZX nIn nMid) (zx1 : ZX nMid nOut),
  ⊙ zx0 ∝ zx0 -> ⊙ zx1 ∝ zx1 -> ⊙ (zx0 ↕ zx1) ∝ (zx0 ↕ zx1).
Proof.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma nStack1_colorswap : forall zx n ,
  ⊙ zx ∝ zx -> ⊙ (n ↑ zx) ∝ (n ↑ zx).
Proof.
  intros.
  subst.
  induction n; simpl.
  - exact empty_colorswap.
  - rewrite H, IHn.
    reflexivity.
Qed.

Lemma nStack_colorswap : forall nIn nOut (zx : ZX nIn nOut) n,
  ⊙ zx ∝ zx -> ⊙ (n ⇑ zx) ∝ (n ⇑ zx).
Proof.
  intros.
  subst.
  induction n; simpl.
  - exact empty_colorswap.
  - rewrite H, IHn.
    reflexivity.
Qed.

Lemma swap_colorswap : ⊙ ⨉ ∝ ⨉.
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
  autorewrite with scalar_move_db.
  apply Mscale_simplify; try reflexivity.
  rewrite <- Mmult_assoc.
  solve_matrix.
Qed.

Ltac swap_colors := 
  apply ColorSwap_lift; simpl; try rewrite wire_colorswap; try rewrite H_colorswap; try rewrite nWire_colorswap; try rewrite nH_colorswap; try rewrite swap_colorswap.

Ltac swap_colors_of proof := 
  intros; swap_colors; try apply proof.

Theorem Hopf_rule_X_Z : 
  (X_Spider 1 2 0) ⟷ (Z_Spider 2 1 0) ∝ (X_Spider 1 0 0) ⟷ (Z_Spider 0 1 0).
Proof.
  swap_colors_of Hopf_rule_Z_X.
Qed.
 
Local Definition Bi_Alg_Z_Stack_2_1 : ZX 2 4 := (Z_Spider 1 2 0) ↕ (Z_Spider 1 2 0).
Local Definition Bi_Alg_X_Stack_1_2 : ZX 4 2 := (X_Spider 2 1 0) ↕ (X_Spider 2 1 0).
Definition Bi_Alg_X_Z := Bi_Alg_Z_Stack_2_1 ⟷ Bi_Alg_SWAP_Stack ⟷ Bi_Alg_X_Stack_1_2.
Theorem BiAlgebra_rule_X_Z : (X_Spider 2 1 0) ⟷ (Z_Spider 1 2 0) ∝ Bi_Alg_X_Z.
Proof.
  unfold Bi_Alg_X_Z, Bi_Alg_Z_Stack_2_1, Bi_Alg_X_Stack_1_2.
  swap_colors_of BiAlgebra_rule_Z_X.
Qed.


Lemma Z_commutes_through_swap_t : forall α, 
  ((Z_Spider 1 1 α) ↕ —) ⟷ ⨉ ∝ 
  ⨉ ⟷ (— ↕ (Z_Spider 1 1 α)).
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
  autorewrite with scalar_move_db.
  apply Mscale_simplify; try reflexivity.
  solve_matrix.
Qed.  

Lemma X_commutes_through_swap_t : forall α, 
  ((X_Spider 1 1 α) ↕ —) ⟷ ⨉ ∝ 
  ⨉ ⟷ (— ↕ (X_Spider 1 1 α)).
Proof.
  swap_colors_of Z_commutes_through_swap_t.
Qed.  

Lemma Z_commutes_through_swap_b : forall α, 
  (— ↕ (Z_Spider 1 1 α)) ⟷ ⨉ ∝ 
  ⨉ ⟷ ((Z_Spider 1 1 α) ↕ —).
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  unfold_spider.
  rewrite ZX_SWAP_is_swap.
  rewrite wire_identity_semantics.
  simpl.
  Msimpl.
  autorewrite with scalar_move_db.
  apply Mscale_simplify; try reflexivity.
  solve_matrix.
Qed.

Lemma X_commutes_through_swap_b : forall α, 
  (— ↕ (X_Spider 1 1 α)) ⟷ ⨉ ∝ 
  ⨉ ⟷ ((X_Spider 1 1 α) ↕ —).
Proof.
  swap_colors_of Z_commutes_through_swap_b.
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
  (zx0 ↕ —) ⟷ ⨉ ∝ ⨉ ⟷ (— ↕ zx0) ->      
  (zx1 ↕ —) ⟷ ⨉ ∝ ⨉ ⟷ (— ↕ zx1) ->
  ((zx0 ⟷ zx1) ↕ —) ⟷ ⨉ ∝ ⨉ ⟷ (— ↕ (zx0 ⟷ zx1)).
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

Lemma ColorSwap_HadamardPass :forall {nIn nOut} (zx : ZX nIn nOut),
  (nIn ↑ □) ⟷ zx ∝ (⊙ zx ⟷ (nOut ↑ □)).
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
  (— ↕ (Z_Spider 1 1 α)) ⟷ ⊃ ∝ ((Z_Spider 1 1 α) ↕ —) ⟷ ⊃.
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
  ⊂ ⟷ (— ↕ (Z_Spider 1 1 α)) ∝ ⊂ ⟷ ((Z_Spider 1 1 α) ↕ —).
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
  (— ↕ (X_Spider 1 1 α)) ⟷ ⊃ ∝ ((X_Spider 1 1 α) ↕ —) ⟷ ⊃.
Proof.
  swap_colors_of Z_1_1_Wire_Cup.
Qed.

Lemma X_1_1_Wire_Cap : forall α,
  ⊂ ⟷ (— ↕ (X_Spider 1 1 α)) ∝ ⊂ ⟷ ((X_Spider 1 1 α) ↕ —).
Proof.
  swap_colors_of Z_1_1_Wire_Cap.
Qed.

Lemma X_spider_1_1_fusion : forall α β, 
  (X_Spider 1 1 α) ⟷ (X_Spider 1 1 β) ∝ X_Spider 1 1 (α + β).
Proof.
  swap_colors_of Z_spider_1_1_fusion.
Qed.
 
Lemma Z_double_H_connection : forall α β,
  (Z_Spider 1 2 α) ⥈ (Z_Spider 2 1 β) ∝ (Z_Spider 1 0 α) ⟷ (Z_Spider 0 1 β).
Proof.
  intros.
  prop_exist_non_zero (Cexp (PI / 4) * (Cexp (PI / 4)) * / C2); try apply Cmult_neq_0; try apply nonzero_div_nonzero; try apply Cmult_neq_0; try nonzero.
  unfold_spider.
  unfold Spider_semantics, bra_ket_MN.
  simpl; Msimpl.
  rewrite ZX_H_is_H.
  autorewrite with scalar_move_db.
  repeat rewrite <- Mscale_assoc.
  apply Mscale_simplify; try reflexivity.
  apply Mscale_simplify; try reflexivity.
  solve_matrix.
Qed.

Lemma X_double_H_connection : forall α β,
  (X_Spider 1 2 α) ⥈ (X_Spider 2 1 β) ∝ (X_Spider 1 0 α) ⟷ (X_Spider 0 1 β).
Proof.
    swap_colors_of Z_double_H_connection.
Qed.

Lemma Empty_H_edge : forall nIn nOut (zx0 : ZX nIn 0) (zx1 : ZX 0 nOut),
  zx0 ⥈ zx1 ∝ zx0 ⟷ zx1.
Proof.
  intros; simpl.
  unfold hadamard_edge.
  simpl.
  rewrite ZX_Compose_Empty_r.
  reflexivity.
Qed. 

Lemma H_edge_ColorSwap_inv_l : forall nMid nOut (zx0 : ZX 0 nMid) (zx1 : ZX nMid nOut), 
  zx0 ∝ ⊙ zx0 -> zx0 ⥈ zx1 ∝ zx0 ⟷ zx1.
Proof.
  intros.
  unfold hadamard_edge.
  rewrite H.
  rewrite <- ColorSwap_HadamardPass.
  remove_empty.
  rewrite <- H.
  reflexivity.
Qed.

Lemma H_edge_ColorSwap_inv_r : forall nIn nMid (zx0 : ZX nIn nMid) (zx1 : ZX nMid 0), 
  zx1 ∝ ⊙ zx1 -> zx0 ⥈ zx1 ∝ zx0 ⟷ zx1.
Proof.
  intros.
  unfold hadamard_edge.
  rewrite ZX_Compose_assoc.
  rewrite ColorSwap_HadamardPass.
  remove_empty.
  rewrite <- H.
  reflexivity.
Qed.

Lemma H_edge_cap : forall nOut (zx : ZX 2 nOut), ⊂ ⥈ zx ∝ ⊂ ⟷ zx.
Proof.
  intros.
  apply H_edge_ColorSwap_inv_l.
  reflexivity.
Qed.

Lemma H_edge_cup : forall nIn (zx : ZX nIn 2), zx ⥈ ⊃ ∝ zx ⟷ ⊃.
Proof.
  intros.
  apply H_edge_ColorSwap_inv_r.
  reflexivity.
Qed.

Lemma H_edge_empty_l : forall nOut (zx : ZX 0 nOut), ⦰ ⥈ zx ∝ ⦰ ⟷ zx.
Proof.
  intros.
  apply H_edge_ColorSwap_inv_l.
  reflexivity.
Qed.

Lemma H_edge_empty_r : forall nIn (zx : ZX nIn 0), zx ⥈ ⦰ ∝ zx ⟷ ⦰.
Proof.
  intros.
  apply H_edge_ColorSwap_inv_r.
  reflexivity.
Qed.

Lemma H_edge_sandwich : forall nIn nMid0 nMid1 nOut (zx0 : ZX nIn nMid0) (zx1 : ZX nMid0 nMid1) (zx2 : ZX nMid1 nOut),
  zx0 ⥈ zx1 ⥈ zx2 ∝ zx0 ⟷ ⊙ zx1 ⟷ zx2.
Proof.
  intros.
  unfold hadamard_edge.
  assert ((zx0 ⟷ (nMid0 ↑ □) ⟷ zx1 ⟷ (nMid1 ↑ □) ⟷ zx2) ∝ (zx0 ⟷ ((nMid0 ↑ □) ⟷ zx1 ⟷ (nMid1 ↑ □)) ⟷ zx2)) by (repeat rewrite <- ZX_Compose_assoc; reflexivity).
  rewrite H.
  rewrite ColorSwap_HadamardPass.
  assert ((⊙ zx1 ⟷ (nMid1 ↑ □) ⟷ (nMid1 ↑ □)) ∝ (⊙ zx1 ⟷ ((nMid1 ↑ □) ⟷ (nMid1 ↑ □)))) by (repeat rewrite <- ZX_Compose_assoc; reflexivity).
  rewrite H0.
  rewrite nH_composition.
  rewrite nwire_r.
  reflexivity.
Qed.

Lemma H_edge_sandwich' : forall nIn nMid0 nMid1 nOut (zx0 : ZX nIn nMid0) (zx1 : ZX nMid0 nMid1) (zx2 : ZX nMid1 nOut),
  zx0 ⥈ zx1 ⥈ zx2 ∝ BiHadamard (⊙ zx0 ⟷ zx1 ⟷ ⊙ zx2).
Proof.
  intros.
  rewrite <- ColorSwap_isBiHadamard.
  rewrite <- ColorSwap_Compose.
  rewrite ColorSwap_involutive.
  rewrite <- ColorSwap_Compose.
  rewrite ColorSwap_involutive.
  apply H_edge_sandwich.
Qed.

Local Close Scope ZX_scope.
