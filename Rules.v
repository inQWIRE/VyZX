Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.VectorStates.
Require Export ZX.
Require Export Gates.
Require Export GateRules.
Require Export VyZX.Proportional.

Local Open Scope ZX_scope.

(* TODO: Move into quantum lib *)
Local Hint Rewrite Mscale_kron_dist_l Mscale_kron_dist_r Mscale_mult_dist_l Mscale_mult_dist_r Mscale_assoc : scalar_move_db.

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

Global Hint Resolve Nat.add_0_r : program_db.
Global Hint Resolve Nat.add_assoc : program_db.
Obligation Tactic := auto with program_db.

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

Lemma nwire_identity_semantics : forall n, ZX_semantics (n ↑ —) = I (2 ^ n).
Proof.
  intros.
  rewrite nStack1_n_kron.
  rewrite wire_identity_semantics.
  apply kron_n_I.
Qed.

Lemma nWire_1_Wire : (1 ↑ —) ∝ Wire.
Proof.
  prop_exist_non_zero 1.
  rewrite nwire_identity_semantics.
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
  rewrite 3 nwire_identity_semantics.
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
  rewrite nwire_identity_semantics.
  rewrite Mmult_1_l; try auto with wf_db.
  lma.
Qed.

Lemma Wire_Compose : — ⟷ — ∝ —.
Proof.
  rewrite <- nWire_1_Wire.
  apply nWire_Compose.
Qed.

Lemma wire_removal_l : forall nOut (zx : ZX 1 nOut), — ⟷ zx ∝ zx.
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  rewrite wire_identity_semantics.
  Msimpl.
  reflexivity.
Qed.

Lemma nwire_removal_l: forall n nOut (zx : ZX n nOut), (n ↑ —) ⟷ zx ∝ zx.
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  rewrite nwire_identity_semantics.
  Msimpl.
  reflexivity.
Qed.

Lemma wire_removal_r : forall nIn (zx : ZX nIn 1), zx ⟷ — ∝ zx.
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  rewrite wire_identity_semantics.
  Msimpl.
  reflexivity.
Qed.

Lemma nwire_removal_r: forall n nIn (zx : ZX nIn n), zx ⟷ (n ↑ —) ∝ zx.
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  rewrite nwire_identity_semantics.
  Msimpl.
  reflexivity.
Qed.

Ltac remove_wire := try repeat rewrite wire_removal_l;
                    try repeat rewrite nwire_removal_l;
                    try repeat rewrite wire_removal_r;
                    try repeat rewrite nwire_removal_r.

Global Hint Resolve Nat.mul_1_r : program_db.

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
  rewrite nwire_identity_semantics.
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
  rewrite nwire_identity_semantics.
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
  unfold X_semantics.
  rewrite <- 2 Mmult_assoc.
  rewrite kron_n_mult.
  rewrite MmultHH.
  rewrite kron_n_I.
  rewrite Mmult_1_l; try auto with wf_db.
Qed.

Lemma hadamard_color_change_X : forall nIn nOut α, 
  (nIn ↑ □) ⟷ (X_Spider nIn nOut α) ∝ (Z_Spider nIn nOut α) ⟷ (nOut ↑ □).
Proof.
  intros.
  prop_exist_non_zero (Cexp (PI / 4 * (INR nIn - INR nOut))).
  simpl.
  rewrite 2 nStack1_n_kron.
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
  unfold X_semantics.
  rewrite 2 Mmult_assoc.
  rewrite kron_n_mult.
  rewrite MmultHH.
  rewrite kron_n_I.
  rewrite Mmult_1_r; try auto with wf_db.
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

Lemma Z_spider_1_1_fusion_eq : forall nIn nOut α β, 
  ZX_semantics ((Z_Spider nIn 1 α) ⟷ (Z_Spider 1 nOut β)) =
  ZX_semantics (Z_Spider nIn nOut (α + β)).
Proof.
  intros.
  simpl.
  rewrite Mscale_1_l.
  prep_matrix_equality.
  unfold Mmult; simpl.
  rewrite Cplus_0_l.
  unfold Z_semantics; simpl.
  destruct (x =? 0); destruct (y =? 0); destruct (x =? 2 ^ nOut - 1); destruct (y =? 2 ^ nIn - 1);
    autorewrite with Cexp_db; C_field_simplify; reflexivity.
Qed.

Lemma Z_spider_1_1_fusion : forall nIn nOut α β, 
  (Z_Spider nIn 1 α) ⟷ (Z_Spider 1 nOut β) ∝
  Z_Spider nIn nOut (α + β).
Proof.
  prop_exist_non_zero 1.
  Msimpl.
  apply Z_spider_1_1_fusion_eq.
Qed.

Lemma Z_0_eq_X_0 : 
  Z_Spider 1 1 0 ∝ X_Spider 1 1 0.
Proof.
  prop_exist_non_zero 1.
  simpl.
  rewrite Mscale_1_l.
  unfold_spider; simpl.
  rewrite kron_1_l; auto with wf_db.
  autorewrite with Cexp_db; C_field_simplify.
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
  unfold X_semantics; simpl.
  rewrite kron_1_l; try auto with wf_db.
  unfold_spider.
  autorewrite with Cexp_db; C_field_simplify.
  solve_matrix.
Qed.

Local Definition Bi_Alg_X_Stack_2_1 : ZX 2 4 := (X_Spider 1 2 0) ↕ (X_Spider 1 2 0).
Local Definition Bi_Alg_SWAP_Stack : ZX 4 4 := — ↕ ⨉ ↕ —.
Local Definition Bi_Alg_Z_Stack_1_2 : ZX 4 2 := (Z_Spider 2 1 0) ↕ (Z_Spider 2 1 0).
Definition Bi_Alg_Z_X := Bi_Alg_X_Stack_2_1 ⟷ Bi_Alg_SWAP_Stack ⟷ Bi_Alg_Z_Stack_1_2.

Definition Bi_Alg_SWAP_Stack_Semantics : Matrix 16 16 :=
  fun x y =>
  match x, y with
  | 0, 0 | 1, 1 | 4, 2 | 5, 3 | 2, 4 | 3, 5 | 6, 6 | 7, 7 
  | 8, 8 | 9, 9 | 12, 10 | 13, 11 | 10, 12 | 11, 13 | 14, 14 | 15, 15 => 1
  | _, _ => 0
  end.

Theorem BiAlgebra_rule_Z_X : 
  (Z_Spider 2 1 0) ⟷ (X_Spider 1 2 0) ∝ Bi_Alg_Z_X.
Proof.
  prop_exist_non_zero 4.
  simpl.
  rewrite ZX_SWAP_is_swap, wire_identity_semantics.
  autorewrite with scalar_move_db.
  prep_matrix_equality.
  unfold scale; unfold Mmult; simpl.
  repeat rewrite Cmult_0_r.
  repeat rewrite Cmult_0_l.
  repeat rewrite Cplus_0_l.
  repeat rewrite Cplus_0_r.
  repeat rewrite Cmult_1_l.
  unfold I; unfold swap; unfold kron; simpl.
  repeat rewrite Cmult_0_r.
  repeat rewrite Cmult_0_l.
  repeat rewrite Cmult_1_l.
  repeat rewrite Cplus_0_l.
  repeat rewrite Cplus_0_r.
  Local Ltac solve_one := (
      unfold X_semantics; unfold Mmult; simpl;
      unfold hadamard; unfold I; unfold kron; unfold Z_semantics; simpl;
      C_field_simplify; try nonzero;
      autorewrite with Cexp_db; lca).
  destruct y; simpl.
  - destruct x; [ solve_one | simpl ].
    destruct x; [ solve_one | simpl ].
    destruct x; [ solve_one | simpl ].
    destruct x; [ solve_one | simpl ].
    

    rewrite (WF_X_semantics(S (S (S (S x)))) 0%nat); [ | left; simpl; lia].
    rewrite (WF_X_semantics(S (S (S (S x)))) 1%nat); [ | left; simpl; lia].
    rewrite 2 Cmult_0_l.
    
    unfold X_semantics; unfold Mmult; simpl; unfold hadamard; unfold I; unfold kron; unfold Z_semantics; simpl.
    C_field_simplify; [ | nonzero ].
    autorewrite with Cexp_db.
    C_field_simplify.

    destruct (fst (Nat.divmod x 1 2 1) =? 1) eqn:DM1.
    + rewrite (beq_nat_true _ _ DM1); simpl.
      repeat rewrite Cmult_0_r.
      repeat rewrite Cmult_0_l.
      repeat rewrite Cplus_0_l.
      destruct (snd (Nat.divmod x 1 2 1)).
      * simpl.
        repeat rewrite Rmult_0_l.
        repeat rewrite Rplus_0_r.
        repeat rewrite Rmult_0_l.
        repeat rewrite Rmult_0_r.
        lca.
        rewrite Cmult_0_l.
        C_field_simplify.

    rewrite (WF_X_semantics 3%nat 0%nat).
    rewrite Cmult_0_r.

    destruct x; [ solve_one | simpl ].
    destruct x; [ solve_one | simpl ].
    unfold X_semantics; unfold Mmult; simpl.
    unfold hadamard. rewrite kron_1_l.
    try solve_one.

    destruct x; try solve_one.
    rewrite (WF_X_semantics (S (S x)) 0%nat).
    rewrite (WF_X_semantics (S (S x)) 0%nat).


  C_field_simplify.
  Local Ltac solve_one := (
      unfold X_semantics; unfold Mmult; simpl;
      unfold hadamard; unfold I; unfold kron; unfold Z_semantics; simpl;
      C_field_simplify; try nonzero;
      autorewrite with Cexp_db; lca).
  destruct y; simpl.
  - destruct x; try solve_one.
    destruct x; try solve_one.
    destruct x; try solve_one.
    destruct x; try solve_one.
  unfold_spider.
  autorewrite with Cexp_db.
  simpl.
  repeat rewrite kron_1_l; try auto with wf_db.
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
 *)
Theorem inverse_Z_Spider : forall nIn nOut α, ZX_semantics (Z_Spider nIn nOut α) = (ZX_semantics (Z_Spider nOut nIn (-α)))†.
Proof.
  intros; simpl.
  rewrite <- Z_semantics_adj.
  rewrite adjoint_involutive.
  reflexivity.
Qed.

Theorem inverse_X_Spider : forall nIn nOut α, ZX_semantics (X_Spider nIn nOut α) = (ZX_semantics (X_Spider nOut nIn (-α)))†.
Proof.
  intros; simpl.
  rewrite <- X_semantics_adj.
  rewrite adjoint_involutive.
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

Lemma ZX_K1_Z_base : Z_Spider 1 1 PI ⟷ X_Spider 1 1 0 ∝ X_Spider 1 1 0 ⟷ Z_Spider 1 1 PI.
Proof.
  prop_exist_non_zero 1.
  Msimpl; simpl.
  prep_matrix_equality.
  unfold Mmult.
  unfold scale.
  unfold Z_semantics; simpl.
  repeat rewrite Cplus_0_l.
  destruct x; destruct y.
  - simpl; C_field_simplify; reflexivity.
  - simpl; C_field_simplify.
    destruct y.
    + simpl; C_field_simplify. unfold X_semantics; simpl.
      rewrite kron_1_l; try auto with wf_db.
      unfold Mmult; simpl.
      repeat rewrite Cplus_0_l.
      unfold Z_semantics; simpl.
      C_field_simplify; try nonzero.
      autorewrite with Cexp_db; lca.
    + simpl; C_field_simplify. unfold X_semantics; simpl.
      rewrite kron_1_l; try auto with wf_db.
      unfold Mmult; simpl.
      lca.
  - simpl; C_field_simplify.
    destruct x.
    + simpl; C_field_simplify.
      unfold X_semantics; simpl.
      rewrite kron_1_l; try auto with wf_db.
      unfold Mmult; simpl.
      unfold Z_semantics; simpl.
      C_field_simplify; try nonzero.
      autorewrite with Cexp_db.
      lca.
    + simpl; C_field_simplify.
      unfold X_semantics; simpl.
      rewrite kron_1_l; try auto with wf_db.
      unfold Mmult.
      unfold Z_semantics; simpl.
      C_field_simplify; try nonzero; lca.
  - destruct x; destruct y.
    + simpl. lca.
    + simpl. unfold X_semantics; simpl.
      rewrite kron_1_l; try auto with wf_db.
      lca.
    + simpl. unfold_spider; unfold Mmult; simpl.
      C_field_simplify. 
      rewrite kron_1_l; try auto with wf_db.
      unfold hadamard; simpl; lca.
    + simpl. lca.
Qed.
(*
Lemma ZX_K2_Z {α} : Z_Spider 1 1 PI ⟷ X_Spider 1 1 α ∝ X_Spider 1 1 (-α) ⟷ Z_Spider 1 1 PI.
Proof.
  prop_exist_non_zero 1; Msimpl.
  rewrite <- adjoint_involutive.
  rewrite <- ZX_semantics_Adjoint_comm.
  simpl.
 *)

Transparent ZX_Z.
Transparent ZX_X.
(*
Lemma Y_colorswap : ⊙ ZX_Y ∝ ZX_Y.
Proof.
  unfold ZX_Y; unfold ZX_Z; unfold ZX_X.
  simpl.
Qed.
 *)
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
(* 
Local Definition Bi_Alg_Z_Stack_2_1 : ZX 2 4 := (Z_Spider 1 2 0) ↕ (Z_Spider 1 2 0).
Local Definition Bi_Alg_X_Stack_1_2 : ZX 4 2 := (X_Spider 2 1 0) ↕ (X_Spider 2 1 0).
Definition Bi_Alg_X_Z := Bi_Alg_Z_Stack_2_1 ⟷ Bi_Alg_SWAP_Stack ⟷ Bi_Alg_X_Stack_1_2.
Theorem BiAlgebra_rule_X_Z : (X_Spider 2 1 0) ⟷ (Z_Spider 1 2 0) ∝ Bi_Alg_X_Z.
Proof.
  unfold Bi_Alg_X_Z, Bi_Alg_Z_Stack_2_1, Bi_Alg_X_Stack_1_2.
  swap_colors_of BiAlgebra_rule_Z_X.
Qed.
 *)

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
  simpl; Msimpl.
  rewrite ZX_H_is_H.
  autorewrite with scalar_move_db.
  repeat rewrite <- Mscale_assoc.
  apply Mscale_simplify; try reflexivity.
  apply Mscale_simplify; try reflexivity.
  unfold Z_semantics.
  solve_matrix.
  - destruct x; simpl.
    + destruct y; simpl.
      * lca.
      * lca.
    + destruct y; simpl.
      * destruct x; simpl.
        -- lca.
        -- lca.
      * destruct x; simpl.
        -- destruct y.
           ++ lca.
           ++ lca.
        -- destruct y.
           ++ lca.
           ++ lca.
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

Lemma H_edge_H_removal_l : forall nOut (zx : ZX 1 nOut), □ ⥈ zx ∝ zx.
Proof.
  intros.
  unfold hadamard_edge.
  simpl; remove_empty.
  rewrite ZX_H_H_is_Wire.
  remove_wire.
  reflexivity.
Qed.

Lemma H_edge_nH_removal_l : forall n nOut (zx : ZX n nOut), (n ↑ □) ⥈ zx ∝ zx.
Proof.
  intros.
  unfold hadamard_edge.
  rewrite nH_composition.
  remove_wire.
  reflexivity.
Qed.
  
Lemma H_edge_H_removal_r : forall nIn (zx : ZX nIn 1), zx ⥈ □ ∝ zx.
Proof.
  intros.
  unfold hadamard_edge.
  rewrite ZX_Compose_assoc.
  simpl; remove_empty.
  rewrite ZX_H_H_is_Wire.
  remove_wire.
  reflexivity.
Qed.

Lemma H_edge_nH_removal_r : forall n nIn (zx : ZX nIn n), zx ⥈ (n ↑ □) ∝ zx.
Proof.
  intros.
  unfold hadamard_edge.
  rewrite ZX_Compose_assoc.
  rewrite nH_composition.
  remove_wire.
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
