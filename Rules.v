Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.VectorStates.
Require Export ZX.
Require Export Gates.
Require Export GateRules.
Require Export VyZX.Proportional.

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

Lemma ZX_SWAP_self_inverse : ⨉ ⟷ ⨉ ∝ — ↕ —.
Proof.
  intros.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  rewrite wire_identity_semantics.
  restore_dims.
  rewrite swap_swap.
  rewrite id_kron.
  easy.
Qed.

Local Transparent ZX_3_CNOT_SWAP.
Lemma ZX_3_CNOT_SWAP_is_swap : ZX_3_CNOT_SWAP ∝ ⨉.
Proof.
  simpl.
  prop_exist_non_zero (/ 2 * / √ 2)%C.
  2: apply Cmult_neq_0; apply nonzero_div_nonzero; nonzero.
  simpl.
  rewrite ZX_CNOT_is_cnot.
  rewrite wire_identity_semantics.
  unfold_spider.
  autorewrite with Cexp_db.
  simpl.
  Msimpl.
  solve_matrix;
  C_field_simplify; try lca; try nonzero.
Qed.
Local Opaque ZX_3_CNOT_SWAP.

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


Print X_Spider.
(*
Lemma bi_pi_rule : forall nIn nOut α, 
  (nStack1 nIn (Z_Spider 1 1 PI)) ⟷ (X_Spider nIn nOut α) ⟷ (nStack1 nOut (Z_Spider 1 1 PI)) ∝
  X_Spider nIn nOut α.
Proof.
  intros.
  prop_exist_non_zero 1.
  rewrite Mscale_1_l.
  simpl.
  rewrite 2 nStack1_n_kron.
  unfold Mmult.
  prep_matrix_equality.
  simpl.
  unfold Z_semantics.
  unfold kron.
  bdestruct (x =? 0); bdestruct (y =? 0).
  - subst; simpl.
    unfold Mmult.
    Locate "Σ^".
    unfold kron.
    simpl.

  prep_matrix_equality.
  unfold Mmult.
  Msimpl.
  unfold X_semantics.
  simpl.
  repeat rewrite kron_1_l; try auto with wf_db.
  unfold Mmult.
  simpl.
  
   simpl.*)

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
  assert (expnonzero : forall a, exists b, (2 ^ a + (2 ^ a + 0) - 1)%nat = S b).
  { 
    intros.
    destruct (2^a)%nat eqn:E.
      - contradict E.
        apply Nat.pow_nonzero; easy.
      - simpl.
        rewrite <- plus_n_Sm.
        exists (n + n)%nat.
        lia.
  }
  intros.
  prep_matrix_equality.
  simpl.
  unfold Mmult.
  simpl.
  rewrite Cplus_0_l.
  destruct nIn, nOut.
  - simpl.
    destruct x,y; [simpl; autorewrite with Cexp_db | | | ]; lca.
  - destruct x,y; simpl; destruct (expnonzero nOut); rewrite H; [ lca | lca | | ].
    + destruct (x =? x0).
      * simpl.
        autorewrite with Cexp_db.
        lca.
      * simpl.
        lca.
    + destruct (x =? x0); lca.
  - destruct x,y; simpl; destruct (expnonzero nIn); rewrite H; [lca | | lca | lca].
    + destruct (y =? x); [autorewrite with Cexp_db | ]; lca.
  - destruct x,y; simpl; destruct (expnonzero nIn), (expnonzero nOut); rewrite H,H0; [lca | lca | | ].
    + destruct (x =? x1); lca.
    + destruct (x =? x1), (y =? x0); [| lca | lca | lca].
      autorewrite with Cexp_db.
      lca.
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

Fixpoint build_left_rec (nIn : nat) (α : R) : ZX (S nIn) 1 := 
 match nIn with
  | 0   => Z_Spider 1 1 α
  | S l => (Z_Spider 2 1 0) ↕ (l ↑ Wire) ⟷ build_left_rec l (α)
 end.

Definition build_left (nIn : nat) (α : R) : ZX nIn 1 :=
  match nIn with
  | 0 => Z_Spider 0 1 α
  | S k => build_left_rec k α
  end.

Lemma Grow_Z_Left_1 : forall n α,
  Z_Spider (S (S n)) 1 α ∝ ((Z_Spider 2 1 0) ↕ (n ↑ Wire)) ⟷ (Z_Spider (S n) 1 α).
Proof.
  intros.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  rewrite nwire_identity_semantics.
  unfold Mmult.
  prep_matrix_equality.
  destruct x,y.
  - unfold Z_semantics.
    simpl. 
    destruct (2 ^ n)%nat eqn:E.
    + contradict E; apply Nat.pow_nonzero; easy.
    + rewrite plus_0_r.
      rewrite <- plus_n_Sm.
      simpl.
      C_field_simplify.
      induction (n0 + n0)%nat.
      * simpl.
        C_field_simplify.
        unfold kron.
        simpl.
        rewrite Nat.sub_diag.
        unfold I.
        simpl.
        lca.
      * simpl.
        rewrite <- IHn1.
        lca.
  - unfold Z_semantics.
    simpl.
    destruct (2^n)%nat eqn:E.
    + contradict E; apply Nat.pow_nonzero; easy.
    + rewrite plus_0_r.
      rewrite <- plus_n_Sm.
      rewrite plus_Sn_m.
      induction (n0 + n0)%nat.
      * simpl.
        rewrite Cmult_0_l.
        rewrite Cplus_0_l.
        rewrite Cplus_0_r.
        rewrite Cmult_1_l.
        unfold kron.
        rewrite andb_false_l.
        bdestruct (S y mod S n0 =? 0).
        -- rewrite H.
           unfold I.
           rewrite <- Nat.div_exact in H; [| auto].
           destruct (S y / S n0)%nat.
           ++ rewrite Nat.mul_0_r in H.
              discriminate H.
           ++ lca.
        -- unfold I.
           destruct (S y mod S n0)%nat.
           ++ contradict H.
              reflexivity.
           ++ simpl.
              rewrite Nat.sub_diag.
              simpl; lca.
      * simpl.
        simpl in IHn1.
        rewrite <- IHn1.
        lca.
  - unfold Z_semantics.
    replace (0 =? 2^ S (S n) - 1) with false.
    + rewrite andb_false_r.
      symmetry.
      apply Csum_0; intros.
      destruct x.
      * rewrite andb_true_l.
        unfold kron.
        rewrite Nat.div_0_l; [| apply Nat.pow_nonzero; auto].
        bdestruct (x0 =? 2 ^ S n - 1).
        -- rewrite H.
           rewrite Nat.mod_0_l; [| apply Nat.pow_nonzero; auto].
           rewrite andb_false_r.
           simpl.
           rewrite plus_0_r.
           rewrite <- Nat.add_sub_assoc.
           ++ replace (2 ^ n)%nat with (1 * 2 ^ n)%nat at 1 by apply Nat.mul_1_l.
              rewrite Nat.div_add_l; [| apply Nat.pow_nonzero; easy].
              lca.
           ++ auto.
              assert (prf : forall n, (1 <= 2^n)%nat ).
              { induction n0.
                - auto.
                - transitivity (2 ^ n0)%nat; [ assumption |].
                  rewrite Nat.pow_succ_r; [| apply Nat.le_0_l].
                  apply le_n_2n. }
              apply prf.
        -- lca.
      * rewrite andb_false_l.
        lca.
    + rewrite Nat.pow_succ_r'.
      destruct (2^S n)%nat eqn:E; [ contradict E; apply Nat.pow_nonzero; auto |].
      rewrite Nat.mul_succ_l.
      rewrite Nat.mul_1_l.
      rewrite <- plus_n_Sm.
      reflexivity.
  - unfold Z_semantics.
    bdestruct (x =? 0); bdestruct (S y =? 2 ^ S (S n) - 1).
    + rewrite H, H0.
      rewrite andb_true_l.
      replace (1 =? 2 ^ 1 - 1)%nat with true by reflexivity.
      rewrite Cexp_0.
      replace (2 ^ 1 - 1)%nat with 1%nat by reflexivity.
      replace (2 ^ 2 - 1)%nat with 3%nat by reflexivity.
      rewrite plus_0_r.
      unfold kron.
      subst.
      replace (2 ^ S (S n))%nat with (2^n + 2^n + 2^n + 2^n)%nat.
      * rewrite <- Nat.add_sub_assoc.
        -- replace (2 ^ n + 2 ^ n + 2 ^ n)%nat with (3 * 2 ^ n)%nat.
           rewrite Nat.div_add_l; [| apply Nat.pow_nonzero; auto].
           rewrite Nat.div_small.
           rewrite plus_0_r.
           rewrite Nat.add_mod; [| apply Nat.pow_nonzero; auto].
           rewrite Nat.mod_mul; [| apply Nat.pow_nonzero; auto].
           rewrite Nat.add_0_l.
           rewrite Nat.mod_mod; [| apply Nat.pow_nonzero; auto].
           assert (simplifyExpr :
                    (fun y0 : nat =>
                     (if true && (y0 =? 2 ^ S n - 1) then Cexp α else 0) *
                     (match (y0 / 2 ^ n)%nat with
                      | 0%nat | _ => if (y0 / 2 ^ n =? 1) && (3 =? 3) then C1 else 0
                      end * I (2 ^ n) (y0 mod 2 ^ n) ((2 ^ n - 1) mod 2 ^ n))) =
                    (fun y0 : nat =>
                      if (y0 =? 2 ^ S n - 1) then Cexp α else 0)).
          { apply functional_extensionality.
            intros.
            bdestruct (x =? 2 ^ S n - 1)%nat.
            - rewrite H.
              simpl.
              rewrite plus_0_r.
              rewrite <- Nat.add_sub_assoc.
              replace ((2 ^ n + (2 ^ n - 1)) / 2 ^ n)%nat with 1%nat.
              simpl.
              rewrite Nat.add_mod; [| apply Nat.pow_nonzero; auto].
              rewrite Nat.mod_same; [| apply Nat.pow_nonzero; auto].
              rewrite Nat.add_0_l.
              rewrite Nat.mod_mod; [| apply Nat.pow_nonzero; auto].
              rewrite Nat.mod_small.
              unfold I.
              rewrite Nat.eqb_refl.
              replace (2 ^ n - 1 <? 2 ^ n) with true.
              lca.
              + destruct (2 ^ n)%nat eqn:E.
                * contradict E; apply Nat.pow_nonzero; easy.
                * simpl.
                  rewrite Nat.sub_0_r.
                  symmetry.
                  assert (prf : forall a, a <? S a = true).
                  { induction a; auto. }
                  apply prf.
              + destruct (2 ^ n)%nat eqn:E; [ contradict E; apply Nat.pow_nonzero; easy |].
                simpl.
                rewrite Nat.sub_0_r.
                apply Nat.lt_succ_diag_r.
              + replace (2 ^ n + (2 ^ n - 1))%nat with (1 * 2 ^ n + (2 ^ n - 1))%nat.
                * rewrite Nat.div_add_l; [| apply Nat.pow_nonzero; auto].
                  rewrite Nat.div_small; [ lia |].
                  destruct (2 ^ n)%nat eqn:E; [contradict E; apply Nat.pow_nonzero; easy |].
                  simpl.
                  rewrite Nat.sub_0_r.
                  apply Nat.lt_succ_diag_r.
                * rewrite mult_1_l; reflexivity.
              + assert (prf : forall n, (1 <= 2^n)%nat ).
                { induction n0.
                  - auto.
                  - transitivity (2 ^ n0)%nat; [ assumption |].
                    rewrite Nat.pow_succ_r; [| apply Nat.le_0_l].
                    apply le_n_2n. }
                apply prf.
            - rewrite andb_false_r.
              lca. }
          rewrite (@Csum_eq _ _ _ simplifyExpr).
          ++ rewrite double_mult.
             rewrite <- Nat.pow_succ_r'.
             clear H0.
             clear simplifyExpr.
             induction n.
             ** lca.
             ** rewrite Nat.pow_succ_r'.
                rewrite <- double_mult.
                rewrite Csum_sum.
                replace (fun x : nat => if 2 ^ S n + x =? 2 ^ S n + 2 ^ S n - 1 then Cexp α else 0)
                   with (fun x : nat => if x =? 2 ^ S n - 1 then Cexp α else 0).
                   --- rewrite <- IHn.
                       rewrite Csum_0_bounded; [lca|].
                       intros.
                       rewrite double_mult.
                       bdestruct (x =? 2 * 2 ^ S n - 1)%nat; [| lca].
                       exfalso.
                       lia.
                   --- apply functional_extensionality.
                       intros.
                       replace (2 ^ S n + x =? 2 ^ S n + 2 ^ S n - 1)%nat
                          with (x =? 2 ^ S n - 1)%nat; [ reflexivity |].
                       clear IHn.
                       assert (prf : forall a b c : nat,
                       (b =? c)%nat = (a + b =? a + c)%nat).
                        { intros. induction a; simpl; auto; reflexivity. }
                        rewrite <- Nat.add_sub_assoc.
                        apply prf.
                        clear prf.
                        assert (prf : forall n, (1 <= 2^n)%nat ).
                          { induction n0.
                            - auto.
                            - transitivity (2 ^ n0)%nat; [ assumption |].
                              rewrite Nat.pow_succ_r; [| apply Nat.le_0_l].
                              apply le_n_2n. }
                          apply prf.
          ++ destruct (2 ^ n)%nat eqn:E; [ contradict E; apply Nat.pow_nonzero; easy | ].
             simpl.
             rewrite Nat.sub_0_r.
             auto.
          ++ lia.
        -- assert (prf : forall n, (1 <= 2^n)%nat ).
           { induction n0.
             - auto.
             - transitivity (2 ^ n0)%nat; [ assumption |].
               rewrite Nat.pow_succ_r; [| apply Nat.le_0_l].
               apply le_n_2n. }
           apply prf.
      * simpl.
        lia.
    + rewrite andb_false_r.
      rewrite H.
      simpl.
      rewrite plus_0_r.
      unfold kron.
      symmetry.
      apply Csum_0.
      intros.
      unfold I.
      (*bdestruct (x0 mod 2 ^ n =? S y mod 2 ^ n)%nat.*)
      simpl.
      bdestruct (x0 =? 2 ^ n + 2 ^ n - 1)%nat.
      * rewrite H1.
        replace ((2 ^ n + 2 ^ n - 1) / 2 ^ n)%nat with 1%nat.
        rewrite andb_true_l.
        replace ((2 ^ n + 2 ^ n - 1) mod 2 ^ n)%nat with (2 ^ n - 1)%nat.
        -- bdestruct (2 ^ n -1 =? S y mod 2 ^ n)%nat; bdestruct (S y / 2 ^ n =? 3)%nat.
          ++ exfalso.
             specialize (Nat.div_mod_eq (S y) (2^n)) as dmeq.
             rewrite H3 in dmeq.
             rewrite <- H2 in dmeq.
             apply H0.
             simpl.
             repeat rewrite plus_0_r.
             rewrite Nat.mul_comm in dmeq.
             simpl in dmeq.
             lia.
          ++ lca.
          ++ lca.
          ++ lca.
        -- rewrite <- Nat.add_sub_assoc.
           rewrite Nat.add_mod; [| apply Nat.pow_nonzero; auto].
           rewrite Nat.mod_same; [| apply Nat.pow_nonzero; auto].
           simpl.
           rewrite Nat.mod_mod; [| apply Nat.pow_nonzero; auto].
           symmetry.
           apply Nat.mod_small.
           destruct (2 ^ n)%nat eqn:E;[ contradict E; apply Nat.pow_nonzero; auto | ].
           simpl.
           rewrite Nat.sub_0_r.
           auto.
           assert (prf : forall n, (1 <= 2^n)%nat ).
             { induction n0.
               - auto.
               - transitivity (2 ^ n0)%nat; [ assumption |].
                 rewrite Nat.pow_succ_r; [| apply Nat.le_0_l].
                 apply le_n_2n. }
           apply prf.
        -- replace (2 ^ n + 2 ^ n - 1)%nat with (1 * 2 ^ n + (2 ^ n - 1))%nat by lia.
           rewrite Nat.div_add_l; [| apply Nat.pow_nonzero; auto].
           rewrite Nat.div_small.
           lia.
           destruct (2 ^ n)%nat eqn:E; [ contradict E; apply Nat.pow_nonzero; auto |].
           simpl.
           rewrite Nat.sub_0_r.
           auto.
      * lca.
    + destruct x; [ destruct H; reflexivity | ].
      simpl.
      unfold kron.
      rewrite Csum_0; [ reflexivity | ].
      intros.
      lca.
    + rewrite andb_false_r.
      destruct x; [ destruct H; reflexivity | ].
      simpl.
      unfold kron.
      rewrite Csum_0; [ reflexivity | ].
      intros.
      lca.
Qed.


Lemma Grow_Z_Right_1 : forall n α,
  Z_Spider 1 (S (S n)) α ∝ (Z_Spider 1 (S n) α) ⟷ ((Z_Spider 1 2 0) ↕ (n ↑ Wire)).
Proof.
  intros.
  replace (Z_Spider 1 (S (S n))%nat α) with ((Z_Spider (S (S n))%nat 1 α)⊺) by reflexivity.
  rewrite Grow_Z_Left_1.
  simpl.
  rewrite nstack1_transpose.
  rewrite zx_transpose_wire.
  reflexivity.
Qed.

Lemma Grow_Z_left : forall nIn nOut α,
  Z_Spider (S (S nIn)) nOut α ∝ ((Z_Spider 2 1 0) ↕ (nIn ↑ Wire)) ⟷ (Z_Spider (S nIn) nOut α).
Proof.
  intros.
  replace α%R with (0 + α)%R at 1 by lra.
  rewrite <- Z_spider_1_1_fusion.
  rewrite Grow_Z_Left_1.
  rewrite ZX_Compose_assoc.
  rewrite Z_spider_1_1_fusion.
  replace (0+α)%R with α%R by lra.
  reflexivity.
Qed.

Lemma Grow_Z_Right : forall nIn nOut α,
  Z_Spider nIn (S (S nOut)) α ∝ (Z_Spider nIn (S nOut) α) ⟷ ((Z_Spider 1 2 0) ↕ (nOut ↑ Wire)).
Proof.
  intros.
  replace α%R with (0 + α)%R at 1 by lra.
  rewrite <- Z_spider_1_1_fusion.
  rewrite Grow_Z_Right_1.
  rewrite <- ZX_Compose_assoc.
  rewrite Z_spider_1_1_fusion.
  replace (0+α)%R with α%R by lra.
  reflexivity.
Qed.

Lemma bp_left : 
  (2 ↑ (X_Spider 1 1 PI)) ⟷ Z_Spider 2 1 0 ∝
  Z_Spider 2 1 0 ⟷ X_Spider 1 1 PI.
Proof. 
  simpl.
  remove_empty.
  specialize (WF_ZX _ _ (X_Spider 1 1 PI ↕ X_Spider 1 1 PI ⟷ Z_Spider 2 1 0)) as wfLeft.
  specialize (WF_ZX _ _ (Z_Spider 2 1 0 ⟷ X_Spider 1 1 PI)) as wfRight.
  unfold WF_Matrix in wfLeft, wfRight.
  simpl in wfLeft, wfRight.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  prep_matrix_equality.
  destruct x, y.
  - admit.
  - destruct y.
    + admit.
    + destruct y.
      * admit.
      * destruct y.
        -- admit.
        -- rewrite wfLeft; [| right ].
           rewrite wfRight; [| right ].
           reflexivity.
           all: destruct y.
           1,3: auto.
           all: constructor;
                repeat apply le_n_S;
                apply Nat.le_0_l.
  - destruct x.
    + admit.
    + rewrite wfLeft; [| left ].
      rewrite wfRight; [| left ].
      reflexivity.
      all: destruct x; auto;
           constructor;
           repeat apply le_n_S;
           apply Nat.le_0_l.
  - destruct x.
    + admit.
    + rewrite wfLeft; [| left ].
      rewrite wfRight; [| left ].
      reflexivity.
      all: destruct x; auto;
           constructor;
           repeat apply le_n_S;
           apply Nat.le_0_l.
Admitted.

Lemma bp_right :
  Z_Spider 1 2 0 ⟷ (2 ↑ X_Spider 1 1 PI) ∝
  X_Spider 1 1 PI ⟷ Z_Spider 1 2 0.
Proof.
  rewrite <- zx_transpose_involutive.
  replace ((Z_Spider 1 2 0 ⟷ (2 ↑ X_Spider 1 1 PI)) ⊺)
  with ((2 ↑ (X_Spider 1 1 PI)) ⟷ Z_Spider 2 1 0)
  by reflexivity.
  rewrite bp_left.
  reflexivity.
Qed.

Theorem bi_pi_rule : forall nIn nOut α,
  ((S nIn) ↑ (X_Spider 1 1 PI)) ⟷ Z_Spider (S nIn) (S nOut) α ⟷ ((S nOut) ↑ (X_Spider 1 1 PI))
  ∝ Z_Spider (S nIn) (S nOut) α.
Proof.
  induction nIn, nOut; intros.
  - simpl.
    remove_empty.
    admit.
  - rewrite Grow_Z_Right.
    simpl.
    rewrite ZX_Stack_assoc.
    rewrite <- ZX_Stack_Compose_distr.
    simpl.
    remove_empty.


  - intros; simpl.
    replace (Z_Spider 0 0 α) with Empty.
    + prop_exist_non_zero 1; solve_matrix.
      destruct x; auto.
      rewrite andb_false_r; auto.
    + simpl.

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
(*
Definition SWAP_Stack_semantics : Matrix 16 16 :=
  fun x y =>
  match x, y with
  | 0, 0 | 1, 1 | 4, 2 | 5, 3 | 2, 4 | 3, 5 | 6, 6 | 7, 7 => C1
  | 8, 8 | 9, 9 | 12, 10 | 13, 11 | 10, 12 | 11, 13 | 14, 14 | 15, 15 => C1
  | _, _ => 0
  end.

Lemma SWAP_Stack_semantics_correct : I 2 ⊗ swap ⊗ I 2 = SWAP_Stack_semantics.
Proof.
  prep_matrix_equality.
  unfold I, swap, kron, SWAP_Stack_semantics.
  destruct x,y.
  - lca.
  - simpl.
    destruct (Nat.divmod y 1 0 0) eqn:E1.
    simpl.
    destruct (Nat.divmod n 3 0 3) eqn:E2.
    destruct n1, n2.
    + lca.
    + admit.
    + lca.
    + lca.
  - simpl.
    destruct (Nat.divmod x 1 0 0).
    simpl.
    destruct (Nat.divmod n 3 0 3).
    simpl.
    destruct n1, n2.
 *)
Theorem BiAlgebra_rule_Z_X : 
 (Z_Spider 2 1 0) ⟷ (X_Spider 1 2 0) ∝ Bi_Alg_Z_X.
Proof.
 prop_exist_non_zero (√ 2).
 simpl.
 rewrite <- ZX_Z_is_Z_semantics. 
 rewrite <- ZX_X_is_X_semantics.
 rewrite wire_identity_semantics.
 repeat rewrite ZX_semantics_equiv.
 unfold_dirac_spider.
 autorewrite with Cexp_db.
 simpl.
 repeat rewrite kron_1_l; try auto with wf_db.
 repeat rewrite Mscale_1_l.
 repeat rewrite Mmult_adjoint.
 repeat rewrite hadamard_sa.
 repeat rewrite ket2bra.
 autorewrite with scalar_move_db.
 solve_matrix.
 all : C_field_simplify; [reflexivity | nonzero].
Qed.

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

Lemma ColorSwap_Cup : ⊃ ∝ ⊙ (⊃).
Proof. intros. reflexivity. Qed.

Lemma ColorSwap_Cap : ⊂ ∝ ⊙ (⊂).
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
    remove_empty.
    symmetry.
    prop_exist_non_zero (4 *
    (Cexp (PI / 4) * / √ 2 * (Cexp (PI / 4) * / √ 2) *
     (Cexp (PI / 4) * / √ 2 * (Cexp (PI / 4) * / √ 2)))).
    Msimpl.
    simpl.
    rewrite ZX_H_is_H.
    solve_matrix.
    apply Cmult_neq_0; [ nonzero | ].
    apply Cmult_neq_0; apply Cmult_neq_0; apply Cmult_neq_0; try nonzero.
    all: apply nonzero_div_nonzero; nonzero.
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
  simpl.
  reflexivity.
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
  rewrite wire_identity_semantics.
  simpl.
  Msimpl.
  autorewrite with scalar_move_db.
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
  rewrite wire_identity_semantics.
  simpl.
  Msimpl.
  autorewrite with scalar_move_db.
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

Lemma Cup_is_Z_spider : ⊃ ∝ Z_Spider 2 0 0.
Proof.
  intros.
  prop_exist_non_zero 1.
  unfold ZX_semantics.
  unfold Z_semantics.
  solve_matrix.
  autorewrite with Cexp_db.
  easy.
Qed.

Lemma Cup_is_X_spider : ⊃ ∝ X_Spider 2 0 0.
Proof.
  rewrite ColorSwap_X.
  rewrite ColorSwap_Cup.
  apply ColorSwap_lift.
  rewrite 2 ColorSwap_involutive.
  apply Cup_is_Z_spider.
Qed.

Lemma Cap_is_Z_spider : ⊂ ∝ Z_Spider 0 2 0.
Proof.
  intros.
  prop_exist_non_zero 1.
  unfold ZX_semantics.
  unfold Z_semantics.
  solve_matrix.
  autorewrite with Cexp_db.
  easy.
Qed.

Lemma Cap_is_X_spider : ⊂ ∝ X_Spider 0 2 0.
Proof.
  rewrite ColorSwap_X.
  rewrite ColorSwap_Cap.
  apply ColorSwap_lift.
  rewrite 2 ColorSwap_involutive.
  apply Cap_is_Z_spider.
Qed.

Local Close Scope ZX_scope.
