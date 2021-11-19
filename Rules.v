Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.Dirac.
Require Export ZX.
Require Export Gates.
Require Export GateRules.
Require Export Proportional.

Local Open Scope ZX_scope.
(* Fixed in a truly nightmarish way. Would need to add in StackAssocHelper
somewhere to even use. Terrible. There must be a better way. *)

Lemma StackAssocHelper :
  forall {nIn0 nIn1 nIn2 nOut0 nOut1 nOut2}
    (zx : ZX (nIn0 + nIn1 + nIn2) (nOut0 + nOut1 + nOut2)),
    ZX (nIn0 + (nIn1 + nIn2)) (nOut0 + (nOut1 + nOut2)).
Proof.
  intros.
  rewrite 2 plus_assoc.
  apply zx.
Defined.

Lemma ZXSemantics_Ignore_StackAssoc : 
  forall {nIn0 nIn1 nIn2 nOut0 nOut1 nOut2}
    (zx0 : ZX nIn0 nOut0) (zx1 : ZX nIn1 nOut1) (zx2 : ZX nIn2 nOut2),
    ZX_semantics (StackAssocHelper (Stack (Stack zx0 zx1) zx2)) = ZX_semantics (Stack (Stack zx0 zx1) zx2).
Proof.
  intros.
  unfold StackAssocHelper.
  simpl; rewrite 2 Nat.add_assoc; simpl.
  restore_dims.
  reflexivity.
Qed.

Lemma ZX_Stack_assoc : 
  forall {nIn1 nIn2 nIn3 nOut1 nOut2 nOut3}
    (zx1 : ZX nIn1 nOut1) (zx2 : ZX nIn2 nOut2) (zx3 : ZX nIn3 nOut3),
    StackAssocHelper (Stack (Stack zx1 zx2) zx3) ∝ Stack zx1 (Stack zx2 zx3).
Proof.
  intros.
  exists 1.
  split; try apply C1_neq_C0.
  - rewrite ZXSemantics_Ignore_StackAssoc.
    rewrite Mscale_1_l.
    simpl.
    restore_dims.
    rewrite kron_assoc; try auto with wf_db.
Qed.

Lemma ZX_Stack_assoc_eq :
forall nIn1 nIn2 nIn3 nOut1 nOut2 nOut3 
  (zx1 : ZX nIn1 nOut1) (zx2 : ZX nIn2 nOut2) (zx3 : ZX nIn3 nOut3),
  ZX_semantics (Stack (Stack zx1 zx2) zx3) = ZX_semantics (Stack zx1 (Stack zx2 zx3)).
Proof.
  intros.
  simpl.
  restore_dims.
  rewrite kron_assoc; try auto with wf_db.
Qed.

Lemma ZX_Compose_assoc : forall nIn nMid1 nMid2 nOut
                              (zx1 : ZX nIn nMid1) (zx2 : ZX nMid1 nMid2) (zx3 : ZX nMid2 nOut),
     Compose (Compose zx1 zx2) zx3 ∝ Compose zx1 (Compose zx2 zx3).
Proof.
  intros.
  simpl.
  prop_exist_non_zero 1.
  simpl.
  rewrite Mmult_assoc.
  lma.
Qed.

Lemma ZX_Semantics_Stack_Empty_l : forall {nIn nOut} (zx : ZX nIn nOut),
  Stack Empty zx ∝ zx.
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

Program Lemma ZX_test : forall a b c (zx : ZX (a + b + c) (a + (b + c))) (zx' : ZX (a + (b + c)) (a + b + c)),
  zx ∝ zx'.
Proof.
  intros.
  unfold eq_rect.
  destruct (eq_sym _).
  destruct (Nat.add_assoc _ _ _).
Abort.


Program Lemma ZX_Semantics_Stack_Empty_r : forall {nIn nOut : nat} (zx : ZX nIn nOut),
  Stack zx Empty ∝ zx.
Proof.
  intros.
  unfold proportional.
  restore_dims.
  prop_exist_non_zero 1.
  restore_dims.
  simpl.
  Msimpl.
  restore_dims.
  unfold eq_rect.
  destruct (plus_n_O _).
  destruct (plus_n_O _).
  trivial.
Qed.


Lemma ZX_Semantics_Compose_Empty_r : forall {nIn} (zx : ZX nIn 0),
  Compose zx Empty ∝ zx.
Proof. 
  intros.
  prop_exist_non_zero 1.
  simpl.  
  restore_dims.
  rewrite Mmult_1_l; try auto with wf_db.
  lma.
Qed.

  
Lemma ZX_Semantics_Compose_Empty_l : forall {nOut} (zx : ZX 0 nOut),
  Compose Empty zx ∝ zx.
Proof. 
  intros.
  prop_exist_non_zero 1.
  simpl. 
  restore_dims.
  rewrite Mmult_1_r; try auto with wf_db.
  lma.
Qed.

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
  simpl.
  restore_dims.
  rewrite kron_mixed_product.
  lma.
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
  unfold proportional.
  prop_exist_non_zero 1.
  rewrite nwire_identity.
  rewrite wire_identity_semantics.
  lma.
Qed.

Lemma nWire_Stack : forall n m, Stack (nWire n) (nWire m) ∝ nWire (n + m).
Proof.
  unfold proportional.
  prop_exist_non_zero 1.
  simpl.
  rewrite 3 nwire_identity.
  rewrite id_kron.
  rewrite Nat.pow_add_r.
  lma'.
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
  unfold proportional.
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
Local Opaque nWire.



(* Cexp (PI / 2 * (INR n)) *)
Lemma nH_composition : forall n, Compose (nH n) (nH n) ∝ nWire n.
Proof.
  intros.
  apply prop_c_to_prop.
  exists 0%nat; exists 0%nat; exists ((PI / 2 * (INR n))%R).
  simpl.
  rewrite nStack1_n_kron.
  restore_dims.
  rewrite kron_n_mult.
  rewrite nwire_identity.
  replace (ZX_semantics ZX_H × (ZX_semantics ZX_H)) with (ZX_semantics (Compose ZX_H ZX_H)) by reflexivity.
  rewrite ZX_H_H_is_Wire.
  rewrite Mscale_kron_n_distr_r.
  rewrite wire_identity_semantics.
  rewrite kron_n_I.
  rewrite Cexp_pow.
  lma.
Qed.

Lemma nStack1_compose : forall (zx0 zx1 : ZX 1 1) n, 
  nStack1 (Compose zx0 zx1) n ∝ Compose (nStack1 zx0 n) (nStack1 zx1 n).
Proof.
  intros.
  exists 1.
  split; try apply C1_neq_C0.
  induction n.
  - simpl. Msimpl. reflexivity.
  - simpl.
    rewrite IHn.
    restore_dims.
    rewrite kron_mixed_product.
    rewrite 2 Mscale_1_l.
    rewrite ZX_semantics_Compose.
    reflexivity.
Qed. 

Lemma wire_stack_identity : forall n, ZX_semantics (nStack Wire n) = I (2 ^ n).
Proof.
    intros.
    induction n.
    - trivial.
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
  Compose zx (nWire nOut) ∝ zx.
Proof.
  intros.
  simpl.
  exists 1.
  split.
  - simpl.
    rewrite nwire_identity.
    Msimpl.
    reflexivity.
  - apply C1_neq_C0.
Qed.

Lemma nwire_l : forall nIn nOut (zx : ZX nIn nOut), 
  Compose (nWire nIn) zx ∝ zx.
Proof.
  intros.
  simpl.
  exists 1.
  split.
  - simpl.
    rewrite nwire_identity.
    Msimpl.
    reflexivity.
  - apply C1_neq_C0.
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

(*(Cexp (PI / 4 * (INR nIn - INR nOut)))*)
Lemma hadamard_color_change_Z : forall nIn nOut α, Compose (nH nIn) (Z_Spider nIn nOut α) ∝ Compose (X_Spider nIn nOut α) (nH nOut).
Proof.
  intros.
  simpl.
  exists (Cexp (PI / 4 * (INR nIn - INR nOut))).
  split.
  - simpl.
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
    restore_dims.
    repeat rewrite <- Mmult_assoc.
    rewrite MmultHH.
    Msimpl.
    apply Mplus_simplify;
      try (apply Mscale_simplify; try reflexivity);
      apply Mmult_simplify; try reflexivity;
                            try (rewrite hadamard_sa; unfold bra; reflexivity).
  - apply Cexp_nonzero.
Qed.

(*(Cexp (PI / 4 * (INR nIn - INR nOut))) *)
Lemma hadamard_color_change_X : forall nIn nOut α, Compose (nH nIn) (X_Spider nIn nOut α) ∝ Compose (Z_Spider nIn nOut α) (nH nOut).
Proof.
  intros.
  exists (Cexp (PI / 4 * (INR nIn - INR nOut))).
  split.
  - simpl.
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
    restore_dims.
    repeat rewrite <- Mmult_assoc.
    Msimpl.
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
  - apply Cexp_nonzero.
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

Lemma Z_spider_fusion : forall nIn nOut α β, (ZX_semantics (Compose (Z_Spider nIn 1 α) (Z_Spider 1 nOut β))) = ZX_semantics (Z_Spider nIn nOut (α + β)).
Proof.
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

Lemma X_spider_fusion : forall α β, (ZX_semantics (Compose (X_Spider 1 1 α) (X_Spider 1 1 β))) = ZX_semantics (X_Spider 1 1 (α + β)).
Proof.
  intros.
  simpl.
  unfold_spider.
  rewrite Mmult_plus_distr_r, Mmult_plus_distr_l.
  rewrite <- Mmult_assoc.
  restore_dims.
  solve_matrix;
  autorewrite with Cexp_db; try C_field_simplify; try lca; try (apply C0_fst_neq; simpl; auto).
Qed.

Lemma Z_commutes_through_swap_t : forall α, ZX_semantics (Compose (Stack (Z_Spider 1 1 α) Wire) ZX_SWAP) = ZX_semantics (Compose ZX_SWAP (Stack Wire (Z_Spider 1 1 α))).
Proof.
  intros.
  simpl.
  unfold_spider.
  rewrite ZX_SWAP_is_swap.
  rewrite wire_identity_semantics.
  simpl.
  Msimpl.
  solve_matrix.
Qed.

Lemma X_commutes_through_swap_t : forall α, ZX_semantics (Compose (Stack (X_Spider 1 1 α) Wire) ZX_SWAP) = ZX_semantics (Compose ZX_SWAP (Stack Wire (X_Spider 1 1 α))).
Proof.
  intros.
  simpl.
  unfold_spider.
  rewrite ZX_SWAP_is_swap.
  rewrite wire_identity_semantics.
  simpl.
  Msimpl.
  solve_matrix.
Qed.

Lemma Z_commutes_through_swap_b : forall α, ZX_semantics (Compose (Stack Wire (Z_Spider 1 1 α)) ZX_SWAP) = ZX_semantics (Compose ZX_SWAP (Stack (Z_Spider 1 1 α) Wire)).
Proof.
  intros.
  simpl.
  unfold_spider.
  rewrite ZX_SWAP_is_swap.
  rewrite wire_identity_semantics.
  simpl.
  Msimpl.
  solve_matrix.
Qed.

Lemma X_commutes_through_swap_b : forall α, ZX_semantics (Compose (Stack Wire (X_Spider 1 1 α)) ZX_SWAP) = ZX_semantics (Compose ZX_SWAP (Stack (X_Spider 1 1 α) Wire)).
Proof.
  intros.
  simpl.
  unfold_spider.
  rewrite ZX_SWAP_is_swap.
  rewrite wire_identity_semantics.
  simpl.
  Msimpl.
  solve_matrix.
Qed.

Lemma Spiders_commute_through_swap_b : forall (zx0 zx1 : ZX 1 1),
                                       ZX_semantics (Compose (Stack Wire zx0) ZX_SWAP) = ZX_semantics (Compose ZX_SWAP (Stack zx0 Wire)) ->      
                                       ZX_semantics (Compose (Stack Wire zx1) ZX_SWAP) = ZX_semantics (Compose ZX_SWAP (Stack zx1 Wire)) ->
                                       ZX_semantics (Compose (Stack Wire (Compose zx0 zx1)) ZX_SWAP) = ZX_semantics (Compose ZX_SWAP (Stack (Compose zx0 zx1) Wire)).
Proof.
  intros.
  simpl.
  replace (ZX_semantics Wire) with (ZX_semantics (Compose Wire Wire)) by (simpl; rewrite wire_identity_semantics; Msimpl; reflexivity).
  restore_dims.
  replace (ZX_semantics zx1 × ZX_semantics zx0) with (ZX_semantics (Compose zx0 zx1)) by reflexivity.
  replace (ZX_semantics (Compose Wire Wire) ⊗ ZX_semantics (Compose zx0 zx1)) with (ZX_semantics (Stack (Compose Wire Wire) (Compose zx0 zx1))) by reflexivity.
  replace (ZX_semantics (Compose zx0 zx1) ⊗ ZX_semantics (Compose Wire Wire)) with (ZX_semantics (Stack (Compose zx0 zx1) (Compose Wire Wire))) by reflexivity.
  rewrite 2 ZX_Stack_Compose_distr.
  simpl.
  simpl in H.
  simpl in H0.
  rewrite <- Mmult_assoc.
  rewrite H0.
  rewrite Mmult_assoc.
  rewrite H.
  rewrite <- Mmult_assoc.
  reflexivity.
Qed.

Lemma Spiders_commute_through_swap_t : forall (zx0 zx1 : ZX 1 1),
                                       ZX_semantics (Compose (Stack zx0 Wire) ZX_SWAP) = ZX_semantics (Compose ZX_SWAP (Stack Wire zx0)) ->      
                                       ZX_semantics (Compose (Stack zx1 Wire) ZX_SWAP) = ZX_semantics (Compose ZX_SWAP (Stack Wire zx1)) ->
                                       ZX_semantics (Compose (Stack (Compose zx0 zx1) Wire) ZX_SWAP) = ZX_semantics (Compose ZX_SWAP (Stack Wire (Compose zx0 zx1))).
Proof.
  intros.
  simpl.
  replace (ZX_semantics Wire) with (ZX_semantics (Compose Wire Wire)) by (simpl; rewrite wire_identity_semantics; Msimpl; reflexivity).
  restore_dims.
  replace (ZX_semantics zx1 × ZX_semantics zx0) with (ZX_semantics (Compose zx0 zx1)) by reflexivity.
  replace (ZX_semantics (Compose Wire Wire) ⊗ ZX_semantics (Compose zx0 zx1)) with (ZX_semantics (Stack (Compose Wire Wire) (Compose zx0 zx1))) by reflexivity.
  replace (ZX_semantics (Compose zx0 zx1) ⊗ ZX_semantics (Compose Wire Wire)) with (ZX_semantics (Stack (Compose zx0 zx1) (Compose Wire Wire))) by reflexivity.
  rewrite 2 ZX_Stack_Compose_distr.
  simpl.
  simpl in H.
  simpl in H0.
  rewrite <- Mmult_assoc.
  rewrite H0.
  rewrite Mmult_assoc.
  rewrite H.
  rewrite <- Mmult_assoc.
  reflexivity.
Qed.

Lemma Z_0_eq_X_0 : ZX_semantics (Z_Spider 1 1 0) = ZX_semantics (X_Spider 1 1 0).
Proof.
  simpl.
  unfold_spider.
  unfold kron_n.
  repeat rewrite kron_1_l; try auto with wf_db.
  autorewrite with Cexp_db.
  solve_matrix.
Qed.

Theorem identity_removal_Z : ZX_semantics (Z_Spider 1 1 0) = ZX_semantics Wire.
Proof.
  reflexivity.
Qed.

Theorem identity_removal_X : ZX_semantics (X_Spider 1 1 0) = ZX_semantics Wire.
Proof.
  rewrite <- Z_0_eq_X_0.
  reflexivity.
Qed.

Theorem trivial_cap_cup : ZX_semantics (Compose Cap Cup) = C2 .* ZX_semantics Empty.
Proof. simpl; solve_matrix. Qed.

Definition back_forth : ZX 1 1 := Compose (Stack Wire Cap) (Stack Cup Wire).

Theorem back_forth_is_wire : ZX_semantics back_forth = ZX_semantics Wire.
Proof. 
  simpl. 
  rewrite wire_identity_semantics.
  solve_matrix.
Qed.

Definition forth_back : ZX 1 1 := Compose (Stack Cap Wire) (Stack Wire Cup).
Theorem forth_back_is_wire : ZX_semantics back_forth = ZX_semantics Wire.
Proof.
  simpl. 
  rewrite wire_identity_semantics.
  solve_matrix.
Qed.

Theorem inverse_angle_Z : forall  α nIn nOut, ZX_semantics(Compose (Z_Spider nIn 1 α) (Z_Spider 1 nOut (-α))) = ZX_semantics (Z_Spider nIn nOut 0).
Proof.
  intros.
Abort.

Theorem Hopf_rule_Z_X : ZX_semantics (Compose (Z_Spider 1 2 0) (X_Spider 2 1 0)) = (/ C2) .* ZX_semantics (Compose (Z_Spider 1 0 0) (X_Spider 0 1 0)).
Proof.
  intros.
  simpl.
  unfold_spider.
  repeat rewrite kron_1_l; try auto with wf_db.
  repeat rewrite Mmult1_l.
  repeat rewrite Mmult1_r.
  autorewrite with Cexp_db.
  repeat rewrite Mscale_1_l.
  solve_matrix.
Qed.

Theorem Hopf_rule_X_Z : ZX_semantics (Compose (X_Spider 1 2 0) (Z_Spider 2 1 0)) = (/ C2) .* ZX_semantics (Compose (X_Spider 1 0 0) (Z_Spider 0 1 0)).
Proof.
  intros.
  simpl.
  unfold_spider.
  repeat rewrite kron_1_l; try auto with wf_db.
  repeat rewrite Mmult1_l.
  repeat rewrite Mmult1_r.
  autorewrite with Cexp_db.
  repeat rewrite Mscale_1_l.
  solve_matrix.
Qed.

Local Definition Bi_Alg_X_Stack_2_1 : ZX 2 4 := Stack (X_Spider 1 2 0) (X_Spider 1 2 0).
Local Definition Bi_Alg_SWAP_Stack : ZX 4 4 := Stack Wire (Stack ZX_SWAP Wire).
Local Definition Bi_Alg_Z_Stack_1_2 : ZX 4 2 := Stack (Z_Spider 2 1 0) (Z_Spider 2 1 0).
Definition Bi_Alg_Z_X := Compose Bi_Alg_X_Stack_2_1 (Compose Bi_Alg_SWAP_Stack Bi_Alg_Z_Stack_1_2).

Theorem BiAlgebra_rule_Z_X : ZX_semantics (Compose (Z_Spider 2 1 0) (X_Spider 1 2 0)) = (C2 * C2) .* ZX_semantics Bi_Alg_Z_X.
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

Lemma Z_1_1_Wire_Cup : forall α, 
  ZX_semantics (Compose (Stack Wire (Z_Spider 1 1 α)) Cup) =
  ZX_semantics (Compose (Stack (Z_Spider 1 1 α) Wire) Cup).
Proof.
  intros.
  simpl.
  unfold_spider.
  rewrite wire_identity_semantics.
  solve_matrix.
Qed.

Lemma Z_1_1_Wire_Cap : forall α, 
  ZX_semantics (Compose Cap (Stack Wire (Z_Spider 1 1 α))) =
  ZX_semantics (Compose Cap (Stack (Z_Spider 1 1 α) Wire)).
Proof.
  intros.
  simpl.
  unfold_spider.
  rewrite wire_identity_semantics.
  solve_matrix.
Qed.

Fixpoint ColorSwap {nIn nOut} (zx : ZX nIn nOut) : ZX nIn nOut := 
  match zx with
  | X_Spider n m α  => Z_Spider n m α
  | Z_Spider n m α  => X_Spider n m α
  | Stack zx1 zx2   => Stack (ColorSwap zx1) (ColorSwap zx2)
  | Compose zx1 zx2 => Compose (ColorSwap zx1) (ColorSwap zx2)
  | otherwise       => otherwise
  end.

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

Lemma nH_Plus_Stack : forall {n0 n1},
    nH (n0 + n1) ∝ Stack (nH n0) (nH n1).
Proof.
  induction n0; intros.
  - rewrite ZX_Semantics_Stack_Empty_l; reflexivity.
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
    

Theorem ColorSwap_Lift : forall {nIn nOut} (zx0 zx1 : ZX nIn nOut),
  ColorSwap zx0 ∝ ColorSwap zx1 -> zx0 ∝ zx1.
Proof.
  intros.
  replace zx1 with (ColorSwap (ColorSwap zx1)) by apply ColorSwap_self_inverse.
  inversion H.
Admitted.

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

Transparent ZX_H.
Lemma ColorSwap_isBiHadamard : forall {nIn nOut} (zx : ZX nIn nOut),
    ColorSwap zx ∝ BiHadamard zx.
Proof.
  intros; unfold BiHadamard.
  induction zx.
  - rewrite 2 ZX_Semantics_Compose_Empty_l.
    reflexivity.
  - rewrite bi_hadamard_color_change_X.
    reflexivity.
  - rewrite bi_hadamard_color_change_Z.
    reflexivity.
  - rewrite ZX_Semantics_Compose_Empty_l.
    unfold nH.
    rewrite ZX_Semantics_Stack_Empty_r.
    clear_eq_ctx.
    simpl.
    rewrite stack_wire_pad_l_r.
    rewrite ZX_Stack_Compose_distr.
    rewrite <- ZX_Compose_assoc.
    rewrite nWire_1_Wire.
    rewrite <- H_comm_cap.
    rewrite ZX_Compose_assoc.
    rewrite <- (ZX_Stack_Compose_distr _ _ _ _ _ _ ZX_H ZX_H _ _).
    rewrite ZX_H_H_is_Wire.
    rewrite Wire_Compose.
    rewrite <- nWire_2_Stack_wire.
    rewrite nwire_r.
    reflexivity.
  - rewrite ZX_Semantics_Compose_Empty_r.
    unfold nH.
    rewrite ZX_Semantics_Stack_Empty_r.
    clear_eq_ctx.
    simpl.
    rewrite stack_wire_pad_l_r.
    rewrite ZX_Stack_Compose_distr.
    rewrite nWire_1_Wire.
    rewrite ZX_Compose_assoc.
    rewrite H_comm_cup.
    rewrite <- ZX_Compose_assoc.
    rewrite <- (ZX_Stack_Compose_distr _ _ _ _ _ _ Wire Wire ZX_H ZX_H).
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

Local Close Scope ZX_scope.
