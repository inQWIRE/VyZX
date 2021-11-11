Require Import externals.QuantumLib.Quantum.
Require Export ZX.
Require Export Gates.
Require Export GateRules.

Local Open Scope ZX_scope.

Lemma ZX_Stack_assoc : forall nIn1 nIn2 nIn3 nOut1 nOut2 nOut3 
                              (zx1 : ZX nIn1 nOut1) (zx2 : ZX nIn2 nOut2) (zx3 : ZX nIn3 nOut3),
                              ZX_semantics (Stack zx1 (Stack zx2 zx3)) = ZX_semantics (Stack (Stack zx1 zx2) zx3).
Proof.
  intros.
  simpl.
  restore_dims.
  rewrite <- kron_assoc; try auto with wf_db.
Qed.

Lemma ZX_Stack_Compose_distr : forall nIn1 nMid12 nIn3 nOut2 nMid34 nOut4 
                                      (zx1 : ZX nIn1 nMid12) (zx2 : ZX nMid12 nOut2) (zx3 : ZX nIn3 nMid34) (zx4 : ZX nMid34 nOut4),
                                      ZX_semantics (Stack (Compose zx1 zx2) (Compose zx3 zx4)) = ZX_semantics (Compose (Stack zx1 zx3) (Stack zx2 zx4)).
Proof.
  intros. 
  simpl.
  restore_dims.
  rewrite kron_mixed_product.
  reflexivity.
Qed.

Local Transparent nWire.
Lemma nwire_identity : forall n, ZX_semantics (nWire n) = I (2 ^ n).
Proof.
  intros.
  induction n.
  - trivial.
  - simpl.
    rewrite IHn.
    rewrite wire_identity_semantics.
    rewrite id_kron.
    rewrite <- plus_n_O.
    rewrite double_mult.
    reflexivity.
Qed.
Local Opaque nWire.

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

Lemma nwire_r : forall nIn nOut (zx : ZX nIn nOut), ZX_semantics (Compose zx (nWire nOut)) = ZX_semantics zx.
Proof.
  intros.
  simpl.
  rewrite nwire_identity.
  Msimpl.
  reflexivity.
Qed.

Lemma nwire_l : forall nIn nOut (zx : ZX nIn nOut), ZX_semantics (Compose (nWire nIn) zx) = ZX_semantics zx.
Proof.
  intros.
  simpl.
  rewrite nwire_identity.
  Msimpl.
  reflexivity.
Qed.

Lemma stack_wire_pad_l_r : forall nIn0 nIn1 nOut0 nOut1 (zx0 : ZX nIn0 nOut0) (zx1 : ZX nIn1 nOut1), ZX_semantics (Stack zx0 zx1) = ZX_semantics (Stack (Compose (nWire nIn0) zx0) (Compose zx1 (nWire nOut1))).
Proof.
  intros.
  simpl.
  rewrite 2 nwire_identity. 
  Msimpl.
  reflexivity.
Qed.

Lemma stack_wire_pad_r_l : forall nIn0 nIn1 nOut0 nOut1 (zx0 : ZX nIn0 nOut0) (zx1 : ZX nIn1 nOut1), ZX_semantics (Stack zx0 zx1) = ZX_semantics (Stack (Compose zx0 (nWire nOut0)) (Compose (nWire nIn1) zx1)).
Proof.
  intros.
  simpl.
  rewrite 2 nwire_identity. 
  Msimpl.
  reflexivity.
Qed.

Lemma Z_spider_fusion : forall α β, (ZX_semantics (Compose (Z_Spider 1 1 α) (Z_Spider 1 1 β))) = ZX_semantics (Z_Spider 1 1 (α + β)).
Proof.
  intros.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  simpl; Msimpl.
  rewrite Mmult_plus_distr_r, Mmult_plus_distr_l.
  rewrite <- Mmult_assoc.
  restore_dims.
  solve_matrix.
  rewrite Cexp_add.
  lca.
Qed.

Lemma X_spider_fusion : forall α β, (ZX_semantics (Compose (X_Spider 1 1 α) (X_Spider 1 1 β))) = ZX_semantics (X_Spider 1 1 (α + β)).
Proof.
  intros.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  simpl; Msimpl.
  rewrite Mmult_plus_distr_r, Mmult_plus_distr_l.
  rewrite <- Mmult_assoc.
  restore_dims.
  solve_matrix;
  rewrite Cexp_add; try C_field_simplify; try lca; try (apply C0_fst_neq; simpl; auto).
Qed.

Lemma Z_commutes_through_swap_t : forall α, ZX_semantics (Compose (Stack (Z_Spider 1 1 α) Wire) ZX_SWAP) = ZX_semantics (Compose ZX_SWAP (Stack Wire (Z_Spider 1 1 α))).
Proof.
  intros.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
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
  unfold Spider_Semantics_Impl, bra_ket_MN.
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
  unfold Spider_Semantics_Impl, bra_ket_MN.
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
  unfold Spider_Semantics_Impl, bra_ket_MN.
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
  unfold Spider_Semantics_Impl; unfold bra_ket_MN.
  unfold kron_n.
  repeat rewrite kron_1_l; try auto with wf_db.
  rewrite Cexp_0.
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
  intros α nIn; induction nIn; intro nOut; induction nOut.
  - simpl; unfold Spider_Semantics_Impl, bra_ket_MN; simpl; Msimpl.
    rewrite Cexp_0.
    rewrite Mmult_plus_distr_r.
    rewrite 2 Mmult_plus_distr_l.
    Msimpl.
    solve_matrix.
    rewrite Cexp_mul_neg_l.
    lca.
  - simpl.
Abort.

Theorem Hopf_rule_Z_X : ZX_semantics (Compose (Z_Spider 1 2 0) (X_Spider 2 1 0)) = (/ C2) .* ZX_semantics (Compose (Z_Spider 1 0 0) (X_Spider 0 1 0)).
Proof.
  intros.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  simpl.
  repeat rewrite kron_1_l; try auto with wf_db.
  repeat rewrite Mmult1_l.
  repeat rewrite Mmult1_r.
  repeat rewrite Cexp_0.
  repeat rewrite Mscale_1_l.
  solve_matrix.
Qed.

Theorem Hopf_rule_X_Z : ZX_semantics (Compose (X_Spider 1 2 0) (Z_Spider 2 1 0)) = (/ C2) .* ZX_semantics (Compose (X_Spider 1 0 0) (Z_Spider 0 1 0)).
Proof.
  intros.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  simpl.
  repeat rewrite kron_1_l; try auto with wf_db.
  repeat rewrite Mmult1_l.
  repeat rewrite Mmult1_r.
  repeat rewrite Cexp_0.
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
  unfold Spider_Semantics_Impl, bra_ket_MN.
  rewrite Cexp_0.
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
  unfold Spider_Semantics_Impl, bra_ket_MN.
  rewrite Cexp_0.
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
  unfold Spider_Semantics_Impl.
  unfold bra_ket_MN.
  rewrite Mplus_adjoint, Mscale_adj.
  rewrite 2 Mmult_adjoint.
  rewrite 2 kron_n_adjoint; try auto with wf_db.
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
  unfold Spider_Semantics_Impl.
  unfold bra_ket_MN.
  rewrite Mplus_adjoint, Mscale_adj.
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

Local Close Scope ZX_scope.
