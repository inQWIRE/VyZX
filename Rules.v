Require Import externals.QuantumLib.Quantum.
Require Export ZX.
Require Export Gates.
Require Export GateRules.

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
