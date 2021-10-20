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

Theorem Z_to_X_with_H_Outputs : forall n m α, ZX_semantics (@Z_Spider n (m * 1) α) = ZX_semantics (Compose (@X_Spider n (m * 1) α) (nStack ZX_H m)).
Proof.
  intro n.
  induction n; intro m; induction m; intros.
  - simpl; unfold Spider_Semantics_Impl; unfold bra_ket_MN; solve_matrix.
Abort.