Require Import externals.QuantumLib.Quantum.
Require Export ZX.

Lemma Z_0_eq_X_0 : ZX_semantics (@Z_Spider 1 1 0) = ZX_semantics (@X_Spider 1 1 0).
Proof.
  simpl.
  unfold Spider_Semantics_Impl; unfold bra_ket_MN.
  unfold kron_n.
  repeat rewrite kron_1_l; try auto with wf_db.
  rewrite Cexp_0.
  solve_matrix.
Qed.

Theorem identity_removal_Z : ZX_semantics (@Z_Spider 1 1 0) = ZX_semantics Wire.
Proof.
  reflexivity.
Qed.

Theorem identity_removal_X : ZX_semantics (@X_Spider 1 1 0) = ZX_semantics Wire.
Proof.
  rewrite <- Z_0_eq_X_0.
  reflexivity.
Qed.