Require Import externals.QuantumLib.Quantum.
Require Export ZX.

Theorem ket_plus_state : ZX_semantics (Z_Spider 0 1 0) = √ 2 .* hadamard × (ket 0).
Proof.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  rewrite Cexp_0.
  solve_matrix.
Qed.

Theorem ket_minus_state : ZX_semantics (Z_Spider 0 1 PI) = √ 2 .* hadamard × (ket 1).
Proof.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  rewrite Cexp_PI.
  solve_matrix.
Qed.

Theorem ket_0_state : ZX_semantics (X_Spider 0 1 0) = √ 2 .* (ket 0).
Proof.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  rewrite Cexp_0.
  solve_matrix.
  C_field_simplify; try reflexivity; try apply Csqrt2_neq_0.
Qed.

Theorem ket_1_state : ZX_semantics (X_Spider 0 1 PI) = √ 2 .* (ket 1).
Proof.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  rewrite Cexp_PI.
  solve_matrix.
  C_field_simplify; try lca; try apply Csqrt2_neq_0.
Qed.

Theorem bra_plus_state : ZX_semantics (Z_Spider 1 0 0) = √ 2 .* (hadamard × (ket 0))†.
Proof.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  rewrite Cexp_0.
  solve_matrix.
Qed.

Theorem bra_minus_state : ZX_semantics (Z_Spider 1 0 PI) = √ 2 .* (hadamard × (ket 1))†.
Proof.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  rewrite Cexp_PI.
  solve_matrix.
Qed.

Theorem bra_0_state : ZX_semantics (X_Spider 1 0 0) = √ 2 .* (bra 0).
Proof.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  rewrite Cexp_0.
  solve_matrix.
  C_field_simplify; try reflexivity; try apply Csqrt2_neq_0.
Qed.

Theorem bra_1_state : ZX_semantics (X_Spider 1 0 PI) = √ 2 .* (bra 1).
Proof.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  rewrite Cexp_PI.
  solve_matrix.
  C_field_simplify; try lca; try apply Csqrt2_neq_0.
Qed.

