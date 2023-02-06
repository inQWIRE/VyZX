Require Import externals.QuantumLib.Quantum.
Require Export ZX.

Local Open Scope ZX_scope.

Theorem ket_plus_state : ZX_semantics (Z_Spider 0 1 0) = √ 2 .* hadamard × (ket 0).
Proof.
  simpl.
  unfold_spider.
  autorewrite with Cexp_db.
  solve_matrix.
Qed.

Theorem ket_minus_state : ZX_semantics (Z_Spider 0 1 PI) = √ 2 .* hadamard × (ket 1).
Proof.
  simpl.
  unfold_spider.
  autorewrite with Cexp_db.
  solve_matrix.
Qed.

Theorem ket_0_state : ZX_semantics (X_Spider 0 1 0) = √ 2 .* (ket 0).
Proof.
  simpl.
  unfold X_semantics; simpl.
  rewrite kron_1_l; try auto with wf_db.
  unfold Z_semantics; simpl.
  autorewrite with Cexp_db.
  solve_matrix.
  rewrite <- Csqrt2_sqrt.
  rewrite <- Cmult_assoc.
  rewrite Cinv_r; try nonzero.
  rewrite Cmult_1_r; reflexivity.
Qed.

Theorem ket_1_state : ZX_semantics (X_Spider 0 1 PI) = √ 2 .* (ket 1).
Proof.
  simpl.
  unfold X_semantics; simpl.
  rewrite kron_1_l; try auto with wf_db.
  unfold Z_semantics; simpl.
  autorewrite with Cexp_db.
  solve_matrix.
  C_field_simplify; try lca; try apply Csqrt2_neq_0.
Qed.

Theorem bra_plus_state : ZX_semantics (Z_Spider 1 0 0) = √ 2 .* (hadamard × (ket 0))†.
Proof.
  simpl.
  unfold Z_semantics; simpl.
  autorewrite with Cexp_db.
  solve_matrix.
Qed.

Theorem bra_minus_state : ZX_semantics (Z_Spider 1 0 PI) = √ 2 .* (hadamard × (ket 1))†.
Proof.
  simpl.
  unfold_spider.
  autorewrite with Cexp_db.
  solve_matrix.
Qed.

Theorem bra_0_state : ZX_semantics (X_Spider 1 0 0) = √ 2 .* (bra 0).
Proof.
  simpl.
  unfold_spider; try auto with wf_db.
  autorewrite with Cexp_db.
  solve_matrix.
  C_field_simplify; try reflexivity; try apply Csqrt2_neq_0.
Qed.

Theorem bra_1_state : ZX_semantics (X_Spider 1 0 PI) = √ 2 .* (bra 1).
Proof.
  simpl.
  unfold_spider; unfold_spider.
  autorewrite with Cexp_db.
  solve_matrix.
  C_field_simplify; try lca; try apply Csqrt2_neq_0.
Qed.

Local Close Scope ZX_scope.
