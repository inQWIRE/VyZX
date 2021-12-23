Require Import externals.QuantumLib.Quantum.
Require Export ZX.
Require Export Gates.
Require Export Proportional.

Local Open Scope ZX_scope.

Local Transparent ZX_H.
Lemma ZX_H_is_H : ZX_semantics □ = Cexp (PI/4)%R .* hadamard.
Proof.
  simpl.
  unfold_spider.
  solve_matrix; 
  field_simplify_eq [Cexp_PI2 Cexp_PI4 Ci2 Csqrt2_sqrt2_inv Csqrt2_inv]; 
  try apply c_proj_eq; try simpl; try R_field_simplify; try reflexivity; (try split; try apply RtoC_neq; try apply sqrt2_neq_0; try auto).
Qed.
Local Opaque ZX_H.

Lemma ZX_H_H_is_Wire_eq : ZX_semantics (□ ⟷ □) = Cexp (PI/2)%R .* ZX_semantics —.
Proof.
  simpl.
  rewrite wire_identity_semantics.
  rewrite ZX_H_is_H.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_mult_dist_r.
  rewrite MmultHH.
  rewrite Mscale_assoc.
  rewrite <- Cexp_add.
  assert ((PI/4+PI/4 = PI/2)%R) as H by lra.
  rewrite H.
  reflexivity.
Qed.

Lemma ZX_H_H_is_Wire : □ ⟷ □ ∝ —.
Proof.
  eexists.
  split.
  apply ZX_H_H_is_Wire_eq.
  nonzero.
Qed.

Local Transparent ZX_Z.
Local Transparent ZX_X.
Lemma ZX_X_is_X : ZX_semantics ZX_X = σx.
Proof.
  simpl.
  unfold_spider.
  autorewrite with Cexp_db.
  solve_matrix.
Qed.

Lemma ZX_Z_is_Z : ZX_semantics ZX_Z = σz.
Proof.
  simpl.
  unfold_spider.
  autorewrite with Cexp_db.
  solve_matrix.
Qed.

Local Opaque ZX_Z.
Local Opaque ZX_X.

Local Transparent ZX_Y.
Lemma ZX_Y_is_Y : ZX_semantics ZX_Y = -Ci .* σy.
Proof.
  simpl.
  rewrite ZX_X_is_X, ZX_Z_is_Z.
  solve_matrix.
Qed.
Local Opaque ZX_Y.

Local Open Scope R_scope.
Local Transparent ZX_CNOT_l. 
Local Transparent ZX_CNOT_r.
Local Transparent ZX_CNOT.
Lemma ZX_CNOT_l_is_cnot : ZX_semantics ZX_CNOT_l = (/ √ 2)%C .* cnot.
Proof.
  simpl.
  unfold_spider.
  rewrite wire_identity_semantics.
  autorewrite with Cexp_db.
  simpl.
  solve_matrix.
Qed.

Lemma ZX_CNOT_r_is_cnot : ZX_semantics ZX_CNOT_r = (/ √ 2)%C .* cnot.
Proof.
  simpl.
  unfold_spider.
  rewrite wire_identity_semantics.
  autorewrite with Cexp_db.
  simpl.
  solve_matrix.
Qed.

Lemma ZX_CNOT_equiv : ZX_semantics ZX_CNOT_l = ZX_semantics ZX_CNOT_r.
Proof.
  rewrite ZX_CNOT_l_is_cnot.
  rewrite <- ZX_CNOT_r_is_cnot.
  reflexivity.
Qed.

Notation ZX_CNOT_is_cnot := ZX_CNOT_l_is_cnot.
Local Opaque ZX_CNOT_l. 
Local Opaque ZX_CNOT_r.
Local Opaque ZX_CNOT.

Local Transparent ZX_SWAP.
Lemma ZX_SWAP_is_swap : ZX_semantics ⨉ = (/ 2 * / √ 2)%C .* swap.
Proof.
  simpl.
  rewrite ZX_CNOT_is_cnot.
  rewrite wire_identity_semantics.
  unfold_spider.
  autorewrite with Cexp_db.
  Msimpl.
  rewrite hadamard_sa.
  repeat rewrite VectorStates.ket2bra.
  restore_dims.
  repeat rewrite <- kron_mixed_product.
  repeat rewrite <- Mmult_assoc.
  solve_matrix.
  simpl.
  all : field_simplify_eq [Csqrt2_sqrt]; try reflexivity; split; nonzero.
Qed.
Local Opaque ZX_SWAP.

Local Close Scope R_scope.
Local Close Scope ZX_scope.
