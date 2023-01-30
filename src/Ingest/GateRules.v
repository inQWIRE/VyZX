Require Import QuantumLib.Quantum.
Require Export ZXCore.
Require Export Gates.
Require Export Proportional.
Require Import Setoid.

Local Open Scope ZX_scope.
(*
Lemma ZX_H_H_is_Wire_eq : ZX_semantics (□ ⟷ □) = ZX_semantics —.
Proof.
  simpl.
  solve_matrix.
Qed.

Lemma ZX_H_H_is_Wire : □ ⟷ □ ∝ —.
Proof.
  prop_exists_nonzero 1.
  rewrite ZX_H_H_is_Wire_eq.
  lma.
Qed.

Lemma ZX_X_is_X : ZX_semantics (_X_) = σx.
Proof.
  simpl.
  unfold X_semantics.
  simpl.
  rewrite kron_1_l; try auto with wf_db.
  solve_matrix;
  try (C_field_simplify; try lca; try nonzero).
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
*)
Lemma ZX_CNOT_l_is_cnot : ZX_semantics _CNOT_ = (/ √ 2)%C .* cnot.
Proof.
  simpl.
  unfold Z_semantics, X_semantics.
  solve_matrix.
  all: autorewrite with Cexp_db.
  all: lca.
Qed.

Lemma ZX_CNOT_inv_is_swapped_cnot : ZX_semantics _CNOT_inv_ = (/ √ 2)%C .* (swap × cnot × swap)%M.
Proof.
  simpl.
  unfold Z_semantics, X_semantics.
  solve_matrix.
  all: autorewrite with Cexp_db.
  all: lca.
Qed.
(* 
Lemma ZX_CNOT_equiv : ZX_semantics ZX_CNOT_l = ZX_semantics ZX_CNOT_r.
Proof.
  simpl.
  rewrite wire_identity_semantics.
  unfold_spider.
  autorewrite with Cexp_db.
  solve_matrix.
Qed.

Lemma ZX_CNOT_r_is_cnot : ZX_semantics ZX_CNOT_r = (/ √ 2)%C .* cnot.
Proof.
  rewrite <- ZX_CNOT_equiv.
  rewrite ZX_CNOT_l_is_cnot.
  reflexivity.
Qed.

Lemma ZX_CNOT_prop : ZX_CNOT_l ∝ ZX_CNOT_r.
Proof.
   prop_exists_nonzero 1.
   rewrite Mscale_1_l.
   apply ZX_CNOT_equiv.
Qed.

Notation ZX_CNOT_is_cnot := ZX_CNOT_l_is_cnot.
Local Opaque ZX_CNOT_l. 
Local Opaque ZX_CNOT_r.
Local Opaque ZX_CNOT.

Lemma hadamard_edge_compat :
  forall nIn nMid nOut,
    forall zx0 zx1 : ZX nIn  nMid, zx0 ∝ zx1 ->
    forall zx2 zx3 : ZX nMid nOut, zx2 ∝ zx3 ->
    zx0 ⥈ zx2 ∝ zx1 ⥈ zx3.
Proof.
  intros.
  unfold hadamard_edge.
  rewrite H, H0.
  reflexivity.
Qed.

Add Parametric Morphism (nIn nMid nOut : nat)  : (@hadamard_edge nIn nMid nOut)
  with signature (@proportional nIn nMid) ==> (@proportional nMid nOut) ==> 
                 (@proportional nIn nOut) as hadamard_edge_mor.
Proof. apply hadamard_edge_compat; assumption. Qed.

Local Close Scope R_scope.
Local Close Scope ZX_scope.
*)