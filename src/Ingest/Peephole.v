Require Import SQIR.UnitarySem.
Require Import SQIR.Equivalences.
Require Import QuantumLib.Quantum.
Require Import CoreData.
Require Import CoreRules.
Require Import Gates.
Require Import ZXPad.
Require Import VOQC.RzQGateSet.
Require Import VOQC.UnitaryListRepresentation.
Require Import Ingest.
Require Import Interact.
Require Import SQIR.SQIR.
Require Import VOQC.RzQGateSet.

Require Import CoreRules.

Definition U := RzQ_Unitary.

Local Open Scope ucom_scope.

(* @nocheck name *)
(* Qualifier *)
Definition RZCNOT {dim} o p : ucom (RzQ_Unitary) dim := uapp2 (URzQ_CNOT) o p.
(* @nocheck name *)
(* Qualifier *)
Definition RZRZ {dim} q t : ucom (RzQ_Unitary) dim := uapp1 (URzQ_Rz q) t.
(* @nocheck name *)
(* Qualifier *)
Definition RZH {dim} t : ucom (RzQ_Unitary) dim := uapp1 (URzQ_H) t.
(* Qualifier *)
(* @nocheck name *)
Definition RZX {dim} t : ucom (RzQ_Unitary) dim := uapp1 (URzQ_X) t.
(* @nocheck name *)
(* Qualifier *)
Definition SKIP {dim} : ucom (RzQ_Unitary) dim := uapp1 (URzQ_Rz 0) 0.
Local Open Scope ZX_scope.

Local Hint Unfold ingest : RzQ_to_ZX.
Local Hint Unfold cnot_ingest : RzQ_to_ZX.
Local Hint Unfold H_ingest : RzQ_to_ZX.
Local Hint Unfold gate_ingest : RzQ_to_ZX.
Local Hint Unfold gate_ingest' : RzQ_to_ZX.
Local Hint Unfold pad_top : RzQ_to_ZX.
Local Hint Unfold pad_bot : RzQ_to_ZX.
Local Hint Unfold cnot_n_m_ingest : RzQ_to_ZX.
Local Hint Unfold cnot_m_n_ingest : RzQ_to_ZX.
Local Hint Unfold unpadded_cnot : RzQ_to_ZX.

Ltac circuit_to_zx_full := circuit_to_zx_b; autounfold with RzQ_to_ZX; simpl;
  cleanup_zx; simpl_casts.

Lemma cnot_flip : @RZH 2 0 ; RZH 1 ; RZCNOT 0 1; RZH 0; RZH 1 ≡u RZCNOT 1 0.
Proof.
  circuit_to_zx_full.
  rewrite compose_assoc.
  rewrite <- (stack_compose_distr □ —).
  cleanup_zx.
  easy.
Qed.

