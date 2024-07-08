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

Local Open Scope ZX_scope.

Lemma prop_implies_scalar_equiv_rz_q {dim} : forall (l o : ucom RzQGateSet.U dim),
  uc_well_typed l -> uc_well_typed o ->
  (ingest l) ∝ (ingest o) -> exists (c : C), (c .* (uc_eval (RzQToBaseUCom l)) = uc_eval (RzQToBaseUCom o) /\ c <> 0)%M.
Proof.
  intros l o WTl WTo [c [semeq cnz]].
  unfold uc_equiv.
  destruct (ingest_correct l); [auto | ].
  destruct (ingest_correct o); [auto | ].
  destruct H.
  destruct H0.
  rewrite <- H in semeq.
  rewrite <- H0 in semeq.
  exists  (x / (c * x0))%C.
  split.
  - unfold Cdiv.
    rewrite (Cmult_comm x).
    rewrite <- Mscale_assoc.
    rewrite semeq.
    repeat rewrite Mscale_assoc.
    replace (/ (c * x0) * c * x0)%C with (C1).
    lma.
    rewrite <- Cmult_assoc.
    rewrite Cmult_comm.
    rewrite Cinv_r; auto.
    apply Cmult_neq_0; auto.
  - unfold Cdiv.
    apply Cmult_neq_0; auto.
    apply nonzero_div_nonzero.
    apply Cmult_neq_0; auto.
Qed.

Local Open Scope ucom.
Local Open Scope matrix_scope.
Ltac solve_uc_well_typed :=
  match goal with
  | [ |- uc_well_typed (useq ?c ?c2) ] => apply WT_seq; uc_well_typed
  | [ |- uc_well_typed (@SQIR.H ?dim ?n) ] => apply uc_well_typed_H
  | [ |- uc_well_typed (@SQIR.X ?dim ?n) ] => apply uc_well_typed_X
  | [ |- uc_well_typed (@SQIR.Y ?dim ?n) ] => apply uc_well_typed_Y
  | [ |- uc_well_typed (@SQIR.ID ?dim ?n) ] => apply uc_well_typed_ID
  | [ |- uc_well_typed (@SQIR.Rx ?dim ?θ ?n) ] => apply uc_well_typed_Rx
  | [ |- uc_well_typed (@SQIR.Ry ?dim ?θ ?n) ] => apply uc_well_typed_Ry
  | [ |- uc_well_typed (@SQIR.Rz ?dim ?θ ?n) ] => apply uc_well_typed_Rz
  | [ |- uc_well_typed (@SQIR.CNOT ?dim ?m ?n) ] => apply uc_well_typed_CNOT
  | [ |- uc_well_typed (@SQIR.SWAP ?dim ?m ?n) ] => apply uc_well_typed_SWAP
  | [ |- uc_well_typed (uapp1 ?u ?n)] => apply (@WT_app1 u n); try lia
  | [ |- uc_well_typed (uapp2 ?u ?m ?n)] =>  apply (@WT_app2 u m n); try lia
  | [ |- uc_well_typed (uapp3 ?u ?m ?n ?p)] =>  apply (@WT_app3 u m n p); try lia
  end.

Ltac circuit_to_zx := apply prop_implies_scalar_equiv_rz_q; [ solve_uc_well_typed | solve_uc_well_typed | ].

