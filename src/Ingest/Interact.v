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

