Require Import SQIR.UnitarySem.
Require Import SQIR.Equivalences.
Require Import QuantumLib.Quantum.
Require Import Gates.
Require Import ZXPad.
Require Import VOQC.RzQGateSet.
Require Import VOQC.UnitaryListRepresentation.
Require Import Ingest.
Require Import Interact.
Require Import SQIR.SQIR.
Require Import VOQC.RzQGateSet.

Require Import CoreRules.
Require Import CoreData.
Require Import CoreRules.ComposeRules.

Definition U := RzQ_Unitary.

Local Open Scope ucom_scope.

(* @nocheck name *)
(* Qualifier *)
Definition RZCNOT {dim} o p : ucom U dim := uapp2 (URzQ_CNOT) o p.
(* @nocheck name *)
(* Qualifier *)
Definition RZRZ {dim} q t : ucom U dim := uapp1 (URzQ_Rz q) t.
(* @nocheck name *)
(* Qualifier *)
Definition RZH {dim} t : ucom U dim := uapp1 (URzQ_H) t.
(* Qualifier *)
(* @nocheck name *)
Definition RZX {dim} t : ucom U dim := uapp1 (URzQ_X) t.
(* @nocheck name *)
(* Qualifier *)
Definition SKIP {dim} : ucom U dim := uapp1 (URzQ_Rz 0) 0.
(* @nocheck name *)
(* Qualifier *)
Definition RZP {dim} t : ucom U dim := uapp1 (URzQ_Rz (1 / 2)) t.
(* @nocheck name *)
(* Qualifier *)
Definition RZPdag {dim} t : ucom U dim := uapp1 (URzQ_Rz (3 / 2)) t.
(* Nam Hadamard reduction*)


Local Open Scope ZX_scope.

Local Hint Unfold ingest : RzQ_to_ZX.
Local Hint Unfold cnot_ingest : RzQ_to_ZX.
Local Hint Unfold H_ingest : RzQ_to_ZX.
Local Hint Unfold Rz_ingest : RzQ_to_ZX.
Local Hint Unfold gate_ingest : RzQ_to_ZX.
Local Hint Unfold gate_ingest' : RzQ_to_ZX.
Local Hint Unfold pad_top : RzQ_to_ZX.
Local Hint Unfold pad_bot : RzQ_to_ZX.
Local Hint Unfold pad_bot_1 : RzQ_to_ZX.
Local Hint Unfold cnot_n_m_ingest : RzQ_to_ZX.
Local Hint Unfold cnot_m_n_ingest : RzQ_to_ZX.
Local Hint Unfold unpadded_cnot : RzQ_to_ZX.
Local Hint Unfold _Rz_ : RzQ_to_ZX.
Local Hint Unfold base_cnot : RzQ_to_ZX.
Local Hint Unfold bottom_to_top : RzQ_to_ZX.
Local Hint Unfold top_to_bottom : RzQ_to_ZX.

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

(* Hadamard reductions from fig 4 in Nam et al*)

Lemma h_p_reduction : □ ⟷ Z 1 1 ((1 / 2) * PI) ⟷ □
∝ Z 1 1 ((3 / 2) * PI) ⟷ □ ⟷ Z 1 1 ((3 / 2) * PI).
Proof.   
  rewrite compose_assoc.
  rewrite <- (nstack1_1 □) at 1 2.
  rewrite <- colorswap_is_bihadamard.
  simpl.
  rewrite <- _H_is_box.
  repeat rewrite compose_assoc.
  rewrite Z_spider_1_1_fusion.
  repeat rewrite <- compose_assoc.
  rewrite Z_spider_1_1_fusion.
  replace (3 / 2 * PI + PI / 2)%R with ((INR 1) * 2 * PI)%R by (simpl; lra).
  replace (PI / 2 + 3 / 2 * PI)%R with ((INR 1) * 2 * PI)%R by (simpl; lra).
  rewrite INR_IZR_INZ.
  rewrite Z_2_PI.
  cleanup_zx.
  apply X_simplify.
  lra.
Qed. 

Lemma h_reduction_1 : RZH 0; @RZP 1 0; RZH 0 ≡u @RZPdag 1 0; RZH 0; RZPdag 0.
Proof.
  circuit_to_zx_full.
  replace (Q2R (1 / 2)) with (1 / 2)%R by easy.
  replace (Q2R (3 / 2)) with (3 / 2)%R by easy.
  apply h_p_reduction.
Qed.

Lemma h_reduction_2 : RZH 0; @RZPdag 1 0; RZH 0 ≡u @RZP 1 0; RZH 0; RZP 0.
Proof.
  circuit_to_zx_full.
  apply adjoint_diagrams.
  unfold ZXCore.adjoint.
  simpl.
  replace (Q2R (1 / 2))%R with (1 / 2)%R by easy.
  replace (Q2R (3 / 2))%R with (3 / 2)%R by easy.
  assert ((Z 1 1 (- (3 / 2 * PI))) ∝ (Z 1 1 (1 / 2 * PI))) by (apply (Z_simplify_general (-1)); lra).
  assert ((Z 1 1 (- (1 / 2 * PI))) ∝ (Z 1 1 (3 / 2 * PI))) by (apply (Z_simplify_general (-1)); lra).
  rewrite H, H0.
  repeat rewrite <- compose_assoc.
  apply h_p_reduction.
Qed.


Lemma h_reduction_3 : @RZH 2 0; RZH 1; RZCNOT 0 1; RZH 0; RZH 1 ≡u RZCNOT 1 0.
Proof.
  circuit_to_zx_full.
  rewrite compose_assoc.
  rewrite <- (stack_compose_distr □ —).
  cleanup_zx.
  assert ((□ ↕ □) ∝ (2 ↑ □)) by (simpl; cleanup_zx; simpl_casts; easy).
  rewrite H.
  easy.
Qed.

Lemma h_p_reduction' : □ ⟷ Z 1 1 (1 / 2 * PI) ∝ Z 1 1 (3 / 2 * PI) ⟷ □ ⟷ Z 1 1 (3 / 2 * PI) ⟷ □.
  rewrite <- h_p_reduction.
  repeat rewrite compose_assoc.
  cleanup_zx.
  easy.
Qed.

Lemma h_p_reduction'' : □ ⟷ Z 1 1 (3 / 2 * PI) ∝ Z 1 1 (1 / 2 * PI) ⟷ □ ⟷ Z 1 1 (1 / 2 * PI) ⟷ □.
  apply adjoint_diagrams.
  unfold ZXCore.adjoint.
  simpl.
  assert ((Z 1 1 (- (3 / 2 * PI))) ∝ (Z 1 1 (1 / 2 * PI))) by (apply (Z_simplify_general (-1)); lra).
  assert ((Z 1 1 (- (1 / 2 * PI))) ∝ (Z 1 1 (3 / 2 * PI))) by (apply (Z_simplify_general (-1)); lra).
  rewrite H, H0.
  repeat rewrite <- compose_assoc.
  rewrite 2 (compose_assoc □).
  rewrite <- h_p_reduction.
  repeat rewrite <- compose_assoc.
  cleanup_zx.
  easy.
Qed.

Lemma h_reduction_4_zx : — ↕ □ ⟷ (— ↕ Z 1 1 ((1 / 2) * PI)) ⟷ (Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0))
⟷ (— ↕ Z 1 1 ((3 / 2) * PI)) ⟷ (— ↕ □)
∝ — ↕ Z 1 1 ((3 / 2) * PI) ⟷ (Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0))
  ⟷ (— ↕ Z 1 1 ((1 / 2) * PI)).
Proof.
  repeat rewrite <- compose_assoc.
  rewrite <- stack_compose_distr.
  rewrite h_p_reduction'.
  do 2 rewrite (compose_assoc (Z 1 1 (3 / 2 * PI))).
  rewrite (compose_assoc □ _ □).
  rewrite <- (nstack1_1 □) at 1 2.
  rewrite <- colorswap_is_bihadamard.
  simpl.
  rewrite stack_compose_distr.
  rewrite (compose_assoc _ (Z 1 2 0 ↕ —)).
  rewrite cnot_is_cnot_r.
  repeat rewrite <- compose_assoc.
  rewrite (compose_assoc _ (— ↕ X 1 1 _)).
  rewrite <- stack_compose_distr.
  rewrite X_spider_1_1_fusion.
  cleanup_zx.
  rewrite (compose_assoc _ (—↕ X 1 2 _)).
  rewrite <- cnot_is_cnot_r_general.
  rewrite Rplus_0_r.
  rewrite <- (Rplus_0_l (3 / 2 * PI)) at 2.
  rewrite <- X_spider_1_1_fusion.
  rewrite stack_wire_distribute_l.
  replace (X 1 1 (3 / 2 * PI)) with (⊙(Z 1 1 (3 / 2 * PI))) by easy.
  rewrite colorswap_is_bihadamard.
  rewrite nstack1_1.
  rewrite 2 stack_wire_distribute_l.
  repeat rewrite compose_assoc.
  rewrite <- 3 stack_wire_distribute_l.
  rewrite <- (compose_assoc (Z 1 1 (3 / 2 * PI))).
  rewrite <- (compose_assoc (Z 1 1 (3 / 2 * PI) ⟷ □)).
  rewrite <- h_p_reduction'.
  rewrite <- stack_wire_distribute_l. 
  rewrite <- (compose_assoc □).
  cleanup_zx.
  easy.
Qed.

Lemma h_reduction_5_zx : — ↕ □ ⟷ (— ↕ Z 1 1 ((3 / 2) * PI)) ⟷ (Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0))
⟷ (— ↕ Z 1 1 ((1 / 2) * PI)) ⟷ (— ↕ □)
∝ — ↕ Z 1 1 ((1 / 2) * PI) ⟷ (Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0))
  ⟷ (— ↕ Z 1 1 ((3 / 2) * PI)).
Proof.
  repeat rewrite <- compose_assoc.
  rewrite <- stack_compose_distr.
  rewrite h_p_reduction''.
  do 2 rewrite (compose_assoc (Z 1 1 (1 / 2 * PI))).
  rewrite (compose_assoc □ _ □).
  rewrite <- (nstack1_1 □) at 1 2.
  rewrite <- colorswap_is_bihadamard.
  simpl.
  rewrite stack_compose_distr.
  rewrite (compose_assoc _ (Z 1 2 0 ↕ —)).
  rewrite cnot_is_cnot_r.
  repeat rewrite <- compose_assoc.
  rewrite (compose_assoc _ (— ↕ X 1 1 _)).
  rewrite <- stack_compose_distr.
  rewrite X_spider_1_1_fusion.
  cleanup_zx.
  rewrite (compose_assoc _ (—↕ X 1 2 _)).
  rewrite <- cnot_is_cnot_r_general.
  rewrite Rplus_0_r.
  rewrite <- (Rplus_0_l (1 / 2 * PI)) at 2.
  rewrite <- X_spider_1_1_fusion.
  rewrite stack_wire_distribute_l.
  replace (X 1 1 (1 / 2 * PI)) with (⊙(Z 1 1 (1 / 2 * PI))) by easy.
  rewrite colorswap_is_bihadamard.
  rewrite nstack1_1.
  rewrite 2 stack_wire_distribute_l.
  repeat rewrite compose_assoc.
  rewrite <- 3 stack_wire_distribute_l.
  rewrite <- (compose_assoc (Z 1 1 (1 / 2 * PI))).
  rewrite <- (compose_assoc (Z 1 1 (1/ 2 * PI) ⟷ □)).
  rewrite <- h_p_reduction''.
  rewrite <- stack_wire_distribute_l. 
  rewrite <- (compose_assoc □).
  cleanup_zx.
  easy.
Qed.
  
Lemma h_reduction_4 : @RZH 2 1; RZP 1; RZCNOT 0 1; RZPdag 1; RZH 1 ≡u RZPdag 1; RZCNOT 0 1; RZP 1.
Proof.
  circuit_to_zx_full.
  replace (Q2R (1 / 2))%R with (1 / 2)%R by easy.
  replace (Q2R (3 / 2))%R with (3 / 2)%R by easy.
  apply h_reduction_4_zx.
Qed.

Lemma h_reduction_5 : @RZH 2 1; RZPdag 1; RZCNOT 0 1; RZP 1; RZH 1 ≡u RZP 1; RZCNOT 0 1; RZPdag 1.
Proof.
  circuit_to_zx_full.
  apply adjoint_diagrams.
  unfold ZXCore.adjoint.
  simpl.
  replace (Q2R (1 / 2))%R with (1 / 2)%R by easy.
  replace (Q2R (3 / 2))%R with (3 / 2)%R by easy.
  assert ((Z 1 1 (- (3 / 2 * PI))) ∝ (Z 1 1 (1 / 2 * PI))) by (apply (Z_simplify_general (-1)); lra).
  assert ((Z 1 1 (- (1 / 2 * PI))) ∝ (Z 1 1 (3 / 2 * PI))) by (apply (Z_simplify_general (-1)); lra).
  rewrite H, H0.
  repeat rewrite <- compose_assoc.
  rewrite Ropp_0.
  rewrite (compose_assoc _ (— ↕ X 1 2 0)).
  rewrite <- cnot_is_cnot_r.
  rewrite h_reduction_5_zx.
  apply compose_simplify ; [ | easy ].
  rewrite compose_assoc.
  rewrite cnot_is_cnot_r.
  easy.
Qed.

(* Fig 5 nam *)

Lemma comm_1 : forall α, @RZRZ 2 α 1; RZH 1; RZCNOT 0 1; RZH 1 ≡u RZH 1; RZCNOT 0 1; RZH 1; RZRZ α 1.
Proof.
  intros.
  circuit_to_zx_full.
  assert ((Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0)) ∝ ⊙((X 1 2 0 ↕ — ⟷ (— ↕ Z 2 1 0)))) by (simpl; easy).
  rewrite H.
  rewrite colorswap_is_bihadamard.
  simpl; cleanup_zx; simpl_casts.
  repeat rewrite compose_assoc.
  rewrite <- (compose_assoc (□ ↕ □) (— ↕ □)).
  rewrite <- (stack_compose_distr □ —); cleanup_zx.
  repeat rewrite <- compose_assoc.
  rewrite (compose_assoc _ (— ↕ □)).
  do 3 (rewrite <- (stack_compose_distr — □); cleanup_zx).
  repeat rewrite compose_assoc.
  do 2 rewrite <- (stack_compose_distr □ —); cleanup_zx.
  rewrite <- (wire_removal_l □) at 4.
  rewrite <- (wire_removal_r (Z 1 1 _)) at 2.
  rewrite stack_compose_distr.
  rewrite <- (compose_assoc (— ↕ (Z 2 1 0))).
  rewrite <- stack_compose_distr.
  rewrite Z_spider_1_1_fusion.
  rewrite Rplus_0_l.
  rewrite <- (Rplus_0_r (Q2R α * PI)) at 2.
  rewrite <- Z_spider_1_1_fusion.
  rewrite stack_compose_distr.
  cleanup_zx.
  bundle_wires.
  cleanup_zx.
  assert (□ ↕ Z 1 1 (Q2R α * PI) ⟷ (X 1 2 0 ↕ — ⟷ (— ↕ Z 2 1 0 ⟷ (□ ↕ —))) ∝ □ ↕ Z 1 1 (Q2R α * PI) ⟷ (X 1 2 0 ↕ — ⟷ (— ↕ Z 2 1 0) ⟷ (□ ↕ —))).
  {
    repeat rewrite compose_assoc.
    easy.
  }
  rewrite H0; clear H0.
  rewrite <- notc_is_notc_r.
  repeat rewrite <- compose_assoc.
  rewrite <- stack_compose_distr.
  rewrite Z_spider_1_1_fusion.
  rewrite Rplus_0_r.
  rewrite <- (Rplus_0_l (Q2R α * PI)) at 1.
  rewrite <- Z_spider_1_1_fusion.
  rewrite stack_compose_distr.
  cleanup_zx.
  apply compose_simplify; try easy.
  repeat rewrite compose_assoc.
  apply compose_simplify; try easy.
  apply notc_is_notc_r_general.
Qed.

Lemma comm_3 : forall α, @RZRZ 2 α 0; RZCNOT 0 1 ≡u RZCNOT 0 1; RZRZ α 0.
Proof.
  intros.
  circuit_to_zx_full.
  rewrite cnot_is_cnot_r at 2.
  repeat rewrite <- compose_assoc.
  rewrite <- (stack_compose_distr (Z 1 1 _) (Z 1 2 0) — —).
  cleanup_zx.
  rewrite Z_spider_1_1_fusion.
  rewrite cnot_is_cnot_r_general.
  repeat rewrite compose_assoc.
  apply compose_simplify; [ easy | ].
  rewrite <- (stack_compose_distr (Z 2 1 0) (Z 1 1 _) — —).
  rewrite Z_spider_1_1_fusion.
  cleanup_zx.
  apply stack_simplify; [ | easy ].
  apply Z_simplify.
  lra.
Qed.

Ltac zx_simpl := simpl; cleanup_zx; simpl_casts.

Lemma top_to_bottom_2 : top_to_bottom 2 ∝ ⨉.
Proof.
  zx_simpl.
  bundle_wires.
  zx_simpl.
  easy.
Qed.

Opaque top_to_bottom.

Lemma swap_comm : forall (zx0 zx1 : ZX 1 1),
  zx0 ↕ zx1 ⟷ ⨉ ∝ ⨉ ⟷ (zx1 ↕ zx0).
Proof.
  intros.
  prop_exists_nonzero 1.
  Msimpl.
  simpl.
  specialize (WF_ZX 1 1 zx0);
  specialize (WF_ZX 1 1 zx1); intros.
  solve_matrix.
Qed.

Lemma bigyank_cap : forall (zx1 : ZX 1 1),
  ⊂ ↕ zx1 ∝ — ↕ ⊂ ⟷ top_to_bottom 3 ⟷ (— ↕ — ↕ zx1).
Proof.
  intros.
  rewrite top_to_bottom_grow_r.
  zx_simpl.
  rewrite top_to_bottom_2.
  repeat rewrite compose_assoc.
  rewrite (stack_assoc — —).
  zx_simpl.
  rewrite <- (stack_wire_distribute_l ⨉ (— ↕ zx1)).
  rewrite <- swap_comm.
  rewrite stack_wire_distribute_l.
  rewrite <- (compose_assoc (⨉ ↕ —)).
  rewrite (stack_assoc_back — (zx1)).
  zx_simpl.
  rewrite <- (stack_wire_distribute_r ⨉ (— ↕ zx1)).
  rewrite <- swap_comm.
  rewrite <- compose_assoc.
  solve_prop 1.
  Unshelve.
  all: lia.
Qed.

Lemma bigyank_cup : forall (zx1 : ZX 1 1),
  top_to_bottom 3 ⟷ (⊃ ↕ zx1) ∝ — ↕ ⊃ ⟷ zx1.
Proof.
  intros.
  rewrite (stack_empty_r_rev zx1) at 2.
  simpl_casts.
  rewrite <- (stack_compose_distr — zx1).
  zx_simpl.
  rewrite top_to_bottom_grow_l.
  zx_simpl.
  rewrite top_to_bottom_2.
  rewrite compose_assoc.
  rewrite <- (nwire_removal_l ⊃).
  rewrite <- (wire_removal_r zx1).
  rewrite (stack_compose_distr).
  zx_simpl.
  rewrite <- (compose_assoc (— ↕ ⨉)).
  rewrite stack_assoc.
  simpl_casts.
  rewrite <- stack_wire_distribute_l.
  rewrite <- swap_comm.
  rewrite stack_wire_distribute_l.
  rewrite <- 2 (compose_assoc (⨉ ↕ —)).
  rewrite (stack_assoc_back — zx1 —). 
  simpl_casts.
  rewrite <- (stack_wire_distribute_r (⨉) (— ↕ zx1)).
  rewrite <- swap_comm.
  zx_simpl.
  rewrite stack_wire_distribute_r.
  repeat rewrite compose_assoc.
  setoid_replace ((⨉ ↕ — ⟷ (— ↕ ⨉ ⟷ (⊃ ↕ —)))) with (— ↕ ⊃).
  rewrite (stack_assoc zx1).
  zx_simpl.
  bundle_wires.
  rewrite <- (stack_compose_distr zx1 —).
  zx_simpl.
  easy.
  solve_prop 1.
  Unshelve.
  all: lia.
Qed.

Transparent top_to_bottom.
Lemma top_to_bottom_1 : top_to_bottom 1 ∝ —.
Proof. easy. Qed.
Opaque top_to_bottom.


Lemma top_to_bottom_X {n m α} {prfn prfm} : forall (zx1 : ZX 1 1), 
  top_to_bottom (n + 1) ⟷ (X n m α ↕ zx1)
  ∝ (cast (n + 1) (m + 1) prfn prfm (— ↕ X n m α)) ⟷ top_to_bottom (m + 1) ⟷ (n_wire m ↕ zx1).
Proof.
  intros.
  generalize dependent m;
  induction n; intros.
  - induction m.
    + simpl.
      zx_simpl.
      rewrite (stack_empty_r_rev zx1) at 2.
      simpl_casts.
      rewrite <- (stack_compose_distr — zx1).
      zx_simpl.
      admit.
    + simpl.
      simpl_casts. 
      rewrite top_to_bottom_1.
Admitted.



Lemma top_to_bottom_big_yank_r {n m} {prfn prfm} : forall (zx1 : ZX 1 1) (zx0 : ZX n m), 
  top_to_bottom (n + 1) ⟷ (zx0 ↕ zx1) ∝
  (cast (n + 1) (m + 1) prfn prfm (— ↕ zx0)) ⟷ 
    top_to_bottom (m + 1) ⟷ (n_wire m ↕ zx1).
Proof.
  intros.
  generalize dependent zx1.
  induction zx0; intros.
  - zx_simpl.
    zx_simpl.
    easy.
  - zx_simpl.
    apply bigyank_cap.
  - zx_simpl.
    apply bigyank_cup.
  - zx_simpl.
    rewrite top_to_bottom_grow_r.
    zx_simpl.
    rewrite top_to_bottom_2.
    rewrite <- (nwire_removal_r ⨉) at 3. 
    rewrite <- (wire_removal_l zx1) at 1.
    rewrite stack_compose_distr.
    zx_simpl.
    repeat rewrite <- compose_assoc.
    apply compose_simplify.
    + solve_prop 1.
      Unshelve.
      all: lia.
    + easy.
  - zx_simpl.
    rewrite top_to_bottom_2.
    bundle_wires.
    zx_simpl.
    easy.
  - zx_simpl.
    rewrite top_to_bottom_2.
    rewrite swap_comm.
    rewrite compose_assoc.
    rewrite <- (stack_compose_distr □ —).
    zx_simpl.
    easy.
  - zx_simpl.
    admit.
  - zx_simpl.
    admit.
  - zx_simpl.
    admit.
  - zx_simpl.
    rewrite <- (wire_removal_l zx1) at 1.
    rewrite stack_compose_distr.
    rewrite <- compose_assoc.
    rewrite IHzx0_1.
    bundle_wires.
    zx_simpl.
    rewrite compose_assoc.
    rewrite IHzx0_2.
    repeat rewrite <- compose_assoc.
    apply compose_simplify.
    apply compose_simplify.
    rewrite stack_wire_distribute_l.
    rewrite cast_compose_distribute.
    erewrite (cast_compose_mid (S m) _ _ ($ n + 1, m + 1 ::: — ↕ zx0_1 $)).
    simpl_casts.
    apply compose_simplify.
    simpl.
    eapply (cast_diagrams (S n) (S m)).
    simpl_casts.
    easy.
    eapply (cast_diagrams (S m) (S o)).
    simpl_casts.
    easy.
    easy.
    easy.
Admitted.

Ltac zx_easy := bundle_wires; zx_simpl; easy.

Lemma top_to_bottom_big_yank_l {n m} {prfn prfm} : forall (zx0 : ZX 1 1) (zx1 : ZX n m),
  (zx0 ↕ zx1) ⟷ top_to_bottom (S m) ∝
  (zx0 ↕ n_wire n) ⟷ top_to_bottom (S n) ⟷
    (cast (S n) (S m) prfn prfm (zx1 ↕ —)).
Proof.
  intros.
  induction zx1.
  - repeat zx_simpl; easy.
  - zx_simpl.
    rewrite top_to_bottom_grow_r.
    rewrite top_to_bottom_2.
    zx_simpl.
    admit.
  - admit.
  - simpl.
    rewrite top_to_bottom_grow_r.
    cleanup_zx.
    simpl_casts.
    rewrite top_to_bottom_2.
    zx_simpl.
    admit.
  - zx_simpl.
    rewrite top_to_bottom_2.
    bundle_wires.
    cleanup_zx.
    easy.
  - zx_simpl.
    rewrite top_to_bottom_2.
    rewrite 2 swap_comm.
    rewrite compose_assoc.
    rewrite <- (stack_compose_distr — □).
    zx_simpl.
    easy.
  - 
Admitted.

