Require Import CoreData.
Require Import CoreData.QlibTemp.
Require Import CoreRules.
Require Import Gates.
Require Import Ingest.
Require Import QuantumLib.Quantum.

Global Open Scope ZX_scope.

Fixpoint Z_phase_gadget_construct  (n : nat) (α : R) : ZX (S n) (S n) := match n with
  | 0 => (Z 1 1 α)
  | (S n') => (_CNOT_ ↕ (n_wire _)) ⟷ (— ↕ Z_phase_gadget_construct _ α) ⟷ (_CNOT_ ↕ (n_wire _))
  end.

Definition Z_phase_gadget (n : nat) (α : R) : ZX n n :=
  match n with
  | 0 => ⦰
  | (S n') => Z_phase_gadget_construct n' α
  end.
    
Lemma Z_phase_gadget_full_fusion : forall α β n, Z_phase_gadget n α ⟷ Z_phase_gadget n β ∝ (Z_phase_gadget n (α + β)).
Proof.
  intros.
  destruct n; [ simpl; cleanup_zx; easy | ].
  induction n.
  - simpl.
    rewrite Z_spider_1_1_fusion.
    easy.
  - simpl.
    assert (Hcnotnwire : (Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0) ↕ n_wire n
    ⟷ (Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0) ↕ n_wire n)) ∝ n_wire _).
    {
      rewrite <- stack_compose_distr.
      rewrite cnot_involutive.
      cleanup_zx; bundle_wires.
      easy.
    }
    repeat rewrite <- ComposeRules.compose_assoc.
    rewrite (ComposeRules.compose_assoc _ ((Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0) ↕ n_wire n)) ((Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0) ↕ n_wire n))).    
    apply compose_simplify; [ | easy ].
    rewrite Hcnotnwire.
    cleanup_zx.
    rewrite ComposeRules.compose_assoc.
    apply compose_simplify; [ easy | ].
    rewrite <- stack_wire_distribute_l.
    rewrite IHn.
    easy.
Qed.

Inductive pauli_op : Type :=
  | PauliX
  | PauliY
  | PauliZ.

Definition pauli_op_diag (op : pauli_op) : ZX 1 1 :=
  match op with
  | PauliX => □
  | PauliY => X 1 1 (PI / 2)
  | PauliZ => —
  end.

Definition pauli_op_adj (op : pauli_op) : ZX 1 1 :=
  match op with
  | PauliX => □
  | PauliY => X 1 1 (- (PI / 2))
  | PauliZ => —
  end.

Lemma pauli_op_adj_is_adj : forall (op : pauli_op), (pauli_op_diag op)† ∝ pauli_op_adj op.
Proof. 
  intros. 
  destruct op; easy.
Qed.

Lemma pauli_op_diag_unitary : forall op, unitary (pauli_op_diag op).
Proof.
  unfold unitary.
  intro op.
  destruct op; simpl; unfold X_semantics, Z_semantics; solve_matrix.
  all: C_field_simplify; autorewrite with Cexp_db; simpl; C_field_simplify; try lca.
  all: try (split; C_field).
  all : unfold Cconj; simpl;
  repeat (rewrite Rdiv_unfold;
  repeat rewrite Rmult_0_r, Rmult_0_l).
  all: apply c_proj_eq; simpl; (R_field_simplify; [easy |  nonzero]).
Qed.

Definition pauli_str := list pauli_op.

Fixpoint U (str : pauli_str) : ZX (length str) (length str) :=
  match str with
  | [] => ⦰
  | hd :: tl => (pauli_op_diag hd) ↕ (U tl)
  end.

(* @nocheck name *)
(* U is the name of an operator *)
Lemma U_unitary : forall str, unitary (U str).
Proof.
  unfold unitary.
  intros str.
  induction str.
  - simpl. cleanup_zx. unfold ZXCore.adjoint. rewrite id_sa. simpl. rewrite Mmult_1_l; auto with wf_db.
  - simpl. restore_dims. 
    rewrite (kron_adjoint (⟦ pauli_op_diag _ ⟧) (⟦ U _ ⟧)). 
    rewrite kron_mixed_product.
    rewrite pauli_op_diag_unitary.
    rewrite IHstr.
    rewrite id_kron.
    resolve_id.
Qed.

Definition pauli_gadget (str : pauli_str) α := (U str)† ⟷ Z_phase_gadget (length str) α ⟷ (U str).

Lemma pauli_gadget_fusion : forall α β str, pauli_gadget str α ⟷ pauli_gadget str β ∝ (pauli_gadget str (α + β)).
Proof.
  intros.
  unfold pauli_gadget.
  assert ((U str) † ⟷ Z_phase_gadget (length str) α ⟷ U str
  ⟷ ((U str) † ⟷ Z_phase_gadget (length str) β ⟷ U str) ∝ (U str) † ⟷ Z_phase_gadget (length str) α ⟷ (U str
  ⟷ (U str)† )  ⟷ Z_phase_gadget (length str) β ⟷ U str)
  as Hassoc by (repeat rewrite <- ComposeRules.compose_assoc; easy).
  rewrite Hassoc; clear Hassoc.
  pose proof (U_unitary str).
  apply unitary_is_weak_unitary_l in H.
  unfold weak_unitary_l in H.
  rewrite H.
  cleanup_zx.
  apply compose_simplify; [ | easy].
  rewrite ComposeRules.compose_assoc.
  rewrite Z_phase_gadget_full_fusion.
  easy.
Qed.

Ltac crewrite H := rewrite H; clear H.

Lemma cnot_commutes_through_phase_gadget : forall n α, 
  (_NOTC_ ↕ n_wire _) ⟷ (— ↕ Z_phase_gadget (S n) α) ∝ (— ↕ Z_phase_gadget (S n) α) ⟷ (_NOTC_ ↕ n_wire _).
Proof.
  intros.
  simpl.
  destruct n.
  - simpl. cleanup_zx. simpl_casts.
    rewrite notc_is_notc_r.
    rewrite ComposeRules.compose_assoc.
    rewrite <- (stack_compose_distr — — (Z 2 1 0)).
    assert (Z 2 1 0 ⟷ Z 1 1 α ∝ — ↕ Z 1 1 α ⟷ Z 2 1 0) as Hcomm.
    {
      rewrite <- Z_0_is_wire. 
      rewrite <- Z_add_l.
      rewrite Z_spider_1_1_fusion.
      repeat rewrite Rplus_0_l.
      easy.
    } 
    rewrite Hcomm.
    cleanup_zx.
    rewrite stack_wire_distribute_l.
    rewrite <- (ComposeRules.compose_assoc (X 1 2 0 ↕ —)).
    rewrite (stack_assoc_back — —).
    simpl_casts.
    rewrite <- (stack_compose_distr (X 1 2 0) (— ↕ —) — (Z 1 1 α)).
    cleanup_zx.
    rewrite <- (wire_removal_r (Z 1 1 α)).
    rewrite stack_compose_distr.
    rewrite <- (ComposeRules.compose_assoc).
    rewrite <- (stack_compose_distr — (X 1 2 0)).
    bundle_wires. cleanup_zx.
    easy.
  - simpl.
    remember (Z_phase_gadget_construct n α) as pg.
    rewrite wire_to_n_wire at 3.
    rewrite n_wire_stack.
    rewrite (@stack_nwire_distribute_r _ _ _ (1 + n)).
    rewrite (ComposeRules.compose_assoc (— ↕ (Z 1 2 0) ↕ (n_wire (1 + n)))).
    rewrite (stack_assoc (X 2 1 0) —).
    simpl_casts.
    bundle_wires.
    rewrite <- (stack_compose_distr (X 2 1 0) — (n_wire (1 + (1 + n)))).
    cleanup_zx.
    rewrite <- nwire_removal_r.
    rewrite (ComposeRules.compose_assoc (— ↕ (Z 1 2 0) ↕ (n_wire _)) (X 2 1 0 ↕ _) (n_wire (1 + (1 + (1 + n))))).
    assert ((n_wire (1 + (1 + (1 + n)))) ∝ (— ↕ (— ↕ n_wire (1 + n)))) as Hrw by (bundle_wires; easy).
    crewrite Hrw.
    rewrite <- (stack_compose_distr (X 2 1 0) — ((Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0) ↕ n_wire n ⟷ (— ↕ pg)
      ⟷ (Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0) ↕ n_wire n))) (— ↕ n_wire (1 + n))).
    rewrite (wire_removal_r (X 2 1 0)).
    rewrite <- (nwire_removal_l (X 2 1 0)) at 1.
    rewrite (stack_compose_distr (n_wire 2)).
    (* Move green spider *)
    assert (n_wire 2 ∝ (— ↕ —)) as H2w by (bundle_wires; easy).
    rewrite H2w at 1; clear H2w.
    rewrite (stack_assoc — —).
    rewrite stack_assoc.
    simpl_casts.
    rewrite <- (ComposeRules.compose_assoc (— ↕ (Z 1 2 0 ↕ n_wire (1 + n)))).
    rewrite <- (stack_compose_distr — — (Z 1 2 0 ↕ n_wire (1 + n)) (— ↕ (Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0) ↕ n_wire n ⟷ (— ↕ pg)
      ⟷ (Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0) ↕ n_wire n)))).
    rewrite wire_removal_l.
    rewrite (stack_wire_distribute_l (_CNOT_ ↕ n_wire _ ⟷ _)).
    rewrite (stack_wire_distribute_l (_CNOT_ ↕ n_wire _)).
    rewrite stack_nwire_distribute_r.
    repeat rewrite (stack_wire_distribute_l (_ ↕ (n_wire n))). 
    rewrite <- Z_0_is_wire at 3.
    repeat rewrite <- ComposeRules.compose_assoc.
    assert (Z 1 1 0 ↕ (Z 1 2 0 ↕ — ↕ n_wire n) ∝ ((Z 1 1 0 ↕ Z 1 2 0) ↕ (— ↕ n_wire n))) as Hstk.
    {
      repeat rewrite stack_assoc.
      simpl_casts.
      easy.
    }
    crewrite Hstk.
    rewrite wire_to_n_wire at 3; rewrite n_wire_stack.
    rewrite <- (@stack_nwire_distribute_r _ _ _ (1 + n) (Z 1 2 0) (Z 1 1 0 ↕ Z 1 2 0)). 
    rewrite <- Z_add_r_base_rot.
    repeat rewrite ComposeRules.compose_assoc.
    rewrite (stack_wire_distribute_l (Z 1 2 0 ↕ — ↕ n_wire n) (— ↕ _ ↕ n_wire n)).
    rewrite <- (ComposeRules.compose_assoc (— ↕ (— ↕ pg))).
    rewrite (stack_assoc (Z 1 2 0) —).
    simpl_casts.
    rewrite <- stack_wire_distribute_l.
    rewrite <- (stack_compose_distr — (Z 1 2 0) pg (— ↕ n_wire n)).
    rewrite wire_removal_l.
    rewrite <- (ComposeRules.compose_assoc (— ↕ (— ↕ X 2 1 0 ↕ n_wire n))).
    rewrite <- stack_wire_distribute_l.
    bundle_wires.
    rewrite nwire_removal_r.
    rewrite (stack_assoc — (X 2 1 0)).
    simpl_casts.
    rewrite <- (stack_compose_distr — (Z 1 2 0) (X 2 1 0 ↕ n_wire n) pg).
    rewrite wire_removal_l.
    rewrite <- (ComposeRules.compose_assoc (Z 1 (1 + 2) 0 ↕ n_wire (1 + n))).
    rewrite (stack_assoc_back — (Z 1 2 0) (X 2 1 0 ↕ n_wire n ⟷ pg)).
    simpl_casts.
    rewrite <- Z_0_is_wire at 3.
    rewrite <- (nwire_removal_l (X 2 1 0 ↕ n_wire n ⟷ pg)).
    rewrite <- (nwire_removal_r (Z 1 1 0 ↕ Z 1 2 0)).
    rewrite (stack_compose_distr (Z 1 1 0 ↕ Z 1 2 0)). 
    rewrite <- (n_wire_stack 2 n).
    rewrite <- (n_wire_stack 1 1).
    rewrite (stack_assoc (n_wire 1) (n_wire 1) _).
    simpl_casts.
    rewrite (n_wire_stack 1 n).
    rewrite stack_assoc_back.
    simpl_casts.
    repeat rewrite <- ComposeRules.compose_assoc.
    rewrite <- (stack_nwire_distribute_r (Z 1 (1+2) 0) (Z 1 1 0 ↕ Z 1 2 0 ↕ n_wire 1 )).
    rewrite (Z_add_r_base_rot 1 2).
    rewrite stack_assoc.
    simpl_casts.
    rewrite Z_0_is_wire.
    rewrite (ComposeRules.compose_assoc (Z 1 2 0)).
    rewrite <- (stack_wire_distribute_l (Z 1 2 _) (Z 1 2 _ ↕ (n_wire 1))).
    rewrite (dominated_Z_spider_fusion_top_left 2 0).
    rewrite wire_to_n_wire at 2.
    rewrite (dominated_Z_spider_fusion_bot_left 3 0 1).
    rewrite 2 Rplus_0_l.
    rewrite  (Z_add_r_base_rot 3 1).
    rewrite Z_0_is_wire.
    rewrite (stack_nwire_distribute_r (Z 1 2 0)).
    rewrite (stack_assoc (Z 1 3 0)).
    simpl_casts.
    rewrite 3 ComposeRules.compose_assoc.
    rewrite <- (ComposeRules.compose_assoc (Z 1 3 0 ↕ (— ↕ (n_wire _)))
      (n_wire (1 + 2) ↕ (X 2 1 0 ↕ n_wire n ⟷ pg))).
    rewrite <- (stack_compose_distr (Z 1 3 0) (n_wire 3) (— ↕ (n_wire (1+ n)))).
    bundle_wires.
    cleanup_zx.
    rewrite <- (nwire_removal_l (Z 1 3 0)).
    rewrite <- (nwire_removal_r (_ ⟷ pg)).
    rewrite stack_compose_distr.
    rewrite (Z_add_r_base_rot 2 1).
    rewrite <- n_wire_stack.
    rewrite stack_assoc_back.
    simpl_casts.
    rewrite (stack_nwire_distribute_l (X 2 1 0 ↕ n_wire n) pg).
    rewrite (stack_nwire_distribute_r (Z 1 2 0)).
    repeat rewrite stack_nwire_distribute_r.
    repeat rewrite stack_wire_distribute_l.
    repeat rewrite ComposeRules.compose_assoc.
    rewrite <- wire_to_n_wire.
    apply compose_simplify; [ easy | ].
    apply compose_simplify; [
    rewrite stack_assoc_back;
    simpl_casts;
    easy | ].
    apply compose_simplify; [ easy | ].
    rewrite <- (n_wire_stack 1 n).
    rewrite <- wire_to_n_wire.
    apply compose_simplify; [
    rewrite (stack_assoc (Z 1 2 0) — (n_wire n));
    simpl_casts;
    easy | ].
    rewrite Z_0_is_wire.
    rewrite stack_assoc_back; simpl_casts.
    rewrite <- ComposeRules.compose_assoc.
    rewrite <- (stack_wire_distribute_l (Z 1 2 0 ↕ — ↕ (— ↕ n_wire n)) ((— ↕ — ↕ (X 2 1 0 ↕ n_wire n)))).
    rewrite stack_assoc; simpl_casts.
    rewrite <- (stack_compose_distr  (Z 1 2 0) (— ↕ —) (— ↕ (— ↕ n_wire n))).
    rewrite wire_to_n_wire at 1 2 3 4 5.
    repeat rewrite n_wire_stack.
    rewrite nwire_removal_l.
    rewrite nwire_removal_r.
    rewrite <- (wire_removal_l (Z 1 2 0)) at 1.
    rewrite <- (wire_removal_r (X 2 1 0)) at 1.
    rewrite (stack_assoc_back (— ⟷ Z 1 2 0) (X 2 1 0 ⟷ —) (n_wire n)); simpl_casts.
    rewrite stack_compose_distr.
    rewrite stack_nwire_distribute_r, stack_nwire_distribute_l.
    rewrite ComposeRules.compose_assoc.
    rewrite <- wire_to_n_wire.
    apply compose_simplify; [ easy | ].
    bundle_wires.
    rewrite stack_nwire_distribute_r.
    apply compose_simplify.
    + rewrite stack_assoc; simpl_casts.
      bundle_wires.
      rewrite (stack_assoc — (Z 1 2 0) (n_wire _)); simpl_casts.
      easy.
    + rewrite (stack_assoc (X 2 1 0) — (n_wire _)); simpl_casts.
      bundle_wires.
      easy.
Unshelve.
  all: lia.
Qed.





    


    

    
    
    
    
    


      
    
