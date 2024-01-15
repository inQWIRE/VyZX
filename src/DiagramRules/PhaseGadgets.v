Require Import CoreData.
Require Import CoreData.QlibTemp.
Require Import CoreRules.
Require Import Gates.
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
    
Lemma Z_phase_gadget_fusion : forall α β n, Z_phase_gadget n α ⟷ Z_phase_gadget n β ∝ (Z_phase_gadget n (α + β)).
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
  | hd :: tl => (pauli_op_to_ZX hd) ↕ (U tl)
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
  rewrite Z_phase_gadget_fusion.
  easy.
Qed.


