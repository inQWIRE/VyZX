Require Import CoreData.CoreData.
Require Import ComposeRules.
Require Import CastRules.
Require Import WireRules.
Require Import StackRules.
Require Import CoreAutomation.

Lemma cup_Z : ⊃ ∝ Z 2 0 0.
Proof.
  prop_exists_nonzero 1.
  Msimpl; simpl.
  solve_matrix.
  autorewrite with Cexp_db; easy.
Qed.

Lemma cap_Z : ⊂ ∝ Z 0 2 0.
Proof.
  prop_exists_nonzero 1.
  Msimpl; simpl.
  solve_matrix.
  autorewrite with Cexp_db; easy.
Qed.

Lemma cup_X : ⊃ ∝ X 2 0 0.
Proof. colorswap_of cup_Z. Qed. 

Lemma cap_X : ⊂ ∝ X 0 2 0.
Proof. colorswap_of cap_Z. Qed. 

Lemma n_cup_0_empty : n_cup 0 ∝ ⦰.
Proof.
  unfold n_cup.
  repeat (simpl;
  cleanup_zx;
  simpl_casts).
  easy.
Qed.

Lemma n_cup_1_cup : n_cup 1 ∝ ⊃.
Proof.
  unfold n_cup.
  simpl.
  simpl_casts.
  simpl.
  cleanup_zx.
  simpl_casts.
  bundle_wires.
  cleanup_zx.
  easy.
Qed.

Opaque n_cup.

Lemma n_cap_0_empty : n_cap 0 ∝ ⦰.
Proof.
  apply transpose_diagrams.
  simpl.
  rewrite n_cup_0_empty.
  easy.
Qed.

Lemma n_cap_1_cap : n_cap 1 ∝ ⊂.
Proof.
  apply transpose_diagrams.
  simpl.
  rewrite  <- n_cup_1_cup.
  unfold n_cap.
  rewrite Proportional.transpose_involutive.
  easy.
Qed.

Global Open Scope ZX_scope.

Lemma n_cup_helper_grow_l : forall n prfn prfm, 
  n_cup_helper (S n) ∝ cast _ _ prfn prfm (n_wire n ↕ ⊃ ↕ n_wire n) ⟷ n_cup_helper n.
Proof.
  intros.
  induction n.
  - simpl.
    simpl_casts.
    cleanup_zx.
    simpl_casts.
    bundle_wires.
    cleanup_zx.
    easy.
  - simpl.
    simpl in IHn.
    rewrite IHn at 1.
    simpl_casts.
    rewrite stack_wire_distribute_l.
    rewrite stack_wire_distribute_r.
    bundle_wires.
    erewrite <- (@cast_n_wire (n + 1) (1 + n)).
    rewrite <- ComposeRules.compose_assoc.
    apply compose_simplify; [ | easy].
    erewrite (cast_compose_mid (S (n + S n))).
    rewrite cast_compose_distribute.
    repeat rewrite cast_contract.
    apply compose_simplify; [ | apply cast_simplify; easy].
    simpl_casts.
    rewrite 2 stack_assoc.
    simpl_casts.
    rewrite 3 stack_assoc_back.
    simpl_casts.
    erewrite <- (@cast_n_wire (n + 1) (1 + n)) at 2.
    rewrite cast_stack_r.
    simpl.
    rewrite (stack_assoc (— ↕ n_wire n ↕ ⊃) (n_wire n) —). 
    bundle_wires.
    simpl_casts.
    easy.
Unshelve.
  all: lia.
Qed.


  
