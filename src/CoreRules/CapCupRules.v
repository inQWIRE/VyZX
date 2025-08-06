Require Import CoreData.CoreData.
Require Import ComposeRules.
Require Import CastRules.
Require Import WireRules.
Require Import StackRules.
Require Import SwapRules.
Require Import CoreAutomation.

Lemma cup_Z : ⊃ ∝= Z 2 0 0.
Proof.
  lma'.
  now rewrite Cexp_0.
Qed.

Lemma cap_Z : ⊂ ∝= Z 0 2 0.
Proof.
  lma'.
  now rewrite Cexp_0.
Qed.

Lemma cup_X : ⊃ ∝= X 2 0 0.
Proof. colorswap_of cup_Z. Qed. 

Lemma cap_X : ⊂ ∝= X 0 2 0.
Proof. colorswap_of cap_Z. Qed. 

Lemma n_cup_0_empty : n_cup 0 ∝= ⦰.
Proof.
  lma'.
Qed.

Lemma n_cup_1_cup : n_cup 1 ∝= ⊃.
Proof.
  unfold n_cup.
  cbn.
  auto_cast_eqn (rewrite stack_empty_r).
  rewrite 2!cast_id_eq.
  rewrite wire_removal_l.
  bundle_wires.
  now rewrite 2!nwire_removal_l.
Qed.

Opaque n_cup.

Lemma n_cap_0_empty : n_cap 0 ∝= ⦰.
Proof.
  apply transpose_diagrams_eq.
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

Lemma n_cup_unswapped_grow_l : forall n prfn prfm, 
  n_cup_unswapped (S n) ∝= cast _ _ prfn prfm (n_wire n ↕ ⊃ ↕ n_wire n) ⟷ 
  n_cup_unswapped n.
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
    erewrite <- (@cast_n_wire (n + 1) (S n)).
    rewrite <- ComposeRules.compose_assoc.
    apply compose_simplify_eq; [ | easy].
    erewrite (cast_compose_mid (S (n + S n))).
    rewrite cast_compose_distribute.
    repeat rewrite cast_contract.
    apply compose_simplify_eq; [ | apply cast_simplify_eq; easy].
    simpl_casts.
    rewrite 2 stack_assoc.
    simpl_casts.
    rewrite 3 stack_assoc_back.
    simpl_casts.
    erewrite <- (@cast_n_wire (n + 1) (S n)) at 2.
    rewrite cast_stack_r.
    simpl.
    rewrite (stack_assoc (— ↕ n_wire n ↕ ⊃) (n_wire n) —). 
    bundle_wires.
    simpl_casts.
    easy.
Unshelve.
  all: lia.
Qed.

Lemma n_cup_inv_n_swap_n_wire : forall n, n_cup n ∝= 
  n_wire n ↕ n_swap n ⟷ n_cup_unswapped n.
Proof.
  intros.
  induction n.
  - lma'. reflexivity.
  - Admitted. (*TODO*)

Lemma n_cup_unswapped_colorswap : forall n, 
  ⊙ (n_cup_unswapped n) = n_cup_unswapped n.
Proof. 
  intros.
  induction n; [ easy | ].
  simpl.
  f_equal.
  rewrite cast_colorswap.
  apply cast_simplify_zx.
  simpl.
  rewrite IHn.
  easy.
Qed.

Lemma n_cup_colorswap : forall n, ⊙ (n_cup n) = n_cup n.
Proof. 
  intros.
Local Transparent n_cup.
  unfold n_cup.
  simpl.
  rewrite n_wire_colorswap.
  rewrite n_swap_colorswap.
  rewrite n_cup_unswapped_colorswap.
  easy.
Qed.

Lemma n_cap_unswapped_colorswap : forall n, ⊙ (n_cap_unswapped n) = n_cap_unswapped n.
Proof.
  intros.
  unfold n_cap_unswapped.
  rewrite colorswap_transpose_commute.
  rewrite n_cup_unswapped_colorswap.
  easy.
Qed.

Lemma n_cap_colorswap : forall n, ⊙ (n_cap n) = n_cap n.
Proof. 
  intros.
  unfold n_cap.
  rewrite colorswap_transpose_commute.
  rewrite n_cup_colorswap.
  easy.
Qed.

#[export] Hint Rewrite
  (fun n => @n_cup_colorswap n)
  (fun n => @n_cap_colorswap n)
  (fun n => @n_cup_unswapped_colorswap n)
  (fun n => @n_cap_unswapped_colorswap n)
  : colorswap_db.

Lemma n_cup_unswapped_transpose : forall n, (n_cup_unswapped n)⊤ = n_cap_unswapped n.
Proof.
  reflexivity.
Qed.

Lemma n_cap_unswapped_transpose : forall n, (n_cap_unswapped n)⊤ = n_cup_unswapped n.
Proof.
  intros.
  unfold n_cap_unswapped.
  rewrite Proportional.transpose_involutive_eq.
  easy.
Qed.

Lemma n_cup_transpose : forall n, (n_cup n)⊤ = n_cap n.
Proof.
  reflexivity.
Qed.

Lemma n_cap_transpose : forall n, (n_cap n)⊤ ∝ n_cup n.
Proof.
  intros.
  unfold n_cap.
  rewrite Proportional.transpose_involutive.
  easy.
Qed.

#[export] Hint Rewrite
  (fun n => @n_cup_unswapped_transpose n)
  (fun n => @n_cap_unswapped_transpose n)
  (fun n => @n_cup_transpose n)
  (fun n => @n_cap_transpose n)
  : transpose_db.
Local Open Scope ZX_scope.

Lemma bigyank_cap : forall (zx1 : ZX 1 1),
  ⊂ ↕ zx1 ∝ — ↕ ⊂ ⟷ top_to_bottom 3 ⟷ (— ↕ — ↕ zx1).
Proof.
  intros.
  rewrite top_to_bottom_grow_r.
  simpl_casts.
  rewrite top_to_bottom_2.
  repeat rewrite compose_assoc.
  rewrite (stack_assoc — —).
  zx_simpl.
  repeat rewrite ComposeRules.compose_assoc.
  rewrite <- (stack_wire_distribute_l ⨉ (— ↕ zx1)).
  rewrite <- swap_comm.
  rewrite stack_wire_distribute_l.
  rewrite <- (ComposeRules.compose_assoc (⨉ ↕ —)).
  rewrite (stack_assoc_back — (zx1)).
  zx_simpl.
  rewrite <- (stack_wire_distribute_r ⨉ (— ↕ zx1)).
  rewrite <- swap_comm.
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
  cleanup_zx.
  rewrite top_to_bottom_grow_l.
  cleanup_zx.
  rewrite top_to_bottom_2.
  rewrite ComposeRules.compose_assoc.
  rewrite <- (nwire_removal_l ⊃).
  rewrite <- (wire_removal_r zx1).
  rewrite (stack_compose_distr).
  zx_simpl.
  rewrite <- (ComposeRules.compose_assoc (— ↕ ⨉)).
  rewrite stack_assoc.
  simpl_casts.
  rewrite <- stack_wire_distribute_l.
  rewrite <- swap_comm.
  rewrite stack_wire_distribute_l.
  rewrite <- 2 (ComposeRules.compose_assoc (⨉ ↕ —)).
  rewrite (stack_assoc_back — zx1 —). 
  simpl_casts.
  rewrite <- (stack_wire_distribute_r (⨉) (— ↕ zx1)).
  rewrite <- swap_comm.
  zx_simpl.
  rewrite stack_wire_distribute_r.
  repeat rewrite ComposeRules.compose_assoc.
  assert ((⨉ ↕ — ⟷ (— ↕ ⨉ ⟷ (⊃ ↕ —))) ∝ (— ↕ ⊃)) as Hrw. { shelve. }
  rewrite Hrw; clear Hrw.
  rewrite (stack_assoc zx1).
  zx_simpl.
  bundle_wires.
  rewrite <- (stack_compose_distr zx1 —).
  zx_simpl.
  easy.
Unshelve.
  all: try lia.
  solve_prop 1.
Qed.