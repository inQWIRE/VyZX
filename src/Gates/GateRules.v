Require Import QuantumLib.Quantum.
Require Export ZXCore.
Require Export GateDefinitions.
Require Export DiagramRules.
Require Export CoreRules.

Local Open Scope ZX_scope.

Lemma Z_is_Z : ⟦ _Z_ ⟧ = σz.
Proof.
  simpl.
  unfold Z_semantics.
  autorewrite with Cexp_db.
  simpl.
  solve_matrix.
Qed.

Lemma X_is_X : ⟦ _X_ ⟧ = σx.
Proof.
  simpl.
  unfold X_semantics; solve_matrix.
  all: autorewrite with Cexp_db.
  all: C_field_simplify; try lca.
  all: split; nonzero.
Qed.

Lemma _H_is_box : _H_ ∝[Cexp (PI/4)] □.
Proof.
  split; [|nonzero].
  prep_matrix_equivalence; cbn.
  unfold X_semantics, Z_semantics.
  simpl.
  Msimpl.
  rewrite Cexp_PI2, Cexp_PI4.
  unfold scale.
  by_cell; cbn; C_field.
Qed.

Lemma _Rz_is_Rz : forall α, ⟦ _Rz_ α ⟧ = phase_shift α.
Proof.
  intros.
  simpl.
  unfold Z_semantics, phase_shift.
  simpl.
  lma.
Qed.

Lemma cnot_l_is_cnot : ⟦ _CNOT_ ⟧ = (/ (√ 2)%R) .* cnot.
Proof.
  simpl.
  unfold Z_semantics, X_semantics.
  solve_matrix.
  all: autorewrite with Cexp_db.
  all: lca.
Qed.

Lemma cnot_involutive : _CNOT_R ⟷ _CNOT_ ∝[/ C2] n_wire 2. 
Proof.
  rewrite <- compose_assoc.
  rewrite (compose_assoc (— ↕ (X 1 2 0))).
  rewrite <- (stack_compose_distr (Z 2 1 0) (Z 1 2 0) — —).
  rewrite Z_spider_1_1_fusion.
  cleanup_zx.
  rewrite (X_wrap_over_top_left 1 1).
  rewrite (X_wrap_over_top_right 1 1) at 1.
  rewrite <- wire_to_n_wire.
  rewrite <- (wire_removal_l —) at 1.
  rewrite <- (wire_removal_l —) at 6.
  rewrite 2 stack_compose_distr.
  rewrite (stack_assoc_back — — (X 1 2 0)).
  rewrite (stack_assoc_back — — (X 2 1 0)).
  simpl_casts.
  bundle_wires.
  rewrite (compose_assoc (— ↕ (⊂ ↕ —))).
  rewrite wire_to_n_wire at 3.
  rewrite (nwire_stack_compose_topleft (X 2 1 0) (Z 2 2 (0 + 0))).
  rewrite <- (nwire_stack_compose_botleft (Z 2 2 (0 + 0)) (X 2 1 0)).
  repeat rewrite <- compose_assoc.
  rewrite (compose_assoc _ (n_wire 2 ↕ (X 2 1 0))).
  rewrite <- (stack_compose_distr (n_wire 2) (n_wire (1 + 1)) (X 2 1 0) (X 1 2 0)).
  rewrite X_spider_1_1_fusion.
  rewrite Rplus_0_r.
  cbn; cleanup_zx; simpl_casts.
  rewrite (compose_assoc _ (— ↕ — ↕ X 2 2 _)).
  rewrite stack_assoc.
  simpl_casts.
  rewrite <- (stack_compose_distr — — (— ↕ X 2 2 _)).
  cleanup_zx.
  rewrite wire_to_n_wire at 7.
  rewrite <- X_wrap_over_top_left.
  rewrite (stack_assoc_back — ⊂ —).
  rewrite stack_assoc_back.
  simpl_casts.
  rewrite <- (stack_compose_distr (— ↕ ⊂) (Z 2 2 _ ↕ —) — —).
  cleanup_zx.
  rewrite wire_to_n_wire at 1.
  erewrite <- (cast_id _ _ (n_wire 1 ↕ ⊂)).
  rewrite <- Z_wrap_under_bot_left.
  erewrite <- (cast_id _ _ (Z _ (1 + 2) _));
  simpl_casts.
  rewrite wire_to_n_wire.
  rewrite grow_Z_bot_right.
  rewrite grow_X_top_left.
  rewrite stack_nwire_distribute_r.
  rewrite stack_nwire_distribute_l.
  repeat rewrite <- compose_assoc.
  rewrite (compose_assoc _ (n_wire 1 ↕ Z 1 2 0 ↕ n_wire 1)).
  rewrite stack_assoc.
  simpl_casts.
  rewrite <- wire_to_n_wire.
  rewrite <- (stack_compose_distr — — (Z 1 2 0 ↕ —)).
  rewrite <- stack_compose_distr.
  cleanup_zx.
  zxrw hopf_rule_Z_X.
  rewrite wire_to_n_wire.
  rewrite stack_nwire_distribute_r.
  rewrite stack_nwire_distribute_l.
  repeat rewrite <- compose_assoc.
  rewrite stack_assoc_back.
  simpl_casts.
  rewrite <- (stack_nwire_distribute_r (Z 1 (1 + 1) 0) (n_wire 1 ↕ Z 1 0 0 )).
  rewrite <- grow_Z_bot_right.
  rewrite compose_assoc.
  rewrite <- stack_nwire_distribute_l.
  rewrite <- X_appendix_rot_l.
  rewrite Rplus_0_r.
  rewrite Z_0_is_wire, X_0_is_wire.
  rewrite <- wire_to_n_wire.
  rewrite <- (stack_compose_distr — — — —).
  cleanup_zx.
  zxrefl.
Unshelve.
all: lia.
Qed.

Lemma cnot_is_cnot_r : _CNOT_ ∝= _CNOT_R.
Proof.
  intros.
  remember (— ↕ X 1 2 0 ⟷ (Z 2 1 0 ↕ —)) as RHS.
  rewrite (Z_wrap_under_bot_left 1 1).
  rewrite (X_wrap_over_top_left 1 1).
  simpl_casts.
  rewrite wire_to_n_wire.
  rewrite stack_nwire_distribute_l.
  rewrite stack_nwire_distribute_r.
  repeat rewrite <- compose_assoc.
  rewrite (compose_assoc _ (Z (1 + 1) 1 0 ↕ (n_wire _) ↕ _)).
  rewrite stack_assoc.
  simpl_casts.
  rewrite n_wire_stack.
  rewrite (nwire_stack_compose_botleft (Z (1 + 1) 1 0) (n_wire 1 ↕ X 1 2 0)).
  rewrite <- (nwire_stack_compose_topleft (n_wire 1 ↕ X 1 2 0)).
  rewrite <- compose_assoc.
  rewrite stack_assoc_back.
  simpl_casts.
  rewrite n_wire_stack.
  rewrite <- (stack_compose_distr ((n_wire 1) ↕ ⊂) (n_wire 3) (n_wire 1) (X 1 2 0)).
  cleanup_zx.
  rewrite <- nwire_stack_compose_topleft.
  rewrite compose_assoc.
  rewrite nwire_stack_compose_botleft.
  rewrite <- (nwire_stack_compose_topleft (⊃ ↕ n_wire 1)).
  rewrite <- compose_assoc.
  rewrite (compose_assoc _ (n_wire 1 ↕ ⊂ ↕ n_wire 2) _).
  cbn; cleanup_zx; simpl_casts.
  rewrite 2 stack_assoc; simpl_casts.
  rewrite <- stack_wire_distribute_l.
  rewrite 2 stack_assoc_back; simpl_casts.
  rewrite <- (stack_wire_distribute_r (⊂ ↕ —) (— ↕ ⊃)).
  rewrite yank_r.
  bundle_wires.
  cleanup_zx.
  subst.
  easy.
Unshelve.
all: lia.
Qed.

Lemma cnot_inv_is_swapped_cnot : _CNOT_inv_ ∝= ⨉ ⟷ _CNOT_ ⟷ ⨉.
Admitted.

Lemma notc_is_swapp_cnot : _NOTC_ ∝= ⨉ ⟷ _CNOT_ ⟷ ⨉. 
Admitted.

Lemma notc_r_is_swapp_cnot_r : _NOTC_R ∝= ⨉ ⟷ _CNOT_R ⟷ ⨉. 
Admitted.

Lemma notc_is_notc_r : _NOTC_ ∝= _NOTC_R.
Proof.
  rewrite notc_is_swapp_cnot.
  rewrite cnot_is_cnot_r.
  rewrite <- notc_r_is_swapp_cnot_r.
  easy.
Qed.