Require Import QuantumLib.Quantum.
Require Export ZXCore.
Require Export GateDefinitions.
Require Export CoreRules.
Require Export DiagramRules.

Local Open Scope ZX_scope.

Lemma Z_is_Z : ZX_semantics (_Z_) = σz.
Proof.
  simpl.
  unfold Z_semantics.
  autorewrite with Cexp_db.
  simpl.
  solve_matrix.
Qed.

Lemma X_is_X : ZX_semantics (_X_) = σx.
Proof.
  simpl.
  unfold X_semantics; solve_matrix.
  all: autorewrite with Cexp_db.
  all: C_field_simplify; try lca.
  all: split; nonzero.
Qed.


Lemma _H_is_box : _H_ ∝ □.
Proof.
  prop_exists_nonzero (Cexp (PI/4)).
  simpl.
  unfold X_semantics, Z_semantics.
  Msimpl.
  solve_matrix;
  field_simplify_eq [Cexp_PI2 Cexp_PI4 Ci2 Csqrt2_sqrt2_inv Csqrt2_inv]; 
  try apply c_proj_eq; try simpl; try R_field_simplify; try reflexivity; (try split; try apply RtoC_neq; try apply sqrt2_neq_0; try auto).
Qed.


Lemma cnot_l_is_cnot : ZX_semantics _CNOT_ = (/ √ 2)%C .* cnot.
Proof.
  simpl.
  unfold Z_semantics, X_semantics.
  solve_matrix.
  all: autorewrite with Cexp_db.
  all: lca.
Qed.

Lemma cnot_inv_is_swapped_cnot : ZX_semantics _CNOT_inv_ = (/ √ 2)%C .* (swap × cnot × swap)%M.
Proof.
  simpl.
  unfold Z_semantics, X_semantics.
  solve_matrix.
  all: autorewrite with Cexp_db.
  all: lca.
Qed.

Lemma _Rz_is_Rz : forall α, ZX_semantics (_Rz_ α) = phase_shift α.
Proof.
  intros.
  simpl.
  unfold Z_semantics, phase_shift.
  simpl.
  lma.
Qed.

Lemma cnot_involutive : _CNOT_R ⟷ _CNOT_ ∝ n_wire 2. 
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
  rewrite wire_to_n_wire at 3 4 6 7.
  rewrite n_wire_stack.
  rewrite (compose_assoc (— ↕ (⊂ ↕ —))).
  rewrite wire_to_n_wire at 4.
  rewrite (nwire_stack_compose_topleft (X 2 1 0) (Z 2 2 (0 + 0))).
  rewrite <- (nwire_stack_compose_botleft (Z 2 2 (0 + 0)) (X 2 1 0)).
  repeat rewrite <- compose_assoc.
  rewrite (compose_assoc _ (n_wire 2 ↕ (X 2 1 0))).
  rewrite <- (stack_compose_distr (n_wire 2) (n_wire (1 + 1)) (X 2 1 0) (X 1 2 0)).
  rewrite X_spider_1_1_fusion.
  rewrite Rplus_0_r.
  simpl; cleanup_zx; simpl_casts.
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
  rewrite <- (cast_id (eq_sym (Nat.add_0_r _)) (wrap_under_dimension 1) (n_wire 1 ↕ ⊂)).
  rewrite <- Z_wrap_under_bot_left.
  assert (1 = 1 + 0)%nat as Hcast by lia;
  rewrite <- (cast_id Hcast (eq_refl) (Z _ (1 + 2) _));
  simpl_casts;
  clear Hcast.
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
  rewrite hopf_rule_Z_X.
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
  easy.
Qed.

Lemma cnot_is_cnot_r : _CNOT_ ∝ _CNOT_R.
Proof.
  intros.
  remember (— ↕ X 1 2 0 ⟷ (Z 2 1 0 ↕ —)) as RHS.
  rewrite (Z_wrap_under_bot_left 1 1).
  rewrite (X_wrap_over_top_left 1 1).
  simpl_casts.
  rewrite wire_to_n_wire at 2 3 4 5.
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
  simpl; cleanup_zx; simpl_casts.
  rewrite 2 stack_assoc; simpl_casts.
  rewrite <- stack_wire_distribute_l.
  rewrite 2 stack_assoc_back; simpl_casts.
  rewrite <- (stack_wire_distribute_r (⊂ ↕ —) (— ↕ ⊃)).
  rewrite yank_r.
  rewrite wire_to_n_wire.
  rewrite 2 n_wire_stack.
  cleanup_zx.
  rewrite <- wire_to_n_wire.
  subst.
  easy.
Qed.
