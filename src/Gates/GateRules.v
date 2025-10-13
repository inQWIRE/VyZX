Require Import QuantumLib.Quantum.
Require Export ZXCore.
Require Export GateDefinitions.
Require Export DiagramRules.
Require Export CoreRules.

Local Open Scope ZX_scope.
Local Open Scope matrix_scope.

(** Rules for manipulating gates *)

Lemma Z_is_Z : ⟦ _Z_ ⟧ = σz.
Proof.
  apply z_1_1_pi_σz.
Qed.

Lemma X_is_X : ⟦ _X_ ⟧ = σx.
Proof.
  apply x_1_1_pi_σx.
Qed.

Lemma _H_is_box : _H_ ∝[Cexp (PI/4)] □.
Proof.
  apply prop_by_iff_zx_scale.
  split; [|nonzero].
  rewrite box_decomposition_Z_X_Z.
  distribute_zxscale.
  rewrite zx_scale_eq_1_l; [reflexivity|].
  rewrite Cexp_PI4.
  C_field; lca.
Qed.

Lemma _Rz_is_Rz : forall α, ⟦ _Rz_ α ⟧ = phase_shift α.
Proof.
  intros.
  lma'.
Qed.

Lemma cnot_l_is_cnot : ⟦ _CNOT_ ⟧ = (/ (√ 2)%R) .* cnot.
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite X_2_1_0_semantics.
  restore_dims.
  compute_matrix (/ √ 2 .* cnot).
  compute_matrix (Z_semantics 1 2 0).
  rewrite Cexp_0.
  rewrite 2!make_WF_equiv.
  rewrite Kronecker.kron_I_l, Kronecker.kron_I_r.
  by_cell; lazy; lca.
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
  rewrite !cast_id.
  change (n_wire 2) with (— ↕ n_wire (0 + 1)).
  rewrite <- wire_to_n_wire, wire_to_n_wire, 2!n_wire_stack, 
    <- wire_to_n_wire.
  change (1 + (0 + 1))%nat with 2%nat.
  rewrite (compose_assoc (— ↕ (⊂ ↕ —))).
  rewrite wire_to_n_wire at 3.
  rewrite (nwire_stack_compose_topleft (X 2 1 0) (Z 2 2 (0 + 0))).
  rewrite <- (nwire_stack_compose_botleft (Z 2 2 (0 + 0)) (X 2 1 0)).
  repeat rewrite <- compose_assoc.
  rewrite (compose_assoc _ (n_wire 2 ↕ (X 2 1 0))).
  rewrite <- (stack_compose_distr (n_wire 2) (n_wire (1 + 1)) (X 2 1 0) (X 1 2 0)).
  rewrite X_spider_1_1_fusion.
  rewrite Rplus_0_r.
  rewrite nwire_removal_l.
  cbn. 
  rewrite stack_empty_r_fwd, cast_id.
  rewrite (compose_assoc _ (— ↕ — ↕ X 2 2 _)).
  rewrite stack_assoc. (* simpl_casts. *)
  rewrite cast_id.
  rewrite <- (stack_compose_distr — — (— ↕ X 2 2 _)).
  rewrite wire_removal_l.
  rewrite wire_to_n_wire at 7.
  rewrite <- X_wrap_over_top_left.
  rewrite (stack_assoc_back — ⊂ —).
  rewrite (stack_assoc_back _ — —).
  rewrite !cast_id.
  rewrite <- (stack_compose_distr (— ↕ ⊂) (Z 2 2 _ ↕ —) — —).
  rewrite wire_removal_l.
  rewrite wire_to_n_wire at 1.
  erewrite <- (cast_id _ _ (n_wire 1 ↕ ⊂)).
  rewrite <- Z_wrap_under_bot_left.
  change (2 + 1)%nat with (1 + 2)%nat.
  
  rewrite wire_to_n_wire.
  rewrite grow_Z_bot_right.
  rewrite grow_X_top_left.
  rewrite stack_nwire_distribute_r.
  rewrite stack_nwire_distribute_l.
  repeat rewrite <- compose_assoc.
  rewrite (compose_assoc _ (n_wire 1 ↕ Z 1 2 0 ↕ n_wire 1)).
  rewrite stack_assoc.
  rewrite cast_id.
  rewrite <- wire_to_n_wire.
  rewrite <- (stack_compose_distr — — (Z 1 2 0 ↕ —)).
  rewrite <- stack_compose_distr.
  rewrite wire_removal_l.
  zxrewrite hopf_rule_Z_X.
  rewrite wire_to_n_wire.
  rewrite stack_nwire_distribute_r.
  rewrite stack_nwire_distribute_l.
  repeat rewrite <- compose_assoc.
  rewrite stack_assoc_back.
  rewrite cast_id.
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
all: reflexivity.
Qed.

Lemma cnot_is_cnot_r : _CNOT_ ∝= _CNOT_R.
Proof.
  intros.
  remember (— ↕ X 1 2 0 ⟷ (Z 2 1 0 ↕ —)) as RHS.
  rewrite (Z_wrap_under_bot_left 1 1).
  rewrite (X_wrap_over_top_left 1 1).
  rewrite cast_id.
  rewrite wire_to_n_wire.
  rewrite stack_nwire_distribute_l.
  rewrite stack_nwire_distribute_r.
  repeat rewrite <- compose_assoc.
  rewrite (compose_assoc _ (Z (1 + 1) 1 0 ↕ (n_wire _) ↕ _)).
  rewrite stack_assoc.
  rewrite cast_id.
  rewrite n_wire_stack.
  rewrite (nwire_stack_compose_botleft (Z (1 + 1) 1 0) (n_wire 1 ↕ X 1 2 0)).
  rewrite <- (nwire_stack_compose_topleft (n_wire 1 ↕ X 1 2 0)).
  rewrite <- compose_assoc.
  rewrite stack_assoc_back.
  rewrite cast_id.
  rewrite n_wire_stack.
  rewrite <- (stack_compose_distr ((n_wire 1) ↕ ⊂) (n_wire 3) (n_wire 1) (X 1 2 0)).
  rewrite nwire_removal_l, nwire_removal_r.
  rewrite <- nwire_stack_compose_topleft.
  rewrite compose_assoc.
  rewrite nwire_stack_compose_botleft.
  rewrite <- (nwire_stack_compose_topleft (⊃ ↕ n_wire 1)).
  rewrite <- compose_assoc.
  rewrite (compose_assoc _ (n_wire 1 ↕ ⊂ ↕ n_wire 2) _).
  cbn; rewrite stack_empty_r_fwd, cast_id.
  (* cbn; cleanup_zx; simpl_casts. *)
  rewrite 2 (@stack_assoc 1 _ _ 1), 2 cast_id.
  rewrite <- stack_wire_distribute_l.
  rewrite (@stack_assoc_back 1 2 1 1 0 1), 
    (@stack_assoc_back 0 1 1 2 1 1), 2 cast_id.
  rewrite <- (stack_wire_distribute_r (⊂ ↕ —) (— ↕ ⊃)).
  rewrite yank_r.
  bundle_wires.
  rewrite nwire_removal_r.
  subst.
  easy.
Unshelve.
all: reflexivity.
Qed.

Import Setoid.
Import Kronecker.
Require Import ZXpermFacts.
Import CoreRules.

Local Open Scope matrix_scope.

Add Parametric Morphism n : (zx_of_perm n) with signature
  perm_eq n ==> eq as zx_of_perm_proper.
Proof.
  intros.
  now apply zx_of_perm_eq_of_perm_eq.
Qed.

Lemma cnot_states_b b0 b1 : 
  state_b b0 ↕ state_b b1 ⟷ _CNOT_ ∝=
  /√2 .* (state_b b0 ↕ state_b (b0 ⊕ b1)).
Proof.
  rewrite <- compose_assoc.
  rewrite <- stack_compose_distr, wire_removal_r.
  rewrite Z_1_2_state_b, Cexp_0, Tauto.if_same, zx_scale_1_l.
  rewrite (@stack_assoc_fwd 0 0 0 1 1 1), cast_id,
    <- (@stack_compose_distr 0 1 1 0 2 1).
  rewrite X_2_1_states_b, wire_removal_r.
  rewrite Rplus_0_l.
  rewrite (state_b_defn' (xorb _ _)).
  rewrite gadget_is_scaled_empty, const_of_zx_invsqrt2; distribute_zxscale.
  rewrite zx_scale_stack_distr_r, zx_scale_assoc.
  rewrite stack_empty_l.
  apply zx_scale_simplify_eq_l; C_field.
Qed.

Lemma cnot_inv_is_colorswap_cnot : 
  _CNOT_inv_ ∝= ⊙ _CNOT_.
Proof.
  now rewrite colorswap_is_bihadamard, ! compose_assoc.
Qed.

Lemma cnot_inv_states_b b0 b1 : 
  state_b b0 ↕ state_b b1 ⟷ _CNOT_inv_ ∝=
  /√2 .* (state_b (b0 ⊕ b1) ↕ state_b b1).
Proof.
  rewrite cnot_inv_is_colorswap_cnot.
  cbn.
  rewrite <- compose_assoc.
  rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
  rewrite X_1_n_state_b, wire_removal_r, Rplus_0_r.
  
  distribute_zxscale.
  rewrite zx_scale_compose_distr_l.
  apply zx_scale_simplify_eq_r.
  destruct b0.
  - rewrite xorb_true_l, X_0_2_PI_to_cup_not, cup_pullthrough_bot_1.
    rewrite not_defn; cbn [transpose]; rewrite <- not_defn.
    rewrite wire_removal_r.
    rewrite <- (nwire_removal_l (state_b b1)) at 1.
    rewrite stack_compose_distr.
    rewrite (@stack_assoc_fwd 1 1 0 1 1 1), cast_id.
    rewrite compose_assoc.
    rewrite <- (@stack_compose_distr 1 1 1 1 2 1).
    rewrite wire_removal_r.
    rewrite (stack_split_antidiag NOT).
    rewrite <- compose_assoc.
    rewrite stack_nwire_distribute_l, <- compose_assoc.
    rewrite (@stack_assoc_back_fwd 1 1 0 1 1 1), cast_id.
    rewrite wire_to_n_wire, n_wire_stack.
    rewrite <- (stack_split_diag ⊂ (state_b b1)).
    rewrite (stack_split_antidiag ⊂).
    rewrite (compose_assoc (n_wire 0 ↕ state_b _)).
    rewrite <- wire_to_n_wire at 2.
    rewrite <- Z_wrap_over_top_right.
    rewrite stack_empty_l.
    rewrite Z_1_2_state_b, Cexp_0, Tauto.if_same, zx_scale_1_l.
    rewrite <- (@stack_compose_distr 0 1 1 0 1 1).
    rewrite not_state_b, nwire_removal_r.
    reflexivity.
  - rewrite xorb_false_l, <- cap_X.
    rewrite stack_split_antidiag, compose_assoc.
    rewrite <- Z_wrap_over_top_right.
    rewrite stack_empty_l.
    rewrite Z_1_2_state_b, Cexp_0, Tauto.if_same, zx_scale_1_l.
    reflexivity.
Qed.

Lemma cnot_inv_is_swapped_cnot : _CNOT_inv_ ∝= ⨉ ⟷ _CNOT_ ⟷ ⨉.
Proof.
  apply prop_eq_by_eq_on_states_b_step.
  intros b0.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b1.
  rewrite <- 2 (compose_assoc (state_b b1)), <- push_out_top.
  rewrite cnot_inv_states_b.
  rewrite (compose_assoc ⨉), <- (compose_assoc (state_b _ ↕ state_b _)).
  rewrite swap_commutes_r, zx_comm_0_0, compose_empty_l.
  rewrite <- compose_assoc.
  rewrite cnot_states_b.
  distribute_zxscale.
  rewrite swap_commutes_r, zx_comm_0_0, compose_empty_l.
  now rewrite xorb_comm.
Qed.

Lemma notc_is_swapp_cnot : _NOTC_ ∝= ⨉ ⟷ _CNOT_ ⟷ ⨉. 
Proof.
  rewrite <- cnot_inv_is_swapped_cnot.
  rewrite compose_assoc.
  rewrite <- colorswap_is_bihadamard.
  rewrite cnot_is_cnot_r.
  easy.
Qed.

Lemma notc_r_is_swapp_cnot_r : _NOTC_R ∝= ⨉ ⟷ _CNOT_R ⟷ ⨉. 
Proof.
  rewrite <- cnot_is_cnot_r.
  rewrite <- cnot_inv_is_swapped_cnot.
  rewrite compose_assoc.
  rewrite <- colorswap_is_bihadamard.
  easy.
Qed.

Lemma notc_is_notc_r : _NOTC_ ∝= _NOTC_R.
Proof.
  rewrite notc_is_swapp_cnot.
  rewrite cnot_is_cnot_r.
  rewrite <- notc_r_is_swapp_cnot_r.
  easy.
Qed.

