Require Import ZXpermFacts.
Require Import CoreData.
Require Import CoreRules.

Definition bi_alg_Z_X := ((Z_Spider 1 2 0) ↕ (Z_Spider 1 2 0) 
  ⟷ (— ↕ ⨉ ↕ —) ⟷ ((X_Spider 2 1 0) ↕ (X_Spider 2 1 0))).
Definition bi_alg_X_Z := ((X_Spider 1 2 0) ↕ (X_Spider 1 2 0) 
  ⟷ (— ↕ ⨉ ↕ —) ⟷ ((Z_Spider 2 1 0) ↕ (Z_Spider 2 1 0))).

Theorem bi_algebra_rule_Z_X : 
 (X_Spider 2 1 0) ⟷ (Z_Spider 1 2 0) ∝[(√2)%R] bi_alg_Z_X.
Proof.
  rewrite prop_by_iff_zx_scale.
  split; [|nonzero].
  unfold bi_alg_Z_X.
  apply prop_eq_by_eq_on_states_b_step; intros b0.
  apply prop_eq_by_eq_on_states_b_step; intros b1.
  rewrite stack_empty_r_fwd, cast_id.
  cbn -[n_wire].
  distribute_zxscale.
  rewrite <- 5 compose_assoc.
  rewrite <- (@push_out_top 0 1 1).
  rewrite X_2_1_states_b.
  rewrite Rplus_0_l.
  assert (Hrw : (if b0 ⊕ b1 then PI else 0%R) = 
    ((b0 ⊕ b1) * PI)%R)
    by (destruct (b0 ⊕ b1); cbn; lra).
  rewrite Hrw.
  distribute_zxscale.
  rewrite (to_scale X_state_copy_phase_0).
  distribute_zxscale.
  rewrite cast_id.
  rewrite <- (@stack_compose_distr 0 1 2 0 1 2).
  rewrite 2 Z_1_2_state_b.
  cbn [n_stack]; rewrite stack_empty_r_fwd, cast_id.
  rewrite Cexp_0, 2 Tauto.if_same, 2 zx_scale_1_l.
  rewrite (@stack_assoc_back_fwd 0 0 0 2 1 1), cast_id.
  rewrite <- (@stack_compose_distr 0 3 3 0 1 1).
  rewrite (@stack_assoc_fwd 0 0 0 1 1 1), cast_id.
  rewrite <- (@stack_compose_distr 0 1 1 0 2 2).
  rewrite (@swap_commutes_r 0 0), zx_comm_0_0, compose_empty_l.
  rewrite 2 wire_removal_r.
  rewrite (@stack_assoc_back_fwd 0 0 0 1 1 1), cast_id.
  rewrite (@stack_assoc_fwd 0 0 0 2 1 1), cast_id.
  rewrite <- (@stack_compose_distr 0 2 1 0 2 1).
  rewrite X_2_1_states_b, Rplus_0_l, Hrw.
  rewrite zx_scale_stack_distr_l, zx_scale_stack_distr_r, 
    2 zx_scale_assoc.
  apply zx_scale_simplify_eq_l.
  cbn.
  autorewrite with RtoC_db.
  C_field.
  Unshelve. all: reflexivity.
Qed.

Theorem bi_algebra_rule_X_Z : 
 (Z_Spider 2 1 0) ⟷ (X_Spider 1 2 0) ∝[(√2)%R] bi_alg_X_Z.
Proof.
  colorswap_of bi_algebra_rule_Z_X.
Qed.


Theorem hopf_rule_Z_X : 
  (Z_Spider 1 2 0) ⟷ (X_Spider 2 1 0) ∝[/C2] (Z_Spider 1 0 0) ⟷ (X_Spider 0 1 0).
Proof.
  (* Faster, semantic proof: 
  
  prop_exists_nonzero (/2).
  prep_matrix_equivalence.
  simpl.
  unfold X_semantics.
  cbn [kron_n].
  rewrite kron_1_l, Mmult_1_r by (auto using WF_Matrix_dim_change with wf_db).
  rewrite (Z_semantics_comm 1 2 0), (Z_semantics_comm 1 0 0), Ropp_0.
  restore_dims.
  compute_matrix (hadamard × Z_semantics 2 1 0 × (hadamard ⊗ hadamard)).
  compute_matrix (hadamard × Z_semantics 0 1 0).
  rewrite Cexp_0.
  rewrite 2!Cmult_1_r.
  group_radicals.
  rewrite Copp_involutive, 2!Cplus_opp_r. 
  rewrite <- Cmult_plus_distr_l, Cplus_div2, Cmult_1_r, <- Cdouble.
  compute_matrix (Z_semantics 2 1 0).
  compute_matrix (Z_semantics 0 1 0).
  rewrite !make_WF_equiv.
  rewrite Cexp_0.
  replace (C2 * /√2) with (√2 : C) by C_field.
  unfold adjoint, Mmult, scale.
  by_cell; cbn; rewrite ?Cconj_R; try lca; C_field.
  *)
  intros.
  rewrite <- (@nwire_removal_r 2).
  cbv delta [n_wire]; simpl.
  rewrite stack_empty_r.
  simpl_casts.
  rewrite wire_loop at 1.
  rewrite cap_Z.
  rewrite cup_X.
  replace (0%R) with (0 + 0)%R by lra.
  rewrite <- (@Z_spider_1_1_fusion 0 2).
  rewrite <- X_spider_1_1_fusion.
  replace (0 + 0)%R with R0 by lra.
  repeat rewrite stack_wire_distribute_r.
  repeat rewrite compose_assoc.
  rewrite wire_to_n_wire.
  rewrite (stack_assoc (Z 0 1 0) (n_wire 1) (n_wire 1)).
  rewrite (stack_assoc (Z 1 2 0) (n_wire 1) (n_wire 1)).
  rewrite (stack_assoc (X 1 0 0) (n_wire 1) (n_wire 1)).
  rewrite (stack_assoc (X 2 1 0) (n_wire 1) (n_wire 1)).
  simpl_casts.
  rewrite n_wire_stack.
Opaque n_stack1.
  simpl.
  repeat rewrite <- compose_assoc.
  rewrite <- (push_out_top (Z 0 1 0)).
  assert (Hl : (Z 0 1 0 ↕ Z 1 2 0) ⟷ ((Z) 1 2 0 ↕ n_wire 2) ∝= Z 0 1 0 ↕ n_wire 1 ⟷ (Z 1 2 0 ↕ Z 1 2 0)).
  {
    rewrite <- stack_compose_distr.
    rewrite nwire_removal_r.
    rewrite <- (nwire_removal_l (Z 1 2 0)) at 2.
    rewrite stack_compose_distr.
    easy.
  }
  rewrite Hl.
  repeat rewrite compose_assoc.
  rewrite <- (pull_out_top (X 1 0 0)).
  assert (Hr : X 2 1 0 ↕ n_wire 2 ⟷ (X 1 0 0 ↕ X 2 1 0) ∝= X 2 1 0 ↕ (X) 2 1 0 ⟷ ((X) 1 0 0 ↕ n_wire 1)).
  {
    rewrite <- stack_compose_distr.
    rewrite nwire_removal_l.
    rewrite <- (nwire_removal_r (X 2 1 0)) at 2.
    rewrite stack_compose_distr.
    easy.
  }
  rewrite Hr.
  repeat rewrite <- compose_assoc.
  assert (HBiAlgAssoc : (Z) 0 1 0 ↕ n_wire 1 ⟷ ((Z) 1 2 0 ↕ (Z) 1 2 0) ⟷ (n_wire 1 ↕ ⨉ ↕ n_wire 1) ⟷ ((X) 2 1 0 ↕ (X) 2 1 0) ⟷ ((X) 1 0 0 ↕ n_wire 1) ∝= 
    (Z) 0 1 0 ↕ n_wire 1 ⟷ (((Z) 1 2 0 ↕ (Z) 1 2 0) ⟷ (n_wire 1 ↕ ⨉ ↕ n_wire 1) ⟷ ((X) 2 1 0 ↕ (X) 2 1 0)) ⟷ ((X) 1 0 0 ↕ n_wire 1)).
  {
    repeat rewrite compose_assoc.
    easy.
  }
  rewrite HBiAlgAssoc.
  clear Hl Hr HBiAlgAssoc.
  rewrite <- wire_to_n_wire.
Transparent n_stack1.
  fold bi_alg_Z_X.
  zxrewrite <- bi_algebra_rule_Z_X.
  assert (X_Wrap_Under_L_base : forall α, X 2 1 α ∝= (X 1 2 α ↕ —) ⟷ (— ↕ ⊃)).
  {
    intros.
    rewrite (X_wrap_under_bot_right 1).
    simpl_casts.
    rewrite <- wire_to_n_wire.
    easy.
  }
  rewrite X_Wrap_Under_L_base.
  repeat rewrite <- compose_assoc.
  rewrite <- stack_wire_distribute_r.
  zxrewrite Z_state_0_copy.
  simpl_casts.
  simpl.
  cleanup_zx; simpl_casts.
  rewrite (stack_assoc (Z 0 1 0) ((Z) (0 + 0) (1 + 0) 0) —).
  simpl_casts.
  rewrite <- (stack_compose_distr ((Z) 0 1 0) — ((Z) (0 + 0) (1 + 0) 0 ↕ —) ⊃).
  assert (Hl: (Z) (0 + 0) (1 + 0) 0 ↕ — ⟷ ⊃ ∝= Z 1 0 0). (* Todo : pull out lemma *)
  {
    rewrite cup_Z.
    rewrite <- Z_0_is_wire.
    rewrite <- Z_add_l.
    rewrite 2 Rplus_0_r.
    easy.
  }
  rewrite Hl.
  cleanup_zx.
  rewrite (stack_empty_r_back (Z 1 2 0)).
  simpl_casts.
  rewrite <- (stack_compose_distr (Z 0 1 0) (Z 1 2 0) (Z 1 0 0) ⦰).
  cleanup_zx.
  rewrite Z_spider_1_1_fusion.
  rewrite Rplus_0_r.
  rewrite <- cap_Z.
  rewrite (disconnected_stack_compose_r).
  simpl_casts.
  assert (Hr : ⊂ ⟷ ((X) 1 0 0 ↕ —) ∝= X 0 1 0).
  {
    rewrite cap_X.
    rewrite <- X_0_is_wire.
    rewrite <- X_add_r.
    rewrite 2 Rplus_0_r.
    easy.
  }
  rewrite compose_assoc.
  rewrite Hr.
  zxrefl.
  autorewrite with RtoC_db; C_field.
Unshelve.
all: reflexivity.
Qed.

Theorem hopf_rule_X_Z : 
  (X_Spider 1 2 0) ⟷ (Z_Spider 2 1 0) ∝[/ 2] (X_Spider 1 0 0) ⟷ (Z_Spider 0 1 0).
Proof.
  colorswap_of hopf_rule_Z_X.
Qed.