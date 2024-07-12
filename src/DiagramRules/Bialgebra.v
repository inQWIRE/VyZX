Require Import CoreData.
Require Import CoreRules.

Definition bi_alg_Z_X := ((Z 1 2 0) ↕ (Z 1 2 0) ⟷ (— ↕ ⨉ ↕ —) ⟷ ((X 2 1 0) ↕ (X 2 1 0))).
Definition bi_alg_X_Z := ((X 1 2 0) ↕ (X 1 2 0) ⟷ (— ↕ ⨉ ↕ —) ⟷ ((Z 2 1 0) ↕ (Z 2 1 0))).

Theorem bi_algebra_rule_Z_X : 
 X 2 1 0 ⟷ Z 1 2 0 ∝ bi_alg_Z_X.
Proof.
  prop_exists_nonzero (√ 2)%R.
  rewrite 2 ZX_semantic_equiv.
  unfold_dirac_spider.
  autorewrite with Cexp_db.
  simpl.
  unfold xbasis_plus, xbasis_minus.
  repeat rewrite kron_1_l; try auto with wf_db.
  repeat rewrite Mscale_1_l.
  repeat rewrite Mmult_adjoint.
  repeat rewrite hadamard_sa.
  repeat rewrite ket2bra.
  autorewrite with scalar_move_db.
  apply Mscale_simplify; [ | C_field_simplify; [easy | nonzero]].
  solve_matrix.
  all: unfold braplus, braminus, scale, Mplus, adjoint, qubit0, qubit1.
  all: repeat rewrite Cconj_R.
  all: C_field_simplify; [ lca | nonzero].
Qed.

Theorem bi_algebra_rule_X_Z : 
 Z 2 1 0 ⟷ X 1 2 0 ∝ bi_alg_X_Z.
Proof.
  colorswap_of bi_algebra_rule_Z_X.
Qed.


Theorem hopf_rule_Z_X : 
  Z 1 2 0 ⟷ X 2 1 0 ∝ Z 1 0 0 ⟷ X 0 1 0.
Proof.
  intros.
  rewrite <- (@nwire_removal_r 2).
  simpl.
  rewrite stack_empty_r.
  simpl_casts.
  rewrite wire_loop at 1.
  rewrite cap_Z.
  rewrite cup_X.
  replace (0%R) with (0 + 0)%R by lra.
  rewrite <- (@Z_spider_1_1_fusion 0 2).
  rewrite <- X_spider_1_1_fusion.
  replace (0 + 0)%R with 0 by lra.
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
  assert (Hl : (Z 0 1 0 ↕ Z 1 2 0) ⟷ ((Z) 1 2 0 ↕ n_wire 2) ∝ Z 0 1 0 ↕ n_wire 1 ⟷ (Z 1 2 0 ↕ Z 1 2 0)).
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
  assert (Hr : X 2 1 0 ↕ n_wire 2 ⟷ (X 1 0 0 ↕ X 2 1 0) ∝ X 2 1 0 ↕ (X) 2 1 0 ⟷ ((X) 1 0 0 ↕ n_wire 1)).
  {
    rewrite <- stack_compose_distr.
    rewrite nwire_removal_l.
    rewrite <- (nwire_removal_r (X 2 1 0)) at 2.
    rewrite stack_compose_distr.
    easy.
  }
  rewrite Hr.
  repeat rewrite <- compose_assoc.
  assert (HBiAlgAssoc : (Z) 0 1 0 ↕ n_wire 1 ⟷ ((Z) 1 2 0 ↕ (Z) 1 2 0) ⟷ (n_wire 1 ↕ ⨉ ↕ n_wire 1) ⟷ ((X) 2 1 0 ↕ (X) 2 1 0) ⟷ ((X) 1 0 0 ↕ n_wire 1) ∝ 
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
  rewrite <- bi_algebra_rule_Z_X.
  assert (X_Wrap_Under_L_base : forall α, X 2 1 α ∝ (X 1 2 α ↕ —) ⟷ (— ↕ ⊃)).
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
  rewrite Z_state_0_copy.
  simpl_casts.
  simpl.
  cleanup_zx; simpl_casts.
  rewrite (stack_assoc (Z 0 1 0) ((Z) (0 + 0) (1 + 0) 0) —).
  simpl_casts.
  rewrite <- (stack_compose_distr ((Z) 0 1 0) — ((Z) (0 + 0) (1 + 0) 0 ↕ —) ⊃).
  assert (Hl: (Z) (0 + 0) (1 + 0) 0 ↕ — ⟷ ⊃ ∝ Z 1 0 0). (* Todo : pull out lemma *)
  {
    rewrite cup_Z.
    rewrite <- Z_0_is_wire.
    rewrite <- Z_add_l.
    rewrite 2 Rplus_0_r.
    easy.
  }
  rewrite Hl.
  cleanup_zx.
  rewrite (stack_empty_r_rev (Z 1 2 0)).
  simpl_casts.
  rewrite <- (stack_compose_distr (Z 0 1 0) (Z 1 2 0) (Z 1 0 0) ⦰).
  cleanup_zx.
  rewrite Z_spider_1_1_fusion.
  rewrite Rplus_0_r.
  rewrite <- cap_Z.
  rewrite (disconnected_stack_compose_r).
  simpl_casts.
  assert (Hr : ⊂ ⟷ ((X) 1 0 0 ↕ —) ∝ X 0 1 0).
  {
    rewrite cap_X.
    rewrite <- X_0_is_wire.
    rewrite <- X_add_r.
    rewrite 2 Rplus_0_r.
    easy.
  }
  rewrite compose_assoc.
  rewrite Hr.
  easy.
Unshelve.
all: lia.
Qed.

Theorem hopf_rule_X_Z : 
  (X 1 2 0) ⟷ (Z 2 1 0) ∝ (X 1 0 0) ⟷ (Z 0 1 0).
Proof.
  colorswap_of hopf_rule_Z_X.
Qed.