Require Import CoreData.
Require Import CoreRules.

Definition bi_alg_Z_X := ((Z_Spider 1 2 0) ↕ (Z_Spider 1 2 0) ⟷ (— ↕ ⨉ ↕ —) ⟷ ((X_Spider 2 1 0) ↕ (X_Spider 2 1 0))).
Definition bi_alg_X_Z := ((X_Spider 1 2 0) ↕ (X_Spider 1 2 0) ⟷ (— ↕ ⨉ ↕ —) ⟷ ((Z_Spider 2 1 0) ↕ (Z_Spider 2 1 0))).

Theorem bi_algebra_rule_Z_X : 
 (X_Spider 2 1 0) ⟷ (Z_Spider 1 2 0) ∝ bi_alg_Z_X.
Proof.
  prop_exists_nonzero 1.
  simpl.
  rewrite X_semantics_equiv, Z_semantics_equiv.
  unfold_dirac_spider.
  autorewrite with Cexp_db.
  Msimpl.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite kron_plus_distr_r.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mmult_plus_distr_r.
  repeat rewrite Mmult_plus_distr_l.
  assert (forall (ket0 : Matrix 2 1) (bra0 : Matrix 1 2) (ket1 : Matrix 2 1) (bra1 : Matrix 1 2), 
  WF_Matrix ket0 -> WF_Matrix ket1 ->
  ket0⊤ = bra0 -> ket1⊤ = bra1 ->
  (ket0 × (bra0 ⊗ bra0)) ⊗ (ket1 × (bra1 ⊗ bra1)) × (I 2 ⊗ swap ⊗ I 2) 
  = (ket0 × (bra0 ⊗ bra1) ⊗ (ket1 × (bra0 ⊗ bra1))))%M.
  {
    intros.
    subst bra0 bra1.
    rewrite kron_assoc; try auto with wf_db.
    rewrite <- 2 kron_mixed_product.
    rewrite Mmult_assoc.
    apply Mmult_simplify; [ easy | ].
    restore_dims.
    repeat rewrite kron_assoc by auto with wf_db.
    rewrite (kron_mixed_product (ket0⊤) (ket0⊤ ⊗ (ket1⊤ ⊗ ket1⊤)) (I 2) _)%M.
    Msimpl.
    apply kron_simplify; [ easy | ].
    rewrite <- 2 kron_assoc by auto with wf_db.
    rewrite (kron_mixed_product (ket0⊤ ⊗ ket1⊤) (ket1⊤) swap _)%M.
    Msimpl.
    apply kron_simplify; [ | easy].
    apply transpose_matrices.
    rewrite Mmult_transpose.
    rewrite swap_transpose.
    rewrite <- 2 kron_transpose.
    rewrite 2 Matrix.transpose_involutive.
    rewrite swap_spec by auto with wf_db.
    easy.
  }
  repeat rewrite <- Mmult_assoc.
  restore_dims.
  rewrite bra0_equiv, bra1_equiv, ket0_equiv, ket1_equiv.
  repeat rewrite H; try auto with wf_db.
  2-9: apply transpose_matrices; try rewrite braplus_transpose_ketplus; try rewrite braminus_transpose_ketminus; rewrite Matrix.transpose_involutive; easy.
  restore_dims.
  repeat rewrite (kron_mixed_product (xbasis_plus × (_ ⊗ _)) (xbasis_plus × (_ ⊗ _))  ((ket _ ⊗ ket _) × bra _) ((ket _ ⊗ ket _) × bra _)).
  repeat rewrite (kron_mixed_product (xbasis_minus × (_ ⊗ _)) (xbasis_minus × (_ ⊗ _))  ((ket _ ⊗ ket _) × bra _) ((ket _ ⊗ ket _) × bra _)).
  repeat rewrite Mmult_assoc.
Admitted.

Theorem bi_algebra_rule_X_Z : 
 (Z_Spider 2 1 0) ⟷ (X_Spider 1 2 0) ∝ bi_alg_X_Z.
Proof.
  colorswap_of bi_algebra_rule_Z_X.
Qed.


Theorem hopf_rule_Z_X : 
  (Z_Spider 1 2 0) ⟷ (X_Spider 2 1 0) ∝ (Z_Spider 1 0 0) ⟷ (X_Spider 0 1 0).
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
  rewrite (stack_assoc (𝒵 0 1 0) (n_wire 1) (n_wire 1)).
  rewrite (stack_assoc (𝒵 1 2 0) (n_wire 1) (n_wire 1)).
  rewrite (stack_assoc (𝒳 1 0 0) (n_wire 1) (n_wire 1)).
  rewrite (stack_assoc (𝒳 2 1 0) (n_wire 1) (n_wire 1)).
  simpl_casts.
  rewrite n_wire_stack.
Opaque n_stack1.
  simpl.
  repeat rewrite <- compose_assoc.
  rewrite <- (push_out_top (𝒵 0 1 0)).
  assert (Hl : (𝒵 0 1 0 ↕ 𝒵 1 2 0) ⟷ (𝒵 1 2 0 ↕ n_wire 2) ∝ 𝒵 0 1 0 ↕ n_wire 1 ⟷ (𝒵 1 2 0 ↕ 𝒵 1 2 0)).
  {
    rewrite <- stack_compose_distr.
    rewrite nwire_removal_r.
    rewrite <- (nwire_removal_l (𝒵 1 2 0)) at 2.
    rewrite stack_compose_distr.
    easy.
  }
  rewrite Hl.
  repeat rewrite compose_assoc.
  rewrite <- (pull_out_top (𝒳 1 0 0)).
  assert (Hr : 𝒳 2 1 0 ↕ n_wire 2 ⟷ (𝒳 1 0 0 ↕ 𝒳 2 1 0) ∝ 𝒳 2 1 0 ↕ 𝒳 2 1 0 ⟷ (𝒳 1 0 0 ↕ n_wire 1)).
  {
    rewrite <- stack_compose_distr.
    rewrite nwire_removal_l.
    rewrite <- (nwire_removal_r (𝒳 2 1 0)) at 2.
    rewrite stack_compose_distr.
    easy.
  }
  rewrite Hr.
  repeat rewrite <- compose_assoc.
  assert (HBiAlgAssoc : 𝒵 0 1 0 ↕ n_wire 1 ⟷ (𝒵 1 2 0 ↕ 𝒵 1 2 0) ⟷ (n_wire 1 ↕ ⨉ ↕ n_wire 1) ⟷ (𝒳 2 1 0 ↕ 𝒳 2 1 0) ⟷ (𝒳 1 0 0 ↕ n_wire 1) ∝ 
    𝒵 0 1 0 ↕ n_wire 1 ⟷ ((𝒵 1 2 0 ↕ 𝒵 1 2 0) ⟷ (n_wire 1 ↕ ⨉ ↕ n_wire 1) ⟷ (𝒳 2 1 0 ↕ 𝒳 2 1 0)) ⟷ (𝒳 1 0 0 ↕ n_wire 1)).
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
  assert (X_Wrap_Under_L_base : forall α, 𝒳 2 1 α ∝ (𝒳 1 2 α ↕ —) ⟷ (— ↕ ⊃)) by admit.
  (* TODO : resurect and make 𝒳 rules *)
  rewrite X_Wrap_Under_L_base.
  repeat rewrite <- compose_assoc.
  rewrite <- stack_wire_distribute_r.
  rewrite Z_state_0_copy.
  simpl_casts.
  simpl.
  cleanup_zx; simpl_casts.
  rewrite (stack_assoc (𝒵 0 1 0) (𝒵 (0 + 0) (1 + 0) 0) —).
  simpl_casts.
  rewrite <- (stack_compose_distr (𝒵 0 1 0) — (𝒵 (0 + 0) (1 + 0) 0 ↕ —) ⊃).
  assert (Hl: 𝒵 (0 + 0) (1 + 0) 0 ↕ — ⟷ ⊃ ∝ 𝒵 1 0 0). (* Todo : pull out lemma *)
  {
    rewrite cup_Z.
    rewrite <- Z_0_is_wire.
    rewrite <- Z_add_l.
    rewrite 2 Rplus_0_r.
    easy.
  }
  rewrite Hl.
  cleanup_zx.
  rewrite (stack_empty_r_rev (𝒵 1 2 0)).
  simpl_casts.
  rewrite <- (stack_compose_distr (𝒵 0 1 0) (𝒵 1 2 0) (𝒵 1 0 0) ⦰).
  cleanup_zx.
  rewrite Z_spider_1_1_fusion.
  rewrite Rplus_0_r.
  rewrite <- cap_Z.
  rewrite (disconnected_stack_compose_r).
  simpl_casts.
  assert (Hr : ⊂ ⟷ (𝒳 1 0 0 ↕ —) ∝ 𝒳 0 1 0).
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
Admitted.

Theorem hopf_rule_X_Z : 
  (X_Spider 1 2 0) ⟷ (Z_Spider 2 1 0) ∝ (X_Spider 1 0 0) ⟷ (Z_Spider 0 1 0).
Proof.
  colorswap_of hopf_rule_Z_X.
Qed.