Require Import QuantumLib.Quantum.
Require Export ZXCore.
Require Export GateDefinitions.
Require Export DiagramRules.
Require Export CoreRules.

Local Open Scope ZX_scope.

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
  by_cell; cbv; lca.
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
  cbn; cleanup_zx; simpl_casts.
  rewrite (compose_assoc _ (— ↕ — ↕ X 2 2 _)).
  rewrite stack_assoc. (* simpl_casts. *)
  rewrite cast_id.
  rewrite <- (stack_compose_distr — — (— ↕ X 2 2 _)).
  cleanup_zx.
  rewrite wire_to_n_wire at 7.
  rewrite <- X_wrap_over_top_left.
  rewrite (stack_assoc_back — ⊂ —).
  rewrite (stack_assoc_back _ — —).
  rewrite !cast_id.
  rewrite <- (stack_compose_distr (— ↕ ⊂) (Z 2 2 _ ↕ —) — —).
  cleanup_zx.
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
  cleanup_zx.
  zxrw hopf_rule_Z_X.
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

Import Setoid.
Import Kronecker.
Require Import ZXpermFacts.
Import CoreRules.


Add Parametric Morphism n : (zx_of_perm n) with signature
  perm_eq n ==> eq as zx_of_perm_proper.
Proof.
  intros.
  now apply zx_of_perm_eq_of_perm_eq.
Qed.

Lemma cnot_inv_is_swapped_cnot : _CNOT_inv_ ∝ ⨉ ⟷ _CNOT_ ⟷ ⨉.
Proof.
  symmetry.
  rewrite <- compose_assoc.
  rewrite swap_commutes_l.
  rewrite !compose_assoc.
  rewrite (swap_pullthrough_l — (X 2 1 0)).
  rewrite <- (compose_assoc (zx_comm 1 2)).
  unfold zx_comm, zx_of_perm_cast.
  simpl_casts.
  rewrite compose_zx_of_perm by auto with perm_db.
  assert (H : perm_eq (1 + 2) 
    (big_swap_perm 2 1 ∘ big_swap_perm 2 1)%prg
    (big_swap_perm 1 2))
    by (by_perm_cell; reflexivity).
  rewrite H.
  clear H.
  rewrite <- (compose_assoc _ _ (2 ↑ □)).
  rewrite <- colorswap_is_bihadamard.
  simpl.
  prop_exists_nonzero 1.
  rewrite Mscale_1_l.
  simpl.
  rewrite zx_of_perm_semantics by auto with perm_db.
  simpl_rewrite' (kron_comm_pows2_eq_perm_to_matrix_big_swap 2 1).
  rewrite !X_semantics_equiv, !Z_semantics_equiv.
  simpl.
  rewrite Cexp_0.
  Msimpl.
  restore_dims.
  distribute_plus.
  restore_dims.
  rewrite 2!kron_id_dist_r by auto_wf.
  rewrite 2!(Mmult_assoc _ _ (kron_comm 2 4)).
  restore_dims.
  rewrite 2!kron_assoc by auto_wf.
  restore_dims.
  rewrite 2!kron_comm_commutes_r by auto_wf.
  rewrite kron_comm_1_l.
  rewrite 2!Mmult_1_l by auto_wf.
  rewrite <- kron_plus_distr_r, <- kron_plus_distr_l, <- !Mmult_plus_distr_r.
  rewrite <- kron_plus_distr_l.
  restore_dims.
  unfold xbasis_plus, xbasis_minus, braplus, braminus.
  autorewrite with scalar_move_db.
  f_equal; [lca|].
  rewrite <- (kron_1_r _ _ (_ ⊗ I 2)).
  restore_dims.
  rewrite 2!kron_mixed_product.
  rewrite !Mmult_1_l by auto_wf.

  rewrite <- (kron_1_r _ _ ((_ .+ _ .* _) ⊗ I 2)).
  restore_dims.
  rewrite 2!kron_mixed_product.
  rewrite !Mmult_1_l by auto_wf.
  prep_matrix_equivalence.
  replace (∣0⟩ .+ ∣1⟩) with (@const_matrix 2 1 1) by lma'.
  replace (⟨0∣ .+ ⟨1∣) with (@const_matrix 1 2 1) by lma'.
  rewrite Mmult_const.
  replace (-1:C) with (- C1) by lca.
  compute_matrix ((∣0⟩ .+ - C1 .* ∣1⟩) × (⟨0∣ .+ - C1 .* ⟨1∣)).
  autorewrite with C_db.
  match goal with |- context [?A .+ ?B] => 
    compute_matrix (A .+ B) end.
  compute_matrix (I 2 ⊗ (∣0⟩ ⊗ ∣0⟩ × ⟨0∣ .+ ∣1⟩ ⊗ ∣1⟩ × ⟨1∣)).
  restore_dims.
  compute_matrix (∣0⟩ × (⟨0∣ ⊗ ⟨0∣) .+ ∣1⟩ × (⟨1∣ ⊗ ⟨1∣)).
  match goal with |- context [?A .+ ?B] => 
    compute_matrix (A .+ B) end.
  autorewrite with C_db.
  rewrite !make_WF_equiv, kron_I_l, kron_I_r.
  by_cell; cbv; lca.
Qed.

Lemma notc_is_swapp_cnot : _NOTC_ ∝ ⨉ ⟷ _CNOT_ ⟷ ⨉.
Proof.
  symmetry.
  rewrite <- compose_assoc.
  rewrite swap_commutes_l.
  rewrite !compose_assoc.
  rewrite (swap_pullthrough_l — (X 2 1 0)).
  rewrite <- (compose_assoc (zx_comm 1 2)).
  unfold zx_comm, zx_of_perm_cast.
  simpl_casts.
  rewrite compose_zx_of_perm by auto with perm_db.
  assert (H : perm_eq (1 + 2) 
    (big_swap_perm 2 1 ∘ big_swap_perm 2 1)%prg
    (big_swap_perm 1 2))
    by (by_perm_cell; reflexivity).
  rewrite H.
  clear H.
  assert (H : zx_of_perm (1 + 2) (big_swap_perm 1 2) ∝ — ↕ ⨉ ⟷ (⨉ ↕ —)). 1: {
    by_perm_eq_nosimpl.
    rewrite perm_of_zx_of_perm_eq by auto with perm_db. 
    by_perm_cell; reflexivity.
  }
  rewrite H.
  rewrite <- !compose_assoc, <- stack_wire_distribute_l.
  rewrite Z_zxperm_absorbtion_right by constructor.
  rewrite compose_assoc, <- (stack_wire_distribute_r ⨉ (X 2 1 0)).
  now rewrite X_zxperm_absorbtion_left by constructor.
Qed.

Lemma notc_r_is_swapp_cnot_r : _NOTC_R ∝ ⨉ ⟷ _CNOT_R ⟷ ⨉. 
Proof.
  symmetry.
  rewrite <- compose_assoc.
  rewrite swap_commutes_l.
  rewrite !compose_assoc.
  rewrite (swap_pullthrough_l (Z 2 1 0) —).
  rewrite <- (compose_assoc (zx_comm 2 1)).
  unfold zx_comm, zx_of_perm_cast.
  simpl_casts.
  rewrite compose_zx_of_perm by auto with perm_db.
  assert (H : perm_eq (2 + 1) 
    (big_swap_perm 1 2 ∘ big_swap_perm 1 2)%prg
    (big_swap_perm 2 1))
    by (by_perm_cell; reflexivity).
  rewrite H.
  clear H.
  assert (H : zx_of_perm (2 + 1) (big_swap_perm 2 1) ∝ (⨉ ↕ —) ⟷ (— ↕ ⨉)). 
  1: {
    by_perm_eq_nosimpl.
    rewrite perm_of_zx_of_perm_eq by auto with perm_db. 
    by_perm_cell; reflexivity.
  }
  rewrite H.
  rewrite compose_assoc, <- (stack_wire_distribute_l ⨉ (Z 2 1 0)).
  rewrite <- !compose_assoc, <- (stack_wire_distribute_r (X 1 2 0) ⨉).
  rewrite Z_zxperm_absorbtion_left by constructor.
  now rewrite X_zxperm_absorbtion_right by constructor.
Qed.

Lemma notc_is_notc_r : _NOTC_ ∝= _NOTC_R.
Proof.
  rewrite notc_is_swapp_cnot.
  rewrite cnot_is_cnot_r.
  rewrite <- notc_r_is_swapp_cnot_r.
  easy.
Qed.