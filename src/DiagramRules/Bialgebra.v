Require Import CoreData.
Require Import CoreRules.

Definition Bi_Alg_Z_X := ((Z_Spider 1 2 0) ↕ (Z_Spider 1 2 0) ⟷ (— ↕ ⨉ ↕ —) ⟷ ((X_Spider 2 1 0) ↕ (X_Spider 2 1 0))).
Definition Bi_Alg_X_Z := ((X_Spider 1 2 0) ↕ (X_Spider 1 2 0) ⟷ (— ↕ ⨉ ↕ —) ⟷ ((Z_Spider 2 1 0) ↕ (Z_Spider 2 1 0))).

Theorem BiAlgebra_rule_Z_X : 
 (X_Spider 2 1 0) ⟷ (Z_Spider 1 2 0) ∝ Bi_Alg_Z_X.
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
  assert (forall n m, (ket n × ((bra n) ⊗ (bra n)) ⊗ (ket m × ((bra m) ⊗ (bra m))))
  × (I 2 ⊗ swap ⊗ I 2) = (ket n × ((bra n) ⊗ (bra m)) ⊗ (ket m × ((bra n) ⊗ (bra m))))).
  {
  intros.
  rewrite kron_assoc; try auto with wf_db.
  rewrite <- kron_mixed_product.
  rewrite Mmult_assoc.
  restore_dims.
  repeat rewrite kron_assoc; try auto with wf_db.
  assert (forall n m o, (bra n ⊗ (bra m ⊗ bra o)) × (swap ⊗ I 2) = bra m ⊗ (bra n ⊗ bra o)).
  {
    intros.
    restore_dims.
    rewrite <- 2 kron_assoc by auto with wf_db.
    rewrite (kron_mixed_product (bra _ ⊗ bra _) (bra _) (swap) _).
    apply kron_simplify; [ | rewrite Mmult_1_r by auto with wf_db; easy ].
    - apply transpose_matrices.
      rewrite Mmult_transpose.
      rewrite kron_transpose.
      rewrite swap_transpose.
      rewrite swap_spec; auto with wf_db.
  }
  restore_dims.
  repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite H.
  restore_dims.
  repeat rewrite <- kron_mixed_product.
  apply Mmult_simplify; [ easy | ].
  restore_dims.
  repeat rewrite <- kron_assoc by auto with wf_db.
  easy. 
  }
  repeat rewrite <- Mmult_assoc.
  repeat rewrite (Mmult_assoc _ _ (_ ⊗ _ ⊗ _)).
  restore_dims.
  unfold braminus, braplus.
  rewrite bra0_equiv, bra1_equiv, ket0_equiv, ket1_equiv.
  repeat rewrite H.
  clear H.
  repeat rewrite <- Mmult_plus_distr_r. 
  repeat rewrite <- Mmult_plus_distr_l.
Admitted.

Theorem BiAlgebra_rule_X_Z : 
 (Z_Spider 2 1 0) ⟷ (X_Spider 1 2 0) ∝ Bi_Alg_X_Z.
Proof.
  colorswap_of BiAlgebra_rule_Z_X.
Qed.


Theorem Hopf_rule_Z_X : 
  (Z_Spider 1 2 0) ⟷ (X_Spider 2 1 0) ∝ (Z_Spider 1 0 0) ⟷ (X_Spider 0 1 0).
Proof.
  intros.
  rewrite <- (@nwire_removal_r 2).
  simpl.
  rewrite ZX_Stack_Empty_r.
  simpl_casts.
  rewrite wire_loop at 1.
  rewrite Cap_Z.
  rewrite Cup_X.
  replace (0%R) with (0 + 0)%R by lra.
  rewrite <- (@Z_spider_1_1_fusion 0 2).
  assert (X_spider_1_1_fusion : forall {nIn nOut} a b, (X nIn 1 a ⟷ X 1 nOut b) ∝ X nIn nOut (a + b)).
  {
    intros.
    colorswap_of (@Z_spider_1_1_fusion nIn nOut).
  } (* TODO: Make X rules *)
  rewrite <- X_spider_1_1_fusion.
  replace (0 + 0)%R with 0 by lra.
  repeat rewrite stack_wire_distribute_r.
  repeat rewrite ZX_Compose_assoc.
  rewrite wire_to_nWire.
  rewrite (ZX_Stack_assoc (Z 0 1 0) (nWire 1) (nWire 1)).
  rewrite (ZX_Stack_assoc (Z 1 2 0) (nWire 1) (nWire 1)).
  rewrite (ZX_Stack_assoc (X 1 0 0) (nWire 1) (nWire 1)).
  rewrite (ZX_Stack_assoc (X 2 1 0) (nWire 1) (nWire 1)).
  simpl_casts.
  rewrite nWire_stack.
Opaque nStack1.
  simpl.
  repeat rewrite <- ZX_Compose_assoc.
  rewrite <- (push_out_top (Z 0 1 0)).
  assert (Hl : (Z 0 1 0 ↕ Z 1 2 0) ⟷ ((Z) 1 2 0 ↕ nWire 2) ∝ Z 0 1 0 ↕ nWire 1 ⟷ (Z 1 2 0 ↕ Z 1 2 0)).
  {
    rewrite <- ZX_Stack_Compose_distr.
    rewrite nwire_removal_r.
    rewrite <- (nwire_removal_l (Z 1 2 0)) at 2.
    rewrite ZX_Stack_Compose_distr.
    easy.
  }
  rewrite Hl.
  repeat rewrite ZX_Compose_assoc.
  rewrite <- (pull_out_top (X 1 0 0)).
  assert (Hr : X 2 1 0 ↕ nWire 2 ⟷ (X 1 0 0 ↕ X 2 1 0) ∝ X 2 1 0 ↕ (X) 2 1 0 ⟷ ((X) 1 0 0 ↕ nWire 1)).
  {
    rewrite <- ZX_Stack_Compose_distr.
    rewrite nwire_removal_l.
    rewrite <- (nwire_removal_r (X 2 1 0)) at 2.
    rewrite ZX_Stack_Compose_distr.
    easy.
  }
  rewrite Hr.
  repeat rewrite <- ZX_Compose_assoc.
  assert (HBiAlgAssoc : (Z) 0 1 0 ↕ nWire 1 ⟷ ((Z) 1 2 0 ↕ (Z) 1 2 0) ⟷ (nWire 1 ↕ ⨉ ↕ nWire 1) ⟷ ((X) 2 1 0 ↕ (X) 2 1 0) ⟷ ((X) 1 0 0 ↕ nWire 1) ∝ 
    (Z) 0 1 0 ↕ nWire 1 ⟷ (((Z) 1 2 0 ↕ (Z) 1 2 0) ⟷ (nWire 1 ↕ ⨉ ↕ nWire 1) ⟷ ((X) 2 1 0 ↕ (X) 2 1 0)) ⟷ ((X) 1 0 0 ↕ nWire 1)).
  {
    repeat rewrite ZX_Compose_assoc.
    easy.
  }
  rewrite HBiAlgAssoc.
  clear Hl Hr HBiAlgAssoc.
  rewrite <- wire_to_nWire.
Transparent nStack1.
  fold Bi_Alg_Z_X.
  rewrite <- BiAlgebra_rule_Z_X.
  assert (X_Wrap_Under_L_base : forall α, X 2 1 α ∝ (X 1 2 α ↕ —) ⟷ (— ↕ ⊃)) by admit. (* TODO : resurect and make X rules *)
  rewrite X_Wrap_Under_L_base.
  repeat rewrite <- ZX_Compose_assoc.
  rewrite <- stack_wire_distribute_r.
  rewrite Z_0_copy.
  simpl_casts.
  simpl.
  cleanup_zx; simpl_casts.
  rewrite (ZX_Stack_assoc (Z 0 1 0) ((Z) (0 + 0) (1 + 0) 0) —).
  simpl_casts.
  rewrite <- (ZX_Stack_Compose_distr ((Z) 0 1 0) — ((Z) (0 + 0) (1 + 0) 0 ↕ —) ⊃).
  assert (Hl: (Z) (0 + 0) (1 + 0) 0 ↕ — ⟷ ⊃ ∝ Z 1 0 0). (* Todo : pull out lemma *)
  {
    rewrite Cup_Z.
    rewrite <- Z_0_is_wire.
    rewrite <- Z_add_l.
    rewrite 2 Rplus_0_r.
    easy.
  }
  rewrite Hl.
  cleanup_zx.
  rewrite (ZX_Stack_Empty_r_rev (Z 1 2 0)).
  simpl_casts.
  rewrite <- (ZX_Stack_Compose_distr (Z 0 1 0) (Z 1 2 0) (Z 1 0 0) ⦰).
  cleanup_zx.
  rewrite Z_spider_1_1_fusion.
  rewrite Rplus_0_r.
  rewrite <- Cap_Z.
  rewrite (disconnected_stack_compose_r).
  simpl_casts.
  assert (X_add_r: forall {n} m o {α β γ}, X n (m + o) (α + β + γ) ∝ X n 2 β ⟷ (X 1 m α ↕ X 1 o γ)). { (* TODO : X rules *)
    intros.
    colorswap_of (@Z_add_r n).
  }
  assert (Hr : ⊂ ⟷ ((X) 1 0 0 ↕ —) ∝ X 0 1 0).
  {
    rewrite Cap_X.
    rewrite <- X_0_is_wire.
    rewrite <- X_add_r.
    rewrite 2 Rplus_0_r.
    easy.
  }
  rewrite ZX_Compose_assoc.
  rewrite Hr.
  easy.
Admitted.


Theorem Hopf_rule_X_Z : 
  (X_Spider 1 2 0) ⟷ (Z_Spider 2 1 0) ∝ (X_Spider 1 0 0) ⟷ (Z_Spider 0 1 0).
Proof.
  colorswap_of Hopf_rule_Z_X.
Qed.




Definition l  : Matrix (2 ^ 4) (2 ^ 2) := (fun x y =>
match x, y with
| 0%nat, 0%nat => 1
| _, _ => 0
end).

