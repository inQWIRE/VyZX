Require Import SemanticsComp CoreData GadgetRules ComposeRules CoreAutomation.

(** Various computational results about explicit ZX-diagrams, using scalars *)


Lemma Z_0_2_semantics α : 
  Z_semantics 0 2 α = make_WF (list2D_to_matrix [[C1];[C0];[C0];[Cexp α]]).
Proof.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  by_cell; reflexivity.
Qed.

Lemma X_2_1_0_semantics : X_semantics 2 1 0 = 
  make_WF (list2D_to_matrix [[/√2;C0;C0;/√2];[C0;/√2;/√2;C0]]).
Proof.
  rewrite X_semantics_equiv.
  cbn.
  rewrite 4 kron_1_l, Cexp_0, Mscale_1_l by auto_wf.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  unfold xbasis_plus, xbasis_minus, braplus, braminus;
    autounfold with U_db; cbn; by_cell_no_intros; cbn;
    Csimpl; group_radicals; C_field; lca.
Qed.

Lemma Z_4_1_0_semantics : Z_semantics 4 1 0 = make_WF
  (list2D_to_matrix
     [[C1;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0];
      [C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;
       C1]]).
Proof.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  by_cell; [reflexivity..|].
  rewrite Cexp_0.
  reflexivity.
Qed.


Lemma hopf_Z_X_rule_base : Z 1 2 0 ⟷ X 2 1 0 ∝= /2 .* (Z 1 0 0 ⟷ X 0 1 0).
Proof.
  prep_matrix_equivalence.
  rewrite zx_scale_semantics.
  cbn.
  rewrite X_2_1_0_semantics.
  compute_matrix (Z_semantics 1 2 0).
  rewrite Cexp_0.
  compute_matrix (X_semantics 0 1 0).
  rewrite kron_1_l, Cexp_0, 2 Cmult_1_r by auto_wf.
  unfold hadamard.
  rewrite Cplus_opp_r.
  replace (C1 / √ 2 + C1 / √2) with (RtoC (√2)) by (C_field; lca).
  compute_matrix (Z_semantics 1 0 0).
  rewrite Cexp_0.
  rewrite 4 make_WF_equiv.
  by_cell; unfold list2D_to_matrix, scale; cbn; Csimpl; C_field.
Qed.



Lemma hopf_Z_X_rule_base_phase α β : Z 1 2 α ⟷ X 2 1 β ∝= 
  /2 .* (Z 1 0 α ⟷ X 0 1 β).
Proof.
  rewrite <- (Rplus_0_r α) at 1.
  rewrite <- Z_spider_1_1_fusion.
  rewrite <- (Rplus_0_l β) at 1.
  rewrite <- X_spider_1_1_fusion.
  rewrite compose_assoc, <- (compose_assoc (Z 1 2 0)).
  rewrite hopf_Z_X_rule_base.
  distribute_zxscale.
  rewrite compose_assoc.
  rewrite X_spider_1_1_fusion, <- compose_assoc, Z_spider_1_1_fusion.
  rewrite Rplus_0_r, Rplus_0_l.
  reflexivity.
Qed.


Lemma hopf_X_Z_rule_base : X 1 2 0 ⟷ Z 2 1 0 ∝= /2 .* (X 1 0 0 ⟷ Z 0 1 0).
Proof.
  colorswap_of (hopf_Z_X_rule_base).
Qed.


Lemma hopf_X_Z_rule_base_phase α β : X 1 2 α ⟷ Z 2 1 β ∝= 
  /2 .* (X 1 0 α ⟷ Z 0 1 β).
Proof.
  colorswap_of (hopf_Z_X_rule_base_phase α β).
Qed.


Lemma Z_0_1_copy β : Z 0 1 0 ⟷ X 1 1 β ∝= Z 0 1 0.
Proof.
  prep_matrix_equivalence.
  by_cell; cbn; unfold kron, hadamard; cbn; 
    rewrite Cexp_0; C_field; lca.
Qed.

Lemma X_0_1_copy β : X 0 1 0 ⟷ Z 1 1 β ∝= X 0 1 0.
Proof.
  colorswap_of (Z_0_1_copy β).
Qed.

(* @nocheck name *)
Lemma X_0_2_PI_mult_l_to_sum (u v : Matrix 1 2) : WF_Matrix u -> WF_Matrix v -> 
  u ⊗ v × ⟦ X 0 2 PI ⟧ = 
  (u × e_i 1 × (v × e_i 0) .+ v × e_i 1 × (u × e_i 0))%M.
Proof.
  intros Hu Hv.
  prep_matrix_equivalence.
  rewrite <- 4 matrix_by_basis by lia.
  by_cell.
  cbn;
  unfold kron, hadamard, Mplus; cbn; Csimpl; 
  rewrite Cexp_PI';
  C_field; lca.
Qed.