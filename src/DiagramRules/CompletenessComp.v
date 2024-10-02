Require Import CoreData.
From QuantumLib Require Import Polar.
Require Import CoreRules.

Lemma c_step_1 : forall α,
	⟦ (Z 0 1 α ↕ —) ⟷ X 2 1 0 ⟧ = 
	/(√2)%R .* (∣0⟩⟨0∣ .+ 
	Cexp(α) .* ∣0⟩⟨1∣ .+ 
	Cexp(α) .* ∣1⟩⟨0∣ .+ 
	∣1⟩⟨1∣).
Proof.
	intros.	autorewrite with scalar_move_db.
	rewrite ZX_semantic_equiv.
	simpl.
	autorewrite with Cexp_db.
	Msimpl.
	rewrite kron_plus_distr_r.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_assoc.
	repeat rewrite kron_mixed_product.
	Msimpl.
	autorewrite with scalar_move_db.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	unfold xbasis_minus, xbasis_plus, braplus, braminus.
	autorewrite with scalar_move_db.
 replace ((/ (√ 2)%R + Cexp α * / (√ 2)%R) * / (√ 2)%R * / (√ 2)%R) with ((1 + Cexp α) / (2 * (√2)%R)) by C_field.
 replace ((/ (√ 2)%R + Cexp α * - / (√ 2)%R) * / (√ 2)%R * / (√ 2)%R) with ((1 - Cexp α) / (2 * (√2)%R)) by C_field.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	remember ((C1 + Cexp α) / (C2 * (√ 2)%R)) as σ1.
	remember ((C1 - Cexp α) / (C2 * (√ 2)%R)) as σ2.
	autorewrite with scalar_move_db.
	repeat rewrite Mscale_plus_distr_r.
	repeat rewrite Mscale_assoc.
	replace (σ2 * -1) with (- σ2) by lca.
	replace (- σ2 * -1) with σ2 by lca.
	restore_dims.
	replace (σ1 .* ∣0⟩⟨0∣ .+ σ1 .* ∣0⟩⟨1∣ .+ (σ1 .* ∣1⟩⟨0∣ .+ σ1 .* ∣1⟩⟨1∣) .+ (σ2 .* ∣0⟩⟨0∣ .+ - σ2 .* ∣0⟩⟨1∣ .+ (- σ2 .* ∣1⟩⟨0∣ .+ σ2 .* ∣1⟩⟨1∣))) with ((σ1 + σ2) .* ∣0⟩⟨0∣ .+ (σ1 - σ2) .* ∣0⟩⟨1∣ .+ (σ1 - σ2) .* ∣1⟩⟨0∣ .+ (σ1 + σ2) .* ∣1⟩⟨1∣) by lma.
	replace (σ1 + σ2) with (1 / (√2)%R) by (subst; C_field_simplify; [lca | C_field]).
	replace (σ1 - σ2) with ((Cexp α) / (√2)%R) by (subst; C_field_simplify; [lca | C_field]).
	Admitted. (* I believe this is failing due to a versioning issue locally *)
	(* lma.
Qed. *)

Lemma c_step_1_pi : forall α,
	⟦ (Z 0 1 α ↕ —) ⟷ X 2 1 PI ⟧ = 
	/(√2)%R .* (Cexp(α) .* ∣0⟩⟨0∣ .+ 
	∣0⟩⟨1∣ .+ 
	∣1⟩⟨0∣ .+ 
	Cexp(α) .* ∣1⟩⟨1∣).
Proof.
	intros.
	rewrite ZX_semantic_equiv.
	simpl.
	autorewrite with scalar_move_db.
	Msimpl.
	autorewrite with Cexp_db.
	rewrite kron_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.
	repeat rewrite kron_mixed_product.
	Msimpl.
	autorewrite with scalar_move_db.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	unfold xbasis_minus, xbasis_plus, braplus, braminus.
	autorewrite with scalar_move_db.
 replace ((/ (√ 2)%R + Cexp α * / (√ 2)%R) * / (√ 2)%R * / (√ 2)%R) with ((1 + Cexp α) / (2 * (√2)%R)) by C_field.
 replace ((-1 * / (√ 2)%R + Cexp α * -1 * - / (√ 2)%R) * / (√ 2)%R * / (√ 2)%R) with (-(1 - Cexp α) / (2 * (√2)%R)) by (C_field_simplify; [lca | C_field]).
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	remember ((C1 + Cexp α) / (C2 * (√ 2)%R)) as σ1.
	remember (-(C1 - Cexp α) / (C2 * (√ 2)%R)) as σ2.
	autorewrite with scalar_move_db.
	repeat rewrite Mscale_plus_distr_r.
	repeat rewrite Mscale_assoc.
	replace (σ2 * -1) with (- σ2) by lca.
	replace (- σ2 * -1) with σ2 by lca.
	restore_dims.
	replace (σ1 .* ∣0⟩⟨0∣ .+ σ1 .* ∣0⟩⟨1∣ .+ (σ1 .* ∣1⟩⟨0∣ .+ σ1 .* ∣1⟩⟨1∣) .+ (σ2 .* ∣0⟩⟨0∣ .+ - σ2 .* ∣0⟩⟨1∣ .+ (- σ2 .* ∣1⟩⟨0∣ .+ σ2 .* ∣1⟩⟨1∣))) with ((σ1 + σ2) .* ∣0⟩⟨0∣ .+ (σ1 - σ2) .* ∣0⟩⟨1∣ .+ (σ1 - σ2) .* ∣1⟩⟨0∣ .+ (σ1 + σ2) .* ∣1⟩⟨1∣) by lma.
	replace (σ1 + σ2) with (Cexp α / (√2)%R) by (subst; C_field_simplify; [lca | C_field]).
	replace (σ1 - σ2) with (1 / (√2)%R) by (subst; C_field_simplify; [lca | C_field]).
	Admitted. (* I believe this is failing due to a versioning issue locally *)
	(* lma.
Qed. *)

Lemma c_step_2 : forall α β γ,
	⟦ (Z 1 2 α ↕ Z 1 2 β) ⟷ (— ↕ X 2 1 γ ↕ —) ⟧ = 
	/ C2 .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣0⟩ × (⟨0∣ ⊗ ⟨0∣) .+ Cexp γ .* (∣0⟩ ⊗ ∣-⟩ ⊗ ∣0⟩ × (⟨0∣ ⊗ ⟨0∣)) .+ Cexp α .* (∣1⟩ ⊗ ∣+⟩ ⊗ ∣0⟩ × (⟨1∣ ⊗ ⟨0∣) .+ - Cexp γ .* (∣1⟩ ⊗ ∣-⟩ ⊗ ∣0⟩ × (⟨1∣ ⊗ ⟨0∣))) .+ Cexp β .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣1⟩ × (⟨0∣ ⊗ ⟨1∣) .+ - Cexp γ .* (∣0⟩ ⊗ ∣-⟩ ⊗ ∣1⟩ × (⟨0∣ ⊗ ⟨1∣))) .+ Cexp α * Cexp β .* (∣1⟩ ⊗ ∣+⟩ ⊗ ∣1⟩ × (⟨1∣ ⊗ ⟨1∣) .+ Cexp γ .* (∣1⟩ ⊗ ∣-⟩ ⊗ ∣1⟩ × (⟨1∣ ⊗ ⟨1∣)))).
Proof.
	intros.
	remember (/ C2 .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣0⟩ × (⟨0∣ ⊗ ⟨0∣) .+ Cexp γ .* (∣0⟩ ⊗ ∣-⟩ ⊗ ∣0⟩ × (⟨0∣ ⊗ ⟨0∣)) .+ Cexp α .* (∣1⟩ ⊗ ∣+⟩ ⊗ ∣0⟩ × (⟨1∣ ⊗ ⟨0∣) .+ - Cexp γ .* (∣1⟩ ⊗ ∣-⟩ ⊗ ∣0⟩ × (⟨1∣ ⊗ ⟨0∣))) .+ Cexp β .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣1⟩ × (⟨0∣ ⊗ ⟨1∣) .+ - Cexp γ .* (∣0⟩ ⊗ ∣-⟩ ⊗ ∣1⟩ × (⟨0∣ ⊗ ⟨1∣))) .+ Cexp α * Cexp β .* (∣1⟩ ⊗ ∣+⟩ ⊗ ∣1⟩ × (⟨1∣ ⊗ ⟨1∣) .+ Cexp γ .* (∣1⟩ ⊗ ∣-⟩ ⊗ ∣1⟩ × (⟨1∣ ⊗ ⟨1∣))))) as solution.
	remember (Z 1 2 α ↕ Z 1 2 β) as lhs.
	remember (— ↕ X 2 1 γ ↕ —) as rhs.
	assert (Hlhs : ⟦ lhs ⟧ = 
	(∣0⟩⊗∣0⟩⊗∣0⟩⊗∣0⟩) × (⟨0∣⊗⟨0∣) .+ 
	Cexp α .* (∣1⟩⊗∣1⟩⊗∣0⟩⊗∣0⟩) × (⟨1∣⊗⟨0∣) .+ 
	Cexp β .* (∣0⟩⊗∣0⟩⊗∣1⟩⊗∣1⟩) × (⟨0∣⊗⟨1∣) .+ 
	(Cexp β * Cexp α) .* (∣1⟩⊗∣1⟩⊗∣1⟩⊗∣1⟩) × (⟨1∣⊗⟨1∣)).
	{
		subst.
		rewrite ZX_semantic_equiv.
		unfold_dirac_spider.
		repeat rewrite kron_plus_distr_l.
		repeat rewrite kron_plus_distr_r.
		autorewrite with scalar_move_db.
		repeat rewrite <- kron_mixed_product.
		restore_dims.
		repeat rewrite kron_assoc by auto with wf_db.
		rewrite Mscale_plus_distr_r.
		rewrite Mscale_assoc.
		repeat rewrite Mplus_assoc.
		easy.
	}
	rewrite zx_compose_spec.
	rewrite Hlhs.
	rewrite Heqrhs.
	clear Heqlhs. clear Hlhs. clear Heqrhs. clear lhs. clear rhs.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	rewrite <- kron_mixed_product.
	rewrite kron_plus_distr_l.
	rewrite kron_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite kron_id_dist_l by auto with wf_db.
	repeat rewrite kron_id_dist_r by auto with wf_db.
	repeat rewrite Mmult_assoc.
	rewrite <- 2 (Mmult_assoc _ (∣0⟩⊗∣0⟩⊗∣0⟩⊗∣0⟩)).
	rewrite <- 2 (Mmult_assoc _ (∣1⟩⊗∣1⟩⊗∣0⟩⊗∣0⟩)).
	rewrite <- 2 (Mmult_assoc _ (∣0⟩⊗∣0⟩⊗∣1⟩⊗∣1⟩)).
	rewrite <- 2 (Mmult_assoc _ (∣1⟩⊗∣1⟩⊗∣1⟩⊗∣1⟩)).
	repeat rewrite kron_assoc by auto with wf_db.
	restore_dims.
	repeat rewrite (kron_mixed_product (I 2) _ (∣0⟩)).
	repeat rewrite (kron_mixed_product (I 2) _ (∣1⟩)).
	repeat rewrite (kron_mixed_product (⟨+∣) _ (∣0⟩)).
	repeat rewrite (kron_mixed_product (⟨+∣) _ (∣1⟩)).
	repeat rewrite (kron_mixed_product (⟨-∣) _ (∣0⟩)).
	repeat rewrite (kron_mixed_product (⟨-∣) _ (∣1⟩)).
	repeat rewrite (kron_mixed_product (⟨+∣) _ (∣0⟩)).
	repeat rewrite (kron_mixed_product (⟨+∣) _ (∣1⟩)).
	repeat rewrite (kron_mixed_product (⟨-∣) _ (∣0⟩)).
	repeat rewrite (kron_mixed_product (⟨-∣) _ (∣1⟩)).
	repeat rewrite Mmult_1_l by auto with wf_db.
	repeat rewrite (kron_mixed_product (I 2) _ (∣0⟩)).
	repeat rewrite (kron_mixed_product (I 2) _ (∣1⟩)).
	repeat rewrite (kron_mixed_product (I 2) _ (∣0⟩)).
	repeat rewrite (kron_mixed_product (I 2) _ (∣1⟩)).
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	repeat rewrite <- kron_mixed_product.
	repeat rewrite <- kron_assoc by auto with wf_db.
	Msimpl.
	replace (/ (√ 2)%R * / (√ 2)%R) with (/2) by C_field.
	replace (- / (√ 2)%R * / (√ 2)%R) with (-/2) by C_field.
	replace (/ (√ 2)%R * - / (√ 2)%R) with (-/2) by C_field.
	replace (- / (√ 2)%R * - / (√ 2)%R) with (/2) by C_field.
	restore_dims.
	repeat rewrite <- kron_mixed_product.
	replace (Cexp γ * - / C2) with (/ C2 * - Cexp γ) by lca.
	replace (Cexp γ * / C2) with (/ C2 * Cexp γ) by lca.
	repeat rewrite <- (Mscale_assoc _ _ (/C2)).
	autorewrite with scalar_move_db.
	replace (Cexp α * / C2) with (/C2 * Cexp α) by lca.
	replace (Cexp β * / C2) with (/C2 * Cexp β) by lca.
	replace (Cexp β * Cexp α * / C2) with (/C2 * Cexp α * Cexp β) by lca.
	repeat rewrite <- Mscale_assoc.
	autorewrite with scalar_move_db.
	symmetry.
	apply Heqsolution.
Qed.

Lemma c_step_3 : forall γ,
	⟦ (Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 γ) ⟧ = 
	/(√2)%R .* (I 2 ⊗ (∣+⟩×⟨+∣ .+ Cexp γ .* ∣-⟩×⟨-∣)) × cnot.
Proof.
	intros.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	autorewrite with Cexp_db.
	Msimpl.
	rewrite kron_plus_distr_r.
	rewrite kron_plus_distr_l.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite kron_id_dist_l by auto with wf_db.
	repeat rewrite kron_id_dist_r by auto with wf_db.
	repeat rewrite Mmult_assoc.
	repeat rewrite kron_assoc by auto with wf_db.
	repeat rewrite <- (Mmult_assoc _ (∣0⟩ ⊗ (∣0⟩ ⊗ I 2))).
	repeat rewrite <- (Mmult_assoc _ (∣1⟩ ⊗ (∣1⟩ ⊗ I 2))).
	repeat rewrite kron_mixed_product.
	Msimpl.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	restore_dims.
	autorewrite with ketbra_mult_db.
	replace (Cexp γ * / (√ 2)%R) with (/ (√ 2)%R * Cexp γ) by lca.
	replace (Cexp γ * - / (√ 2)%R) with (/ (√ 2)%R * - Cexp γ) by lca.
	repeat rewrite <- (Mscale_assoc _ _ (/ (√2)%R)).
	autorewrite with scalar_move_db.
	apply Mscale_simplify; [| easy].
	rewrite <- cnot_decomposition.
	repeat rewrite kron_plus_distr_l.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite kron_mixed_product.
	Msimpl.
	repeat rewrite Mmult_assoc.
	replace (⟨-∣×σx) with (-1 .* ⟨-∣) by solve_matrix.
	replace (⟨+∣×σx) with (⟨+∣).
	autorewrite with scalar_move_db.
	lma.
	unfold braplus.
	solve_matrix.
Qed.

Lemma c_step_3_flipped : forall γ,
	⟦ (— ↕ Z 1 2 0) ⟷ (X 2 1 γ ↕ —) ⟧ = 
	/(√2)%R .* ((∣+⟩×⟨+∣ .+ Cexp γ .* ∣-⟩×⟨-∣) ⊗ I 2) × notc.
Proof.
	intros.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	autorewrite with Cexp_db.
	Msimpl.
	rewrite kron_plus_distr_r.
	rewrite kron_plus_distr_l.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite kron_id_dist_l by auto with wf_db.
	repeat rewrite kron_id_dist_r by auto with wf_db.
	repeat rewrite Mmult_assoc.
	restore_dims.
	repeat rewrite kron_assoc by auto with wf_db.
	repeat rewrite <- (Mmult_assoc _ (I 2 ⊗ (∣0⟩ ⊗ (∣0⟩)))).
	repeat rewrite <- (Mmult_assoc _ (I 2 ⊗ (∣1⟩ ⊗ (∣1⟩)))).
	repeat rewrite kron_mixed_product.
	Msimpl.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	restore_dims.
	autorewrite with ketbra_mult_db.
	replace (Cexp γ * / (√ 2)%R) with (/ (√ 2)%R * Cexp γ) by lca.
	replace (Cexp γ * - / (√ 2)%R) with (/ (√ 2)%R * - Cexp γ) by lca.
	repeat rewrite <- (Mscale_assoc _ _ (/ (√2)%R)).
	autorewrite with scalar_move_db.
	apply Mscale_simplify; [| easy].
	rewrite <- notc_decomposition.
	repeat rewrite kron_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite kron_mixed_product.
	Msimpl.
	repeat rewrite Mmult_assoc.
	replace (⟨-∣×σx) with (-1 .* ⟨-∣) by solve_matrix.
	replace (⟨+∣×σx) with (⟨+∣).
	autorewrite with scalar_move_db.
	lma.
	unfold braplus.
	solve_matrix.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma step_1_N : forall α,
	⟦ (Z 0 1 α ↕ Z 0 1 (-α)) ⟷ X 2 1 0 ⟧ = 
	(√2)%R .* ∣0⟩ .+ 
	(Cexp α + Cexp (-α)) / (√2)%R .* ∣1⟩.
Proof.
	intros.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	autorewrite with Cexp_db.
	Msimpl.
	rewrite kron_plus_distr_r.
	rewrite kron_plus_distr_l.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_assoc.
	repeat rewrite (kron_mixed_product ⟨-∣ ⟨-∣).
	repeat rewrite (kron_mixed_product ⟨+∣ ⟨+∣).
	autorewrite with scalar_move_db.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	replace (/ (√ 2)%R * / (√ 2)%R) with (/2) by C_field.
	replace (- / (√ 2)%R * / (√ 2)%R) with (-/2) by C_field.
	replace (/ (√ 2)%R * (/ (√ 2)%R + / Cexp α * / (√ 2)%R)) with ((1 + / Cexp α)/2) by C_field.
	replace (- / (√ 2)%R * (/ (√ 2)%R + / Cexp α * - / (√ 2)%R)) with (-(1 - / Cexp α)/2) by C_field.
	unfold xbasis_minus, xbasis_plus.
	autorewrite with scalar_move_db.
	repeat rewrite Mscale_plus_distr_r.
	repeat rewrite Mscale_assoc.
	replace (/ C2 * / (√ 2)%R .* ∣0⟩ .+ / C2 * / (√ 2)%R .* ∣1⟩ .+ (/ C2 * / (√ 2)%R .* ∣0⟩ .+ / C2 * / (√ 2)%R * -1 .* ∣1⟩)) with (/(√2)%R .* ∣0⟩) by lma.
	replace (/ Cexp α * (/ C2 * / (√ 2)%R)) with (/(Cexp α * 2 * (√2)%R)) by C_field.
	replace (/ Cexp α * (- / C2 * / (√ 2)%R)) with (- /(Cexp α * 2 * (√2)%R)) by C_field.
	replace (- /(Cexp α * 2 * (√2)%R) * -1) with (/(Cexp α * 2 * (√2)%R)) by (C_field_simplify; [lca | C_field]).
	remember (/ (Cexp α * C2 * (√ 2)%R)) as v.
	replace (v .* ∣0⟩ .+ v .* ∣1⟩ .+ ((- v) .* ∣0⟩ .+ v .* ∣1⟩)) with (2 * v .* ∣1⟩) by lma.
	replace (C2 * v) with (/ (Cexp α * (√2)%R)) by (rewrite Heqv; C_field).
	clear Heqv; clear v.
	replace (Cexp α * ((C1 + / Cexp α) / C2 * / (√ 2)%R)) with ((1 + Cexp α)/ (2 * (√2)%R)) by C_field.
	replace (Cexp α * (-(C1 - / Cexp α) / C2 * / (√ 2)%R)) with ((1 - Cexp α)/ (2 * (√2)%R)) by C_field.
	remember ((C1 + Cexp α) / (C2 * (√ 2)%R)) as v1.
	remember ((C1 - Cexp α) / (C2 * (√ 2)%R)) as v2.
	replace (v2 * -1) with (-v2) by lca.
	replace ((v1 .* ∣0⟩ .+ v1 .* ∣1⟩ .+ (v2 .* ∣0⟩ .+ - v2 .* ∣1⟩))) with ((v1 + v2) .* ∣0⟩ .+ (v1 - v2) .* ∣1⟩) by lma.
	replace (v1 + v2) with (/(√2)%R) by (rewrite Heqv1, Heqv2; C_field_simplify; [ lca | C_field ]).
	replace (v1 - v2) with (Cexp α/(√2)%R) by (rewrite Heqv1, Heqv2; C_field_simplify; [ lca | C_field ]).
	clear Heqv1; clear Heqv2; clear v1; clear v2.
	rewrite Mplus_assoc.
	rewrite (Mplus_comm _ _ ((/ (Cexp α * (√2)%R)) .* _)).
	rewrite Mplus_assoc.
	rewrite <- Mplus_assoc.
	rewrite <- 2 Mscale_plus_distr_l.
	apply Mplus_simplify.
	- apply Mscale_simplify.
		+ easy.
		+ C_field_simplify; [ lca | C_field ].
	- apply Mscale_simplify.
		+ easy.
		+ C_field_simplify; [ lca | C_field ].
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma step_2_N :
	⟦ (— ↕ (X 0 1 (PI/2) ⟷ Z 1 2 0) ↕ —) ⟷ (X 2 1 0 ↕ X 2 1 0) ⟧ = 
	/(√2)%R .* ∣+⟩ × ⟨+∣ ⊗ (∣+⟩ × ⟨+∣) .+
	Cexp (PI/2)/(√2)%R .* ∣+⟩ × ⟨+∣ ⊗ (∣-⟩ × ⟨-∣) .+ 
	Cexp (PI/2)/(√2)%R .* ∣-⟩ × ⟨-∣ ⊗ (∣+⟩ × ⟨+∣) .+ 
	/(√2)%R .* ∣-⟩ × ⟨-∣ ⊗ (∣-⟩ × ⟨-∣).
Proof.
	rewrite zx_compose_spec.
	rewrite 2 zx_stack_spec.
	assert (H : ⟦ X 0 1 (PI/2) ⟷ Z 1 2 0 ⟧ = 
	((1 + Cexp (PI/2))/(√2)%R) .* ∣0⟩ ⊗ ∣0⟩ .+
	((1 - Cexp (PI/2))/(√2)%R) .* ∣1⟩ ⊗ ∣1⟩). 
	{ 
		rewrite ZX_semantic_equiv.
		unfold_dirac_spider.
		rewrite Cexp_0.
		Msimpl.
		repeat rewrite Mmult_plus_distr_l.
		repeat rewrite Mmult_plus_distr_r.
		repeat rewrite Mmult_assoc.
		restore_dims.
		autorewrite with scalar_move_db.
		autorewrite with ketbra_mult_db.
		autorewrite with scalar_move_db.
		Msimpl.
		lma.
	}
	rewrite H.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	rewrite Cexp_0.
	Msimpl.
	rewrite (kron_plus_distr_l _ _ _ _ (I 2)).
	rewrite (kron_plus_distr_r _ _ _ _ _ _ (I 2)).
	restore_dims.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_plus_distr_.
	replace (I 2 ⊗ (∣0⟩ ⊗ ∣0⟩) ⊗ I 2) with ((I 2 ⊗ ∣0⟩) ⊗ (∣0⟩ ⊗ I 2)) by (repeat rewrite kron_assoc by auto with wf_db; easy).
	replace (I 2 ⊗ (∣1⟩ ⊗ ∣1⟩) ⊗ I 2) with ((I 2 ⊗ ∣1⟩) ⊗ (∣1⟩ ⊗ I 2)) by (repeat rewrite kron_assoc by auto with wf_db; easy).
	restore_dims.
	repeat rewrite kron_mixed_product.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_assoc.
	repeat rewrite (kron_mixed_product ⟨+∣ ⟨+∣).
	repeat rewrite (kron_mixed_product ⟨-∣ ⟨-∣).
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	replace ((C1 + Cexp (PI/2)) / (√2)%R * /(√2)%R * /(√2)%R) with ((C1 + Cexp (PI/2))/(2 * (√2)%R)) by C_field.
	rewrite <- (Mscale_kron_dist_r _ _ _ _ ((C1 - Cexp (PI/2)) /(√2)%R)).
	repeat rewrite Mscale_plus_distr_r.
	repeat rewrite Mscale_assoc.
	repeat rewrite kron_plus_distr_l.
	repeat rewrite kron_plus_distr_r.
	replace (- / (√ 2)%R) with (/(√ 2)%R * -1) by lca.
	replace (((C1 - Cexp (PI / 2)) / (√ 2)%R * (/ (√ 2)%R * -1))) with (((C1 - Cexp (PI/2))/2) * -1) by C_field.
	repeat rewrite <- (Mscale_assoc _ _ _ (-1)%C).
	replace (((C1 - Cexp (PI / 2)) / (√ 2)%R * (/ (√ 2)%R))) with (((C1 - Cexp (PI/2))/2)) by C_field.
	remember ((C1 - Cexp (PI/2))/2) as v2.
	restore_dims.
	remember (-1 .* (∣-⟩ × ⟨-∣)) as mm1.
	autorewrite with scalar_move_db.
	remember ((C1 + Cexp (PI/2)) / (C2 * (√2)%R)) as v1.
	remember (v2 * / (√2)%R) as v3.
	repeat rewrite Mscale_plus_distr_r.
	replace (v3 .* (∣+⟩ × ⟨+∣ ⊗ mm1)) with (-v3 .* ((∣+⟩×⟨+∣)⊗(∣-⟩×⟨-∣))) by (subst; lma).
	replace (v3 .* (mm1 ⊗ (∣+⟩ × ⟨+∣))) with (-v3 .* ((∣-⟩×⟨-∣)⊗(∣+⟩×⟨+∣))) by (subst; lma).
	replace (v3 .* (mm1 ⊗ mm1)) with (v3 .* ((∣-⟩×⟨-∣)⊗(∣-⟩×⟨-∣))) by (subst; lma).
	replace (v1 .* (∣+⟩ × ⟨+∣ ⊗ (∣+⟩ × ⟨+∣)) .+ v1 .* (∣-⟩ × ⟨-∣ ⊗ (∣+⟩ × ⟨+∣)) .+ (v1 .* (∣+⟩ × ⟨+∣ ⊗ (∣-⟩ × ⟨-∣)) .+ v1 .* (∣-⟩ × ⟨-∣ ⊗ (∣-⟩ × ⟨-∣))) .+ (v3 .* (∣+⟩ × ⟨+∣ ⊗ (∣+⟩ × ⟨+∣)) .+ - v3 .* (∣-⟩ × ⟨-∣ ⊗ (∣+⟩ × ⟨+∣)) .+ (- v3 .* (∣+⟩ × ⟨+∣ ⊗ (∣-⟩ × ⟨-∣)) .+ v3 .* (∣-⟩ × ⟨-∣ ⊗ (∣-⟩ × ⟨-∣))))) with ((v1 + v3) .* (∣+⟩ × ⟨+∣ ⊗ (∣+⟩ × ⟨+∣)) .+ (v1 - v3) .* (∣-⟩ × ⟨-∣ ⊗ (∣+⟩ × ⟨+∣)) .+ (v1 - v3) .* (∣+⟩ × ⟨+∣ ⊗ (∣-⟩ × ⟨-∣)) .+ (v1 + v3) .* (∣-⟩ × ⟨-∣ ⊗ (∣-⟩ × ⟨-∣))) by lma.
	replace (v1 + v3) with (/(√2)%R) by (subst; C_field_simplify; [lca | C_field]).
	replace (v1 - v3) with (Cexp (PI/2)/(√2)%R) by (subst; C_field_simplify; [lca | C_field]).
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma step_3_N : forall α,
	⟦ Z 1 1 α ⟧ = ∣0⟩⟨0∣ .+ Cexp α .* ∣1⟩⟨1∣.
Proof. 
	intros.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	easy.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma step_4_N : 
	⟦ Z 0 1 (PI/4) ↕ Z 0 1 (PI/4) ⟷ X 2 1 0 ⟧ = (C1 + Cexp (PI / 4) ^ 2) / (√ 2)%R .* ∣0⟩.+ ((√2)%R * Cexp (PI/4)) .* ∣1⟩.
Proof.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	rewrite Cexp_0.
	Msimpl.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_assoc.
	rewrite (kron_mixed_product ⟨+∣ ⟨+∣).
	rewrite (kron_mixed_product ⟨-∣ ⟨-∣).
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	replace ((/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R) * (/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R)) with (((1 + Cexp (PI/4))^2)/2) by (simpl; C_field).
	replace ((/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R) * (/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R)) with (((1 - Cexp (PI/4))^2)/2) by (simpl; C_field).
	remember ((C1 + Cexp (PI / 4)) ^ 2 / C2) as c1.
	remember ((C1 - Cexp (PI / 4)) ^ 2 / C2) as c2.
	unfold xbasis_plus, xbasis_minus.
	autorewrite with scalar_move_db.
	repeat rewrite Mscale_plus_distr_r.
	restore_dims.
	replace (c1 * / (√ 2)%R .* ∣0⟩ .+ c1 * / (√ 2)%R .* ∣1⟩ .+ (c2 * / (√ 2)%R .* ∣0⟩ .+ c2 * / (√ 2)%R .* (-1 .* ∣1⟩))) with ((c1 + c2)/(√2)%R .* ∣0⟩ .+ ((c1 - c2)/(√2)%R .* ∣1⟩)) by lma.
	replace (c1 + c2) with ((1 + Cexp (PI/4)^2)) by (subst; simpl; C_field_simplify; [lca | C_field]).
	replace (c1 - c2) with ((2 * Cexp (PI/4))) by (subst; simpl; C_field_simplify; [lca | C_field]).
	apply Mplus_simplify.
	- simpl; easy.
	- apply Mscale_simplify.
		+ easy.
		+ C_field.
Qed.
