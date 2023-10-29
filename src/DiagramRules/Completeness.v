Require Import CoreData.
From QuantumLib Require Import Polar.
Require Import CoreRules.

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_SUP : forall α, ((Z 0 1 α) ↕ (Z 0 1 (α + PI))) ⟷ (X 2 1 0) ∝ Z 0 2 (2 *α + PI) ⟷ X 2 1 0.
Proof.
	intros.
	prop_exists_nonzero 1;
	simpl;
	unfold X_semantics.
	solve_matrix.
	- C_field_simplify; [ | split; nonzero ].
		repeat rewrite Cexp_add.
		autorewrite with Cexp_db.
		C_field_simplify.
		repeat rewrite <- Cexp_add.
		replace ((R1 + R1)%R, (R0 + R0)%R) with C2 by lca.
		apply Cplus_simplify; try easy.
		rewrite <- 3 Cmult_assoc.
		apply Cmult_simplify; try easy.
		rewrite Cmult_assoc.
		rewrite <- Cexp_add.
		replace (α + α)%R with (2 * α)%R by lra.
		lca.
	- C_field_simplify; [ | split; nonzero ].
		repeat rewrite Cexp_add.
		autorewrite with Cexp_db.
		C_field_simplify.
		repeat rewrite <- Cexp_add.
		lca.
Qed.  

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
	lma.
Qed.

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
	lma.
Qed.

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

Lemma z_to_x_plus : ∣0⟩ .+ ∣1⟩ = (√2)%R .* ∣+⟩.
Proof.
	rewrite xbasis_plus_spec.
	autorewrite with scalar_move_db.
	replace ((√ 2)%R * / (√ 2)%R) with (C1) by C_field.
	lma.
Qed.

Lemma z_to_x_minus : ∣0⟩ .+ -1 .* ∣1⟩ = (√2)%R .* ∣-⟩.
Proof.
	rewrite xbasis_minus_spec.
	autorewrite with scalar_move_db.
	replace ((√ 2)%R * / (√ 2)%R) with (C1) by C_field.
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mplus_plus_minus : ∣+⟩ .+ ∣-⟩ = (√2)%R .* ∣0⟩.
Proof. 
	unfold xbasis_plus.
	unfold xbasis_minus.
	solve_matrix.
	C_field.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mplus_plus_minus_opp : ∣+⟩ .+ -1 .* ∣-⟩ = (√2)%R .* ∣1⟩.
Proof. 
	unfold xbasis_plus.
	unfold xbasis_minus.
	solve_matrix.
	C_field_simplify.
	lca.
	C_field.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mplus_minus_plus : ∣-⟩ .+ ∣+⟩ = (√2)%R .* ∣0⟩.
Proof. 
	unfold xbasis_plus.
	unfold xbasis_minus.
	solve_matrix.
	C_field.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mplus_minus_opp_plus : -1 .* ∣-⟩ .+ ∣+⟩ = (√2)%R .* ∣1⟩.
Proof.
	unfold xbasis_plus.
	unfold xbasis_minus.
	solve_matrix.
	C_field_simplify.
	lca.
	C_field.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mplus_0_1 : ∣0⟩ .+ ∣1⟩ = (√2)%R .* ∣+⟩.
Proof. 
	unfold xbasis_plus.
	unfold xbasis_minus.
	solve_matrix.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mplus_0_1_opp : ∣0⟩ .+ -1 .* ∣1⟩ = (√2)%R .* ∣-⟩.
Proof. 
	unfold xbasis_plus.
	unfold xbasis_minus.
	solve_matrix.
	C_field_simplify.
	lca.
	C_field.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mplus_1_0 : ∣1⟩ .+ ∣0⟩ = (√2)%R .* ∣+⟩.
Proof. 
	unfold xbasis_plus.
	unfold xbasis_minus.
	solve_matrix.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mplus_1_opp_0 : -1 .* ∣1⟩ .+ ∣0⟩ = (√2)%R .* ∣-⟩.
Proof.
	unfold xbasis_plus.
	unfold xbasis_minus.
	solve_matrix.
	C_field_simplify.
	lca.
	C_field.
Qed.

Lemma σz_decomposition : σz = ∣0⟩⟨0∣ .+ -1 .* ∣1⟩⟨1∣.
Proof. solve_matrix. Qed.

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
Lemma completeness_C : forall (α β γ : R),
	(Z 1 2 0) ⟷ (((Z 0 1 β ↕ —) ⟷ X 2 1 PI) ↕ ((Z 0 1 α ↕ —) ⟷ X 2 1 0)) ⟷ ((Z 1 2 β ↕ Z 1 2 α) ⟷ (— ↕ X 2 1 γ ↕ —)) ⟷ (((— ↕ Z 1 2 0) ⟷ (X 2 1 (-γ) ↕ —)) ↕ —)
	∝ 
	(Z 1 2 0) ⟷ (((Z 0 1 α ↕ —) ⟷ X 2 1 0) ↕ ((Z 0 1 β ↕ —) ⟷ X 2 1 PI)) ⟷ ((Z 1 2 α ↕ Z 1 2 β) ⟷ (— ↕ X 2 1 (-γ) ↕ —)) ⟷ (— ↕ ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 γ))).
Proof. (* solve matrix takes forever *)
	intros.
	remember ((Z 0 1 α ↕ —) ⟷ X 2 1 0) as cs1.
	remember ((Z 0 1 β ↕ —) ⟷ X 2 1 PI) as cs1pi.
	remember (((Z 1 2 β ↕ Z 1 2 α) ⟷ (— ↕ X 2 1 γ ↕ —))) as cs2.	
	remember (((Z 1 2 α ↕ Z 1 2 β) ⟷ (— ↕ X 2 1 (-γ) ↕ —))) as cs2n.
	remember ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 γ)) as cs3.
	remember (((— ↕ Z 1 2 0) ⟷ (X 2 1 (-γ) ↕ —))) as cs3f.
	prop_exists_nonzero 1.
	simpl.
	rewrite Heqcs1.
	rewrite Heqcs1pi.
	clear Heqcs1; clear Heqcs1pi; clear cs1; clear cs1pi.
	rewrite c_step_1, c_step_1_pi.
	autorewrite with scalar_move_db.
	rewrite Cmult_1_l.
	apply Mscale_simplify; [| C_field].
	replace ((Cexp β .* ∣0⟩⟨0∣ .+ ∣0⟩⟨1∣ .+ ∣1⟩⟨0∣ .+ Cexp β .* ∣1⟩⟨1∣)) with (Cexp β .* (I 2) .+ ∣0⟩⟨1∣ .+ ∣1⟩⟨0∣) by (rewrite <- Mplus01; lma).
	replace ((∣0⟩⟨0∣ .+ Cexp α .* ∣0⟩⟨1∣ .+ Cexp α .* ∣1⟩⟨0∣ .+ ∣1⟩⟨1∣)) with (I 2 .+ Cexp α .* (∣0⟩⟨1∣ .+ ∣1⟩⟨0∣)) by (rewrite <- Mplus01; lma).
	fold (⟦ Z 1 2 0 ⟧).
	rewrite (ZX_semantic_equiv _ _ (Z 1 2 0)).
	unfold_dirac_spider.
	rewrite Cexp_0.
	Msimpl.
	restore_dims.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite <- (Mmult_assoc _ _ ⟨0∣).
	repeat rewrite <- (Mmult_assoc _ _ ⟨1∣).
	rewrite 2 (kron_mixed_product _ _ ∣0⟩ ∣0⟩).
	rewrite 2 (kron_mixed_product _ _ ∣1⟩ ∣1⟩).
	autorewrite with scalar_move_db.
	restore_dims.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_plus_distr_r.
	Msimpl.
	repeat rewrite Mmult_assoc.
	autorewrite with ketbra_mult_db.
	Msimpl.
	repeat rewrite <- Mmult_plus_distr_l.
	remember (Cexp β .* ∣0⟩ .+ ∣1⟩) as b0p1.
	remember (Cexp β .* ∣1⟩ .+ ∣0⟩) as b1p0.
	remember (∣0⟩ .+ Cexp α .* ∣1⟩) as a1p0.
	remember (∣1⟩ .+ Cexp α .* ∣0⟩) as a0p1.

	rewrite Heqcs2.
	rewrite Heqcs2n.
	rewrite 2 c_step_2.

	restore_dims.
	autorewrite with scalar_move_db.
	apply Mscale_simplify; [| lca].
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.

	repeat rewrite Mmult_plus_distr_l.

	repeat rewrite <- (Mmult_assoc _ _ ⟨0∣).
	repeat rewrite <- (Mmult_assoc _ _ ⟨1∣).
	restore_dims.
	repeat rewrite (kron_mixed_product).

	replace (⟨0∣ × b0p1) with (Cexp β .* I 1) by (subst; rewrite Mmult_plus_distr_l; autorewrite with scalar_move_db; autorewrite with ketbra_mult_db; lma).
	replace (⟨0∣ × b1p0) with (I 1) by (subst; rewrite Mmult_plus_distr_l; autorewrite with scalar_move_db; autorewrite with ketbra_mult_db; lma).
	replace (⟨1∣ × b0p1) with (I 1) by (subst; rewrite Mmult_plus_distr_l; autorewrite with scalar_move_db; autorewrite with ketbra_mult_db; lma).
	replace (⟨1∣ × b1p0) with (Cexp β .* I 1) by (subst; rewrite Mmult_plus_distr_l; autorewrite with scalar_move_db; autorewrite with ketbra_mult_db; lma).
	replace (⟨0∣ × a0p1) with (Cexp α .* I 1) by (subst; rewrite Mmult_plus_distr_l; autorewrite with scalar_move_db; autorewrite with ketbra_mult_db; lma).
	replace (⟨0∣ × a1p0) with (I 1) by (subst; rewrite Mmult_plus_distr_l; autorewrite with scalar_move_db; autorewrite with ketbra_mult_db; lma).
	replace (⟨1∣ × a0p1) with (I 1) by (subst; rewrite Mmult_plus_distr_l; autorewrite with scalar_move_db; autorewrite with ketbra_mult_db; lma).
	replace (⟨1∣ × a1p0) with (Cexp α .* I 1) by (subst; rewrite Mmult_plus_distr_l; autorewrite with scalar_move_db; autorewrite with ketbra_mult_db; lma).

	autorewrite with scalar_move_db.
	Msimpl.

	restore_dims.
	repeat rewrite <- Mscale_mult_dist_r.
	repeat rewrite Mmult_assoc.
	repeat rewrite <- Mmult_plus_distr_l.
	restore_dims.
	repeat rewrite kron_assoc by auto with wf_db.

	remember (Cexp β .* ⟨0∣ .+ Cexp α .* ⟨1∣) as b0a1.
	remember (Cexp α .* ⟨0∣ .+ Cexp β .* ⟨1∣) as a0b1.
	rewrite (Cmult_comm (Cexp β)).
	remember (⟨0∣ .+ Cexp α * Cexp β .* ⟨1∣) as p0ab1.
	remember (Cexp α * Cexp β .* ⟨0∣ .+ ⟨1∣) as ab0p1.

	autorewrite with scalar_move_db.
	repeat rewrite <- kron_assoc by auto with wf_db.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	repeat rewrite <- Mmult_assoc.
	repeat rewrite kron_mixed_product.
	Msimpl.

	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	repeat rewrite kron_assoc by auto with wf_db.
	repeat rewrite <- Mmult_assoc.
	restore_dims.
	repeat rewrite kron_mixed_product.
	Msimpl.

	assert (comp_0p : (⟦ cs3f ⟧) × (∣0⟩ ⊗ ∣+⟩) = / C2 .* ((∣+⟩ ⊗ ∣+⟩ .+ Cexp (- γ) .* (∣-⟩ ⊗ ∣-⟩)))).
	{
		subst.
		rewrite c_step_3_flipped.
		rewrite Mmult_assoc.
		rewrite <- notc_decomposition.
		rewrite Mmult_plus_distr_r.
		repeat rewrite kron_mixed_product.
		Msimpl.
		rewrite MmultX0.
		repeat rewrite Mmult_assoc.
		autorewrite with ketbra_mult_db.
		autorewrite with scalar_move_db.
		Msimpl.
		rewrite kron_plus_distr_r.
		repeat rewrite Mmult_plus_distr_r.
		repeat rewrite Mmult_plus_distr_l.
		autorewrite with scalar_move_db.
		repeat rewrite kron_mixed_product.
		Msimpl.
		repeat rewrite Mmult_assoc.
		autorewrite with ketbra_mult_db.
		autorewrite with scalar_move_db.
		Msimpl.
		replace (- / (√ 2)%R) with (/ (√2)%R * -1) by (C_field_simplify; [lca | C_field]).
		rewrite <- (Mscale_assoc _ _ _ (-1)).
		autorewrite with scalar_move_db.
		replace (∣+⟩ ⊗ ∣1⟩ .+ ∣+⟩ ⊗ ∣0⟩) with ((√2)%R .* ∣+⟩⊗∣+⟩) by (rewrite xbasis_plus_spec at 2; autorewrite with scalar_move_db; rewrite Cinv_l by C_field; lma).
		replace ((-1 .* (∣-⟩ ⊗ ∣1⟩) .+ ∣-⟩ ⊗ ∣0⟩)) with ((√2)%R .* ∣-⟩⊗∣-⟩) by (rewrite xbasis_minus_spec at 2; autorewrite with scalar_move_db; rewrite Cinv_l by C_field; lma).
		autorewrite with scalar_move_db.
		rewrite <- Cmult_assoc.
		repeat rewrite Cinv_l by C_field.
		Msimpl.
		rewrite Cmult_1_r.
		rewrite Cinv_sqrt2_sqrt.
		easy.
	}
	Msimpl.

	rewrite Heqcs3f.
	rewrite c_step_3_flipped.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.
	rewrite <- notc_decomposition.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite kron_mixed_product.
	repeat rewrite Mmult_assoc.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	rewrite MmultX0.
	rewrite MmultX1.
	replace (- / (√ 2)%R) with (/(√2)%R * -1) by (C_field_simplify; [lca | C_field]).
	repeat rewrite <- Mscale_assoc.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	repeat rewrite kron_mixed_product.
	Msimpl.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	replace (Cexp (- γ) * - / (√ 2)%R) with (/ (√ 2)%R * - Cexp (- γ)) by lca.
	replace (Cexp (- γ) * / (√ 2)%R) with (/ (√ 2)%R * Cexp (- γ)) by lca.
	repeat rewrite <- Mscale_assoc.
	autorewrite with scalar_move_db.
	replace (-1 * / (√ 2)%R) with (/ (√ 2)%R * -1) by lca.
	repeat rewrite <- (Mscale_assoc _ _ _ (-1)).
	autorewrite with scalar_move_db.
	replace (- Cexp γ * / (√ 2)%R * / (√ 2)%R * / (√ 2)%R) with (/ (√ 2)%R * / (√ 2)%R * / (√ 2)%R * - Cexp γ) by lca.
	replace (Cexp γ * / (√ 2)%R * / (√ 2)%R * / (√ 2)%R) with (/ (√ 2)%R * / (√ 2)%R * / (√ 2)%R * Cexp γ) by lca.
	repeat rewrite <- (Mscale_assoc _ _ _ (Cexp γ)).
	repeat rewrite <- (Mscale_assoc _ _ _ (- Cexp γ)).
	autorewrite with scalar_move_db.
	repeat rewrite (Cmult_comm _ ((/ (√ 2)%R * / (√ 2)%R) * / (√ 2)%R)).
	repeat rewrite <- (Mscale_assoc _ _ ((/ (√ 2)%R * / (√ 2)%R) * / (√ 2)%R)).
	autorewrite with scalar_move_db.
	remember (∣+⟩ .+ Cexp (- γ) .* ∣-⟩) as pcngm.
	remember (∣+⟩ .+ - Cexp (- γ) .* ∣-⟩) as  pncngm.
	repeat rewrite <- (Mscale_mult_dist_l _ _ _ (Cexp _)).
	repeat rewrite <- (Mscale_mult_dist_l _ _ _ (- Cexp _)).
	repeat rewrite <- (Mscale_mult_dist_l _ _ _ (Cexp α * _)).
	restore_dims.
	repeat rewrite <- Mscale_kron_dist_l.
	repeat rewrite <- Mmult_plus_distr_r.
	repeat rewrite <- kron_plus_distr_r.

	rewrite Heqcs3, c_step_3.
	autorewrite with Cexp_db.
	repeat rewrite Mmult_assoc.
	rewrite <- cnot_decomposition.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite kron_mixed_product.
	rewrite MmultX0, MmultX1.
	repeat rewrite Mmult_assoc.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.

	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	repeat rewrite kron_mixed_product.
	Msimpl.
	
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.

	replace (Cexp γ * - / (√ 2)%R) with (/(√2)%R * - Cexp γ) by lca.
	replace (Cexp γ * / (√ 2)%R) with (/(√2)%R * Cexp γ) by lca.
	repeat rewrite <- (Mscale_assoc _ _ _ (Cexp γ)).
	repeat rewrite <- (Mscale_assoc _ _ _ (- Cexp γ)).
	autorewrite with scalar_move_db.

	replace (- / (√ 2)%R * / (√ 2)%R) with (/ (√ 2)%R * / (√ 2)%R * -1) by lca.

	repeat rewrite <- (Mscale_assoc _ _ _ (-1)).
	autorewrite with scalar_move_db.

	replace (/ (√ 2)%R * - / Cexp γ * (/ (√ 2)%R * / (√ 2)%R)) with (/ (√ 2)%R * / (√ 2)%R * / (√ 2)%R * (- / Cexp γ)) by lca.
	replace (/ (√ 2)%R * / Cexp γ * (/ (√ 2)%R * / (√ 2)%R)) with (/ (√ 2)%R * / (√ 2)%R * / (√ 2)%R * / Cexp γ) by lca.
	repeat rewrite <- (Mscale_assoc _ _ _ (/ Cexp γ)).
	repeat rewrite <- (Mscale_assoc _ _ _ (- / Cexp γ)).
	autorewrite with scalar_move_db.

	repeat rewrite <- (Mscale_assoc _ _ _ (/ Cexp γ)).
	repeat rewrite <- (Mscale_assoc _ _ _ (- / Cexp γ)).
	autorewrite with scalar_move_db.

	replace (Cexp α * (/ (√ 2)%R * / (√ 2)%R * / (√ 2)%R)) with ((/ (√ 2)%R * / (√ 2)%R * / (√ 2)%R) * Cexp α) by lca.
	replace (Cexp β * (/ (√ 2)%R * / (√ 2)%R * / (√ 2)%R)) with ((/ (√ 2)%R * / (√ 2)%R * / (√ 2)%R) * Cexp β) by lca.
	replace (Cexp α * Cexp β * (/ (√ 2)%R * / (√ 2)%R * / (√ 2)%R)) with ((/ (√ 2)%R * / (√ 2)%R * / (√ 2)%R) * Cexp α * Cexp β) by lca.
	repeat rewrite <- (Mscale_assoc _ _ _ (Cexp _)).
	autorewrite with scalar_move_db.
	apply Mscale_simplify; [|lca].

	remember (∣+⟩ .+ - Cexp γ .* ∣-⟩) as pncgm.
	remember (∣+⟩ .+ Cexp γ .* ∣-⟩) as pcgm.

	rewrite <- Cexp_neg.
	repeat rewrite <- Mscale_mult_dist_l.
	repeat rewrite <- Mmult_plus_distr_r.

  replace (pncngm ⊗ ∣1⟩ .+ pcngm ⊗ ∣0⟩ .+ Cexp γ .* (-1 .* (pncngm ⊗ ∣1⟩) .+ pcngm ⊗ ∣0⟩)) with (((1 - Cexp γ) .* pncngm) ⊗ ∣1⟩ .+ ((1 + Cexp γ) .* pcngm) ⊗ ∣0⟩) by lma.

	replace ((pcngm ⊗ ∣1⟩ .+ pncngm ⊗ ∣0⟩ .+ - Cexp γ .* (-1 .* (pcngm ⊗ ∣1⟩) .+ pncngm ⊗ ∣0⟩))) with (((1 + Cexp γ) .* pcngm) ⊗ ∣1⟩ .+ ((1 - Cexp γ) .* pncngm) ⊗ ∣0⟩) by lma.

	replace ((pncngm ⊗ ∣1⟩ .+ pcngm ⊗ ∣0⟩ .+ - Cexp γ .* (-1 .* (pncngm ⊗ ∣1⟩) .+ pcngm ⊗ ∣0⟩))) with (((1 + Cexp γ) .* pncngm) ⊗ ∣1⟩ .+ ((1 - Cexp γ) .* pcngm) ⊗ ∣0⟩) by lma.

	replace (pcngm ⊗ ∣1⟩ .+ pncngm ⊗ ∣0⟩ .+ Cexp γ .* (-1 .* (pcngm ⊗ ∣1⟩) .+ pncngm ⊗ ∣0⟩)) with (((1 - Cexp γ) .* pcngm ⊗ ∣1⟩) .+ (1 + Cexp γ) .* pncngm ⊗ ∣0⟩) by lma.

	(* from here *)

	replace (∣0⟩ ⊗ (∣1⟩ ⊗ pncgm .+ ∣0⟩ ⊗ pcgm) .+ Cexp (- γ) .* (∣0⟩ ⊗ (-1 .* (∣1⟩ ⊗ pncgm) .+ ∣0⟩ ⊗ pcgm))) with (∣0⟩ ⊗ (∣1⟩ ⊗ ((1 - Cexp (-γ)).* pncgm) .+ ∣0⟩ ⊗ ((1 + Cexp (-γ)) .* pcgm))) by lma.

	replace ((∣1⟩ ⊗ (∣1⟩ ⊗ pncgm .+ ∣0⟩ ⊗ pcgm) .+ - Cexp (- γ) .* (∣1⟩ ⊗ (-1 .* (∣1⟩ ⊗ pncgm) .+ ∣0⟩ ⊗ pcgm)))) with (∣1⟩ ⊗ (∣1⟩ ⊗ ((1 + Cexp (-γ)) .* pncgm) .+ ∣0⟩ ⊗ ((1 - Cexp (- γ)) .* pcgm))) by lma.

	replace ((∣0⟩ ⊗ (∣1⟩ ⊗ pcgm .+ ∣0⟩ ⊗ pncgm) .+ - Cexp (- γ) .* (∣0⟩ ⊗ (-1 .* (∣1⟩ ⊗ pcgm) .+ ∣0⟩ ⊗ pncgm)))) with (∣0⟩ ⊗ (∣1⟩ ⊗ ((1 + Cexp (-γ)) .* pcgm) .+ ∣0⟩ ⊗ ((1 - Cexp (-γ)) .* pncgm))) by lma.

	replace (∣1⟩ ⊗ (∣1⟩ ⊗ pcgm .+ ∣0⟩ ⊗ pncgm) .+ Cexp (- γ) .* (∣1⟩ ⊗ (-1 .* (∣1⟩ ⊗ pcgm) .+ ∣0⟩ ⊗ pncgm))) with (∣1⟩ ⊗ (∣1⟩ ⊗ ((1 - Cexp (-γ)).* pcgm) .+ ∣0⟩ ⊗ ((1 + Cexp (-γ)) .* pncgm))) by lma.

	remember (((C1 - Cexp γ) .* pncngm ⊗ ∣1⟩ .+ (C1 + Cexp γ) .* pcngm ⊗ ∣0⟩) ⊗ ∣0⟩) as v1.
	remember ((((C1 + Cexp γ) .* pcngm ⊗ ∣1⟩ .+ (C1 - Cexp γ) .* pncngm ⊗ ∣0⟩) ⊗ ∣0⟩)) as v2.
	remember ((((C1 + Cexp γ) .* pncngm ⊗ ∣1⟩ .+ (C1 - Cexp γ) .* pcngm ⊗ ∣0⟩) ⊗ ∣1⟩)) as v3.
	remember ((((C1 - Cexp γ) .* pcngm ⊗ ∣1⟩ .+ (C1 + Cexp γ) .* pncngm ⊗ ∣0⟩) ⊗ ∣1⟩)) as v4.
	remember (∣0⟩ ⊗ (∣1⟩ ⊗ ((C1 - Cexp (- γ)) .* pncgm) .+ ∣0⟩ ⊗ ((C1 + Cexp (- γ)) .* pcgm))) as g1.
	remember (∣1⟩ ⊗ (∣1⟩ ⊗ ((C1 + Cexp (- γ)) .* pncgm) .+ ∣0⟩ ⊗ ((C1 - Cexp (- γ)) .* pcgm))) as g2.
	remember (∣0⟩ ⊗ (∣1⟩ ⊗ ((C1 + Cexp (- γ)) .* pcgm) .+ ∣0⟩ ⊗ ((C1 - Cexp (- γ)) .* pncgm))) as g3.
	remember (∣1⟩ ⊗ (∣1⟩ ⊗ ((C1 - Cexp (- γ)) .* pcgm) .+ ∣0⟩ ⊗ ((C1 + Cexp (- γ)) .* pncgm))) as g4.
	autorewrite with scalar_move_db.
	
	rewrite Heqb0a1, Heqp0ab1, Heqab0p1, Heqa0b1.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	repeat rewrite Mscale_plus_distr_r.
	repeat rewrite Mscale_assoc.

	restore_dims.
	replace (Cexp β .* (v1 × ⟨0∣) .+ Cexp α .* (v1 × ⟨1∣) .+ (Cexp β .* (v2 × ⟨0∣) .+ Cexp β * (Cexp α * Cexp β) .* (v2 × ⟨1∣)) .+ (Cexp α * (Cexp α * Cexp β) .* (v3 × ⟨0∣) .+ Cexp α .* (v3 × ⟨1∣)) .+ (Cexp α * Cexp β * Cexp α .* (v4 × ⟨0∣) .+ Cexp α * Cexp β * Cexp β .* (v4 × ⟨1∣))) with (Cexp β .* ((v1 .+ v2)×⟨0∣) .+ Cexp α .* ((v1 .+ v3)×⟨1∣) .+ (Cexp α * Cexp α * Cexp β).* ((v3 .+ v4)×⟨0∣) .+ (Cexp α * Cexp β * Cexp β) .* ((v2 .+ v4)×⟨1∣)) by lma.

	replace (Cexp β .* (g1 × ⟨0∣) .+ Cexp α .* (g1 × ⟨1∣) .+ (Cexp α * (Cexp α * Cexp β) .* (g2 × ⟨0∣) .+ Cexp α .* (g2 × ⟨1∣)) .+ (Cexp β .* (g3 × ⟨0∣) .+ Cexp β * (Cexp α * Cexp β) .* (g3 × ⟨1∣)) .+ (Cexp α * Cexp β * Cexp α .* (g4 × ⟨0∣) .+ Cexp α * Cexp β * Cexp β .* (g4 × ⟨1∣))) with (Cexp β .* ((g1 .+ g3)×⟨0∣) .+ Cexp α .* ((g1 .+ g2)×⟨1∣) .+ (Cexp α * Cexp α * Cexp β) .* ((g2 .+ g4)×⟨0∣) .+ (Cexp α * Cexp β * Cexp β) .* ((g3 .+ g4)×⟨1∣)) by lma.
	apply Mplus_simplify.
	apply Mplus_simplify.
	apply Mplus_simplify.
	-	apply Mscale_simplify; try easy.
		apply Mmult_simplify; try easy.
		subst.
		repeat rewrite Cminus_unfold.
		repeat rewrite Mscale_plus_distr_l.
		repeat rewrite Mscale_plus_distr_r.
		Msimpl.
		repeat rewrite Mscale_assoc.
		restore_dims.
		replace (- Cexp γ * - Cexp (- γ)) with (Cexp γ * Cexp (-γ)) by lca.
		replace (- Cexp (-γ) * - Cexp γ) with (Cexp γ * Cexp (-γ)) by lca.
		replace (Cexp (-γ) * Cexp γ) with (Cexp γ * Cexp (-γ)) by lca.
		repeat rewrite <- Cexp_add.
		rewrite Rplus_opp_r.
		rewrite Cexp_0.
		Msimpl.
		repeat rewrite kron_plus_distr_l.		
		repeat rewrite kron_plus_distr_r.		
		repeat rewrite <- Mplus_assoc.

		autorewrite with scalar_move_db.

		replace (∣+⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ .+ - Cexp (- γ) .* (∣-⟩ ⊗ ∣1⟩ ⊗ ∣0⟩) .+ - Cexp γ .* (∣+⟩ ⊗ ∣1⟩ ⊗ ∣0⟩) .+ ∣-⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ .+ ∣+⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ .+ Cexp (- γ) .* (∣-⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .+ Cexp γ .* (∣+⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .+ ∣-⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ .+ ∣+⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ .+ Cexp (- γ) .* (∣-⟩ ⊗ ∣1⟩ ⊗ ∣0⟩) .+ Cexp γ .* (∣+⟩ ⊗ ∣1⟩ ⊗ ∣0⟩) .+ ∣-⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ .+ ∣+⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ .+ - Cexp (- γ) .* (∣-⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .+ - Cexp γ .* (∣+⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .+ ∣-⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) with (((∣+⟩ .+ ∣-⟩) ⊗ ∣1⟩ ⊗ ∣0⟩) .+ ((∣+⟩ .+ ∣-⟩) ⊗ ∣1⟩ ⊗ ∣0⟩) .+ ((∣+⟩ .+ ∣-⟩) ⊗ ∣0⟩ ⊗ ∣0⟩) .+ ((∣+⟩ .+ ∣-⟩) ⊗ ∣0⟩ ⊗ ∣0⟩) .+ (Cexp γ .* (∣+⟩ ⊗ ∣+⟩ ⊗ ∣0⟩) .+ - Cexp γ .* (∣+⟩ ⊗ ∣+⟩ ⊗ ∣0⟩)) .+ (Cexp (-γ) .* (∣-⟩ ⊗ ∣+⟩ ⊗ ∣0⟩) .+ - Cexp (-γ) .* (∣-⟩ ⊗ ∣+⟩ ⊗ ∣0⟩))) by lma.

		replace (∣0⟩ ⊗ (∣1⟩ ⊗ ∣+⟩) .+ - Cexp γ .* (∣0⟩ ⊗ (∣1⟩ ⊗ ∣-⟩)) .+ - Cexp (- γ) .* (∣0⟩ ⊗ (∣1⟩ ⊗ ∣+⟩)) .+ ∣0⟩ ⊗ (∣1⟩ ⊗ ∣-⟩) .+ ∣0⟩ ⊗ (∣0⟩ ⊗ ∣+⟩) .+ Cexp γ .* (∣0⟩ ⊗ (∣0⟩ ⊗ ∣-⟩)) .+ Cexp (- γ) .* (∣0⟩ ⊗ (∣0⟩ ⊗ ∣+⟩)) .+ ∣0⟩ ⊗ (∣0⟩ ⊗ ∣-⟩) .+ ∣0⟩ ⊗ (∣1⟩ ⊗ ∣+⟩) .+ Cexp γ .* (∣0⟩ ⊗ (∣1⟩ ⊗ ∣-⟩)) .+ Cexp (- γ) .* (∣0⟩ ⊗ (∣1⟩ ⊗ ∣+⟩)) .+ ∣0⟩ ⊗ (∣1⟩ ⊗ ∣-⟩) .+ ∣0⟩ ⊗ (∣0⟩ ⊗ ∣+⟩) .+ - Cexp γ .* (∣0⟩ ⊗ (∣0⟩ ⊗ ∣-⟩)) .+ - Cexp (- γ) .* (∣0⟩ ⊗ (∣0⟩ ⊗ ∣+⟩)) .+ ∣0⟩ ⊗ (∣0⟩ ⊗ ∣-⟩)) with ((∣0⟩ ⊗ (∣1⟩ ⊗ (∣+⟩ .+ ∣-⟩))) .+(∣0⟩ ⊗ (∣1⟩ ⊗ (∣+⟩ .+ ∣-⟩))) .+(∣0⟩ ⊗ (∣0⟩ ⊗ (∣+⟩ .+ ∣-⟩))) .+(∣0⟩ ⊗ (∣0⟩ ⊗ (∣+⟩ .+ ∣-⟩))) .+(Cexp γ .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣-⟩) .+- Cexp γ .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣-⟩)) .+(Cexp (-γ) .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣+⟩) .+- Cexp (-γ) .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣+⟩))) by lma.
		rewrite Mplus_plus_minus.
		autorewrite with scalar_move_db.
		repeat rewrite Cplus_opp_r.
		Msimpl.
		repeat rewrite kron_assoc by auto with wf_db.
		lma.
	- apply Mscale_simplify; try easy.
		apply Mmult_simplify; try easy.
		subst.
		repeat rewrite Cminus_unfold.
		repeat rewrite Mscale_plus_distr_l.
		repeat rewrite Mscale_plus_distr_r.
		Msimpl.
		repeat rewrite Mscale_assoc.
		restore_dims.
		replace (- Cexp γ * - Cexp (- γ)) with (Cexp γ * Cexp (-γ)) by lca.
		replace (- Cexp (-γ) * - Cexp γ) with (Cexp γ * Cexp (-γ)) by lca.
		replace (Cexp (-γ) * Cexp γ) with (Cexp γ * Cexp (-γ)) by lca.
		replace (- Cexp γ * Cexp (-γ)) with (-(Cexp γ * Cexp (-γ))) by lca. 
		replace (Cexp γ * - Cexp (-γ)) with (-(Cexp γ * Cexp (-γ))) by lca. 
		replace (- Cexp (-γ) * Cexp γ) with (-(Cexp γ * Cexp (-γ))) by lca. 
		replace (Cexp (-γ) * - Cexp γ) with (-(Cexp γ * Cexp (-γ))) by lca. 
		repeat rewrite <- Cexp_add.
		rewrite Rplus_opp_r.
		rewrite Cexp_0.
		Msimpl.
		repeat rewrite kron_plus_distr_l.		
		repeat rewrite kron_plus_distr_r.		
		repeat rewrite <- Mplus_assoc.
		repeat rewrite <- kron_assoc by auto with wf_db.
		autorewrite with scalar_move_db.
		unfold xbasis_plus, xbasis_minus.
		autorewrite with scalar_move_db.
		repeat rewrite kron_plus_distr_l.
		repeat rewrite kron_plus_distr_r.
		autorewrite with scalar_move_db.
		repeat rewrite Mscale_plus_distr_r.
		repeat rewrite Mscale_assoc.
		lma.
	- apply Mscale_simplify; try easy.
		apply Mmult_simplify; try easy.
		subst.
		repeat rewrite Cminus_unfold.
		repeat rewrite Mscale_plus_distr_l.
		repeat rewrite Mscale_plus_distr_r.
		Msimpl.
		repeat rewrite Mscale_assoc.
		restore_dims.
		replace (- Cexp γ * - Cexp (- γ)) with (Cexp γ * Cexp (-γ)) by lca.
		replace (- Cexp (-γ) * - Cexp γ) with (Cexp γ * Cexp (-γ)) by lca.
		replace (Cexp (-γ) * Cexp γ) with (Cexp γ * Cexp (-γ)) by lca.
		replace (- Cexp γ * Cexp (-γ)) with (-(Cexp γ * Cexp (-γ))) by lca. 
		replace (Cexp γ * - Cexp (-γ)) with (-(Cexp γ * Cexp (-γ))) by lca. 
		replace (- Cexp (-γ) * Cexp γ) with (-(Cexp γ * Cexp (-γ))) by lca. 
		replace (Cexp (-γ) * - Cexp γ) with (-(Cexp γ * Cexp (-γ))) by lca. 
		repeat rewrite <- Cexp_add.
		rewrite Rplus_opp_r.
		rewrite Cexp_0.
		Msimpl.
		repeat rewrite kron_plus_distr_l.		
		repeat rewrite kron_plus_distr_r.		
		repeat rewrite <- Mplus_assoc.
		repeat rewrite <- kron_assoc by auto with wf_db.
		autorewrite with scalar_move_db.
		unfold xbasis_plus, xbasis_minus.
		autorewrite with scalar_move_db.
		repeat rewrite kron_plus_distr_l.
		repeat rewrite kron_plus_distr_r.
		autorewrite with scalar_move_db.
		repeat rewrite Mscale_plus_distr_r.
		repeat rewrite Mscale_assoc.
		lma.
	- apply Mscale_simplify; try easy.
		apply Mmult_simplify; try easy.
		subst.
		repeat rewrite Cminus_unfold.
		repeat rewrite Mscale_plus_distr_l.
		repeat rewrite Mscale_plus_distr_r.
		Msimpl.
		repeat rewrite Mscale_assoc.
		restore_dims.
		replace (- Cexp γ * - Cexp (- γ)) with (Cexp γ * Cexp (-γ)) by lca.
		replace (- Cexp (-γ) * - Cexp γ) with (Cexp γ * Cexp (-γ)) by lca.
		replace (Cexp (-γ) * Cexp γ) with (Cexp γ * Cexp (-γ)) by lca.
		replace (- Cexp γ * Cexp (-γ)) with (-(Cexp γ * Cexp (-γ))) by lca. 
		replace (Cexp γ * - Cexp (-γ)) with (-(Cexp γ * Cexp (-γ))) by lca. 
		replace (- Cexp (-γ) * Cexp γ) with (-(Cexp γ * Cexp (-γ))) by lca. 
		replace (Cexp (-γ) * - Cexp γ) with (-(Cexp γ * Cexp (-γ))) by lca. 
		repeat rewrite <- Cexp_add.
		rewrite Rplus_opp_r.
		rewrite Cexp_0.
		Msimpl.
		repeat rewrite kron_plus_distr_l.		
		repeat rewrite kron_plus_distr_r.		
		repeat rewrite <- Mplus_assoc.
		repeat rewrite <- kron_assoc by auto with wf_db.
		autorewrite with scalar_move_db.
		unfold xbasis_plus, xbasis_minus.
		autorewrite with scalar_move_db.
		repeat rewrite kron_plus_distr_l.
		repeat rewrite kron_plus_distr_r.
		autorewrite with scalar_move_db.
		repeat rewrite Mscale_plus_distr_r.
		repeat rewrite Mscale_assoc.
		lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_BW :
	◁ ⟷ Z 1 1 PI ⟷ ▷ ∝ ▷ ⟷ X 1 1 PI.
Proof. 
	prop_exists_nonzero 1.
	remember (Z 1 1 PI) as z.
	remember (X 1 1 PI) as x.
	simpl.
	rewrite zx_triangle_semantics, zx_triangle_left_semantics.
	Msimpl.
	rewrite Heqz, Heqx.
	rewrite z_1_1_pi_σz, x_1_1_pi_σx.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite <- (Mmult_assoc _ ∣0⟩).
	repeat rewrite <- (Mmult_assoc _ ∣1⟩).
	restore_dims.
	rewrite MmultX1.
	rewrite MmultX0.
	rewrite ket0_equiv.
	rewrite ket1_equiv.
	restore_dims.
	rewrite Z0_spec.
	rewrite Z1_spec.
	rewrite <- ket0_equiv.
	rewrite <- ket1_equiv.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_assoc.
	repeat rewrite <- (Mmult_assoc _ ∣0⟩).
	repeat rewrite <- (Mmult_assoc _ ∣1⟩).
	autorewrite with ketbra_mult_db.
	Msimpl.
	lma.
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

(* @nocheck name *)
(* Conventional name *)
Lemma Cexp_spec : forall α, Cexp α = cos α + Ci * sin α.
Proof. intros; lca. Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Cexp_minus : forall θ,
	Cexp θ + Cexp (-θ) = 2 * cos θ.
Proof.
	intros.
	unfold Cexp.
	rewrite cos_neg.
	rewrite sin_neg.
	lca.
Qed.

Lemma xbasis_add_0 : 
	∣+⟩ .+ ∣-⟩ = (√2)%R .* ∣0⟩.
Proof.
	unfold xbasis_plus, xbasis_minus.
	solve_matrix.
	C_field.
Qed.

Lemma xbasis_add_1 : 
	∣+⟩ .+ -1 .* ∣-⟩ = (√2)%R .* ∣1⟩.
Proof.
	unfold xbasis_plus, xbasis_minus.
	solve_matrix.
	C_field_simplify; [lca | C_field].
Qed.

Lemma zbasis_add_plus :
	∣0⟩ .+ ∣1⟩ = (√2)%R .* ∣+⟩.
Proof. unfold xbasis_plus. solve_matrix. Qed.

Lemma zbasis_add_minus :
	∣0⟩ .+ -1 .* ∣1⟩ = (√2)%R .* ∣-⟩.
Proof. unfold xbasis_minus. solve_matrix. C_field. Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_N : forall α β θ_1 θ_2 γ θ_3,
	2 * Cexp (θ_3) * cos(γ) = Cexp (θ_1) * cos(α) + Cexp (θ_2) * cos(β) ->
	(((Z 0 1 α ↕ Z 0 1 (-α) ⟷ X 2 1 0) ⟷ Z 1 1 θ_1) ↕ ((Z 0 1 β ↕ Z 0 1 (-β) ⟷ X 2 1 0) ⟷ Z 1 1 θ_2)) ⟷ ((— ↕ (X 0 1 (PI/2) ⟷ Z 1 2 0) ↕ —) ⟷ (X 2 1 0 ↕ X 2 1 0)) ⟷ (Z 1 1 (PI/4) ↕ Z 1 1 (PI/4)) ⟷ X 2 1 0 ∝ 
	((Z 0 1 γ ↕ Z 0 1 (-γ) ⟷ X 2 1 0) ↕ (Z 0 1 (PI/4) ↕ Z 0 1 (PI/4) ⟷ X 2 1 0)) ⟷ (Z 2 1 θ_3).
Proof. 
	intros.
	remember (Z 0 1 α ↕ Z 0 1 (- α) ⟷ X 2 1 0) as step_1_1.
	remember (Z 0 1 β ↕ Z 0 1 (- β) ⟷ X 2 1 0) as step_1_2.
	remember (Z 0 1 γ ↕ Z 0 1 (- γ)) as step_1_3.
	remember ((Z 0 1 (PI / 4) ↕ Z 0 1 (PI / 4) ⟷ X 2 1 0)) as step_4.
	remember ((— ↕ (X 0 1 (PI / 2) ⟷ Z 1 2 0) ↕ —)
⟷ (X 2 1 0 ↕ X 2 1 0)) as step_2.
	remember (Z 1 1 (PI / 4) ↕ Z 1 1 (PI / 4)) as step_3.
	remember (X 2 1 0) as final_step.
	remember (Z 2 1 θ_3) as final_step_2.
	remember (Z 1 1 θ_1) as step_1_5.
	remember (Z 1 1 θ_2) as step_1_6.
	prop_exists_nonzero 1.
	Msimpl.
	simpl.
	rewrite Heqstep_1_1, Heqstep_1_2.
	rewrite Heqfinal_step.
	rewrite 2 step_1_N.
	rewrite <- Heqfinal_step.
	rewrite Heqstep_1_6.
	rewrite Heqstep_1_5.
	rewrite 2 step_3_N.
	rewrite 2 Mmult_plus_distr_r.
	rewrite 4 Mmult_plus_distr_l.
	restore_dims.
	autorewrite with scalar_move_db.
	rewrite 2 (Mmult_assoc ∣0⟩).
	rewrite 2 (Mmult_assoc ∣1⟩).
	autorewrite with ketbra_mult_db.
	Msimpl.
	rewrite Heqstep_2.
	rewrite Heqfinal_step.
	rewrite zx_compose_spec.
	rewrite <- zx_compose_spec.
	rewrite step_2_N.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	(* Simplify scalars here potentially *)
	rewrite 2 Cexp_minus.
	replace (2 * cos α / (√2)%R * Cexp θ_1) with ((√2)%R * (cos α * Cexp θ_1)) by C_field.
	replace (2 * cos β / (√2)%R * Cexp θ_2) with ((√2)%R * (cos β * Cexp θ_2)) by C_field.
	rewrite <- 4 Mscale_assoc.
	rewrite <- 2 Mscale_plus_distr_r.
	autorewrite with scalar_move_db.
	replace (/ (√ 2)%R * ((√ 2)%R * (√ 2)%R)) with ((√2)%R * C1) by C_field.
	replace (Cexp (PI / 2) / (√ 2)%R * ((√ 2)%R * (√ 2)%R)) with (Ci * (√2)%R) by (autorewrite with Cexp_db; C_field).
	rewrite Cmult_1_r.
	(* End simplify block (Can break proof below) *)
	repeat rewrite Mmult_assoc.
	repeat rewrite kron_mixed_product.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_assoc.
	autorewrite with scalar_move_db.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	(* Simplify scalars here potentially *)
	(* End simplify block (Can break proof below) *)
	Msimpl.
	replace ((√ 2)%R * ((/ (√ 2)%R + cos β * Cexp θ_2 * / (√ 2)%R) * (/ (√ 2)%R + cos α * Cexp θ_1 * / (√ 2)%R))) with ((1 + cos α * Cexp θ_1 ) * (1 + cos β * Cexp θ_2) / (√2)%R) by C_field.
	replace (Ci * (√ 2)%R * ((/ (√ 2)%R + cos β * Cexp θ_2 * - / (√ 2)%R) * (/ (√ 2)%R + cos α * Cexp θ_1 * / (√ 2)%R))) with (Ci * (1 + cos α * Cexp θ_1 ) * (1 - cos β * Cexp θ_2) / (√2)%R) by C_field.
	replace (Ci * (√ 2)%R * ((/ (√ 2)%R + cos β * Cexp θ_2 * / (√ 2)%R) * (/ (√ 2)%R + cos α * Cexp θ_1 * - / (√ 2)%R))) with (Ci * (1 - cos α * Cexp θ_1 ) * (1 + cos β * Cexp θ_2) / (√2)%R) by C_field.
	replace ((√ 2)%R * ((/ (√ 2)%R + cos β * Cexp θ_2 * - / (√ 2)%R) * (/ (√ 2)%R + cos α * Cexp θ_1 * - / (√ 2)%R))) with ((1 - cos α * Cexp θ_1 ) * (1 - cos β * Cexp θ_2) / (√2)%R) by C_field.
	rewrite Heqstep_3.
	rewrite <- Heqfinal_step.
	rewrite (zx_stack_spec _ _ _ _ (Z 1 1 (PI/4))).
	repeat rewrite (kron_mixed_product (⟦ Z 1 1 (PI/4) ⟧)(⟦ Z 1 1 (PI/4) ⟧)).
	rewrite step_3_N.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	autorewrite with scalar_move_db.
	rewrite Heqfinal_step at 1.
	rewrite Heqfinal_step at 1.
	rewrite Heqfinal_step at 1.
	rewrite Heqfinal_step at 1.
	rewrite ZX_semantic_equiv at 1.
	rewrite ZX_semantic_equiv at 1.
	rewrite ZX_semantic_equiv at 1.
	rewrite ZX_semantic_equiv at 1.
	unfold_dirac_spider.
	rewrite Cexp_0.
	Msimpl.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_assoc.
	autorewrite with scalar_move_db.
	repeat rewrite (kron_mixed_product ⟨+∣ ⟨+∣).
	repeat rewrite (kron_mixed_product ⟨-∣ ⟨-∣).
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	replace ((/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R) * / (√ 2)%R * ((/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R) * / (√ 2)%R)) with ((1 + Cexp (PI/4)) * (1 + Cexp (PI/4)) / 4) by (C_field_simplify; [lca | C_field]).
	replace ((/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R * - / (√ 2)%R) * (/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R * - / (√ 2)%R)) with ((1 - Cexp (PI/4)) * (1 - Cexp (PI/4))/4) by (C_field_simplify; [lca | C_field]).
	replace ((/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R) * / (√ 2)%R * ((/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R) * / (√ 2)%R)) with ((1 + Cexp (PI/4)) * (1 - Cexp (PI/4)) / 4) by (C_field_simplify; [lca | C_field]).
	replace ((/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R * - / (√ 2)%R) * (/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R * - / (√ 2)%R)) with ((1 + Cexp (PI/4)) * (1 - Cexp (PI/4)) / 4) by (C_field_simplify; [lca | C_field]).
	rewrite <- Mscale_plus_distr_r.
	restore_dims.
	rewrite xbasis_add_0.
	replace ((/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R) * / (√ 2)%R * ((/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R) * / (√ 2)%R)) with ((1 + Cexp (PI/4)) * (1 - Cexp (PI/4))/4) by (C_field_simplify; [lca | C_field]).
	replace (((/ (√ 2)%R * / (√ 2)%R +
Cexp (PI / 4) * / (√ 2)%R * - / (√ 2)%R) *
(/ (√ 2)%R * / (√ 2)%R +
Cexp (PI / 4) * - / (√ 2)%R * - / (√ 2)%R))) with ((1 + Cexp (PI/4)) * (1 - Cexp (PI/4))/4) by (C_field_simplify; [lca | C_field]).
	rewrite <- Mscale_plus_distr_r.
	restore_dims.
	rewrite xbasis_add_0.
	replace ((/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R) * / (√ 2)%R * ((/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R) * / (√ 2)%R)) with ((1 - Cexp (PI/4)) * (1 - Cexp (PI/4))/4) by (C_field_simplify; [lca | C_field]).
	replace ((/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R * - / (√ 2)%R) * (/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R * - / (√ 2)%R)) with ((1 + Cexp (PI/4)) * (1 + Cexp (PI/4))/4) by (C_field_simplify; [lca | C_field]).
	autorewrite with scalar_move_db.
	remember ((C1 + cos α * Cexp θ_1) * (C1 + cos β * Cexp θ_2) / (√ 2)%R) as v1.
	remember (Ci * (C1 + cos α * Cexp θ_1) * (C1 - cos β * Cexp θ_2) / (√ 2)%R) as v2.
	remember (Ci * (C1 - cos α * Cexp θ_1) * (C1 + cos β * Cexp θ_2) / (√ 2)%R) as v3.
	remember ((C1 - cos α * Cexp θ_1) * (C1 - cos β * Cexp θ_2) / (√ 2)%R) as v4.
	remember (C1 + Cexp (PI/4)) as g1.
	remember (C1 - Cexp (PI/4)) as g2.
	unfold xbasis_minus, xbasis_plus.
	repeat rewrite Mscale_plus_distr_r.
	repeat rewrite Mscale_assoc.
	replace (g1 * g2) with (1 - Cexp (PI/2)) by (subst; C_field_simplify; autorewrite with Cexp_db; C_field_simplify; [lca | C_field]).
	replace (1 - Cexp (PI/2)) with ((√2)%R*Cexp (-PI/4)) by (autorewrite with Cexp_db; C_field).
	replace (g1 * g1) with (1 + 2 * Cexp (PI/4) + Cexp (PI/2)) by (subst; autorewrite with Cexp_db; C_field_simplify; [lca | C_field]).
	replace (g2 * g2) with (1 - 2 * Cexp (PI/4) + Cexp (PI/2)) by (subst; autorewrite with Cexp_db; C_field_simplify; [lca | C_field]).
	clear Heqg1; clear g1; clear Heqg2; clear g2.
	remember ((C1 + C2 * Cexp (PI / 4) + Cexp (PI / 2)) / 4) as g1.
	remember (((C1 - C2 * Cexp (PI / 4) + Cexp (PI / 2)) / 4)) as g2.
	replace (v2 * ((√ 2)%R * Cexp (- PI / 4) / 4) * (√ 2)%R) with (v2 * Cexp (- PI / 4) / 2) by (C_field_simplify; [lca | C_field]).
	replace (v3 * ((√ 2)%R * Cexp (- PI / 4) / 4) * (√ 2)%R) with (v3 * Cexp (- PI / 4) / 2) by (C_field_simplify; [lca | C_field]).
	autorewrite with scalar_move_db.
	repeat rewrite <- (Mscale_assoc _ _ _ (-1)).
	repeat rewrite <- Mscale_plus_distr_r.
	rewrite zbasis_add_plus.
	rewrite zbasis_add_minus.
	autorewrite with scalar_move_db.
	replace (v1 * g1 * / (√ 2)%R * (√ 2)%R) with (v1 * g1) by C_field.
	replace (v1 * g2 * / (√ 2)%R * (√ 2)%R) with (v1 * g2) by C_field.
	replace (v2 * g2 * / (√ 2)%R * (√ 2)%R) with (v2 * g2) by C_field.
	replace (v4 * g2 * / (√ 2)%R * (√ 2)%R) with (v4 * g2) by C_field.
	replace (v4 * g1 * / (√ 2)%R * (√ 2)%R) with (v4 * g1) by C_field.
	replace (v1 * g1 .* ∣+⟩ .+ v1 * g2 .* ∣-⟩ .+ v2 * Cexp (- PI / 4) / C2 .* ∣0⟩ .+ v3 * Cexp (- PI / 4) / C2 .* ∣0⟩ .+ (v4 * g2 .* ∣+⟩ .+ v4 * g1 .* ∣-⟩)) with ((v1 * g1 + v4 * g2) .* ∣+⟩ .+ (v1 * g2 + v4 * g1) .* ∣-⟩ .+ v2 * Cexp (- PI / 4) / C2 .* ∣0⟩ .+ v3 * Cexp (- PI / 4) / C2 .* ∣0⟩) by lma.
	rewrite Mplus_assoc.
	rewrite <- Mscale_plus_distr_l.
	replace ((v2 * Cexp (- PI / 4) / C2 + v3 * Cexp (- PI / 4) / C2)) with ((v2 + v3) * Cexp (-PI/4) /2) by C_field.
	replace (v2 + v3) with (Ci * (√2)%R * (1 - (cos α)*Cexp(θ_1)*cos(β)*Cexp(θ_2))) by (subst; C_field_simplify; [lca | C_field]).
	replace (Ci * (√ 2)%R * (C1 - cos α * Cexp θ_1 * cos β * Cexp θ_2) * Cexp (- PI / 4) / C2) with (Ci * (C1 - cos α * Cexp θ_1 * cos β * Cexp θ_2) * Cexp (- PI / 4) / (√2)%R) by C_field.
	unfold xbasis_plus, xbasis_minus.
	replace ((v1 * g1 + v4 * g2) .* (/ (√ 2)%R .* (∣0⟩ .+ ∣1⟩)) .+ (v1 * g2 + v4 * g1) .* (/ (√ 2)%R .* (∣0⟩ .+ -1 .* ∣1⟩))) with ((((v1 * g1 + v4 * g2) + (v1 * g2 + v4 * g1))/(√2)%R) .* ∣0⟩ .+ (((v1 * g1 + v4 * g2) - (v1 * g2 + v4 * g1))/(√2)%R) .* ∣1⟩) by lma.
	replace (v1 * g1 + v4 * g2 + (v1 * g2 + v4 * g1)) with (v1 * (g1 + g2) + v4 * (g1 + g2)) by lca.
	replace (v1 * g1 + v4 * g2 - (v1 * g2 + v4 * g1)) with (v1 * (g1 - g2) + v4 * (g2 - g1)) by lca.
	replace (g1 + g2) with ((1 + Cexp (PI/2))/2) by (subst; lca).
	replace ((1 + Cexp (PI/2))/2) with (Cexp (PI/4)/(√2)%R) by (autorewrite with Cexp_db; C_field).
	replace ((v1 * (Cexp (PI / 4) / (√ 2)%R) + v4 * (Cexp (PI / 4) / (√ 2)%R)) / (√ 2)%R) with ((v1 + v4) * (Cexp (PI/4))/2) by C_field.
	replace (g1 - g2) with (Cexp (PI/4)) by (subst; autorewrite with Cexp_db; C_field_simplify; [lca | C_field]).
	replace (g2 - g1) with (- Cexp (PI/4)) by (subst; autorewrite with Cexp_db; C_field_simplify; [lca | C_field]).
	replace ((v1 * Cexp (PI / 4) + v4 * - Cexp (PI / 4))) with ((v1 - v4) * Cexp (PI/4)) by C_field.
	replace (v1 + v4) with ((√2)%R * (1 + cos α * Cexp θ_1 * cos β * Cexp θ_2)) by (subst; C_field_simplify; [lca | C_field]).
	replace (v1 - v4) with ((√2)%R * (cos α * Cexp θ_1 + cos β * Cexp θ_2)) by (subst; C_field_simplify; [lca | C_field]).
	replace (Ci * (C1 - cos α * Cexp θ_1 * cos β * Cexp θ_2) * Cexp (- PI / 4)) with ((C1 - cos α * Cexp θ_1 * cos β * Cexp θ_2) * Cexp (PI/4)) by (autorewrite with Cexp_db; C_field).
	rewrite Mplus_comm.
	rewrite <- Mplus_assoc.
	rewrite <- Mscale_plus_distr_l.
	replace ((√ 2)%R * (cos α * Cexp θ_1 + cos β * Cexp θ_2) * Cexp (PI / 4) / (√ 2)%R) with ((cos α * Cexp θ_1 + cos β * Cexp θ_2) * Cexp (PI / 4)) by C_field.
	(* Right hand side *)
	rewrite Heqstep_1_3.
	rewrite Heqfinal_step.
	rewrite <- zx_compose_spec.
	rewrite step_1_N.
	simpl.
	rewrite Heqstep_4.
	rewrite Heqfinal_step.
	rewrite (ZX_semantic_equiv _ _ (_ ⟷ _)).
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
	rewrite Heqfinal_step_2.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.
	repeat rewrite kron_mixed_product.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	autorewrite with scalar_move_db.
	Msimpl.
	apply Mplus_simplify; apply Mscale_simplify; try easy.
	- autorewrite with Cexp_db.
		C_field_simplify; [lca | C_field].
	- rewrite Cexp_minus.
		rewrite (Cmult_comm (cos α)).
		rewrite (Cmult_comm (cos β)).
		rewrite <- H.
		C_field.
Qed.

(* harny completeness result *)
Definition green_box (a : C) : Matrix 2 2 :=
	fun x y => 
		match (x, y) with 
		| (0, 0) => 1
		| (1, 1) => a
		| _      => 0
		end.
Definition red_box (a : C) : Matrix 2 2 :=
	hadamard × (green_box a) × hadamard.

Open Scope C.

Definition harny_z (α β γ : R) : C := cos (β / 2) * cos ((α + γ) / 2) + (Ci * (sin(β/2) * cos ((α - γ) / 2))).

Definition harny_z_1 (α β γ : R) : C := cos (β / 2) * sin ((α + γ) / 2) + (Ci * (sin(β/2) * sin ((α - γ) / 2))).

Definition harny_τ (l1 l2 l3 : C) : C := (1 - l2) * (l1 + l3) + (1 + l2) * (1 + l1 * l3).

Definition harny_u (l1 l2 l3 : C) : C := (1 + l2) * (l1 * l3 - 1).

Definition harny_s (l1 l2 l3 : C) : C := (1 - l2) * (l1 + l3) - (1 + l2) * (1 + l1 * l3).

Definition harny_v (l1 l2 l3 : C) := (1 - l2) * (l1 - l3).

Definition harny_t (l1 l2 l3 : C) := 
	let τ := harny_τ l1 l2 l3 in 
	let u := harny_u l1 l2 l3 in  
	let v := harny_v l1 l2 l3 in  
	τ * (u * u - v * v).

Definition harny_σ1 (l1 l2 l3 : C) : C := 
	let u := harny_u l1 l2 l3 in
	let v := harny_v l1 l2 l3 in
	let s := harny_s l1 l2 l3 in
	let t := harny_t l1 l2 l3 in
	Ci * (-(u + v) * √(s / t)).

Definition harny_σ2 (l1 l2 l3 : C) : C := 
	let τ := harny_τ l1 l2 l3 in 
	let u := harny_u l1 l2 l3 in
	let v := harny_v l1 l2 l3 in
	let s := harny_s l1 l2 l3 in
	let t := harny_t l1 l2 l3 in
	(C1 * τ + Ci * √(t / s)) 
	/ (C1 * τ + -Ci * √(t / s)).

Definition harny_σ3 (l1 l2 l3 : C) : C := 
	let u := harny_u l1 l2 l3 in
	let v := harny_v l1 l2 l3 in
	let s := harny_s l1 l2 l3 in
	let t := harny_t l1 l2 l3 in
	Ci * (-(u - v) * √(s / t)).

Definition harny_k (l1 l2 l3 : C) : C := 
	let s := harny_s l1 l2 l3 in 
	let τ := harny_τ l1 l2 l3 in 
	let t := harny_t l1 l2 l3 in 
	(8 * (s * τ + √((- s) * t)) / (s * τ * τ + t)).

#[export] Hint Unfold harny_k harny_s harny_t harny_u harny_v harny_z harny_z_1 harny_τ : harny_db.
#[export] Hint Unfold harny_σ1 harny_σ2 harny_σ3 : harny_σ_db.

Definition create_m (mx my mz mw : C) : (Matrix 2 2)
	:= fun (x y : nat) => match x, y with
											| 0, 0 => mx
											| 0, 1 => my
											| 1, 0 => mz
											| 1, 1 => mw
											| _, _ => C0
end.

Lemma harny_simpl : forall l1 l2 l3,
	let σ1 := harny_σ1 l1 l2 l3 in
	let σ2 := harny_σ2 l1 l2 l3 in
	let σ3 := harny_σ3 l1 l2 l3 in
	let MX := ((C1 + σ3) * (C1 + σ1) + (C1 - σ3) * σ2 * (C1 - σ1)) in
	let MY := ((C1 + σ3) * (C1 - σ1) + (C1 - σ3) * σ2 * (C1 + σ1)) in
	let MZ := ((C1 - σ3) * (C1 + σ1) + (C1 + σ3) * σ2 * (C1 - σ1)) in
	let MW := ((C1 - σ3) * (C1 - σ1) + (C1 + σ3) * σ2 * (C1 + σ1)) in 
	C2 * C2 .* (red_box σ3 × green_box σ2 × red_box σ1) = create_m MX MY MZ MW.
Proof.
	intros.
	subst MX MY MZ MW.
	unfold red_box, green_box.
	(* Broken by addition of Csqrt and moving harny scalars to C, see old commit. *)
Admitted.


Lemma harny_general_phases_color_swap : forall l1 l2 l3 : C,
	let k := harny_k l1 l2 l3 in
	let σ1 := harny_σ1 l1 l2 l3 in
	let σ2 := harny_σ2 l1 l2 l3 in
	let σ3 := harny_σ3 l1 l2 l3 in
	k .* (green_box l3 × red_box l2 × green_box l1) = (red_box σ3 × green_box σ2 × red_box σ1).
Proof.
	intros.
	pose proof (harny_simpl l1 l2 l3).
	rewrite Mscale_inv in H.
	subst σ1 σ2 σ3.
	rewrite H.
	subst k.
	unfold green_box, red_box.
Admitted.

Transparent Z_semantics.

Lemma z_spider_to_green_box : forall α,
 ⟦ Z 1 1 α ⟧ = green_box (Cexp α).
Proof.
	intros.
	simpl.
	unfold Z_semantics, green_box.
	solve_matrix.
Qed.

Transparent X_semantics.

Lemma x_spider_to_red_box : forall α,
 ⟦ X 1 1 α ⟧ = red_box (Cexp α).
Proof.
	intros.
	simpl.
	unfold X_semantics.
	fold (⟦ Z 1 1 α ⟧).
	rewrite z_spider_to_green_box.
	unfold red_box.
	simpl.
	rewrite kron_1_l.
	easy.
	auto with wf_db.
Qed.

(* Prior harny rule can be used to prove this. *)
Lemma harny_completeness : forall α β γ, 
	Z 1 1 α ⟷ X 1 1 β ⟷ Z 1 1 γ ∝
	X 1 1 (get_arg (harny_z α β γ) + get_arg (harny_z_1 α β γ)) ⟷ 
	Z 1 1 (2 * get_arg ( Cmod (harny_z α β γ / harny_z_1 α β γ) + Ci)) ⟷
	X 1 1 (get_arg (harny_z α β γ) + get_arg (harny_z_1 α β γ)).
Proof.
	intros.
	remember (harny_z α β γ) as z.
	remember (harny_z_1 α β γ) as z_1.
	remember (harny_k (Cexp α) (Cexp β) (Cexp γ)) as k.
	prop_exists_nonzero (1%R / k).
	simpl.
	fold (⟦ Z 1 1 α ⟧).
	fold (⟦ X 1 1 β ⟧).
	fold (⟦ Z 1 1 γ ⟧).
	fold (⟦ X 1 1 (get_arg z + get_arg z_1 ) ⟧).
	fold (⟦ Z 1 1 (2 * get_arg ( Cmod (z / z_1) + Ci)) ⟧).
	fold (⟦ X 1 1 (get_arg z - get_arg z_1) ⟧).
	repeat rewrite z_spider_to_green_box.
	repeat rewrite x_spider_to_red_box.
	assert (H : forall a {n m} (U V : Matrix n m), a <> C0 -> a .* U = V -> U = (C1 / a) .* V).
	{ 
		intros.
		rewrite <- H0.
		rewrite Mscale_assoc.
		replace ((C1 / a) * a) with (C1).
		lma.
		C_field_simplify.
		easy.
		easy.
	}
	apply H.
	- rewrite Heqk.
		autounfold with harny_db.
		C_field_simplify.
		admit.
	- rewrite Heqk.
		repeat rewrite <- Mmult_assoc.
		rewrite harny_general_phases_color_swap.
Admitted.
