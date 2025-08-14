Require Import CoreData.
From QuantumLib Require Import Polar.
Require Import CoreRules.
Require Import CompletenessComp.

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_SUP : forall α, 
	((Z 0 1 α) ↕ (Z 0 1 (α + PI))) ⟷ (X 2 1 0) ∝= Z 0 2 (2 *α + PI) ⟷ X 2 1 0.
Proof.
	intros.
	hnf.
	cbn [ZX_semantics Nat.add].
	rewrite X_2_1_0_semantics.
	compute_matrix (Z_semantics 0 1 α ⊗ Z_semantics 0 1 (α + PI)).
	compute_matrix (Z_semantics 0 2 (2 * α + PI)).
	rewrite <- Cexp_add, <- Rplus_assoc, 3!Cexp_plus_PI, <- double.
	prep_matrix_equivalence.
	by_cell; lca.
Qed.  

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_E : Z 0 1 (PI / 4) ⟷ X 1 0 (- PI / 4) ∝= ⦰.
Proof.
	unfold proportional_by_1.
	prep_matrix_equivalence.
	by_cell.
	unfold X_semantics; simpl; autounfold with U_db; simpl.
	C_field.
	rewrite Rdiv_opp_l.
	rewrite Cexp_neg.
	rewrite Cexp_PI4.
	C_field.
	- lca.
	- split; [nonzero|].
		intros H%(f_equal fst).
		simpl in H.
		lra.
Qed.
	

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_E : Z 0 1 (PI / 4) ⟷ X 1 0 (- PI / 4) ∝= ⦰.
Proof.
	unfold proportional_by_1.
	prep_matrix_equivalence.
	by_cell.
	unfold X_semantics; simpl; autounfold with U_db; simpl.
	C_field.
	rewrite Rdiv_opp_l.
	rewrite Cexp_neg.
	rewrite Cexp_PI4.
	C_field.
	- lca.
	- split; [nonzero|].
		intros H%(f_equal fst).
		simpl in H.
		lra.
Qed.
	

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_C : forall (α β γ : R),
	(Z 1 2 0) ⟷ (((Z 0 1 β ↕ —) ⟷ X 2 1 PI) ↕ ((Z 0 1 α ↕ —) ⟷ X 2 1 0)) ⟷ ((Z 1 2 β ↕ Z 1 2 α) ⟷ (— ↕ X 2 1 γ ↕ —)) ⟷ (((— ↕ Z 1 2 0) ⟷ (X 2 1 (-γ) ↕ —)) ↕ —)
	∝= 
	(Z 1 2 0) ⟷ (((Z 0 1 α ↕ —) ⟷ X 2 1 0) ↕ ((Z 0 1 β ↕ —) ⟷ X 2 1 PI)) ⟷ ((Z 1 2 α ↕ Z 1 2 β) ⟷ (— ↕ X 2 1 (-γ) ↕ —)) ⟷ (— ↕ ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 γ))).
Proof. (* solve matrix takes forever *)
	intros.
	remember ((Z 0 1 α ↕ —) ⟷ X 2 1 0) as cs1.
	remember ((Z 0 1 β ↕ —) ⟷ X 2 1 PI) as cs1pi.
	remember (((Z 1 2 β ↕ Z 1 2 α) ⟷ (— ↕ X 2 1 γ ↕ —))) as cs2.	
	remember (((Z 1 2 α ↕ Z 1 2 β) ⟷ (— ↕ X 2 1 (-γ) ↕ —))) as cs2n.
	remember ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 γ)) as cs3.
	remember (((— ↕ Z 1 2 0) ⟷ (X 2 1 (-γ) ↕ —))) as cs3f.
	unfold proportional_by_1.
	simpl.
	rewrite Heqcs1.
	rewrite Heqcs1pi.
	clear cs1 cs1pi Heqcs1 Heqcs1pi.
	rewrite c_step_1, c_step_1_pi.
	autorewrite with scalar_move_db.
	(* rewrite Cmult_1_l. *)
	apply Mscale_simplify; [| easy].
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
	◁ ⟷ Z 1 1 PI ⟷ ▷ ∝= ▷ ⟷ X 1 1 PI.
Proof. 
	unfold proportional_by_1.
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
Lemma completeness_N : forall α β θ_1 θ_2 γ θ_3,
	2 * Cexp (θ_3) * cos(γ) = Cexp (θ_1) * cos(α) + Cexp (θ_2) * cos(β) ->
	(((Z 0 1 α ↕ Z 0 1 (-α) ⟷ X 2 1 0) ⟷ Z 1 1 θ_1) ↕ ((Z 0 1 β ↕ Z 0 1 (-β) ⟷ X 2 1 0) ⟷ Z 1 1 θ_2)) ⟷ ((— ↕ (X 0 1 (PI/2) ⟷ Z 1 2 0) ↕ —) ⟷ (X 2 1 0 ↕ X 2 1 0)) ⟷ (Z 1 1 (PI/4) ↕ Z 1 1 (PI/4)) ⟷ X 2 1 0 ∝= 
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
	unfold proportional_by_1.
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
	match goal with |- _ = ?A => set (temp := A) end.
	rewrite Heqfinal_step.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	subst temp.
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
	rewrite Mplus_plus_minus.
	replace ((/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R) * / (√ 2)%R * ((/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R) * / (√ 2)%R)) with ((1 + Cexp (PI/4)) * (1 - Cexp (PI/4))/4) by (C_field_simplify; [lca | C_field]).
	replace (((/ (√ 2)%R * / (√ 2)%R +
Cexp (PI / 4) * / (√ 2)%R * - / (√ 2)%R) *
(/ (√ 2)%R * / (√ 2)%R +
Cexp (PI / 4) * - / (√ 2)%R * - / (√ 2)%R))) with ((1 + Cexp (PI/4)) * (1 - Cexp (PI/4))/4) by (C_field_simplify; [lca | C_field]).
	rewrite <- Mscale_plus_distr_r.
	restore_dims.
	rewrite Mplus_plus_minus.
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
	rewrite Mplus_0_1.
	rewrite Mplus_0_1_opp.
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