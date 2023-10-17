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
	/(√2)%R .* ∣0⟩⟨0∣ .+ 
	Cexp(α) / (√2)%R .* ∣0⟩⟨1∣ .+ 
	Cexp(α) / (√2)%R .* ∣1⟩⟨0∣ .+ 
	/(√2)%R .* ∣1⟩⟨1∣.
Proof.
	intros.
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
	Cexp(α) / (√2)%R .* ∣0⟩⟨0∣ .+ 
	/ (√2)%R .* ∣0⟩⟨1∣ .+ 
	/ (√2)%R .* ∣1⟩⟨0∣ .+ 
	Cexp(α) / (√2)%R .* ∣1⟩⟨1∣.
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
	⟦ (Z 1 2 α ↕ Z 1 2 β) ⟷ (— ↕ X 2 3 γ ↕ —) ⟧ = 
	∣0⟩⟨0∣.
Proof.
Admitted.

Lemma c_step_3 : forall γ,
	⟦ (Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 γ) ⟧ = 
	(1 .* ∣0⟩⊗∣0⟩ × ⟨0∣⊗⟨0∣) .+
	(1 .* ∣0⟩⊗∣1⟩ × ⟨0∣⊗⟨1∣) .+
	(1 .* ∣1⟩⊗∣1⟩ × ⟨1∣⊗⟨0∣) .+
	(1 .* ∣1⟩⊗∣0⟩ × (⟨1∣⊗⟨1∣)).
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
	repeat rewrite <- kron_mixed_product.
Admitted.

Lemma cnot_braket :
	⟦ (Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 0) ⟧ = 
	(1 .* ∣0⟩⊗∣0⟩ × ⟨0∣⊗⟨0∣) .+
	(1 .* ∣0⟩⊗∣1⟩ × ⟨0∣⊗⟨1∣) .+
	(1 .* ∣1⟩⊗∣1⟩ × ⟨1∣⊗⟨0∣) .+
	(1 .* ∣1⟩⊗∣0⟩ × (⟨1∣⊗⟨1∣)).
Proof.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	autorewrite with Cexp_db.
	Msimpl.
	repeat rewrite kron_plus_distr_l.
	repeat rewrite kron_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite kron_id_dist_l by auto with wf_db.
	repeat rewrite kron_id_dist_r by auto with wf_db.
	repeat rewrite kron_assoc by auto with wf_db.
	repeat rewrite Mmult_assoc.
	rewrite <- (Mmult_assoc _ (∣0⟩ ⊗ (∣0⟩ ⊗ (I 2)))).
	rewrite <- (Mmult_assoc _ (∣1⟩ ⊗ (∣1⟩ ⊗ (I 2)))).
	Msimpl.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	rewrite <- (kron_plus_distr_l _ _ _ _ ∣0⟩⟨0∣).
	autorewrite with scalar_move_db.
	rewrite <- (Mscale_kron_dist_r _ _ _ _ (- / (√2)%R)).
	rewrite <- (Mscale_kron_dist_r _ _ _ _ (/ (√2)%R) (∣1⟩⟨1∣)).
	rewrite <- (kron_plus_distr_l _ _ _ _ ∣1⟩⟨1∣).
	autorewrite with scalar_move_db.


(* @nocheck name *)
(* Conventional name *)
Lemma completeness_C : forall α β γ,
	(Z 1 2 0) ⟷ 
	(X 1 2 0 ↕ X 1 2 PI) ⟷ 
	(Z 1 0 α ↕ Z 1 2 α ↕ Z 1 2 β ↕ Z 1 0 β) ⟷ 
	(X 1 2 (- γ) ↕ X 2 1 γ ↕ —) ⟷ (— ↕ Z 2 1 0 ↕ —) ∝ 
		(Z 1 2 0) ⟷ 
		(X 1 2 PI ↕ X 1 2 0) ⟷ 
		(Z 1 0 β ↕ Z 1 2 β ↕ Z 1 2 α ↕ Z 1 0 α) ⟷ 
		(— ↕ X 2 1 (- γ) ↕ X 1 2 γ) ⟷ 
		(— ↕ Z 2 1 0 ↕ —).
Proof. (* solve matrix takes forever *)
Abort.

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
	rewrite ket0_equiv.
	rewrite ket1_equiv.
	restore_dims.
	rewrite Z0_spec.
	rewrite X0_spec.
	rewrite Z1_spec.
	rewrite X1_spec.
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
	(* remember (Cexp (PI / 2) / (√ 2)%R) as cpot.
	remember ((Cexp α + Cexp (- α)) / (√ 2)%R * Cexp θ_1) as cat1.
	remember ((Cexp β + Cexp (- β)) / (√ 2)%R * Cexp θ_2) as bat2. *)
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
	remember (/ (√ 2)%R * (((√ 2)%R * / (√ 2)%R + (Cexp β + Cexp (- β)) / (√ 2)%R * Cexp θ_2 * - / (√ 2)%R) * ((√ 2)%R * / (√ 2)%R + (Cexp α + Cexp (- α)) / (√ 2)%R * Cexp θ_1 * - / (√ 2)%R))) as v4.
	remember (Cexp (PI / 2) / (√ 2)%R * (((√ 2)%R + (Cexp β + Cexp (- β)) / (√ 2)%R * Cexp θ_2) * / (√ 2)%R) * ((√ 2)%R * / (√ 2)%R + (Cexp α + Cexp (- α)) / (√ 2)%R * Cexp θ_1 * - / (√ 2)%R)) as v3.
	remember (Cexp (PI / 2) / (√ 2)%R * (((√ 2)%R + (Cexp α + Cexp (- α)) / (√ 2)%R * Cexp θ_1) * / (√ 2)%R) * ((√ 2)%R * / (√ 2)%R + (Cexp β + Cexp (- β)) / (√ 2)%R * Cexp θ_2 * - / (√ 2)%R)) as v2.
	remember (/ (√ 2)%R * (((√ 2)%R + (Cexp β + Cexp (- β)) / (√ 2)%R * Cexp θ_2) * / (√ 2)%R * ((√ 2)%R + (Cexp α + Cexp (- α)) / (√ 2)%R * Cexp θ_1) * / (√ 2)%R)) as v1.
	rewrite Heqstep_3.
	rewrite <- Heqfinal_step.
	rewrite <- (Mscale_mult_dist_r _ _ _ v1), <- (Mscale_mult_dist_r _ _ _ v2), <- (Mscale_mult_dist_r _ _ _ v3), <- (Mscale_mult_dist_r _ _ _ v4).
	repeat rewrite <- Mmult_plus_distr_l. 
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
	remember (((/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R * - / (√ 2)%R) * (/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R * - / (√ 2)%R))) as g1.
	remember (((/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R * - / (√ 2)%R) * (/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R * - / (√ 2)%R))) as g2.
	remember (((/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R * - / (√ 2)%R) * (/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R * - / (√ 2)%R))) as g3.
	remember (((/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R * - / (√ 2)%R) * (/ (√ 2)%R * / (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R * - / (√ 2)%R))) as g4.
	remember (((/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R) * / (√ 2)%R * ((/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R) * / (√ 2)%R))) as k1.
	remember (((/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R) * / (√ 2)%R * ((/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R) * / (√ 2)%R))) as k2.
remember (((/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R) * / (√ 2)%R * ((/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R) * / (√ 2)%R))) as k3.
remember (((/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R) * / (√ 2)%R * ((/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R) * / (√ 2)%R))) as k4.
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
	rewrite 2 Mscale_plus_distr_r.
	rewrite Mscale_assoc.
	replace ((v1 * k1 + v2 * k2 + v3 * k3 + v4 * k4) * / (√ 2)%R .* ∣0⟩ .+ (v1 * k1 + v2 * k2 + v3 * k3 + v4 * k4) * / (√ 2)%R .* ∣1⟩ .+ ((v1 * g1 + v2 * g2 + v3 * g3 + v4 * g4) * / (√ 2)%R .* ∣0⟩ .+ (v1 * g1 + v2 * g2 + v3 * g3 + v4 * g4) * / (√ 2)%R * -1 .* ∣1⟩)) with (((v1 * k1 + v2 * k2 + v3 * k3 + v4 * k4) + (v1 * g1 + v2 * g2 + v3 * g3 + v4 * g4))/(√2)%R.* ∣0⟩ .+ ((v1 * k1 + v2 * k2 + v3 * k3 + v4 * k4) - (v1 * g1 + v2 * g2 + v3 * g3 + v4 * g4))/(√2)%R .* ∣1⟩) by lma.
	apply Mplus_simplify.
Admitted.
	

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
