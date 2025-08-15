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

Import ZXStateRules.

Local Open Scope matrix_scope.

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_C : forall (α β γ : R),
	(Z 1 2 0) ⟷ (((Z 0 1 β ↕ —) ⟷ X 2 1 PI) ↕ ((Z 0 1 α ↕ —) ⟷ X 2 1 0)) ⟷ ((Z 1 2 β ↕ Z 1 2 α) ⟷ (— ↕ X 2 1 γ ↕ —)) ⟷ (((— ↕ Z 1 2 0) ⟷ (X 2 1 (-γ) ↕ —)) ↕ —)
	∝= 
	(Z 1 2 0) ⟷ (((Z 0 1 α ↕ —) ⟷ X 2 1 0) ↕ ((Z 0 1 β ↕ —) ⟷ X 2 1 PI)) ⟷ ((Z 1 2 α ↕ Z 1 2 β) ⟷ (— ↕ X 2 1 (-γ) ↕ —)) ⟷ (— ↕ ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 γ))).
Proof. (* solve matrix takes forever *)intros.
	apply prop_eq_by_eq_on_state_b_1_n.
	intros b.
	rewrite <- 9 compose_assoc.
	rewrite Z_1_2_state_b.
	rewrite Cexp_0, Tauto.if_same, zx_scale_1_l.
	rewrite <- 2(@stack_compose_distr 0 1 1 0 1 1).
	(* Search "X" "wrap". *)
	rewrite <- 2 compose_assoc.
	rewrite wire_to_n_wire, <- 2 push_out_top. 
	rewrite 2 (@X_push_over_top_left 1 1 1 0).
	rewrite 2 X_1_n_state_b.
	cbn -[n_wire].
	distribute_zxscale.
	rewrite 6 zx_scale_compose_distr_l.
	apply zx_scale_simplify_eq_r.
	rewrite completeness_C_step1, Rplus_0_r, completeness_C_step1'.
	rewrite <- 2 (@stack_compose_distr 0 1 2 0 1 2).

	rewrite 2 Z_0_1_decomp, 2 (compose_plus_distr_l state_0).
	rewrite <- (negb_if _ NOT —).
	distribute_zxscale.
	rewrite 2 if_b_not_state_0, 2 if_b_not_state_1, 
		negb_involutive.
	rewrite 2 (compose_plus_distr_l (state_b _)).
	distribute_zxscale.
	rewrite 4 Z_1_2_state_b.
	rewrite 2 zx_scale_assoc.
	rewrite 2 stack_plus_distr_l, 4 zx_scale_stack_distr_l,
		4 stack_plus_distr_r, 8 zx_scale_stack_distr_r.
	rewrite 2 (compose_plus_distr_l _ _ (n_wire 1 ↕ X 2 1 _ ↕ n_wire 1)), 
		4 zx_scale_compose_distr_l, 
		4 (compose_plus_distr_l _ _ (n_wire 1 ↕ X 2 1 _ ↕ n_wire 1)).
	rewrite 8 completeness_C_step2.
	rewrite 2 (compose_plus_distr_l ),
		4 zx_scale_compose_distr_l, 
		4 (compose_plus_distr_l ).
	rewrite xorb_nb_b, xorb_b_nb, 2 xorb_nilpotent. 
	rewrite 4 completeness_C_step3.
	rewrite 4 completeness_C_step3'.
	rewrite 4 zx_scale_plus_distr_r, 8 zx_scale_assoc.
	rewrite 8 X_0_1_decomp.
	rewrite 8 (if_dist R C _ Cexp).
	unfold Rminus.
	rewrite 3 Cexp_add, Cexp_PI', <- 2 Copp_mult_distr_r, 2 Cmult_1_r, 
		<- Copp_mult_distr_l, Cmult_1_l.
	rewrite Cexp_neg.
	unfold Cminus.
	rewrite Copp_involutive.
	pose proof (Cexp_nonzero γ).
	(* assert (Hrw : forall c, c / C2 / (√2 * C2) *)

	prep_matrix_equivalence.
	rewrite 6 zx_plus_semantics, 8 zx_scale_semantics.
	cbn [ZX_semantics].
	rewrite 8 zx_plus_semantics, 16 zx_scale_semantics.
	cbn [ZX_semantics].
	rewrite 8 zx_plus_semantics, 16 zx_scale_semantics.
	rewrite state_0_semantics, state_1_semantics, 
		2 state_b_semantics.
	unfold Mplus, scale, kron;
	by_cell;
	destruct b; cbn;
	C_field.
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
	rewrite Mscale_mult_dist_l, Mscale_mult_dist_r.
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
	Local Open Scope matrix_scope.
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