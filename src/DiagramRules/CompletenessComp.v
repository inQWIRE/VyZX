Require Import CoreData.
From QuantumLib Require Import Polar.
Import Complex.

Require Import CoreRules.

Local Open Scope matrix_scope.

(** Some computational proofs used to prove the completeness results *)


(* @nocheck name *)
(* Conventional name *)
Lemma completeness_C_step1 β (b : bool) : 
	X 0 2 (if b then (PI + PI)%R else PI)
		⟷ (Z 1 0 β ↕ n_wire 1) ∝=
	Z 0 1 β ⟷ if b then — else NOT.
Proof.
	destruct b.
	- rewrite X_eq_2_PI, <- cap_X by lra.
		rewrite cup_pullthrough_top, n_cap_0_empty, compose_empty_l, stack_empty_l, 
			nwire_removal_r, wire_removal_r.
		reflexivity.
	- rewrite X_0_2_PI_to_cup_not, compose_assoc, wire_to_n_wire,
			<- (@stack_split_antidiag 1 0 1 1), stack_split_diag.
		rewrite <- compose_assoc, cup_pullthrough_top, n_cap_0_empty, 
			compose_empty_l, stack_empty_l, nwire_removal_r, stack_empty_l.
		reflexivity.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_C_step1' β (b : bool) : 
	X 0 2 (if b then PI else 0)
		⟷ (Z 1 0 β ↕ n_wire 1) ∝=
	Z 0 1 β ⟷ if b then NOT else —.
Proof.
	generalize (completeness_C_step1 β (negb b)).
	destruct b; cbn -[n_wire].
	- easy.
	- intros <-.
		symmetry.
		now rewrite X_eq_2_PI by lra.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_C_step2 b0 b1 b2 b3 γ c : 
	c .* (state_b b0 ↕ state_b b1 ↕ (state_b b2 ↕ state_b b3)) ⟷
	(n_wire 1 ↕ X 2 1 γ ↕ n_wire 1) ∝=
	c/C2 .* (state_b b0 ↕ X 0 1 (if b1 ⊕ b2 then (γ + PI) else γ) ↕ state_b b3).
Proof.
	distribute_zxscale.
	rewrite stack_assoc_back_fwd, cast_id.
	rewrite <- (@stack_compose_distr 0 3 2 0 1 1).
	rewrite nwire_removal_r.
	rewrite stack_assoc_fwd, cast_id.
	rewrite <- (@stack_compose_distr 0 1 1 0 2 1).
	rewrite nwire_removal_r.
	rewrite X_2_1_states_b.
	rewrite zx_scale_stack_distr_r, zx_scale_stack_distr_l, zx_scale_assoc.
	reflexivity.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_C_step3 b0 b1 α c γ : 
	(c .* (state_b b0 ↕ X 0 1 α ↕ state_b b1))
		⟷ (n_wire 1 ↕ Z 1 2 0 ⟷ (X 2 1 (- γ) ↕ n_wire 1) ↕ n_wire 1) ∝=
	c / (√ 2 * C2) .* ((
	(C1 + Cexp α) .* (X 0 1 (if b0 then (PI - γ)%R else (- γ)%R) ↕ state_0)
	.+ (C1 - Cexp α) .* (X 0 1 (if b0 then (- γ)%R else (PI - γ)%R) ↕ state_1)
	) ↕ state_b b1).
Proof.
	distribute_zxscale.
	rewrite <- stack_compose_distr.
	rewrite <- 2 zx_scale_stack_distr_l.
	apply stack_simplify_eq; [|now rewrite nwire_removal_r].
	rewrite <- compose_assoc.
	rewrite <- stack_compose_distr, nwire_removal_r.
	rewrite X_0_1_decomp, compose_plus_distr_l.
	distribute_zxscale.
	rewrite Z_1_2_state_0, Z_1_2_state_1, Cexp_0, zx_scale_1_l.
	rewrite stack_plus_distr_r, compose_plus_distr_l.
	distribute_zxscale.
	rewrite 2 (@stack_assoc_back_fwd 0 0 0 1 1 1), 2 cast_id.
	rewrite <- 2 (@stack_compose_distr 0 2 1 0 1 1), 2 nwire_removal_r.
	rewrite state_0_to_b, state_1_to_b.
	rewrite 2 X_2_1_states_b.
	rewrite xorb_false_r, xorb_true_r.
	distribute_zxscale.
	rewrite 2 zx_scale_plus_distr_r.
	distribute_zxscale.
	replace (-γ + PI)%R with (PI - γ)%R by lra.
	rewrite negb_if.
	apply zx_plus_mor; 
	apply zx_scale_simplify_eq_l; C_field.
Qed.


(* @nocheck name *)
(* Conventional name *)
Lemma completeness_C_step3' b0 b1 α c γ : 
	(c .* (state_b b0 ↕ X 0 1 α ↕ state_b b1))
		⟷ (n_wire 1 ↕ (Z 1 2 0 ↕ n_wire 1 ⟷ (n_wire 1 ↕ X 2 1 γ))) ∝=
	c / (√ 2 * C2) .* (state_b b0 ↕ (
	(C1 + Cexp α) .* (state_0 ↕ X 0 1 (if b1 then (γ + PI)%R else γ))
	.+ (C1 - Cexp α) .* (state_1 ↕ X 0 1 (if b1 then γ else (γ + PI)%R))
	)).
Proof.
	distribute_zxscale.
	rewrite stack_assoc_fwd, cast_id.
	rewrite <- (@stack_compose_distr 0 1 1 0 2 _).
	rewrite <- 4 zx_scale_stack_distr_r.
	apply stack_simplify_eq; [now rewrite nwire_removal_r|].

	rewrite <- compose_assoc.
	rewrite <- (@stack_compose_distr 0 1 2 0 1 1), nwire_removal_r.
	rewrite X_0_1_decomp, compose_plus_distr_l.
	distribute_zxscale.
	rewrite Z_1_2_state_0, Z_1_2_state_1, Cexp_0, zx_scale_1_l.
	rewrite stack_plus_distr_l, compose_plus_distr_l.
	distribute_zxscale.
	rewrite 2 (@stack_assoc_fwd 0 0 0 1 1 1), 2 cast_id, 
		2 zx_scale_compose_distr_l.
	rewrite <- 2 (@stack_compose_distr 0 1 1 0 2 1), 2 nwire_removal_r.
	rewrite state_0_to_b, state_1_to_b.
	rewrite 2 X_2_1_states_b.
	rewrite xorb_false_l, xorb_true_l.
	distribute_zxscale.
	rewrite 2 zx_scale_plus_distr_r.
	distribute_zxscale.
	rewrite 2zx_scale_assoc.
	replace (-γ + PI)%R with (PI - γ)%R by lra.
	rewrite negb_if.
	apply zx_plus_mor; 
	apply zx_scale_simplify_eq_l; C_field.
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
