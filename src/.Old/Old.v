
Lemma Z_2_1_through_cap : forall α, 
	𝒵 2 1 α ↕ — ⟷ ⊃ ∝ (— ↕ — ↕ 𝒵 1 2 α) ⟷  (— ↕ ⊃ ↕ —) ⟷ ⊃.
Proof. solve_prop 1. Qed.

Lemma Grow_Z_Left_1_2 : forall {n m} α,
	𝒵 (S n) (S m) α ∝ 
	(𝒵 1 2 0 ↕ nWire n) ⟷ (— ↕ 𝒵 (S n) m α).
Proof.
	intros.
	rewrite Z_WrapOver_Top_Right.
	rewrite Grow_Z_Left.
	rewrite (nstack1_split 1 n).
	fold (nWire n). fold (nWire 1).
	rewrite stack_wire_distribute_l.
	rewrite <- ZX_Compose_assoc.
	rewrite (ZX_Stack_assoc_back ⊂ (nWire 1) (nWire n)).
	rewrite (ZX_Stack_assoc_back — (𝒵 2 1 0) (nWire n)).
	simpl_casts.
	rewrite <- (ZX_Stack_Compose_distr (⊂ ↕ nWire 1) (— ↕ 𝒵 2 1 0) (nWire n) (nWire n)).
	rewrite <- Z_WrapOver_Top_Right.
	cleanup_zx.
	easy.
Qed.

Lemma Grow_Z_Right_2_1 : forall {n m} α,
	𝒵 (S n) (S m) α ∝ 
	(— ↕ 𝒵 n (S m) α) ⟷ (𝒵 2 1 0 ↕ nWire m).
Proof.
	intros.
	apply transpose_diagrams.
	simpl.
	rewrite nstack1_transpose.
	rewrite transpose_wire.
	apply Grow_Z_Left_1_2.
Qed.

Lemma Grow_Z_Left_Bot_2_1 : forall {n m} α,
	𝒵 (n + 2) m α ∝ 
	(nWire n ↕ 𝒵 2 1 0) ⟷ (𝒵 (n + 1) m α).
Proof.
	intros.
	induction n.
	- simpl.
		cleanup_zx.
		rewrite Z_spider_1_1_fusion.
		rewrite Rplus_0_l.
		reflexivity.
	- destruct n.
		+ simpl.
			cleanup_zx.
			simpl_casts.
			rewrite (Z_WrapOver_Top_Left 1 m).
			rewrite <- ZX_Compose_assoc.
			rewrite <- stack_wire_distribute_l.
			rewrite Z_spider_1_1_fusion.
			rewrite Rplus_0_l.
			rewrite <- Z_WrapOver_Top_Left.
			easy.
		+ rewrite (Grow_Z_Left (n + 1)).
			rewrite <- ZX_Compose_assoc.
			rewrite (nstack1_split 2 n).
			rewrite (ZX_Stack_assoc (nWire 2) (nWire n) (𝒵 2 1 0)).
			simpl_casts.
			rewrite <- (ZX_Stack_Compose_distr (nWire 2) _ (nWire n ↕ (𝒵 2 1 0)) _).
			cleanup_zx.
			rewrite <- nwire_stack_compose_botleft.
			rewrite ZX_Compose_assoc.
			rewrite ZX_Stack_assoc_back.
			simpl_casts.
			rewrite <- nstack1_split.
			rewrite <- IHn.
			rewrite <- (Grow_Z_Left (n + 2)).
			simpl.
			easy.
Qed.

Lemma Grow_Z_Right_Bot_1_2 : forall {n m} α,
	𝒵 n (m + 2) α ∝ 
	(𝒵 n (m + 1) α) ⟷ (nWire m ↕ 𝒵 1 2 0).
Proof.
	intros.
	apply transpose_diagrams.
	simpl.
	rewrite nstack1_transpose.
	rewrite transpose_wire.
	apply Grow_Z_Left_Bot_2_1.
Qed.

Lemma Grow_Z_Left_Bot_dim : forall n,
	(n + 1 + 1 = n + 2)%nat.
Proof. lia. Qed.
Opaque Grow_Z_Left_Bot_dim.

Opaque Cast.

(* TODO: Finish Grow_Z_Left_Bot_1_2 *)


Lemma Grow_Z_Left_Bot_1_2 : forall {n m} α,
	𝒵 (n + 1) (m + 1) α ∝
	Cast (n + 1) (n + 1 + 1) (eq_refl) (Grow_Z_Left_Bot_dim _) (nWire n ↕ 𝒵 1 2 0) ⟷ (𝒵 (n + 1) m α ↕ —).
Proof.
	induction n; intros.
	- simpl_casts.
		cleanup_zx.
		eapply (cast_diagrams 1 (m + 1)).
		simpl_casts.
		simpl.
		induction m.
		+ solve_prop 1.
		+ destruct m.
			* solve_prop 1.
			* rewrite (Grow_Z_Right 1 m).
				rewrite stack_wire_distribute_r.
				rewrite <- ZX_Compose_assoc.
				rewrite <- IHm.
				rewrite wire_to_nWire at 2.
				rewrite (ZX_Stack_assoc (𝒵 1 2 0) (nWire m)).
				simpl_casts.
				rewrite <- nstack1_split.
				simpl.
				rewrite <- Grow_Z_Right.
				easy.
	- simpl.
		destruct n.
		+ simpl.
			simpl_casts.
			cleanup_zx.
			simpl_casts.
			simpl in IHn.
			induction m.
			* solve_prop 1.
			* simpl.
				destruct m.
				-- solve_prop 1.
				-- rewrite (Grow_Z_Right 2 m).
					 rewrite stack_wire_distribute_r.
					 rewrite <- ZX_Compose_assoc.
					 rewrite <- IHm.
					 rewrite wire_to_nWire at 2.
					 rewrite (ZX_Stack_assoc (𝒵 1 2 0) (nWire m) (nWire 1)).
					 simpl_casts.
					 rewrite <- nstack1_split.
					 simpl.
					 admit.
		+ rewrite cast_compose_l.
			simpl_casts.
			rewrite (ZX_Stack_assoc — (nWire (S n))).
			simpl_casts.
			eapply (cast_diagrams (1 + ((S n) + 1)) (m + 1)).
			rewrite cast_compose_distribute.
			simpl_casts.
			erewrite (cast_compose_mid (S (S n + 1) + 1)).
			simpl_casts.
			simpl.
			erewrite (cast_stack_bot _ _ — (nWire (S n) ↕ 𝒵 1 2 0)).
			rewrite (Grow_Z_Left (n + 1) m).
			simpl in IHn.
Admitted.

Lemma Z_1_2_1_fusion : forall α β,
	(𝒵 1 2 α ⟷ 𝒵 2 1 β) ∝ (𝒵 1 1 (α + β)).
Proof. solve_prop 1. Qed.

Lemma nWire_S_l : forall n,
	nWire (S n) ∝ — ↕ nWire n.
Proof. intros. easy. Qed.

Lemma Z_Absolute_Fusion : forall {n m o} α β,
	(𝒵 n (S m) α ⟷ 𝒵 (S m) o β) ∝
	𝒵 n o (α + β).
Proof.
	intros.
	induction m.
	- apply Z_spider_1_1_fusion.
	- rewrite Grow_Z_Right, Grow_Z_Left.
		rewrite ZX_Compose_assoc.
		rewrite <- (ZX_Compose_assoc ((𝒵 1 2 0) ↕ (m ↑ —))
																 ((𝒵 2 1 0) ↕ (m ↑ —))
																	(𝒵 (S m) o β)) .
		rewrite <- ZX_Stack_Compose_distr.
		rewrite Z_1_2_1_fusion.
		rewrite Rplus_0_l.
		rewrite Z_0_is_wire.
		cleanup_zx.
		apply IHm.
Qed.

Lemma cap_absorb_dim : forall n m,
	(n + 0 + m = n + m)%nat.
Proof. lia. Qed.

Opaque Cast.

Lemma Z_Cap_absord_base : forall α,
	𝒵 1 2 α ⟷ ⊃ ∝ 𝒵 1 0 α.
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl.
	Msimpl.
	unfold Z_semantics.
	simpl.
	solve_matrix.
Qed.

Lemma Z_appendix_top_l : forall n m α,
	𝒵 n m α ∝ (𝒵 0 1 0 ↕ nWire n) ⟷ 𝒵 (S n) m α.
Proof.
	induction n; intros.
	- cleanup_zx.
		simpl_casts.
		rewrite Z_spider_1_1_fusion.
		rewrite Rplus_0_l.
		easy.
	- rewrite Grow_Z_Left.
		rewrite <- ZX_Compose_assoc.
		fold (nWire n).
		rewrite nWire_S_l.
		rewrite (ZX_Stack_assoc_back (𝒵 0 1 0) (—) (nWire n)).
		simpl_casts.
		rewrite <- (ZX_Stack_Compose_distr (𝒵 0 1 0 ↕ —) (𝒵 2 1 0) (nWire n)).
		rewrite Grow_Z_Left_1_2.
		rewrite <- ZX_Compose_assoc.
		rewrite <- wire_to_nWire.
		rewrite <- (ZX_Stack_Compose_distr (𝒵 0 1 0) _ _ _).
		rewrite Z_spider_1_1_fusion.
		rewrite Rplus_0_l.
		cleanup_zx.
		rewrite Z_2_0_0_is_cap.
		rewrite Z_0_2_0_is_cup.
		rewrite yank_r.
		cleanup_zx.
		easy.
Qed.

Lemma Z_appendix_top_r : forall n m α,
	𝒵 n m α ∝  𝒵 n (S m) α ⟷ (𝒵 1 0 0 ↕ nWire m).
Proof.
	intros.
	apply transpose_diagrams.
	simpl.
	cleanup_zx.
	rewrite nstack1_transpose.
	rewrite transpose_wire.
	fold (nWire m).
	rewrite <- (Z_appendix_top_l m n).
	easy.
Qed.

Lemma Z_Wrap_Under_R_base : forall α,
	𝒵 1 2 α ∝  (— ↕ ⊂) ⟷ (𝒵 2 1 α ↕ —).
Proof.
	intros.
	simpl.
	prop_exists_nonzero 1.
	simpl; Msimpl.
	unfold Z_semantics; simpl.
	solve_matrix.
Qed.

Lemma Z_Wrap_Under_L_base : forall α,
	𝒵 2 1 α ∝ (𝒵 1 2 α ↕ —) ⟷ (— ↕ ⊃).
Proof. transpose_of Z_Wrap_Under_R_base. Qed.

Lemma Z_Cap_absorb : forall n m0 m1 α,
	𝒵 n (m0 + 2 + m1) α ⟷ (nWire m0 ↕ ⊃ ↕ nWire m1) ∝ 
	(𝒵 n (m0 + 0 + m1) α).
Proof.
	intros.
	induction m0.
	- simpl.
		cleanup_zx.
		rewrite Grow_Z_Right.
		rewrite ZX_Compose_assoc.
		rewrite <- (ZX_Stack_Compose_distr (𝒵 1 2 0) ⊃ (nWire m1) (nWire m1)).
		rewrite Z_Cap_absord_base.
		cleanup_zx.
		rewrite <- Z_appendix_top_r.
		easy.
	- destruct m0.
		+ simpl.
			rewrite Grow_Z_Right.
			rewrite ZX_Compose_assoc.
			rewrite nWire_S_l.
			rewrite (ZX_Stack_assoc_back (𝒵 1 2 0) —).
			simpl_casts.
			rewrite <- (ZX_Stack_Compose_distr (𝒵 1 2 0 ↕ —) (nWire 1 ↕ ⊃) (nWire m1)).
			rewrite <- wire_to_nWire.
			rewrite <- Z_Wrap_Under_L_base.
			cleanup_zx.
			rewrite Grow_Z_Right.
			rewrite ZX_Compose_assoc.
			rewrite <- (ZX_Stack_Compose_distr (𝒵 1 2 0) (𝒵 2 1 0) (nWire m1) _).
			cleanup_zx.
			rewrite Z_Absolute_Fusion.
			rewrite Rplus_0_l.
			cleanup_zx.
			easy.
		+ simpl.
			rewrite Grow_Z_Right.
			rewrite (ZX_Stack_assoc_back — —).
			simpl_casts.
			rewrite ZX_Compose_assoc.
			rewrite (ZX_Stack_assoc (— ↕ —)).
			simpl_casts.
			rewrite (ZX_Stack_assoc (— ↕ —)).
			simpl_casts.
			rewrite <- (ZX_Stack_Compose_distr (𝒵 1 2 0) (— ↕ —) 
														 (nWire (m0 + 2 + m1)) (nWire m0 ↕ ⊃ ↕ nWire m1)).
			rewrite wire_to_nWire at 2.
			rewrite <- nWire_S_l.
			cleanup_zx.
			rewrite <- nwire_stack_compose_topleft.
			rewrite <- wire_to_nWire.
			rewrite ZX_Stack_assoc_back.
			simpl_casts.
			rewrite ZX_Stack_assoc_back.
			simpl_casts.
			rewrite <- nWire_S_l.
			rewrite <- ZX_Compose_assoc.
			rewrite IHm0.
			rewrite <- Grow_Z_Right.
			easy.
Qed.

Lemma Grow_Z_Top_Left_by : forall n {m o α},
	𝒵 (n + m) o α ∝
	(𝒵 n 1 0 ↕ nWire m) ⟷ 𝒵 (S m) o α.
Proof.
	induction n; intros.
	- simpl.
		rewrite <- (Z_appendix_top_l m).
		easy.
	- intros.
		simpl.
		destruct n.
		+ simpl.
			cleanup_zx.
			easy.
		+ rewrite Grow_Z_Left.
			rewrite stack_nwire_distribute_r.
			rewrite ZX_Compose_assoc.
			rewrite <- IHn.
			rewrite (ZX_Stack_assoc (𝒵 2 1 0) (nWire n) (nWire m)).
			simpl_casts.
			rewrite <- nstack1_split.
			rewrite <- (Grow_Z_Left (n + m)).
			easy.
Qed.

Lemma Grow_Z_Top_Right_by : forall {n} m {o α},
	𝒵 n (m + o) α ∝
	𝒵 n (S o) α ⟷ (𝒵 1 m 0 ↕ nWire o).
Proof.
	intros.
	apply transpose_diagrams.
	simpl.
	rewrite nstack1_transpose.
	rewrite transpose_wire.
	apply Grow_Z_Top_Left_by.
Qed.

Lemma Grow_Z_Bot_Left_by : forall n {m o α},
	𝒵 (n + m) o α ∝ 
	(nWire n ↕ 𝒵 m 1 0) ⟷ 𝒵 (n + 1) o α.
Proof.
	induction n; intros.
	- simpl.
		cleanup_zx.
		rewrite Z_spider_1_1_fusion.
		rewrite Rplus_0_l.
		easy.
	- destruct n. 
		+ simpl.
			cleanup_zx.
			simpl_casts.
			rewrite (Z_WrapOver_Top_Left 1 o).
			rewrite <- ZX_Compose_assoc.
			rewrite <- stack_wire_distribute_l.
			rewrite Z_spider_1_1_fusion.
			rewrite Rplus_0_l.
			rewrite <- Z_WrapOver_Top_Left.
			easy.
		+ simpl. 
			rewrite (Grow_Z_Left (n + 1) o).
			rewrite <- ZX_Compose_assoc.
			rewrite (ZX_Stack_assoc_back — —).
			simpl_casts.
			rewrite (ZX_Stack_assoc (— ↕ —)).
			simpl_casts.
			rewrite <- (ZX_Stack_Compose_distr (— ↕ —) (𝒵 2 1 0) (nWire n ↕ 𝒵 m 1 0)).
			cleanup_zx.
			rewrite <- nwire_stack_compose_botleft.
			rewrite ZX_Stack_assoc_back.
			simpl_casts.
			rewrite <- nstack1_split.
			rewrite ZX_Compose_assoc.
			rewrite <- (IHn m o α).
			simpl.
			rewrite wire_to_nWire at 1.
			rewrite wire_to_nWire at 2.
			rewrite <- nstack1_split.
			cleanup_zx.
			rewrite <- (Grow_Z_Left (n + m)).
			easy.
Qed.

Lemma Grow_Z_Bot_Right_by : forall {n m} o {α},
	𝒵 n (m + o) α ∝ 
	𝒵 n (m + 1) α ⟷ (nWire m ↕ 𝒵 1 o 0).
Proof.
	intros.
	apply transpose_diagrams.
	simpl.
	rewrite nstack1_transpose.
	rewrite transpose_wire.
	apply Grow_Z_Bot_Left_by.
Qed.

Lemma WrapUnder_dim : forall n, 
	(n + 1 + 1 = n + 2)%nat.
Proof. lia. Qed.

Lemma WrapUnder_L_base : forall α,
	𝒵 0 1 α ∝
	⊂ ⟷ (𝒵 1 0 α ↕ —).
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl; Msimpl.
	unfold Z_semantics.
	gridify.
	solve_matrix.
Qed.

Lemma WrapUnder_L_ind :
	(— ↕ ⊂) ⟷ (𝒵 2 1 0 ↕ —) ∝ 𝒵 1 2 0.
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl; Msimpl.
	unfold Z_semantics.
	simpl.
	solve_matrix.
Qed.

Lemma WrapUnder_L : forall n m α,
	𝒵 n (m + 1) α ∝ 
	(Cast n (n + 1 + 1) (eq_sym (plus_0_r _)) (WrapUnder_dim _) 
				(nWire n ↕ Cap)) ⟷ 𝒵 (n + 1) m α ↕ —.
Proof.
	induction n; intros.
	- simpl.
		simpl_casts.
		cleanup_zx.
		induction m.
		+ simpl.
			prop_exists_nonzero 1. 
			simpl; Msimpl.
			unfold Z_semantics.
			solve_matrix.
		+ simpl.
			destruct m.
			* simpl.
				rewrite (Grow_Z_Top_Right_by 1).
				prop_exists_nonzero 1.
				simpl; Msimpl.
				unfold Z_semantics.
				simpl.
				solve_matrix.
				rewrite Cexp_0.
				lca.
			* rewrite Grow_Z_Right.
				rewrite stack_wire_distribute_r.
				rewrite <- ZX_Compose_assoc.
				rewrite <- IHm.
				rewrite wire_to_nWire at 2.
				rewrite (ZX_Stack_assoc (𝒵 1 2 0) (nWire m)).
				simpl_casts.
				rewrite <- nstack1_split.
				simpl.
				rewrite <- Grow_Z_Right.
				easy.
	- destruct n.
		+ simpl.
			simpl_casts.
			cleanup_zx.
			simpl_casts.
			simpl in IHn.
			rewrite Grow_Z_Left.
			cleanup_zx.
			simpl_casts.
			rewrite stack_wire_distribute_r.
			rewrite wire_to_nWire.
Admitted.

Lemma dominant_spider_fusion_r : forall n m0 m1 o α β,
	𝒵 n ((S m0) + m1) α ⟷ (𝒵 (S m0) o β ↕ nWire m1) ∝ 
	𝒵 n (o + m1) (α + β).
Proof.
	intros.
	replace α with (0 + α + 0)%R at 1 by lra. 
	rewrite Z_add_r.
	repeat rewrite ZX_Compose_assoc.
	rewrite <- (ZX_Stack_Compose_distr (𝒵 1 (S m0) 0)).
	rewrite Z_Absolute_Fusion.
	rewrite Rplus_0_l.
	cleanup_zx.
	rewrite <- (Rplus_0_l β).
	rewrite (Z_appendix_rot_r 1 o β).
	rewrite <- (nwire_removal_r (𝒵 1 m1 0)).
	rewrite ZX_Stack_Compose_distr.
	rewrite <- ZX_Compose_assoc.
	rewrite <- Z_add_r.
	rewrite (ZX_Stack_assoc (𝒵 1 0 0) (nWire o)).
	simpl_casts.
	rewrite <- nstack1_split.
	simpl.
	rewrite <- Z_appendix_rot_r.
	replace (0 + (β + α + 0))%R with (α + (0 + β))%R by lra.
	easy.
Qed.

Lemma dominated_spider_fusion_r : forall n m0 m1 o α β,
	(𝒵 n (S m0) α ↕ nWire m1 ⟷ 𝒵 (S m0 + m1) o β) ∝
	𝒵 (n + m1) o (α + β).
Proof.
	intros.
	replace β%R with (0 + β + 0)%R at 1 by lra.
	rewrite Z_add_l.
	rewrite <- ZX_Compose_assoc.
	rewrite <- ZX_Stack_Compose_distr.
	rewrite Z_Absolute_Fusion.
	cleanup_zx.
	rewrite <- Z_add_l.
	replace (α + 0 + β + 0)%R with (α + β)%R by lra.
	easy.
Qed.

Lemma SpiderFusion : forall top mid bot input output α β,
	𝒵 input (top + S mid) α ↕ nWire bot ⟷
	Cast (top + (S mid) + bot) (top + output) (eq_sym (Nat.add_assoc _ _ _)) eq_refl 
		(nWire top ↕ 𝒵 (S mid + bot) output β) ∝
	𝒵 (input + bot) (top + output) (α + β).
Proof.
	intros.
	replace α%R with (0 + α + 0)%R at 1 by lra.
	rewrite Z_add_r.
	rewrite stack_nwire_distribute_r.
	rewrite ZX_Compose_assoc.
	rewrite (ZX_Stack_assoc (𝒵 1 top 0)).
	rewrite cast_compose_r.
	simpl_casts.
	rewrite <- (ZX_Stack_Compose_distr (𝒵 1 top 0) (nWire top) (𝒵 1 (S mid) 0 ↕ nWire bot)).
	cleanup_zx.
	rewrite dominated_spider_fusion_r.
	rewrite Grow_Z_Bot_Left_by.
	simpl.
	cleanup_zx.
	simpl_casts.
	rewrite Z_WrapOver_Top_Right.
	rewrite stack_nwire_distribute_r.
	rewrite (ZX_Stack_assoc — (𝒵 (S input) 1 α) (nWire bot)).
	simpl_casts.
	rewrite ZX_Compose_assoc.
	rewrite <- (ZX_Stack_Compose_distr — (𝒵 1 top 0) (𝒵 (S input) 1 α ↕ nWire bot)).
	cleanup_zx.
	rewrite wire_to_nWire at 4.
	rewrite <- ZX_Compose_assoc.
	rewrite (nwire_stack_compose_botleft (𝒵 (S input) 1 α)).
	rewrite <- Z_add_l.
	rewrite <- (wire_removal_l (𝒵 1 top 0)).
	rewrite <- (nwire_removal_r (𝒵 (S input + bot) _ _)).
	rewrite ZX_Stack_Compose_distr.
	rewrite <- ZX_Compose_assoc.
	rewrite (ZX_Stack_assoc ⊂ (nWire input)).
	simpl_casts.
	rewrite <- nstack1_split.
	rewrite <- (Z_WrapOver_Top_Right (input + bot)).
	rewrite <- Grow_Z_Top_Right_by.
	replace (α + (0 + β) + 0)%R with (α + β)%R by lra.
	easy.
Qed.
