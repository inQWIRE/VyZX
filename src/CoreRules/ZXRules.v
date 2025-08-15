Require Import CoreData.CoreData.
Require Import CoreRules.WireRules.
Require Import CoreRules.CastRules.
Require Import CoreRules.StackComposeRules.
Require Import CoreRules.CoreAutomation.
Require Export CoreRules.ZRules.
Require Export CoreRules.XRules.

Theorem X_state_copy_phase_0 : forall (r n : nat) prfn prfm,
	(X 0 1 ((INR r) * PI) ⟷ Z 1 n 0) 
	∝[(√2 * (/√2 ^ n))%R]
	cast 0%nat n prfn prfm (n ⇑ (X 0 1 ((INR r) * PI))).
Proof.
	intros.
	assert (X_state_copy_ind : (X 0 1 (INR r * PI) ⟷ Z 1 2 0) ∝[/(√2)%R]
		X 0 1 (INR r * PI) ↕ X 0 1 (INR r * PI)).
	{ 
		zxsymmetry.
		split; [|C_field].
		symmetry.
		prep_matrix_equivalence.
		Msimpl; simpl.
		unfold X_semantics, Z_semantics.
		rewrite Cexp_0.
		destruct (INR_pi_exp r); rewrite H;
		cbv delta [kron_n kron hadamard Mmult scale I];
		by_cell; simpl; C_field; lca.
	} 
	induction n; [| destruct n].
	- simpl. (* n = 0 --> √2 *)
		simpl_casts.
		split; [|nonzero].
		prep_matrix_equivalence.
		by_cell.
		unfold X_semantics, Z_semantics, Mmult, 
			kron_n, kron, hadamard, I, scale;
		simpl.
		Csimpl.
		rewrite Rinv_1, Rmult_1_r.
		C_field.
		destruct (INR_pi_exp r); rewrite H;
		autorewrite with Cexp_db; lca.
	-	simpl. (* n = 1 --> 1 *)
		rewrite Z_0_is_wire.
		rewrite cast_id.
		rewrite stack_empty_r.
		rewrite cast_id.
		cleanup_zx.
		zxrefl.
	  rewrite Rmult_1_r.
		rewrite Rinv_r by nonzero.
		reflexivity.
	- eapply (cast_diagrams_by (S (S n) * 0) (S (S n) * 1)).
		rewrite cast_contract.
		rewrite cast_compose_distribute.
		rewrite cast_X, cast_Z, cast_id.
		simpl.
		eapply (@cast_simplify_by 0 (S n * 0)%nat (S n) (S n * 1)%nat) in IHn.
		rewrite cast_compose_distribute in IHn.
		rewrite cast_Z in IHn.
		rewrite cast_X in IHn.
		rewrite cast_contract in IHn.
		simpl in IHn.
		rewrite cast_id in IHn.
		rewrite grow_Z_top_right.
		rewrite <- compose_assoc.
		zxrewrite IHn.
		rewrite <- (stack_compose_distr
			(X 0 1 (INR r * PI)) (Z 1 2 0) (n ⇑ X 0 1 (INR r * PI)) (n_wire (n * 1))).
		zxrewrite X_state_copy_ind.
		cleanup_zx.
		rewrite (stack_assoc (X 0 1 (INR r * PI)) (X 0 1 (INR r * PI))).
		simpl_casts.
		zxrefl.
		autorewrite with RtoC_db.
		C_field.
		Unshelve.
		all: lia.
Qed.

Theorem Z_state_copy_phase_0 : forall (r n : nat) prfn prfm,
	(Z 0 1 ((INR r) * PI) ⟷ X 1 n 0) 
	∝[(√2 * (/√2 ^ n))%R]
	cast 0%nat n prfn prfm (n ⇑ (Z 0 1 ((INR r) * PI))).
Proof.
	intros r n prfn prfm.
	colorswap_of (X_state_copy_phase_0 r n prfn prfm).
Qed.

Theorem X_state_copy : forall (r n : nat) (a : R) prfn prfm,
	(X 0 1 ((INR r) * PI) ⟷ Z 1 n a) 
	∝[((/√2 ^ S n))%R *
	(((C1 + Cexp ((INR r) * PI)) * (C1 - Cexp a) + 2 * Cexp a))]
	cast 0%nat n prfn prfm (n ⇑ (X 0 1 ((INR r) * PI))).
Proof.
	assert (X_Z_phase_value' : forall (a b : R),
		(⟦ X 0 1 a ⟷ Z 1 0 b ⟧ = 
		(((C1 + Cexp a) * (C1 - Cexp b) + 2 * Cexp b) / √2) .* I 1)%M). 1: {
		intros a b.
		prep_matrix_equivalence.
		by_cell.
		cbn; unfold kron, scale; cbn.
		Csimpl.
		C_field_simplify; [|nonzero].
		lca.
	}
	intros r n a prfn prfm.
	replace (((/√2 ^ S n))%R * (((C1 + Cexp ((INR r) * PI)) * (C1 - Cexp a) + 2 * Cexp a))) 
		with  (((/√2 ^ n))%R * (((C1 + Cexp ((INR r) * PI)) * (C1 - Cexp a) + 2 * Cexp a) / √2))
		by (simpl; unfold Cdiv; rewrite Rinv_mult, Cmult_assoc, Cmult_comm, 
			Cmult_assoc, RtoC_mult, !RtoC_inv; reflexivity).
	replace (Z 1 n a) with (Z 1 n (a + 0)) by (f_equal; lra).
	rewrite Z_appendix_rot_r.
	rewrite <- compose_assoc.
	zxrewrite X_state_copy_phase_0.
	simpl.
	rewrite cast_compose_l.
	erewrite <- (cast_stack_r (nBot' := n * 1) (mBot' := n) 
		_ _ _ _ (Z 1 0 a) (n_wire n)).
	rewrite <- (stack_compose_distr (X 0 1 _) (Z 1 0 a) (n ⇑ X 0 1 _)
		($ n * 1, n ::: n_wire n $)).
	erewrite (cast_stack_distribute (n':=0) (m' := 0) (o' := 0) (p' := n)
		_ _ _ _ _ _ (X 0 1 (INR r * PI) ⟷ Z 1 0 a)
		((n ⇑ X 0 1 (INR r * PI) ⟷ $ n * 1, n ::: n_wire n $))).
	rewrite cast_id.
	zxsymmetry.
	rewrite <- stack_empty_l.
	erewrite (proportional_by_trans_iff_l _ _ _ 1).
	- apply (stack_prop_by_compat_l
		⦰ (X 0 1 (INR r * PI) ⟷ Z 1 0 a)
		($ 0, n ::: n ⇑ X 0 1 (INR r * PI) ⟷ $ n * 1, n ::: n_wire n $ $)).
		assert (Hnz : ((C1 + Cexp (INR r * PI)) * (C1 - Cexp a) + C2 * Cexp a) <> C0). 1: {
			rewrite Cmult_plus_distr_r.
			unfold Cminus at 1.
			rewrite Cmult_plus_distr_l.
			Csimpl.
			rewrite Cplus_comm, Cplus_assoc. 
			replace (C2 * Cexp a + (C1 + - Cexp a)) with (C1 + Cexp a) by lca.
			destruct (INR_pi_exp r) as [-> | ->].
			- Csimpl.
				rewrite <- Cplus_assoc, (Cplus_comm (Cexp a)).
				unfold Cminus.
				rewrite <- Cplus_assoc, Cplus_opp_l.
				intros H%(f_equal fst); simpl in H; lra.
			- pose proof (Cexp_nonzero a) as Hnz.
				replace (C1 + Cexp a + -1 * (C1 - Cexp a)) with (C2 * Cexp a) by lca.
				apply Cmult_nonzero_iff.
				split; nonzero.
		} 
		split.
		+ rewrite X_Z_phase_value'.
			prep_matrix_equivalence.
			by_cell.
			unfold scale;
			cbn.
			Csimpl.
			rewrite Cdiv_1_r.
			unfold Cdiv.
			rewrite Cinv_mult_distr.
			rewrite <- 2!Cmult_assoc.
			rewrite Cinv_l by (apply Cdiv_nonzero_iff; split; assumption + nonzero).
			Csimpl.
			rewrite Rinv_mult, <- Rmult_assoc, Rinv_r, Rmult_1_l by nonzero.
			symmetry.
			apply Cinv_r.
			rewrite RtoC_inv, <- RtoC_pow.
			apply nonzero_div_nonzero.
			nonzero.
		+ apply Cdiv_nonzero; [|nonzero].
			apply Cmult_nonzero_iff; split; [nonzero|].
			apply nonzero_div_nonzero.
			apply Cmult_nonzero_iff; split; [nonzero|].
			apply Cdiv_nonzero_iff; split; [nonzero|assumption].
	- zxrefl.
		rewrite 2!stack_empty_l.
		rewrite cast_compose_r, nwire_removal_r.
		rewrite 2!cast_contract.
		cast_irrelevance.
	Unshelve.
	all: lia.
Qed.

Theorem Z_state_copy : forall (r n : nat) (a : R) prfn prfm,
	(Z 0 1 ((INR r) * PI) ⟷ X 1 n a) 
	∝[((/√2 ^ S n))%R *
	(((C1 + Cexp ((INR r) * PI)) * (C1 - Cexp a) + 2 * Cexp a))]
	cast 0%nat n prfn prfm (n ⇑ (Z 0 1 ((INR r) * PI))).
Proof.
	intros r n a prfn prfm.
	colorswap_of (X_state_copy r n a prfn prfm).
Qed.

Theorem X_state_pi_copy : forall n prfn prfm,
	((X 0 1 PI) ⟷ Z 1 n 0) ∝[(√2 * (/√2 ^ n))%R]
	(cast 0 n prfn prfm (n ⇑ (X 0 1 PI))).
Proof.
	intros.
	replace (PI)%R with (1 * PI)%R by lra.
	replace (1)%R with (INR 1)%R by reflexivity.
	zxrewrite X_state_copy_phase_0.
	zxrefl.
Qed.

Theorem X_state_0_copy : forall n prfn prfm,
	((X 0 1 0) ⟷ Z 1 n 0) ∝[(√2 * (/√2 ^ n))%R]
	(cast 0 n prfn prfm (n ⇑ (X 0 1 0))).
Proof.
	intros.
	replace (0)%R with (0 * PI)%R at 1 by lra.
	replace (0)%R with (INR 0)%R by reflexivity.
	zxrewrite X_state_copy_phase_0.
	rewrite Rmult_0_l.
	zxrefl.
Qed.

Theorem Z_state_pi_copy : forall n prfn prfm,
	((Z 0 1 PI) ⟷ X 1 n 0) ∝[(√2 * (/√2 ^ n))%R]
	(cast 0 n prfn prfm (n ⇑ (Z 0 1 PI))).
Proof.
	intros.
	replace (PI)%R with (1 * PI)%R by lra.
	replace (1)%R with (INR 1)%R by reflexivity.
	zxrewrite Z_state_copy_phase_0.
	zxrefl.
Qed.

Theorem Z_state_0_copy : forall n prfn prfm,
	((Z 0 1 0) ⟷ X 1 n 0) ∝[(√2 * (/√2 ^ n))%R]
	(cast 0 n prfn prfm (n ⇑ (Z 0 1 0))).
Proof.
	intros.
	replace (0)%R with (0 * PI)%R at 1 by lra.
	replace (0)%R with (INR 0)%R by reflexivity.
	zxrewrite Z_state_copy_phase_0.
	rewrite Rmult_0_l.
	zxrefl.
Qed.

Lemma Z_copy : forall n r prfn prfm, 
	(Z 1 1 (INR r * PI) ⟷ X 1 n 0) ∝=
	X 1 n 0 ⟷ 
		(cast n n prfn prfm
			(n ⇑ (Z 1 1 (INR r * PI)))).
Proof.
	intros.
	assert (Z_copy_ind : (Z 1 1 (INR r * PI) ⟷ X 1 2 0) ∝=
		X 1 2 0 ⟷ (Z 1 1 (INR r * PI) ↕ Z 1 1 (INR r * PI))).
	{ 
		prep_matrix_equivalence.
		Msimpl; simpl.
		unfold X_semantics, Z_semantics.
		rewrite Cexp_0.
		destruct (INR_pi_exp r); rewrite H;
		cbv delta [kron_n kron hadamard Mmult scale I];
		by_cell; simpl; C_field; lca.
	} 
	eapply (cast_diagrams_eq 1 (n * 1)).
	rewrite 2 cast_compose_distribute.
	simpl_casts.
	erewrite (@cast_compose_mid _ _ _ (n * 1)%nat _ _ (X 1 n 0)).
	rewrite cast_X, cast_contract, cast_id.
	induction n; [ | destruct n].
	- simpl.
		prep_matrix_equivalence.
		simpl.
		unfold X_semantics, Z_semantics;
		rewrite Cexp_0;
		cbv [kron_n kron hadamard Mmult scale I];
		by_cell; simpl; C_field; lca.
	- simpl.
		repeat rewrite X_0_is_wire.
		cleanup_zx.
		now rewrite cast_id.
	- simpl.
		rewrite grow_X_top_right.
		simpl in IHn.
		rewrite <- compose_assoc.
		rewrite IHn by lia.
		rewrite compose_assoc.
		rewrite <- (stack_compose_distr 
			(Z 1 1 (INR r * PI)) 				(X 1 2 0) 
			(n ⇑ (Z 1 1 (INR r * PI))) (n_wire (n * 1))).
		rewrite Z_copy_ind.
		rewrite nwire_removal_r.
		rewrite <- (nwire_removal_l (n ⇑ Z 1 1 (INR r * PI))) at 1.
		rewrite stack_compose_distr.
		rewrite compose_assoc.
		rewrite (stack_assoc (Z 1 1 (INR r * PI))).
		rewrite cast_id.
		easy.
	Unshelve.
	all: lia.
Qed.

Lemma X_copy : forall n r prfn prfm,
	(X 1 1 (INR r * PI) ⟷ Z 1 n 0) ∝=
	Z 1 n 0 ⟷ 
		(cast n n
			prfn prfm
			(n ⇑ (X 1 1 (INR r * PI)))).
Proof.
	intros n r prfn prfm.
	colorswap_of (Z_copy n r prfn prfm).
Qed.

Lemma Z_0_copy : forall n prfn prfm, 
	(Z 1 1 0 ⟷ X 1 n 0) ∝=
	X 1 n 0 ⟷ 
		(cast n n prfn prfm
			(n ⇑ (Z 1 1 0))).
Proof.
	intros.
	specialize (Z_copy n 0).
	intros.
	simpl in H.
	rewrite Rmult_0_l in H.
	apply H.
Qed.

Lemma Z_pi_copy : forall n prfn prfm, 
	(Z 1 1 PI ⟷ X 1 n 0) ∝=
	X 1 n 0 ⟷ 
		(cast n n prfn prfm
			(n ⇑ (Z 1 1 PI))).
Proof.
	intros.
	specialize (Z_copy n 1).
	intros.
	simpl in H.
	rewrite Rmult_1_l in H.
	apply H.
Qed.

Lemma X_0_copy : forall n prfn prfm, 
	(X 1 1 0 ⟷ Z 1 n 0) ∝=
	Z 1 n 0 ⟷ 
		(cast n n prfn prfm
			(n ⇑ (X 1 1 0))).
Proof.
	intros.
	specialize (X_copy n 0).
	intros.
	simpl in H.
	rewrite Rmult_0_l in H.
	apply H.
Qed.

Lemma X_pi_copy : forall n prfn prfm, 
	(X 1 1 PI ⟷ Z 1 n 0) ∝=
	Z 1 n 0 ⟷ 
		(cast n n prfn prfm
			(n ⇑ (X 1 1 PI))).
Proof.
	intros.
	specialize (X_copy n 1).
	intros.
	simpl in H.
	rewrite Rmult_1_l in H.
	apply H.
Qed.