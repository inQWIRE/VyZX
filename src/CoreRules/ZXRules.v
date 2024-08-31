Require Import CoreData.CoreData.
Require Import CoreRules.WireRules.
Require Import CoreRules.CastRules.
Require Import CoreRules.StackComposeRules.
Require Import CoreRules.CoreAutomation.
Require Export CoreRules.ZRules.
Require Export CoreRules.XRules.



Theorem X_state_copy : forall (r n : nat) prfn prfm,
	(X 0 1 ((INR r) * PI) ⟷ Z 1 n 0) ∝
	cast 0%nat n prfn prfm (n ⇑ (X 0 1 ((INR r) * PI))).
Proof.
	intros.
	assert (X_state_copy_ind : (X 0 1 (INR r * PI) ⟷ Z 1 2 0) ∝
		X 0 1 (INR r * PI) ↕ X 0 1 (INR r * PI)).
	{ 
		prop_exists_nonzero (/ (√ 2)%R).
		prep_matrix_equivalence.
		cbn.
		unfold X_semantics.
		rewrite kron_n_1, Mmult_1_r by auto_wf.
		rewrite <- kron_mixed_product.
		restore_dims.
		compute_matrix (hadamard ⊗ hadamard).
		group_radicals.
		compute_matrix 
			(Z_semantics 0 1 (INR r * PI) ⊗ Z_semantics 0 1 (INR r * PI)).
		compute_matrix (Z_semantics 1 2 0).
		rewrite Cexp_0.
		rewrite <- Cexp_add, <- Rmult_plus_distr_r, <- plus_INR.
		rewrite double_mult, mult_INR.
		rewrite !INR_IZR_INZ, <- mult_IZR, Cexp_2nPI.
		unfold scale;
		by_cell; cbn; lca.
	} 
	induction n; [| destruct n].
	- simpl.
		rewrite cast_id. 
		prop_exists_nonzero (√ 2)%R; Msimpl.
		cbn; unfold X_semantics.
		rewrite kron_n_1, Mmult_1_r by auto_wf.
		prep_matrix_equivalence.
		by_cell; unfold scale;
		cbn.
		rewrite Cexp_0.
		C_field.
		lca.
	-	simpl. 
		rewrite Z_0_is_wire.
		rewrite cast_id.
		rewrite stack_empty_r.
		rewrite cast_id.
		cleanup_zx.
		easy.
	- eapply (cast_diagrams (S (S n) * 0) (S (S n) * 1)).
		rewrite cast_contract.
		rewrite cast_compose_distribute.
		rewrite cast_X, cast_Z, cast_id.
		simpl.
		eapply (@cast_simplify 0 (S n * 0)%nat (S n) (S n * 1)%nat) in IHn.
		rewrite cast_compose_distribute in IHn.
		rewrite cast_Z in IHn.
		rewrite cast_X in IHn.
		rewrite cast_contract in IHn.
		simpl in IHn.
		rewrite cast_id in IHn.
		rewrite grow_Z_top_right.
		rewrite <- compose_assoc.
		rewrite IHn.
		rewrite <- (stack_compose_distr
			(X 0 1 (INR r * PI)) (Z 1 2 0) (n ⇑ X 0 1 (INR r * PI)) (n_wire (n * 1))).
		rewrite X_state_copy_ind.
		cleanup_zx.
		rewrite (stack_assoc (X 0 1 (INR r * PI)) (X 0 1 (INR r * PI))).
		rewrite cast_id.
		easy.
		Unshelve.
		all: lia.
Qed.

Theorem Z_state_copy : forall (r n : nat) prfn prfm,
	(Z 0 1 ((INR r) * PI) ⟷ X 1 n 0) ∝
	cast 0%nat n prfn prfm (n ⇑ (Z 0 1 ((INR r) * PI))).
Proof.
	intros.
	eapply (cast_diagrams (n * 0) (n * 1)).
	rewrite cast_compose_distribute.
	simpl_casts.
	apply colorswap_diagrams.
	autorewrite with colorswap_db.
	simpl.
	destruct n.
	- simpl.
		simpl_casts.
		rewrite X_state_copy.
		simpl.
		simpl_casts.
		easy.
	- eapply (cast_diagrams (0) (S n)).
		rewrite cast_compose_distribute.
		simpl_casts.
		apply X_state_copy.
		Unshelve.
		all: lia.
Qed.

Theorem X_state_pi_copy : forall n prfn prfm,
	((X 0 1 PI) ⟷ Z 1 n 0) ∝ 
	(cast 0 n prfn prfm (n ⇑ (X 0 1 PI))).
Proof.
	intros.
	replace (PI)%R with (1 * PI)%R by lra.
	replace (1)%R with (INR 1)%R by reflexivity.
	rewrite X_state_copy.
	easy.
Qed.

Theorem X_state_0_copy : forall n prfn prfm,
	((X 0 1 0) ⟷ Z 1 n 0) ∝ 
	(cast 0 n prfn prfm (n ⇑ (X 0 1 0))).
Proof.
	intros.
	replace (0)%R with (0 * PI)%R at 1 by lra.
	replace (0)%R with (INR 0)%R by reflexivity.
	rewrite X_state_copy.
	replace (0 * PI)%R with (0)%R at 1 by lra.
	easy.
Qed.

Theorem Z_state_pi_copy : forall n prfn prfm,
	((Z 0 1 PI) ⟷ X 1 n 0) ∝ 
	(cast 0 n prfn prfm (n ⇑ (Z 0 1 PI))).
Proof.
	intros.
	replace (PI)%R with (1 * PI)%R by lra.
	replace (1)%R with (INR 1)%R by reflexivity.
	rewrite Z_state_copy.
	easy.
Qed.

Theorem Z_state_0_copy : forall n prfn prfm,
	((Z 0 1 0) ⟷ X 1 n 0) ∝ 
	(cast 0 n prfn prfm (n ⇑ (Z 0 1 0))).
Proof.
	intros.
	replace (0)%R with (0 * PI)%R at 1 by lra.
	replace (0)%R with (INR 0)%R by reflexivity.
	rewrite Z_state_copy.
	replace (0 * PI)%R with (0)%R at 1 by lra.
	easy.
Qed.

Lemma Z_copy : forall n r prfn prfm, 
	(Z 1 1 (INR r * PI) ⟷ X 1 n 0) ∝
	X 1 n 0 ⟷ 
		(cast n n prfn prfm
			(n ⇑ (Z 1 1 (INR r * PI)))).
Proof.
	intros.
	assert (Z_copy_ind : (Z 1 1 (INR r * PI) ⟷ X 1 2 0) ∝
		X 1 2 0 ⟷ (Z 1 1 (INR r * PI) ↕ Z 1 1 (INR r * PI))).
	{ 
		prop_exists_nonzero (1); rewrite Mscale_1_l. 
		cbn.
		rewrite <- X_semantics_transpose, X_2_1_0_semantics.
		restore_dims.
		compute_matrix (Z_semantics 1 1 (INR r * PI) 
			⊗ Z_semantics 1 1 (INR r * PI)).
		rewrite <- Cexp_add, <- Rmult_plus_distr_r, 
			<- plus_INR, double_mult, mult_INR, 
			!INR_IZR_INZ, <- mult_IZR.
		rewrite Cexp_2nPI.
		lma'.
	} 
	eapply (cast_diagrams 1 (n * 1)).
	rewrite 2 cast_compose_distribute.
	simpl_casts.
	erewrite (@cast_compose_mid _ _ _ (n * 1)%nat _ _ (X 1 n 0)).
	rewrite cast_X, cast_contract, cast_id.
	induction n; [ | destruct n].
	- simpl.
		prop_exists_nonzero 1.
		rewrite Mscale_1_l.
		prep_matrix_equivalence.
		cbn.
		unfold X_semantics.
		rewrite kron_n_1, 2!Mmult_1_l by auto_wf. 
		by_cell; cbn;
		rewrite Cexp_0;
		lca.
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
	(X 1 1 (INR r * PI) ⟷ Z 1 n 0) ∝
	Z 1 n 0 ⟷ 
		(cast n n
			prfn prfm
			(n ⇑ (X 1 1 (INR r * PI)))).
Proof.
	intros.
	apply colorswap_diagrams.
	simpl.
	rewrite cast_colorswap.
	rewrite n_stack_colorswap.
	simpl.
	apply Z_copy.
Qed.

Lemma Z_0_copy : forall n prfn prfm, 
	(Z 1 1 0 ⟷ X 1 n 0) ∝
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
	(Z 1 1 PI ⟷ X 1 n 0) ∝
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
	(X 1 1 0 ⟷ Z 1 n 0) ∝
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
	(X 1 1 PI ⟷ Z 1 n 0) ∝
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