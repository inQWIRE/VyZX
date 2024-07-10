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
		prop_exists_nonzero (/ (√ 2)%R); Msimpl; simpl.
		unfold X_semantics; unfold Z_semantics.
		simpl. solve_matrix.
		all: autorewrite with Cexp_db.
		all: destruct (INR_pi_exp r); rewrite H.
		all: try lca; C_field_simplify; try lca.
		all: nonzero.
	} 
	induction n; [| destruct n].
	- simpl. 
		simpl_casts.
		prop_exists_nonzero (√ 2)%R; Msimpl; simpl.
		unfold X_semantics; unfold Z_semantics.
		simpl.
		solve_matrix.
		destruct (INR_pi_exp r); rewrite H.
		all: autorewrite with Cexp_db.
		all: C_field_simplify; try lca; try nonzero.
	-	simpl. 
		rewrite Z_0_is_wire.
		simpl_casts.
		rewrite stack_empty_r.
		simpl_casts.
		cleanup_zx.
		easy.
	- eapply (cast_diagrams (S (S n) * 0) (S (S n) * 1)).
		rewrite cast_contract.
		rewrite cast_compose_distribute.
		simpl_casts.
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
		simpl_casts.
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
		prop_exists_nonzero (1); Msimpl; simpl.
		unfold X_semantics; unfold Z_semantics.
		simpl. solve_matrix.
		all: autorewrite with Cexp_db.
		all: destruct (INR_pi_exp r); rewrite H.
		all: try lca; C_field_simplify; try lca.
		all: nonzero.
	} 
	eapply (cast_diagrams 1 (n * 1)).
	rewrite 2 cast_compose_distribute.
	simpl_casts.
	erewrite (@cast_compose_mid _ _ _ (n * 1)%nat _ _ (X 1 n 0)).
	simpl_casts.
	induction n; [ | destruct n].
	- simpl.
		solve_prop 1.
	- simpl.
		repeat rewrite X_0_is_wire.
		cleanup_zx.
		simpl_casts.
		easy.
	- simpl.
		rewrite grow_X_top_right.
		simpl in IHn.
		rewrite <- compose_assoc.
		rewrite IHn.
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
		simpl_casts.
		easy.
	Unshelve.
	all: lia.
Qed.

Lemma Z_X_pi_comm : forall α,
	Z 1 1 PI ⟷ X 1 1 α ∝
	X 1 1 (-α) ⟷ Z 1 1 PI.
Proof.
	intros.
	prop_exists_nonzero (Cexp α).
	repeat rewrite ZX_semantic_equiv.
	Msimpl.
	simpl.
	Msimpl.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.
	restore_dims.
	repeat rewrite <- (Mmult_assoc ⟨-∣).
	repeat rewrite <- (Mmult_assoc ⟨+∣).
	repeat rewrite <- (Mmult_assoc ⟨1∣).
	repeat rewrite <- (Mmult_assoc ⟨0∣).
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	rewrite Cexp_PI.
	replace (-1 * - / (√ 2)%R) with (/ (√2)%R) by lca.
	rewrite Mscale_plus_distr_r.
	repeat rewrite Mscale_assoc.
	replace (-1 * (Cexp α * - / (√ 2)%R)) with (Cexp α * / (√2)%R) by lca.
	replace (-1 * / (√ 2)%R) with (-/(√2)%R) by lca.
	repeat rewrite Mscale_plus_distr_r.
	repeat rewrite Mscale_assoc.
	replace (Cexp α * Cexp (-α)) with C1.
	rewrite Cmult_1_l.
	lma.
	rewrite <- Cexp_add.
	rewrite Rplus_opp_r.
	rewrite Cexp_0.
	easy.
Qed.

Lemma X_Z_pi_comm : forall α,
	X 1 1 PI ⟷ Z 1 1 α ∝
	Z 1 1 (-α) ⟷ X 1 1 PI.
Proof.
	colorswap_of Z_X_pi_comm.
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



Lemma Z_0_copy_base : forall α, Z 1 1 0 ⟷ X 1 0 α ∝ X 1 0 (α).
Proof.
	intros.
	simpl.
	prop_exists_nonzero 1.
	simpl.
	unfold X_semantics, Z_semantics.
	simpl.
	solve_matrix.
	autorewrite with Cexp_db.
	lca.
Qed.

Lemma X_0_copy_base : forall α, X 1 1 0 ⟷ Z 1 0 α ∝ Z 1 0 (α).
Proof.
	intros.
	colorswap_of Z_0_copy_base.
Qed.


Lemma Z_pi_copy_base : forall α, Z 1 1 (INR 1 * PI) ⟷ X 1 0 α ∝ X 1 0 (-α).
Proof.
	intros.
	simpl.
	prop_exists_nonzero (Cexp α).
	simpl.
	rewrite Rmult_1_l.
	unfold X_semantics, Z_semantics.
	simpl.
	solve_matrix.
	autorewrite with Cexp_db.
	rewrite Cmult_plus_distr_l.
	rewrite Cmult_assoc.
	rewrite Cinv_r.
	lca.
	nonzero.
	field_simplify.
	autorewrite with Cexp_db.
	repeat rewrite <- Copp_mult_distr_l.
	field_simplify.
	lca.
	all:nonzero.
Qed.

Lemma X_pi_copy_base : forall α, X 1 1 (INR 1 * PI) ⟷ Z 1 0 α ∝ Z 1 0 (-α).
Proof.
	intros.
	colorswap_of Z_pi_copy_base.
Qed.

Lemma Z_0_copy : forall n α, 
	(Z 1 1 0 ⟷ X 1 n α) ∝
	X 1 n α.
Proof.
	intros.
	replace (α) with (α + 0+ 0)%R by lra.
	rewrite (@X_add_r 1%nat 0%nat n) at 1.
	rewrite <- compose_assoc.
	replace 0%R with (INR 0 * PI)%R at 01 by (simpl; lra).
	rewrite Z_copy at 1.
	simpl_casts.
	simpl.
	cleanup_zx.
	simpl_casts.
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (Z 1 1 (0 * PI)) (X 1 0 α) (Z 1 1 (0 * PI)) (X 1 n 0)).
	replace (0 * PI)%R with (INR 0 * PI)%R by easy.
	rewrite Z_copy.
	simpl.
	rewrite Rmult_0_l.
	rewrite Z_0_copy_base.
	rewrite <- (nwire_removal_r (X 1 0 _)).
	rewrite stack_compose_distr.
	rewrite <- compose_assoc.
	rewrite <- X_add_r.
	simpl_casts.
	simpl.
	cleanup_zx.
	rewrite nstack_is_nstack1.
	simpl_casts.
	cleanup_zx.
	easy.
Unshelve.
all: lia.
Qed.

Lemma Z_pi_copy : forall n α prfn prfm, 
	(Z 1 1 PI ⟷ X 1 n α) ∝
	X 1 n (-α) ⟷ 
		(cast n n prfn prfm
			(n ⇑ (Z 1 1 PI))).
Proof.
	intros.
	replace (α) with (α + 0+ 0)%R by lra.
	rewrite (@X_add_r 1%nat 0%nat n).
	rewrite <- compose_assoc.	
	replace (PI) with (INR 1 * PI)%R by (simpl; lra).
	rewrite Z_copy.
	simpl_casts.
	simpl.
	cleanup_zx.
	simpl_casts.
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (Z 1 1 (1 * PI)) (X 1 0 α) (Z 1 1 (1 * PI)) (X 1 n 0)).
	replace (1 * PI)%R with (INR 1 * PI)%R by easy.
	rewrite Z_copy.
	rewrite Z_pi_copy_base.
	rewrite <- (nwire_removal_r (X 1 0 _)).
	rewrite stack_compose_distr.
	rewrite <- compose_assoc.
	rewrite <- X_add_r.
	apply compose_simplify.
	apply X_simplify; lra.
	simpl.
	cleanup_zx.
	easy.
Unshelve.
all: lia.
Qed.


Lemma X_0_copy : forall n α, 
	(X 1 1 0 ⟷ Z 1 n α) ∝
	Z 1 n α.
Proof.
	intros.
	colorswap_of Z_0_copy.
Qed.

Lemma X_pi_copy : forall n α prfn prfm, 
	(X 1 1 PI ⟷ Z 1 n α) ∝
	Z 1 n (-α) ⟷ 
		(cast n n prfn prfm
			(n ⇑ (X 1 1 PI))).
Proof.
	intros.
	colorswap_of Z_pi_copy.
Qed.