Require Import CoreData.CoreData.
Require Import CoreRules.ZRules.
Require Import CoreRules.WireRules.
Require Import CoreRules.CastRules.
Require Import CoreRules.StackComposeRules.
Require Import CoreRules.CoreAutomation.
Require Export CoreRules.ZRules.

Lemma INR_PI_EXP : forall (r : nat),
	Cexp (INR r * PI) = 1 \/ Cexp (INR r * PI) = -1.
Proof.
	intros.
	dependent induction r.
	- simpl.
		rewrite Rmult_0_l.
		left.
		apply Cexp_0.
	-	rewrite S_O_plus_INR.
		rewrite Rmult_plus_distr_r.
		rewrite Rmult_1_l.
		rewrite Rplus_comm.
		rewrite Cexp_plus_PI.
		destruct IHr.
		+ rewrite H; right; lca.
		+ rewrite H; left; lca.
Qed.

Theorem X_state_copy : forall (r n : nat),
	(X 0 1 ((INR r) * PI) ⟷ Z 1 n 0) ∝
	Cast 0%nat n (mult_n_O _) (eq_sym (mult_1_r _)) (n ⇑ (X 0 1 ((INR r) * PI))).
Proof.
	intros.
	assert (X_state_copy_ind : (X 0 1 (INR r * PI) ⟷ Z 1 2 0) ∝
		X 0 1 (INR r * PI) ↕ X 0 1 (INR r * PI)).
	{ 
		prop_exists_nonzero (/ √ 2); Msimpl; simpl.
		unfold X_semantics; unfold Z_semantics.
		simpl. solve_matrix.
		all: autorewrite with Cexp_db.
		all: destruct (INR_PI_EXP r); rewrite H.
		all: try lca; C_field_simplify; try lca.
		all: nonzero.
	} 
	induction n; [| destruct n].
	- simpl. 
		simpl_casts.
		prop_exists_nonzero (√ 2); Msimpl; simpl.
		unfold X_semantics; unfold Z_semantics.
		simpl.
		solve_matrix.
		destruct (INR_PI_EXP r); rewrite H.
		all: autorewrite with Cexp_db.
		all: C_field_simplify; try lca; try nonzero.
	-	simpl. 
		rewrite Z_0_is_wire.
		simpl_casts.
		rewrite ZX_Stack_Empty_r.
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
		rewrite Grow_Z_Top_Right.
		rewrite <- ZX_Compose_assoc.
		rewrite IHn.
		rewrite <- (ZX_Stack_Compose_distr
			(X 0 1 (INR r * PI)) (Z 1 2 0) (n ⇑ X 0 1 (INR r * PI)) (nWire (n * 1))).
		rewrite X_state_copy_ind.
		cleanup_zx.
		rewrite (ZX_Stack_assoc (X 0 1 (INR r * PI)) (X 0 1 (INR r * PI))).
		simpl_casts.
		easy.
		Unshelve.
		all: lia.
Qed.

Theorem Z_state_copy : forall (r n : nat),
	(Z 0 1 ((INR r) * PI) ⟷ X 1 n 0) ∝
	Cast 0%nat n (mult_n_O _) (eq_sym (mult_1_r _)) (n ⇑ (Z 0 1 ((INR r) * PI))).
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

Theorem X_PI_copy : forall n,
	((X 0 1 PI) ⟷ Z 1 n 0) ∝ 
	(Cast 0 n (mult_n_O _) (eq_sym (mult_1_r _)) (n ⇑ (X 0 1 PI))).
Proof.
	intros.
	replace (PI)%R with (1 * PI)%R by lra.
	replace (1)%R with (INR 1)%R by reflexivity.
	rewrite X_state_copy.
	easy.
Qed.

Theorem X_0_copy : forall n,
	((X 0 1 0) ⟷ Z 1 n 0) ∝ 
	(Cast 0 n (mult_n_O _) (eq_sym (mult_1_r _)) (n ⇑ (X 0 1 0))).
Proof.
	intros.
	replace (0)%R with (0 * PI)%R at 1 by lra.
	replace (0)%R with (INR 0)%R by reflexivity.
	rewrite X_state_copy.
	replace (0 * PI)%R with (0)%R at 1 by lra.
	easy.
Qed.

Theorem Z_PI_copy : forall n,
	((Z 0 1 PI) ⟷ X 1 n 0) ∝ 
	(Cast 0 n (mult_n_O _) (eq_sym (mult_1_r _)) (n ⇑ (Z 0 1 PI))).
Proof.
	intros.
	replace (PI)%R with (1 * PI)%R by lra.
	replace (1)%R with (INR 1)%R by reflexivity.
	rewrite Z_state_copy.
	easy.
Qed.

Theorem Z_0_copy : forall n,
	((Z 0 1 0) ⟷ X 1 n 0) ∝ 
	(Cast 0 n (mult_n_O _) (eq_sym (mult_1_r _)) (n ⇑ (Z 0 1 0))).
Proof.
	intros.
	replace (0)%R with (0 * PI)%R at 1 by lra.
	replace (0)%R with (INR 0)%R by reflexivity.
	rewrite Z_state_copy.
	replace (0 * PI)%R with (0)%R at 1 by lra.
	easy.
Qed.
