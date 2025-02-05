Require Import CoreData.CoreData.
Require Import CoreRules.WireRules.
Require Import CoreRules.CastRules.
Require Import CoreRules.StackComposeRules.
Require Import CoreRules.CoreAutomation.
Require Export CoreRules.ZRules.
Require Export CoreRules.XRules.


Theorem X_state_copy : forall (r n : nat) prfn prfm,
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
		(* rewrite Mscale_inv by nonzero. *)
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
		simpl_casts.
		rewrite stack_empty_r.
		simpl_casts.
		cleanup_zx.
		zxrefl.
	  rewrite Rmult_1_r.
		rewrite Rinv_r by nonzero.
		reflexivity.
	- eapply (cast_diagrams_by (S (S n) * 0) (S (S n) * 1)).
		rewrite cast_contract.
		rewrite cast_compose_distribute.
		simpl_casts.
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

Theorem Z_state_copy : forall (r n : nat) prfn prfm,
	(Z 0 1 ((INR r) * PI) ⟷ X 1 n 0) 
	∝[(√2 * (/√2 ^ n))%R]
	cast 0%nat n prfn prfm (n ⇑ (Z 0 1 ((INR r) * PI))).
Proof.
	intros r n prfn prfm.
	colorswap_of (X_state_copy r n prfn prfm).
Qed.

Theorem X_state_pi_copy : forall n prfn prfm,
	((X 0 1 PI) ⟷ Z 1 n 0) ∝[(√2 * (/√2 ^ n))%R]
	(cast 0 n prfn prfm (n ⇑ (X 0 1 PI))).
Proof.
	intros.
	replace (PI)%R with (1 * PI)%R by lra.
	replace (1)%R with (INR 1)%R by reflexivity.
	zxrewrite X_state_copy.
	zxrefl.
Qed.

Theorem X_state_0_copy : forall n prfn prfm,
	((X 0 1 0) ⟷ Z 1 n 0) ∝[(√2 * (/√2 ^ n))%R]
	(cast 0 n prfn prfm (n ⇑ (X 0 1 0))).
Proof.
	intros.
	replace (0)%R with (0 * PI)%R at 1 by lra.
	replace (0)%R with (INR 0)%R by reflexivity.
	zxrewrite X_state_copy.
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
	zxrewrite Z_state_copy.
	zxrefl.
Qed.

Theorem Z_state_0_copy : forall n prfn prfm,
	((Z 0 1 0) ⟷ X 1 n 0) ∝[(√2 * (/√2 ^ n))%R]
	(cast 0 n prfn prfm (n ⇑ (Z 0 1 0))).
Proof.
	intros.
	replace (0)%R with (0 * PI)%R at 1 by lra.
	replace (0)%R with (INR 0)%R by reflexivity.
	zxrewrite Z_state_copy.
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
	simpl_casts.
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