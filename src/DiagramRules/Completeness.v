Require Import CoreData.
From QuantumLib Require Import Polar.

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
	(Z 0 1 (PI / 4) ↕ Z 1 2 0 ↕ Z 0 1 (PI / 4)) ⟷ 
	(X 2 1 0 ↕ X 2 1 0) ⟷
	(Z 1 1 (- PI / 2) ↕ (Z 1 0 (PI / 4))) ⟷
	(X 1 2 0) ⟷
	(Z 1 0 (PI / 4) ↕ Z 1 2 0 ↕ (Z 0 1 (PI / 4))) ⟷
	(— ↕ X 2 1 0) ⟷
	(— ↕ Z 1 0 (PI / 4)) ∝
	(X 1 1 (PI / 2)) ⟷
	(Z 1 1 (PI / 4)) ⟷
	(X 1 2 PI) ⟷ 
	(Z 1 0 (PI / 4) ↕ Z 1 2 0 ↕ (Z 0 1 (PI / 4))) ⟷
	(— ↕ X 2 1 0) ⟷
	(— ↕ Z 1 0 (PI / 4)).
Proof. (* solve matrix takes forever *)
Abort.

(* Harny completeness result *)
Definition GreenBox (a : C) : Matrix 2 2 :=
	fun x y => 
		match (x, y) with 
		| (0, 0) => 1
		| (1, 1) => a
		| _      => 0
		end.
Definition RedBox (a : C) : Matrix 2 2 :=
	hadamard × (GreenBox a) × hadamard.

Open Scope R.

Definition z (α β γ : R) : C := (cos (β / 2) * cos ((α + γ) / 2), (sin(β/2) * cos ((α - γ) / 2))).

Definition z_1 (α β γ : R) : C := (cos (β / 2) * sin ((α + γ) / 2), -(sin(β/2) * sin ((α - γ) / 2))).

Definition Harny_τ (l1 l2 l3 : R) := (1 - l2) * (l1 + l3) + (1 + l2) * (1 + l1 * l3).

Definition Harny_U (l1 l2 l3 : R) := (1 + l2) * (l1 * l3 - 1).

Definition Harny_S (l1 l2 l3 : R) := (1 - l2) * (l1 + l3) - (1 + l2) * (1 + l1 * l3).

Definition Harny_V (l1 l2 l3 : R) := (1 - l2) * (l1 - l3).

Definition Harny_T (l1 l2 l3 : R) := (Harny_τ l1 l2 l3) * (Harny_U l1 l2 l3 * Harny_U l1 l2 l3 - Harny_V l1 l2 l3 * Harny_V l1 l2 l3).


Print Rcase_abs.
Check Rcase_abs.

Definition Harny_σ1 (l1 l2 l3 : R) : C := (0, -(Harny_U l1 l2 l3 + Harny_V l1 l2 l3) * sqrt(Harny_S l1 l2 l3 / Harny_T l1 l2 l3)).

Definition Harny_σ2 (l1 l2 l3 : R) : C := (Harny_τ l1 l2 l3, sqrt(Harny_T l1 l2 l3 / Harny_S l1 l2 l3)) / (Harny_τ l1 l2 l3, -1 * sqrt(Harny_T l1 l2 l3 / Harny_S l1 l2 l3)).

Definition Harny_σ3 (l1 l2 l3 : R) : C := (0, -(Harny_U l1 l2 l3 - Harny_V l1 l2 l3) * sqrt(Harny_S l1 l2 l3 / Harny_T l1 l2 l3)).

Close Scope R.
Open Scope C.

(* Needs to have an explicit scalar k given which depends on all the above, see Harny paper for more details. *)
Lemma Harny_General_phases_color_swap : forall l1 l2 l3 : R,
	GreenBox l3 × RedBox l2 × GreenBox l1 = RedBox (Harny_σ3 l1 l2 l3) × GreenBox (Harny_σ2 l1 l2 l3) × RedBox (Harny_σ1 l1 l2 l3).
Proof.
	intros.
	unfold RedBox.
	unfold GreenBox.
Admitted.

(* Prior Harny rule can be used to prove this. *)
Lemma Harny_Completeness : forall α β γ, 
	Z 1 1 α ⟷ X 1 1 β ⟷ Z 1 1 γ ∝
	X 1 1 (get_arg (z α β γ) + get_arg (z_1 α β γ)) ⟷ 
	Z 1 1 (2) ⟷
	X 1 1 (get_arg (z α β γ) + get_arg (z_1 α β γ)).
Proof.
Admitted.
