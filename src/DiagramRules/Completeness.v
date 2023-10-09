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

Open Scope R.

Definition harny_z (α β γ : R) : C := cos (β / 2) * cos ((α + γ) / 2) + (Ci * (sin(β/2) * cos ((α - γ) / 2))).

Definition harny_z_1 (α β γ : R) : C := cos (β / 2) * sin ((α + γ) / 2) + (Ci * (sin(β/2) * sin ((α - γ) / 2))).

Definition harny_τ (l1 l2 l3 : R) := (1 - l2) * (l1 + l3) + (1 + l2) * (1 + l1 * l3).

Definition harny_u (l1 l2 l3 : R) := (1 + l2) * (l1 * l3 - 1).

Definition harny_s (l1 l2 l3 : R) := (1 - l2) * (l1 + l3) - (1 + l2) * (1 + l1 * l3).

Definition harny_v (l1 l2 l3 : R) := (1 - l2) * (l1 - l3).

Definition harny_t (l1 l2 l3 : R) := (harny_τ l1 l2 l3) * (harny_u l1 l2 l3 * harny_u l1 l2 l3 - harny_v l1 l2 l3 * harny_v l1 l2 l3).

Definition harny_σ1 (l1 l2 l3 : R) : C := (0, -(harny_u l1 l2 l3 + harny_v l1 l2 l3) * sqrt(harny_s l1 l2 l3 / harny_t l1 l2 l3)).

Definition harny_σ2 (l1 l2 l3 : R) : C := (harny_τ l1 l2 l3, sqrt(harny_t l1 l2 l3 / harny_s l1 l2 l3)) / (harny_τ l1 l2 l3, -1 * sqrt(harny_t l1 l2 l3 / harny_s l1 l2 l3)).

Definition harny_σ3 (l1 l2 l3 : R) : C := (0, -(harny_u l1 l2 l3 - harny_v l1 l2 l3) * sqrt(harny_s l1 l2 l3 / harny_t l1 l2 l3)).

Definition harny_k l1 l2 l3 := 
  let S := harny_s l1 l2 l3 in 
  let τ := harny_τ l1 l2 l3 in 
  let T := harny_t l1 l2 l3 in 
  (8 * (S * τ + sqrt((- S) * T)) / (S * τ * τ + T)).

Close Scope R.
Open Scope C.

(* Needs to have an explicit scalar k given which depends on all the above, see harny paper for more details. *)
Lemma harny_general_phases_color_swap : forall l1 l2 l3 : R,
	green_box l3 × red_box l2 × green_box l1 = harny_k l1 l2 l3 .* (red_box (harny_σ3 l1 l2 l3) × green_box (harny_σ2 l1 l2 l3) × red_box (harny_σ1 l1 l2 l3)).
Proof.
	intros.
	unfold red_box.
	unfold green_box.
	solve_matrix.
	C_field_simplify.
	replace (C2 * C2 * C2 * l2 + C2 * C2 * C2) with ((C2 * C2) *(C2 * (l2 + C1))) by lca.
Admitted.

(* Prior harny rule can be used to prove this. *)
Lemma harny_completeness : forall α β γ, 
	Z 1 1 α ⟷ X 1 1 β ⟷ Z 1 1 γ ∝
	X 1 1 (get_arg (harny_z α β γ) + get_arg (harny_z_1 α β γ)) ⟷ 
	Z 1 1 (2) ⟷
	X 1 1 (get_arg (harny_z α β γ) + get_arg (harny_z_1 α β γ)).
Proof.
Admitted.
