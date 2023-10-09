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

Definition harny_t (l1 l2 l3 : R) := 
  let τ := harny_τ l1 l2 l3 in 
  let u := harny_u l1 l2 l3 in  
  let v := harny_v l1 l2 l3 in  
  τ * (u * u - v * v).

Definition harny_σ1 (l1 l2 l3 : R) : C := 
  let u := harny_u l1 l2 l3 in
  let v := harny_v l1 l2 l3 in
  let s := harny_s l1 l2 l3 in
  let t := harny_t l1 l2 l3 in
  Ci * (-(u + v) * sqrt(s / t)).

Definition harny_σ2 (l1 l2 l3 : R) : C := 
  let τ := harny_τ l1 l2 l3 in 
  let u := harny_u l1 l2 l3 in
  let v := harny_v l1 l2 l3 in
  let s := harny_s l1 l2 l3 in
  let t := harny_t l1 l2 l3 in
  (C1 * τ + Ci * sqrt(t / s)) 
  / (C1 * τ + -Ci * sqrt(t / s)).

Definition harny_σ3 (l1 l2 l3 : R) : C := 
  let u := harny_u l1 l2 l3 in
  let v := harny_v l1 l2 l3 in
  let s := harny_s l1 l2 l3 in
  let t := harny_t l1 l2 l3 in
  Ci * (-(u - v) * sqrt(s / t)).

Definition harny_k l1 l2 l3 := 
  let s := harny_s l1 l2 l3 in 
  let τ := harny_τ l1 l2 l3 in 
  let t := harny_t l1 l2 l3 in 
  (8 * (s * τ + sqrt((- s) * t)) / (s * τ * τ + t)).

Close Scope R.
Open Scope C.

(* Needs to have an explicit scalar k given which depends on all the above, see harny paper for more details. *)
Lemma harny_general_phases_color_swap : forall l1 l2 l3 : R,
  let k := harny_k l1 l2 l3 in
  let σ1 := harny_σ1 l1 l2 l3 in
  let σ2 := harny_σ2 l1 l2 l3 in
  let σ3 := harny_σ3 l1 l2 l3 in
	k .* (green_box l3 × red_box l2 × green_box l1) = (red_box σ3 × green_box σ2 × red_box σ1).
Proof.
	intros.
	unfold σ1, σ2, σ3.
	unfold harny_σ1, harny_σ2, harny_σ3.
	unfold harny_u, harny_v, harny_s, harny_τ, harny_t.
	unfold harny_u, harny_v, harny_s, harny_τ, harny_t.
	unfold red_box.
	unfold green_box.
	prep_matrix_equality.
	intros.
	destruct x.
	- destruct y.
		simpl.
		unfold Mmult; simpl.
		R_field_simplify.

	
Admitted.

Lemma z_spider_to_green_box : forall α,
 ⟦ Z 1 1 α ⟧ = green_box (Cexp α).
Proof.
	intros.
	simpl.
	unfold Z_semantics, green_box.
	solve_matrix.
Qed.

Lemma x_spider_to_red_box : forall α,
 ⟦ X 1 1 α ⟧ = red_box (Cexp α).
Proof.
	intros.
	simpl.
	unfold X_semantics.
	fold (⟦ Z 1 1 α ⟧).
	rewrite z_spider_to_green_box.
	unfold red_box.
	simpl.
	rewrite kron_1_l.
	easy.
	auto with wf_db.
Qed.

(* Prior harny rule can be used to prove this. *)
Lemma harny_completeness : forall α β γ, 
	Z 1 1 α ⟷ X 1 1 β ⟷ Z 1 1 γ ∝
	X 1 1 (get_arg (harny_z α β γ) + get_arg (harny_z_1 α β γ)) ⟷ 
	Z 1 1 (2 * get_arg ( Cmod (harny_z α β γ / harny_z_1 α β γ) + Ci)) ⟷
	X 1 1 (get_arg (harny_z α β γ) + get_arg (harny_z_1 α β γ)).
Proof.
	intros.
	remember (harny_z α β γ) as z.
	remember (harny_z_1 α β γ) as z_1.
	remember (harny_k α β γ) as k.
	prop_exists_nonzero (1%R / k).
	simpl.
	fold (⟦ Z 1 1 α ⟧).
	fold (⟦ X 1 1 β ⟧).
	fold (⟦ Z 1 1 γ ⟧).
	fold (⟦ X 1 1 (get_arg z + get_arg z_1 ) ⟧).
	fold (⟦ Z 1 1 (2 * get_arg ( Cmod (z / z_1) + Ci)) ⟧).
	fold (⟦ X 1 1 (get_arg z - get_arg z_1) ⟧).
	repeat rewrite z_spider_to_green_box.
	repeat rewrite x_spider_to_red_box.
	Search (_ .* _).
	assert (H : forall a {n m} (U V : Matrix n m), a <> C0 -> a .* U = V -> U = (C1 / a) .* V).
	{ 
		intros.
		rewrite <- H0.
		rewrite Mscale_assoc.
		replace ((C1 / a) * a) with (C1).
		lma.
		C_field_simplify.
		easy.
		easy.
	}
	apply H.
	admit.
	rewrite Heqk.
	repeat rewrite <- Mmult_assoc.
Admitted.
