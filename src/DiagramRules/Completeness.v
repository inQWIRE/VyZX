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
	◁ ⟷ Z 1 1 PI ⟷ ▷ ∝ ▷ ⟷ X 1 1 PI.
Proof. 
	prop_exists_nonzero 1.
	remember (Z 1 1 PI) as z.
	remember (X 1 1 PI) as x.
	simpl.
	rewrite zx_triangle_semantics, zx_triangle_left_semantics.
	Msimpl.
	rewrite Heqz, Heqx.
	rewrite z_1_1_pi_σz, x_1_1_pi_σx.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite <- (Mmult_assoc _ ∣0⟩).
	repeat rewrite <- (Mmult_assoc _ ∣1⟩).
	rewrite ket0_equiv.
	rewrite ket1_equiv.
	restore_dims.
	rewrite Z0_spec.
	rewrite X0_spec.
	rewrite Z1_spec.
	rewrite X1_spec.
	rewrite <- ket0_equiv.
	rewrite <- ket1_equiv.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_assoc.
	repeat rewrite <- (Mmult_assoc _ ∣0⟩).
	repeat rewrite <- (Mmult_assoc _ ∣1⟩).
	autorewrite with ketbra_mult_db.
	Msimpl.
	lma.
Qed.

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

Lemma WF_green_box : forall a, WF_Matrix (green_box a).
Proof.
	intros.
	unfold green_box, WF_Matrix.
	intros.
	destruct x.
	- destruct y.
		+ destruct H; contradict H; lia.
		+ easy.
	- destruct x.
		+ destruct y.
			* easy.
			* destruct y.
				-- destruct H; contradict H; lia.
				-- easy.
		+ easy.
Qed.

#[export] Hint Resolve WF_green_box : wf_db.

Lemma WF_red_box : forall a, WF_Matrix (red_box a).
Proof.
	intros.
	unfold red_box.
	auto with wf_db.
Qed.

Definition red_box_alt (a : C) : Square 2 :=
	fun x y => 
	match (x, y) with 
	| (0, 0) => (a + 1) / C2
	| (0, 1) => (1 - a) / C2
	| (1, 0) => (1 - a) / C2
	| (1, 1) => (a + 1) / C2
	| _      => 0
	end.

Lemma red_box_eq : forall a, red_box a = red_box_alt a.
Proof.
	intros.
	unfold red_box, red_box_alt, green_box.
	solve_matrix; C_field_simplify; try lca. 
	all: split; [apply C2_neq_0 | apply Csqrt2_neq_0 ].
Qed.


#[export] Hint Resolve WF_red_box : wf_db.


Open Scope C.

Definition harny_z (α β γ : R) : C := cos (β / 2) * cos ((α + γ) / 2) + (Ci * (sin(β/2) * cos ((α - γ) / 2))).

Definition harny_z_1 (α β γ : R) : C := cos (β / 2) * sin ((α + γ) / 2) + (Ci * (sin(β/2) * sin ((α - γ) / 2))).

Definition harny_τ (l1 l2 l3 : C) : C := (1 - l2) * (l1 + l3) + (1 + l2) * (1 + l1 * l3).

Definition harny_u (l1 l2 l3 : C) : C := (1 + l2) * (l1 * l3 - 1).

Definition harny_s (l1 l2 l3 : C) : C := (1 - l2) * (l1 + l3) - (1 + l2) * (1 + l1 * l3).

Definition harny_v (l1 l2 l3 : C) := (1 - l2) * (l1 - l3).

Definition harny_t (l1 l2 l3 : C) := 
  let τ := harny_τ l1 l2 l3 in 
  let u := harny_u l1 l2 l3 in  
  let v := harny_v l1 l2 l3 in  
  τ * (u * u - v * v).

Definition harny_σ1 (l1 l2 l3 : C) : C := 
  let u := harny_u l1 l2 l3 in
  let v := harny_v l1 l2 l3 in
  let s := harny_s l1 l2 l3 in
  let t := harny_t l1 l2 l3 in
  Ci * (-(u + v) * √(s / t)).

Definition harny_σ2 (l1 l2 l3 : C) : C := 
  let τ := harny_τ l1 l2 l3 in 
  let u := harny_u l1 l2 l3 in
  let v := harny_v l1 l2 l3 in
  let s := harny_s l1 l2 l3 in
  let t := harny_t l1 l2 l3 in
  (C1 * τ + Ci * √(t / s)) 
  / (C1 * τ + -Ci * √(t / s)).

Definition harny_σ3 (l1 l2 l3 : C) : C := 
  let u := harny_u l1 l2 l3 in
  let v := harny_v l1 l2 l3 in
  let s := harny_s l1 l2 l3 in
  let t := harny_t l1 l2 l3 in
  Ci * (-(u - v) * √(s / t)).

Definition harny_k (l1 l2 l3 : C) : C := 
  let s := harny_s l1 l2 l3 in 
  let τ := harny_τ l1 l2 l3 in 
  let t := harny_t l1 l2 l3 in 
  (2 * (s * τ + √((- s) * t)) / (s * τ * τ + t)).

#[export] Hint Unfold harny_k harny_s harny_t harny_u harny_v harny_z harny_z_1 harny_τ : harny_db.
#[export] Hint Unfold harny_σ1 harny_σ2 harny_σ3 : harny_σ_db.

Definition create_m (mx my mz mw : C) : (Matrix 2 2)
  := fun (x y : nat) => match x, y with
                      | 0, 0 => mx
                      | 0, 1 => my
                      | 1, 0 => mz
                      | 1, 1 => mw
                      | _, _ => C0
end.

Lemma WF_create_m : forall (mx my mz mw : C), WF_Matrix (create_m mx my mz mw).
Proof.
	intros.
	unfold create_m.
	unfold WF_Matrix.
	intros.
	destruct x.
	- destruct y. 
		+ destruct H; contradict H; lia.
		+ destruct y.
			* destruct H; contradict H; lia.
			* easy.
	- destruct x.
		+ destruct y.
			* destruct H; contradict H; lia.
			* destruct y.
				-- destruct H; contradict H; lia.
				-- easy.
		+ easy.
Qed.   

Lemma scale_create_m : forall (c mx my mz mw : C), c .* (create_m mx my mz mw) = create_m (c * mx) (c * my) (c * mz) (c * mw).
Proof.
	intros.
	unfold create_m.
	solve_matrix.
Qed.

Lemma solve_create_m : forall mx mx' my my' mz mz' mw mw', 
	mx = mx' -> my = my' -> mz = mz' -> mw = mw' ->
		create_m mx my mz mw = create_m mx' my' mz' mw'.
Proof.
	intros.
	subst.
	easy.
Qed.

Lemma solve_create_m' : forall mx mx' my my' mz mz' mw mw', 
	mx = mx' /\ my = my' /\ mz = mz' /\ mw = mw' ->
		create_m mx my mz mw = create_m mx' my' mz' mw'.
Proof.
	intros.
	destruct H; destruct H0; destruct H1.
	apply solve_create_m; easy.
Qed.

#[export] Hint Resolve WF_create_m : wf_db.


Lemma harny_simpl : forall l1 l2 l3,
  let σ1 := harny_σ1 l1 l2 l3 in
  let σ2 := harny_σ2 l1 l2 l3 in
  let σ3 := harny_σ3 l1 l2 l3 in
  let MX := ((C1 + σ3) * (C1 + σ1) + (C1 - σ3) * σ2 * (C1 - σ1)) in
  let MY := ((C1 + σ3) * (C1 - σ1) + (C1 - σ3) * σ2 * (C1 + σ1)) in
  let MZ := ((C1 - σ3) * (C1 + σ1) + (C1 + σ3) * σ2 * (C1 - σ1)) in
  let MW := ((C1 - σ3) * (C1 - σ1) + (C1 + σ3) * σ2 * (C1 + σ1)) in 
  C2 * C2 .* (red_box σ3 × green_box σ2 × red_box σ1) = create_m MX MY MZ MW.
Proof.
  intros.
	assert (WF_Matrix (C2 * C2 .* (red_box σ3 × green_box σ2 × red_box σ1))) as H0 by auto with wf_db.
  subst MX MY MZ MW.
  unfold red_box, green_box, create_m in *.
	prep_matrix_equality.
	unfold scale, Mmult in *.
	destruct x.
	- do 2 (destruct y; [simpl; C_field_simplify; [ easy | apply Csqrt2_neq_0 ] | ]).
		unfold WF_Matrix in H0; rewrite H0; [easy |  right; lia].
	- destruct x.
		do 2 (destruct y; [simpl; C_field_simplify; [ easy | apply Csqrt2_neq_0 ] | ]).
		unfold WF_Matrix in H0; rewrite H0; [easy |  right; lia].
		simpl; C_field_simplify; [ easy | apply Csqrt2_neq_0 ].
Qed.



Lemma harny_simpl_l : forall l1 l2 l3,
  C2 .* (green_box l3 × red_box l2 × green_box l1) = create_m (l2 + 1) ((1 - l2) * l1) (l3 * (1 - l2)) (l1 * (1 + l2) * l3).
Proof.
	intros.
	rewrite red_box_eq.
	unfold create_m, red_box_alt, green_box.
	solve_matrix; C_field_simplify; 
		try (split; [apply Csqrt2_neq_0 | apply C2_neq_0 ]);
		try lca.
Qed.

Definition harny_k_1_prop l1 l2 l3 := 
	let τ := harny_τ l1 l2 l3 in
  let σ1 := harny_σ1 l1 l2 l3 in
  let σ2 := harny_σ2 l1 l2 l3 in
  let σ3 := harny_σ3 l1 l2 l3 in
	/ C2 * ((σ1 + σ3) * (1 - σ2) + (1 + σ2) * (1 + (σ1 * σ3))) / (1 + l2).

Lemma harny_general_phases_color_swap : forall l1 l2 l3 : C,
  let k := harny_k l1 l2 l3 in
  let σ1 := harny_σ1 l1 l2 l3 in
  let σ2 := harny_σ2 l1 l2 l3 in
  let σ3 := harny_σ3 l1 l2 l3 in
	l2 <> - C1 ->
	k = harny_k_1_prop l1 l2 l3 ->
	k .* (green_box l3 × red_box l2 × green_box l1) = (red_box σ3 × green_box σ2 × red_box σ1) /\ k <> 0.
Proof.
  intros; split; [ | shelve].
  pose proof (harny_simpl l1 l2 l3) as Hr.
	pose proof (harny_simpl_l l1 l2 l3) as Hl.
  rewrite Mscale_inv in Hr; [ | shelve ].
  rewrite Mscale_inv in Hl; [ | shelve ].
	assert (forall k, WF_Matrix (k .* (green_box l3 × red_box l2 × green_box l1))) as WF_LHS by auto with wf_db.
	assert (WF_Matrix (red_box σ3 × green_box σ2 × red_box σ1)) as WF_RHS by auto with wf_db.
	subst σ1 σ2 σ3.
	rewrite Hl, Hr in *.
	autorewrite with scalar_move_db.
	rewrite 2 scale_create_m.
	apply solve_create_m.
	- rewrite H0.
		unfold harny_k_1_prop.
		C_field_simplify; [ | shelve].
		reflexivity.
	- autounfold with harny_σ_db.
		C_field_simplify.
		lca.
	- admit.
	-     
 

Admitted.

Transparent Z_semantics.

Lemma z_spider_to_green_box : forall α,
 ⟦ Z 1 1 α ⟧ = green_box (Cexp α).
Proof.
	intros.
	simpl.
	unfold Z_semantics, green_box.
	solve_matrix.
Qed.

Transparent X_semantics.

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
	remember (harny_k (Cexp α) (Cexp β) (Cexp γ)) as k.
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
	- rewrite Heqk.
		autounfold with harny_db.
		C_field_simplify.
		admit.
	- rewrite Heqk.
		repeat rewrite <- Mmult_assoc.
		rewrite harny_general_phases_color_swap.
Admitted.

