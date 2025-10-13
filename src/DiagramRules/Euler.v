Require Import CoreRules.

Module EulerMatrix.

Section UnitaryFacts.


Local Open Scope matrix_scope.
Context (A : Square 2) (HAU : WF_Unitary A).

#[local] 
Hint Extern 0 (WF_Matrix A) => exact (proj1 HAU) : wf_db.
#[local] 
Hint Extern 0 (WF_Matrix (list2D_to_matrix _)) => 
  apply show_WF_list2D_to_matrix; reflexivity : wf_db.

(* @nocheck name *)
Lemma HAeq : A † × A = I 2.
Proof. exact (proj2 HAU). Qed.
(* @nocheck name *)
Lemma HAeq' : A × A † = I 2.
Proof.
  rewrite <- (Matrix.adjoint_involutive _ _ A) at 1.
  apply adjoint_unitary, HAU.
Qed.

Let a := A O O.

Let b := A O (S O).

Let c := A (S O) O.

Let d := A (S O) (S O).

(* @nocheck name *)
Lemma Minverse_Minv {n} (B : Square n) : WF_Matrix B ->
  Determinant B <> 0 -> 
  Minv B (Minverse B).
Proof.
  intros HB HDB.
  split.
  - now apply Mmult_Minverse_r.
  - now apply Mmult_Minverse_l.
Qed.
Lemma unitary_rw {n} (B : Square n) : WF_Unitary B -> B † × B = I n.
Proof. 
  now intros [].
Qed.
Lemma unitary_rw' {n} (B : Square n) : WF_Unitary B -> B × B † = I n.
Proof.
  intros HB.
  rewrite <- (Matrix.adjoint_involutive _ _ B) at 1.
  now apply unitary_rw, adjoint_unitary.
Qed.
(* @nocheck name *)
Lemma Unitary_adjoint_Minv {n} (B : Square n) : WF_Unitary B -> 
  Minv B (B †).
Proof.
  intros HB.
  split.
  - now apply unitary_rw'.
  - now apply unitary_rw.
Qed.
(* @nocheck name *)
Lemma Unitary_Determinant_mod_1 {n} (B : Square n) : WF_Unitary B -> 
  Cmod (Determinant B) = 1.
Proof.
  intros HB.
  pose proof (proj1 HB) as HBWF.
  pose proof (unitary_rw _ HB) as HDet%(f_equal Determinant).
  rewrite <- Determinant_multiplicative, <- Determinant_adjoint, Det_I in HDet.
  unfold Cmod.
  transitivity (√ fst ((Determinant B) ^* * Determinant B)); [f_equal; cbn; lra|].
  rewrite HDet.
  cbn.
  apply sqrt_1.
Qed.
(* @nocheck name *)
Lemma Unitary_Determinant_nonzero {n} (B : Square n) : WF_Unitary B -> 
  Determinant B <> 0.
Proof.
  intros HB%Unitary_Determinant_mod_1.
  intros Hdet.
  rewrite Hdet, Cmod_R in HB.
  rewrite Rabs_right in HB by lra.
  lra.
Qed.
(* @nocheck name *)
Lemma Cmod_1_minus_Cexp θ : Cmod (1 - Cexp θ) = √ (2 - 2 * cos θ).
Proof.
  unfold Cmod.
  f_equal.
  cbn.
  autorewrite with R_db.
  pose proof sin2_cos2 θ as H.
  rewrite 2!Rsqr_pow2 in H.
  lra.
Qed.

(* @nocheck name *)
Lemma Aadj_eq_adjugate : A † = Minverse A.
Proof.
  apply (Minv_unique _ A); auto_wf.
  - now apply Unitary_adjoint_Minv.
  - apply Minverse_Minv; [auto_wf|].
    now apply Unitary_Determinant_nonzero.
Qed.


Local Notation DA := (Determinant A).

(* @nocheck name *)
Lemma Det_2 : DA = a * d - b * c.
Proof.
  cbn.
  fold a b c d.
  lca.
Qed.

(* @nocheck name *)
Lemma DA_mod_1 : Cmod DA = 1.
Proof.
  now apply Unitary_Determinant_mod_1.
Qed.

(* @nocheck name *)
Lemma DA_nonzero : DA <> 0.
Proof.
  now apply Unitary_Determinant_nonzero.
Qed.

Import Polar.
(* @nocheck name *)
Lemma DA_eq_exp_arg : DA = Cexp (get_arg DA).
Proof.
  rewrite <- (rect_to_polar_to_rect DA) at 1 by apply DA_nonzero.
  unfold polar_to_rect, rect_to_polar.
  cbn [fst snd].
  rewrite DA_mod_1.
  ring.
Qed.

(* @nocheck name *)
Lemma A_to_abcd : 
  A = list2D_to_matrix [[a;b]; [c;d]].
Proof.
  prep_matrix_equivalence.
  by_cell; reflexivity.
Qed.

(* @nocheck name *)
Lemma A_Minverse_eq : 
  Minverse A = / DA .* list2D_to_matrix [[d; -b];[-c;a]].
Proof.
  unfold Minverse.
  f_equal.
  prep_matrix_equivalence.
  by_cell; cbn; subst a b c d; lca.
Qed.

(* @nocheck name *)
Lemma A_decomp : 
  A = list2D_to_matrix [[a;b]; [- DA * b^*; DA * a^*]].
Proof.
  rewrite A_to_abcd at 1.
  f_equal.
  f_equal.
  f_equal.
  pose proof (Aadj_eq_adjugate) as HAadjeq.
  rewrite A_Minverse_eq in HAadjeq.
  rewrite <- mat_equiv_eq_iff, mat_equiv_iff_conj in HAadjeq by auto_wf.
  unfold scale, Matrix.adjoint in HAadjeq.
  set (DA' := DA) in *.
  cbn -[DA'] in HAadjeq.
  fold a b c d in HAadjeq.
  destruct HAadjeq as (Ha & _ & Hb & _).
  rewrite Ha, Hb.
  f_equal; [|f_equal]; C_field;
  apply DA_nonzero.
Qed.

Lemma c_proj_eq_iff : forall (c d : C), c = d <-> fst c = fst d /\ snd c = snd d.
Proof. intros [] []; apply pair_equal_spec. Qed.
Lemma a_b_sqr' : a * a ^* + b * b ^* = C1.
Proof.
  generalize (unitary_rw' _ HAU).
  rewrite <- mat_equiv_eq_iff, mat_equiv_iff_conj by auto_wf.
  cbn.
  unfold Matrix.adjoint.
  fold a b c d.
  Csimpl.
  now intros [].
Qed.
Lemma c_proj_neq_iff : forall (c d : C), 
  c <> d <-> fst c <> fst d \/ snd c <> snd d.
Proof. intros ? ?; rewrite c_proj_eq_iff; lra. Qed.
Lemma a_b_sqr : a ^* * a + b ^* * b = C1.
Proof.
  generalize (unitary_rw' _ HAU).
  rewrite <- mat_equiv_eq_iff, mat_equiv_iff_conj by auto_wf.
  cbn.
  unfold Matrix.adjoint.
  fold a b c d.
  Csimpl.
  intros [H%(f_equal Cconj) _].
  rewrite c_proj_eq_iff in *.
  cbn in *.
  lra.
Qed.


(* @nocheck name *)
Lemma Cmod_1_minus_Cexp_alt θ : Cmod (1 - Cexp θ) = (2 * Rabs (sin (θ/2)))%R.
Proof.
  replace θ with (2 * (θ/2))%R at 1 by lra.
  rewrite Cmod_Cexp_alt.
  rewrite Cmod_mult, 2 Cmod_R, Rabs_right by lra.
  reflexivity.
Qed.

(* @nocheck name *)
Lemma Cmod_1_plus_Cexp_alt θ : Cmod (1 + Cexp θ) = Rmult 2 (Rabs (cos (θ/2))).
Proof.
  rewrite <- (Copp_involutive (Cexp θ)).
  rewrite <- Cminus_unfold.
  rewrite <- Cexp_minus_PI.
  rewrite Cmod_1_minus_Cexp_alt.
  rewrite <- sin_shift.
  rewrite <- (Rabs_Ropp (sin (_ - _))).
  rewrite <- sin_neg.
  do 3 f_equal.
  lra.
Qed.

(* @nocheck name *)
Lemma Rinv_pos r : 0 <= r -> 0 <= /r.
Proof.
  intros Hr.
  destruct (Req_dec r 0) as [->|].
  - now rewrite Rinv_0.
  - apply Rlt_le.
    apply Rinv_0_lt_compat.
    lra.
Qed.

(* @nocheck name *)
Lemma Rmult_div' r1 r2 r3 r4 : 
  (r1 / r2 * (r3 / r4))%R = (r1 * r3 / (r2 * r4))%R.
Proof.
  destruct (Req_dec r2 0) as [->|];
  [|destruct (Req_dec r4 0) as [->|]];
  [rewrite 1?Rmult_0_l, 1?Rmult_0_r, 2 Rdiv_0_r; lra..|].
  now apply Rmult_div.
Qed.


(* @nocheck name *)
Lemma ZXZ_semantics_base α β γ :
  ⟦ Z 1 1 α ⟷ X 1 1 β ⟷ Z 1 1 γ ⟧ = 
  list2D_to_matrix 
    [[(1 + Cexp β) / 2; Cexp α * (1 - Cexp β) / 2];
     [(Cexp γ * (1 - Cexp β)) / 2; (Cexp γ * Cexp α * (1 + Cexp β)) / 2]].
Proof.
  prep_matrix_equivalence.
  by_cell; cbn; Csimpl;
  unfold kron; cbn; C_field; lca.
Qed.
(* @nocheck name *)
Lemma Cexp_get_arg_eq_div (z : C) : z <> 0 ->
  Cexp (get_arg z) = z / Cmod z.
Proof.
  intros Hc.
  C_field; [|rewrite c_proj_eq_iff; simpl; rewrite Cmod_eq_0_iff; tauto].
  rewrite Cmult_comm. 
  apply (rect_to_polar_to_rect z), Hc.
Qed.

(* @nocheck name *)
Definition BalZ α := 
  (Cexp α .* Z 1 1 (- 2 * α))%ZX.

(* @nocheck name *)
Lemma BalZ_semantics α : 
  ⟦ BalZ α ⟧ = list2D_to_matrix [[Cexp α;C0];[C0;Cexp(-α)]].
Proof.
  unfold BalZ.
  rewrite zx_scale_semantics.
  prep_matrix_equivalence.
  unfold scale.
  by_cell; cbn; rewrite <- 1?Cexp_add; 
  [lca..|f_equal; lra].
Qed.

(* @nocheck name *)
Definition BalX α :=
  (Cexp α .* X 1 1 (- 2 * α))%ZX.

(* @nocheck name *)
Lemma BalX_semantics α : 
  ⟦ BalX α ⟧ = list2D_to_matrix [[RtoC (cos α);Ci * sin α];[Ci * sin α;RtoC (cos α)]].
Proof.
  prep_matrix_equivalence.
  unfold BalX.
  rewrite zx_scale_semantics.
  unfold scale; by_cell; cbn; Csimpl; unfold kron; cbn;
  group_radicals;
  repeat field_simplify_eq [ Csqrt2_sqrt Csqrt2_inv Ci2]; try solve [nonzero | trivial];
  rewrite <- 1? Copp_mult_distr_l, <- Cexp_add;
  replace ((-2 * α) + α)%R with (-α)%R by lra;
  unfold Cexp; rewrite sin_neg, cos_neg; lca.
Qed.

(* @nocheck name *)
Lemma Bal_ZXZ_semantics_base_alt α β γ :
  ⟦ BalZ γ ⟷ BalX β ⟷ BalZ α ⟧ = 
  list2D_to_matrix 
    [[Cexp (α+γ) * cos β; Ci * Cexp (α-γ) * sin β];
     [Ci * Cexp (-α+γ) * sin β; Cexp (-α-γ) * cos β]].
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite 2 BalZ_semantics, BalX_semantics.
  by_cell; cbn; Csimpl;
  rewrite 1?Rminus_unfold, Cexp_add; lca.
Qed.

Definition arg (z : C) := if Ceq_dec z 0 then 0%R else get_arg z.

Lemma arg_mod_decomp z : z = Cexp (arg z) * Cmod z.
Proof.
  unfold arg.
  destruct Ceq_dec.
  - subst z.
    rewrite Cmod_0.
    lca.
  - rewrite Cexp_get_arg_eq_div by auto.
    C_field.
    apply RtoC_neq.
    now rewrite Cmod_eq_0_iff.
Qed.

Local Ltac lca' :=
  rewrite ?c_proj_eq_iff, ?c_proj_neq_iff in *;
  cbn;
  lra.

Local Ltac nca' :=
  rewrite ?c_proj_eq_iff, ?c_proj_neq_iff in *;
  cbn;
  nra.

(* @nocheck name *)
Lemma arg_Rmult r z : 0 < r -> 
  arg (z * r) = arg z.
Proof.
  intros Hr.
  unfold arg.
  assert (z * r = 0 <-> z = 0) by nca'.
  do 2 destruct Ceq_dec; try solve [exfalso; firstorder].
  easy.
  rewrite Cmult_comm.
  now apply get_arg_Rmult.
Qed.

Lemma arg_mod_inj : forall c d, 
  Cmod c = Cmod d -> arg c = arg d -> 
  c = d.
Proof.
  intros x y Hmod Harg.
  rewrite (arg_mod_decomp x), (arg_mod_decomp y).
  congruence.
Qed.

Lemma arg_mod_inj' : forall c r α, 
  Cmod c = r -> Cexp (arg c) = Cexp α -> 
  c = Cexp α * r.
Proof.
  intros x r α Hmod Harg.
  rewrite (arg_mod_decomp x).
  congruence.
Qed.


Lemma mod_a : 0 <= Cmod a <= 1.
Proof.
  split; [apply Cmod_ge_0|].
  pose proof a_b_sqr as Hab%(f_equal fst).
  rewrite <- 2 Cmod_sqr in Hab.
  cbn in Hab.
  nra.
Qed.

Lemma mod_b : 0 <= Cmod b <= 1.
Proof.
  split; [apply Cmod_ge_0|].
  pose proof a_b_sqr as Hab%(f_equal fst).
  rewrite <- 2 Cmod_sqr in Hab.
  cbn in Hab.
  nra.
Qed.
(* @nocheck name *)
Lemma Cmod_eq_sqrt_fst z : Cmod z = √ (fst (z ^* * z)).
Proof.
  unfold Cmod.
  f_equal.
  cbn. 
  lra.
Qed.
(* @nocheck name *)
Lemma Cmod_sqr_fst z : (Cmod z ^ 2)%R = fst (z ^* * z).
Proof.
  rewrite <- Cmod_sqr.
  cbn; lra.
Qed.
Lemma mod_a_eq : Cmod a = √ (1 - Cmod b ^ 2).
Proof.
  rewrite Cmod_eq_sqrt_fst.
  pose proof a_b_sqr as Hab.
  rewrite Cmod_sqr_fst.
  replace (1 - (fst (b ^* * b)%C))%R with (fst (1 - b^* * b)) by (cbn; lra).
  f_equal.
  rewrite <- Hab.
  cbn; lra.
Qed.
Lemma mod_b_eq : Cmod b = √ (1 - Cmod a ^ 2).
Proof.
  rewrite Cmod_eq_sqrt_fst.
  pose proof a_b_sqr as Hab.
  rewrite Cmod_sqr_fst.
  replace (1 - (fst (a ^* * a)%C))%R with (fst (1 - a^* * a)) by (cbn; lra).
  f_equal.
  rewrite <- Hab.
  cbn; lra.
Qed.

Lemma and_by_left (P Q : Prop) : P -> (P -> Q) -> P /\ Q.
Proof.
  firstorder.
Qed.

Lemma euler_decomposition_base : DA = C1 -> 
  let β := acos (Cmod a) in 
  let α := ((arg a + arg b - PI/2) / 2)%R in 
  let γ := (arg a - α)%R in 
  A = 
  list2D_to_matrix 
    [[Cexp (α+γ) * cos β; Ci * Cexp (α-γ) * sin β];
     [Ci * Cexp (-α+γ) * sin β; Cexp (-α-γ) * cos β]].
Proof.
  intros HDA β α γ.
  assert (Cmod_a : Cmod a = cos β).
  1: {
    unfold β.
    rewrite cos_acos; [reflexivity|].
    pose proof mod_a; lra.
  }
  assert (Cmod_b : Cmod b = sin β).
  1: {
    unfold β.
    rewrite sin_acos by (pose mod_a; lra).
    rewrite mod_b_eq.
    now rewrite Rsqr_pow2.
  }
  rewrite A_decomp.
  rewrite HDA, <- Copp_mult_distr_l, 2 Cmult_1_l.
  prep_matrix_equivalence.
  apply mat_equiv_iff_conj.
  cbn.
  apply and_by_left; [|intros Ha; apply and_by_left; 
    [|intros Hb; split; [|split; [|easy]]]].
  - apply arg_mod_inj'; [easy|].
    f_equal.
    unfold γ, α.
    lra.
  - rewrite <- Cexp_PI2, <- Cexp_add.
    apply arg_mod_inj'; [easy|].
    f_equal.
    unfold γ, α.
    lra.
  - rewrite Hb.
    replace (α - γ)%R with (- (- α + γ))%R by lra.
    rewrite <- Cexp_conj_neg.
    lca.
  - rewrite Ha.
    replace (- α - γ)%R with (- (α + γ))%R by lra.
    rewrite <- Cexp_conj_neg.
    lca.
Qed.

End UnitaryFacts.

Import Polar.
(* @nocheck name *)
Lemma euler_decomposition_Bal (A : Square 2) (HA : WF_Unitary A) : 
  let DA := Determinant A in 
  let A' := (/ Cexp (get_arg DA / 2) .* A)%M in 
  let a := A' 0%nat 0%nat in let b := A' 0%nat 1%nat in 
  
  let α := ((arg a + arg b - PI/2) / 2)%R in 
  let β := acos (Cmod a) in 
  let γ := (arg a - α)%R in 
  A = ⟦ Cexp (get_arg DA / 2) .* (BalZ γ ⟷ BalX β ⟷ BalZ α) ⟧.
Proof.
  intros DA A' a b α β γ.
  rewrite zx_scale_semantics.
  rewrite Bal_ZXZ_semantics_base_alt.
  transitivity (Cexp (get_arg DA / 2) .* A')%M.
  1: {
    unfold A'.
    rewrite Mscale_assoc.
    rewrite Cinv_r by nonzero.
    now rewrite Mscale_1_l.
  }
  f_equal.
  apply euler_decomposition_base.
  - apply scale_unitary; [easy|].
    rewrite <- Cexp_neg, Cexp_conj_neg.
    rewrite <- Cexp_add, <- Cexp_0.
    f_equal; lra.
  - subst A'. 
    rewrite Determinant_scalar.
    (* fold DA. *)
    rewrite DA_eq_exp_arg by auto.
    rewrite <- Cexp_neg.
    cbn [Cpow].
    rewrite Cmult_1_r, <- Cexp_add, <- Cexp_add, <- Cexp_0.
    fold DA.
    f_equal; lra.
Qed.

(* @nocheck name *)
Lemma euler_decomposition_ZXZ_base (A : Square 2) (HA : WF_Unitary A) : 
  let DA := Determinant A in 
  let A' := (/ Cexp (get_arg DA / 2) .* A)%M in 
  let a := A' 0%nat 0%nat in let b := A' 0%nat 1%nat in 
  
  let α := ((arg a + arg b - PI/2) / 2)%R in 
  let β := acos (Cmod a) in 
  let γ := (arg a - α)%R in 
  A = ⟦ Cexp (get_arg DA / 2 + α + β + γ) .* 
    (Z 1 1 (-2 * γ) ⟷ X 1 1 (- 2 * β) ⟷ Z 1 1 (-2 * α)) ⟧.
Proof.
  intros. 
  rewrite (euler_decomposition_Bal A HA).
  fold DA A' a b α β γ.
  change (⟦ ?l ⟧ = ⟦ ?r ⟧) with (l ∝= r).
  unfold BalZ, BalX.
  distribute_zxscale.
  apply zx_scale_simplify_eq_l.
  rewrite <- 3 Cexp_add.
  f_equal; lra.
Qed.


(* @nocheck name *)
Lemma Cexp_get_arg_mult c d : c <> C0 -> d <> C0 -> 
  Cexp (get_arg (c * d)) = Cexp (get_arg c + get_arg d).
Proof.
  intros Hc Hd.
  rewrite Cexp_add.
  rewrite 3 Cexp_get_arg_eq_div by (easy || now apply Cmult_nonzero_iff).
  rewrite Cmod_mult.
  unfold Cdiv.
  rewrite RtoC_mult, Cinv_mult_distr.
  ring.
Qed.


(* @nocheck name *)
Lemma euler_decomposition_ZXZ_step2 (A : Square 2) (HA : WF_Unitary A) : 
  let DA := Determinant A in 
  let A' := (/ Cexp (get_arg DA / 2) .* A)%M in 
  let a := A' 0%nat 0%nat in let b := A' 0%nat 1%nat in 
  
  let α := (PI/2 - arg a - arg b)%R in 
  let β := (-2 * acos (Cmod a))%R in 
  let γ := ( - α - 2 * arg a)%R in 
  let δ := (get_arg DA / 2 - (α + β + γ) / 2)%R in 
  A = ⟦ Cexp δ .* 
    (Z 1 1 γ ⟷ X 1 1 β ⟷ Z 1 1 α) ⟧.
Proof.
  intros. 
  rewrite (euler_decomposition_ZXZ_base A HA).
  fold DA A' a b.
  set (α' := ((arg a + arg b - PI/2) / 2)%R).
  set (β' := acos (Cmod a)%R).
  set (γ' := (arg a - α')%R).
  repeat match goal with
  | |- @eq R _ _ => idtac
  | _ => f_equal
  end;
  unfold δ, γ, α, β, γ', α', β';
  lra.
Qed.

(* @nocheck name *)
Definition euler_ZXZ_α (A : Square 2) : R :=
  Eval cbv zeta in 
  let DA := Determinant A in 
  let A' := (/ Cexp (get_arg DA / 2) .* A)%M in 
  let a := A' 0%nat 0%nat in let b := A' 0%nat 1%nat in 
  PI/2 - arg a - arg b.

(* @nocheck name *)
Definition euler_ZXZ_β (A : Square 2) : R :=
  Eval cbv zeta in 
  let DA := Determinant A in 
  let A' := (/ Cexp (get_arg DA / 2) .* A)%M in 
  let a := A' 0%nat 0%nat in let b := A' 0%nat 1%nat in 
  -2 * acos (Cmod a).

(* @nocheck name *)
Definition euler_ZXZ_γ (A : Square 2) : R :=
  Eval cbv zeta in 
  let DA := Determinant A in 
  let A' := (/ Cexp (get_arg DA / 2) .* A)%M in 
  let a := A' 0%nat 0%nat in let b := A' 0%nat 1%nat in 
   - euler_ZXZ_α A - 2 * arg a.

(* @nocheck name *)
Definition euler_ZXZ_δ (A : Square 2) : R :=
  Eval cbv zeta in 
  let DA := Determinant A in 
  get_arg DA / 2 - (euler_ZXZ_α A + euler_ZXZ_β A + euler_ZXZ_γ A) / 2.

(* @nocheck name *)
Lemma euler_decomposition_ZXZ (A : Square 2) (HA : WF_Unitary A) : 
  A = ⟦ Cexp (euler_ZXZ_δ A) .* 
    (Z 1 1 (euler_ZXZ_γ A) ⟷ X 1 1 (euler_ZXZ_β A) ⟷ Z 1 1 (euler_ZXZ_α A)) ⟧.
Proof.
  now apply euler_decomposition_ZXZ_step2.
Qed.

End EulerMatrix.
