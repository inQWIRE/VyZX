
Module SoundnessC.

Require QuantumLib.Complex QuantumLib.Matrix QuantumLib.RealAux.

Require Import QuantumLib.Polar.
Import Modulus.

Definition prop_lb (z : C) : nat := 
  (BinInt.Z.to_nat (Int_part (ln (Cmod z / 2) / ln (√2))%R%C) + 1)%nat.

(* Decomposition assuming |z| <= 2 *)
Definition small_decomp (z : C) : R * R :=
  let a := acos ((Cmod z)^2 / 2 - 1) in
  (a, get_arg (z / (1 + Cexp a))).

Definition prop_decomp (z : C) : nat * (R * R) :=
  (prop_lb z, small_decomp (z / (√2 ^ prop_lb z))).



Definition Cexp' (c : C) :=
  exp (Re c) * Cexp (Im c).

Lemma Cexp'_def (c : C) : 
  Cexp' c = exp (Re c) * Cexp (Im c).
Proof. reflexivity. Qed.

Lemma Cexp'_add (c d : C) : 
  Cexp' (c + d) = Cexp' c * Cexp' d.
Proof.
  unfold Cexp', Im, Re.
  cbn.
  rewrite exp_plus, Cexp_add.
  lca.
Qed.

Lemma Cexp'_zero : Cexp' 0 = 1.
Proof.
  unfold Cexp'.
  cbn.
  rewrite exp_0, Cexp_0.
  lca.
Qed.

Lemma Cmod_Cexp' c : Cmod (Cexp' c) = exp (Re c).
Proof.
  unfold Cexp'.
  rewrite Cmod_mult, Cmod_Cexp, Rmult_1_r.
  apply Cmod_real; [cbn | reflexivity].
  pose proof (exp_pos (Re c)).
  lra.
Qed.


Definition Clog (c : C) :=
  (ln (Cmod c), get_arg c).

Lemma Cexp'_Clog (c : C) (Hc : c <> 0) : 
  Cexp' (Clog c) = c.
Proof.
  unfold Clog, Cexp'.
  cbn.
  rewrite exp_ln.
  - exact (rect_to_polar_to_rect c Hc).
  - apply Cmod_gt_0, Hc.
Qed.


Lemma if_sumbool {A P Q} (x y : A) (c : {P} + {Q}) : 
  (if c then x else y) = if RMicromega.sumboolb c then x else y.
Proof.
  destruct c; reflexivity.
Qed.

Section get_arg.

Local Open Scope R_scope.

Lemma get_arg_R_pos (r : R) (Hr : 0 < r) : get_arg r = 0.
Proof.
  unfold get_arg.
  simpl.
  destruct (Rcase_abs 0) as [Hfalse | Hge0]; [lra|].
  rewrite Cmod_R, Rabs_pos_eq, Rdiv_diag, acos_1 by lra.
  reflexivity.
Qed.

Lemma get_arg_R_neg (r : R) (Hr : r < 0) : get_arg r = PI.
Proof.
  unfold get_arg.
  simpl.
  destruct (Rcase_abs 0) as [Hfalse | Hge0]; [lra|].
  rewrite Cmod_R, Rabs_left, Rdiv_opp_r, Rdiv_diag, 
    acos_opp, acos_1 by lra.
  lra.
Qed.

Lemma Rdiv_le_iff a b c (Hb : 0 < b) : 
  a / b <= c <-> a <= b * c.
Proof.
  split.
  - intros Hle.
    replace a with (b * (a / b)).
    2: {
      unfold Rdiv.
      rewrite <- Rmult_assoc, (Rmult_comm b a), Rmult_assoc.
      rewrite Rmult_inv_r; lra.
    }
    apply Rmult_le_compat_l; lra.
  - intros Hle.
    apply Rle_trans with (b * c / b).
    + apply Rmult_le_compat_r.
      * enough (0 < / b) by lra.
        now apply Rinv_0_lt_compat.
      * easy.
    + rewrite Rmult_comm.
      unfold Rdiv.
      rewrite Rmult_assoc, Rmult_inv_r; lra.
Qed.

End get_arg.

Section Rpower.

Local Open Scope R_scope.

Lemma Rpower_pos (b c : R) : 
  0 < Rpower b c.
Proof.
  apply exp_pos.
Qed.

Lemma ln_nondecreasing x y : 0 < x ->
  x <= y -> ln x <= ln y.
Proof.
  intros Hx [Hlt | ->]; [|right; reflexivity].
  left.
  apply ln_increasing; auto.
Qed.

Lemma ln_le_inv x y : 0 < x -> 0 < y ->
  ln x <= ln y -> x <= y.
Proof.
  intros Hx Hy [Hlt | Heq];
  [left; apply ln_lt_inv; auto|].
  right.
  apply ln_inv; auto.
Qed.


Lemma div_Rpower_le_of_le (r b c d : R) : 
  0 < r -> 1 < b -> 0 < c -> 0 < d ->
  ln (r / d) / ln b <= c ->
  r / (Rpower b c) <= d.
Proof.
  intros Hr Hb Hc Hd Hle.
  assert (0 < Rpower b c) by apply Rpower_pos.
  rewrite Rdiv_le_iff, Rmult_comm, 
    <- Rdiv_le_iff by auto.
  apply ln_le_inv;
  [apply Rdiv_lt_0_compat; lra|auto|].
  unfold Rpower.
  rewrite ln_exp.
  rewrite Rmult_comm.
  rewrite <- Rdiv_le_iff; [auto|].
  rewrite <- ln_1.
  apply ln_increasing; lra.
Qed.

End Rpower.


Lemma get_arg_Rmult (r : R) c (Hr : 0 < r) : 
  get_arg (r * c) = get_arg c.
Proof.
  unfold get_arg.
  cbn.
  rewrite 2!Rmult_0_l, Rplus_0_r, Rminus_0_r.
  rewrite 2!if_sumbool.
  apply f_equal_if.
  - destruct (Rcase_abs (snd c)) as [Hlt0 | Hgt0], 
      (Rcase_abs (r * snd c)) as [Hlt0' | Hgt0'];
    [reflexivity | | | reflexivity].
    + exfalso.
      revert Hgt0'.
      apply Rgt_not_ge.
      apply Rlt_gt.
      apply Rmult_pos_neg; lra.
    + exfalso.
      revert Hlt0'.
      apply Rle_not_lt.
      apply Rmult_le_pos; lra.
  - f_equal.
    f_equal.
    rewrite Cmod_mult, Cmod_R, Rabs_pos_eq by lra.
    apply Rdiv_mult_l_l; lra.
  - f_equal.
    rewrite Cmod_mult, Cmod_R, Rabs_pos_eq by lra.
    apply Rdiv_mult_l_l; lra.
Qed.

Lemma RtoC_exp (x : R) : 
  RtoC (exp x) = Cexp' x.
Proof.
  apply c_proj_eq; simpl;
  autorewrite with trig_db; lra.
Qed.

Lemma Cmod_1_plus_Cexp (r : R) : 
  Cmod (1 + Cexp r) = √ (2 + 2 * cos r)%R.
Proof.
  unfold Cmod.
  f_equal.
  simpl.
  pose proof sin2_cos2 r as H.
  rewrite 2!Rsqr_pow2 in H.
  field_simplify.
  rewrite (Rplus_comm _ (_ ^ 2)), <- Rplus_assoc.
  rewrite H.
  lra.
Qed.

Lemma prop_step_1 (r : R) (Hr : 0 < r <= 2) : 
  √ (2 + 2 * cos (acos (r^2 / 2 - 1))) = r.
Proof.
  assert (0 <= r ^ 2) by 
    (rewrite <- Rsqr_pow2, Rsqr_def;
    apply Rmult_le_pos;
    lra).
  assert (r ^ 2 <= 2 ^ 2) by 
    (apply Rpow_le_compat_r;
    lra).
  rewrite cos_acos by lra.
  apply sqrt_lem_1; [lra.. | ].
  rewrite <- Rsqr_pow2, Rsqr_def.
  lra.
Qed.

Lemma Cexp_Cexp' (r : R) : 
  Cexp r = Cexp' (0, r).
Proof.
  unfold Cexp'.
  cbn.
  rewrite exp_0.
  lca.
Qed.

Lemma Cexp_get_arg_unit (z : C) : Cmod z = 1 ->
  Cexp (get_arg z) = z.
Proof.
  intros Hmod.
  rewrite <- (Cexp'_Clog z) at 2 by 
    (intros H; rewrite H, Cmod_0 in Hmod; lra).
  rewrite Cexp_Cexp'.
  f_equal.
  unfold Clog.
  rewrite Hmod, ln_1.
  reflexivity.
Qed.

Lemma small_decomp_correct (z : C) : z <> 0 -> Cmod z <= 2 ->
  (1 + Cexp (fst (small_decomp z))) * 
  (Cexp (snd (small_decomp z))) =
  z.
Proof.
  intros Hz0 Hz.
  unfold small_decomp.
  cbn -[pow].
  assert (Hmod : 
    Cmod (C1 + Cexp (acos (Cmod z ^ 2 / 2 - 1))) = Cmod z). 1:{
    rewrite Cmod_1_plus_Cexp.
    assert (0 < Cmod z) by (apply Cmod_gt_0, Hz0).
    rewrite prop_step_1; lra.
  }
  assert (C1 + Cexp (acos (Cmod z ^ 2 / 2 - 1)) <> 0) by 
    (rewrite <- Cmod_eq_0_iff, Hmod, Cmod_eq_0_iff; auto).
  rewrite Cexp_get_arg_unit.
  - C_field.
  - rewrite Cmod_div by auto.
    rewrite Hmod.
    rewrite Rdiv_diag; [reflexivity|].
    rewrite Cmod_eq_0_iff.
    auto.
Qed.




Lemma pos_IZR (p : positive) : IZR (Z.pos p) = INR (Pos.to_nat p).
Proof.
  induction p.
  - rewrite IZR_POS_xI.
    rewrite Pos2Nat.inj_xI.
    rewrite IHp.
    rewrite S_INR, mult_INR, S_INR, INR_1.
    lra.
  - rewrite IZR_POS_xO.
    rewrite Pos2Nat.inj_xO.
    rewrite IHp.
    rewrite mult_INR, S_INR, INR_1.
    lra.
  - reflexivity.
Qed.

Lemma INR_to_nat (z : Z) : (0 <= z)%Z ->
  INR (Z.to_nat z) = IZR z.
Proof.
  intros Hz.
  destruct z; [reflexivity| | ].
  - simpl.
    rewrite pos_IZR.
    reflexivity.
  - lia.
Qed.


Lemma lt_S_Int_part r : r < IZR (1 + Int_part r).
Proof.
  rewrite (Rplus_Int_part_frac_part r) at 1.
  rewrite Z.add_comm, plus_IZR.
  pose proof (base_fp r).
  lra.
Qed.

Lemma lt_Int_part (r s : R) : (Int_part r < Int_part s)%Z -> r < s.
Proof.
  intros Hlt.
  apply Rlt_le_trans with (IZR (Int_part s));
  [apply Rlt_le_trans with (IZR (1 + Int_part r))|].
  - apply lt_S_Int_part.
  - apply IZR_le.
    lia.
  - apply base_Int_part.
Qed.


Lemma Int_part_le (r s : R) : r <= s -> (Int_part r <= Int_part s)%Z.
Proof.
  intros Hle.
  rewrite <- Z.nlt_ge.
  intros H%lt_Int_part.
  lra.
Qed.

Lemma IZR_le_iff (z y : Z) : IZR z <= IZR y <-> (z <= y)%Z.
Proof.
  split.
  - apply le_IZR.
  - apply IZR_le.
Qed.

Lemma IZR_lt_iff (z y : Z) : IZR z < IZR y <-> (z < y)%Z.
Proof.
  split.
  - apply lt_IZR.
  - apply IZR_lt.
Qed.

Lemma Int_part_IZR (z : Z) : Int_part (IZR z) = z.
Proof.
  symmetry.
  apply Int_part_spec.
  change 1 with (INR (Pos.to_nat 1)).
  rewrite <- pos_IZR, <- minus_IZR.
  rewrite IZR_le_iff, IZR_lt_iff.
  lia.
Qed.


#[local]
Instance Rle_trans_instance : RelationClasses.Transitive Rle := Rle_trans.

Lemma Int_part_ge_iff (r : R) (z : Z) : 
  (z <= Int_part r)%Z <-> (IZR z <= r).
Proof.
  split.
  - intros Hle.
    transitivity (IZR (Int_part r)).
    + apply IZR_le, Hle.
    + apply base_Int_part.
  - intros Hle.
    rewrite <- (Int_part_IZR z).
    apply Int_part_le, Hle.
Qed.



Lemma prop_lb_correct (z : C) : z <> 0 -> Cmod (z / (√2 ^ prop_lb z)) <= 2.
Proof.
  intros Hz.
  assert (Rlt 0 (√2 ^ prop_lb z)). 1:{
    pose proof (Rpow_pos (prop_lb z) (√2) 
      ltac:(pose Rlt_sqrt2_0; lra)) as H.
    destruct H as [H | H]; [exact H|].
    symmetry in H.
    rewrite Rpow_eq_0_iff in H.
    pose proof sqrt2_neq_0.
    lra.
  }
  assert (√ 2 ^ prop_lb z <> 0). 1:{
    rewrite RtoC_pow.
    apply RtoC_neq.
    lra.
  }
  rewrite Cmod_div by auto.
  rewrite Rdiv_le_iff by (apply Cmod_gt_0; auto).
  rewrite RtoC_pow.
  rewrite Cmod_R.
  rewrite Rabs_right by lra.
  unfold prop_lb.
  rewrite <- Rpower_pow by exact Rlt_sqrt2_0.
  rewrite <- Rdiv_le_iff by apply exp_pos.
  apply div_Rpower_le_of_le.
  - apply Cmod_gt_0; auto.
  - rewrite <- sqrt_1.
    apply sqrt_lt_1; lra.
  - rewrite plus_INR, INR_1.
    enough (0 <= INR (Z.to_nat (Int_part (ln (Cmod z / 2) / ln (√ 2))))) by lra.
    apply pos_INR.
  - lra.
  - rewrite plus_INR.
    transitivity (IZR (1 + (Int_part (ln (Cmod z / 2) / ln (√ 2)))));
    [apply Rlt_le, lt_S_Int_part|].
    rewrite Z.add_comm.
    rewrite plus_IZR, INR_1.
    apply Rplus_le_compat_r.
    generalize (Int_part (ln (Cmod z / 2) / ln (√2))).
    intros w.
    case w.
    + simpl; lra.
    + intros p.
      rewrite pos_IZR.
      simpl.
      lra.
    + intros p.
      simpl.
      rewrite IZR_NEG, pos_IZR.
      pose proof (INR_pos p).
      lra.
Qed.

Lemma prop_equation (z : C) : z <> 0 ->
  z = (√2 ^ fst (prop_decomp z)) * 
  (1 + Cexp (fst (snd (prop_decomp z)))) * 
  (Cexp (snd (snd (prop_decomp z)))).
Proof.
  intros Hz.
  assert (Rlt 0 (√2 ^ prop_lb z)). 1:{
    pose proof (Rpow_pos (prop_lb z) (√2) 
      ltac:(pose Rlt_sqrt2_0; lra)) as H.
    destruct H as [H | H]; [exact H|].
    symmetry in H.
    rewrite Rpow_eq_0_iff in H.
    pose proof sqrt2_neq_0.
    lra.
  }
  assert (√ 2 ^ prop_lb z <> 0). 1:{
    rewrite RtoC_pow.
    apply RtoC_neq.
    lra.
  }
  unfold prop_decomp.
  cbn [fst snd].
  rewrite <- Cmult_assoc.
  rewrite small_decomp_correct.
  - C_field.
  - apply Cdiv_nonzero; auto.
  - apply prop_lb_correct, Hz.
Qed.

Lemma fst_small_decomp_0 : fst (small_decomp 0) = PI.
Proof.
  unfold small_decomp.
  rewrite Cmod_0.
  simpl.
  rewrite Rmult_0_l, Rdiv_0_l, Rminus_0_l, acos_opp, acos_1.
  lra.
Qed.

Lemma prop_equation' (z : C) : 
  z = (√2 ^ fst (prop_decomp z)) * 
  (1 + Cexp (fst (snd (prop_decomp z)))) * 
  (Cexp (snd (snd (prop_decomp z)))).
Proof.
  destruct (Ceq_dec z 0) as [H0 | Hnz].
  - unfold prop_decomp.
    cbn [fst snd].
    rewrite H0.
    unfold Cdiv.
    rewrite Cmult_0_l, fst_small_decomp_0.
    rewrite Cexp_PI.
    lca.
  - apply prop_equation, Hnz.
Qed.

End SoundnessC.

Import SoundnessC.


From VyZX Require Import ZXCore Proportional.



Lemma X_0_0_semantics (r : R) : 
  ⟦ X 0 0 r ⟧ = (1 + Cexp r) .* I 1. 
Proof.
  lma'.
Qed.

Lemma Z_0_0_semantics (r : R) : 
  ⟦ Z 0 0 r ⟧ = (1 + Cexp r) .* I 1. 
Proof.
  lma'.
Qed.

Lemma Z_semantics_0_0 (r : R) : 
  Z_semantics 0 0 r = (1 + Cexp r) .* I 1. 
Proof.
  exact (Z_0_0_semantics r).
Qed.

Definition zx_sqrt2 : ZX 0 0 :=
  Z 0 1 0 ⟷ X 1 0 PI.

Local Open Scope R_scope.

Lemma zx_sqrt2_semantics : 
  ⟦ zx_sqrt2 ⟧ = (√2)%R .* I 1.
Proof.
  match goal with |- ?A = _ => compute_matrix A end.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  by_cell.
  autounfold with U_db.
  cbn [list2D_to_matrix nth].
  cbn.
  rewrite Cexp_0, Cexp_PI.
  C_field.
  lca.
Qed.

Definition zx_invsqrt2 : ZX 0 0 :=
  X 0 3 0 ⟷ Z 3 0 0.

Lemma zx_invsqrt2_semantics : 
  ⟦ zx_invsqrt2 ⟧ = / sqrt 2 .* I 1.
Proof.
  cbn.
  compute_matrix (Z_semantics 3 0 0).
  rewrite Cexp_0.
  prep_matrix_equivalence.
  by_cell.
  cbn -[X_semantics].
  Csimpl.
  cbn.
  rewrite Cexp_0.
  Csimpl.
  autounfold with U_db; cbn.
  C_field.
  lca.
Qed.

Definition zx_cexp (r : R) : ZX 0 0 :=
  X 0 1 r ⟷ Z 1 0 PI ⟷ zx_invsqrt2.

Lemma zx_cexp_semantics (r : R) : 
  ⟦ zx_cexp r ⟧ = Cexp r .* I 1.
Proof.
  unfold zx_cexp.
  set (T := X 0 1 r ⟷ Z 1 0 PI).
  cbn -[zx_invsqrt2 T].
  rewrite zx_invsqrt2_semantics.
  rewrite Mscale_mult_dist_l, Mmult_1_l by (restore_dims; auto_wf).

  match goal with |- ?A = _ => compute_matrix A end.
  prep_matrix_equivalence.
  autounfold with U_db; by_cell_no_intros; cbn.
  rewrite Cexp_PI.
  C_field.
  lca.
Qed.


Fixpoint zx_nsqrt2 (n : nat) : ZX 0 0 :=
  match n with 
  | 0 => Empty
  | S n' => zx_sqrt2 ⟷ zx_nsqrt2 n'
  end.

Lemma zx_nsqrt2_semantics n : 
  ⟦ zx_nsqrt2 n ⟧ = sqrt 2 ^ n .* I 1.
Proof.
  induction n.
  - lma'.
  - cbn [zx_nsqrt2 ZX_semantics].
    rewrite zx_sqrt2_semantics.
    rewrite IHn.
    rewrite Mscale_mult_dist_l, Mscale_mult_dist_r, Mscale_assoc.
    Msimpl.
    rewrite Cmult_comm.
    reflexivity.
Qed.

Definition zx_of_const (z : C) : ZX 0 0 :=
  zx_nsqrt2 (fst (prop_decomp z)) ⟷
  Z 0 0 (fst (snd (prop_decomp z))) ⟷
  zx_cexp (snd (snd (prop_decomp z))).


Lemma zx_of_const_semantics c : 
  ⟦zx_of_const c⟧ = c .* I 1.
Proof.
  unfold zx_of_const.
  cbn [ZX_semantics].
  rewrite zx_cexp_semantics, Z_semantics_0_0, zx_nsqrt2_semantics.
  repeat rewrite Mscale_mult_dist_l, Mmult_1_l by auto_wf. 
  rewrite 2!Mscale_assoc.
  f_equal.
  rewrite Cmult_comm, (Cmult_comm (Cexp _)), Cmult_assoc.
  rewrite <- prop_equation'.
  reflexivity.
Qed.

Local Open Scope ZX_scope.

Lemma proportional_sound : forall {nIn nOut} (zx0 zx1 : ZX nIn nOut),
  zx0 ∝ zx1 -> exists (zxConst : ZX 0 0), ⟦ zx0 ⟧ = ⟦ zxConst ↕ zx1 ⟧.
Proof.
  intros.
  simpl; unfold proportional, proportional_general in H.
  destruct H as [c [H cneq0]].
  rewrite H.
  exists (zx_of_const c).
  rewrite zx_of_const_semantics.
  rewrite Mscale_kron_dist_l, kron_1_l by auto_wf.
  reflexivity.
Qed.




Module ConcreteProp.


Import Matrix Setoid Complex.

Fixpoint last_nonzero (f : nat -> C) (n : nat) : nat :=
  match n with 
  | 0 => 0
  | S n' => if Ceq_dec (f n') 0 then last_nonzero f n' else n' 
  end.

Definition last_nonzero_val (f : nat -> C) (n : nat) : C :=
  f (last_nonzero f n).

Lemma UIPC {c d : C} (h g : c = d) : h = g.
Proof.
  apply Eqdep_dec.UIP_dec, Ceq_dec.
Qed.

Lemma Ceq_dec_eq {c d : C} (h : c = d) :
  Ceq_dec c d = left h.
Proof.
  destruct (Ceq_dec c d); [f_equal; apply UIPC|easy].
Qed.


Lemma last_nonzero_correct f n (Hn : exists (m : nat), (m < n)%nat /\ f m <> C0) :
  f (last_nonzero f n) <> C0 /\ 
  forall m, (last_nonzero f n < m < n)%nat -> f m = 0.
Proof.
  induction n; [destruct Hn as (?&?&?); easy|].
  simpl.
  destruct (Ceq_dec (f n) C0) as [H0 | Hn0].
  - destruct Hn as (m & Hm & Hfm).
    assert (m <> n) by (intros ->; easy).
    specialize (IHn (ltac:(exists m; split;auto with zarith))) as [Hl Hr].
    split; [apply Hl|].
    intros m' [Hlast Hlt].
    bdestruct (m' =? n).
    + subst; easy.
    + apply Hr; lia.
  - split; [auto|].
    lia.
Qed.

Local Open Scope nat_scope.

Lemma last_nonzero_small f n (Hn : n <> O) : 
  last_nonzero f n < n.
Proof.
  enough (forall m, m <= n -> last_nonzero f m < n) by auto.
  intros m Hm.
  induction m; [simpl; lia|].
  simpl.
  destruct (Ceq_dec (f m) C0); lia.
Qed.

Lemma last_nonzero_small_or_eq f n : 
  {last_nonzero f n < n} + {last_nonzero f n = 0}.
Proof.
  enough (forall m, m <= n -> 
    {last_nonzero f m < n} + {last_nonzero f m = 0}) by auto.
  intros m Hm.
  induction m; [simpl; right; reflexivity|].
  simpl.
  destruct (Ceq_dec (f m) C0); [|left; lia].
  apply IHm; lia.
Qed.


Lemma last_nonzero_spec f n : 
  {last_nonzero f n < n /\ f (last_nonzero f n) <> C0} + 
  {last_nonzero f n = 0 /\ forall k, k < n -> f k = C0}.
Proof.
  enough (forall m, m <= n -> 
  {last_nonzero f m < n /\ f (last_nonzero f m) <> C0} + 
  {last_nonzero f m = 0 /\ forall k, k < m -> f k = C0}) by auto.
  intros m Hm.
  induction m; [simpl; right; split; intros; lia|].
  simpl.
  destruct (Ceq_dec (f m) C0).
  - specialize (IHm ltac:(lia)).
    destruct IHm as [Hl | [Hlv0 Hall]]; [left; auto|].
    right; split; [auto|].
    intros k Hk.
    bdestruct (k =? m).
    + subst; auto.
    + apply Hall; lia.
  - left; split; [lia | auto].
Qed.

Definition mat_last_nonzero {n m} (A : Matrix n m) : nat :=
  last_nonzero (fun i => A (i mod n) (i / n))%nat (n * m)%nat.

Definition mat_last_nonzero_val {n m} (A : Matrix n m) : C :=
  last_nonzero_val (fun i => A (i mod n) (i / n))%nat (n * m)%nat.

Lemma last_nonzero_eq_of_zero_iff (f g : nat -> C) n
  (Hfg : forall k, (k < n)%nat -> f k = C0 <-> g k = C0) :
  last_nonzero f n = last_nonzero g n.
Proof.
  induction n; [reflexivity|].
  simpl.
  specialize (IHn (fun k Hk => ltac:(auto))).
  rewrite IHn.
  destruct (Ceq_dec (f n) C0) as [Hf | Hf], (Ceq_dec (g n) C0); 
  rewrite Hfg in Hf by auto; easy.
Qed.

Open Scope matrix_scope.

Lemma mat_last_nonzero_eq_of_prop {n m} (A B : Matrix n m) 
  c (Hc : c <> C0) : 
  A ≡ c .* B ->
  mat_last_nonzero A = mat_last_nonzero B.
Proof.
  intros HAB.
  unfold mat_last_nonzero.
  apply last_nonzero_eq_of_zero_iff.
  intros k Hk.
  rewrite HAB by Modulus.show_moddy_lt.
  unfold scale.
  split.
  - intros []%Cmult_integral; easy + auto.
  - intros ->; lca.
Qed.

Lemma mat_last_nonzero_val_eq_of_prop_gen {n m} (A B : Matrix n m) 
  c (Hc : c <> C0) (HAB0 : A 0 0 = (c * B 0 0)%C) : 
  A ≡ c .* B ->
  mat_last_nonzero_val A = (c * mat_last_nonzero_val B)%C.
Proof.
  intros HAB.
  unfold mat_last_nonzero_val.
  pose proof (mat_last_nonzero_eq_of_prop A B c Hc HAB) as Hrw.
  unfold mat_last_nonzero in Hrw.
  unfold last_nonzero_val.
  rewrite Hrw.
  destruct (last_nonzero_small_or_eq (fun i => B (i mod n) (i / n)) (n * m)) as
    [Hsmall | Hz].
  - apply HAB; Modulus.show_moddy_lt.
  - rewrite Hz.
    destruct n; [apply HAB0|].
    simpl.
    rewrite Nat.sub_diag.
    apply HAB0.
Qed.

Lemma mat_last_nonzero_val_eq_of_prop_nonempty {n m} (A B : Matrix n m) 
  c (Hc : c <> C0) (Hnm : n * m <> 0) : 
  A ≡ c .* B ->
  mat_last_nonzero_val A = (c * mat_last_nonzero_val B)%C.
Proof.
  intros HAB.
  apply mat_last_nonzero_val_eq_of_prop_gen; [auto| |auto].
  apply HAB; lia.
Qed.

Lemma prop_by_val_of_prop' {n m} (A B : Matrix n m) (c : C) (Hc : c <> C0) : 
  A ≡ c .* B -> 
  A ≡ (mat_last_nonzero_val A / mat_last_nonzero_val B) .* B.
Proof.
  bdestruct (n * m =? 0).
  - intros _ ?; nia.
  - intros HAB.
    rewrite HAB at 1. 
    apply mat_last_nonzero_val_eq_of_prop_nonempty in HAB; [|auto..].
    rewrite HAB.
    unfold mat_last_nonzero_val, last_nonzero_val.
    intros i j Hi Hj.
    unfold scale.
    destruct (last_nonzero_spec (fun i=>B (i mod n) (i / n)) (n * m))
      as [[Hsmall Hnz] | [Hlast Hzero]].
    + C_field.
    + specialize (Hzero (j * n + i) ltac:(Modulus.show_moddy_lt)).
      rewrite Modulus.mod_add_l, Nat.mod_small, Nat.div_add_l, 
        Nat.div_small, Nat.add_0_r in Hzero by lia.
      rewrite Hzero.
      lca.
Qed.

Lemma mat_last_nonzero_eq_of_equiv {n m} {A B : Matrix n m} 
  (HAB : A ≡ B) (H : n * m <> 0) : 
  mat_last_nonzero_val A = mat_last_nonzero_val B.
Proof.
  unfold mat_last_nonzero_val, last_nonzero_val.
  pose proof (last_nonzero_small (fun i => A (i mod n) (i / n)) _ H) as Hsm.
  revert Hsm.
  erewrite last_nonzero_eq_of_zero_iff; 
    [intros ?; apply HAB; Modulus.show_moddy_lt|].
  intros k Hk.
  rewrite HAB by Modulus.show_moddy_lt.
  reflexivity.
Qed.

Lemma prop_by_val_of_weakprop' {n m} (A B : Matrix n m) (c : C) : 
  A ≡ c .* B -> 
  A ≡ (mat_last_nonzero_val A / mat_last_nonzero_val B) .* B.
Proof.
  destruct (Ceq_dec c C0).
  - subst.
    rewrite Mscale_0_l.
    intros HA.
    intros i j Hi Hj.
    rewrite HA by auto.
    unfold Zero.
    assert (n * m <> 0) as Hnm by nia.
    rewrite (mat_last_nonzero_eq_of_equiv HA Hnm).
    unfold scale, mat_last_nonzero_val, last_nonzero_val, Zero.
    lca.
  - apply prop_by_val_of_prop'; auto.
Qed.

Lemma prop_by_val_of_prop {n m} (A B : Matrix n m) : 
  (exists c, A ≡ c .* B /\ c <> C0) -> 
  A ≡ (mat_last_nonzero_val A / mat_last_nonzero_val B) .* B.
Proof.
  intros (c & HAB & Hc).
  apply prop_by_val_of_prop' with c; auto.
Qed.

Lemma weakprop_iff_by_val {n m} (A B : Matrix n m) :
  (exists c, A ≡ c .* B) <->
  A ≡ (mat_last_nonzero_val A / mat_last_nonzero_val B) .* B.
Proof.
  split; [intros (c & HAB); apply prop_by_val_of_weakprop' with c; auto|].
  eauto.
Qed.

Lemma mat_last_nonzero_val_eq_of_prop_strict {n m} (A B : Matrix n m) 
  c (Hc : c <> C0) : 
  A = c .* B ->
  mat_last_nonzero_val A = (c * mat_last_nonzero_val B)%C.
Proof.
  intros HAB.
  unfold mat_last_nonzero_val.
  pose proof (mat_last_nonzero_eq_of_prop A B c Hc ltac:(now rewrite HAB)) as Hrw.
  unfold mat_last_nonzero in Hrw.
  unfold last_nonzero_val.
  rewrite Hrw, HAB.
  reflexivity.
Qed.

Lemma prop_by_val_of_strict_prop_WF {n m} (A B : Matrix n m) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) : 
  (exists c, A = c .* B /\ c <> C0) ->
  A = mat_last_nonzero_val A / mat_last_nonzero_val B .* B.
Proof.
  intros (c & HAB & Hc).
  apply mat_equiv_eq; [auto_wf..|].
  apply prop_by_val_of_prop.
  rewrite HAB.
  eauto using mat_equiv_refl.
Qed.



End ConcreteProp.

Import ConcreteProp.


Definition zxquot {n m} (zx0 zx1 : ZX n m) : C :=
  mat_last_nonzero_val ⟦zx0⟧ / mat_last_nonzero_val ⟦zx1⟧.

Lemma prop_by_of_prop {n m} (zx0 zx1 : ZX n m) : 
  zx0 ∝ zx1 -> zx0 ∝[zxquot zx0 zx1] zx1.
Proof.
  intros H%prop_by_val_of_strict_prop_WF. 
  Abort.
