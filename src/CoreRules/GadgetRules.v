Require Gadgets. 

(* Some computational results, not needed outside the file *)

Module ConstC.

Import QuantumLib.Complex QuantumLib.Polar Gadgets.ScalarC.

Local Open Scope C_scope.

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
    apply Rinv_r.
    rewrite Cmod_eq_0_iff.
    auto.
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
  - rewrite plus_INR.
    simpl.
    enough (0 <= INR (Z.to_nat (Int_part (ln (Cmod z / 2) / ln (√ 2))))) by lra.
    apply pos_INR.
  - lra.
  - rewrite plus_INR.
    apply Rle_trans with (IZR (1 + (Int_part (ln (Cmod z / 2) / ln (√ 2)))));
    [apply Rlt_le, lt_S_Int_part|].
    rewrite Z.add_comm.
    rewrite plus_IZR.
    simpl.
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

End ConstC.


Require Import CoreData CastRules SemanticsComp ComposeRules.


Lemma gadget_semantics (zx : ZX 0 0) :
  ⟦ zx ⟧ = (const_of_zx zx .* I 1)%M.
Proof.
  prep_matrix_equivalence.
  by_cell.
  unfold scale, I.
  cbn.
  now rewrite Cmult_1_r.
Qed.

(* Rules about const_of_zx *)

Lemma const_of_zx_eq_iff (zx : ZX 0 0) c : 
  const_of_zx zx = c <-> ⟦ zx ⟧ = scale c (I 1).
Proof.
  split.
  - intros <-.
    apply gadget_semantics.
  - unfold const_of_zx.
    intros ->.
    unfold scale; lca.
Qed.

Lemma const_of_zx_stack (zx0 zx1 : ZX 0 0) : 
  const_of_zx (zx0 ↕ zx1) = const_of_zx zx0 * const_of_zx zx1.
Proof.
  reflexivity.
Qed.

Lemma const_of_zx_compose (zx0 zx1 : ZX 0 0) : 
  const_of_zx (zx0 ⟷ zx1) = const_of_zx zx0 * const_of_zx zx1.
Proof.
  unfold const_of_zx; cbn; lca.
Qed.

Lemma const_of_zx_n_stack (zx : ZX 0 0) k prf0 prf1 : 
  const_of_zx (cast _ _ prf0 prf1 (n_stack k zx)) = 
  const_of_zx zx ^ k.
Proof.
  induction k.
  - rewrite cast_id; reflexivity.
  - simpl.
    change O with (0+0)%nat.
    erewrite (@cast_stack_distribute _ 0 _ 0 _ 0 _ 0 _ _ _ _ _ _ zx (k ⇑ zx)).
    rewrite const_of_zx_stack, cast_id, IHk.
    reflexivity.
  Unshelve. all: lia.
Qed.


(* Specific constants *)

Open Scope matrix_scope.

Lemma zx_sqrt2_semantics : 
  ⟦ zx_sqrt2 ⟧ = (√2)%R .* I 1.
Proof.
  rewrite zx_sqrt2_defn.
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


Lemma zx_invsqrt2_semantics : 
  ⟦ zx_invsqrt2 ⟧ = / sqrt 2 .* I 1.
Proof.
  rewrite zx_invsqrt2_defn.
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


Lemma zx_cexp_semantics (r : R) : 
  ⟦ zx_cexp r ⟧ = Cexp r .* I 1.
Proof.
  rewrite zx_cexp_defn.
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

Lemma zx_of_const_semantics c : 
  ⟦zx_of_const c⟧ = c .* I 1.
Proof.
  rewrite zx_of_const_defn.
  cbn [ZX_semantics].
  rewrite zx_cexp_semantics, Z_semantics_0_0', zx_nsqrt2_semantics.
  repeat rewrite Mscale_mult_dist_l, Mmult_1_l by auto_wf. 
  rewrite 2!Mscale_assoc.
  f_equal.
  rewrite Cmult_comm, (Cmult_comm (Cexp _)), Cmult_assoc.
  rewrite <- ConstC.prop_equation'.
  reflexivity.
Qed.


Lemma stack_zx_of_const_semantics {n m} (zx : ZX n m) c : 
  ⟦ zx_of_const c ↕ zx ⟧ = c .* ⟦ zx ⟧.
Proof.
  simpl.
  rewrite zx_of_const_semantics.
  rewrite Mscale_kron_dist_l, kron_1_l by auto_wf.
  reflexivity.
Qed.

(* A version with dimensions that simplify the addition *)
Lemma stack_zx_of_const_semantics' {n m} (zx : ZX n m) c : 
  @ZX_semantics n m (zx_of_const c ↕ zx) = c .* ⟦ zx ⟧.
Proof.
  apply stack_zx_of_const_semantics.
Qed.

Lemma prop_by_iff_eq_gadget_nonzero {n m} (zx0 zx1 : ZX n m) c : 
  zx0 ∝[c] zx1 <-> zx0 ∝= zx_of_const c ↕ zx1 /\ c <> C0.
Proof.
  split.
  - intros Hby.
    split; [|apply Hby].
    unfold proportional_by_1.
    rewrite stack_zx_of_const_semantics'.
    apply Hby.
  - intros [Hprop Hnz].
    split; [|apply Hnz].
    rewrite Hprop, stack_zx_of_const_semantics'.
    reflexivity.
Qed.

Lemma prop_by_to_gadget {n m} (zx0 zx1 : ZX n m) c : 
  zx0 ∝[c] zx1 -> zx0 ∝= zx_of_const c ↕ zx1.
Proof.
  rewrite prop_by_iff_eq_gadget_nonzero.
  easy.
Qed.

Local Open Scope ZX_scope.

Lemma proportional_sound : forall {nIn nOut} (zx0 zx1 : ZX nIn nOut),
  zx0 ∝ zx1 -> exists (zxConst : ZX 0 0), ⟦ zx0 ⟧ = ⟦ zxConst ↕ zx1 ⟧.
Proof.
  intros.
  destruct H as [c Hby].
  exists (zx_of_const c).
  apply prop_by_to_gadget, Hby.
Qed.

(* Automation for gadgets *)

(* Automatically convert an explicit proportionality lemma
  (i.e. ending in [_ ∝[_] _]) to the corresponding semantic
  equality statement. *)
Ltac zxlem_to_gadget h :=
  lazymatch type of h with 
  | ?zx0 ∝[?c] ?zx1 => open_constr:(prop_by_to_gadget zx0 zx1 c h)
  | forall x : ?T, _ => 
    let x := fresh x in 
    constr:(fun x : T => 
      ltac:(
        let happ := eval cbn beta in (h x) in 
        let res := zxlem_to_gadget happ
        in exact res))
  | ?T => fail 0 "Couldn't see lemma of type '" T
    "' as a lemma of shape '_ ∝[_] _'"
  end.

(* Use an explicit proportionality [∝[c]] lemma in a semantic 
  equality [∝=] context by converting to a gadget statement. 
  For example, [rewrite (to_gadget bi_algebra_rule_Z_X)]. Note
  that the lemma cannot have any implicit arguments, which is 
  usually most easily rectified by writing [to_gadget @lem] 
  instead of [to_gadget lem]. (Specifically, [lem] can be any
  term without holes, potentially with evars, so it can be 
  partially applied to arguments)*)
Notation "'to_gadget' h" := 
  (ltac:(
    let res := zxlem_to_gadget open_constr:(h) in 
    exact res))
  (at level 0, h at level 100, only parsing) : ZX_scope.


(* Rules about zx_scale *)

Lemma zx_scale_semantics {n m} c (zx : ZX n m) : ⟦ c .* zx ⟧ = scale c ⟦ zx ⟧.
Proof.
  rewrite zx_scale_defn.
  etransitivity; [apply zx_stack_spec|].
  rewrite zx_of_const_semantics.
  rewrite Mscale_kron_dist_l, kron_1_l by auto_wf.
  reflexivity.
Qed.

Lemma zx_scale_assoc {n m} c d (zx : ZX n m) : c .* (d .* zx) ∝= (c * d) .* zx.
Proof.
  hnf.
  rewrite 3 zx_scale_semantics.
  apply Mscale_assoc.
Qed.

Lemma zx_scale_1_l {n m} (zx : ZX n m) : 1 .* zx ∝= zx.
Proof.
  hnf.
  rewrite zx_scale_semantics.
  apply Mscale_1_l.
Qed.

Lemma zx_scale_eq_1_l {n m} c (zx : ZX n m) : c = C1 -> 
  c .* zx ∝= zx.
Proof.
  intros ->; apply zx_scale_1_l.
Qed.

Lemma zx_scale_compose_distr_l {n m o} (c : C) (zx0 : ZX n m) (zx1 : ZX m o) : 
  (c .* zx0) ⟷ zx1 ∝= c .* (zx0 ⟷ zx1).
Proof.
  hnf.
  simpl; rewrite 2 zx_scale_semantics.
  apply Mscale_mult_dist_r.
Qed.

Lemma zx_scale_compose_distr_r {n m o} (c : C) (zx0 : ZX n m) (zx1 : ZX m o) : 
  zx0 ⟷ (c .* zx1) ∝= c .* (zx0 ⟷ zx1).
Proof.
  hnf.
  simpl; rewrite 2 zx_scale_semantics.
  apply Mscale_mult_dist_l.
Qed.

Lemma zx_scale_stack_distr_l {n m o p} (c : C) (zx0 : ZX n m) (zx1 : ZX o p) : 
  (c .* zx0) ↕ zx1 ∝= c .* (zx0 ↕ zx1).
Proof.
  hnf.
  simpl; rewrite 2 zx_scale_semantics.
  apply Mscale_kron_dist_l.
Qed.

Lemma zx_scale_stack_distr_r {n m o p} (c : C) (zx0 : ZX n m) (zx1 : ZX o p) : 
  zx0 ↕ (c .* zx1) ∝= c .* (zx0 ↕ zx1).
Proof.
  hnf.
  simpl; rewrite 2 zx_scale_semantics.
  apply Mscale_kron_dist_r.
Qed.

Lemma zx_scale_transpose {n m} c (zx : ZX n m) : 
  (c .* zx) ⊤ ∝= c .* zx ⊤.
Proof.
  hnf.
  rewrite semantics_transpose_comm, 2 zx_scale_semantics, 
    semantics_transpose_comm. 
  apply Mscale_trans.
Qed.

Lemma zx_scale_adjoint {n m} c (zx : ZX n m) : 
  (c .* zx) † ∝= c ^* .* zx †.
Proof.
  hnf.
  rewrite semantics_adjoint_comm, 2 zx_scale_semantics, 
    semantics_adjoint_comm. 
  apply Mscale_adj.
Qed.

Lemma zx_scale_conjugate {n m} c (zx : ZX n m) : 
  (c .* zx) ⊼ ∝= c ^* .* zx ⊼.
Proof.
  rewrite 2 conjugate_decomp.
  rewrite zx_scale_adjoint, zx_scale_transpose.
  reflexivity.
Qed.

Lemma zx_scale_colorswap {n m} c (zx : ZX n m) : 
  ⊙ (c .* zx) ∝= c .* ⊙ zx.
Proof.
  hnf.
  rewrite semantics_colorswap_comm, 2 zx_scale_semantics, 
    semantics_colorswap_comm.
  now rewrite Mscale_mult_dist_r, Mscale_mult_dist_l.
Qed.

Lemma zx_scale_n_stack {n m} k c (zx : ZX n m) : 
  k ⇑ (c .* zx) ∝= c ^ k .* k ⇑ zx.
Proof.
  induction k.
  - simpl.
    now rewrite zx_scale_1_l.
  - simpl.
    rewrite IHk.
    rewrite zx_scale_stack_distr_l, zx_scale_stack_distr_r, zx_scale_assoc.
    reflexivity.
Qed.

Lemma zx_scale_n_stack1 k c (zx : ZX 1 1) : 
  k ↑ (c .* zx) ∝= c ^ k .* k ↑ zx.
Proof.
  induction k.
  - simpl.
    now rewrite zx_scale_1_l.
  - simpl.
    rewrite IHk.
    rewrite zx_scale_stack_distr_l, zx_scale_stack_distr_r, zx_scale_assoc.
    reflexivity.
Qed.

Lemma zx_scale_cast {n m n' m'} c (zx : ZX n' m') H H' : 
  cast n m H H' (c .* zx) = c .* cast n m H H' zx.
Proof.
  now subst.
Qed.

(* NB: This is entirely unnecessary, as rewrite databases are completely
  separate from standard hint databases, but it's probably good practice
  (and hopefully someday that'll change). *)
Create HintDb zxscale_db discriminated.
#[export] Hint Rewrite 
  @zx_scale_1_l
  @zx_scale_assoc
  @zx_scale_compose_distr_l   @zx_scale_compose_distr_r
  @zx_scale_stack_distr_l     @zx_scale_stack_distr_r
  @zx_scale_transpose   @zx_scale_adjoint   @zx_scale_conjugate
  @zx_scale_colorswap
  @zx_scale_n_stack     @zx_scale_n_stack1
  @zx_scale_cast : zxscale_db.

#[export] Hint Rewrite @zx_scale_colorswap : colorswap_db.
#[export] Hint Rewrite @zx_scale_transpose : transpose_db.
#[export] Hint Rewrite @zx_scale_adjoint : adjoint_db.

Ltac distribute_zxscale := rewrite_strat (bottomup (hints zxscale_db)).
Tactic Notation "distribute_zxscale" "in" hyp(H) :=
  rewrite_strat (bottomup (hints zxscale_db)) in H.

Lemma zx_scale_simplify_eq {n m} (c c' : C) (zx zx' : ZX n m) : 
  c = c' -> zx ∝= zx' -> c .* zx ∝= c' .* zx'.
Proof.
  intros -> ->.
  reflexivity.
Qed.

Lemma zx_scale_simplify_eq_l {n m} (c c' : C) (zx : ZX n m) : 
  c = c' -> c .* zx ∝= c' .* zx.
Proof.
  intros ->.
  reflexivity.
Qed.

Lemma zx_scale_simplify_eq_r {n m} (c : C) (zx zx' : ZX n m) : 
  zx ∝= zx' -> c .* zx ∝= c .* zx'.
Proof.
  intros ->.
  reflexivity.
Qed.

Lemma prop_by_iff_zx_scale {n m} c (zx zx' : ZX n m) : 
  zx ∝[c] zx' <-> zx ∝= c .* zx' /\ c <> C0.
Proof.
  unfold proportional_by.
  unfold proportional_by_1.
  now rewrite zx_scale_semantics.
Qed.

Lemma prop_iff_zx_scale {n m} (zx zx' : ZX n m) : 
  zx ∝ zx' <-> exists c, zx ∝= c .* zx' /\ c <> C0.
Proof.
  unfold proportional.
  now setoid_rewrite prop_by_iff_zx_scale.
Qed.

Lemma zx_scale_eq_l {n m} c (zx zx' : ZX n m) : c <> C0 ->
  c .* zx ∝= zx' <-> zx ∝= /c .* zx'.
Proof.
  intros Hc.
  split; [intros <- | intros ->]; distribute_zxscale; 
  rewrite 1?Cinv_l, 1?Cinv_r by auto;
  now rewrite zx_scale_1_l.
Qed.

Lemma zx_scale_eq_r {n m} c (zx zx' : ZX n m) : c <> C0 ->
  zx ∝= c .* zx' <-> / c .* zx ∝= zx'.
Proof.
  intros Hc.
  split; [intros -> | intros <-]; distribute_zxscale; 
  rewrite 1?Cinv_l, 1?Cinv_r by auto;
  now rewrite zx_scale_1_l.
Qed.

Lemma zx_scale_prop_by_l {n m} c d (zx zx' : ZX n m) : c <> C0 -> 
  c .* zx ∝[d] zx' <-> zx ∝[d/c] zx'.
Proof.
  intros Hc.
  rewrite 2 prop_by_iff_zx_scale.
  rewrite zx_scale_eq_l by auto.
  distribute_zxscale.
  rewrite Cmult_comm.
  apply Modulus.and_iff_distr_l.
  intros _. 
  unfold Cdiv.
  rewrite Cmult_integral_iff, Cinv_eq_0_iff.
  intuition idtac.
Qed.

Lemma zx_scale_prop_by_r {n m} c d (zx zx' : ZX n m) : c <> C0 -> 
  zx ∝[d] c .* zx' <-> zx ∝[d * c] zx'.
Proof.
  intros Hc.
  rewrite 2 prop_by_iff_zx_scale.
  distribute_zxscale.
  apply Modulus.and_iff_distr_l.
  intros _.
  rewrite Cmult_integral_iff.
  intuition fail.
Qed.

Lemma zx_scale_prop_l {n m} c (zx zx' : ZX n m) : c <> C0 ->
  c .* zx ∝ zx' <-> zx ∝ zx'.
Proof.
  intros Hc.
  rewrite 2 prop_iff_zx_scale.
  split.
  - intros (d & Heq & Hd).
    rewrite zx_scale_eq_l in Heq by auto.
    exists (/c * d).
    split.
    + distribute_zxscale in Heq.
      apply Heq.
    + rewrite Cmult_integral_iff, Cinv_eq_0_iff.
      intuition fail.
  - intros (d & Heq & Hd).
    exists (d * c).
    rewrite zx_scale_eq_l by auto.
    split.
    + distribute_zxscale.
      rewrite Heq.
      apply zx_scale_simplify_eq_l.
      C_field.
    + rewrite Cmult_integral_iff.
      intuition fail.
Qed.

Lemma zx_scale_prop_r {n m} c (zx zx' : ZX n m) : c <> C0 ->
  zx ∝ c .* zx' <-> zx ∝ zx'.
Proof.
  intros Hc.
  split.
  - intros ->.
    now apply zx_scale_prop_l.
  - intros ->.
    symmetry.
    now apply zx_scale_prop_l.
Qed.


Lemma zx_of_const_to_scaled_empty c : 
  zx_of_const c ∝= c .* ⦰.
Proof.
  prep_matrix_equivalence.
  rewrite zx_of_const_semantics, zx_scale_semantics.
  reflexivity.
Qed.




Lemma prop_by_to_zx_scale {n m} (zx0 zx1 : ZX n m) c : 
  zx0 ∝[c] zx1 -> zx0 ∝= c .* zx1.
Proof.
  rewrite prop_by_iff_zx_scale.
  easy.
Qed.

(* Automation for gadgets *)

(* Automatically convert an explicit proportionality lemma
  (i.e. ending in [_ ∝[_] _]) to the corresponding semantic
  equality statement. *)
Ltac zxlem_to_scale h :=
  lazymatch type of h with 
  | ?zx0 ∝[?c] ?zx1 => open_constr:(prop_by_to_zx_scale zx0 zx1 c h)
  | forall x : ?T, _ => 
    let x := fresh x in 
    constr:(fun x : T => 
      ltac:(
        let happ := eval cbn beta in (h x) in 
        let res := zxlem_to_scale happ
        in exact res))
  | ?T => fail 0 "Couldn't see lemma of type '" T
    "' as a lemma of shape '_ ∝[_] _'"
  end.

(* Use an explicit proportionality [∝[c]] lemma in a semantic 
  equality [∝=] context by converting to a gadget statement. 
  For example, [rewrite (to_scale bi_algebra_rule_Z_X)]. Note
  that the lemma cannot have any implicit arguments, which is 
  usually most easily rectified by writing [to_scale @lem] 
  instead of [to_scale lem]. (Specifically, [lem] can be any
  term without holes, potentially with evars, so it can be 
  partially applied to arguments)*)
Notation "'to_scale' h" := 
  (ltac:(
    let res := zxlem_to_scale open_constr:(h) in 
    exact res))
  (at level 0, h at level 100, only parsing) : ZX_scope.




Lemma gadget_is_scaled_empty (zx : ZX 0 0) : 
  zx ∝= const_of_zx zx .* ⦰.
Proof.
  prep_matrix_equivalence.
  rewrite zx_scale_semantics.
  by_cell; symmetry; apply Cmult_1_r.
Qed.
Lemma const_of_empty : const_of_zx ⦰ = 1.
Proof. reflexivity. Qed.
Lemma const_of_scale zx c : const_of_zx (c .* zx) = c * const_of_zx zx.
Proof.
  unfold const_of_zx.
  now rewrite zx_scale_semantics.
Qed.


Lemma const_of_zx_X_0_2_Z_1_0_Z_1_0_gen α β γ : 
  const_of_zx (X 0 2 α ⟷ (Z 1 0 β ↕ Z 1 0 γ)) = 
  /2 * (Cexp (α + β + γ) - Cexp (α + β) - Cexp (α + γ)
    + Cexp (β + γ) + Cexp α + Cexp β + Cexp γ + 1).
Proof.
  rewrite 4 Cexp_add.
  cbn; autounfold with U_db; cbn; 
  C_field.
Qed.

Lemma const_of_zx_X_0_1_Z_1_0_gen α β : 
  const_of_zx (X 0 1 α ⟷ Z 1 0 β) = 
  (1 + Cexp α + Cexp β - Cexp (α + β)) / √2.
Proof.
  unfold const_of_zx.
  cbn.
  rewrite kron_1_l by auto_wf.
  unfold hadamard.
  rewrite Cexp_add.
  C_field.
Qed.

Lemma const_of_zx_X_0_1_0_Z_1_0_0 : 
  const_of_zx (X 0 1 0 ⟷ Z 1 0 0) = √2.
Proof.
  rewrite const_of_zx_X_0_1_Z_1_0_gen.
  rewrite Rplus_0_l, Cexp_0.
  C_field; lca.
Qed.


Lemma const_of_zx_Z_gen α : 
  const_of_zx (Z 0 0 α) = 1 + Cexp α.
Proof. reflexivity. Qed.

Lemma const_of_zx_Z_0 : 
  const_of_zx (Z 0 0 0) = 2.
Proof. cbn; rewrite Cexp_0; lca. Qed.

Lemma const_of_zx_invsqrt2 : const_of_zx zx_invsqrt2 = /√2.
Proof.
  unfold const_of_zx.
  rewrite zx_invsqrt2_semantics.
  lca.
Qed.

(* FIXME: Move *)
Lemma X_0_0_is_Z_0_0 β : X 0 0 β ∝= Z 0 0 β.
Proof.
  change ((⊙ (Z 0 0 β)) ∝= Z 0 0 β).
  rewrite colorswap_is_bihadamard.
  simpl.
  now rewrite compose_empty_l, compose_empty_r.
Qed.

Lemma Z_0_0_is_X_0_0 β : Z 0 0 β ∝= X 0 0 β.
Proof.
  apply colorswap_diagrams_eq;
  exact (X_0_0_is_Z_0_0 β).
Qed.

Lemma const_of_zx_X_gen β : const_of_zx (X 0 0 β) = (C1 + Cexp β)%C.
Proof.
  rewrite X_0_0_is_Z_0_0.
  apply const_of_zx_Z_gen.
Qed. 

Lemma const_of_zx_half : const_of_zx (zx_half) = /C2.
Proof.
  rewrite zx_half_defn, const_of_zx_stack, const_of_zx_invsqrt2.
  C_field.
Qed.

Lemma const_of_zx_two : const_of_zx (zx_two) = C2.
Proof.
  rewrite zx_two_defn.
  rewrite const_of_zx_Z_0.
  reflexivity.
Qed.