Require Import ZXCore.
Require Import Setoid.

(* 
A generalized form of proportionality which can be used to build notions for 
other IRs easily 
*)

Open Scope ZX_scope.

Definition proportional_general {T_0 m_0 n_0 T_1 m_1 n_1} 
  (eval_0 : T_0 -> (Matrix m_0 n_0)) 
  (eval_1 : T_1 -> (Matrix m_1 n_1)) 
  (t_0 : T_0) (t_1 : T_1) := 
    exists (c : C), eval_0 t_0 = c .* eval_1 t_1 /\ c <> 0.

(* ZX Proportionality *)

Definition proportional_by {n m} (c : C) (zx0 zx1 : ZX n m) :=
  ⟦ zx0 ⟧ = c .* ⟦ zx1 ⟧ /\ c <> C0.

Definition proportional_by_1 {n m} (zx0 zx1 : ZX n m) :=
  ⟦ zx0 ⟧ = ⟦ zx1 ⟧.

Notation "zx0 '∝[' c ']' zx1" := 
  (proportional_by c%C zx0 zx1) (at level 70) : ZX_scope.

Notation "zx0 '∝=' zx1" := 
  (proportional_by_1 zx0 zx1) (at level 70) : ZX_scope.

Lemma proportional_by_1_defn {n m} (zx0 zx1 : ZX n m) :
  zx0 ∝= zx1 <-> zx0 ∝[1] zx1.
Proof.
  unfold proportional_by, proportional_by_1.
  rewrite Mscale_1_l.
  pose proof C1_nonzero.
  intuition auto.
Qed.

Lemma proportional_by_1_refl {n m} (zx0 : ZX n m) :
  zx0 ∝= zx0.
Proof. 
  unfold proportional_by_1.
  reflexivity.
Qed.

Lemma proportional_by_1_sym {n m} (zx0 zx1 : ZX n m) :
  zx0 ∝= zx1 -> zx1 ∝= zx0.
Proof. 
  unfold proportional_by_1.
  now intros ->.
Qed.

Lemma proportional_by_1_trans {n m} (zx0 zx1 zx2 : ZX n m) :
  zx0 ∝= zx1 -> zx1 ∝= zx2 -> zx0 ∝= zx2.
Proof. 
  unfold proportional_by_1.
  now intros -> ->.
Qed.


Add Parametric Relation n m : (ZX n m) (proportional_by_1)
  reflexivity proved by proportional_by_1_refl
  symmetry proved by proportional_by_1_sym
  transitivity proved by proportional_by_1_trans
  as proportional_by_1_setoid.

Add Parametric Morphism n m o : (@Compose n m o) with signature
  proportional_by_1 ==> proportional_by_1 ==> proportional_by_1
  as compose_prop_by_1_proper.
Proof.
  unfold proportional_by_1.
  cbn [ZX_semantics].
  congruence.
Qed.

Add Parametric Morphism n m o p : (@Stack n m o p) with signature
  proportional_by_1 ==> proportional_by_1 ==> proportional_by_1
  as stack_prop_by_1_proper.
Proof.
  unfold proportional_by_1.
  cbn [ZX_semantics].
  congruence.
Qed.

Add Parametric Morphism n m n' m' prfn prfm : (@cast n' m' n m prfn prfm)
  with signature proportional_by_1 ==> proportional_by_1 as
  cast_prop_by_1_proper.
Proof.
  unfold proportional_by_1.
  intros ? ? ?.
  now simpl_cast_semantics.
Qed.

Add Parametric Morphism n m : (@transpose n m) with signature
  proportional_by_1 ==> proportional_by_1 as 
  transpose_prop_by_1_proper.
Proof.
  intros zx0 zx1.
  unfold proportional_by_1.
  rewrite 2!semantics_transpose_comm.
  now intros ->.
Qed.

Add Parametric Morphism n m : (@color_swap n m) with signature
  proportional_by_1 ==> proportional_by_1 as 
  colorswap_prop_by_1_proper.
Proof.
  intros zx0 zx1.
  unfold proportional_by_1.
  rewrite 2!semantics_colorswap_comm.
  now intros ->.
Qed.

Add Parametric Morphism n m : (@adjoint n m) with signature
  proportional_by_1 ==> proportional_by_1 as 
  adjoint_prop_by_1_proper.
Proof.
  intros zx0 zx1.
  unfold proportional_by_1.
  rewrite 2!semantics_adjoint_comm.
  now intros ->.
Qed.

Add Parametric Morphism n m : (@conjugate n m) with signature
  proportional_by_1 ==> proportional_by_1 as 
  conjugate_prop_by_1_proper.
Proof.
  intros zx0 zx1.
  unfold proportional_by_1.
  rewrite 2!semantics_conjugate_comm.
  now intros ->.
Qed.

Add Parametric Morphism n m k : (@n_stack n m k) with signature
  proportional_by_1 ==> proportional_by_1 as 
  nstack_prop_by_1_proper.
Proof.
  intros zx0 zx1 H.
  induction k; [reflexivity|].
  cbn [n_stack].
  apply stack_prop_by_1_proper; auto.
Qed.

Add Parametric Morphism k : (@n_stack1 k) with signature
  proportional_by_1 ==> proportional_by_1 as 
  nstack1_prop_by_1_proper.
Proof.
  intros zx0 zx1 H.
  induction k; [reflexivity|].
  cbn [n_stack].
  apply stack_prop_by_1_proper; auto.
Qed.

Add Parametric Morphism n m c : (@proportional_by n m c) with signature
  proportional_by_1 ==> proportional_by_1 ==> iff 
  as proportional_by_proper_eq.
Proof.
  unfold proportional_by, proportional_by_1.
  now intros ? ? -> ? ? ->.
Qed.

Lemma compose_prop_by_if_l {n m o} (zx0 zx1 : ZX n m) 
  (zx2 : ZX m o) (zx3 : ZX n o) c d : zx0 ∝[c] zx1 ->
  zx0 ⟷ zx2 ∝[d] zx3 <-> zx1 ⟷ zx2 ∝[d / c] zx3.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [-> Hc].
  distribute_scale.
  rewrite Mscale_inv by auto.
  distribute_scale.
  apply ZifyClasses.and_morph; [now rewrite Cmult_comm|].
  symmetry.
  now apply Cdiv_nonzero_iff_r.
Qed.

Lemma compose_prop_by_if_r {n m o} (zx0 : ZX n m) 
  (zx1 zx2 : ZX m o) (zx3 : ZX n o) c d : zx1 ∝[c] zx2 ->
  zx0 ⟷ zx1 ∝[d] zx3 <-> zx0 ⟷ zx2 ∝[d / c] zx3.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [-> Hc].
  distribute_scale.
  rewrite Mscale_inv by auto.
  distribute_scale.
  apply ZifyClasses.and_morph; [now rewrite Cmult_comm|].
  symmetry.
  now apply Cdiv_nonzero_iff_r.
Qed.

Lemma stack_prop_by_if_l {n m o p} (zx0 zx1 : ZX n m) 
  (zx2 : ZX o p) zx3 c d : zx0 ∝[c] zx1 ->
  zx0 ↕ zx2 ∝[d] zx3 <-> zx1 ↕ zx2 ∝[d / c] zx3.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [-> Hc].
  restore_dims.
  distribute_scale.
  rewrite Mscale_inv by auto.
  restore_dims.
  distribute_scale.
  apply ZifyClasses.and_morph; [now rewrite Cmult_comm|].
  symmetry.
  now apply Cdiv_nonzero_iff_r.
Qed.

Lemma stack_prop_by_if_r {n m o p} (zx0 : ZX n m) 
  (zx1 zx2 : ZX o p) zx3 c d : zx1 ∝[c] zx2 ->
  zx0 ↕ zx1 ∝[d] zx3 <-> zx0 ↕ zx2 ∝[d / c] zx3.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [-> Hc].
  restore_dims.
  distribute_scale.
  rewrite Mscale_inv by auto.
  restore_dims.
  distribute_scale.
  apply ZifyClasses.and_morph; [now rewrite Cmult_comm|].
  symmetry.
  now apply Cdiv_nonzero_iff_r.
Qed.


Lemma compose_prop_by_compat_l {n m o} (zx0 zx1 : ZX n m) 
  (zx2 : ZX m o) c : zx0 ∝[c] zx1 ->
  zx0 ⟷ zx2 ∝[c] zx1 ⟷ zx2.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [-> Hc].
  distribute_scale.
  auto.
Qed.

Lemma compose_prop_by_compat_r {n m o} (zx0 : ZX n m) 
  (zx1 zx2 : ZX m o) c : zx1 ∝[c] zx2 ->
  zx0 ⟷ zx1 ∝[c] zx0 ⟷ zx2.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [-> Hc].
  distribute_scale.
  auto.
Qed.

Lemma stack_prop_by_compat_l {n m o p} (zx0 zx1 : ZX n m) 
  (zx2 : ZX o p) c : zx0 ∝[c] zx1 ->
  zx0 ↕ zx2 ∝[c] zx1 ↕ zx2.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [-> Hc].
  distribute_scale.
  auto.
Qed.

Lemma stack_prop_by_compat_r {n m o p} (zx0 : ZX n m) 
  (zx1 zx2 : ZX o p) c : zx1 ∝[c] zx2 ->
  zx0 ↕ zx1 ∝[c] zx0 ↕ zx2.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [-> Hc].
  distribute_scale.
  auto.
Qed.

Lemma cast_prop_by_compat {n m n' m'} (zx0 zx1 : ZX n m) 
  prfn prfn' prfm prfm' c : zx0 ∝[c] zx1 -> 
  cast n' m' prfn prfm zx0 ∝[c] cast n' m' prfn' prfm' zx1.
Proof.
  unfold proportional_by.
  now simpl_cast_semantics.
Qed.

Lemma transpose_prop_by_compat {n m} (zx0 zx1 : ZX n m) c : 
  zx0 ∝[c] zx1 -> 
  zx0 ⊤ ∝[c] zx1 ⊤.
Proof.
  unfold proportional_by.
  rewrite 2!semantics_transpose_comm.
  intros [-> Hc].
  now rewrite Mscale_trans.
Qed.

Lemma colorswap_prop_by_compat {n m} (zx0 zx1 : ZX n m) c : 
  zx0 ∝[c] zx1 -> 
  ⊙ zx0 ∝[c] ⊙ zx1.
Proof.
  unfold proportional_by.
  rewrite 2!semantics_colorswap_comm.
  intros [-> Hc].
  now distribute_scale.
Qed.

Lemma adjoint_prop_by_compat {n m} (zx0 zx1 : ZX n m) c : 
  zx0 ∝[c ^*] zx1 -> 
  zx0 † ∝[c] zx1 †.
Proof.
  unfold proportional_by.
  rewrite 2!semantics_adjoint_comm.
  intros [-> Hc].
  rewrite Mscale_adj.
  rewrite Cconj_involutive.
  split; [reflexivity|].
  rewrite <- (Cconj_involutive c).
  now apply Cconj_neq_0.
Qed.


Create HintDb zx_prop_by_db discriminated.
#[export] Hint Resolve 
  compose_prop_by_compat_l compose_prop_by_compat_r
  stack_prop_by_compat_l stack_prop_by_compat_r 
  cast_prop_by_compat 
  transpose_prop_by_compat 
  adjoint_prop_by_compat 
  colorswap_prop_by_compat : zx_prop_by_db.

(* For concrete examples with bad sizes *)
#[export]
Hint Extern 0 (?x ⟷ ?y ∝[?c] ?x ⟷ ?z) =>
  apply (compose_prop_by_compat_r x y z) : zx_prop_by_db.
#[export]
Hint Extern 0 (?x ⟷ ?y ∝[?c] ?z ⟷ ?y) =>
  apply (compose_prop_by_compat_l x z y) : zx_prop_by_db.
#[export]
Hint Extern 0 (?x ↕ ?y ∝[?c] ?x ↕ ?z) =>
  apply (stack_prop_by_compat_r x y z) : zx_prop_by_db.
#[export]
Hint Extern 0 (?x ↕ ?y ∝[?c] ?z ↕ ?y) =>
  apply (stack_prop_by_compat_l x z y) : zx_prop_by_db.
  
Lemma eq_sym_iff {A} (a b : A) : a = b <-> b = a.
Proof. easy. Qed.

Lemma proportional_by_trans_iff_l {n m} (zx0 zx1 zx2 : ZX n m) c d : 
  zx0 ∝[c] zx1 -> (zx0 ∝[d] zx2 <-> zx1 ∝[d / c] zx2).
Proof.
  unfold proportional_by.
  intros [-> Hc].
  rewrite Mscale_inv by auto.
  distribute_scale.
  apply ZifyClasses.and_morph; [now rewrite Cmult_comm|].
  rewrite Cdiv_nonzero_iff_r;
  intuition auto.
Qed.

Lemma proportional_by_trans_iff_r {n m} (zx0 zx1 zx2 : ZX n m) c d : 
  zx1 ∝[c] zx2 -> (zx0 ∝[d] zx1 <-> zx0 ∝[d * c] zx2).
Proof.
  unfold proportional_by.
  intros [-> Hc].
  distribute_scale.
  apply ZifyClasses.and_morph; [reflexivity|].
  rewrite Cmult_nonzero_iff;
  intuition auto.
Qed.

Lemma proportional_by_sym {n m} {zx0 zx1 : ZX n m} {c} : 
  zx0 ∝[c] zx1 -> zx1 ∝[/c] zx0.
Proof.
  intros [Heq Hc].
  split.
  - rewrite <- Mscale_inv by auto.
    easy.
  - rewrite Cinv_eq_0_iff.
    apply Hc.
Qed.

Lemma proportional_by_sym_iff {n m} {zx0 zx1 : ZX n m} {c} : 
  zx0 ∝[c] zx1 <-> zx1 ∝[/c] zx0.
Proof.
  split; [apply proportional_by_sym|].
  intros H%proportional_by_sym.
  rewrite Cinv_inv in H.
  exact H.
Qed.

Lemma proportional_by_sym_div_iff {n m} {zx0 zx1 : ZX n m} {c d} : 
  zx0 ∝[c / d] zx1 <-> zx1 ∝[d / c] zx0.
Proof.
  rewrite proportional_by_sym_iff, Cinv_div.
  reflexivity.
Qed.





(** Taken from stdpp:

The tactic [eunify x y] succeeds if [x] and [y] can be unified, and fails
otherwise. If it succeeds, it will instantiate necessary evars in [x] and [y].

Contrary to Coq's standard [unify] tactic, which uses [constr] for the arguments
[x] and [y], [eunify] uses [open_constr] so that one can use holes (i.e., [_]s).
For example, it allows one to write [eunify x (S _)], which will test if [x]
unifies a successor. *)
Tactic Notation "eunify" uconstr(x) uconstr(y) :=
  unify x y.

(** Given a term [dom], an open term [tgt], and a tactic [test],
  attempt to find a subterm of [dom] that unifies with [tgt]. 
  May fill evars of [tgt]. If such a subterm is found, 
  return a function mapping a term [x] with the type of [tgt] to
  the term replacing the matched subterm of [dom] with [x].
  [test] is used to filter matched subterms: when a subterm [y] is 
  found to match [tgt], [test] is called with argument [y]. If [test] 
  raises an error, this match is discarded and another tried.
  *)
Ltac epat_func_test dom tgt test :=
  let rec epat dom tgt :=
  match dom with
  | ?x => 
    let _ := lazymatch goal with _ => 
      (* idtac "1:" x tgt; *) 
      eunify x tgt; test x 
      (* ;idtac "PASS" *) end in
    let T := type of dom in 
    constr:(fun a : T => a)
  | ?f ?x => 
    let r := epat x tgt in 
    (* let _ := match goal with _ => 
      (* idtac "2:" f x tgt; *)
      eunify x tgt;
      test x
      (* ;idtac "PASS" *) end in *)
    constr:(fun t => f (r t))
  | ?f ?x =>
    let r := epat f tgt in 
    (* let _ := match goal with _ => idtac "3:" r x end in *)
    constr:((fun t => r t x))
  end in 
  epat dom tgt.

(** Given a term [dom] and an open term [tgt], attempt to find a 
  subterm of [dom] that unifies with [tgt]. May fill evars of [tgt]. 
  If such a subterm is found, return a function mapping a term [x] 
  with the type of [tgt] to the term replacing the matched subterm 
  of [dom] with [x]. See [epat_func_test] for a version that filters
  matched subterms. *)
Ltac epat_func dom tgt :=
  let r := epat_func_test dom tgt ltac:(fun k => idtac) in 
  let r' := eval cbn beta in r in 
  constr:(r').

(** Given a lemma statement [lem], give an [open_constr] which 
  fills in all dependent arguments before the first non-dependent 
  argument with [evar]s. 
  For example, think of [lem] as having type 
  [forall (x : A) (y : B) ..., Q x y ... -> ... -> P x y ...].
  In this example, it would return a term (lem _ _ ...) of type
  [Q ?[x] ?[y] ... -> ... -> P ?[x] ?[y] ...].
  NB that any depending arguments after [Q] would not be filled. 
*)
Ltac fill_lem_args_dep lem :=
  match type of lem with
  | ?A -> ?B => constr:(lem)
  | forall a : ?A, _ => 
    let lapp := open_constr:(lem _) in 
    let r := fill_lem_args_dep lapp in 
    constr:(r)
  | ?T => constr:(lem)
  end.

(** Given a lemma statement [lem], give an [open_constr] 
  which fills in all arguments with [evar]s. 
  For example, think of [lem] as having type 
  [forall (x : A) (y : B) ..., Q x y ... -> 
    ... -> forall ... -> ... -> P x y ...])
  In that case, it would return a term (lem _ _ ...) of type
  [P ?[x] ?[y] ...], having filled in [Q] and all other arguments. 
*)
Ltac fill_lem_args lem :=
  match type of lem with
  | forall a : ?A, _ => 
    let lapp := open_constr:(lem _) in 
    let r := fill_lem_args lapp in 
    constr:(r)
  | ?T => constr:(lem)
  end.


(** Given a [constr] [H] of type [rwsrc ∝[c] rwtgt], rewrites [H] 
  in a goal [LHS ∝[d] RHS]. It matches topdown, trying first to match
  [rwsrc] with a subterm of [LHS], then of [RHS]. Given a match, 
  it reconstructs a statement reducing the goal to a goal replacing
  the subterm with [rwtgt] (and necessarily changing the constant [d]) 
  using [auto with zx_prop_by_db]. *)
Ltac zxrw_one H :=
  match type of H with
  | ?rwsrc ∝[ ?rwfac ] ?rwtgt =>
  let Hrw := fresh "Hrw" in 
  match goal with 
  | |- ?zxL ∝[ ?fac ] ?zxR => 
    let Lpat := eval pattern rwsrc in zxL in 
    lazymatch Lpat with 
    | (fun _ => ?P) _ => let r := constr:(P) in fail
    | (fun x => @?P x) _ => 
      let rwt := eval cbn beta in (P rwsrc ∝[rwfac] P rwtgt) in 
      assert (Hrw : rwt) by auto 100 using H with zx_prop_by_db nocore;
      apply <- (proportional_by_trans_iff_l _ _ zxR rwfac fac Hrw);
      clear Hrw
    end
  | |- ?zxL ∝[ ?fac ] ?zxR => 
    let Rpat := eval pattern rwsrc in zxR in 
    lazymatch Rpat with 
    | (fun _ => ?P) _ => let r := constr:(P) in fail
    | (fun x => @?P x) _ => 
      let rwt := eval cbn beta in (P rwsrc ∝[rwfac] P rwtgt) in 
      assert (Hrw : rwt) by auto 100 using H with zx_prop_by_db nocore;
      apply <- (proportional_by_trans_iff_r zxL _ _ rwfac fac Hrw);
      clear Hrw
    end
  end
  end.

(** Given an [open_constr] [H] of type [rwsrc ∝[c] rwtgt], possibly
  containing [evar] holes, rewrites [H] in a goal [LHS ∝[d] RHS]. 
  It matches topdown, trying first to match [rwsrc] with a subterm 
  of [LHS], then of [RHS]. Given a match, it reconstructs a statement 
  reducing the goal to a goal replacing the subterm with [rwtgt] (and 
  necessarily changing the constant [d]) using [auto with zx_prop_by_db]. *)
Ltac zxrw_one_open H :=
  lazymatch type of H with
  | ?rwsrc ∝[ ?rwfac ] ?rwtgt =>
  let Hrw := fresh "Hrw" in 
  match goal with 
  | |- ?zxL ∝[ ?fac ] ?zxR => 
    let Lpat := epat_func zxL rwsrc in 
    let P := Lpat in 
      let rwtbase := open_constr:(P rwsrc ∝[_] P rwtgt) in
      let rwt := eval cbn beta in rwtbase in 
      assert (Hrw : rwt) by eauto 100 using H with zx_prop_by_db nocore;
      apply <- (proportional_by_trans_iff_l _ _ zxR _ fac Hrw);
      clear Hrw
  | |- ?zxL ∝[ ?fac ] ?zxR => 
    let Rpat := epat_func zxR rwsrc in 
    let P := Rpat in 
      let rwtbase := open_constr:(P rwsrc ∝[_] P rwtgt) in
      let rwt := eval cbn beta in rwtbase in 
      assert (Hrw : rwt) by eauto 100 using H with zx_prop_by_db nocore;
      apply <- (proportional_by_trans_iff_r zxL _ _ _ fac Hrw);
      clear Hrw
  end
  end.

Lemma proportional_by_refl_iff {n m} (zx0 zx1 : ZX n m) c : 
  c = C1 ->
  zx0 ∝[c] zx1 <-> zx0 ∝= zx1.
Proof.
  intros ->.
  now rewrite proportional_by_1_defn.
Qed.

(** The tactic used by [zxrefl] to solve the [c = 1] side-condition,
  by default [try (now C_field)]. 
  Redefine ([Ltac zxrefl_tac ::= ...]) to change behavior. *)
Ltac zxrefl_tac := try (now C_field). 

(** On a goal of type [LHS ∝[c] RHS], replaces it with two goals,
  [c = 1] and [LHS ∝= RHS]. It attempts to solve the first with
  [zxrefl_tac] (by default, [try (now C_field)]) and attempts to
  solve the second with reflexivity. *)
Ltac zxrefl :=
  apply proportional_by_refl_iff;
  [(repeat match goal with
    | H : _ ∝[_] _ |- _ => destruct H as [? ?]
    end); zxrefl_tac
  | try reflexivity].

(** On a goal of type [LHS ∝[c] RHS], replace this by symmetry with
  [RHS ∝[d] LHS], where [d] is chosen somewhat intelligently. 
  Specifically, if [c = / c0] then we take [d = c0], 
  if [c = c0 / c1] then we take [d = c1 / c0], and 
  otherwise we take [d = / c]. *)
Ltac zxsymmetry :=
  lazymatch goal with
  | |- proportional_by (Cinv _) _ _ => refine (proportional_by_sym _)
  | |- proportional_by (Cdiv _ _) _ _ =>
    refine (proj1 proportional_by_sym_div_iff _)
  | |- proportional_by _ _ _ => 
    refine (proj2 proportional_by_sym_iff _)
  | |- _ => fail 0 "Goal is not of form '_ ∝[_] _'"
  end.

(** Given a hypothesis [H] of type [LHS ∝[c] RHS], replace this 
  by symmetry with [RHS ∝[d] LHS], where [d] is chosen 
  somewhat intelligently. 
  Specifically, if [c = / c0] then we take [d = c0], 
  if [c = c0 / c1] then we take [d = c1 / c0], and 
  otherwise we take [d = / c]. *)
Ltac zxsymmetry_in H :=
  lazymatch type of H with
  | proportional_by (Cinv _) _ _ => 
    apply (proj2 proportional_by_sym_iff) in H
  | proportional_by (Cdiv _ _) _ _ =>
    apply (proj1 proportional_by_sym_div_iff) in H
  | proportional_by _ _ _ => 
    apply (proj2 proportional_by_sym_iff) in H
  | _ => fail 0 "Hypothesis is not of form '_ ∝[_] _'"
  end.

(** Apply symmetry to the hypothesis [H] using [zxsymmetry_in]. 
  See [zxsymmetry_in] documentation for details. *)
Tactic Notation "zxsymmetry" "in" hyp(H) :=
  zxsymmetry_in H.

(** Apply symmetry to the goal using [zxsymmetry]. See
  [zxsymmetry] documentation for details. *)
Tactic Notation "zxsymmetry" :=
  zxsymmetry.

(** Prepare a lemma [H] to be rewritten with by filling 
  all arguments with holes, and failing if [H] is not 
   seen to be of type [_ ∝[_] _] (after arguments are filled). *)
Ltac zxrw_prep H :=
  lazymatch type of H with 
  | _ ∝[_] _ => open_constr:(H)
  | forall _, _ => zxrw_prep open_constr:(H _)
  | ?T => fail 0 "Couldn't see lemma of type '" T
    "' as a lemma of shape '_ ∝[_] _'"
  end.

(** Given a lemma [H : forall (...), rwsrc ∝[d] rwtgt], rewrite [H] 
  left-to-right in a goal of type [LHS ∝[c] RHS] using [zxrw_one_open], 
  having first checked it has the correct type and filled its arguments 
  with [evar] holes using [zxrw_prep]. *)
Tactic Notation "zxrewrite" open_constr(H) :=
  let H' := zxrw_prep H in 
  zxrw_one_open H'.

(** Given a lemma [H : forall (...), rwsrc ∝[d] rwtgt], rewrite [H] 
  right-to-left in a goal of type [LHS ∝[c] RHS] using [zxrw_one_open], 
  having first checked it has the correct type and filled its arguments 
  with [evar] holes using [zxrw_prep]. *)
Tactic Notation "zxrewrite" "<-" open_constr(H) :=
  let H' := zxrw_prep H in 
  zxrw_one_open (proportional_by_sym H).













Definition proportional {n m} 
  (zx_0 : ZX n m) (zx_1 : ZX n m) := exists c, zx_0 ∝[c] zx_1.
Notation "zx0 ∝ zx1" := (proportional zx0 zx1) (at level 70) : ZX_scope. (* \propto *)

(** On a goal [exists c : C, ?P /\ c <> 0], give [c] as witness and try to 
  solve the [c <> 0] side-condition. For instance, [prop_exists_nonzero c] 
  on a goal [zx0 ∝ zx1] reduces the goal to [⟦zx0⟧ = c .* ⟦zx1⟧], 
  along with [c <> 0] if this is not solved automatically. *)
Ltac prop_exists_nonzero c := 
  exists c; split; [|repeat (apply nonzero_div_nonzero +
    apply Cmult_neq_0); try nonzero; auto].

(** On a goal [zx0 ∝ zx1], replace this goal with 
  [⟦zx0⟧ = c .* ⟦zx1⟧] and try to solve that goal by brute force. 
  Specifically, simplify with [Msimpl] and unfolding Z/X semantics, 
  then use [solve_matrix] to brute-force a solution, and finally
  [autorewrite with Cexp_db; lca] to solve any remaining goals. *)
Ltac solve_prop c := 
	prop_exists_nonzero c; simpl; Msimpl; 
	unfold X_semantics; unfold Z_semantics; simpl; solve_matrix; 
	autorewrite with Cexp_db; lca.

Lemma proportional_of_by_1 {n m} (zx0 zx1 : ZX n m) : zx0 ∝= zx1 ->
  zx0 ∝ zx1.
Proof.
  intros H%proportional_by_1_defn.
  now exists 1.
Qed.

(** Reduces a goal [zx0 ∝ zx1] to [zx0 ∝= zx1]. Acts somewhat like
  a refined version of [prop_exists_nonzero C1]. *)
Ltac zxprop_by_1 := 
  apply proportional_of_by_1.


Lemma proportional_refl : forall {n m} (zx : ZX n m), 
  zx ∝ zx.
Proof. intros; zxprop_by_1; reflexivity. Qed.

Lemma proportional_symm : forall {n m} (zx_0 : ZX n m) (zx_1 : ZX n m),
  zx_0 ∝ zx_1 -> zx_1 ∝ zx_0.
Proof. 
  intros * (c & Hzx & Hc).
  prop_exists_nonzero (/ c).
  rewrite <- Mscale_inv by auto.
  easy.
Qed.

Lemma proportional_trans : forall {n m} 
  (zx0 : ZX n m) (zx1 : ZX n m) (zx2 : ZX n m),
  zx0 ∝ zx1 -> zx1 ∝ zx2 -> zx0 ∝ zx2.
Proof. 
  intros * (c & Hzx01 & Hc) (d & Hzx12 & Hd).
  prop_exists_nonzero (c * d).
  rewrite Hzx01, Hzx12.
  now distribute_scale.
Qed.

Add Parametric Relation (n m : nat) : (ZX n m) (proportional)
  reflexivity proved by proportional_refl
  symmetry proved by proportional_symm
  transitivity proved by proportional_trans
  as zx_prop_equiv_rel.

#[export]
Instance proportional_by_subrel n m c : 
  subrelation (@proportional_by n m c) (@proportional n m).
Proof.
  intros zx0 zx1 H.
  now exists c.
Qed.



Add Parametric Morphism (n m : nat) (c : C) : (@proportional n m) with signature
  proportional_by c ==> proportional_by_1 ==> iff as 
  proportional_proper_by_l.
Proof.
  intros ? ? H0%proportional_by_subrel ? ? 
    H1%proportional_by_1_defn%proportional_by_subrel.
  now rewrite H0, H1.
Qed.

Add Parametric Morphism (n m : nat) (c : C) : (@proportional n m) with signature
  proportional_by_1 ==> proportional_by c ==> iff as 
  proportional_proper_by_r.
Proof.
  intros ? ? H0%proportional_by_1_defn%proportional_by_subrel ? ? 
    H1%proportional_by_subrel.
  now rewrite H0, H1.
Qed.

Add Parametric Morphism (n m : nat) : (@proportional n m) with signature
  proportional_by_1 ==> proportional_by_1 ==> iff as 
  proportional_proper_by_1.
Proof.
  intros ? ? H0%proportional_by_1_defn%proportional_by_subrel ? ? 
    H1%proportional_by_1_defn%proportional_by_subrel.
  now rewrite H0, H1.
Qed.





Lemma stack_compat :
  forall n0 m0 n1 m1,
    forall (zx0 : ZX n0 m0) (zx2 : ZX n0 m0), zx0 ∝ zx2 ->
    forall (zx1 : ZX n1 m1) (zx3 : ZX n1 m1), zx1 ∝ zx3 ->
    zx0 ↕ zx1 ∝ zx2 ↕ zx3.
Proof.
  intros n0 m0 n1 m1 zx0 zx2 [x [Hzx0 Hx]] zx1 zx3 [x0 [Hzx1 Hx0]].
  prop_exists_nonzero (x * x0). 
  simpl.
  rewrite Hzx0, Hzx1.
  now distribute_scale.
Qed.

Add Parametric Morphism (n0 m0 n1 m1 : nat) : Stack
  with signature 
    (@proportional n0 m0) ==> 
    (@proportional n1 m1) ==> 
    proportional as stack_mor.
Proof. apply stack_compat; assumption. Qed.

Lemma n_stack_compat :
  forall nIn nOut n,
    forall zx0 zx1 : ZX nIn nOut, zx0 ∝ zx1 ->
    n ⇑ zx0 ∝ n ⇑ zx1.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite H.
    reflexivity.
Qed.

Add Parametric Morphism (n m d : nat) : (n_stack d)
  with signature 
      (@proportional n m) ==> 
      proportional as nstack_mor.
Proof. apply n_stack_compat. Qed.

Lemma n_stack1_compat :
  forall n,
    forall zx0 zx1 : ZX 1 1, zx0 ∝ zx1 ->
    n ↑ zx0 ∝ n ↑ zx1.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite H.
    reflexivity.
Qed. 

Add Parametric Morphism (n : nat) : (n_stack1 n)
  with signature 
      (@proportional 1 1) ==> 
      (@proportional n n) as nstack1_mor.
Proof. apply n_stack1_compat. Qed. 

Lemma compose_compat :
  forall {n m} o,
    forall (zx0 : ZX n m) (zx2 : ZX n m), zx0 ∝ zx2 ->
    forall (zx1 : ZX m o) (zx3 : ZX m o), zx1 ∝ zx3 ->
    zx0 ⟷ zx1 ∝ zx2 ⟷ zx3.
Proof.
  intros n m o zx0 zx2 [x [Hzx0 Hx]] zx1 zx3 [x0 [Hzx1 Hx0]].
  prop_exists_nonzero (x * x0). 
  simpl.
  rewrite Hzx0, Hzx1.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  auto.
Qed.

Add Parametric Morphism (n o m : nat)  : Compose
  with signature (@proportional n m) ==> (@proportional m o) ==> 
                 (@proportional n o) as compose_mor.
Proof. apply compose_compat; assumption. Qed.

Lemma cast_compat :
  forall {n m} n' m' prfn0 prfm0,
    forall (zx0 : ZX n m) (zx1 : ZX n m), zx0 ∝ zx1 ->
    cast n' m' prfn0 prfm0 zx0 ∝ cast n' m' prfn0 prfm0 zx1.
Proof.
  intros n m n' m' Hn Hm zx0 zx1 [x [Hzx0 Hx]].
  subst.
  prop_exists_nonzero x; auto.
Qed.

Add Parametric Morphism (n m : nat) {n' m' : nat} {prfn prfm} : (@cast n m n' m' prfn prfm)
  with signature (@proportional n' m') ==> 
                 (@proportional n m) as cast_mor.
Proof. apply cast_compat. Qed.

Lemma transpose_compat : 
  forall {n m},
    forall zx0 zx1 : ZX n m, zx0 ∝ zx1 ->
    (zx0⊤) ∝ (zx1⊤).
Proof.
  intros n m zx0 zx1 [x [Hzx0 Hx]].
  prop_exists_nonzero x; auto.
  rewrite 2 semantics_transpose_comm.
  rewrite Hzx0.
  rewrite Mscale_trans.
  auto.
Qed.

Add Parametric Morphism (n m : nat) : transpose
  with signature 
      (@proportional n m) ==> 
      (@proportional m n) as transpose_mor.
Proof. apply transpose_compat. Qed.

Lemma adjoint_compat : 
  forall {n m},
    forall (zx0 : ZX n m) (zx1 : ZX n m),
      zx0 ∝ zx1 -> (zx0 †) ∝ (zx1 †).
Proof.
  intros n m zx0 zx1 [x [Hzx0 Hx]].
  prop_exists_nonzero (x ^*)%C; try apply Cconj_neq_0; auto.
  rewrite 2 semantics_adjoint_comm.
  rewrite Hzx0.
  rewrite Mscale_adj.
  easy.
Qed.

Add Parametric Morphism (n m : nat) : (@adjoint n m)
  with signature (@proportional n m) ==> proportional as adj_mor.
Proof. apply adjoint_compat. Qed.

Lemma colorswap_is_bihadamard : forall {n m} (zx : ZX n m),
  ⊙ zx ∝= (n ↑ □) ⟷ (zx ⟷ (m ↑ □)).
Proof.
  intros n m zx.
  unfold proportional_by_1.
  cbn [ZX_semantics].
  rewrite 2 n_stack1_n_kron.
  rewrite semantics_colorswap_comm.
  easy.
Qed.

Lemma colorswap_is_bihadamard_gen : forall {n m} (zx : ZX n m),
  ⊙ zx ∝ (n ↑ □) ⟷ (zx ⟷ (m ↑ □)).
Proof.
  intros n m zx.
  now rewrite colorswap_is_bihadamard.
Qed.

Lemma colorswap_compat :
  forall nIn nOut,
    forall zx0 zx1 : ZX nIn nOut, zx0 ∝ zx1 ->
    (⊙ zx0) ∝ (⊙ zx1).
Proof.
  intros.
  rewrite 2 colorswap_is_bihadamard.
  rewrite H.
  easy.
Qed.

Add Parametric Morphism (nIn nOut : nat) : (@color_swap nIn nOut)
  with signature (@proportional nIn nOut) ==> (@proportional nIn nOut) 
    as colorswap_mor.
Proof. apply colorswap_compat. Qed.

Theorem sem_eq_prop : forall {n m} (zx0 : ZX n m) (zx1 : ZX n m),
  ⟦ zx0 ⟧ = ⟦ zx1 ⟧ -> zx0 ∝ zx1.
Proof.
  now intros n m zx0 zx1 ->%proportional_by_1_defn.
Qed.

(* Useful Lemmas *)

Lemma transpose_involutive_eq : forall {n m} (zx : ZX n m),
  zx ⊤ ⊤ = zx.
Proof.
  intros n m zx.
  induction zx; [reflexivity.. | |];
  cbn; rewrite IHzx1, IHzx2; reflexivity.
Qed.

Lemma adjoint_involutive_eq : forall {n m} (zx : ZX n m),
  zx † † = zx.
Proof.
  intros.
  induction zx; [reflexivity.. | | | |];
  [cbn; now rewrite Ropp_involutive.. | |];
  cbn; now f_equal.
Qed.

Lemma colorswap_involutive_eq {n m} (zx : ZX n m) :
  (⊙ ⊙ zx) = zx.
Proof.
  intros.
  induction zx; [reflexivity..| |];
  cbn; rewrite IHzx1, IHzx2; reflexivity.
Qed.

Lemma transpose_involutive : forall {n m} (zx : ZX n m),
  zx ⊤ ⊤ ∝= zx.
Proof.
  intros n m zx.
  now rewrite transpose_involutive_eq.
Qed.

Lemma adjoint_involutive : forall {n m} (zx : ZX n m),
  zx † † ∝= zx.
Proof.
  intros n m zx.
  now rewrite adjoint_involutive_eq.
Qed.

Lemma colorswap_involutive {n m} (zx : ZX n m) :
  (⊙ ⊙ zx) ∝= zx.
Proof.
  now rewrite colorswap_involutive_eq.
Qed.

Lemma colorswap_zx : forall {n m} (zx0 zx1 : ZX n m),
  ⊙ zx0 = ⊙ zx1 -> zx0 = zx1.
Proof. 
  intros.
  rewrite <- (colorswap_involutive_eq zx0).
  rewrite H.
  apply colorswap_involutive_eq.
Qed.

Lemma colorswap_diagrams_eq : forall {n m} (zx0 zx1 : ZX n m),
  ⊙ zx0 ∝= ⊙ zx1 -> zx0 ∝= zx1.
Proof.
  intros.
  rewrite <- colorswap_involutive.
  rewrite H.
  apply colorswap_involutive.
Qed.

Lemma colorswap_diagrams_by : forall {n m} (zx0 zx1 : ZX n m) c,
  ⊙ zx0 ∝[c] ⊙ zx1 -> zx0 ∝[c] zx1.
Proof.
  intros.
  rewrite <- colorswap_involutive.
  zxrewrite H.
  rewrite colorswap_involutive.
  zxrefl.
Qed.

Lemma colorswap_diagrams : forall {n m} (zx0 zx1 : ZX n m),
  ⊙ zx0 ∝ ⊙ zx1 -> zx0 ∝ zx1.
Proof.
  intros.
  rewrite <- colorswap_involutive.
  rewrite H.
  now rewrite colorswap_involutive.
Qed.

Lemma transpose_zx : forall {n m} (zx0 zx1 : ZX n m),
  zx0 ⊤ = zx1 ⊤ -> zx0 = zx1.
Proof.
  intros.
  rewrite <- (transpose_involutive_eq zx0).
  rewrite H.
  now rewrite transpose_involutive_eq.
Qed.

Lemma transpose_diagrams_eq : forall {n m} (zx0 zx1 : ZX n m),
  zx0 ⊤ ∝= zx1 ⊤ -> zx0 ∝= zx1.
Proof.
  intros.
  rewrite <- transpose_involutive.
  rewrite H.
  now rewrite transpose_involutive.
Qed.

Lemma transpose_diagrams_by : forall {n m} (zx0 zx1 : ZX n m) c,
  zx0 ⊤ ∝[c] zx1 ⊤ -> zx0 ∝[c] zx1.
Proof.
  intros.
  rewrite <- transpose_involutive.
  zxrewrite H.
  rewrite transpose_involutive.
  zxrefl.
Qed.

Lemma transpose_diagrams : forall {n m} (zx0 zx1 : ZX n m),
  zx0 ⊤ ∝ zx1 ⊤ -> zx0 ∝ zx1.
Proof.
  intros.
  rewrite <- transpose_involutive.
  rewrite H.
  now rewrite transpose_involutive.
Qed.

Lemma adjoint_zx : forall {n m} (zx0 zx1 : ZX n m),
  zx0 † = zx1 † -> zx0 = zx1.
Proof.
  intros.
  rewrite <- (adjoint_involutive_eq zx0).
  rewrite H.
  now rewrite adjoint_involutive_eq.
Qed.

Lemma adjoint_diagrams_eq : forall {n m} (zx0 zx1 : ZX n m),
  zx0 † ∝= zx1 † -> zx0 ∝= zx1.
Proof.
  intros.
  rewrite <- adjoint_involutive.
  rewrite H.
  now rewrite adjoint_involutive.
Qed.

Lemma adjoint_diagrams_by : forall {n m} (zx0 zx1 : ZX n m) c,
  zx0 † ∝[c ^*] zx1 † -> zx0 ∝[c] zx1.
Proof.
  intros.
  rewrite <- adjoint_involutive.
  zxrewrite H.
  rewrite adjoint_involutive.
  zxrefl.
  enough (c <> 0) by C_field.
  rewrite <- (Cconj_involutive c).
  now apply Cconj_neq_0.
Qed.

Lemma adjoint_diagrams : forall {n m} (zx0 zx1 : ZX n m),
  zx0 † ∝ zx1 † -> zx0 ∝ zx1.
Proof.
  intros.
  rewrite <- adjoint_involutive.
  rewrite H.
  now rewrite adjoint_involutive.
Qed.

Lemma colorswap_adjoint_commute : forall {n m} (zx : ZX n m),
  ⊙ (zx †) = (⊙ zx) †.
Proof.
  intros.
  induction zx; [reflexivity.. | |];
  cbn; now f_equal.
Qed.

Lemma transpose_adjoint_commute : forall {n m} (zx : ZX n m),
  (zx †) ⊤ = (zx ⊤) †.
Proof.
  intros.
  induction zx; [reflexivity.. | |];
  cbn; now f_equal.
Qed.

Lemma colorswap_transpose_commute : forall {n m} (zx : ZX n m),
  ⊙ (zx ⊤) = (⊙ zx) ⊤.
Proof.
  intros.
  induction zx; [reflexivity.. | |];
  cbn; now f_equal.
Qed.


Lemma wire_transpose : Wire ⊤ = Wire.
Proof.
  reflexivity.
Qed.

Lemma box_transpose : Box ⊤ = Box.
Proof. 
  reflexivity.
Qed.

Lemma nstack1_transpose : forall {n} (zx : ZX 1 1),
  (n ↑ zx)⊤ = n ↑ (zx ⊤).
Proof.
  intros.
  induction n.
  - easy.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma nstack_transpose {n m} k (zx : ZX n m) : 
  (k ⇑ zx) ⊤ = k ⇑ (zx ⊤).
Proof.
  induction k; [reflexivity|].
  cbn; now rewrite IHk.
Qed.

Lemma n_wire_transpose n : (n_wire n) ⊤ = n_wire n.
Proof.
  apply nstack1_transpose.
Qed.

Lemma nbox_tranpose n : (n_box n) ⊤ = n_box n.
Proof. 
  apply nstack1_transpose.
Qed.



Lemma Z_spider_1_1_fusion : forall {nIn nOut} α β, 
  (Z nIn 1 α) ⟷ (Z 1 nOut β) ∝=
  Z nIn nOut (α + β).
Proof.
  intros nIn nOut α β.
  unfold proportional_by_1.
  apply Z_spider_1_1_fusion_eq.
Qed.

Lemma X_spider_1_1_fusion : forall {nIn nOut} α β, 
  (X nIn 1 α) ⟷ (X 1 nOut β) ∝=
  X nIn nOut (α + β).
Proof.
  intros nIn nOut α β.
  apply colorswap_diagrams_eq.
  simpl.
  apply Z_spider_1_1_fusion.
Qed.