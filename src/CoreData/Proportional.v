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
Notation " t1 '≡' t2 'by' eval" := 
  (proportional_general eval eval t1 t2) (at level 70). (* \equiv *)

(* ZX Proportionality *)

Definition proportional_by {n m} (c : C) (zx0 zx1 : ZX n m) :=
  c .* ⟦ zx0 ⟧ = ⟦ zx1 ⟧ /\ c <> C0.

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

Add Parametric Morphism n m c : (@proportional_by n m c) with signature
  proportional_by_1 ==> proportional_by_1 ==> iff 
  as proportional_by_proper_eq.
Proof.
  unfold proportional_by, proportional_by_1.
  now intros ? ? -> ? ? ->.
Qed.

(* Add Parametric Morphism n m o c d : (@Compose n m o) with signature
  proportional_by c ==> proportional_by d ==> proportional_by (c * d)
  as compose_prop_by_proper.
Proof.
  unfold proportional_by, proportional_by_1.
  cbn [ZX_semantics].
  intros ? ? [<- ?] ? ? [<- ?].
  split; [|now apply Cmult_neq_0].
  distribute_scale.
  now rewrite Cmult_comm.
Qed.

Add Parametric Morphism n m o p c d : (@Stack n m o p) with signature
  proportional_by c ==> proportional_by d ==> proportional_by (c * d)
  as stack_prop_by_proper.
Proof.
  unfold proportional_by, proportional_by_1.
  cbn [ZX_semantics].
  intros ? ? [<- ?] ? ? [<- ?].
  split; [|now apply Cmult_neq_0].
  distribute_scale.
  now rewrite Cmult_comm.
Qed. *)

(* FIXME: Move *)
Lemma Cdiv_0_l c : 0 / c = 0.
Proof. apply Cmult_0_l. Qed.

Lemma Cdiv_nonzero_iff (c d : C) : c <> 0 ->
  d / c <> 0 <-> d <> 0.
Proof.
  intros Hc.
  split.
  - intros Hdc ->.
    now rewrite Cdiv_0_l in Hdc.
  - intros Hd. 
    now apply Cdiv_nonzero.
Qed.

Lemma Cmult_nonzero_iff (c d : C) : 
  c * d <> 0 <-> c <> 0 /\ d <> 0.
Proof.
  split.
  - intros Hcd.
    split.
    + intros ->.
      now rewrite Cmult_0_l in Hcd.
    + intros ->.
      now rewrite Cmult_0_r in Hcd.
  - intros [].
    now apply Cmult_neq_0.
Qed.


Lemma compose_prop_by_if_l {n m o} (zx0 zx1 : ZX n m) 
  (zx2 : ZX m o) (zx3 : ZX n o) c d : zx0 ∝[c] zx1 ->
  zx0 ⟷ zx2 ∝[d] zx3 <-> zx1 ⟷ zx2 ∝[d / c] zx3.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [<- Hc].
  distribute_scale.
  replace (d / c * c) with d by C_field.
  apply ZifyClasses.and_morph; [reflexivity|].
  symmetry.
  now apply Cdiv_nonzero_iff.
Qed.

Lemma compose_prop_by_if_r {n m o} (zx0 : ZX n m) 
  (zx1 zx2 : ZX m o) (zx3 : ZX n o) c d : zx1 ∝[c] zx2 ->
  zx0 ⟷ zx1 ∝[d] zx3 <-> zx0 ⟷ zx2 ∝[d / c] zx3.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [<- Hc].
  distribute_scale.
  replace (d / c * c) with d by C_field.
  apply ZifyClasses.and_morph; [reflexivity|].
  symmetry.
  now apply Cdiv_nonzero_iff.
Qed.

Lemma stack_prop_by_if_l {n m o p} (zx0 zx1 : ZX n m) 
  (zx2 : ZX o p) zx3 c d : zx0 ∝[c] zx1 ->
  zx0 ↕ zx2 ∝[d] zx3 <-> zx1 ↕ zx2 ∝[d / c] zx3.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [<- Hc].
  restore_dims.
  distribute_scale.
  replace (d / c * c) with d by C_field.
  apply ZifyClasses.and_morph; [reflexivity|].
  symmetry.
  now apply Cdiv_nonzero_iff.
Qed.

Lemma stack_prop_by_if_r {n m o p} (zx0 : ZX n m) 
  (zx1 zx2 : ZX o p) zx3 c d : zx1 ∝[c] zx2 ->
  zx0 ↕ zx1 ∝[d] zx3 <-> zx0 ↕ zx2 ∝[d / c] zx3.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [<- Hc].
  restore_dims.
  distribute_scale.
  replace (d / c * c) with d by C_field.
  apply ZifyClasses.and_morph; [reflexivity|].
  symmetry.
  now apply Cdiv_nonzero_iff.
Qed.


Lemma compose_prop_by_compat_l {n m o} (zx0 zx1 : ZX n m) 
  (zx2 : ZX m o) c : zx0 ∝[c] zx1 ->
  zx0 ⟷ zx2 ∝[c] zx1 ⟷ zx2.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [<- Hc].
  distribute_scale.
  split; [reflexivity|auto].
Qed.

Lemma compose_prop_by_compat_r {n m o} (zx0 : ZX n m) 
  (zx1 zx2 : ZX m o) c : zx1 ∝[c] zx2 ->
  zx0 ⟷ zx1 ∝[c] zx0 ⟷ zx2.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [<- Hc].
  distribute_scale.
  split; [reflexivity|auto].
Qed.

Lemma stack_prop_by_compat_l {n m o p} (zx0 zx1 : ZX n m) 
  (zx2 : ZX o p) c : zx0 ∝[c] zx1 ->
  zx0 ↕ zx2 ∝[c] zx1 ↕ zx2.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [<- Hc].
  distribute_scale.
  split; [reflexivity|auto].
Qed.

Lemma stack_prop_by_compat_r {n m o p} (zx0 : ZX n m) 
  (zx1 zx2 : ZX o p) c : zx1 ∝[c] zx2 ->
  zx0 ↕ zx1 ∝[c] zx0 ↕ zx2.
Proof.
  unfold proportional_by.
  cbn [ZX_semantics].
  intros [<- Hc].
  distribute_scale.
  split; [reflexivity|auto].
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
  intros [<- Hc].
  now rewrite Mscale_trans.
Qed.

Lemma colorswap_prop_by_compat {n m} (zx0 zx1 : ZX n m) c : 
  zx0 ∝[c] zx1 -> 
  ⊙ zx0 ∝[c] ⊙ zx1.
Proof.
  unfold proportional_by.
  rewrite 2!semantics_colorswap_comm.
  intros [<- Hc].
  now distribute_scale.
Qed.

Lemma adjoint_prop_by_compat {n m} (zx0 zx1 : ZX n m) c : 
  zx0 ∝[c ^*] zx1 -> 
  zx0 † ∝[c] zx1 †.
Proof.
  unfold proportional_by.
  rewrite 2!semantics_adjoint_comm.
  intros [<- Hc].
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

Lemma eq_sym_iff {A} (a b : A) : a = b <-> b = a.
Proof. easy. Qed.

Lemma proportional_by_trans_iff_l {n m} (zx0 zx1 zx2 : ZX n m) c d : 
  zx0 ∝[c] zx1 -> (zx0 ∝[d] zx2 <-> zx1 ∝[d / c] zx2).
Proof.
  unfold proportional_by.
  intros [<- Hc].
  distribute_scale.
  replace (d / c * c) with d by C_field.
  apply ZifyClasses.and_morph; [reflexivity|].
  rewrite Cdiv_nonzero_iff;
  intuition auto.
Qed.

Lemma proportional_by_trans_iff_r {n m} (zx0 zx1 zx2 : ZX n m) c d : 
  zx1 ∝[c] zx2 -> (zx0 ∝[d] zx1 <-> zx0 ∝[d * c] zx2).
Proof.
  unfold proportional_by.
  intros [<- Hc].
  distribute_scale.
  apply ZifyClasses.and_morph.
  - symmetry.
    rewrite eq_sym_iff.
    rewrite Mscale_inv by auto.
    distribute_scale.
    replace (/ c * (d * c)) with d by C_field.
    apply eq_sym_iff.
  - rewrite Cmult_nonzero_iff.
    intuition auto.
Qed.

Ltac zxrw H :=
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
      assert (Hrw : rwt) by auto 100 with zx_prop_by_db nocore;
      apply <- (proportional_by_trans_iff_l _ _ zxR rwfac fac Hrw);
      clear Hrw
    end
  | |- ?zxL ∝[ ?fac ] ?zxR => 
    let Rpat := eval pattern rwsrc in zxR in 
    lazymatch Rpat with 
    | (fun _ => ?P) _ => let r := constr:(P) in fail
    | (fun x => @?P x) _ => 
      let rwt := eval cbn beta in (P rwsrc ∝[rwfac] P rwtgt) in 
      assert (Hrw : rwt) by auto 100 with zx_prop_by_db nocore;
      apply <- (proportional_by_trans_iff_r zxL _ _ rwfac fac Hrw);
      clear Hrw
    end
  end
  end.

Lemma proportional_by_refl_iff {n m} (zx0 zx1 : ZX n m) c : 
  c = C1 ->
  zx0 ∝[c] zx1 <-> zx0 ∝= zx1.
Proof.
  intros ->.
  now rewrite proportional_by_1_defn.
Qed.

Ltac zxprop_refl :=
  apply proportional_by_refl_iff;
  [(repeat match goal with
    | H : _ ∝[_] _ |- _ => destruct H as [? ?]
    end); try (now C_field)
  | try reflexivity].
  

Lemma zxprop_test {n m o p} (zxnm0 zxnm1 : ZX n m)
  (zxop0 zxop1 : ZX o p) (c d : C) : zxnm0 ∝[c] zxnm1 -> 
  zxop0 ∝[d] zxop1 -> zxnm0 ↕ zxop0 ∝[c * d] zxnm1 ↕ zxop1.
Proof.
  intros Hnm Hop.
  zxrw Hnm.
  zxrw Hop.
  zxprop_refl.
Qed.








Definition proportional {n m} 
  (zx_0 : ZX n m) (zx_1 : ZX n m) := zx_0 ≡ zx_1 by ZX_semantics.
Notation "zx0 ∝ zx1" := (proportional zx0 zx1) (at level 70) : ZX_scope. (* \propto *)

Ltac prop_exists_nonzero c := 
  exists c; split; try apply nonzero_div_nonzero; try nonzero.
Ltac prep_proportional := unfold proportional; intros; split; [split; lia | ].
Ltac solve_prop c := 
	prop_exists_nonzero c; simpl; Msimpl; 
	unfold X_semantics; unfold Z_semantics; simpl; solve_matrix; 
	autorewrite with Cexp_db; lca.


Lemma proportional_general_refl : forall T n m eval (t : T), 
  @proportional_general T n m T n m eval eval t t.
Proof. prop_exists_nonzero 1; intros; lma. Qed.

Lemma proportional_general_symm : 
  forall T_0 n_0 m_0 T_1 n_1 m_1 eval_0 eval_1 (t0 : T_0) (t1: T_1), 
  @proportional_general T_0 n_0 m_0 T_1 n_1 m_1 eval_0 eval_1 t0 t1 -> 
  @proportional_general T_1 n_1 m_1 T_0 n_0 m_0 eval_1 eval_0 t1 t0.
Proof.
  intros.
  destruct H.
  exists (/x).
  destruct H.
  split.
  - rewrite H.  
    Msimpl.
    rewrite Mscale_assoc.
    rewrite Cinv_l; try lma.
    apply H0.
  - apply nonzero_div_nonzero.
    apply H0.
Qed.

Lemma proportional_general_trans : 
  forall T_0 n_0 m_0 eval_0 (t0 : T_0) 
         T_1 n_1 m_1 eval_1 (t1 : T_1) 
         T_2 n_2 m_2 eval_2 (t2 : T_2),
    @proportional_general T_0 n_0 m_0 T_1 n_1 m_1 eval_0 eval_1 t0 t1 -> 
    @proportional_general T_1 n_1 m_1 T_2 n_2 m_2 eval_1 eval_2 t1 t2 -> 
    @proportional_general T_0 n_0 m_0 T_2 n_2 m_2 eval_0 eval_2 t0 t2.
Proof.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  exists (x * x0).
  split.
  - rewrite <- Mscale_assoc.
    rewrite <- H0.
    rewrite H.
    reflexivity.
  - apply Cmult_neq_0; try assumption. 
Qed.


Lemma proportional_refl : forall {n m} (zx : ZX n m), 
  zx ∝ zx.
Proof. intros; apply proportional_general_refl. Qed.

Lemma proportional_symm : forall {n m} (zx_0 : ZX n m) (zx_1 : ZX n m),
  zx_0 ∝ zx_1 -> zx_1 ∝ zx_0.
Proof. intros; apply proportional_general_symm; apply H. Qed.

Lemma proportional_trans : forall {n m} 
  (zx0 : ZX n m) (zx1 : ZX n m) (zx2 : ZX n m),
  zx0 ∝ zx1 -> zx1 ∝ zx2 -> zx0 ∝ zx2.
Proof. 
  intros.
  apply (proportional_general_trans _ _ _ _ _ _ n m ZX_semantics zx1); 
  assumption.
Qed.

Add Parametric Relation (n m : nat) : (ZX n m) (proportional)
  reflexivity proved by proportional_refl
  symmetry proved by proportional_symm
  transitivity proved by proportional_trans
  as zx_prop_equiv_rel.

Lemma stack_compat :
  forall n0 m0 n1 m1,
    forall (zx0 : ZX n0 m0) (zx2 : ZX n0 m0), zx0 ∝ zx2 ->
    forall (zx1 : ZX n1 m1) (zx3 : ZX n1 m1), zx1 ∝ zx3 ->
    zx0 ↕ zx1 ∝ zx2 ↕ zx3.
Proof.
  intros n0 m0 n1 m1 zx0 zx2 [x [Hzx0 Hx]] zx1 zx3 [x0 [Hzx1 Hx0]].
  prop_exists_nonzero (x * x0); [ | (apply Cmult_neq_0; auto)]. 
  simpl.
  rewrite Hzx0, Hzx1.
  lma.
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
  forall n m o,
    forall (zx0 : ZX n m) (zx2 : ZX n m), zx0 ∝ zx2 ->
    forall (zx1 : ZX m o) (zx3 : ZX m o), zx1 ∝ zx3 ->
    zx0 ⟷ zx1 ∝ zx2 ⟷ zx3.
Proof.
  intros n m o zx0 zx2 [x [Hzx0 Hx]] zx1 zx3 [x0 [Hzx1 Hx0]].
  prop_exists_nonzero (x * x0); [ | (apply Cmult_neq_0; auto)]. 
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
  forall n m n' m' prfn0 prfm0,
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
  forall n m,
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
  forall n m,
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

Lemma colorswap_is_bihadamard : forall n m (zx : ZX n m),
  ⊙ zx ∝ (n ↑ □) ⟷ (zx ⟷ (m ↑ □)).
Proof.
  prop_exists_nonzero 1.
  Msimpl.
  simpl.
  rewrite 2 n_stack1_n_kron.
  simpl.
  rewrite semantics_colorswap_comm.
  easy.
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
  intros.
  prop_exists_nonzero 1.
  rewrite H; lma.
Qed.

(* Useful Lemmas *)

Lemma nstack1_transpose : forall n (zx : ZX 1 1),
  (n ↑ zx)⊤ ∝ n ↑ (zx ⊤).
Proof.
  intros.
  induction n.
  - easy.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma transpose_involutive : forall n m (zx : ZX n m),
  zx ⊤ ⊤ ∝ zx.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  repeat rewrite semantics_transpose_comm.
  rewrite transpose_involutive.
  lma.
Qed.

Lemma adjoint_involutive : forall n m (zx : ZX n m),
  zx † † ∝ zx.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  repeat rewrite semantics_adjoint_comm.
  rewrite adjoint_involutive.
  lma.
Qed.

Lemma colorswap_involutive : forall n m (zx : ZX n m),
  (⊙ ⊙ zx) ∝ zx.
Proof.
  intros.
  induction zx; try (simpl; easy).
  all: simpl; rewrite IHzx1, IHzx2; easy.
Qed.

Lemma colorswap_diagrams : forall n m (zx0 zx1 : ZX n m),
  ⊙ zx0 ∝ ⊙ zx1 -> zx0 ∝ zx1.
Proof.
  intros.
  rewrite <- colorswap_involutive.
  rewrite H.
  apply colorswap_involutive.
Qed.

Lemma transpose_diagrams : forall n m (zx0 zx1 : ZX n m),
  zx0 ⊤ ∝ zx1 ⊤ -> zx0 ∝ zx1.
Proof.
  intros n m zx0 zx1 [x [Hzx Hx]].
  prop_exists_nonzero x; try assumption.
  apply transpose_matrices.
  rewrite Mscale_trans.
  repeat rewrite <- semantics_transpose_comm.
  apply Hzx.
Qed.

Lemma adjoint_diagrams : forall n m (zx0 zx1 : ZX n m),
  zx0 † ∝ zx1 † -> zx0 ∝ zx1.
Proof.
  intros n m zx0 zx1 [x [Hzx Hx]].
  prop_exists_nonzero (x ^*)%C.
  apply adjoint_matrices.
  rewrite Mscale_adj.
  repeat rewrite <- semantics_adjoint_comm.
  rewrite Cconj_involutive.
  apply Hzx.
  apply Cconj_neq_0.
  assumption.
Qed.

Lemma colorswap_adjoint_commute : forall n m (zx : ZX n m),
  ⊙ (zx †) ∝ (⊙ zx) †.
Proof.
  intros.
  induction zx; try easy.
  all: simpl; rewrite IHzx1, IHzx2; easy.
Qed.

Lemma transpose_adjoint_commute : forall n m (zx : ZX n m),
  (zx †) ⊤ ∝ (zx ⊤) †.
Proof.
  intros.
  induction zx; try easy.
  all: simpl; rewrite IHzx1, IHzx2; easy.
Qed.

Lemma colorswap_transpose_commute : forall n m (zx : ZX n m),
  ⊙ (zx ⊤) ∝ (⊙ zx) ⊤.
Proof.
  intros.
  induction zx; try easy.
  all: simpl; rewrite IHzx1, IHzx2; easy.
Qed.


Lemma transpose_wire : Wire ⊤ ∝ Wire.
Proof.
  prop_exists_nonzero 1.
  simpl; lma.
Qed.

Lemma Z_spider_1_1_fusion : forall {nIn nOut} α β, 
  (Z nIn 1 α) ⟷ (Z 1 nOut β) ∝
  Z nIn nOut (α + β).
Proof.
  prop_exists_nonzero 1.
  Msimpl.
  apply Z_spider_1_1_fusion_eq.
Qed.

Lemma X_spider_1_1_fusion : forall {nIn nOut} α β, 
  (X nIn 1 α) ⟷ (X 1 nOut β) ∝
  X nIn nOut (α + β).
Proof.
  intros.
  apply colorswap_diagrams.
  simpl.
  apply Z_spider_1_1_fusion.
Qed.

Lemma proportional_sound : forall {nIn nOut} (zx0 zx1 : ZX nIn nOut),
  zx0 ∝ zx1 -> exists (zxConst : ZX 0 0), ⟦ zx0 ⟧ = ⟦ zxConst ↕ zx1 ⟧.
Proof.
  intros.
  simpl; unfold proportional, proportional_general in H.
  destruct H as [c [H cneq0]].
  rewrite H.
Abort.