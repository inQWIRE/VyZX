Require Import ZXCore.
Require Import Setoid.
Require Import QuantumLib.Polar.
Require Import Coq.Reals.ClassicalDedekindReals.
Require Import Coq.Reals.Rdefinitions.
Require Import ZArith.
Module Import Zabs2N.

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

Lemma colorswap_compat :
  forall nIn nOut,
    forall zx0 zx1 : ZX nIn nOut, zx0 ∝ zx1 ->
    (⊙ zx0) ∝ (⊙ zx1).
Proof.
  intros.
  destruct H; destruct H; exists x; split; try assumption.
  rewrite 2 semantics_colorswap_comm.
  rewrite H.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  reflexivity.
Qed.

Add Parametric Morphism (nIn nOut : nat) : (@color_swap nIn nOut)
  with signature (@proportional nIn nOut) ==> (@proportional nIn nOut) 
    as colorswap_mor.
Proof. apply colorswap_compat. Qed.

Theorem sem_eq_prop : forall {n m} (zx0 : ZX n m) (zx1 : ZX n m),
  ZX_semantics zx0 = ZX_semantics zx1 -> zx0 ∝ zx1.
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
  ⊙ zx0 ∝ ⊙zx1 -> zx0 ∝ zx1.
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
  zx0 ∝ zx1 -> exists (zxConst : ZX 0 0), ZX_semantics zx0 = ZX_semantics (zxConst ↕ zx1).
Proof.
  intros.
  simpl; unfold proportional, proportional_general in H.
  destruct H as [c [H cneq0]].
  rewrite H.
Abort.

Global Close Scope ZX_scope.
Print Visibility.

Lemma complex_decompose : forall z : C, 
  exists k (α β : R), z = (√2)^k * (1 + Cexp(α)) * (√2 * Cexp(β)).
Proof.
  intro.
  remember (rect_to_polar z) as polar.
  destruct polar as [r θ].
  remember (up (Rlog (√2) (r / 2))) as ceiling.
  exists ((Z.abs_N ceiling) + 1).
Abort.