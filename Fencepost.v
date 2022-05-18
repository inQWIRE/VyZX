Require Import ZX.
Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.Proportional.
Require Import externals.QuantumLib.VectorStates.
Require Import Coq.Logic.Eqdep_dec.

Inductive ZX_PostPred : forall {nIn nOut}, ZX nIn nOut -> Prop := 
  | Post_Empty                         : ZX_PostPred Empty
  | Post_Cap                           : ZX_PostPred Cap
  | Post_Cup                           : ZX_PostPred Cup
  | Post_Swap                          : ZX_PostPred Swap
  | Post_Z {nIn0 nOut0 α}              : ZX_PostPred (Z_Spider nIn0 nOut0 α)
  | Post_X {nIn0 nOut0 α}              : ZX_PostPred (X_Spider nIn0 nOut0 α)
  | Post_Stack {nIn0 nOut0 nIn1 nOut1} : 
      forall (zx0 : ZX nIn0 nOut0) (zx1 : ZX nIn1 nOut1),
              ZX_PostPred zx0 -> ZX_PostPred zx1 -> ZX_PostPred (zx0 ↕ zx1).

Lemma Post_Unstack_L {nIn0 nOut0 nIn1 nOut1} {zx0 : ZX nIn0 nOut0} {zx1 : ZX nIn1 nOut1} :
  ZX_PostPred (zx0 ↕ zx1) -> ZX_PostPred zx0.
Proof.
  intros; inversion H; subst.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in H9; apply (inj_pair2_eq_dec _ Nat.eq_dec) in H9; subst; assumption.
Qed.

Lemma Post_Unstack_R {nIn0 nOut0 nIn1 nOut1} {zx0 : ZX nIn0 nOut0} {zx1 : ZX nIn1 nOut1} :
  ZX_PostPred (zx0 ↕ zx1) -> ZX_PostPred zx1.
Proof.
  intros; inversion H; subst.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in H10; apply (inj_pair2_eq_dec _ Nat.eq_dec) in H10; subst; assumption.
Qed.

Lemma Post_NoComp {nIn nMid nOut} {zx0 : ZX nIn nMid} {zx1 : ZX nMid nOut} :
  ~ (ZX_PostPred (zx0 ⟷ zx1)).
Proof. unfold not; intros; inversion H. Qed.

Inductive ZX_FencePred : forall {nIn nOut}, ZX nIn nOut -> Prop :=
  | IsPost {nIn0 nOut0} : forall (zx : ZX nIn0 nOut0), ZX_PostPred zx -> ZX_FencePred zx
  | FenceCompose {nIn0 nMid0 nOut0} : 
    forall (zxl : ZX nIn0 nMid0) (zxr : ZX nMid0 nOut0),
      ZX_FencePred zxl -> ZX_FencePred zxr ->
      ZX_FencePred (zxl ⟷ zxr).

Lemma Fence_Unstack_L {nIn0 nOut0 nIn1 nOut1} {zx0 : ZX nIn0 nOut0} {zx1 : ZX nIn1 nOut1} :
  ZX_FencePred (zx0 ↕ zx1) -> ZX_PostPred zx0.
Proof.
  intros.
  inversion H; subst.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in H0.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in H0; subst.
  apply Post_Unstack_L in H3.
  auto.
Qed.

Lemma Fence_Unstack_R {nIn0 nOut0 nIn1 nOut1} {zx0 : ZX nIn0 nOut0} {zx1 : ZX nIn1 nOut1} :
  ZX_FencePred (zx0 ↕ zx1) -> ZX_PostPred zx1.
Proof.
  intros.
  inversion H; subst.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in H0.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in H0; subst.
  apply Post_Unstack_R in H3.
  auto.
Qed.

Lemma Fence_Decompose_L {nIn nMid nOut} {zx0 : ZX nIn nMid} {zx1 : ZX nMid nOut} :
  ZX_FencePred (zx0 ⟷ zx1) -> ZX_FencePred zx0.
Proof.
  intros.
  inversion H.
  - apply (inj_pair2_eq_dec _ Nat.eq_dec) in H0;
    apply (inj_pair2_eq_dec _ Nat.eq_dec) in H0; subst.
    destruct (Post_NoComp H3).
  - apply (inj_pair2_eq_dec _ Nat.eq_dec) in H1;
    apply (inj_pair2_eq_dec _ Nat.eq_dec) in H1; subst.
    auto.
Qed.
    
Lemma Fence_Decompose_R {nIn nMid nOut} {zx0 : ZX nIn nMid} {zx1 : ZX nMid nOut} :
  ZX_FencePred (zx0 ⟷ zx1) -> ZX_FencePred zx1.
Proof.
  intros.
  inversion H.
  - apply (inj_pair2_eq_dec _ Nat.eq_dec) in H0;
    apply (inj_pair2_eq_dec _ Nat.eq_dec) in H0; subst.
    destruct (Post_NoComp H3).
  - apply (inj_pair2_eq_dec _ Nat.eq_dec) in H5;
    apply (inj_pair2_eq_dec _ Nat.eq_dec) in H5; subst.
    auto.
Qed.

Local Open Scope R_scope.
Inductive ZX_Post : nat -> nat -> Type :=
  | P_Empty : ZX_Post 0 0
  | P_X_Spider nIn nOut (α : R) : ZX_Post nIn nOut
  | P_Z_Spider nIn nOut (α : R) : ZX_Post nIn nOut
  | P_Cap : ZX_Post 0 2
  | P_Cup : ZX_Post 2 0
  | P_Swap : ZX_Post 2 2
  | P_Stack {nIn0 nIn1 nOut0 nOut1} (zx0 : ZX_Post nIn0 nOut0) (zx1 : ZX_Post nIn1 nOut1) :
      ZX_Post (nIn0 + nIn1) (nOut0 + nOut1).
Local Close Scope R_scope.

Inductive ZX_Fence : nat -> nat -> Type :=
  | FencePost {nIn nOut} (zxp : ZX_Post nIn nOut) : ZX_Fence nIn nOut
  | F_Compose {nIn nMid nOut} (zx0 : ZX_Fence nIn nMid) (zx1 : ZX_Fence nMid nOut) : ZX_Fence nIn nOut.

Fixpoint PostP_to_Post {nIn nOut} {zx : ZX nIn nOut} : ZX_PostPred zx -> ZX_Post nIn nOut.
Proof.
  destruct zx.
  - intros; apply P_Empty.
  - intros; apply P_X_Spider; auto.
  - intros; apply P_Z_Spider; auto.
  - intros; apply P_Cap.
  - intros; apply P_Cup.
  - intros; apply P_Swap.
  - intros; apply P_Stack.
    + apply (PostP_to_Post _ _ zx1).
      apply Post_Unstack_L in H.
      auto.
    + apply (PostP_to_Post _ _ zx2).
      apply Post_Unstack_R in H.
      auto.
  - intros.
    destruct (Post_NoComp H).
Defined.
  

Fixpoint FenceP_to_Fence {nIn nOut} {zx : ZX nIn nOut} : ZX_FencePred zx -> ZX_Fence nIn nOut.
Proof.
  destruct zx.
  - intros; apply FencePost; apply P_Empty.
  - intros; apply FencePost; apply P_X_Spider; apply α.
  - intros; apply FencePost; apply P_Z_Spider; apply α.
  - intros; apply FencePost; apply P_Cap.
  - intros; apply FencePost; apply P_Cup.
  - intros; apply FencePost; apply P_Swap.
  - intros; apply FencePost; apply P_Stack.
    + apply Fence_Unstack_L in H.
      apply (PostP_to_Post H).
    + apply Fence_Unstack_R in H.
      apply (PostP_to_Post H).
  - intros.
    apply (@F_Compose nIn nMid nOut).
    + apply Fence_Decompose_L in H. 
      apply (FenceP_to_Fence _ _ _ H).
    + apply Fence_Decompose_R in H.
      apply (FenceP_to_Fence _ _ _ H).
Defined.

