Require Import ZX.
Require Import Rules.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Proportional.
Require Import QuantumLib.VectorStates.
Require Import Coq.Logic.Eqdep_dec.


Local Open Scope R_scope.
Definition isZero (a : R) : bool := true.

Definition isWire {nIn nOut} (D : ZX nIn nOut) : bool :=
  match D with
  | X_Spider _ _ r | Z_Spider _ _ r => 
      match Req_EM_T r 0 with
      | left _ => true
      | _ => false
      end
  | _ => false
  end.

Fixpoint allWires {nIn nOut} (D : ZX nIn nOut) : bool :=
  match D with
  | Compose D1 D2 | Stack D1 D2 => allWires D1 && allWires D2
  | other => isWire other
  end.

Fixpoint isSparseFencepost {nIn nOut} (D : ZX nIn nOut) : bool := 
  match D with
  | Compose DL DR => isSparseFencepost DL && isSparseFencepost DR
  | Stack   DT DB => (allWires DT && isSparseFencepost DB) || (isSparseFencepost DT && allWires DB)
  | _ => true
  end.

Fixpoint noComposes {nIn nOut} (D : ZX nIn nOut) : bool :=
  match D with
  | Compose _ _ => false
  | Stack DT DB => noComposes DT && noComposes DB
  | _ => true
  end.

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

Lemma PostPred_reflect {nIn nOut} : forall (zx : ZX nIn nOut),  reflect (ZX_PostPred zx) (noComposes zx).
Proof.
  intros.
  induction zx; (try (constructor; constructor)).
  - simpl; destruct (noComposes zx1), (noComposes zx2).
    1: constructor; constructor; 
       [ inversion IHzx1; assumption
       | inversion IHzx2; assumption ].
    all: constructor; unfold not; intros;
         inversion H; subst; inversion IHzx1; inversion IHzx2;
         apply (inj_pair2_eq_dec _ Nat.eq_dec) in H9;
         apply (inj_pair2_eq_dec _ Nat.eq_dec) in H9;
         apply (inj_pair2_eq_dec _ Nat.eq_dec) in H10;
         apply (inj_pair2_eq_dec _ Nat.eq_dec) in H10; subst;
         contradiction.
  - constructor; unfold not; intros C; inversion C.
Qed.

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

Fixpoint isFencepost {nIn nOut} (D : ZX nIn nOut) : bool :=
  match D with
  | Compose DL DR => isFencepost DL && isFencepost DR
  | other => noComposes other
  end.

Inductive ZX_FencePred : forall {nIn nOut}, ZX nIn nOut -> Prop :=
  | IsPost {nIn0 nOut0} : forall (zx : ZX nIn0 nOut0), ZX_PostPred zx -> ZX_FencePred zx
  | FenceCompose {nIn0 nMid0 nOut0} : 
    forall (zxl : ZX nIn0 nMid0) (zxr : ZX nMid0 nOut0),
      ZX_FencePred zxl -> ZX_FencePred zxr ->
      ZX_FencePred (zxl ⟷ zxr).

Lemma FencePred_reflect {nIn nOut} : forall (zx : ZX nIn nOut),  reflect (ZX_FencePred zx) (isFencepost zx).
Proof.
  intros.
  induction zx; try (constructor; constructor; constructor).
  - simpl.
    destruct (noComposes zx1) eqn:E1, (noComposes zx2) eqn:E2.
    1:  constructor; constructor;
        specialize (PostPred_reflect zx1); specialize (PostPred_reflect zx2); intros PP2 PP1;
        rewrite E1 in PP1; rewrite E2 in PP2;
        inversion PP1; inversion PP2;
        constructor; assumption.
    all:  constructor; unfold not; intros C;
          inversion C; subst;
          apply (inj_pair2_eq_dec _ Nat.eq_dec) in H;
          apply (inj_pair2_eq_dec _ Nat.eq_dec) in H; subst;
          inversion H2; subst;
          apply (inj_pair2_eq_dec _ Nat.eq_dec) in H9;
          apply (inj_pair2_eq_dec _ Nat.eq_dec) in H9;
          apply (inj_pair2_eq_dec _ Nat.eq_dec) in H10;
          apply (inj_pair2_eq_dec _ Nat.eq_dec) in H10; subst;
          specialize (PostPred_reflect zx2); specialize (PostPred_reflect zx1); intros PP1 PP2;
          rewrite E2 in PP2;
          rewrite E1 in PP1;
          inversion PP1;
          inversion PP2;
          contradiction.
  - simpl.
    destruct (isFencepost zx1), (isFencepost zx2).
    1: constructor; apply FenceCompose; [ inversion IHzx1 | inversion IHzx2 ]; assumption.
    all:  constructor; unfold not; intros C;
          inversion C;
          [ apply (inj_pair2_eq_dec _ Nat.eq_dec) in H;
            apply (inj_pair2_eq_dec _ Nat.eq_dec) in H; subst;
            inversion H2
          | apply (inj_pair2_eq_dec _ Nat.eq_dec) in H0;
            apply (inj_pair2_eq_dec _ Nat.eq_dec) in H0; subst;
            apply (inj_pair2_eq_dec _ Nat.eq_dec) in H4;
            apply (inj_pair2_eq_dec _ Nat.eq_dec) in H4; subst;
            inversion IHzx1; inversion IHzx2;
            contradiction ].
Qed.

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

Inductive ZX_Sparse_Obj : nat -> nat -> Type :=
  | SO_Empty : ZX_Sparse_Obj 0 0
  | SO_X_Spider nIn nOut (α : R) : ZX_Sparse_Obj nIn nOut
  | SO_Z_Spider nIn nOut (α : R) : ZX_Sparse_Obj nIn nOut
  | SO_Cap : ZX_Sparse_Obj 0 2
  | SO_Cup : ZX_Sparse_Obj 2 0
  | SO_Swap : ZX_Sparse_Obj 2 2.

Inductive ZX_Sparse_Post : nat -> nat -> Type :=
  | SP_Stack {nIn nOut} above (object : ZX_Sparse_Obj nIn nOut) below : ZX_Sparse_Post (above + nIn + below) (above + nOut + below).

Inductive ZX_Sparse_Fence : nat -> nat -> Type :=
  | SF_Post {nIn nOut} (p : ZX_Sparse_Post nIn nOut) : ZX_Sparse_Fence nIn nOut
  | SF_Fence_Comp {nIn nMid nOut} (f1 : ZX_Sparse_Fence nIn nMid) (f2 : ZX_Sparse_Fence nMid nOut) : ZX_Sparse_Fence nIn nOut.

Definition ZX_Sparse_Obj_to_ZX {nIn nOut} (o : ZX_Sparse_Obj nIn nOut) : ZX nIn nOut :=
  match o with
  | SO_Empty => ⦰
  | SO_X_Spider nIn nOut α => X_Spider nIn nOut α 
  | SO_Z_Spider nIn nOut α => Z_Spider nIn nOut α 
  | SO_Cap => Cap
  | SO_Cup => Cup
  | SO_Swap => Swap
  end.

Definition ZX_Sparse_Post_to_ZX {nIn nOut} (p : ZX_Sparse_Post nIn nOut) : ZX nIn nOut :=
  match p with 
  | SP_Stack above object below  => (nWire above ↕ ZX_Sparse_Obj_to_ZX object ↕ nWire below)
  end.

Fixpoint ZX_Sparse_Fence_to_ZX {nIn nOut} (f : ZX_Sparse_Fence nIn nOut) : ZX nIn nOut :=
  match f with
  | SF_Post p => ZX_Sparse_Post_to_ZX p
  | SF_Fence_Comp f1 f2 => ZX_Sparse_Fence_to_ZX f1 ⟷ ZX_Sparse_Fence_to_ZX f2
  end.

Definition ZX_Sparse_Obj_semantics {nIn nOut} (obj : ZX_Sparse_Obj nIn nOut) : Matrix (2 ^ nOut) (2 ^ nIn) :=
  match obj with
  | SO_Empty => I 1
  | SO_X_Spider _ _ α => X_semantics nIn nOut α
  | SO_Z_Spider _ _ α => Z_semantics nIn nOut α
  | SO_Cup => ZX_semantics Cup
  | SO_Cap => ZX_semantics Cap
  | SO_Swap => swap
  end.

Lemma WF_ZX_Sparse_Obj_semantics : forall {nIn nOut} (obj : ZX_Sparse_Obj nIn nOut), WF_Matrix (ZX_Sparse_Obj_semantics obj).
Proof. Opaque ZX_semantics. intros; destruct obj; simpl; restore_dims; auto with wf_db. Transparent ZX_semantics. Qed.

Global Hint Resolve WF_ZX_Sparse_Obj_semantics : wf_db.

Definition ZX_Sparse_Post_semantics {nIn nOut} (zxs : ZX_Sparse_Post nIn nOut) : Matrix (2 ^ nOut) (2 ^ nIn) :=
  match zxs with
  | SP_Stack above obj below =>
      I (2 ^ above) ⊗ ZX_Sparse_Obj_semantics obj ⊗ I (2 ^ below)
  end.

Lemma WF_ZX_Sparse_Post_semantics : forall {nIn nOut} (p : ZX_Sparse_Post nIn nOut), WF_Matrix (ZX_Sparse_Post_semantics p).
Proof. intros; destruct p; simpl; auto with wf_db. Qed.

Global Hint Resolve WF_ZX_Sparse_Post_semantics : wf_db.

Fixpoint ZX_Sparse_Fence_semantics {nIn nOut} (zxs : ZX_Sparse_Fence nIn nOut) : Matrix (2 ^ nOut) (2 ^ nIn) :=
  match zxs with
  | SF_Post zxsp => ZX_Sparse_Post_semantics zxsp
  | SF_Fence_Comp zxf1 zxf2 =>
      ZX_Sparse_Fence_semantics zxf2 × ZX_Sparse_Fence_semantics zxf1
  end.

Lemma WF_ZX_Sparse_Fence_semantics : forall {nIn nOut} (f : ZX_Sparse_Fence nIn nOut), WF_Matrix (ZX_Sparse_Fence_semantics f).
Proof. intros; induction f; simpl; auto with wf_db. Qed.

Global Hint Resolve WF_ZX_Sparse_Fence_semantics : wf_db.

Lemma ZX_Sparse_Obj_semantics_conversion : forall {nIn nOut} (obj : ZX_Sparse_Obj nIn nOut), ZX_Sparse_Obj_semantics obj = ZX_semantics (ZX_Sparse_Obj_to_ZX obj).
Proof. destruct obj; easy. Qed.

Lemma ZX_Sparse_Post_semantics_conversion : forall {nIn nOut} (p : ZX_Sparse_Post nIn nOut), ZX_Sparse_Post_semantics p = ZX_semantics (ZX_Sparse_Post_to_ZX p).
Proof.
  destruct p.
  simpl.
  rewrite ZX_Sparse_Obj_semantics_conversion.
  rewrite 2 nwire_identity_semantics.
  easy.
Qed.

Lemma ZX_Sparse_Fence_semantics_conversion : forall {nIn nOut} (f : ZX_Sparse_Fence nIn nOut), ZX_Sparse_Fence_semantics f = ZX_semantics (ZX_Sparse_Fence_to_ZX f).
Proof.
  intros.
  induction f.
  + apply ZX_Sparse_Post_semantics_conversion.
  + simpl.
    rewrite IHf1, IHf2.
    easy.
Qed.  

Definition Height_Used_In {nIn nOut} (p : ZX_Sparse_Post nIn nOut) h :=
  match p with
  | @SP_Stack nInObj _ above _ _ => h >= above \/ h < (above + nInObj)
  end.

Definition Height_Used_Out {nIn nOut} (p : ZX_Sparse_Post nIn nOut) h :=
  match p with
  | @SP_Stack _ nOutObj above _ _ => h >= above \/ h < (above + nOutObj)
  end.

Definition NonInterference {nIn0 nOut0} (p0 : ZX_Sparse_Post nIn0 nOut0) {nIn1 nOut1} (p1 : ZX_Sparse_Post nIn1 nOut1) := forall h, Height_Used_Out p0 h -> ~(Height_Used_In p1 h).
