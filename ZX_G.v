Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.VectorStates.
Require Export ZX.
Require Export ZX_H.
Require Export Gates.
Require Export GateRules.
Require Export Rules.
Require Export Proportional.
Require Import Setoid.

Local Declare Scope G_ZX_scope.
Local Open Scope G_ZX_scope.

Local Open Scope R_scope.
Inductive G_ZX : nat -> nat -> Type :=
  | G_Empty : G_ZX 0 0
  | G_Z_Spider_In nOut (α : R) : G_ZX 1 nOut
  | G_Z_Spider_Out nIn (α : R) : G_ZX nIn 1
  | G_Cap : G_ZX 0 2
  | G_Cup : G_ZX 2 0
  | G_Stack {nIn0 nIn1 nOut0 nOut1} (zx0 : G_ZX nIn0 nOut0) (zx1 : G_ZX nIn1 nOut1) :
        G_ZX (nIn0 + nIn1) (nOut0 + nOut1)
  | G_Compose {nIn nMid nOut} (zx0 : G_ZX nIn nMid) (zx1 : G_ZX nMid nOut) : G_ZX nIn nOut.
Local Close Scope R_scope.

Notation "⦰G" := G_Empty. (* \revemptyset *)
Notation "⊂G'" := G_Cap. (* \subset *)
Notation "⊃G'" := G_Cup. (* \supset *)
Infix "⟷G" := G_Compose (left associativity, at level 40). (* \longleftrightarrow *)
Infix "↕G" := G_Stack (left associativity, at level 40). (* \updownarrow *)

Fixpoint G_ZX_semantics {nIn nOut} (zx : G_ZX nIn nOut) : 
  Matrix (2 ^ nOut) (2 ^nIn) := 
  match zx with
  | ⦰G => H_ZX_semantics ⦰H
  | G_Z_Spider_In nOut α => H_ZX_semantics (H_Z_Spider 1 nOut α)
  | G_Z_Spider_Out nIn α => H_ZX_semantics (H_Z_Spider nIn 1 α)
  | G_Cap => H_ZX_semantics (H_Cap)
  | G_Cup => H_ZX_semantics (H_Cup)
  | zx0 ↕G zx1 => (G_ZX_semantics zx0) ⊗ (G_ZX_semantics zx1)
  | @G_Compose _ nMid _ zx0 zx1 => (G_ZX_semantics zx1) × (nMid ⨂ hadamard) × (G_ZX_semantics zx0)
  end.

Fixpoint G_ZX_to_H_ZX {nIn nOut} (zx : G_ZX nIn nOut) : H_ZX nIn nOut :=
  match zx with
  | G_Empty => H_Empty
  | G_Z_Spider_In nOut α => H_Z_Spider 1 nOut α
  | G_Z_Spider_Out nIn α => H_Z_Spider nIn 1 α
  | G_Cap => H_Cap
  | G_Cup => H_Cup
  | G_Stack zx0 zx1 => (G_ZX_to_H_ZX zx0) ↕H (G_ZX_to_H_ZX zx1)
  | G_Compose zx0 zx1 => (G_ZX_to_H_ZX zx0) ⟷H (G_ZX_to_H_ZX zx1)
  end.

Local Opaque H_ZX_semantics.
Lemma WF_G_ZX : forall nIn nOut (zx : G_ZX nIn nOut), WF_Matrix (G_ZX_semantics zx).
Proof.
  intros.
  induction zx; simpl; restore_dims; try auto with wf_db. 
Qed.
Local Transparent H_ZX_semantics.

Global Hint Resolve WF_G_ZX : wf_db.

Definition G_proportional {nIn nOut} (zx0 : G_ZX nIn nOut) (zx1 : G_ZX nIn nOut) :=
  proportional_general G_ZX_semantics zx0 zx1.

Infix "∝G" := G_proportional (at level 70).

Lemma G_proportional_refl : forall {nIn nOut} (zx : G_ZX nIn nOut), zx ∝G zx.
Proof.
  intros.
  apply proportional_general_refl.
Qed.

Lemma G_proportional_symm : forall {nIn nOut} (zx0 zx1 : G_ZX nIn nOut),
  zx0 ∝G zx1 -> zx1 ∝G zx0.
Proof.
  intros.
  apply proportional_general_symm; assumption.
Qed.

Lemma G_proportional_trans : forall {nIn nOut} (zx0 zx1 zx2 : G_ZX nIn nOut),
  zx0 ∝G zx1 -> zx1 ∝G zx2 -> zx0 ∝G zx2.
Proof.
  intros.
  apply (proportional_general_trans _ _ _ G_ZX_semantics zx0 zx1 zx2); assumption.
Qed.

Add Parametric Relation (nIn nOut : nat) : (G_ZX nIn nOut) (@G_proportional nIn nOut)
  reflexivity proved by G_proportional_refl
  symmetry proved by G_proportional_symm
  transitivity proved by G_proportional_trans
  as zx_g_prop_equiv_rel.

Lemma G_stack_compat :
  forall nIn0 nOut0 nIn1 nOut1,
    forall zx0 zx1 : G_ZX nIn0 nOut0, zx0 ∝G zx1 ->
    forall zx2 zx3 : G_ZX nIn1 nOut1, zx2 ∝G zx3 ->
    zx0 ↕G zx2 ∝G zx1 ↕G zx3.
Proof.
  intros.
  destruct H; destruct H; destruct H0; destruct H0.
  exists (x * x0).
  split.
  - simpl; rewrite H; rewrite H0.
    lma.
  - apply Cmult_neq_0; try assumption.
Qed.

Add Parametric Morphism (nIn0 nOut0 nIn1 nOut1 : nat) : (@G_Stack nIn0 nIn1 nOut0 nOut1)
  with signature (@G_proportional nIn0 nOut0) ==> (@G_proportional nIn1 nOut1) ==> 
                 (@G_proportional (nIn0 + nIn1) (nOut0 + nOut1)) as G_stack_mor.
Proof. apply G_stack_compat; assumption. Qed.

Local Open Scope C_scope.

Theorem G_ZX_to_H_ZX_consistent : forall nIn nOut (zx : G_ZX nIn nOut),
  G_ZX_semantics zx = (H_ZX_semantics (G_ZX_to_H_ZX zx)).
Proof.
  intros.
  induction zx; try auto;
  (* Composition cases *)
  simpl; rewrite IHzx1, IHzx2; reflexivity.
Qed.

Definition G_Wire := G_Z_Spider_Out 1 0.

Local Opaque H_ZX_semantics.
Local Transparent H_Wire.
Lemma G_wire_identity_semantics : G_ZX_semantics G_Wire = I 2.
Proof.
  simpl.
  rewrite <- H_wire_identity_semantics.
  unfold H_Wire.
  reflexivity.
Qed.
Local Transparent H_ZX_semantics.
Local Opaque H_Wire.
Local Opaque G_Wire.

Fixpoint H_ZX_to_G_ZX {nIn nOut} (zx : H_ZX nIn nOut) : G_ZX nIn nOut :=
  match zx with
  | H_Empty => G_Empty
  | H_Z_Spider nIn nOut α => G_Z_Spider_Out nIn α ⟷G G_Wire ⟷G G_Z_Spider_In nOut 0%R
  | H_Cap => G_Cap
  | H_Cup => G_Cup
  | zx0 ↕H zx1 => (H_ZX_to_G_ZX zx0) ↕G (H_ZX_to_G_ZX zx1)
  | zx0 ⟷H zx1 => (H_ZX_to_G_ZX zx0) ⟷G (H_ZX_to_G_ZX zx1)
  end.

Theorem H_ZX_to_G_ZX_consistent : forall nIn nOut (zx : H_ZX nIn nOut),
  H_ZX_semantics zx = (G_ZX_semantics (H_ZX_to_G_ZX zx)).
Proof.
  intros.
  induction zx; try auto;
  (* Composition *)
  try (simpl;
  rewrite IHzx1, IHzx2;
  reflexivity). 
  (* Interesting case: Spider fusion *)
  Local Opaque ZX_semantics.
  simpl.
  rewrite G_wire_identity_semantics.
  Msimpl.
  rewrite <- Mmult_assoc.
  rewrite (Mmult_assoc _ hadamard hadamard).
  rewrite MmultHH.
  Msimpl.
  rewrite <- ZX_semantics_Compose.
  rewrite Z_spider_1_1_fusion_eq.
  rewrite Rplus_0_r.
  reflexivity.
  Local Transparent ZX_semantics.
Qed.

Definition ZX_to_G_ZX {nIn nOut} (zx : ZX nIn nOut) := H_ZX_to_G_ZX (ZX_to_H_ZX zx).
Definition G_ZX_to_ZX {nIn nOut} (zx : G_ZX nIn nOut) := H_ZX_to_ZX (G_ZX_to_H_ZX zx).

Theorem G_ZX_to_ZX_consistent : forall nIn nOut (zx : G_ZX nIn nOut),
  exists (θ : R), G_ZX_semantics zx = (Cexp θ) .* (ZX_semantics (G_ZX_to_ZX zx)).
Proof.
  intros.
  rewrite G_ZX_to_H_ZX_consistent.
  apply H_ZX_to_ZX_consistent.
Qed.

Theorem ZX_to_ZX_G_consistent : forall nIn nOut (zx : ZX nIn nOut),
  exists (θ : R), ZX_semantics zx = (Cexp θ) .* (G_ZX_semantics (ZX_to_G_ZX zx)).
Proof.
  intros.
  simpl.
  unfold ZX_to_G_ZX.
  rewrite <- H_ZX_to_G_ZX_consistent.
  apply ZX_to_H_ZX_consistent.
Qed.

Lemma ZX_G_ZX_H_involutive : forall nIn nOut (zx : H_ZX nIn nOut), G_ZX_to_H_ZX (H_ZX_to_G_ZX zx) ∝H zx.
Proof.
  intros.
  prop_exist_non_zero 1%R.
  Msimpl.
  simpl.
  rewrite <- G_ZX_to_H_ZX_consistent.
  rewrite <- H_ZX_to_G_ZX_consistent.
  reflexivity.
Qed.

Lemma ZX_H_ZX_G_involutive : forall nIn nOut (zx : G_ZX nIn nOut), H_ZX_to_G_ZX (G_ZX_to_H_ZX zx) ∝G zx.
Proof.
  intros.
  prop_exist_non_zero 1%R.
  Msimpl.
  simpl.
  rewrite <- H_ZX_to_G_ZX_consistent.
  rewrite <- G_ZX_to_H_ZX_consistent.
  reflexivity.
Qed.

Lemma H_ZX_to_G_ZX_compat : forall nIn nOut (zx0 zx1 : H_ZX nIn nOut), 
  zx0 ∝H zx1 -> (H_ZX_to_G_ZX zx0) ∝G (H_ZX_to_G_ZX zx1).
Proof.
  intros.
  destruct H.
  destruct H.
  unfold H_proportional.
  unfold proportional_general.
  exists x.
  repeat rewrite <- H_ZX_to_G_ZX_consistent.
  split; assumption.
Qed.

Lemma G_ZX_to_H_ZX_compat : forall nIn nOut (zx0 zx1 : G_ZX nIn nOut), 
  zx0 ∝G zx1 -> (G_ZX_to_H_ZX zx0) ∝H (G_ZX_to_H_ZX zx1).
Proof.
  intros.
  destruct H.
  destruct H.
  unfold H_proportional.
  unfold proportional_general.
  exists x.
  repeat rewrite <- G_ZX_to_H_ZX_consistent.
  split; assumption.
Qed.

Lemma ZX_to_G_ZX_compat : forall nIn nOut (zx0 zx1 : ZX nIn nOut), 
  zx0 ∝ zx1 -> (ZX_to_G_ZX zx0) ∝G (ZX_to_G_ZX zx1).
Proof.
  intros.
  apply H_ZX_to_G_ZX_compat.
  apply ZX_to_H_ZX_compat.
  assumption.
Qed.

Lemma G_ZX_to_ZX_compat : forall nIn nOut (zx0 zx1 : G_ZX nIn nOut), 
  zx0 ∝G zx1 -> (G_ZX_to_ZX zx0) ∝ (G_ZX_to_ZX zx1).
Proof.
  intros.
  apply H_ZX_to_ZX_compat.
  apply G_ZX_to_H_ZX_compat.
  assumption.
Qed.

Add Parametric Morphism (nIn nOut : nat) : (@ZX_to_G_ZX nIn nOut)
  with signature (@proportional nIn nOut) ==> (@G_proportional nIn nOut) as ZX_to_G_ZX_mor.
Proof. apply ZX_to_G_ZX_compat. Qed.

Add Parametric Morphism (nIn nOut : nat) : (@G_ZX_to_ZX nIn nOut)
  with signature (@G_proportional nIn nOut) ==> (@proportional nIn nOut) as G_ZX_to_ZX_mor.
Proof. apply G_ZX_to_ZX_compat. Qed. 

Add Parametric Morphism (nIn nOut : nat) : (@H_ZX_to_G_ZX nIn nOut)
  with signature (@H_proportional nIn nOut) ==> (@G_proportional nIn nOut) as H_ZX_to_G_ZX_mor.
Proof. apply H_ZX_to_G_ZX_compat. Qed.

Add Parametric Morphism (nIn nOut : nat) : (@G_ZX_to_H_ZX nIn nOut)
  with signature (@G_proportional nIn nOut) ==> (@H_proportional nIn nOut) as G_ZX_to_H_ZX_mor.
Proof. apply G_ZX_to_H_ZX_compat. Qed. 

Lemma G_ZX_ZX_involutive : forall nIn nOut (zx : ZX nIn nOut), G_ZX_to_ZX (ZX_to_G_ZX zx) ∝ zx.
Proof.
  intros.
  Msimpl.
  simpl.
  unfold ZX_to_G_ZX.
  unfold G_ZX_to_ZX.
  rewrite ZX_G_ZX_H_involutive.
  apply ZX_H_ZX_involutive.
Qed.

Lemma ZX_G_ZX_involutive : forall nIn nOut (zx : G_ZX nIn nOut), ZX_to_G_ZX (G_ZX_to_ZX zx) ∝G zx.
Proof.
  intros.
  Msimpl.
  simpl.
  unfold ZX_to_G_ZX.
  unfold G_ZX_to_ZX.
  rewrite H_ZX_ZX_involutive.
  apply ZX_H_ZX_G_involutive.
Qed.





