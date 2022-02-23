Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.VectorStates.
Require Export ZX.
Require Export ZX_G_2.
Require Export Gates.
Require Export GateRules.
Require Export Rules.
Require Export VyZX.Proportional.
Require Import Setoid.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

Local Open Scope R_scope.
Inductive A_G2_ZX : nat (* #inputs *) -> nat (* #outputs *) -> Type :=
  | A_G2_Empty                 : A_G2_ZX 0 0
  | A_G2_Z_Spider_1_0  (α : R) : forall n : nat, A_G2_ZX 1 0
  | A_G2_Z_Spider_0_1  (α : R) : forall n : nat, A_G2_ZX 0 1
  | A_G2_Z_Spider_1_1  (α : R) : forall n : nat, A_G2_ZX 1 1 (* Required to build wire construct *)
  | A_G2_Z_Spider_1_2  (α : R) : forall n : nat, A_G2_ZX 1 2
  | A_G2_Z_Spider_2_1  (α : R) : forall n : nat, A_G2_ZX 2 1
  | A_G2_Cap                   : forall n : nat, A_G2_ZX 0 2
  | A_G2_Cup                   : forall n : nat, A_G2_ZX 2 0
  | A_G2_Stack {nIn0 nIn1 nOut0 nOut1} 
               (zx0 : A_G2_ZX nIn0 nOut0) 
               (zx1 : A_G2_ZX nIn1 nOut1) : A_G2_ZX (nIn0 + nIn1) (nOut0 + nOut1)
  | A_G2_Compose {nIn nMid nOut} 
               (zx0 : A_G2_ZX nIn nMid) 
               (zx1 : A_G2_ZX nMid nOut) : A_G2_ZX nIn nOut.
Local Close Scope R_scope.

Notation "⦰AG2" := A_G2_Empty. (* \revemptyset *)
Notation "⊂AG2" := A_G2_Cap. (* \subset *)
Notation "⊃AG2" := A_G2_Cup. (* \supset *)

Fixpoint A_G2_ZX_semantics {nIn nOut} (zx : A_G2_ZX nIn nOut) : 
  Matrix (2 ^ nOut) (2 ^nIn) := 
  match zx with
  | ⦰AG2 => G2_ZX_semantics ⦰G2
  | A_G2_Z_Spider_1_0 α _ => G2_ZX_semantics (G2_Z_Spider_1_0 α)
  | A_G2_Z_Spider_0_1 α _ => G2_ZX_semantics (G2_Z_Spider_0_1 α)
  | A_G2_Z_Spider_1_1 α _ => G2_ZX_semantics (G2_Z_Spider_1_1 α)
  | A_G2_Z_Spider_1_2 α _ => G2_ZX_semantics (G2_Z_Spider_1_2 α)
  | A_G2_Z_Spider_2_1 α _ => G2_ZX_semantics (G2_Z_Spider_2_1 α)
  | A_G2_Cap _ => G2_ZX_semantics (G2_Cap)
  | A_G2_Cup _ => G2_ZX_semantics (G2_Cup)
  | A_G2_Stack zx0 zx1 => (A_G2_ZX_semantics zx0) ⊗ (A_G2_ZX_semantics zx1)
  | @A_G2_Compose _ nMid _ zx0 zx1 => (A_G2_ZX_semantics zx1) × (nMid ⨂ hadamard) × (A_G2_ZX_semantics zx0)
  end.

Fixpoint A_G2_ZX_to_G2_ZX {nIn nOut} (zx : A_G2_ZX nIn nOut) : G2_ZX nIn nOut :=
  match zx with
  | ⦰AG2 => ⦰G2
  | A_G2_Z_Spider_1_0 α _ => G2_Z_Spider_1_0 α
  | A_G2_Z_Spider_0_1 α _ => G2_Z_Spider_0_1 α
  | A_G2_Z_Spider_1_1 α _ => G2_Z_Spider_1_1 α
  | A_G2_Z_Spider_1_2 α _ => G2_Z_Spider_1_2 α
  | A_G2_Z_Spider_2_1 α _ => G2_Z_Spider_2_1 α
  | A_G2_Cap _ => G2_Cap
  | A_G2_Cup _ => G2_Cup
  | A_G2_Stack zx0 zx1 => (A_G2_ZX_to_G2_ZX zx0) ↕G2 (A_G2_ZX_to_G2_ZX zx1)
  | A_G2_Compose zx0 zx1 => (A_G2_ZX_to_G2_ZX zx0) ⟷G2 (A_G2_ZX_to_G2_ZX zx1)
  end.

Fixpoint G2_ZX_to_A_G2_ZX_helper (base : nat) {nIn nOut} (zx : G2_ZX nIn nOut) : (A_G2_ZX nIn nOut) * nat :=
  match zx with
  | ⦰G2 => (⦰AG2, S base)
  | G2_Z_Spider_1_0 α  => (A_G2_Z_Spider_1_0 α base , S base)
  | G2_Z_Spider_0_1 α  => (A_G2_Z_Spider_0_1 α base , S base)
  | G2_Z_Spider_1_1 α  => (A_G2_Z_Spider_1_1 α base , S base)
  | G2_Z_Spider_1_2 α  => (A_G2_Z_Spider_1_2 α base , S base)
  | G2_Z_Spider_2_1 α  => (A_G2_Z_Spider_2_1 α base , S base)
  | G2_Cap             => (A_G2_Cap base, S base)
  | G2_Cup             => (A_G2_Cup base, S base)
  | G2_Stack zx0 zx1   => (A_G2_Stack 
                            (fst (G2_ZX_to_A_G2_ZX_helper base zx0)) 
                            (fst (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper base zx0)) zx1)),
                            S (snd (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper base zx0)) zx1)))
  | G2_Compose zx0 zx1 => (A_G2_Compose
                            (fst (G2_ZX_to_A_G2_ZX_helper base zx0)) 
                            (fst (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper base zx0)) zx1)),
                            S (snd (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper base zx0)) zx1)))
  end.

Definition G2_ZX_to_A_G2_ZX {nIn nOut} (zx : G2_ZX nIn nOut) := fst (G2_ZX_to_A_G2_ZX_helper 0 zx).

(* Todo: 
   - State/Prove no collisions
   - Add maps from node id -> [node id] * [node id] (i.e. map to connected spider/cap/cup) 
*)

Inductive In_A_G2_ZX : forall {nIn nOut : nat}, nat -> A_G2_ZX nIn nOut -> Prop :=
  | In_Z_Spider_1_0 {α} n : In_A_G2_ZX n (A_G2_Z_Spider_1_0 α n)
  | In_Z_Spider_0_1 {α} n : In_A_G2_ZX n (A_G2_Z_Spider_0_1 α n)
  | In_Z_Spider_1_1 {α} n : In_A_G2_ZX n (A_G2_Z_Spider_1_1 α n)
  | In_Z_Spider_2_1 {α} n : In_A_G2_ZX n (A_G2_Z_Spider_2_1 α n)
  | In_Z_Spider_1_2 {α} n : In_A_G2_ZX n (A_G2_Z_Spider_1_2 α n)
  | In_Stack_L (nIn0 nIn1 nOut0 nOut1 : nat) 
               (zx0 : A_G2_ZX nIn0 nOut0) (zx1 : A_G2_ZX nIn1 nOut1) n : 
                In_A_G2_ZX n zx0 -> In_A_G2_ZX n (A_G2_Stack zx0 zx1)
  | In_Stack_R (nIn0 nIn1 nOut0 nOut1 : nat)
               (zx0 : A_G2_ZX nIn0 nOut0) (zx1 : A_G2_ZX nIn1 nOut1) n : 
                In_A_G2_ZX n zx1 -> In_A_G2_ZX n (A_G2_Stack zx0 zx1)
  | In_Compose_L {nIn nMid nOut}
               (zx0 : A_G2_ZX nIn nMid)
               (zx1 : A_G2_ZX nMid nOut) n : In_A_G2_ZX n zx0 -> In_A_G2_ZX n (A_G2_Compose zx0 zx1)
  | In_Compose_R {nIn nMid nOut}
               (zx0 : A_G2_ZX nIn nMid)
               (zx1 : A_G2_ZX nMid nOut) n : In_A_G2_ZX n zx1 -> In_A_G2_ZX n (A_G2_Compose zx0 zx1).

Inductive WF_A_G2_ZX : forall {nIn nOut : nat}, A_G2_ZX nIn nOut -> Prop :=
  | WF_Empty                 : WF_A_G2_ZX ⦰AG2
  | WF_A_G2_Z_Spider_1_0 n α : WF_A_G2_ZX (A_G2_Z_Spider_1_0 n α)
  | WF_A_G2_Z_Spider_0_1 n α : WF_A_G2_ZX (A_G2_Z_Spider_0_1 n α)
  | WF_A_G2_Z_Spider_1_1 n α : WF_A_G2_ZX (A_G2_Z_Spider_1_1 n α)
  | WF_A_G2_Z_Spider_2_1 n α : WF_A_G2_ZX (A_G2_Z_Spider_2_1 n α)
  | WF_A_G2_Z_Spider_1_2 n α : WF_A_G2_ZX (A_G2_Z_Spider_1_2 n α)
  | WF_A_G2_Cap n : WF_A_G2_ZX (A_G2_Cap n)
  | WF_A_G2_Cup n : WF_A_G2_ZX (A_G2_Cup n)
  | WF_A_G2_Stack : 
      forall (nIn0 nIn1 nOut0 nOut1 : nat) (zx0 : A_G2_ZX nIn0 nOut0) (zx1 : A_G2_ZX nIn1 nOut1),
        (forall n, In_A_G2_ZX n zx0 -> ~ In_A_G2_ZX n zx1) -> 
          WF_A_G2_ZX zx0 -> WF_A_G2_ZX zx1 ->
          WF_A_G2_ZX (A_G2_Stack zx0 zx1)
  | WF_A_G2_Compose {nIn nMid nOut}
      (zx0 : A_G2_ZX nIn nMid) (zx1 : A_G2_ZX nMid nOut) : 
        (forall n, In_A_G2_ZX n zx0 -> ~ In_A_G2_ZX n zx1) ->
          WF_A_G2_ZX zx0 -> WF_A_G2_ZX zx1 ->
          WF_A_G2_ZX (A_G2_Compose zx0 zx1).

Lemma G2_ZX_to_A_G2_ZX_helper_ret_gt_base : 
  forall base {nIn nOut} (zx : G2_ZX nIn nOut), 
    base < snd (G2_ZX_to_A_G2_ZX_helper base zx).
Proof.
  intros.
  generalize dependent base.
  induction zx; intros; simpl; try auto (* Non composite *).
  all: 
  apply (Nat.lt_trans _ (snd (G2_ZX_to_A_G2_ZX_helper base zx1)) _); [ apply IHzx1 | apply IHzx2].
Qed.

(* 
TODO:

  Prove that if we have In_A_G2_ZX n (A_G2_Stack zx0 zx1) then In_A_G2_ZX n zx0 \/ In_A_G2_ZX n zx1
    Same for compose

  Prove a relation between In_A_G2_ZX and G2_ZX_to_A_G2_ZX.
   Well, if In n (fst G2_ZX_to_A_G2_ZX zx) then n <= snd (G2_ZX_to_A_G2_ZX zx).

  From there we can prove that the output will be well founded.

  Prove that the helper function produces a WF_A_G2_ZX (for any base)
  
    Corrollary that the non helper function works (could just start here, but no real benefit).


*)

Lemma In_A_G2_ZX_Stack_Rev {nIn0 nOut0 nIn1 nOut1} : 
  forall n (zx0 : A_G2_ZX nIn0 nOut0) (zx1 : A_G2_ZX nIn1 nOut1), 
    In_A_G2_ZX n (A_G2_Stack zx0 zx1) -> In_A_G2_ZX n zx0 \/ In_A_G2_ZX n zx1.
Proof.
  intros.
  inversion H.
  - subst.
    inversion H10.
    apply inj_pair2_eq_dec in H6; [| apply eq_nat_dec].
    apply inj_pair2_eq_dec in H6; [| apply eq_nat_dec].
    left.
    subst; assumption.
  - subst.
    inversion H11.
    apply inj_pair2_eq_dec in H6; [| apply eq_nat_dec].
    apply inj_pair2_eq_dec in H6; [| apply eq_nat_dec].
    right.
    subst; assumption.
Qed.

Lemma In_A_G2_ZX_Compose_Rev {nIn nMid nOut} :
  forall n (zx0 : A_G2_ZX nIn nMid) (zx1 : A_G2_ZX nMid nOut),
    In_A_G2_ZX n (A_G2_Compose zx0 zx1) -> In_A_G2_ZX n zx0 \/ In_A_G2_ZX n zx1.
Proof.
  intros.
  inversion H.
  - subst.
    inversion H5.
    apply inj_pair2_eq_dec in H1; [| apply eq_nat_dec].
    apply inj_pair2_eq_dec in H1; [| apply eq_nat_dec].
    left; subst; assumption.
  - subst.
    inversion H6.
    apply inj_pair2_eq_dec in H1; [| apply eq_nat_dec].
    apply inj_pair2_eq_dec in H1; [| apply eq_nat_dec].
    right; subst; assumption.
Qed.

Lemma G2_ZX_to_A_G2_ZX_labels_small {nIn nOut} : 
  forall (n base : nat) (zx : G2_ZX nIn nOut) , 
    In_A_G2_ZX n (fst (G2_ZX_to_A_G2_ZX_helper base zx)) -> n < snd (G2_ZX_to_A_G2_ZX_helper base zx).
Proof.
  intros.
  generalize dependent base.
  generalize dependent n.
  induction zx; intros.
  1 - 8: inversion H.
  1 - 5: simpl; auto.
  (* Stack / Compose cases *)
  all: simpl in H.
  1: apply In_A_G2_ZX_Stack_Rev in H.
  2: apply In_A_G2_ZX_Compose_Rev in H.
  all: destruct H; simpl.
  1,3: rewrite IHzx1; [ apply Nat.lt_lt_succ_r; apply G2_ZX_to_A_G2_ZX_helper_ret_gt_base | apply H ].
  all: rewrite IHzx2; [ constructor | apply H ].
Qed.

Lemma Not_In_A_G2_ZX_lt_base : forall {nIn nOut} n base (zx : G2_ZX nIn nOut), n < base -> ~ In_A_G2_ZX n (fst (G2_ZX_to_A_G2_ZX_helper base zx)).
Proof.
  intros.
  generalize dependent n.
  generalize dependent base.
  induction zx; intros.
  all: simpl; unfold not; intros Hcontra.
  1-8: inversion Hcontra.
  1-5: apply Nat.lt_neq in H; subst; congruence.
  all: simpl.
  1: apply In_A_G2_ZX_Stack_Rev in Hcontra.
  2: apply In_A_G2_ZX_Compose_Rev in Hcontra.
  all: destruct Hcontra; contradict H0.
  1,3: apply IHzx1; assumption.
  all: apply IHzx2. 
  all: eapply Nat.lt_trans; [ | apply G2_ZX_to_A_G2_ZX_helper_ret_gt_base ].
  all: congruence.
Qed.
 
Lemma WF_G2_ZX_to_A_G2_ZX_helper : forall {nIn nOut} base (zx : G2_ZX nIn nOut), WF_A_G2_ZX (fst (G2_ZX_to_A_G2_ZX_helper base zx)).
Proof.
  intros.
  generalize dependent base.
  induction zx; intros; simpl; constructor.
  2,5: apply IHzx1.
  2,4: apply IHzx2.
  all: intros.
  all: apply Not_In_A_G2_ZX_lt_base.
  all: apply G2_ZX_to_A_G2_ZX_labels_small. 
  all: assumption.
Qed.

Corollary WF_G2_ZX_to_A_G2_ZX : forall {nIn nOut} (zx : G2_ZX nIn nOut), WF_A_G2_ZX (G2_ZX_to_A_G2_ZX zx).
Proof. intros. unfold G2_ZX_to_A_G2_ZX. apply WF_G2_ZX_to_A_G2_ZX_helper. Qed.
