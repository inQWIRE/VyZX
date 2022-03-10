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
Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapAVL.

Local Open Scope R_scope.
Inductive A_G2_ZX : nat (* #inputs *) -> nat (* #outputs *) -> Type :=
  | A_G2_Empty                 : forall n : nat, A_G2_ZX 0 0
  | A_G2_Z_Spider_1_0  (α : R) : forall n : nat, A_G2_ZX 1 0
  | A_G2_Z_Spider_0_1  (α : R) : forall n : nat, A_G2_ZX 0 1
  | A_G2_Z_Spider_1_1  (α : R) : forall n : nat, A_G2_ZX 1 1 (* Required to build wire construct *)
  | A_G2_Z_Spider_1_2  (α : R) : forall n : nat, A_G2_ZX 1 2
  | A_G2_Z_Spider_2_1  (α : R) : forall n : nat, A_G2_ZX 2 1
  | A_G2_Cap                   : forall n : nat, A_G2_ZX 0 2
  | A_G2_Cup                   : forall n : nat, A_G2_ZX 2 0
  | A_G2_Swap                  : forall n : nat, A_G2_ZX 2 2
  | A_G2_Stack {nIn0 nIn1 nOut0 nOut1} 
               (zx0 : A_G2_ZX nIn0 nOut0) 
               (zx1 : A_G2_ZX nIn1 nOut1) : 
                                 forall n : nat, A_G2_ZX (nIn0 + nIn1) (nOut0 + nOut1)
  | A_G2_Compose {nIn nMid nOut} 
               (zx0 : A_G2_ZX nIn nMid) 
               (zx1 : A_G2_ZX nMid nOut) : 
                                 forall n : nat, A_G2_ZX nIn nOut.
Local Close Scope R_scope.

Notation "⦰AG2" := A_G2_Empty. (* \revemptyset *)
Notation "⊂AG2" := A_G2_Cap. (* \subset *)
Notation "⊃AG2" := A_G2_Cup. (* \supset *)
Notation "⨉AG2" := A_G2_Swap. (* \bigtimes *)

Fixpoint A_G2_ZX_semantics {nIn nOut} (zx : A_G2_ZX nIn nOut) : 
  Matrix (2 ^ nOut) (2 ^nIn) := 
  match zx with
  | ⦰AG2 _ => G2_ZX_semantics ⦰G2
  | A_G2_Z_Spider_1_0 α _ => G2_ZX_semantics (G2_Z_Spider_1_0 α)
  | A_G2_Z_Spider_0_1 α _ => G2_ZX_semantics (G2_Z_Spider_0_1 α)
  | A_G2_Z_Spider_1_1 α _ => G2_ZX_semantics (G2_Z_Spider_1_1 α)
  | A_G2_Z_Spider_1_2 α _ => G2_ZX_semantics (G2_Z_Spider_1_2 α)
  | A_G2_Z_Spider_2_1 α _ => G2_ZX_semantics (G2_Z_Spider_2_1 α)
  | A_G2_Cap _ => G2_ZX_semantics (G2_Cap)
  | A_G2_Cup _ => G2_ZX_semantics (G2_Cup)
  | A_G2_Swap _ => G2_ZX_semantics (G2_Swap)
  | A_G2_Stack zx0 zx1 _ => (A_G2_ZX_semantics zx0) ⊗ (A_G2_ZX_semantics zx1)
  | @A_G2_Compose _ nMid _ zx0 zx1 _ => (A_G2_ZX_semantics zx1) × (nMid ⨂ hadamard) × (A_G2_ZX_semantics zx0)
  end.

Fixpoint A_G2_ZX_to_G2_ZX {nIn nOut} (zx : A_G2_ZX nIn nOut) : G2_ZX nIn nOut :=
  match zx with
  | ⦰AG2 _ => ⦰G2
  | A_G2_Z_Spider_1_0 α _ => G2_Z_Spider_1_0 α
  | A_G2_Z_Spider_0_1 α _ => G2_Z_Spider_0_1 α
  | A_G2_Z_Spider_1_1 α _ => G2_Z_Spider_1_1 α
  | A_G2_Z_Spider_1_2 α _ => G2_Z_Spider_1_2 α
  | A_G2_Z_Spider_2_1 α _ => G2_Z_Spider_2_1 α
  | A_G2_Cap _ => G2_Cap
  | A_G2_Cup _ => G2_Cup
  | A_G2_Swap _ => G2_Swap
  | A_G2_Stack zx0 zx1 _ => (A_G2_ZX_to_G2_ZX zx0) ↕G2 (A_G2_ZX_to_G2_ZX zx1)
  | A_G2_Compose zx0 zx1 _ => (A_G2_ZX_to_G2_ZX zx0) ⟷G2 (A_G2_ZX_to_G2_ZX zx1)
  end.

Fixpoint G2_ZX_to_A_G2_ZX_helper (base : nat) {nIn nOut} (zx : G2_ZX nIn nOut) : (A_G2_ZX nIn nOut) * nat :=
  match zx with
  | ⦰G2 => (⦰AG2 base, S base)
  | G2_Z_Spider_1_0 α  => (A_G2_Z_Spider_1_0 α base , S base)
  | G2_Z_Spider_0_1 α  => (A_G2_Z_Spider_0_1 α base , S base)
  | G2_Z_Spider_1_1 α  => (A_G2_Z_Spider_1_1 α base , S base)
  | G2_Z_Spider_1_2 α  => (A_G2_Z_Spider_1_2 α base , S base)
  | G2_Z_Spider_2_1 α  => (A_G2_Z_Spider_2_1 α base , S base)
  | G2_Cap             => (A_G2_Cap base, S base)
  | G2_Cup             => (A_G2_Cup base, S base)
  | G2_Swap            => (A_G2_Swap base, S base)
  | G2_Stack zx0 zx1   => (A_G2_Stack 
                            (fst (G2_ZX_to_A_G2_ZX_helper base zx0)) 
                            (fst (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper base zx0)) zx1)) 
                            (snd (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper base zx0)) zx1)),
                            S (snd (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper base zx0)) zx1)))
  | G2_Compose zx0 zx1 => (A_G2_Compose
                            (fst (G2_ZX_to_A_G2_ZX_helper base zx0)) 
                            (fst (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper base zx0)) zx1))
                            (snd (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper base zx0)) zx1)),
                            S (snd (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper base zx0)) zx1)))
  end.

Definition G2_ZX_to_A_G2_ZX {nIn nOut} (zx : G2_ZX nIn nOut) := fst (G2_ZX_to_A_G2_ZX_helper (nIn + nOut (* Reserve for inputs / outputs *)) zx).

(* Todo: 
   - State/Prove no collisions
   - Add maps from node id -> [node id] * [node id] (i.e. map to connected spider/cap/cup) 
*)

Inductive In_A_G2_ZX : forall {nIn nOut : nat}, nat -> A_G2_ZX nIn nOut -> Prop :=
  | In_Empty n : In_A_G2_ZX n (⦰AG2 n)
  | In_Z_Spider_1_0 {α} n : In_A_G2_ZX n (A_G2_Z_Spider_1_0 α n)
  | In_Z_Spider_0_1 {α} n : In_A_G2_ZX n (A_G2_Z_Spider_0_1 α n)
  | In_Z_Spider_1_1 {α} n : In_A_G2_ZX n (A_G2_Z_Spider_1_1 α n)
  | In_Z_Spider_2_1 {α} n : In_A_G2_ZX n (A_G2_Z_Spider_2_1 α n)
  | In_Z_Spider_1_2 {α} n : In_A_G2_ZX n (A_G2_Z_Spider_1_2 α n)
  | In_Cap n : In_A_G2_ZX n (A_G2_Cap n)
  | In_Cup n : In_A_G2_ZX n (A_G2_Cup n)
  | In_Swap n : In_A_G2_ZX n (A_G2_Swap n)
  | In_Stack_L {nIn0 nIn1 nOut0 nOut1 idnum : nat}
               (zx0 : A_G2_ZX nIn0 nOut0) (zx1 : A_G2_ZX nIn1 nOut1) n : 
                In_A_G2_ZX n zx0 -> In_A_G2_ZX n (A_G2_Stack zx0 zx1 idnum)
  | In_Stack_R {nIn0 nIn1 nOut0 nOut1 idnum : nat}
               (zx0 : A_G2_ZX nIn0 nOut0) (zx1 : A_G2_ZX nIn1 nOut1) n : 
                In_A_G2_ZX n zx1 -> In_A_G2_ZX n (A_G2_Stack zx0 zx1 idnum)
  | In_Stack {nIn0 nIn1 nOut0 nOut1 : nat} 
               (zx0 : A_G2_ZX nIn0 nOut0) (zx1 : A_G2_ZX nIn1 nOut1) n : In_A_G2_ZX n (A_G2_Stack zx0 zx1 n)
  | In_Compose_L {nIn nMid nOut idnum : nat}
               (zx0 : A_G2_ZX nIn nMid)
               (zx1 : A_G2_ZX nMid nOut) n : In_A_G2_ZX n zx0 -> In_A_G2_ZX n (A_G2_Compose zx0 zx1 idnum)
  | In_Compose_R {nIn nMid nOut idnum : nat}
               (zx0 : A_G2_ZX nIn nMid)
               (zx1 : A_G2_ZX nMid nOut) n : In_A_G2_ZX n zx1 -> In_A_G2_ZX n (A_G2_Compose zx0 zx1 idnum)
  | In_Compose {nIn nMid nOut} 
               (zx0 : A_G2_ZX nIn nMid)
               (zx1 : A_G2_ZX nMid nOut) n : In_A_G2_ZX n (A_G2_Compose zx0 zx1 n).

Inductive WF_A_G2_ZX : forall {nIn nOut : nat}, A_G2_ZX nIn nOut -> Prop :=
  | WF_Empty n               : WF_A_G2_ZX (⦰AG2 n)
  | WF_A_G2_Z_Spider_1_0 n α : WF_A_G2_ZX (A_G2_Z_Spider_1_0 n α)
  | WF_A_G2_Z_Spider_0_1 n α : WF_A_G2_ZX (A_G2_Z_Spider_0_1 n α)
  | WF_A_G2_Z_Spider_1_1 n α : WF_A_G2_ZX (A_G2_Z_Spider_1_1 n α)
  | WF_A_G2_Z_Spider_2_1 n α : WF_A_G2_ZX (A_G2_Z_Spider_2_1 n α)
  | WF_A_G2_Z_Spider_1_2 n α : WF_A_G2_ZX (A_G2_Z_Spider_1_2 n α)
  | WF_A_G2_Cap n : WF_A_G2_ZX (A_G2_Cap n)
  | WF_A_G2_Cup n : WF_A_G2_ZX (A_G2_Cup n)
  | WF_A_G2_Swap n : WF_A_G2_ZX (A_G2_Swap n)
  | WF_A_G2_Stack : 
      forall (nIn0 nIn1 nOut0 nOut1 idnum : nat) (zx0 : A_G2_ZX nIn0 nOut0) (zx1 : A_G2_ZX nIn1 nOut1),
        (forall n, In_A_G2_ZX n zx0 -> ~ In_A_G2_ZX n zx1) -> 
        (~ In_A_G2_ZX idnum zx0) -> (~ In_A_G2_ZX idnum zx1) ->
          WF_A_G2_ZX zx0 -> WF_A_G2_ZX zx1 ->
          WF_A_G2_ZX (A_G2_Stack zx0 zx1 idnum)
  | WF_A_G2_Compose {nIn nMid nOut idnum}
      (zx0 : A_G2_ZX nIn nMid) (zx1 : A_G2_ZX nMid nOut) : 
        (forall n, In_A_G2_ZX n zx0 -> ~ In_A_G2_ZX n zx1) ->
        (~ In_A_G2_ZX idnum zx0) -> (~ In_A_G2_ZX idnum zx1) ->
          WF_A_G2_ZX zx0 -> WF_A_G2_ZX zx1 ->
          WF_A_G2_ZX (A_G2_Compose zx0 zx1 idnum).

Lemma G2_ZX_to_A_G2_ZX_helper_ret_gt_base : 
  forall base {nIn nOut} (zx : G2_ZX nIn nOut), 
    base < snd (G2_ZX_to_A_G2_ZX_helper base zx).
Proof.
  intros.
  generalize dependent base.
  induction zx; intros; simpl; try auto (* Non composite *).
  all: 
  apply (Nat.lt_trans _ (snd (G2_ZX_to_A_G2_ZX_helper base zx1)) _); [ apply IHzx1 | apply Nat.lt_lt_succ_r; apply IHzx2].
Qed.

Lemma In_A_G2_ZX_Stack_Rev {nIn0 nOut0 nIn1 nOut1 idnum} : 
  forall n (zx0 : A_G2_ZX nIn0 nOut0) (zx1 : A_G2_ZX nIn1 nOut1), 
    In_A_G2_ZX n (A_G2_Stack zx0 zx1 idnum) -> In_A_G2_ZX n zx0 \/ In_A_G2_ZX n zx1 \/ idnum = n.
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
    right; left.
    subst; assumption.
  - right; right; reflexivity.
Qed.

Lemma In_A_G2_ZX_Compose_Rev {nIn nMid nOut idnum} :
  forall n (zx0 : A_G2_ZX nIn nMid) (zx1 : A_G2_ZX nMid nOut),
    In_A_G2_ZX n (A_G2_Compose zx0 zx1 idnum) -> In_A_G2_ZX n zx0 \/ In_A_G2_ZX n zx1 \/ n = idnum.
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
    right; left; subst; assumption.
  - right; right; easy.
Qed.

Lemma G2_ZX_to_A_G2_ZX_labels_small {nIn nOut} : 
  forall (n base : nat) (zx : G2_ZX nIn nOut) , 
    In_A_G2_ZX n (fst (G2_ZX_to_A_G2_ZX_helper base zx)) -> n < snd (G2_ZX_to_A_G2_ZX_helper base zx).
Proof.
  intros.
  generalize dependent base.
  generalize dependent n.
  induction zx; intros.
  1 - 9: inversion H.
  1 - 9: simpl; auto.
  (* Stack / Compose cases *)
  all: simpl in H.
  1: apply In_A_G2_ZX_Stack_Rev in H.
  2: apply In_A_G2_ZX_Compose_Rev in H.
  all: destruct H; simpl.
  1,3: rewrite IHzx1; [ apply Nat.lt_lt_succ_r; apply G2_ZX_to_A_G2_ZX_helper_ret_gt_base | apply H ].
  all: destruct H; [ rewrite IHzx2; [ constructor | apply H ] | rewrite H; constructor ].
Qed.

Lemma Not_In_A_G2_ZX_lt_base : forall {nIn nOut} n base (zx : G2_ZX nIn nOut), n < base -> ~ In_A_G2_ZX n (fst (G2_ZX_to_A_G2_ZX_helper base zx)).
Proof.
  intros.
  generalize dependent n.
  generalize dependent base.
  induction zx; intros.
  all: simpl; unfold not; intros Hcontra.
  1-9: inversion Hcontra.
  1-9: apply Nat.lt_neq in H; subst; congruence.
  all: simpl.
  1: apply In_A_G2_ZX_Stack_Rev in Hcontra.
  2: apply In_A_G2_ZX_Compose_Rev in Hcontra.
  all: destruct Hcontra; contradict H0.
  1,3: apply IHzx1; assumption.
  all: apply Classical_Prop.and_not_or; split.
  1,3: apply IHzx2.
  1,2: apply (Nat.lt_trans _ base); [ assumption | ].
  1,2: apply G2_ZX_to_A_G2_ZX_helper_ret_gt_base.
  1: apply not_eq_sym.
  all: apply Nat.lt_neq.
  all: apply (Nat.lt_trans _ base); [ assumption | ].
  all: apply (Nat.lt_trans _ (snd (G2_ZX_to_A_G2_ZX_helper base zx1))); apply G2_ZX_to_A_G2_ZX_helper_ret_gt_base.
Qed.
 
Lemma WF_G2_ZX_to_A_G2_ZX_helper : forall {nIn nOut} base (zx : G2_ZX nIn nOut), WF_A_G2_ZX (fst (G2_ZX_to_A_G2_ZX_helper base zx)).
Proof.
  intros.
  generalize dependent base.
  induction zx; intros.
  all: simpl; constructor.
  4,9: apply IHzx1.
  4,8: apply IHzx2.
  1,4: intros;
       apply Not_In_A_G2_ZX_lt_base;
       apply G2_ZX_to_A_G2_ZX_labels_small;
       assumption.
  all: unfold not; intros.
  all: apply G2_ZX_to_A_G2_ZX_labels_small in H.
  all: contradict H.
  all: apply le_not_lt.
  2,4: constructor.
  all: apply Nat.lt_le_incl.
  all: apply G2_ZX_to_A_G2_ZX_helper_ret_gt_base.
Qed.

Corollary WF_G2_ZX_to_A_G2_ZX : forall {nIn nOut} (zx : G2_ZX nIn nOut), WF_A_G2_ZX (G2_ZX_to_A_G2_ZX zx).
Proof. intros. unfold G2_ZX_to_A_G2_ZX. apply WF_G2_ZX_to_A_G2_ZX_helper. Qed.



(* TODO 2:
  
  Create a map which annotates the edges 
    (Map node# -> (Vector nIn node# * Vector nOut node#) or a similar idea where inputs and outputs are differentiated)
      What facts can we prove about this?
        - 


  Create a function which generates the map automatically.
    Function should be bottom-up generation
      What facts can we prove about this?
        - 

  A function which matches inputs and outputs.
    What facts can we prove about this?
      -

  Graph semantics (or graph back to ZX diagram, same difficulty)

 *)

Module OrderedNat <: OrderedType with Definition t := nat%type.
  Definition t := nat%type.
  Definition eq := @eq nat.
  Definition lt (a b : nat) := a < b.
  Theorem eq_refl : forall x, eq x x.
    reflexivity.
  Qed.

  Theorem eq_sym : forall a b, eq a b -> eq b a.
    intros; symmetry; auto.
  Qed.

  Theorem eq_trans : forall a b c, eq a b -> eq b c -> eq a c.
    intros; etransitivity; eauto.
  Qed.

  Theorem lt_trans : forall a b c, lt a b -> lt b c -> lt a c.
    intros. 
    unfold lt in *.
    etransitivity; [ apply H | apply H0 ].
  Qed.

  Theorem lt_not_eq : forall a b, lt a b -> ~(eq a b).
    unfold eq, lt.
    intros.
    lia.
  Qed.

  Lemma eq_dec (x y : nat) : {x = y} + {x <> y}.
  Proof.
    apply eq_nat_dec.
  Defined.

  Lemma le_not_eq_lt : forall n n1,  n <= n1 -> n <> n1 -> n < n1.
  Proof.
    intros.
    apply le_lt_or_eq in H.
    destruct H.
    - assumption.
    - contradiction.
  Qed. 

  Lemma lt_eq_gt_dec (x y : nat) : {lt x y} + {eq x y} + {lt y x}.
  Proof.
    bdestruct (x <? y).
    - left; left. assumption.
    - bdestruct (x =? y).
      + left; right. assumption.
      + right. apply not_eq_sym in H0. apply le_not_eq_lt; assumption.
  Qed.

Definition compare (x y : t) : OrderedType.Compare lt eq x y.
Proof.
  assert ({lt x y} + {eq x y} + {lt y x}) by apply lt_eq_gt_dec.
  destruct H; 
  [ destruct s | ];
  [ apply LT | apply EQ | apply GT ];
  assumption.
Defined.

End OrderedNat.

Module OrderedNatPair <: OrderedType with Definition t := (nat * nat)%type.

  Definition t := (nat * nat)%type.
  Definition eq := @eq (nat * nat).
  Definition lt (a b : (nat * nat)) := 
    match a, b with
    | (a1, a2), (b1, b2) => (a1 < b1) \/ (a1 = b1 /\ a2 < b2)
    end.

  Theorem eq_refl : forall x, eq x x.
    reflexivity.
  Qed.

  Theorem eq_sym : forall a b, eq a b -> eq b a.
    intros; symmetry; auto.
  Qed.

  Theorem eq_trans : forall a b c, eq a b -> eq b c -> eq a c.
    intros; etransitivity; eauto.
  Qed.

  Theorem lt_trans : forall a b c, lt a b -> lt b c -> lt a c.
    intros. 
    destruct a, b, c.
    unfold lt in *.
    destruct H, H0.
    - left.
      etransitivity; [ apply H | apply H0 ].
    - destruct H0.
      subst.
      left.
      assumption.
    - destruct H.
      subst.
      left.
      assumption.
    - destruct H, H0.
      subst.
      right.
      split; [ easy | ].
      etransitivity; [ apply H1 | apply H2 ].
  Qed.

  Theorem lt_not_eq : forall a b, lt a b -> ~(eq a b).
    unfold eq, lt. destruct a, b.
    intros; destruct H.
    - unfold not.
      intros.
      apply pair_equal_spec in H0.
      destruct H0.
      subst.
      lia.
    - destruct H.
      unfold not.
      intros.
      apply pair_equal_spec in H1.
      destruct H1.
      subst.
      lia.
  Qed.

  Lemma eq_dec (x y : (nat * nat)) : {x = y} + {x <> y}.
  Proof.
    destruct x, y.
    decide equality; subst; apply eq_nat_dec.
  Defined.

  Lemma le_not_eq_lt : forall n n1,  n <= n1 -> n <> n1 -> n < n1.
  Proof.
    intros.
    apply le_lt_or_eq in H.
    destruct H.
    - assumption.
    - contradiction.
  Qed. 

  Lemma lt_eq_gt_dec (x y : (nat * nat)) : {lt x y} + {eq x y} + {lt y x}.
  Proof.
    destruct x, y.
    unfold eq.
    unfold lt.
    bdestruct (n <? n1).
    + left.
      left.
      left.
      assumption.
    + bdestruct (n =? n1); bdestruct (n0 =? n2).
      * left.
        right.
        subst.
        easy.
      * bdestruct (n0 <? n2).
        -- left.
           left.
           right.
           split; assumption.
        -- right.
           right.
           split.
           symmetry; assumption.
           apply le_not_eq_lt.
           assumption.
           apply not_eq_sym.
           assumption.
      * right.
        left.
        apply le_not_eq_lt.
        assumption.
        apply not_eq_sym.
        assumption.
      * right.
        left.
        apply le_not_eq_lt.
        assumption.
        apply not_eq_sym.
        assumption.
  Qed.

  Definition compare (x y : t) : OrderedType.Compare lt eq x y.
  Proof.
    assert ({lt x y} + {eq x y} + {lt y x}) by apply lt_eq_gt_dec.
    destruct H; 
    [ destruct s | ];
    [ apply LT | apply EQ | apply GT ];
    assumption.
  Defined.

End OrderedNatPair.

Module NatMaps := Make OrderedNat.

Definition NatListNatMaps := NatMaps.t (list nat).
Definition EmptyNatListNatMaps := NatMaps.empty (list nat).

Definition get_id {nIn nOut} (zx : A_G2_ZX nIn nOut) : nat :=
  match zx with
  | ⦰AG2 id                => id
  | A_G2_Z_Spider_1_0 α id => id
  | A_G2_Z_Spider_0_1 α id => id
  | A_G2_Z_Spider_1_1 α id => id
  | A_G2_Z_Spider_1_2 α id => id
  | A_G2_Z_Spider_2_1 α id => id
  | A_G2_Cap id            => id
  | A_G2_Cup id            => id
  | A_G2_Swap id           => id
  | A_G2_Stack zx0 zx1 id  => id
  | A_G2_Compose zx0 zx1 id => id
  end.

Lemma Equal_in : forall {nIn nOut} (zx : A_G2_ZX nIn nOut) n,
  n = get_id zx -> In_A_G2_ZX n zx.
Proof.
  intros.
  destruct zx; simpl in H; subst.
  1-9: constructor.
  apply In_Stack.
  apply In_Compose.
Qed.


Lemma Not_In_Not_Equal : forall {nIn nOut} (zx : A_G2_ZX nIn nOut) n,
  ~In_A_G2_ZX n zx -> n <> get_id zx.
Proof.
  intros.
  unfold not in *.
  intros.
  apply H.
  apply Equal_in.
  assumption.
Qed.


Fixpoint A_G2_Edge_Annotator_Helper (baseInMap baseOutMap : NatListNatMaps) {nIn nOut} (zx : A_G2_ZX nIn nOut) : (NatListNatMaps * NatListNatMaps) :=
  match zx with
  | ⦰AG2 id                => (NatMaps.add id [] baseInMap,  NatMaps.add id [] baseOutMap)
  | A_G2_Z_Spider_1_0 α id => (NatMaps.add id [id] baseInMap,  NatMaps.add id [] baseOutMap)
  | A_G2_Z_Spider_0_1 α id => (NatMaps.add id [] baseInMap,  NatMaps.add id [id] baseOutMap)
  | A_G2_Z_Spider_1_1 α id => (NatMaps.add id [id] baseInMap,  NatMaps.add id [id] baseOutMap)
  | A_G2_Z_Spider_1_2 α id => (NatMaps.add id [id] baseInMap,  NatMaps.add id [id; id] baseOutMap)
  | A_G2_Z_Spider_2_1 α id => (NatMaps.add id [id; id] baseInMap,  NatMaps.add id [id] baseOutMap)
  | A_G2_Cap id            => (NatMaps.add id [] baseInMap,  NatMaps.add id [id] baseOutMap)
  | A_G2_Cup id            => (NatMaps.add id [] baseInMap,  NatMaps.add id [id; id] baseOutMap)
  | A_G2_Swap id           => (NatMaps.add id [id; id] baseInMap,  NatMaps.add id [id; id] baseOutMap)
  | A_G2_Stack zx0 zx1 id  => let lId := get_id zx0 in
                              let rId := get_id zx1 in
                              match A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx0 with 
                              | (lIn, lOut) => match A_G2_Edge_Annotator_Helper lIn lOut zx1 with
                                              | (rIn, rOut) =>  match (NatMaps.find lId lIn, NatMaps.find lId lOut, NatMaps.find rId rIn, NatMaps.find rId rOut) with
                                                                | (Some lIdIn, Some lIdOut, Some rIdIn, Some rIdOut) => (NatMaps.add id (lIdIn ++ rIdIn) rIn, NatMaps.add id (lIdOut ++ rIdOut) rOut)
                                                                | _ =>  (NatMaps.add id [] rIn, NatMaps.add id [] rOut)
                                                                end
                                              end
                              end
  
  | A_G2_Compose zx0 zx1 id =>let lId := get_id zx0 in
                              let rId := get_id zx1 in
                              match A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx0 with 
                              | (lIn, lOut) => match A_G2_Edge_Annotator_Helper lIn lOut zx1 with
                                              | (rIn, rOut) =>  match (NatMaps.find lId lIn, NatMaps.find lId lOut, NatMaps.find rId rIn, NatMaps.find rId rOut) with
                                                                | (Some lIdIn, Some lIdOut, Some rIdIn, Some rIdOut) => (NatMaps.add id (lIdIn) rIn, NatMaps.add id (lIdOut) rOut)
                                                                | _ =>  (NatMaps.add id [] rIn, NatMaps.add id [] rOut)
                                                                end
                                              end
                              end
  end.

Definition A_G2_Edge_Annotator {nIn nOut} (zx : A_G2_ZX nIn nOut) : (NatListNatMaps * NatListNatMaps) := (A_G2_Edge_Annotator_Helper EmptyNatListNatMaps EmptyNatListNatMaps zx).

Lemma all_lookup_id : forall {nIn nOut} (zx : A_G2_ZX nIn nOut) baseInMap baseOutMap x,
                              x = get_id zx ->
                              (exists valIn, NatMaps.find x (fst (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)) = Some valIn) /\
                              (exists valOut, NatMaps.find x (snd (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)) = Some valOut).
Proof.
  intros.
  generalize dependent baseInMap.
  generalize dependent baseOutMap.
  subst x.
  induction zx; intros.
  1-9: split; eexists;
    simpl;
    unfold NatMaps.find;
    unfold NatMaps.this;
    unfold NatMaps.add;
    rewrite NatMaps.Raw.Proofs.add_find; try apply NatMaps.is_bst;
    destruct (OrderedNat.compare n n);
    try reflexivity;
      subst;
      inversion l;
      try (
        apply Nat.neq_succ_diag_l in H;
        contradiction
      );
      try (
        apply le_Sn_le in H;
        apply Nat.nle_succ_diag_l in H;
        contradiction
      ).
  all: split;
    simpl;
    destruct (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx1) eqn:Hzx1;
    destruct (A_G2_Edge_Annotator_Helper n0 n1 zx2) eqn:Hzx2;
    assert (n0 = (fst (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx1))) by (rewrite Hzx1; easy);
    assert (n1 = (snd (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx1))) by (rewrite Hzx1; easy);
    assert (n2 = (fst (A_G2_Edge_Annotator_Helper n0 n1 zx2))) by (rewrite Hzx2; easy);
    assert (n3 = (snd (A_G2_Edge_Annotator_Helper n0 n1 zx2))) by (rewrite Hzx2; easy);
    destruct (NatMaps.find (elt:=list nat) (get_id zx1) n2),
              (NatMaps.find (elt:=list nat) (get_id zx1) n3),
              (NatMaps.find (elt:=list nat) (get_id zx2) n2),
              (NatMaps.find (elt:=list nat) (get_id zx2) n3);
    subst n2 n3;
    simpl;
    unfold NatMaps.find;
    unfold NatMaps.this;
    unfold NatMaps.add;
    try rewrite NatMaps.Raw.Proofs.add_find; try apply NatMaps.is_bst;
    destruct (OrderedNat.compare n n);
      try inversion l3;
      try inversion l2;
      try inversion l1;
      try inversion l0;
      try inversion l;
      try (
        apply Nat.neq_succ_diag_l in H1;
        contradiction
      );
      try (
        apply le_Sn_le in H1;
        apply Nat.nle_succ_diag_l in H1;
        contradiction
      );
    try (eexists; reflexivity).
Qed.

Corollary all_lookup_id_fst : forall {nIn nOut} (zx : A_G2_ZX nIn nOut) baseInMap baseOutMap x,
                              x = get_id zx ->
                              (exists valIn, NatMaps.find x (fst (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)) = Some valIn).
Proof.
  intros.
  assert (
  (exists valIn, NatMaps.find x (fst (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)) = Some valIn) /\
  (exists valOut, NatMaps.find x (snd (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)) = Some valOut) ).
  {
    intros.
    apply all_lookup_id.
    assumption.
  }
  destruct H0.
  assumption.
Qed.

Corollary all_lookup_id_snd : forall {nIn nOut} (zx : A_G2_ZX nIn nOut) baseInMap baseOutMap x,
                              x = get_id zx ->
                              (exists valOut, NatMaps.find x (snd (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)) = Some valOut).
Proof.
  intros.
  assert (
  (exists valIn, NatMaps.find x (fst (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)) = Some valIn) /\
  (exists valOut, NatMaps.find x (snd (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)) = Some valOut)).
  {
    intros.
    apply all_lookup_id.
    assumption.
  }
  destruct H0.
  assumption.
Qed.
  


Lemma all_base_lookups_same : forall {nIn nOut} (zx : A_G2_ZX nIn nOut) baseInMap baseOutMap, WF_A_G2_ZX zx -> 
                                    forall x valIn valOut, 
                                        NatMaps.find x baseInMap = valIn -> 
                                        NatMaps.find x baseOutMap = valOut -> 
                                        x <> (get_id zx) -> 
                                          NatMaps.find x (fst (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)) = valIn /\
                                          NatMaps.find x (snd (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)) = valOut.
Proof.
  intros.
  generalize dependent x.
  generalize dependent valIn.
  generalize dependent valOut.
  generalize dependent baseInMap.
  generalize dependent baseOutMap.
  induction zx;
  try (
    simpl;
    split;
    unfold NatMaps.find;
    unfold NatMaps.this;
    unfold NatMaps.add;
    rewrite NatMaps.Raw.Proofs.add_find; try apply NatMaps.is_bst;
    destruct (OrderedNat.compare x n); try assumption;
    inversion e;
    subst;
    contradiction
  ).
  - intros.
    split.
    + inversion H.
      inversion H12.
      apply inj_pair2_eq_dec in H21; [ | apply eq_nat_dec ].
      subst nIn0 nIn1.
      subst nOut0 nOut1.
      clear H20.
      clear H3 H4 H5 H6. 
      apply inj_pair2_eq_dec in H21; [ | apply eq_nat_dec ]. 
      inversion H13.
      subst zx4.
      apply inj_pair2_eq_dec in H4; [ | apply eq_nat_dec ]. 
      apply inj_pair2_eq_dec in H4; [ | apply eq_nat_dec ].
      subst zx5.
      simpl.
      destruct (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx1) eqn:Hzx1.
      destruct (A_G2_Edge_Annotator_Helper n0 n1 zx2) eqn:Hzx2.
      assert (n0 = (fst (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx1))) by (rewrite Hzx1; easy).
      assert (n1 = (snd (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx1))) by (rewrite Hzx1; easy).
      assert (n2 = (fst (A_G2_Edge_Annotator_Helper n0 n1 zx2))) by (rewrite Hzx2; easy).
      assert (n3 = (snd (A_G2_Edge_Annotator_Helper n0 n1 zx2))) by (rewrite Hzx2; easy).
      assert (WF_A_G2_ZX zx1 ->
              forall (baseOutMap baseInMap : NatMaps.t (list nat))
                (valOut valIn : option (list nat)) (x : NatMaps.key),
              NatMaps.find (elt:=list nat) x baseInMap = valIn ->
              NatMaps.find (elt:=list nat) x baseOutMap = valOut ->
              x <> get_id zx1 ->
              NatMaps.find (elt:=list nat) x
                (fst (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx1)) = valIn) as IHzx1_1.
                {
                  intros.
                  specialize (IHzx1 H7 baseOutMap0 baseInMap0 valOut0 valIn0 x0 H8 H9 H11).
                  destruct IHzx1.
                  assumption.
                }
      assert (WF_A_G2_ZX zx1 ->
              forall (baseOutMap baseInMap : NatMaps.t (list nat))
                (valOut valIn : option (list nat)) (x : NatMaps.key),
              NatMaps.find (elt:=list nat) x baseInMap = valIn ->
              NatMaps.find (elt:=list nat) x baseOutMap = valOut ->
              x <> get_id zx1 ->
              NatMaps.find (elt:=list nat) x
                (snd (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx1)) = valOut) as IHzx1_2.
                {
                  intros.
                  specialize (IHzx1 H7 baseOutMap0 baseInMap0 valOut0 valIn0 x0 H8 H9 H11).
                  destruct IHzx1.
                  assumption.
                }
        assert (WF_A_G2_ZX zx2 ->
                forall (baseOutMap baseInMap : NatMaps.t (list nat))
                  (valOut valIn : option (list nat)) (x : NatMaps.key),
                NatMaps.find (elt:=list nat) x baseInMap = valIn ->
                NatMaps.find (elt:=list nat) x baseOutMap = valOut ->
                x <> get_id zx2 ->
                NatMaps.find (elt:=list nat) x
                  (fst (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx2)) = valIn) as IHzx2_1.
                  {
                    intros.
                    specialize (IHzx2 H7 baseOutMap0 baseInMap0 valOut0 valIn0 x0 H8 H9 H11).
                    destruct IHzx2.
                    assumption.
                  }
        assert (WF_A_G2_ZX zx2 ->
                forall (baseOutMap baseInMap : NatMaps.t (list nat))
                  (valOut valIn : option (list nat)) (x : NatMaps.key),
                NatMaps.find (elt:=list nat) x baseInMap = valIn ->
                NatMaps.find (elt:=list nat) x baseOutMap = valOut ->
                x <> get_id zx2 ->
                NatMaps.find (elt:=list nat) x
                  (snd (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx2)) = valOut) as IHzx2_2.
                  {
                    intros.
                    specialize (IHzx2 H7 baseOutMap0 baseInMap0 valOut0 valIn0 x0 H8 H9 H11).
                    destruct IHzx2.
                    assumption.
                  }          
      assert (forall A (a1 a2 : A), fst (a1, a2) = a1) by easy.
      rewrite H3;
      rewrite H4;
      rewrite H5;
      rewrite H6.
      assert (exists valOut, NatMaps.find (get_id zx1) (snd (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx1)) = Some valOut).
      {
        apply all_lookup_id_snd.
        easy.
      }
      destruct H8.
      rewrite H8.
      assert (exists valOut, NatMaps.find (get_id zx1) (fst (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx1)) = Some valOut).
      {
        apply all_lookup_id_fst.
        easy.
      }
      destruct H9.
      rewrite H9.
      assert (exists valOut, NatMaps.find (get_id zx2) (snd (A_G2_Edge_Annotator_Helper n0 n1 zx2)) = Some valOut).
      {
        apply all_lookup_id_snd.
        easy.
      }
      destruct H11.
      rewrite H11.
      assert (exists valOut, NatMaps.find (get_id zx2) (fst (A_G2_Edge_Annotator_Helper n0 n1 zx2)) = Some valOut).
      {
        apply all_lookup_id_fst.
        easy.
      }
      destruct H19.
      rewrite H19.
      simpl in H2.
      unfold NatMaps.find.
      simpl.
      unfold NatMaps.add.
      rewrite NatMaps.Raw.Proofs.add_find; try apply NatMaps.is_bst.
      destruct (OrderedNat.compare x n) eqn:Hcomp.
      * simpl.
        apply (IHzx2_1 H18 _ _ valOut valIn).
        -- unfold NatMaps.find in IHzx1_1.
           rewrite H3.
           apply (IHzx1_1 H17 _ _ valOut valIn); try assumption. 
Abort.      


Lemma id_populated_inmap : forall {nIn nOut} (zx : A_G2_ZX nIn nOut) n baseInMap baseOutMap, In_A_G2_ZX n zx -> NatMaps.In n (fst (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)) /\ NatMaps.In n (snd (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx)).
Proof.
  intros.
  generalize dependent baseInMap.
  generalize dependent baseOutMap.
  generalize dependent n.
  induction zx;
  try (
    intros;
    split;
    inversion H;
    simpl;
    intros;
    unfold NatMaps.In;
    rewrite NatMaps.Raw.Proofs.In_alt;
    apply NatMaps.Raw.Proofs.add_in;
    left;
    easy).
  - intros.
    simpl.
    inversion H.
    + subst.
      inversion H10.
      apply inj_pair2_eq_dec in H6; [ | apply eq_nat_dec ]. 
      apply inj_pair2_eq_dec in H6; [ | apply eq_nat_dec ]. 
      inversion H11.
      apply inj_pair2_eq_dec in H7; [ | apply eq_nat_dec ]. 
      apply inj_pair2_eq_dec in H7; [ | apply eq_nat_dec ].
      subst.
      destruct H10.
      destruct H11.
      destruct H0.
      destruct H1.
      destruct H2.
      destruct H5.
      specialize (IHzx1 n0 H4).
      split.
      * destruct (A_G2_Edge_Annotator_Helper baseInMap baseOutMap zx1) eqn:H0.
        destruct (A_G2_Edge_Annotator_Helper n1 n2 zx2) eqn:H1.
        destruct zx1, zx2; simpl.
        -- destruct (NatMaps.find (elt:=list nat) n5 n3).
          destruct (NatMaps.find (elt:=list nat) n5 n4).
          destruct (NatMaps.find (elt:=list nat) n6 n3).
          destruct (NatMaps.find (elt:=list nat) n6 n4).
          unfold NatMaps.In;
          rewrite NatMaps.Raw.Proofs.In_alt.
          replace n3 with (fst (A_G2_Edge_Annotator_Helper n1 n2 (⦰AG2 n6))); [ | rewrite H1; easy ].
        admit.
Abort.       

(* 
  Proof steps: 
  1. Prove id is populated after visist.
  2. Prove all ids are populated
  3. Prove list length is equal to node in/outputs

*)