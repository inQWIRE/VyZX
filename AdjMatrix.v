Set Implicit Arguments.

Require Import Lists.List.
Require Import externals.QuantumLib.Complex.
Import ListNotations.

Local Open Scope nat_scope.

Inductive Edge : Set :=
| NEdge : Edge
| E : Edge.

Definition AdjMatrix (n : nat) := nat -> nat -> Edge.

Definition edgeCount (e : Edge) :=
  match e with
  | NEdge => 0
  | E     => 1
  end.

Fixpoint columnSumRecurse {n : nat} (col : nat) (rec : nat) 
                                    (mat : AdjMatrix n) :=
  match rec with
  | 0   => edgeCount (mat 0 col)
  | S k => edgeCount (mat (S k) col) + (columnSumRecurse 0 k mat)
  end.

Definition colSum {n : nat} (col : nat) (mat : AdjMatrix n) :=
  columnSumRecurse col n mat.

Fixpoint rowSumRecurse {n : nat} (row : nat) (rec : nat) 
                                    (mat : AdjMatrix n) :=
match rec with
| 0   => edgeCount (mat row 0)
| S k => edgeCount (mat row (S k)) + (rowSumRecurse 0 k mat)
end.

Definition rowSum {n : nat} (row : nat) (mat : AdjMatrix n) :=
  rowSumRecurse row n mat.


Definition identity (size : nat) : AdjMatrix size :=
  fun n m =>
  match n =? m with
  | true  => E
  | false => NEdge
  end.

Definition allOnes (size : nat) : AdjMatrix size :=
  fun n m => E.

Definition identity2b2 : AdjMatrix 2 :=
  identity 2.

Lemma testRowSum : rowSum 0 (identity2b2) = 1.
Proof. intros. unfold rowSum. reflexivity. Qed.
(*
Flaws highlighted here: Can't easily go down in the size of our matrices.

Lemma testRowSumN : forall (n : nat), rowSum 0 (allOnes n) = S n.
Proof. induction n.
  - unfold rowSum. reflexivity.
  - unfold rowSum in *.
    simpl.
*)
Lemma testColSum : colSum 0 (identity2b2) = 1.
Proof. intros. unfold colSum. reflexivity. Qed. 

Definition isEdgeP (e : Edge) : Prop :=
  e = E.

Definition notNoneP (e : Edge) : Prop :=
  e <> NEdge.

Definition isEdge (e : Edge) : bool :=
  match e with
  | NEdge => false
  | E => true
  end.

Lemma isEdgePropToBool (e : Edge) : isEdgeP e -> isEdge e = true.
Proof.
  intro H; destruct e. discriminate. easy.
Qed.

Lemma isEdgeBoolToProp (e : Edge) : isEdge e = true -> isEdgeP e.
Proof.
  intro H; destruct e.
  - discriminate H.
  - reflexivity.
Qed.

Fixpoint isWalk {n : nat} (l : list nat) (A : AdjMatrix n) (source sink : nat) : bool :=
  match l with
  | [] => true
  | a :: l' => (isEdge (A source a)) && (isWalk l' A a sink)
  end.

Inductive ConnectedGraph : Type :=
  | CG (n : nat) (A : AdjMatrix n) : (forall (source sink : nat), (source <> sink) -> (source <= n) -> (source <= n) -> exists l, isWalk l A source sink = true) -> ConnectedGraph.

Inductive EqAdj : Type :=
   | PointWiseEqAdj (n : nat) (A B : AdjMatrix n) : forall (a b : nat), (a <= n)
   -> (b <= n) -> (A a b) = (B a b) -> EqAdj.
   
  