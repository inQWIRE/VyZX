Set Implicit Arguments.

Require Import Lists.List.
Require Import externals.QuantumLib.Complex.
Import ListNotations.

Local Open Scope nat_scope.

Inductive Edge : Set :=
| None : Edge
| E : Edge
| H : Edge.

Definition AdjMatrix (n : nat) := nat -> nat -> Edge.

Definition StartNode := 0.
Definition EndNode := 1.

Definition isEdge (e : Edge) : bool :=
  match e with
  | None => false
  | E => true
  | H => true
  end.

Fixpoint isWalk {n : nat} (l : list nat) (A : AdjMatrix n) (source sink : nat) : bool :=
  match l with
  | [] => true
  | a :: l' => (isEdge (A source a)) && (isWalk l' A a sink)
  end.

Inductive ConnectedGraph : Type :=
  | CG (n : nat) (A : AdjMatrix n) : (forall (source sink : nat), (source <> sink) -> (source <= n) -> (source <= n) -> exists l, isWalk l A source sink = true) -> ConnectedGraph.

Inductive EqAdj : Type :=
   | PointWiseEqAdj (n : nat) (A B : AdjMatrix n) : forall (a b : nat), (a <= n) -> (b <= n) -> (A a b) = (B a b) -> EqAdj.

Definition NodeWeightMap (n : nat) := nat -> C.


