Require Import ZXCore.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Reals.ROrderedType.
Require Import Coq.MSets.MSetAVL.
Require Import Coq.MSets.MSetInterface.

Definition Vertex := (nat * R * bool)%type.
Definition Edge   := (nat * nat * bool)%type.

Module OTV := 
  PairOrderedType Nat_as_OT R_as_OT.
Module OTE :=
  PairOrderedType Nat_as_OT Nat_as_OT.
Module OTEdge := 
  PairOrderedType OTE Bool_as_OT.
Module OTVertex :=
  PairOrderedType OTV Bool_as_OT.

Module EdgeSet := MSetAVL.Make OTEdge.
Module VertexSet := MSetAVL.Make OTVertex.

