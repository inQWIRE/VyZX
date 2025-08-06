Require Import Proportional.
Require Import ZXCore.
Require Import List.
Require Import Nat.
Require Import Decidable.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.FSets.FSetInterface.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Structures.Orders.



Module ZXG.


  Module ZXVert.
    
    Inductive Vertex := 
    | zsp (n : nat) (r : R)
    | xsp (n : nat) (r : R).


    Definition lt (x y : ZXVert.Vertex) :=
      match x, y with
      | ZXVert.zsp n0 r0, ZXVert.zsp n1 r1 => 
          if n0 =? n1 then (Rlt r0 r1) else (n0 < n1)%nat
      | ZXVert.zsp _ _, ZXVert.xsp _ _ => True
      | ZXVert.xsp _ _, ZXVert.zsp _ _ => False
      | ZXVert.xsp n0 r0, ZXVert.xsp n1 r1 => 
        if n0 =? n1 then r0 < r1 else (n0 < n1)%nat
      end.

  End ZXVert.

  Module OTVertex <: OrderedType.

    Definition t := ZXVert.Vertex.

    Definition eq (x y : ZXVert.Vertex) := x = y.

    Definition eq_equiv : Equivalence eq.
    Proof.
      constructor.
      - constructor.
      - intros x y H.
        rewrite H.
        reflexivity.
      - intros x y z H0 H1.
        rewrite H0, H1.
        reflexivity. Qed.

    Definition lt := ZXVert.lt.
    
  End OTVertex.

  Module EdgeSet := FSetAVL.Make OTVertex.

End EdgeSet.

End ZXG.