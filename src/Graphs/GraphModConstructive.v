Require Import ZXCore.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Reals.ROrderedType.
Require Import Coq.MSets.MSetAVL.
Require Import Coq.MSets.MSetInterface.

Definition Vertex := (nat * R * bool)%type.
Definition zsp (n : nat) (r : R) := (n, r, false).
Definition xsp (n : nat) (r : R) := (n, r, true).

Inductive EdgeType :=
  | Boundary (n : nat) : EdgeType
  | Internal (n : nat) : EdgeType.

Module EdgeType_as_OT <: OrderedType.

  Definition t := EdgeType.

  Definition eq (x y : t) := x = y.

  Definition eq_equiv : Equivalence eq.
  Proof.
    constructor.
    - intros x; easy.
    - intros x y []; easy.
    - intros x y z [] []; easy. Qed.

  Local Open Scope nat.

  Definition lt (x y : t) :=
  match x, y with
  | Boundary n0, Boundary n1 => n0 < n1
  | Internal n0, Internal n1 => n0 < n1
  | Internal n0, Boundary n1 => True
  | Boundary n0, Internal n1 => False
  end.

  Definition lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [] Hlt.
      + apply (Nat.lt_irrefl n);
        assumption.
      + apply (Nat.lt_irrefl n);
        auto.
    - intros [] [] []; simpl; intros H0 H1; 
        try auto; try contradiction;
        transitivity n0; auto. Qed.

  Definition lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
    constructor;
      rewrite H, H0; auto. Qed.
  
  Definition compare (x y : t) : comparison :=
  match x, y with
  | Boundary n0, Boundary n1 => Coq.Init.Nat.compare n0 n1
  | Internal n0, Internal n1 => Coq.Init.Nat.compare n0 n1
  | Internal n0, Boundary n1 => Lt
  | Boundary n0, Internal n1 => Gt
  end.

  Definition compare_spec : forall (x y : t),
    CompareSpec (x=y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [] []; simpl; try (constructor; auto).
    - destruct (n ?= n0) eqn:E; constructor.
      + apply Nat.compare_eq in E; subst; auto. 
      + apply nat_compare_Lt_lt in E; auto.
      + apply nat_compare_Gt_gt in E; auto.
    - destruct (n ?= n0) eqn:E; constructor.
      + apply Nat.compare_eq in E; subst; auto.
      + apply nat_compare_Lt_lt in E; auto.
      + apply nat_compare_Gt_gt in E; auto.
  Qed.

  Definition eq_dec : forall (x y : t), 
    {x = y} + {x <> y}.
  Proof.
    intros [] [].
    - destruct (Nat.eq_dec n n0); subst.
      + left; reflexivity.
      + right; injection; auto.
    - right; easy.
    - right; easy.
    - destruct (Nat.eq_dec n n0); subst.
      + left; reflexivity.
      + right; injection; auto.
  Qed.

End EdgeType_as_OT.

Definition Edge   := (nat * nat * bool)%type.
Definition edge  (n0 n1 : nat) := (n0, n1, false).
Definition hedge (n0 n1 : nat) := (n0, n1, true).

Module OTV := 
  PairOrderedType Nat_as_OT R_as_OT.
Module OTE :=
  PairOrderedType Nat_as_OT Nat_as_OT.
Module OTEdge := 
  PairOrderedType OTE Bool_as_OT.
Module OTVertex :=
  PairOrderedType OTV Bool_as_OT.

Module EdgeSetM := MSetAVL.Make OTEdge.
Module VertexSetM := MSetAVL.Make OTVertex.

Module Type ZXGModule.

  Parameter t : Type.
  Parameter proportional : t -> t -> Prop.
  Parameter st : Type.
  Parameter semantic : t -> st.
  
  Parameter MkGraph : VertexSetM.t -> EdgeSetM.t -> t.

  Parameter vertices : t -> VertexSetM.t.
  Parameter edges    : t -> EdgeSetM.t.

End ZXGModule.

Module ZXGraph (GraphInstance :  ZXGModule).

  Include GraphInstance.