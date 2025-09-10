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

Definition Edge   := (EdgeType * EdgeType * bool)%type.
Definition edge  (n0 n1 : EdgeType) : Edge := (n0, n1, false).
Definition hedge (n0 n1 : EdgeType) : Edge := (n0, n1, true).

Module OTV := 
  PairOrderedType Nat_as_OT R_as_OT.
Module OTE :=
  PairOrderedType EdgeType_as_OT EdgeType_as_OT.
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

  (* @nocheck name *)
  Definition EdgeSet := EdgeSetM.t.
  (* @nocheck name *)
  Definition VertexSet := VertexSetM.t.
  Transparent VertexSet.
  Transparent EdgeSet.

  Parameter MkGraph : VertexSet -> EdgeSet -> t.

  Parameter vertices : t -> VertexSet.
  Parameter edges    : t -> EdgeSet.

End ZXGModule.

Module Type ZXGraphM (GraphInstance :  ZXGModule).

  Include GraphInstance.

  (* @nocheck name *)
  Definition ZXGraph := t.
  Transparent ZXGraph.

  Definition empty_graph : ZXGraph :=
    MkGraph VertexSetM.empty EdgeSetM.empty.

  Definition add_vertex (v : Vertex) (zxg : ZXGraph) :=
    MkGraph (VertexSetM.add v (vertices zxg)) (edges zxg).
  Definition add_edge (e : Edge) (zxg : ZXGraph) :=
    MkGraph (vertices zxg) (EdgeSetM.add e (edges zxg)).

    (* Low level graph construction notations *)
  Notation "v '+v' G" := 
    (add_vertex v G) (at level 41, right associativity).
  Notation "e '+e' G" := 
    (add_edge e G) (at level 41, right associativity).

  Definition remove_vertex (v : Vertex) (zxg : ZXGraph) :=
    MkGraph (VertexSetM.remove v (vertices zxg)) (edges zxg).
  Definition remove_edge (e : Edge) (zxg : ZXGraph) :=
    MkGraph (vertices zxg) (EdgeSetM.remove e (edges zxg)).

  Notation "vs0 '[=v]' vs1" := (VertexSetM.Equal vs0 vs1) (at level 80).
  Notation "es0 '[=e]' es1" := (EdgeSetM.Equal es0 es1) (at level 80).

  (* @nocheck name *)
  Definition Equal (zx0 zx1 : ZXGraph) :=
    vertices zx0 [=v] vertices zx1 /\ 
    edges zx0 [=e] edges zx1.
  Notation "zx0 [=] zx1" := (Equal zx0 zx1) (at level 80).

    (* Low level graph construction notations *)
  Notation "v '-v' G" := 
    (remove_vertex v G) (at level 41, right associativity).
  Notation "e '-e' G" := 
    (remove_edge e G) (at level 41, right associativity).

  Definition v_idx (v : Vertex) : nat :=
    fst (fst v).
  
  Definition et_idx (et : EdgeType) : nat :=
  match et with
  | Boundary n => n
  | Internal n => n
  end.

  Definition edge_l (e : Edge) : EdgeType :=
    fst (fst e).
  Definition edge_l_idx (e : Edge) : nat :=
    et_idx (edge_l e).
  Definition edge_r (e : Edge) : EdgeType :=
    snd (fst e).
  Definition edge_r_idx (e : Edge) : nat :=
    et_idx (edge_r e).
  Definition edge_b (e : Edge) : bool :=
    snd e.

  Definition input (e : Edge) : Prop :=
    edge_l e = Boundary (edge_l_idx e).
  Definition output (e : Edge) : Prop :=
    edge_r e = Boundary (edge_r_idx e).
  Definition internal (e : Edge) : Prop :=
    edge_l e = Internal (edge_l_idx e) /\
    edge_r e = Internal (edge_r_idx e).
  Definition boundary (e : Edge) : Prop :=
    input e \/ output e.
  Definition hadamard (e : Edge) : Prop :=
    edge_b e = true.

  Definition inputb (edge : Edge) : bool :=
    match edge_l edge with
    | Boundary _ => true
    | _          => false
    end.

  Definition outputb (edge : Edge) : bool :=
    match edge_r edge with
    | Boundary _ => true
    | _          => false
    end.

  Definition internalb (edge : Edge) : bool :=
    match edge with
    |(Internal _, Internal _, _) => true
    | _ => false
    end.
  
  Definition boundaryb (e: Edge) : bool :=
    inputb e || outputb e.

  Notation "'input?' e" := (inputb e) (at level 20).
  Notation "'output?' e" := (outputb e) (at level 20).
  Notation "'internal?' e" := (internalb e) (at level 20).
  Notation "'boundary?' e" := (boundaryb e) (at level 20).
  Notation "'hadamard?' e" := (edge_b e) (at level 20).

  Lemma reflect_input : forall (e : Edge),
    reflect (input e) (input? e).
  Proof.
    intros [[[][]]]; simpl.
    1-2: left; unfold input; 
      unfold edge_l_idx; unfold edge_l;
      simpl; reflexivity.
    1-2: right; intros contra;
      inversion contra. Qed.
  
  Lemma reflect_output : forall (e : Edge),
    reflect (output e) (output? e).
  Proof.
    intros [[[][]]]; simpl.
    1, 3: left; unfold input; 
      unfold edge_r_idx; unfold edge_r;
      simpl; reflexivity.
    1-2: right; intros contra;
      inversion contra. Qed.

  Lemma reflect_boundary : forall (e : Edge),
    reflect (boundary e) (boundary? e).
  Proof.
    unfold boundaryb.
    unfold boundary.
    intros.
    destruct (reflect_input e); [left; left; assumption|].
    destruct (reflect_output e); [left; right; assumption|].
    right.
    intros [c|c]; contradiction. 
  Qed.

  Lemma reflect_internal : forall (e : Edge),
    reflect (internal e) (internal? e).
  Proof.
    intros [[[][]]]; simpl.
    1-2: right; intros contra; inversion contra;
      unfold edge_l in H; simpl; discriminate H.
    - right; intros contra; inversion contra;
      unfold edge_l in H0; simpl; discriminate H0.
    - left. unfold internal. split.
      + unfold edge_l, edge_l_idx. simpl. reflexivity.
      + unfold edge_r, edge_r_idx. simpl. reflexivity. 
  Qed.

  Lemma reflect_hadamard : forall (e : Edge),
    reflect (hadamard e) (hadamard? e).
  Proof.
    intros [ p [] ].
    - constructor; reflexivity.
    - constructor; intros c.
      inversion c.
  Qed.

  Parameter vertices_add_vertex : forall v zx,
    vertices (v +v zx) = VertexSetM.add v (vertices zx).
  
  Parameter edges_add_vertex : forall v zx,
    edges (v +v zx) = edges zx.

  Lemma add_vertex_compat_eq : forall v zx0 zx1,
  zx0 [=] zx1 -> v +v zx0 [=] v +v zx1.
  Proof.
    intros v zx0 zx1 [Hv He].
    unfold Equal.
    split.
    - unfold VertexSetM.Equal.
      unfold VertexSetM.Equal in Hv.
      intros a.
      split.
      + intros.
        rewrite vertices_add_vertex in H.
        rewrite VertexSetM.add_spec in H.
        destruct H.
        * simpl in H.
          rewrite H.
          rewrite vertices_add_vertex.
          rewrite VertexSetM.add_spec.
          left; auto.
        * rewrite vertices_add_vertex.
          rewrite VertexSetM.add_spec.
          right.
          rewrite <- Hv.
          auto.
      + intros.
        rewrite vertices_add_vertex in H.
        rewrite VertexSetM.add_spec in H.
        destruct H.
        * simpl in H.
          rewrite H.
          rewrite vertices_add_vertex.
          rewrite VertexSetM.add_spec.
          left; auto.
        * rewrite vertices_add_vertex.
          rewrite VertexSetM.add_spec.
          right.
          rewrite Hv.
          auto.
    - split; intros.
      + rewrite edges_add_vertex.
        rewrite edges_add_vertex in H.
        unfold EdgeSetM.Equal in He.
        rewrite <- He.
        assumption.
      + rewrite edges_add_vertex.
        rewrite edges_add_vertex in H.
        unfold EdgeSetM.Equal in He.
        rewrite He.
        auto.
  Qed.
    

  Lemma add_vertex_comm : forall v0 v1 zxg, 
    v0 +v v1 +v zxg [=] v1 +v v0 +v zxg.
  Proof.
    intros v0 v1 zxg.
    split.
    - split; intros.
      + repeat rewrite vertices_add_vertex.
        repeat rewrite vertices_add_vertex in H.
        repeat rewrite VertexSetM.add_spec.
        repeat rewrite VertexSetM.add_spec in H.
        destruct H as [ | [ | ]]; auto.
      + repeat rewrite vertices_add_vertex.
        repeat rewrite vertices_add_vertex in H.
        repeat rewrite VertexSetM.add_spec.
        repeat rewrite VertexSetM.add_spec in H.
        destruct H as [ | [ | ]]; auto.
    - repeat rewrite edges_add_vertex.
      reflexivity.
  Qed.

End ZXGraphM.