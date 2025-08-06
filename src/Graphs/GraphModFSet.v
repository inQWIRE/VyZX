Require Import Proportional.
Require Import ZXCore.
Require Import List.
Require Import Nat.
Require Import Decidable.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.FSets.FSetInterface.

Module Type ZXGModule (VertexSetModule : S) (EdgeSetModule : S).

  (* @nocheck name *)
  Definition VertexSet := VertexSetModule.t.
  (* @nocheck name *)
  Definition EdgeSet := EdgeSetModule.t.

  Parameter ZXG : Type.
  Parameter SemanticType : Type.
  Parameter semantic : ZXG -> SemanticType.

  (* Allows for flexible types of graph nodes *)
  Parameter VertexType : Type. 
  Parameter VertexZ : nat -> R -> VertexType.
  Parameter VertexX : nat -> R -> VertexType.

  Module VertexTypeSpec.
    Parameter decVT : forall (vt0 vt1 : VertexType), 
      decidable (vt0 = vt1).
    Parameter eqb_vt : VertexType -> VertexType -> bool.
    Parameter reflect_vt : forall (vt0 vt1 : VertexType), 
      reflect (vt0 = vt1) (eqb_vt vt0 vt1).
  End VertexTypeSpec.

  Definition Vertex := VertexSetModule.elt.

  Parameter v_idx : Vertex -> nat.
  Parameter v_rot : Vertex -> R.
  Parameter v_typ : Vertex -> VertexType.

  Parameter MkVertex : nat -> R -> VertexType -> Vertex.

  Module VertexSpec.

  End VertexSpec.

  Definition Edge := EdgeSetModule.elt.

  Inductive EdgeType :=
    | Boundary : nat -> EdgeType
    | Internal : nat -> EdgeType.

  Parameter edge_l : Edge -> EdgeType.
  Parameter edge_r : Edge -> EdgeType.
  Parameter edge_h : Edge -> bool.

  Parameter MkEdge : EdgeType -> EdgeType -> bool -> Edge.

  Module EdgeSpec.

    Parameter edge_eq_spec : forall e0 e1,
      edge_l e0 = edge_l e1 -> edge_r e0 = edge_r e1 -> edge_h e0 = edge_h e1 ->
      e0 = e1.

  End EdgeSpec.

  Parameter empty_graph : ZXG.

  Parameter MkGraph : VertexSet -> EdgeSet -> ZXG.

  Parameter vertices : ZXG -> VertexSet.
  Parameter edges : ZXG -> EdgeSet.

  Parameter MkGraph_vertices : forall (vs : VertexSet) (es : EdgeSet),
      vertices (MkGraph vs es) = vs.

  Parameter MkGraph_edges : forall (vs : VertexSet) (es : EdgeSet),
      edges (MkGraph vs es) = es.

  Definition add_v (v : Vertex) (G : ZXG) : ZXG := 
    MkGraph (VertexSetModule.add v (vertices G)) (edges G).
  Definition add_e (e : Edge) (G : ZXG) : ZXG :=
    MkGraph (vertices G) (EdgeSetModule.add e (edges G)).

  Definition remove_v (v : Vertex) (G : ZXG) : ZXG :=
    MkGraph (VertexSetModule.remove v (vertices G)) (edges G).
  Definition remove_e (e : Edge) (G : ZXG) : ZXG :=
    MkGraph (vertices G) (EdgeSetModule.remove e (edges G)).

  Definition In_v (v : Vertex) (G : ZXG) := 
    VertexSetModule.In v (vertices G).
  Definition In_e (e : Edge) (G : ZXG) :=
    EdgeSetModule.In e (edges G).

  Module VertexSetSpec.

    Lemma add_in_v : forall (v : Vertex) (G : ZXG),
      In_v v (add_v v G).
    Proof.
      intros.
      unfold In_v, add_v.
      rewrite MkGraph_vertices.
      apply VertexSetModule.add_1.
      apply VertexSetModule.E.eq_refl.
    Qed.

    Parameter in_v_empty : forall (v : Vertex),
      ~ In_v v empty_graph.

  End VertexSetSpec.

  Module EdgeSetSpec.

    Lemma add_in_e : forall (e : Edge) (G : ZXG),
      In_e e (add_e e G).
    Proof.
      intros.
      unfold In_e, add_e.
      rewrite MkGraph_edges.
      apply EdgeSetModule.add_1.
      apply EdgeSetModule.E.eq_refl.
    Qed.

    Parameter in_e_empty : forall (e : Edge),
      ~ In_e e empty_graph.

  End EdgeSetSpec.

End ZXGModule.

Module ZXGraph 
  (EdgeSetModule : S) (VertexSetModule : S) 
  (GraphModule : ZXGModule VertexSetModule EdgeSetModule).

  Include GraphModule.

  (* Graph Notations *)
  Notation " A '∝' B" := (proportional A B).
  Notation "'Z' α"    := (VertexZ α) (at level 20).
  Notation "'X' α"    := (VertexX α) (at level 20).
  Notation "∅"         := empty_graph.

  (* Vertex and Edge Notations *)
  Definition mk_vert (idx : nat) (vertid : VertexType) := 
    pair idx vertid.
  Notation "id @ idx" := (mk_vert idx id) (at level 20).
  Notation "id0 '--' id1" := (id0, id1, false) (at level 20).
  Notation "id0 'h-' id1" := (id0, id1, true) (at level 20).

  (* Low level graph construction notations *)
  Notation "v '+v' G" := 
    (add_v v G) (at level 41, right associativity).
  Notation "e '+e' G" := 
    (add_e e G) (at level 41, right associativity).

  (* Low level graph deconstruction notations *)
  Notation "v '-v' G" := 
    (remove_v v G) (at level 41, right associativity).
  Notation "e '-e' G" := 
    (remove_e e G) (at level 41, right associativity).

  Definition inputb (e : Edge) : bool :=
    match (edge_l e) with
    | Boundary _ => true
    | _ => false
    end.

  (* @nocheck name *)
  Inductive Input : Edge -> Prop :=
    | IsInput (idxl : nat) (etr : EdgeType) (b : bool) : 
        Input (MkEdge (Boundary idxl) etr b).

  Definition outputb (e : Edge) : bool :=
    match (edge_r e) with
    | Boundary _ => true
    | _ => false
    end.

  (* @nocheck name *)
  Inductive Output : Edge -> Prop :=
    | IsOutput (etl : EdgeType) (idxr : nat) (b : bool) : 
        Output (MkEdge etl (Boundary idxr) b).

  Definition internalb (e : Edge) : bool :=
    match (edge_l e) with
    | Internal _ => match (edge_r e) with
                    | Internal _ => true
                    | _ => false
                    end
    | _ => false
    end.

  Notation "'input?' e" := (inputb e) (at level 20).
  Notation "'output?' e" := (outputb e) (at level 20).
  Notation "'internal?' e" := (internalb e) (at level 20).
  Notation "'hadamard?' e" := (edge_h e) (at level 20).

  Definition edges_l (graph : ZXG) : EdgeSet := 
    EdgeSetModule.filter (inputb) (edges graph).

  Definition edges_r (graph : ZXG) : EdgeSet := 
    EdgeSetModule.filter (outputb) (edges graph).

  Definition edgetype_idx (et : EdgeType) : nat :=
    match et with
    | Boundary n => n
    | Internal n => n
    end.

  Definition eqb_edgetype (et0 et1 : EdgeType) : bool :=
    match (et0, et1) with
    | (Boundary n0, Boundary n1) => n0 =? n1
    | (Internal n0, Internal n1) => n0 =? n1
    | _ => false
    end.


  Definition composableb (e0 e1 : Edge) : bool :=
    eqb_edgetype (edge_r e0) (edge_l e1) && (output? e0) && (input? e1).

  Definition composable (e0 e1 : Edge) : Prop :=
    (edge_r e0 = edge_l e1) /\ Output e0 /\ Input e1.
    
  Definition compose_edge (e0 e1 : Edge) : Edge :=
    MkEdge (edge_l e0) (edge_r e1) 
    (xorb (edge_h e0) (edge_h e1)).

  Definition compose_and_accumulate (e0 : Edge) (acc : EdgeSet * EdgeSet) : EdgeSet * EdgeSet :=
    let (new_es, remaining_es1) := acc in
    let potential_matches :=
      EdgeSetModule.filter (fun e1 => composableb e0 e1) remaining_es1 in
    match EdgeSetModule.choose potential_matches with
    | None => (* No match for e0, so we keep it. *)
      (EdgeSetModule.add e0 new_es, remaining_es1)
    | Some e1 => (* Found a match e1. Compose e0 and e1, and consume e1. *)
      (EdgeSetModule.add (compose_edge e0 e1) new_es, EdgeSetModule.remove e1 remaining_es1)
    end.

  Definition compose_edge_to_edgeset (e : Edge) (es : EdgeSet) : EdgeSet :=
    let potential_matches := EdgeSetModule.filter (fun e1 => composableb e e1) es in
    if EdgeSetModule.is_empty potential_matches then
      EdgeSetModule.add e es
    else
      let composed_matches := EdgeSetModule.fold (fun e0 es0 => EdgeSetModule.add (compose_edge e e0) es0) EdgeSetModule.empty potential_matches in
      EdgeSetModule.union composed_matches (EdgeSetModule.diff es potential_matches).




  Definition compose_edgeset_to_edgeset 
    (es0 es1 : EdgeSet) : EdgeSet :=
    let composed_uncomposed := 
      EdgeSetModule.fold compose_and_accumulate es0 (EdgeSetModule.empty, es1) in
    EdgeSetModule.union (fst composed_uncomposed) (snd composed_uncomposed).

  Definition compose_graphs (zx0 zx1 : ZXG) : ZXG :=
    MkGraph (VertexSetModule.union (vertices zx0) (vertices zx1))
    (compose_edgeset_to_edgeset (edges zx0) (edges zx1)).

  Notation "A '↔' B" := (compose_graphs A B) (at level 42).

  Definition no_composable_to (e : Edge) (es : EdgeSet) : Prop :=
    forall e0, EdgeSetModule.In e0 es -> ~ (composable e e0).

  Definition no_composable_from (e : Edge) (es : EdgeSet) : Prop :=
    forall e0, EdgeSetModule.In e0 es -> ~ (composable e0 e).

  Lemma in_v_compose : forall (v : Vertex) (zx0 zx1 : ZXG),
    In_v v (compose_graphs zx0 zx1) <-> In_v v zx0 \/ In_v v zx1.
  Proof.
    intros v zx0 zx1.
    unfold In_v, compose_graphs.
    rewrite MkGraph_vertices.
    split.
    - apply VertexSetModule.union_1.
    - intros [H0 | H1].
      + apply (VertexSetModule.union_2 _ H0).
      + apply (VertexSetModule.union_3 _ H1).
  Qed.

  Lemma no_composable_filter : forall (e : Edge) (es : EdgeSet),
    no_composable_to e es ->
    EdgeSetModule.Equal (EdgeSetModule.filter (composableb e) es) EdgeSetModule.empty.
  Proof.
    intros.
    unfold EdgeSetModule.Equal.
    intros.
    split.
    - intros.
      apply EdgeSetModule.filter_2 in H0.
      unfold no_composable_to in H.

  Definition in_left_compose 
    (e : Edge) (zx0 zx1 : ZXG) : Prop :=
  In_e e zx0 /\ no_composable_to e (edges zx1).

  Definition in_right_compose
    (e : Edge) (zx0 zx1 : ZXG) : Prop :=
    In_e e zx1 /\ no_composable_from e (edges zx0).

  Definition is_joined_compose
    (e : Edge) (zx0 zx1 : ZXG) :=
    exists e0 e1, In_e e0 zx0 /\ In_e e1 zx1 /\ compose_edge e0 e1 = e.

  Parameter edge_compat_bool : forall e, compat_bool EdgeSetModule.E.eq
  (fun e0 : EdgeSetModule.elt => composableb e e0).

  Lemma reflect_output : forall (e : Edge),
    reflect (Output e) (output? e).
  Proof.
    intros.
    unfold outputb.
    destruct (edge_r e) eqn:Er.
    - constructor.
      destruct (edge_l e) eqn:El.

  Lemma reflect_composable : forall (e0 e1 : Edge),
    reflect (composable e0 e1) (composableb e0 e1).
  Proof.
    intros.
    unfold composable.
    unfold composableb.

  Lemma no_composable_filter_empty : forall (e : Edge) (es : EdgeSet),
    no_composable_to e es ->
    EdgeSetModule.Equal 
      (EdgeSetModule.filter (fun e0 => composableb e e0) es) 
      EdgeSetModule.empty.
  Proof.
    intros e es Hnc a.
    split.
    - unfold no_composable_to in Hnc.
      intros Hinf.
      specialize (Hnc a).
      specialize (EdgeSetModule.filter_2).
      intros Hft.
      specialize 
        (Hft es a 
          (fun e0 : EdgeSetModule.elt => composableb e e0)
          (edge_compat_bool e)
          Hinf).
      simpl in Hft.

  Lemma in_edgeset : forall (e : Edge) (es : EdgeSet),
    no_composable_to e es ->
    EdgeSetModule.In e (compose_edge_to_edgeset e es).
  Proof.
    intros.
    unfold compose_edge_to_edgeset.
    assert (EdgeSetModule.Equal (EdgeSetModule.filter (fun e1 : EdgeSetModule.elt => composableb e e1) es) EdgeSetModule.empty).
    { intros a.
      split.
      - intros.
        specialize (@EdgeSetModule.filter_1 es a 
        (fun e1 : EdgeSetModule.elt => composableb e e1)
        ).
        intros.
        specialize (@EdgeSetModule.filter_2 es a).
        intros.
        unfold no_composable_to in H.
        specialize (H a).
        contradict H.
        apply H1 in H0.
        intros.
        apply EdgeSetModule.filter_2 in H0.
        unfold no_composable_to in H. }

  Lemma in_e_compose : forall (e : Edge) (zx0 zx1 : ZXG),
    In_e e (compose_graphs zx0 zx1) <-> 
      in_left_compose e zx0 zx1 \/ 
      in_right_compose e zx0 zx1 \/ 
      is_joined_compose e zx0 zx1.
  Proof.
    intros v zx0 zx1.
    unfold In_e, compose_graphs.
    rewrite MkGraph_edges.
    split; intros.
    - admit.
    - destruct H.
      + destruct H.
        unfold compose_edgeset_to_edgeset.
        rewrite EdgeSetModule.fold_1.
        unfold In_e in H.
        apply EdgeSetModule.elements_1 in H.
        generalize dependent (edges zx1).
        induction (EdgeSetModule.elements (edges zx0)).
        * inversion H.
        * inversion H; subst.
          -- admit.
          -- simpl.
             intros.
             inversion H.
             ++ intros.
                subst.
        
  Admitted.



End ZXGraph.