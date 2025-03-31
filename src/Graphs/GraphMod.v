Require Import Proportional.
Require Import ZXCore.
Require Import List.
Require Import Nat.
Require Import Decidable.
Require Import Coq.Arith.PeanoNat.

(*   autosubst                                                    *)
(* C Rework edges to be end - ver ver - ver end - end ver - end   *)
(* C Hadamard Edges                                               *)
(* C Subgraph Isolation *)
(*   Subgraph Isolation Proof *)
(*   Phase gadgets                                                *)
(*   Sum of diagrams                                              *)
(*   Arbitrary Scalars                                            *)
(*   Flow and Flow Conditions - eventual circuit extraction       *)

Module Type ZXGModule.

  Parameter ZXG : Type.
  Parameter proportional : ZXG -> ZXG -> Prop.
  Parameter SemanticType : Type.
  Parameter semantic : ZXG -> SemanticType.

  (* Allows for flexible types of graph nodes *)
  Parameter VertexType : Type. 
  Parameter VertexZ : R -> VertexType.
  Parameter VertexX : R -> VertexType.
  Parameter decVT : forall (vt0 vt1 : VertexType), decidable (vt0 = vt1).
  Parameter eqb_vt : VertexType -> VertexType -> bool.
  Parameter reflect_vt : forall (vt0 vt1 : VertexType), 
    reflect (vt0 = vt1) (eqb_vt vt0 vt1).

  Parameter empty_graph : ZXG.

(* Typed aliases for indexing internal graphs *)
  Definition Idx    : Type := nat. 
  Definition Vertex : Type := (Idx * VertexType).

(* Different types of edges we may see *)
  Inductive EdgeType : Type :=
    | Boundary : Idx -> EdgeType
    | Internal : Idx -> EdgeType.

  Definition Edge : Type := (EdgeType * EdgeType * bool).

  (* Accessing different parts of graph *)
  Parameter vertices : ZXG -> list Vertex.
  Parameter edges : ZXG -> list Edge.

  (* Building graphs incrementally *)
  Parameter add_vertex : Vertex -> ZXG -> ZXG.
  Parameter add_edge : Edge -> ZXG -> ZXG.

  (* Destructing graphs incrementally *)
  Parameter remove_vertex : Vertex  -> ZXG -> ZXG.
  Parameter remove_edge : Edge ->
    ZXG -> ZXG.

  (* Algebraic constructors for graphs (might define) *)

  (* Axioms for well behaved adding and removal of vertices and edges *)
  Parameter add_vertex_commutes : forall (G : ZXG) (v0 v1 : Vertex),
    add_vertex v1 (add_vertex v0 G) = add_vertex v0 (add_vertex v1 G).
  Parameter remove_add_vertex : forall (G : ZXG) (v : Vertex),
    remove_vertex v (add_vertex v G) = G.
  Parameter remove_add_edge : forall (G : ZXG) (e : Edge),
    remove_edge e (add_edge e G) = G.

End ZXGModule.

Module ZXGraph (GraphInstance :  ZXGModule).

  Include GraphInstance.

  (* Graph Notations *)
  Notation " A '∝' B" := (proportional A B).
  Notation "'Z' α"    := (VertexZ α) (at level 20).
  Notation "'X' α"    := (VertexX α) (at level 20).
  Notation "∅"         := empty_graph.

  (*  *)
  Notation "id @ idx" := (idx, id) (at level 20).
  Notation "id0 '--' id1" := (id0, id1, false) (at level 20).
  Notation "id0 'h-' id1" := (id0, id1, true) (at level 20).

  (* Low level graph construction notations *)
  Notation "v '+v' G" := 
    (add_vertex v G) (at level 41, right associativity).
  Notation "e '+e' G" := 
    (add_edge e G) (at level 41, right associativity).

  (* Low level graph deconstruction notations *)
  Notation "v '-v' G" := 
    (remove_vertex v G) (at level 41, right associativity).
  Notation "e '-e' G" := 
    (remove_edge e G) (at level 41, right associativity).

  Definition inputb (edge : Edge) : bool :=
    match edge with
    | (Boundary _, _, _) => true
    | _               => false
    end.

  Definition outputb (edge : Edge) : bool :=
    match edge with
    | (_, Boundary _, _) => true
    | _               => false
    end.

  Definition internalb (edge : Edge) : bool :=
    match edge with
    |(Internal _, Internal _, _) => true
    | _ => false
    end.

  Definition hadamardb (edge : Edge) : bool :=
    match edge with
    | (_, _, hb) => hb
    end.

  Notation "'input?' e" := (inputb e) (at level 20).
  Notation "'output?' e" := (outputb e) (at level 20).
  Notation "'internal?' e" := (internalb e) (at level 20).
  Notation "'hadamard?' e" := (hadamardb e) (at level 20).

  Definition ledges (graph : ZXG) : list Edge := 
    filter (inputb) (edges graph).

  Definition redges (graph : ZXG) : list Edge := 
    filter (outputb) (edges graph).

  Definition edgetype_idx (e : EdgeType) : nat :=
    match e with
    | Boundary x | Internal x => x
    end.

  (* Decidable Equality for vertices, edges, and edgetypes. *)

  Lemma dec_eq_vert (v0 v1 : Vertex) : decidable (v0 = v1).
  Proof.
    destruct v0, v1.
    destruct (decVT v v0), (dec_eq_nat i i0); subst.
    2-4: right;
      intros pairEQ;
      inversion pairEQ;
      contradiction.
    - left; reflexivity. Qed.

  Definition dec_eq_et : forall (et0 et1 : EdgeType), decidable (et0 = et1).
  Proof.
    intros [] [].
    - destruct (dec_eq_nat i i0); subst.
      + left; reflexivity.
      + right; intros contra.
        inversion contra; contradiction.
    - right; intros contra; inversion contra.
    - right; intros contra; inversion contra.
    - destruct (dec_eq_nat i i0); subst.
      + left; reflexivity.
      + right; intros contra.
        inversion contra; contradiction. Qed.

  Definition dec_eq_edge : forall (e0 e1 : Edge), decidable (e0 = e1).
  Proof.
    intros [[e0l e0r] []] [[e1l e1r] []];
      destruct (dec_eq_et e0l e1l), (dec_eq_et e0r e1r); subst; 
        try (left; reflexivity); 
        right; intros contra; inversion contra; contradiction. Qed.

  (* Reflect equality over vertices and edges *)

  Notation "vt0 =vt? vt1" := (eqb_vt vt0 vt1) (at level 40).

  Definition eqb_edgetype (id0 : EdgeType) (id1 : EdgeType) : bool :=
    match (id0, id1) with
    | (Internal x, Internal y)
    | (Boundary x, Boundary y) => x =? y
    | _ => false
    end.
  Notation "et0 '=et?' et1" := (eqb_edgetype et0 et1) (at level 40).

  Definition eqb_edge (e0 e1 : Edge) : bool :=
    match (e0, e1) with
    | ((l, r, b), (l', r', b')) => (l =et? l') && (r =et? r') && bool_eq b b'
    end.
  Notation "e0 '=e?' e1" := (eqb_edge e0 e1) (at level 40).

  Definition eqb_vert (v0 v1 : Vertex) : bool :=
    match (v0, v1) with
    | ((i0, t0), (i1, t1)) => (i0 =? i1) && (t0 =vt? t1)
    end.
  Notation "v0 '=v?' v1" := (eqb_vert v0 v1) (at level 40).

  Definition reflect_vert : forall (v0 v1 : Vertex), 
      reflect (v0 = v1) (v0 =v? v1).
  Proof.
    intros [i0 vt0] [i1 vt1].
    unfold eqb_vert.
    destruct (reflect_vt vt0 vt1), (Nat.eqb_spec i0 i1); 
      try (subst; left; reflexivity); 
      subst; right; intros contra; inversion contra; contradiction. Qed.

  Definition reflect_edgetype : forall (et0 et1 : EdgeType),
      reflect (et0 = et1) (et0 =et? et1).
  Proof.
    intros [] [];
    unfold eqb_edgetype;
    destruct (Nat.eqb_spec i i0); subst; try (left; reflexivity);
      right; intros contra; inversion contra; contradiction. Qed.

  Definition reflect_edge : forall (e0 e1 : Edge),
      reflect (e0 = e1) (e0 =e? e1).
  Proof.
    unfold eqb_edge.
    intros [[][]][[][]];
      destruct (reflect_edgetype e e1);
        destruct (reflect_edgetype e0 e2); subst; simpl; 
          try (left; reflexivity);
          right; intros contra; inversion contra; contradiction. Qed.
  
  Definition vertex_idx : Vertex -> nat := fst.
  Definition left_et   (e : Edge) : EdgeType := fst (fst e).
  Definition right_et  (e : Edge) : EdgeType := snd (fst e).
  Definition left_idx  (e : Edge) : nat := edgetype_idx (left_et e).
  Definition right_idx (e : Edge) : nat := edgetype_idx (right_et e).

  Definition edges_idx (graph : ZXG) : list nat :=
    match (split (edges graph)) with
    | (lr, _) => match (split lr) with
                | (l, r) => map edgetype_idx (l ++ r)
                 end
    end.

  (* Get a fresh index for the purposes of graph isolation, 
     they have arbitrary space above them *)
  Definition fresh_idx (graph : ZXG) : nat :=
    S (list_max (edges_idx graph ++ map vertex_idx (vertices graph))).
  
  (* Repeated addition of vertices and edges *)
  Reserved Notation "e '^e' n '+e' zxg"
    (at level 41, right associativity).
  Fixpoint add_n_edges (zx : ZXG) (idx0 : EdgeType) 
    (idx1 : EdgeType) (iter : nat) : ZXG :=
      match iter with
      | 0 => zx
      | S k => idx0 -- idx1 +e add_n_edges zx idx0 idx1 k
      end.
  Notation "e '^e' n '+e' zxg" := (add_n_edges zxg (fst (fst e)) (snd (fst e)) n).
  
  Fixpoint add_list_edges (zx : ZXG) (el : list Edge) : ZXG :=
    match el with
    | [] => zx
    | e::es => e +e add_list_edges zx es
    end.
  Notation "ls +el zxg" := 
    (add_list_edges zxg ls) (at level 41, right associativity).

  Fixpoint remove_list_edges (zx : ZXG) (el : list Edge) : ZXG :=
    match el with
    | [] => zx
    | e::es => e -e remove_list_edges zx es
    end.
  Notation "ls -el zxg" := 
    (remove_list_edges zxg ls) (at level 41, right associativity).

  Fixpoint add_list_vertices (zx : ZXG) (el : list Vertex) : ZXG :=
    match el with
    | [] => zx
    | v::vs => v +v add_list_vertices zx vs
    end.
  Notation "ls +vl zxg" := 
    (add_list_vertices zxg ls) (at level 41, right associativity).

  Fixpoint remove_list_vertices (zx : ZXG) (vl : list Vertex) : ZXG :=
    match vl with
    | [] => zx
    | v::vs => v -v remove_list_vertices zx vs
    end.
  Notation "ls -vl zxg" := 
    (remove_list_vertices zxg ls) (at level 41, right associativity).

  Definition vertex_in_edge (v : Vertex) (e : Edge) :=
    let vidx := vertex_idx v in
      (vidx =? left_idx e) || (vidx =? right_idx e).

  Definition connected_verticesb (zxg : ZXG) (v0 v1 : Vertex) : bool :=
    existsb 
      (fun e => vertex_in_edge v0 e && vertex_in_edge v1 e) 
      (edges zxg).
  Notation "x '-?' y 'in' G" := (connected_verticesb G x y) (at level 40).

  (* Access elements of the graph *)
  Definition vertex_neighborhood (zxg : ZXG) (v : Vertex) : list Vertex := 
    filter (fun v0 => v -? v0 in zxg) (vertices zxg).
  Definition vertex_neighborhood_edges (zxg : ZXG) (v : Vertex) : list Edge :=
    filter (vertex_in_edge v) (edges zxg).

  Definition input_edges_vert (zxg : ZXG) (v : Vertex) : list Edge :=
    filter (fun e => vertex_in_edge v e && input? e) (edges zxg).

  Definition output_edges_vert (zxg : ZXG) (v : Vertex) : list Edge :=
    filter (fun e => vertex_in_edge v e && output? e) (edges zxg).

  Definition internal_edges_vert (zxg : ZXG) (v : Vertex) : list Edge :=
    filter (fun e => vertex_in_edge v e && internal? e) (edges zxg).

  (* High level graph rewriting through induced subgraphs *)
  Parameter induced_subgraph :
    ZXG -> list Vertex -> list Vertex -> ZXG.

  Fixpoint list_minus (data remover : list nat) : list nat.
  Proof.
    intros.
    destruct remover.
    - exact data.
    - exact (list_minus (remove Nat.eq_dec n data) remover).
  Defined.

  Fixpoint satisfy {A} (P : A -> bool) (lst : list A) : option A.
  Proof.
    destruct lst.
    - exact None.
    - case (P a).
      + exact (Some a).
      + exact (satisfy A P lst).
  Defined.

  Fixpoint remap_edges_input (idx : nat) (es : list Edge) :=
    match es with
    | []    => []
    | e::es => match e with
               | (_, r, b) => (Boundary idx, r, b)::(remap_edges_input (S idx) es)
               end
    end.

  Fixpoint remap_edges_output (idx : nat) (es: list Edge) :=
    match es with
    | []    => []
    | e::es => match e with
               | (l, _, b) => (l, Boundary idx, b)::(remap_edges_output (S idx) es)
               end
    end.

  Fixpoint remap_edges_internal_l (idx : nat) (es: list Edge) :=
    match es with
    | []    => []
    | e::es => match e with
               | (_, r, b) => (Internal idx, r, b)::(remap_edges_internal_l idx es)
               end
    end.

  Fixpoint remap_edges_internal_r (idx : nat) (es: list Edge) :=
    match es with
    | []    => []
    | e::es => match e with
               | (l, _, b) => (l, Internal idx, b)::(remap_edges_internal_r idx es)
               end
    end.

  Definition composable_edges (e0 e1 : Edge) : bool :=
    match (e0, e1) with
    | ((l, r, b), (l', r', b')) => (et_eqb r l')
    end.

  Definition move_ident_to_left (id : EdgeType) (e : Edge) :=
    match e with
    | (l, r, b) => if et_eqb r id then (r, l, b) else (l, r, b)
    end.
  Definition move_ident_to_right (id : EdgeType) (e : Edge) :=
    match e with
    | (l, r, b) => if et_eqb l id then (r, l, b) else (l, r, b)
    end.
  Definition flip (e : Edge) :=
    match e with
    | (l, r, b) => (r, l, b)
    end.

  (* Definition pull_vertex_left' (vert : Vertex)  *)
  (*   (target : ZXG) (source : ZXG) : (ZXG * ZXG) := *)

  Definition split_edge (between : nat) (e : Edge) : (Edge * Edge) :=
    match e with
    | (l, r, b) => ((l, Boundary between, b), 
                    (Boundary between, r, false))
    end.

  Fixpoint split_edges_from (start : nat) (edges : list Edge) : list (Edge * Edge) :=
    match edges with
    | [] => []
    | e::es => split_edge start e :: split_edges_from (S start) es
    end.
  
  Definition separate_vert_from_graph (vert : Vertex)
    (source : ZXG) : (ZXG * ZXG).
  Proof.
    specialize (input_edges_vert source vert) as vert_inputs.
    specialize (output_edges_vert source vert) as vert_outputs.
    specialize (internal_edges_vert source vert) as vert_internal.
    specialize 
      (split (split_edges_from (fresh_idx source) 
              (internal_edges_vert source vert))) as inis.
    exact (((fst inis) +el vert_inputs +el vert_outputs +el vert +v ∅), ((snd inis) +el vert -v vert_inputs -el vert_outputs -el vert_internal -el source)).
  Defined.

  Print separate_vert_from_graph.

  Definition isolate_vertex (vert : Vertex) (source : ZXG) : ZXG :=
    fst (separate_vert_from_graph vert source).

  Definition remove_vertex_and_edges (vert : Vertex) (source : ZXG) : ZXG :=
    snd (separate_vert_from_graph vert source).

  Fixpoint compose_edge_to_list (e : Edge) (el  : list Edge) : list Edge :=
    match el  with
    | [] => [e]
    | e'::es => match (e, e') with
                | ((l, r, bv), (l' , r', bv')) => 
                    if r =? r'
                    then (l, r', if bv then negb bv' else bv) :: es
                    else e' :: (compose_edge_to_list e es)
                end
    end.

  Fixpoint compose_edgelist_to_edgelist (el0 el1 : list Edge) : list Edge :=
    match el0 with
    | [] => el1
    | e'::es => compose_edgelist_to_edgelist es (compose_edge_to_list e' el1)
    end.

  Definition shift (zx : ZXG) (degree : nat) : ZXG := zx.

  Definition compose (zx0 zx1 : ZXG) : ZXG := 
    (compose_edgelist_to_edgelist (edges zx0) (edges zx1)) +el vertices zx0 +vl vertices zx1 +vl ∅.

  Definition stack (zx0 zx1 : ZXG) : ZXG :=
    (edges zx0) +el (vertices zx0) +vl zx1.

  (* Ways to combine graphs *)
  Notation "A '↔' B" := (compose A B) (at level 42).
  Notation "A '⊗' B" := (stack A B).

  Definition pull_vertex_left (vert : Vertex) 
    (target : ZXG) (source : ZXG) : (ZXG * ZXG) :=
    match separate_vert_from_graph vert source with 
    | (zx0, zx1) => (target ↔ zx0, zx1)
    end.

  Fixpoint subgraph_rec (acc : ZXG) (zx : ZXG) (vl : list Vertex) : ZXG * ZXG :=
    match vl with
    | [] => (acc, zx)
    | v::vs => match pull_vertex_left v acc zx with
               | (nacc, nzx) => subgraph_rec nacc nzx vs
               end
    end.

  Definition isolate_subgraph (zx : ZXG) (vl : list Vertex) := 
    fst (subgraph_rec zx ∅ vl). 

  Definition remove_subgraph (zx : ZXG) (vl : list Vertex) := 
    snd (subgraph_rec zx ∅ vl).

  Definition remove_vertex_subgraph (zx : ZXG) (v : Vertex) :=
    vertex_neighborhood_edges zx v -el v -v zx.

  
  (* Subgraph Equivalence and Vertex/Edge in Graphs *)

  Definition In_v (v : Vertex) (zx : ZXG) := In v (vertices zx).
  Definition In_e (e : Edge) (zx : ZXG) := In e (edges zx).

  Definition equiv_graphs (zx0 zx1 : ZXG) :=
    forall (v : Vertex) (e : Edge),
    (In_v v zx0 <-> In_v v zx1) /\
    (In_e e zx0 <-> In_e e zx1).
  Notation "zx0 '≡g' zx1" := (equiv_graphs zx0 zx1) (at level 70).

  Fixpoint remove_vertexlist_subgraph (zx : ZXG) (vl : list Vertex) :=
    match vl with
    | [] => zx
    | v::vs => remove_vertexlist_subgraph (remove_vertex_subgraph zx v) vs
    end.

  Parameter vertices_add_v_comm : forall (v : Vertex) (zx : ZXG),
    vertices (v +v zx) = v :: vertices zx.
  Parameter vertices_add_e_comm : forall (e : Edge) (zx : ZXG),
    vertices (e +e zx) = vertices zx.
  Parameter edges_add_v_comm : forall (v : Vertex) (zx : ZXG),
    edges (v +v zx) = edges zx.
  Parameter edges_add_e_comm : forall (e : Edge) (zx : ZXG),
    edges (e +e zx) = e :: edges zx.
  Parameter edges_empty : edges ∅ = [].
  Parameter vertices_empty : vertices ∅ = [].

  Lemma v_not_in_empty : forall (v : Vertex), ~ In_v v ∅. 
  Proof. 
    intros v contra. 
    unfold In_v in contra. 
    rewrite vertices_empty in contra.
    assumption. Qed.

  Lemma e_not_in_empty : forall (e : Edge), ~ In_e e ∅. 
  Proof.
    intros e contra. 
    unfold In_e in contra. 
    rewrite edges_empty in contra.
    assumption. Qed.

  Lemma vertices_add_vl_comm : forall (vl : list Vertex) (zx : ZXG),
    vertices (vl +vl zx) = vl ++ vertices zx.
  Proof.
    induction vl.
    - reflexivity.
    - simpl. intros. rewrite vertices_add_v_comm.
      rewrite IHvl.
      reflexivity. Qed.

  Lemma edges_add_el_comm : forall (el : list Edge) (zx : ZXG),
    edges (el +el zx) = el ++ edges zx.
  Proof.
    induction el.
    - reflexivity.
    - simpl. intros. rewrite edges_add_e_comm.
      rewrite IHel.
      reflexivity. Qed.

  Lemma vertices_add_el_comm : forall (el : list Edge) (zx : ZXG),
    vertices (el +el zx) = vertices zx.
  Proof.
    induction el.
    - reflexivity.
    - simpl; intros. rewrite vertices_add_e_comm.
      rewrite IHel. reflexivity. Qed.

  Lemma edges_add_vl_comm : forall (vl : list Vertex) (zx : ZXG),
    edges (vl +vl zx) = edges zx.
  Proof.
    induction vl.
    - reflexivity.
    - simpl; intros. rewrite edges_add_v_comm.
      rewrite IHvl. reflexivity. Qed.


  Lemma In_v_add_v_here : forall (v : Vertex) (zx : ZXG),
    In_v v (v +v zx).
  Proof.
    intros.
    unfold In_v.
    rewrite vertices_add_v_comm.
    constructor; reflexivity. Qed.

  Lemma In_v_add_v_list : forall (v : Vertex) (vl : list Vertex) (zx : ZXG),
    In v vl -> In_v v (vl +vl zx).
  Proof.
    induction vl; intros; inversion H.
    - subst.
      simpl.
      apply In_v_add_v_here.
    - simpl.
      unfold In_v.
      rewrite vertices_add_v_comm.
      right.
      apply IHvl.
      assumption. Qed.

  Lemma In_v_add_e : forall (v : Vertex) (e : Edge) (zx : ZXG),
    In_v v zx -> In_v v (e +e zx).
  Proof.
    intros.
    unfold In_v.
    rewrite vertices_add_e_comm.
    apply H. Qed.
    
  Lemma In_v_add_e_list : forall (v : Vertex) (el : list Edge) (zx : ZXG),
    In_v v zx -> In_v v (el +el zx).
  Proof.
    induction el; intros; [assumption |].
    simpl.
    apply In_v_add_e.
    apply IHel.
    assumption. Qed.

  Create HintDb graphalg.
  Hint Rewrite vertices_add_e_comm : graphalg. 
  Hint Rewrite vertices_add_el_comm : graphalg. 
  Hint Rewrite vertices_add_v_comm : graphalg. 
  Hint Rewrite vertices_add_vl_comm : graphalg. 
  Hint Rewrite vertices_empty : graphalg.
  Hint Rewrite edges_add_e_comm : graphalg. 
  Hint Rewrite edges_add_el_comm : graphalg. 
  Hint Rewrite edges_add_v_comm : graphalg. 
  Hint Rewrite edges_add_vl_comm : graphalg. 
  Hint Rewrite edges_empty : graphalg.

  Ltac graphalg_simpl := autorewrite with graphalg.

  Lemma vertices_isolate_vertex : forall (v : Vertex) (zx : ZXG), 
    vertices (isolate_vertex v zx) = [v].
  Proof.
    intros.
    unfold isolate_vertex.
    unfold separate_vert_from_graph.
    simpl.
    graphalg_simpl.
    reflexivity. Qed.

  Lemma v_in_isolate_implies_eq : forall (v0 v1 : Vertex) (zx : ZXG),
    In_v v0 (isolate_vertex v1 zx) -> v0 = v1.
  Proof.
    intros.
    unfold In_v in H.
    rewrite vertices_isolate_vertex in H.
    inversion H; auto.
    contradiction H0. Qed.

  Lemma v_in_isolate : forall (v : Vertex) (zx : ZXG),
    In_v v (isolate_vertex v zx).
  Proof.
    intros.
    unfold In_v.
    rewrite vertices_isolate_vertex.
    left; reflexivity. Qed.

  Lemma compose_in_v_l : forall (v : Vertex) (zx0 zx1 : ZXG),
    In_v v zx0 -> In_v v (zx0 ↔ zx1).
  Proof.
    intros.
    unfold In_v in H.
    unfold compose.
    apply In_v_add_e_list.
    apply In_v_add_v_list.
    assumption. Qed.

  Lemma compose_in_v_r : forall (v : Vertex) (zx0 zx1 : ZXG),
    In_v v zx1 -> In_v v (zx0 ↔ zx1).
  Proof.
    intros.
    unfold In_v in H.
    unfold compose.
    apply In_v_add_e_list. Admitted.

  Lemma vertices_compose_distribute : forall (v : Vertex) (zx0 zx1 : ZXG),
    In v ((vertices zx0) ++ (vertices zx1)) ->
    In v (vertices (zx0 ↔ zx1)).
  Proof.
    intros.
    rewrite in_app_iff in H.
    destruct H.
    - apply compose_in_v_l.
      apply H.
    - apply compose_in_v_r.
      apply H. Qed.

  Lemma In_v_compose_In_v : forall (v : Vertex) (zx0 zx1 : ZXG),
    In_v v (zx0 ↔ zx1) -> In_v v zx0 \/ In_v v zx1.
  Proof.
    intros.
    unfold In_v.
    Search (In _ _ \/ In _ _).
    rewrite <- in_app_iff.
    unfold In_v in H.
    unfold compose in H. Admitted.

  Lemma separate_maintains_graph : 
    forall (vert : Vertex) (source : ZXG),
      isolate_vertex vert source ↔ 
      remove_vertex_and_edges vert source ≡g source.
  Proof. 
    intros.
    intros v e.
    split.
    - destruct (dec_eq_vert v vert); subst.

      


    - split.
      + intros.
        apply In_v_compose_In_v in H.
        destruct H.
        * specialize (v_in_isolate_implies_eq v vert source H) as Hveq; 
            subst.
          admit.
        * admit.
      + intros.
        admit.
    - split.
      + intros.
        admit.
      + intros.
        admit.
  Admitted.

  Notation "zxa '|_' inputs '#' vertices" := 
      (induced_subgraph zxa inputs vertices) (at level 40).
  Parameter replace_subgraph : forall (G : ZXG) (S : list Vertex) (H : ZXG), ZXG.
  Notation "G '|_{' S '>=>' H '}'" := (replace_subgraph G S H) (at level 40).
  Parameter gen_rewrite : forall {n m o p : nat} 
    (G : ZXG) (S : list Vertex) (I : list Vertex) 
    (H : ZXG) (P : H ∝ G |_ I # S), 
      G ∝ G |_{ S >=> H }.

  (* Parameter permute_inputs *)

  (* Google doc of contributions for VyZX - Google Doc, different contributions and 
     different configurations of papers. ViCAR, etc. *)

  (* Stating ZX-Calc rules in the language *)

  Definition Bo : nat -> EdgeType := Boundary.
  Definition It : nat -> EdgeType := Internal.

  Definition bialg_l : ZXG := 
    It 2 -- Bo 2 +e It 3 -- Bo 3 +e
    Bo 0 -- It 0 +e Bo 1 -- It 1 +e
    It 0 -- It 2 +e It 0 -- It 3 +e
    It 1 -- It 2 +e It 1 -- It 3 +e
    (X 0) @ 3 +v (X 0) @ 2 +v 
    (Z 0) @ 1 +v (Z 0) @ 0 +v ∅.

  Definition bialg_r : ZXG :=
     Bo 0 -- It 0 +e Bo 1 -- It 0 +e 
     It 1 -- Bo 0 +e It 1 -- Bo 1 +e
    (X 0) @ 0 +v (Z 0) @ 1 +v ∅ .

  (* Parameter bialgebra_rule : bialg_l ∝ bialg_r. *)

  (* Definition hopf_l : ZXG 1 1 := *)
  (* 0 <=> 1 +e 0 <=>1 +e <=> 1 +e 0 <=> +e *)
  (* (Z 0) @ 1 +v (X 0) @ 0 +v ∅ . *)

  (* Definition hopf_r : ZXG 1 1 := *)
  (* <=> 1 +e 0 <=> +e *)
  (* (Z 0) @ 1 +v (X 0) @ 0 +v ∅ . *)

  (* Parameter hopf_rule : hopf_l ∝ hopf_r. *)

  (* Definition fusion_g_l_fin {m : nat} {α β : R} : ZXG 2 2 := *)
  (*   0 <-> +e 1 <=> +e *)
  (*   <=> 0 +e <=> 1 +e *)
  (*   0 <=> 1 ^e m +e *)
  (*   (Z α) @ 0 +v Z β @ 1 +v ∅.  *)

  (* Definition fusion_g_r_fin {α β : R} : ZXG 2 2 := *)
  (*   0 <=> +e 0 <=> +e *)
  (*   <=> 0 +e <=> 0 +e *)
  (*   Z (α + β) @ 0 +v ∅. *)

  (* Parameter fusion_g_fin : forall {α β : R}, *)
  (*   @fusion_g_l_fin α β ∝ @fusion_g_r_fin α β. *)

  (* Definition fusion_g_l {n0 n1 o0 o1 m} {α β : R} : ZXG := *)
  (*   0 - 1 ^e m +e *)
  (*   0 - 1 ^e o0 +e 1 - 0 ^e o1 +e *)
  (*   1 - 0 ^e n0 +e 0 - 1 ^e n1 +e *)
  (*   (Z β) @ 1 +v (Z α) @ 0 +v ∅ . *)

  (* Definition fusion_g_r {n0 n1 o0 o1} {α β : R} : ZXG (n0 + (n1 + 0)) (o0 + (o1 + 0)) := *)
  (*   0 <=> ^e o0 +e 1 <=> ^e o1 +e *)
  (*   <=> 0 ^e n0 +e <=> 1 ^e n1 +e *)
  (*   (Z (α + β)) @ 0 +v ∅ . *)

  (* Parameter fusion_g : forall {n0 n1 o0 o1 m : nat} {α β : R}, *)
  (*   @fusion_g_l n0 n1 o0 o1 m α β ∝ @fusion_g_r n0 n1 o0 o1 α β. *)

  Local Close Scope nat.

End ZXGraph.
