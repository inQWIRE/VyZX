Require Import Proportional.
Require Import ZXCore.
Require Import List.
Require Import Nat.

Module Type ZXGModule.

  Parameter ZXG : Type.
  Parameter proportional : ZXG -> ZXG -> Prop.

  (* Allows for flexible types of graph nodes *)
  Parameter VertexType : Type. 
  Parameter VertexZ : R -> VertexType.
  Parameter VertexX : R -> VertexType.

  Parameter empty_graph : ZXG.

(* Typed aliases for indexing internal graphs *)
  Definition Idx    : Type := nat. 
  Definition Vertex : Type := (Idx * VertexType).

(* Different types of edges we may see *)
  Inductive EdgeType : Type :=
    | Boundary : Idx -> EdgeType
    | Internal : Idx -> EdgeType.

  Definition Edge : Type := (EdgeType * EdgeType).

(*  autosubst                                                    *)
(*  Rework edges to be end - ver ver - ver end - end ver - end   *)
(*  Hadamard Edges                                               *)
(*  Phase gadgets                                                *)
(*  Sum of diagrams                                              *)
(*  Arbitrary Scalars                                            *)
(*  Flow and Flow Conditions - eventual circuit extraction       *)
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
  Parameter compose : forall {n m o : nat}, 
    ZXG -> ZXG -> ZXG.
  Parameter stack   : forall {n m o p : nat}, 
    ZXG -> ZXG -> ZXG.

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

  (* Low level graph construction notations *)
  Notation "vt '@' vidx '+v' G" := 
    (add_vertex (vidx, vt) G) (at level 41, right associativity).
  Notation "idx0 '-' idx1 '+e' G" := 
    (add_edge (idx0, idx1) G) (at level 41, right associativity).

  (* Low level graph deconstruction notations *)
  Notation "vt '@' vidx '-v' G" := 
    (remove_vertex (vidx, vt) G) (at level 41, right associativity).
  Notation "idx0 '-' idx1 '-e' G" := 
    (remove_edge (idx0, idx1) G) (at level 41, right associativity).

  Definition inputb (edge : Edge) : bool :=
    match edge with
    | (Boundary _, _) => true
    | _               => false
    end.

  Definition outputb (edge : Edge) : bool :=
    match edge with
    | (_, Boundary _) => true
    | _               => false
    end.

  Definition internalb (edge : Edge) : bool :=
    match edge with
    |(Internal _, Internal _) => true
    | _ => false
    end.

  Notation "'input?' e" := (inputb e) (at level 20).
  Notation "'output?' e" := (outputb e) (at level 20).
  Notation "'internal?' e" := (internalb e) (at level 20).

  Definition ledges (graph : ZXG) : list Edge := filter (inputb) (edges graph).

  Definition redges (graph : ZXG) : list Edge := filter (outputb) (edges graph).

  Definition edgetype_idx (e : EdgeType) : nat :=
    match e with
    | Boundary x | Internal x => x
    end.
  
  Definition vertex_idx (v : Vertex) : nat :=
    match v with
    | (id, vt) => id
    end.

  Definition left_et (e : Edge) : EdgeType :=
    match e with
    | (l, r) => l
    end.

  Definition right_et (e : Edge) : EdgeType :=
    match e with
    | (l, r) => r
    end.

  Definition left_idx (e : Edge) : nat := edgetype_idx (left_et e).
  Definition right_idx (e : Edge) : nat := edgetype_idx (right_et e).

  Definition edges_idx (graph : ZXG) : list nat :=
    match (split (edges graph)) with
    | (l, r) => map edgetype_idx (l ++ r)
    end.

  (* Get a fresh index for the purposes of graph isolation, 
     they have arbitrary space above them *)
  Definition fresh_idx (graph : ZXG) : nat :=
    S (list_max (edges_idx graph ++ map fst (vertices graph))).
  
  (* Repeated addition of vertices and edges *)
  Reserved Notation "bidx '-' idx '^e' n '+e' zxg"
    (at level 41, right associativity).
  Fixpoint add_n_edges (zx : ZXG) (idx0 : EdgeType) 
    (idx1 : EdgeType) (iter : nat) : ZXG :=
      match iter with
      | 0 => zx
      | S k => idx0 - idx1 +e idx0 - idx1 ^e k +e zx
      end
      where "bidx '-' idx '^e' n '+e' zxg" :=
      (add_n_edges zxg bidx idx n).
    
  (* Ways to combine graphs *)
  Notation "A '+' B" := (compose A B).
  Notation "A '⊗' B" := (stack A B).
  
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

  Definition pull_vertex_left (vert : Vertex) 
    (target : ZXG) (source : ZXG) : (ZXG * ZXG).
  Proof.
    destruct vert as [idx ty].
    exact (source, source). Defined.

  Definition isolate_subgraph :
    ZXG -> list Vertex -> list Vertex -> ZXG.
  Proof.
  Admitted.

  Definition induce_subgraph : 
    ZXG -> list Vertex -> list Vertex -> ZXG.
  Proof.
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

  Local Open Scope nat.

  (* Stating ZX-Calc rules in the language *)

  (* Definition bialg_l : ZXG 2 2 :=  *)
  (*   2 <=> +e 3 <=> +e *)
  (*   <=> 0 +e <=> 1 +e *)
  (*   0 <=> 2 +e 0 <=> 3 +e *)
  (*   1 <=> 2 +e 1 <=> 3 +e *)
  (*   (X 0) @ 3 +v (X 0) @ 2 +v  *)
  (*   (Z 0) @ 1 +v (Z 0) @ 0 +v ∅. *)

  (* Definition bialg_r : ZXG 2 2 := *)
  (*   <=> 0 +e <=> 0 +e 1 <=> +e 1 <=> +e *)
  (*   (X 0) @ 0 +v (Z 0) @ 1 +v ∅ . *)

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
