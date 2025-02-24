Require Import Proportional.
Require Import ZXCore.
Require Import List.
Require Import Nat.

Module Type ZXGModule.

  Parameter ZXG : nat -> nat -> Type.

  (* Allows for flexible types of graph nodes *)
  Parameter VertexType : Type. 
  Parameter proportional : forall {n m : nat}, ZXG n m -> ZXG n m -> Prop.

  Parameter VertexZ : R -> VertexType.
  Parameter VertexX : R -> VertexType.

  Parameter empty_graph : ZXG 0 0.

(* Typed aliases for indexing internal graphs *)
  Definition VertexIdx  : Type := nat. 
  Definition Vertex     : Type := (VertexIdx * VertexType).
  Definition IEdge      : Type := (VertexIdx * VertexIdx).

(* Typed aliases for the different types of boundary cases we may see *)
  Definition BoundaryType : Type := nat.
  Definition LEdge        : Type := (BoundaryType * VertexIdx).
  Definition REdge        : Type := (VertexIdx * BoundaryType).
  Definition BEdge        : Type := (BoundaryType * BoundaryType).
  Definition Edge         : Type := (nat * nat).

  (* Accessing different parts of graph *)
  Parameter vertices : forall {n m : nat}, 
    ZXG n m -> list Vertex.
  Parameter iedges   : forall {n m : nat},
    ZXG n m -> list IEdge.
  Parameter ledges   : forall {n m : nat},
    ZXG n m -> list LEdge.
  Parameter redges   : forall {n m : nat},
    ZXG n m -> list REdge.
  Parameter bedges   : forall {n m : nat},
    ZXG n m -> list BEdge.

  (* Building graphs incrementally *)
  Parameter add_vertex : forall {n m : nat}, 
    Vertex -> ZXG n m -> ZXG n m.
  Parameter add_internal_edge : forall {n m : nat}, 
    ZXG n m -> IEdge -> ZXG n m.
  Parameter add_input_edge : forall {n m : nat}, 
    ZXG n m -> LEdge -> ZXG (S n) m.
  Parameter add_output_edge : forall {n m : nat}, 
    ZXG n m -> REdge -> ZXG n (S m).
  Parameter add_boundary_edge : forall {n m : nat},
    ZXG n m -> BEdge -> ZXG (S n) (S m).

  (* Destructing graphs incrementally *)
  Parameter remove_vertex : forall {n m : nat}, 
    ZXG n m -> Vertex -> ZXG n m.
  Parameter remove_internal_edge : forall {n m : nat}, 
    ZXG n m -> IEdge -> ZXG n m.
  Parameter remove_input_edge : forall {n m : nat}, 
    ZXG (S n) m -> LEdge -> ZXG n m.
  Parameter remove_output_edge : forall {n m : nat}, 
    ZXG n (S m) -> REdge -> ZXG n m.
  Parameter remove_boundary_edge : forall {n m : nat},
    ZXG (S n) (S m) -> BEdge -> ZXG n m.

  (* Algebraic constructors for graphs (might define) *)
  Parameter compose : forall {n m o : nat}, 
    ZXG n m -> ZXG m o -> ZXG n o.
  Parameter stack   : forall {n m o p : nat}, 
    ZXG n m -> ZXG o p -> ZXG (n + m) (o + p).

  (* Axioms for well behaved adding and removal of vertices and edges *)
  Parameter add_vertex_commutes : forall {n m : nat} (G : ZXG n m) (v0 v1 : Vertex),
    add_vertex v1 (add_vertex v0 G) = add_vertex v0 (add_vertex v1 G).
  Parameter remove_add_vertex : forall {n m : nat} (G : ZXG n m) (v : Vertex),
    remove_vertex (add_vertex v G) v = G.
  Parameter remove_add_iedge : forall {n m : nat} (G : ZXG n m) (e : Edge),
    remove_internal_edge (add_internal_edge G e) e = G.
  Parameter remove_add_ledge : forall {n m : nat} (G : ZXG n m) (e : Edge),
    remove_input_edge (add_input_edge G e) e = G.
  Parameter remove_add_redge : forall {n m : nat} (G : ZXG n m) (e : Edge),
    remove_output_edge (add_output_edge G e) e = G.
  Parameter remove_add_bedge : forall {n m : nat} (G : ZXG n m) (e : Edge),
    remove_boundary_edge (add_boundary_edge G e) e = G.

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
  Notation "idx0 '<i>' idx1 '+e' G" := 
    (add_internal_edge G (idx0, idx1)) (at level 41, right associativity).
  Notation "idx0 '<l>' idx1 '+e' G" := 
    (add_input_edge G (idx0, idx1)) (at level 41, right associativity).
  Notation "idx0 '<r>' idx1 '+e' G" := 
    (add_output_edge G (idx0, idx1)) (at level 41, right associativity).
  Notation "idx0 '<b>' idx1 '+e' G" := 
    (add_boundary_edge G (idx0, idx1)) (at level 41, right associativity).

  (* Low level graph deconstruction notations *)
  Notation "vt '@' vidx '-v' G" := 
    (remove_vertex G (vidx, vt)) (at level 41, right associativity).
  Notation "idx0 '<i>' idx1 '-e' G" := 
    (remove_internal_edge G (idx0, idx1)) (at level 41, right associativity).
  Notation "idx0 '<l>' idx1 '-e' G" := 
    (remove_input_edge G (idx0, idx1)) (at level 41, right associativity).
  Notation "idx0 '<r>' idx1 '-e' G" := 
    (remove_output_edge G (idx0, idx1)) (at level 41, right associativity).
  Notation "idx0 '<b>' idx1 '-e' G" := 
    (remove_boundary_edge G (idx0, idx1)) (at level 41, right associativity).

  (* Get a fresh index for the purposes of graph isolation, 
     they have arbitrary space above them *)
  Definition fresh_idx {n m} (graph : ZXG n m) : nat :=
    S (list_max (map fst (ledges graph) ++ 
                 map snd (redges graph) ++ 
                 map fst (vertices graph))).

  (* Repeated addition of vertices and edges *)
  Reserved Notation "bidx '<l>' idx '^e' n '+e' zxg" 
    (at level 41, right associativity).
  Fixpoint add_n_input_edges {n m : nat} (zx : ZXG n m) 
                         (bidx : BoundaryType) (idx : VertexIdx) (iter : nat) : 
    ZXG (iter + n) m :=
    match iter as k return (ZXG (k + n) m) with
    | 0 => zx
    | S k => bidx <l> idx +e (S bidx) <l> idx ^e k +e zx
    end
  where "bidx '<l>' idx '^e' n '+e' zxg" := 
    (add_n_input_edges zxg bidx idx n).

  Reserved Notation "idx '<r>' bidx '^e' n '+e' zxg" 
    (at level 41, right associativity).
  Fixpoint add_n_output_edges {n m : nat} (zx : ZXG n m) 
                          (idx : VertexIdx) (bidx : BoundaryType) (iter : nat) : 
    ZXG n (iter + m) :=
    match iter as k return (ZXG n (k + m)) with
    | 0 => zx
    | S k => idx <r> bidx +e idx <r> (S bidx) ^e k +e zx
    end
    where "idx '<r>' bidx '^e' n '+e' zxg" := 
      (add_n_output_edges zxg idx bidx n).

  Reserved Notation "idxl '<i>' idxr '^e' n '+e' zxg" 
    (at level 41, right associativity).
  Fixpoint add_n_internal_edges {n m : nat} (zx : ZXG n m) 
                      (idxl idxr : VertexIdx) (iter : nat) : 
    ZXG n m :=
    match iter with
    | 0 => zx
    | S k => idxl <i> idxr +e idxl <i> idxr ^e k +e zx
    end
    where "idxl '<i>' idxr '^e' n '+e' zxg" := 
      (add_n_internal_edges zxg idxl idxr n).
  
  Reserved Notation "idxl '<b>' idxr '^e' n '+e' zxg" 
    (at level 41, right associativity).
  Fixpoint add_n_boundary_edges {n m : nat} (zx : ZXG n m) 
                      (idxl idxr : BoundaryType) (iter : nat) : 
                      ZXG (iter + n) (iter + m) :=
    match iter as k return (ZXG (k + n) (k + m)) with
    | 0 => zx
    | S k => idxl <b> idxr +e idxl <b> idxr ^e k +e zx
    end
    where "idxl '<b>' idxr '^e' n '+e' zxg" := 
      (add_n_boundary_edges zxg idxl idxr n).

  (* Ways to combine graphs *)
  Notation "A '+' B" := (compose A B).
  Notation "A '⊗' B" := (stack A B).
  
  (* Testing properties of the graph *)
  Definition connected_vertices {n m : nat} (zxg : ZXG n m) 
    (l : Vertex) (r : Vertex) : bool :=
    let gv := iedges zxg in
      (existsb (fun p => 
                orb (andb (fst p =? (fst l)) (snd p =? (fst r)))
                    (andb (fst p =? (fst r)) (snd p =? (fst l))))
                gv).
  Notation "x '<i>?' y 'in' G" := (connected_vertices G x y) (at level 40).
  
  Definition connected_edge (vert : VertexIdx) (edge : Edge) :=
    (fst edge =? vert) || (snd edge =? vert).

  (* Access elements of the graph *)
  Definition all_edges {n m : nat} (zxg : ZXG n m) : list LEdge :=
    ledges zxg ++ iedges zxg ++ redges zxg.

  Definition input_edges_vert {n m : nat} (zxg : ZXG n m) (vert : VertexIdx) : list LEdge :=
    filter (connected_edge vert) (ledges zxg).

  Definition internal_edges_vert {n m : nat} (zxg : ZXG n m) (vert : VertexIdx) : list IEdge :=
    filter (connected_edge vert) (iedges zxg).
  Definition output_edges_vert {n m : nat} (zxg : ZXG n m) (vert : VertexIdx) : list REdge :=
    filter (connected_edge vert) (redges zxg).

  Definition neighborhood_edges {n m : nat} (zxg : ZXG n m) (vert : VertexIdx) : list IEdge := 
    filter (connected_edge vert) (all_edges zxg).

  (* High level graph rewriting through induced subgraphs *)
  Parameter induced_subgraph : forall {n m o p : nat}, 
    ZXG n m -> list VertexIdx -> list VertexIdx -> ZXG o p.

  Fixpoint list_minus (data remover : list nat) : list nat.
  Proof.
    intros.
    destruct remover.
    - exact data.
    - exact (list_minus (remove Nat.eq_dec n data) remover).
  Defined.

  Fixpoint add_list_vertices {n m} (verts : list Vertex) : ZXG n m -> ZXG n m.
  Proof.
    intros zx.
    destruct verts as [|[lbl rog] verts].
    - exact zx.
    - exact ((add_list_vertices _ _ verts) (rog @ lbl +v zx)).
  Defined.

  Fixpoint satisfy {A} (P : A -> bool) (lst : list A) : option A.
  Proof.
    destruct lst.
    - exact None.
    - case (P a).
      + exact (Some a).
      + exact (satisfy A P lst).
  Defined.

  Fixpoint get_vertices {n m} (verts : list VertexIdx) : ZXG n m -> list (VertexIdx * VertexType).
  Proof.
    intros zxg.
    specialize (vertices zxg) as gverts.
    exact (fold_left (fun acc nxt => acc)
                     gverts []).
  Defined.

  Definition join_edge (ledge : LEdge) (redge : REdge) : IEdge :=
    (fst ledge, snd redge).

  Definition pull_vertex_left {n m o p} (vert : Vertex) 
    (target : ZXG o p) (source : ZXG n m) : (ZXG o p * ZXG n m).
  Proof.
    destruct vert                                          as [idx ty].
    specialize (max (fresh_idx target) (fresh_idx source)) as f_idx.
    specialize (input_edges_vert source idx)               as source_inputs.
    specialize (internal_edges_vert source idx)            as source_internal.
    specialize (output_edges_vert source idx)              as source_output.
    specialize (ty @ idx -v source)                        as newsource.
    specialize (ty @ idx +v target)                        as newtarget.
    exact (newtarget, newsource). Defined.

  Definition isolate_subgraph : forall {n m o p : nat},
    ZXG n m -> list VertexIdx -> list (VertexIdx * VertexType) -> ZXG o p.
  Proof.
    intros n m o p graph inputs internal.
    specialize (vertices graph) as all_vertices.
    specialize (iedges graph) as all_edges.
    specialize (map fst all_vertices) as all_vertices_idx.
    specialize (map fst internal) as internal_idx.
    specialize (filter 
                    (fun e => 
                      (0 <? (count_occ Nat.eq_dec internal_idx (fst e)))
                   || (0 <? (count_occ Nat.eq_dec internal_idx (snd e)))) 
                    all_edges) 
      as connected_to_internal.
    specialize (filter
                    (fun e =>
                      (0 <? (count_occ Nat.eq_dec inputs (fst e)))
                   || (0 <? (count_occ Nat.eq_dec inputs (snd e))))
                connected_to_internal)
      as input_connected_to_internal.
    specialize (filter
                    (fun e =>
                      (0 =? (count_occ Nat.eq_dec inputs (fst e)))
                   || (0 =? (count_occ Nat.eq_dec inputs (snd e))))
                connected_to_internal)
      as output_connected_to_internal.
    specialize 0%nat as x.
    specialize (add_list_vertices internal empty_graph) as subgraph.
  Admitted.

  Definition induce_subgraph : forall {n m o p : nat},
    ZXG n m -> list VertexIdx -> list (VertexIdx * VertexType) -> ZXG o p.
  Proof.
    intros n m o p big_graph inputs internal.
    specialize (vertices big_graph) as all_vertices.
    specialize (iedges big_graph) as all_edges.
    specialize (list_minus (list_minus (map fst all_vertices) inputs) (map fst internal)) as remainder.
    specialize (add_list_vertices internal empty_graph) as subgraph.

  Admitted.

  Notation "zxa '|_' inputs '#' vertices" := 
      (induced_subgraph zxa inputs vertices) (at level 40).
  Parameter replace_subgraph : forall {n m o p : nat} 
  (G : ZXG n m) (S : list VertexIdx) 
  (H : ZXG o p), ZXG n m.
  Notation "G '|_{' S '>=>' H '}'" := (replace_subgraph G S H) (at level 40).
  Parameter gen_rewrite : forall {n m o p : nat} 
    (G : ZXG n m) (S : list VertexIdx) (I : list VertexIdx) 
    (H : ZXG o p) (P : H ∝ G |_ I # S), 
      G ∝ G |_{ S >=> H }.

  (* Parameter permute_inputs *)

  (* Google doc of contributions for VyZX - Google Doc, different contributions and 
     different configurations of papers. ViCAR, etc. *)

  Local Open Scope nat.

  (* Stating ZX-Calc rules in the language *)

  Definition bialg_l : ZXG 2 2 := 
    2 <=> +e 3 <=> +e
    <=> 0 +e <=> 1 +e
    0 <=> 2 +e 0 <=> 3 +e
    1 <=> 2 +e 1 <=> 3 +e
    (X 0) @ 3 +v (X 0) @ 2 +v 
    (Z 0) @ 1 +v (Z 0) @ 0 +v ∅.

  Definition bialg_r : ZXG 2 2 :=
    <=> 0 +e <=> 0 +e 1 <=> +e 1 <=> +e
    (X 0) @ 0 +v (Z 0) @ 1 +v ∅ .

  Parameter bialgebra_rule : bialg_l ∝ bialg_r.

  Definition hopf_l : ZXG 1 1 :=
  0 <=> 1 +e 0 <=>1 +e <=> 1 +e 0 <=> +e
  (Z 0) @ 1 +v (X 0) @ 0 +v ∅ .

  Definition hopf_r : ZXG 1 1 :=
  <=> 1 +e 0 <=> +e
  (Z 0) @ 1 +v (X 0) @ 0 +v ∅ .

  Parameter hopf_rule : hopf_l ∝ hopf_r.

  Definition fusion_g_l_fin {m : nat} {α β : R} : ZXG 2 2 :=
    0 <=> +e 1 <=> +e
    <=> 0 +e <=> 1 +e
    0 <=> 1 ^e m +e
    (Z α) @ 0 +v Z β @ 1 +v ∅. 

  Definition fusion_g_r_fin {α β : R} : ZXG 2 2 :=
    0 <=> +e 0 <=> +e
    <=> 0 +e <=> 0 +e
    Z (α + β) @ 0 +v ∅.

  Parameter fusion_g_fin : forall {m : nat} {α β : R},
    @fusion_g_l_fin m α β ∝ @fusion_g_r_fin α β.

  Definition fusion_g_l {n0 n1 o0 o1 m} {α β : R} : ZXG (n0 + (n1 + 0)) (o0 + (o1 + 0)) :=
    0 <=> 1 ^e m +e
    0 <=> ^e o0 +e 1 <=> ^e o1 +e
    <=> 0 ^e n0 +e <=> 1 ^e n1 +e
    (Z β) @ 1 +v (Z α) @ 0 +v ∅ .

  Definition fusion_g_r {n0 n1 o0 o1} {α β : R} : ZXG (n0 + (n1 + 0)) (o0 + (o1 + 0)) :=
    0 <=> ^e o0 +e 1 <=> ^e o1 +e
    <=> 0 ^e n0 +e <=> 1 ^e n1 +e
    (Z (α + β)) @ 0 +v ∅ .

  Parameter fusion_g : forall {n0 n1 o0 o1 m : nat} {α β : R},
    @fusion_g_l n0 n1 o0 o1 m α β ∝ @fusion_g_r n0 n1 o0 o1 α β.

  Local Close Scope nat.

End ZXGraph.
