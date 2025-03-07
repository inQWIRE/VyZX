Require Import Proportional.
Require Import ZXCore.
Require Import List.
Require Import Nat.

(*   autosubst                                                    *)
(* C Rework edges to be end - ver ver - ver end - end ver - end   *)
(* C Hadamard Edges                                               *)
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

  (*  *)
  Notation "id @ idx" := (idx%nat, id) (at level 20).
  Notation "id0 '--' id1" := (id0%nat, id1%nat, false) (at level 20).
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
    | (l, _, _) => l
    end.

  Definition right_et (e : Edge) : EdgeType :=
    match e with
    | (_, r, _) => r
    end.

  Definition left_idx (e : Edge) : nat := edgetype_idx (left_et e).
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
    S (list_max (edges_idx graph ++ map fst (vertices graph))).
  
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

  Definition et_eqb (id0 : EdgeType) (id1 : EdgeType) : bool :=
    match (id0, id1) with
    | (Internal x, Internal y)
    | (Boundary x, Boundary y) => x =? y
    | _ => false
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

  Definition pull_vertex_left (vert : Vertex) 
    (target : ZXG) (source : ZXG) : (ZXG * ZXG).
  Proof.
    inversion vert as [idx vt].
    specialize (input_edges_vert source vert) as vert_inputs.
    specialize (output_edges_vert source vert) as vert_outputs.
    specialize (internal_edges_vert source vert) as vert_internal.
    specialize 
      (vert_inputs -el vert_outputs -el vert_internal -el source) 
      as clean_source.
    specialize (max (fresh_idx source) (fresh_idx target)) as fresh_src.
    specialize 
      (remap_edges_input 
        fresh_src 
        (map (move_ident_to_left (Internal idx)) 
              vert_outputs)) as new_passthrough.
    specialize 
      (remap_edges_input 
        fresh_src 
        (map (move_ident_to_left (Internal idx)) 
              vert_internal)) as new_inputs.
    specialize 
      (remap_edges_internal_l
        idx
        (map flip new_passthrough)) as new_outputs_pass.
  exact 
    (new_outputs_pass +el vert +v target, 
     new_inputs +el new_passthrough +el clean_source). 
  Defined.

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
