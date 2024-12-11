Require Import Proportional.
Require Import ZXCore.
Require Import List.
Require Import Nat.

Module Type ZXGModule.

  Parameter ZXG : nat -> nat -> Type.

  Parameter VertexType : Type. (* Allows for flexible types of graph nodes *)
  Parameter proportional : forall {n m : nat}, ZXG n m -> ZXG n m -> Prop.

  Parameter VertexZ : R -> VertexType.
  Parameter VertexX : R -> VertexType.

  Parameter empty_graph : ZXG 0 0. 

  Definition VertexIdx  : Type := nat. (* Indexing vertices with nats *)
  Definition EdgeType  : Type := (VertexIdx * VertexIdx). (* Edges are therefore two indices *)

  Parameter vertices : forall {n m : nat}, 
    ZXG n m -> list (VertexIdx * VertexType).
  Parameter edges    : forall {n m : nat}, 
    ZXG n m -> list (VertexIdx * VertexIdx).

  Parameter add_vertex : forall {n m : nat}, 
    VertexType -> VertexIdx -> ZXG n m -> ZXG n m.
  Parameter add_internal_edge : forall {n m : nat}, 
    ZXG n m -> (VertexIdx * VertexIdx) -> ZXG n m.
  Parameter add_input_edge : forall {n m : nat}, 
    ZXG n m -> VertexIdx -> ZXG (S n) m.
  Parameter add_output_edge : forall {n m : nat}, 
    ZXG n m -> VertexIdx -> ZXG n (S m).

  Parameter compose : forall {n m o : nat}, 
    ZXG n m -> ZXG m o -> ZXG n o.
  Parameter stack   : forall {n m o p : nat}, 
    ZXG n m -> ZXG o p -> ZXG (n + m) (o + p).

End ZXGModule.

Module ZXGraph (GraphInstance :  ZXGModule).

  Include GraphInstance.

  (* Graph Notations *)
  Notation "A '∝' B" := (proportional A B).
  Notation "'Z' α" := (VertexZ α) (at level 20).
  Notation "'X' α" := (VertexX α) (at level 20).
  Notation "∅" := empty_graph.

  (* Low level graph manipulation notations *)
  Notation "vt '@' vidx '+v' G" := 
    (add_vertex vt vidx G) (at level 41, right associativity).
  Notation "idx0 '<=>' idx1 '+e' G" := 
    (add_internal_edge G (idx0, idx1)) (at level 41, right associativity).
  Notation "'<=>' idx '+e' G" := 
    (add_input_edge G idx) (at level 41, right associativity).
  Notation "idx '<=>' '+e' G" := 
    (add_output_edge G idx) (at level 41, right associativity).

  (* Repeated addition of vertices *)
  Fixpoint add_n_input_edges {n m : nat} (zx : ZXG n m) 
                         (idx : VertexIdx) (iter : nat) : 
    ZXG (iter + n) m :=
    match iter with
    | 0 => zx
    | S k => <=> idx +e (add_n_input_edges zx idx k)
    end.
  Notation "'<=>' idx '^e' n '+e' zxg" := 
    (add_n_input_edges zxg idx n) (at level 41, right associativity).

  Fixpoint add_n_output_edges {n m : nat} (zx : ZXG n m) 
                          (idx : VertexIdx) (iter : nat) : 
    ZXG n (iter + m) :=
    match iter with
    | 0 => zx
    | S k => idx <=> +e (add_n_output_edges zx idx k)
    end.
  Notation "idx '<=>' '^e' n '+e' zxg" := 
    (add_n_output_edges zxg idx n) (at level 41, right associativity).

  Fixpoint add_n_internal_edges {n m : nat} (zx : ZXG n m) 
                      (idxl idxr : VertexIdx) (iter : nat) : 
    ZXG n m :=
    match iter with
    | 0 => zx
    | S k => idxl <=> idxr +e (add_n_internal_edges zx idxl idxr k)
    end.
  Notation "idxl '<=>' idxr '^e' n '+e' zxg" := 
    (add_n_internal_edges zxg idxl idxr n) (at level 41, right associativity).

  (* Ways to combine graphs *)
  Notation "A '+' B" := (compose A B).
  Notation "A '⊗' B" := (stack A B).

  (* Access elements of the graph *)

  (* Testing properties of the graph *)
  Definition connected_vertices {n m : nat} (zxg : ZXG n m) 
    (l : VertexIdx) (r : VertexIdx) : bool :=
    let gv := edges zxg in
      (existsb (fun p => 
                orb (andb (fst p =? l) (snd p =? r))
                    (andb (fst p =? r) (snd p =? l)))
                gv).
  Notation "x '<=>?' y 'in' G" := (connected_vertices G x y) (at level 40).

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

  Fixpoint add_list_vertices {n m} (verts : list (VertexIdx * VertexType)) : ZXG n m -> ZXG n m.
  Proof.
    intros zx.
    destruct verts.
    - exact zx.
    - destruct p as [lbl rog].
      exact ((add_list_vertices _ _ verts) (rog @ lbl +v zx)).
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

  Definition isolate_subgraph : forall {n m o p : nat},
    ZXG n m -> list VertexIdx -> list (VertexIdx * VertexType) -> ZXG o p.
  Proof.
    intros n m o p graph inputs internal.
    specialize (vertices graph) as all_vertices.
    specialize (edges graph) as all_edges.
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
    specialize (edges big_graph) as all_edges.
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
