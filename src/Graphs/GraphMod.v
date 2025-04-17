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

  (* Vertex and Edge Notations *)
  Definition mk_vert (idx : nat) (vertid : VertexType) := pair idx vertid.
  Notation "id @ idx" := (mk_vert idx id) (at level 20).
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

  Definition input (e : Edge) : Prop :=
    left_et e = Boundary (left_idx e).
  Definition output (e : Edge) : Prop :=
    right_et e = Boundary (right_idx e).
  Definition internal (e : Edge) : Prop :=
    left_et e = Internal (left_idx e) /\
    right_et e = Internal (right_idx e).

  Lemma reflect_input : forall (e : Edge),
    reflect (input e) (input? e).
  Proof.
    intros [[[][]]]; simpl.
    1-2: left; unfold input; 
      unfold left_idx; unfold left_et;
      simpl; reflexivity.
    1-2: right; intros contra;
      inversion contra. Qed.

  Lemma reflect_output : forall (e : Edge),
    reflect (output e) (output? e).
  Proof.
    intros [[[][]]]; simpl.
    1, 3: left; unfold input; 
      unfold right_idx; unfold right_et;
      simpl; reflexivity.
    1-2: right; intros contra;
      inversion contra. Qed.

  Lemma reflect_internal : forall (e : Edge),
    reflect (internal e) (internal? e).
  Proof.
    intros [[[][]]]; simpl.
    1-2: right; intros contra; inversion contra;
      unfold left_et in H; simpl; discriminate H.
    - right; intros contra; inversion contra;
      unfold left_et in H0; simpl; discriminate H0.
    - left. unfold internal. split.
      + unfold left_et, left_idx. simpl. reflexivity.
      + unfold right_et, right_idx. simpl. reflexivity. Qed.

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
      (Internal vidx =et? left_et e) || (Internal vidx =et? right_et e).

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
    | ((l, r, b), (l', r', b')) => r =et? l'
    end.

  Definition move_ident_to_left (id : EdgeType) (e : Edge) :=
    match e with
    | (l, r, b) => if r =et? id then (r, l, b) else (l, r, b)
    end.
  Definition move_ident_to_right (id : EdgeType) (e : Edge) :=
    match e with
    | (l, r, b) => if l =et? id then (r, l, b) else (l, r, b)
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

  Definition In_v (v : Vertex) (zx : ZXG) := In v (vertices zx).
  Definition In_e (e : Edge) (zx : ZXG) := In e (edges zx).

  Definition in_v (v : Vertex) (zx : ZXG) : bool :=
    existsb (fun v0 => v =v? v0) (vertices zx).

  Lemma decidable_in_v : forall (v : Vertex) (zx : ZXG), 
    decidable (In_v v zx).
  Proof.
    intros.
    unfold In_v.
    induction (vertices zx).
    - right; intros contra; destruct contra.
    - destruct (dec_eq_vert v a).
      + subst.
        left; left; reflexivity.
      + destruct IHl.
        * left; right; assumption.
        * right; intros contra.
          inversion contra.
          -- subst; contradiction.
          -- apply H0. apply H1. Defined.

  Lemma reflect_in_v : forall (v : Vertex) (zx : ZXG), 
    reflect (In_v v zx) (in_v v zx).
  Proof.
    intros v zx.
    specialize (decidable_in_v v zx); intros.
    unfold In_v, in_v.
    induction (vertices zx).
    - right; intros contra; destruct contra.
    - simpl. destruct (IHl);
      destruct (reflect_vert v a); subst.
      + left; left; reflexivity.
      + left; right; assumption.
      + left; left; reflexivity.
      + right; intros contra; destruct contra; auto. Qed.

  
  Definition edge_connected_to_vertex (e : Edge) (v : Vertex) : Prop :=
    Internal (vertex_idx v) = left_et e \/ 
    Internal (vertex_idx v) = right_et e.

  Notation "e '-c' v" := (edge_connected_to_vertex e v) (at level 20).
  Notation "e '-c?' v" := (vertex_in_edge v e) (at level 20).

  Lemma reflect_edge_connected (e : Edge) (v : Vertex) : 
    reflect (e -c v) (e -c? v).
  Proof.
    unfold edge_connected_to_vertex.
    unfold vertex_in_edge.
    destruct e, v; simpl.
    destruct p; simpl.
    unfold left_idx, right_idx.
    unfold left_et, right_et.
    simpl.
    destruct (reflect_edgetype (Internal i) e), 
             (reflect_edgetype (Internal i) e0); subst.
    - left; left; reflexivity.
    - left; left; reflexivity.
    - left; right; reflexivity.
    - right; intros contra; destruct contra; contradiction. Qed.

  Definition separate_vert_from_graph (v : Vertex) (source : ZXG) : 
    (ZXG * ZXG) :=
    if (in_v v source) 
    then
      let v_inputs := input_edges_vert source v in
      let v_output := output_edges_vert source v in
      let v_intern := internal_edges_vert source v in
      let inis := split (split_edges_from 
                          (fresh_idx source)
                          (v_intern)) in
        (((fst inis) +el v_inputs +el v_output +el v +v ∅), 
          ((snd inis) +el v -v v_inputs 
          -el v_output -el v_intern -el source))
    else
     (∅, source). 

  Definition isolate_vertex (vert : Vertex) (source : ZXG) : ZXG :=
    fst (separate_vert_from_graph vert source).

  Definition remove_vertex_and_edges (vert : Vertex) (source : ZXG) : ZXG :=
    snd (separate_vert_from_graph vert source).

  Definition composable (e0 e1 : Edge) : Prop :=
    right_et e0 = left_et e1.

  Definition composableb (e0 e1 : Edge) : bool :=
    right_et e0 =et? left_et e1.
  Notation "e0 'composable?' e1" := (composableb e0 e1) (at level 40).

  Lemma reflect_composable : forall (e0 e1 : Edge),
    reflect (composable e0 e1) (e0 composable? e1).
  Proof.
    intros.
    unfold composable.
    unfold composableb.
    apply (reflect_edgetype (right_et e0) (left_et e1)). Qed.

  Definition uniquely_composable_in (e0 e1 : Edge) (el : list Edge) := 
    forall e2, In e2 el -> composable e0 e2 -> e2 = e1.

  Definition compose_edge (e0 e1 : Edge) : Edge :=
    match (e0, e1) with
    | ((l, _, bv), (_, r, bv')) => (l, r, if bv then negb bv' else bv')
    end.

  Fixpoint compose_edge_to_list_rec (e : Edge) (el  : list Edge) : Edge * list Edge :=
    match el  with
    | [] => (e, [])
    | e'::es => if e composable? e'
                then ((compose_edge e e'), es)
                else match (compose_edge_to_list_rec e es) with
                     | (edge, remel) => (edge, e' :: remel)
                     end
    end.

  Definition compose_edge_to_list_edge (e : Edge) (el : list Edge) := 
    fst (compose_edge_to_list_rec e el).

  Definition compose_edge_to_list_edge_list (e : Edge) (el : list Edge) :=
    snd (compose_edge_to_list_rec e el).

  Definition compose_edge_to_list (e : Edge) (el : list Edge) :=
    compose_edge_to_list_edge e el :: compose_edge_to_list_edge_list e el.

  Lemma compose_edge_to_list_in : forall (e0 e1 : Edge) (el : list Edge),
    In e1 el -> composable e0 e1 -> 
    uniquely_composable_in e0 e1 el ->
    In (compose_edge e0 e1) (compose_edge_to_list e0 el).
  Proof.
    intros.
    unfold uniquely_composable_in in H1.
    induction el.
    - inversion H.
    - simpl.
      unfold compose_edge_to_list in IHel;
      unfold compose_edge_to_list_edge_list in *;
      unfold compose_edge_to_list_edge in *; simpl.
      destruct (reflect_composable e0 a).
      + rewrite (H1 a); auto; left; reflexivity.
      + destruct H; subst.
        * contradiction.
        * right.
          destruct (compose_edge_to_list_rec e0 el) eqn:E.
          simpl in IHel.
          simpl.
          destruct IHel.
          -- auto.
          -- intros. 
             apply H1.
             ++ right; assumption.
             ++ assumption. 
          -- subst.
             right. 
  Admitted.

  Lemma compose_edge_to_list_eq : forall (e0 e1 : Edge) (el : list Edge),
    In e1 el -> composable e0 e1 -> 
    uniquely_composable_in e0 e1 el ->
    (compose_edge e0 e1) = (compose_edge_to_list_edge e0 el).

  Definition no_composable_edges (e : Edge) (el : list Edge) :=
    forall e1, In e1 el -> ~ composable e e1.

  Lemma compose_edge_to_list_out : forall (e0 : Edge) (el : list Edge),
    no_composable_edges e0 el ->
    In e0 (compose_edge_to_list e0 el).
  Proof.
    intros.
    unfold no_composable_edges in H.
    induction el.
    - left; reflexivity.
    - simpl.
      destruct (reflect_composable e0 a).
      + contradict c.
        apply H.
        left; reflexivity.
      + right. Admitted.

  Fixpoint compose_edgelist_to_edgelist (el0 el1 : list Edge) : list Edge :=
    match el0 with
    | [] => el1
    | e'::es => match compose_edge_to_list_rec e' el1 with
                | (e'_composed, el1') => e'_composed :: compose_edgelist_to_edgelist es el1'
                end
    end.

  Lemma composable_edgelist_to_edgelist : 
    forall (e0 e1 : Edge) (el0 el1 : list Edge),
      In e0 el0 -> In e1 el1 -> composable e0 e1 ->
      uniquely_composable_in e0 e1 el1 ->
      In (compose_edge e0 e1) (compose_edgelist_to_edgelist el0 el1).
  Proof.
    intros e0 e1.
    induction el0; intros.
    - inversion H.
    - simpl.
      apply IHel0.
      + inversion H.
        * admit.
  Admitted.

  Definition shift (zx : ZXG) (degree : nat) : ZXG := zx.

  Definition compose (zx0 zx1 : ZXG) : ZXG := 
    (compose_edgelist_to_edgelist (edges zx0) (edges zx1))
    +el vertices zx0 +vl vertices zx1 +vl ∅.

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

  Lemma empty_vert_empty_edge_equiv_empty : forall (zx : ZXG),
    vertices zx = [] -> edges zx = [] -> zx ≡g ∅.
  Proof.
    intros.
    unfold equiv_graphs.
    intros.
    split; split; intros.
    - unfold In_v in H1.
      rewrite H in H1.
      contradiction H1.
    - unfold In_v in H1. 
      rewrite vertices_empty in H1.
      contradiction H1.
    - unfold In_e in H1.
      rewrite H0 in H1.
      contradiction H1.
    - unfold In_e in H1.
      rewrite edges_empty in H1.
      contradiction H1. Qed.

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

  Lemma In_v_add_v_later : forall (v l : Vertex) (zx : ZXG),
    v <> l ->
    In_v v (l +v zx) <-> In_v v zx.
  Proof.
    split; intros.
    - unfold In_v in *.
      rewrite vertices_add_v_comm in H0.
      induction (vertices zx).
      + inversion H0; subst; contradiction.
      + inversion H0.
        * subst. right. apply IHl0. left; reflexivity.
        * apply H1.
    - unfold In_v in *.
      rewrite vertices_add_v_comm.
      induction (vertices zx).
      + destruct H0.
      + right; apply H0. Qed.

  Lemma In_e_add_e_here : forall (e : Edge) (zx : ZXG),
    In_e e (e +e zx).
  Proof.
    intros.
    unfold In_e.
    rewrite edges_add_e_comm.
    constructor; reflexivity. Qed.

  Lemma In_e_add_e_later : forall (e l : Edge) (zx : ZXG),
    e <> l ->
    In_e e (l +e zx) <-> In_e e zx.
  Proof.
    split; intros.
    - unfold In_e in *.
      rewrite edges_add_e_comm in H0.
      induction (edges zx).
      + inversion H0; subst; contradiction.
      + inversion H0.
        * subst. right. apply IHl0. left; reflexivity.
        * apply H1.
    - unfold In_e in *.
      rewrite edges_add_e_comm.
      induction (edges zx).
      + destruct H0.
      + right; apply H0. Qed.

  Lemma In_v_add_v_list_here : forall (v : Vertex) (vl : list Vertex) (zx : ZXG),
    ~ In_v v zx ->
    In_v v (vl +vl zx) <-> In v vl.
  Proof.
    induction vl; intros.
    - simpl; split.
      + intros; apply H; assumption.
      + intros; contradict H0.
    - simpl.
      destruct (reflect_vert a v); subst.
      + split; intros.
        * left; reflexivity.
        * apply In_v_add_v_here.
      + rewrite In_v_add_v_later; [|auto].
        rewrite IHvl; auto.
        split; intros.
        * right; auto.
        * destruct H0; try auto; try contradiction. Qed.

  Lemma In_v_add_v_list_later : forall (v : Vertex) (vl : list Vertex) (zx : ZXG),
    ~ In v vl ->
    In_v v (vl +vl zx) <-> In_v v zx.
  Proof.
    induction vl; intros.
    - split; intros; assumption.
    - simpl.
      rewrite In_v_add_v_later.
      apply IHvl.
      intros contra.
      simpl in H.
      contradict H.
      right; apply contra.
      contradict H; subst.
      left; reflexivity. Qed.

  Lemma In_e_add_e_list_here : forall (e : Edge) (el : list Edge) (zx : ZXG),
    ~ In_e e zx ->
    In_e e (el +el zx) <-> In e el.
  Proof.
    induction el; intros.
    - simpl; split.
      + intros; apply H; assumption.
      + intros; contradict H0.
    - simpl.
      destruct (reflect_edge a e); subst.
      + split; intros.
        * left; reflexivity.
        * apply In_e_add_e_here.
      + rewrite In_e_add_e_later; [|auto].
        rewrite IHel; auto.
        split; intros.
        * right; auto.
        * destruct H0; try auto; try contradiction. Qed.

  Lemma In_e_add_e_list_later : forall (e : Edge) (el : list Edge) (zx : ZXG),
    ~ In e el ->
    In_e e (el +el zx) <-> In_e e zx.
  Proof.
    induction el; intros.
    - split; intros; assumption.
    - simpl.
      rewrite In_e_add_e_later.
      apply IHel.
      intros contra.
      simpl in H.
      contradict H.
      right; apply contra.
      contradict H; subst.
      left; reflexivity. Qed.

  Lemma In_v_add_e : forall (v : Vertex) (e : Edge) (zx : ZXG),
    In_v v zx <-> In_v v (e +e zx).
  Proof.
    intros.
    unfold In_v.
    rewrite vertices_add_e_comm.
    reflexivity. Qed.
    
  Lemma In_v_add_e_list : forall (v : Vertex) (el : list Edge) (zx : ZXG),
    In_v v (el +el zx) <-> In_v v zx .
  Proof.
    induction el; intros; [reflexivity|].
    simpl. rewrite <- In_v_add_e. apply IHel. Qed.

  Lemma In_e_add_v : forall (v : Vertex) (e : Edge) (zx : ZXG),
    In_e e zx <-> In_e e (v +v zx).
  Proof.
    intros.
    unfold In_e.
    rewrite edges_add_v_comm.
    reflexivity. Qed.
    
  Lemma In_e_add_v_list : forall (e : Edge) (vl : list Vertex) (zx : ZXG),
    In_e e (vl +vl zx) <-> In_e e zx .
  Proof.
    induction vl; intros; [reflexivity|].
    simpl. rewrite <- In_e_add_v. apply IHvl. Qed.

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

  Lemma compose_empty_l : forall (zx : ZXG),
   ∅ ↔ zx ≡g zx.
  Proof.
    intros zx v e; split.
    - unfold compose.
      rewrite edges_empty; simpl.
      rewrite In_v_add_e_list.
      rewrite vertices_empty.
      simpl.
      rewrite In_v_add_v_list_here.
      + reflexivity.
      + intros contra.
        unfold In_v in contra.
        rewrite vertices_empty in contra.
        contradiction.
    - unfold compose.
      rewrite edges_empty; simpl.
      rewrite In_e_add_e_list_here.
      + reflexivity.
      + rewrite 2 In_e_add_v_list.
        apply e_not_in_empty. Qed.

  Lemma compose_edgelist_to_edgelist_empty_r : forall (e : Edge) (el : list Edge),
    In e (compose_edgelist_to_edgelist el []) <-> In e el.
  Proof.
    intros e el.
    generalize dependent e.
    induction el.
    - reflexivity.
    - simpl.
  Admitted.

  Lemma compose_empty_r : forall (zx : ZXG),
   zx ↔ ∅ ≡g zx.
  Proof.
    intros zx v e; split.
    - unfold compose.
      rewrite edges_empty; simpl.
      rewrite In_v_add_e_list.
      rewrite vertices_empty.
      simpl.
      rewrite In_v_add_v_list_here.
      + reflexivity.
      + intros contra.
        unfold In_v in contra.
        rewrite vertices_empty in contra.
        contradiction.
    - unfold compose.
      rewrite edges_empty; simpl.
      rewrite In_e_add_e_list_here.
  Admitted.

  Lemma vertices_isolate_vertex : forall (v : Vertex) (zx : ZXG), 
    In_v v zx -> vertices (isolate_vertex v zx) = [v].
  Proof.
    intros.
    unfold isolate_vertex.
    unfold separate_vert_from_graph.
    destruct (reflect_in_v v zx); simpl; graphalg_simpl; try reflexivity.
    contradiction. Qed.

  Lemma vertices_isolate_nothing : forall (v : Vertex) (zx : ZXG), 
    ~ In_v v zx -> vertices (isolate_vertex v zx) = [].
  Proof.
    intros.
    unfold isolate_vertex.
    unfold separate_vert_from_graph.
    destruct (reflect_in_v v zx); simpl; graphalg_simpl; try reflexivity.
    contradiction. Qed.

  Lemma vertices_isolate_nothing_edges : forall (v : Vertex) (zx : ZXG), 
    ~ In_v v zx -> edges (isolate_vertex v zx) = [].
  Proof.
    intros.
    unfold isolate_vertex.
    unfold separate_vert_from_graph.
    destruct (reflect_in_v v zx); simpl; graphalg_simpl; try reflexivity.
    contradiction. Qed.

  Lemma v_in_isolate_implies_eq : forall (v0 v1 : Vertex) (zx : ZXG),
    In_v v0 (isolate_vertex v1 zx) -> v0 = v1.
  Proof.
    intros.
    destruct (decidable_in_v v1 zx); simpl.
    - unfold In_v in H.
      rewrite (vertices_isolate_vertex v1 zx H0) in H.
      inversion H; auto.
      contradiction H1.
    - unfold In_v in H.
      rewrite (vertices_isolate_nothing v1 zx H0) in H.
      contradiction H. Qed.

  Lemma e_in_isolate_implies_connected : 
    forall (v : Vertex) (e : Edge) (zx : ZXG),
      In_e e (isolate_vertex v zx) <-> e -c v.
  Proof.
    intros v e zx.
    unfold isolate_vertex.
    unfold separate_vert_from_graph.
    destruct (reflect_in_v v zx); simpl.
  Admitted.

  Lemma v_in_isolate : forall (v : Vertex) (zx : ZXG),
    In_v v zx -> In_v v (isolate_vertex v zx).
  Proof.
    intros.
    unfold In_v.
    rewrite (vertices_isolate_vertex v zx H).
    left; reflexivity. Qed.

  Lemma compose_in_v_l : forall (v : Vertex) (zx0 zx1 : ZXG),
    ~ In_v v zx1 ->
    In_v v zx0 <-> In_v v (zx0 ↔ zx1).
  Proof.
    intros.
    unfold In_v in H.
    unfold compose.
    rewrite In_v_add_e_list.
    rewrite In_v_add_v_list_here.
    reflexivity.
    unfold In_v.
    rewrite vertices_add_vl_comm.
    rewrite vertices_empty.
    rewrite app_nil_r.
    assumption.
    Qed.

  Lemma compose_in_v_r : forall (v : Vertex) (zx0 zx1 : ZXG),
    ~ In_v v zx0 ->
    In_v v zx1 <-> In_v v (zx0 ↔ zx1).
  Proof.
    intros.
    unfold In_v in H.
    unfold compose.
    rewrite In_v_add_e_list.
    rewrite In_v_add_v_list_later; [|assumption].
    unfold In_v.
    rewrite vertices_add_vl_comm.
    rewrite vertices_empty.
    rewrite app_nil_r.
    reflexivity. Qed.

  Lemma In_v_compose_In_v : forall (v : Vertex) (zx0 zx1 : ZXG),
    In_v v (zx0 ↔ zx1) <-> In_v v zx0 \/ In_v v zx1.
  Proof.
    intros.
    unfold In_v.
    unfold compose.
    rewrite vertices_add_el_comm.
    rewrite 2 vertices_add_vl_comm.
    rewrite vertices_empty.
    rewrite app_nil_r.
    rewrite <- in_app_iff.
    reflexivity. Qed.

  Lemma In_v_isolate_In_v_source : forall (v : Vertex) (source : ZXG),
    In_v v (isolate_vertex v source) <-> In_v v source.
  Proof.
    intros v source.
    unfold isolate_vertex.
    unfold separate_vert_from_graph.
    destruct (reflect_in_v v source); intros.
    - simpl.
      rewrite 3 In_v_add_e_list.
      split; intros; auto.
      apply In_v_add_v_here.
    - simpl.
      split; intros.
      + unfold In_v in H.
        rewrite vertices_empty in H.
        destruct H.
      + contradict n; assumption. Qed.

  Lemma sumdec_vert : forall (v0 v1 : Vertex),
    { v0 = v1 } + { v0 <> v1 }.
  Proof.
    intros.
    destruct (reflect_vert v0 v1); auto. Defined.

  Parameter vertices_sub_v_comm : forall (v : Vertex) (zx : ZXG),
    vertices (v -v zx) = remove sumdec_vert v (vertices zx).

  Parameter vertices_sub_e_comm : forall (e : Edge) (zx : ZXG),
    vertices (e -e zx) = (vertices zx).

  Lemma In_v_rem_v_comm : forall (v0 v1 : Vertex) (zx : ZXG),
    v0 <> v1 -> In_v v0 zx <-> In_v v0 (v1 -v zx).
  Proof.
    intros v0 v1 zx Hneq.
    unfold In_v in *.
    rewrite vertices_sub_v_comm.
    induction (vertices zx).
    - split; intros; apply H.
    - split; intros.
      + simpl.
        destruct (sumdec_vert v1 a); subst.
        * rewrite <- IHl.
          inversion H; subst; try contradiction.
          assumption.
        * inversion H; subst; [(left; reflexivity)|].
          right.
          rewrite <- IHl.
          assumption.
      + simpl in H.
        destruct (sumdec_vert v1 a) eqn:E; subst.
        * right.
          rewrite IHl.
          assumption.
        * inversion H; subst; [left; reflexivity|].
          right.
          rewrite IHl.
          apply H0. Qed.

  Lemma In_v_remove_v_later : forall (v0 v1 : Vertex) (zx : ZXG),
    v0 <> v1 ->
    In_v v0 (v1 -v zx) <-> In_v v0 zx.
  Proof.
    intros.
    unfold In_v.
    rewrite vertices_sub_v_comm.
    induction (vertices zx).
    - reflexivity.
    - simpl. 
      destruct (sumdec_vert v1 a); subst.
      + rewrite IHl.
        split; intros; auto.
        destruct H0; auto; subst; contradiction.
      + split; intros.
        * inversion H0; subst.
          -- left; reflexivity.
          -- right. rewrite <- IHl. apply H1.
        * destruct H0; subst.
          -- left; reflexivity.
          -- right. rewrite IHl. assumption. Qed.

  Lemma In_v_remove_e : forall (v : Vertex) (e : Edge) (zx : ZXG),
    In_v v (e -e zx) <-> In_v v zx.
  Proof.
    intros.
    unfold In_v.
    rewrite vertices_sub_e_comm.
    reflexivity. Qed.

  Lemma In_v_remove_e_list : forall (v : Vertex) (el : list Edge) (zx : ZXG),
    In_v v (el -el zx) <-> In_v v zx.
  Proof.
    induction el; intros.
    - reflexivity.
    - simpl.
      rewrite In_v_remove_e.
      rewrite IHel; reflexivity. Qed.

  Lemma In_v_remove_In_v_source : forall (v0 v1 : Vertex) (source : ZXG),
    v0 <> v1 ->
    In_v v0 (remove_vertex_and_edges v1 source) <-> In_v v0 source.
  Proof.
    intros v0 v1 source.
    unfold remove_vertex_and_edges.
    unfold separate_vert_from_graph.
    destruct (reflect_in_v v1 source); intros.
    - simpl.
      rewrite In_v_add_e_list.
      rewrite In_v_remove_v_later; [|assumption].
      rewrite 3 In_v_remove_e_list.
      reflexivity.
    - simpl; reflexivity. Qed.

  Lemma In_v_remove_v : forall (v : Vertex) (zx : ZXG),
    ~ In_v v (v -v zx).
  Proof.
    intros.
    unfold In_v.
    rewrite vertices_sub_v_comm.
    induction (vertices zx).
    - auto.
    - simpl.
      destruct (sumdec_vert v a); subst; auto.
      intros contra; destruct contra; subst; auto. Qed.

  Lemma In_v_remove_no_v : forall (v : Vertex) (zx : ZXG),
    ~ In_v v (remove_vertex_and_edges v zx).
  Proof.
    intros v zx.
    unfold remove_vertex_and_edges.
    unfold separate_vert_from_graph.
    destruct (reflect_in_v v zx); simpl.
    - rewrite In_v_add_e_list.
      apply In_v_remove_v. 
    - assumption. Qed.

  Lemma In_e_compose_In_e : forall (e : Edge) (zx0 zx1 : ZXG),
    In_e e (zx0 ↔ zx1) <-> 
      In_e e (zx0) \/ In_e e (zx1) \/ 
      exists (idx : nat) (b : bool), 
        In_e (left_et e, Boundary idx, b) zx0 /\
        In_e (Boundary idx, right_et e, b) zx1.
  Proof.
    intros.
    unfold compose.
    split; intros.
    - unfold In_e in H.
      autorewrite with graphalg in H.
      rewrite app_nil_r in H.
      remember (edges zx0) as ezx0.
      remember (edges zx1) as ezx1.
      generalize dependent zx1.
      induction ezx0; induction ezx1; intros.
      + inversion H.
      + 
  Admitted.

  Lemma test : forall (v : Vertex) (e : Edge) (zx : ZXG),
    e -c v -> output e ->
    In e (output_edges_vert zx v) <-> In_e e zx.
    Proof.
      intros v e zx.
      unfold output_edges_vert.
    Admitted.

  Lemma connected_in_isolate_iff : 
    forall (v : Vertex) (e : Edge) (zx : ZXG),
      e -c v -> In_v v zx ->
      In_e e (isolate_vertex v zx) <-> In_e e zx.
  Proof.
    intros.
    unfold isolate_vertex.
    unfold separate_vert_from_graph.
    destruct (reflect_in_v v zx); simpl; subst; [|contradiction].
    - destruct e, p.
      inversion H. unfold left_et in H0; simpl in H0.
      + destruct e0; simpl.
        * rewrite 2 In_e_add_e_list_later.
          unfold left_et in H1.
          simpl in H1.
          rewrite In_e_add_e_list_here.
  Admitted.

  Lemma separate_maintains_graph : 
    forall (vert : Vertex) (source : ZXG),
      isolate_vertex vert source ↔ 
      remove_vertex_and_edges vert source ≡g source.
  Proof. 
    intros.
    intros v e.
    split.
    - rewrite In_v_compose_In_v.
      destruct (reflect_vert v vert); subst.
      + rewrite In_v_isolate_In_v_source.
        split; intros; auto.
        destruct H; auto.
        exfalso.
        apply (In_v_remove_no_v vert source).
        assumption.
      + rewrite In_v_remove_In_v_source; [|auto].
        split; intros; auto.
        destruct H; auto.
        apply v_in_isolate_implies_eq in H; subst.
        contradiction n; reflexivity.
    - rewrite In_e_compose_In_e.
      destruct (reflect_edge_connected e v).
      + 
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

  Definition bo : nat -> EdgeType := Boundary.
  Definition it : nat -> EdgeType := Internal.

  Open Scope nat.

  Definition bialg_l : ZXG := 
    it 2 -- bo 2 +e it 3 -- bo 3 +e
    bo 0 -- it 0 +e bo 1 -- it 1 +e
    it 0 -- it 2 +e it 0 -- it 3 +e
    it 1 -- it 2 +e it 1 -- it 3 +e
    (X 0) @ 3 +v (X 0) @ 2 +v 
    (Z 0) @ 1 +v (Z 0) @ 0 +v ∅.

  Definition bialg_r : ZXG :=
     bo 0 -- it 0 +e bo 1 -- it 0 +e 
     it 1 -- bo 0 +e it 1 -- bo 1 +e
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
