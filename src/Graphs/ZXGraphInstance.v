Require Import ZXGraph.



Module Type ZXGModule.
  Import Decidable.

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


  Definition Idx    : Type := nat. 

  (* Different types of edges we may see *)
  Inductive EdgeType : Type :=
    | Boundary : Idx -> EdgeType
    | Internal : Idx -> EdgeType.
  
  (* Notation Boundary n := (@inl nat nat n).
  Notation Internal n := (@inr nat nat n). *)
  
  Definition Edge : Type := (EdgeType * EdgeType * bool).
  

(* Typed aliases for indexing internal graphs *)
  Definition Vertex : Type := (Idx * VertexType).


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


Module ZXGInstance : ZXGModule.


Definition Idx    : Type := nat. 

(* Different types of edges we may see *)
Inductive EdgeType : Type :=
  | Boundary : Idx -> EdgeType
  | Internal : Idx -> EdgeType.

(* Notation Boundary n := (@inl nat nat n).
Notation Internal n := (@inr nat nat n). *)

Definition Edge : Type := (EdgeType * EdgeType * bool).




Definition ZXG := ZX_map_graph.

Definition SemanticType :=
  {nm : nat * nat & ZX_el_graph nm.1 nm.2}.

Definition semantic (G : ZX_map_graph) : SemanticType :=
  existT (G.(mg_insize), G.(mg_outsize)) (ZX_el_graph_of_map_graph G).

Definition proportional (G H : ZX_map_graph) :=
  WF_ZX_map_graph G ∧
  WF_ZX_map_graph H ∧
  exists (Hin : G.(mg_insize) = H.(mg_insize)) 
    (Hout : G.(mg_outsize) = H.(mg_outsize)),
  ZXvert_of_el_graph (ZX_el_graph_of_map_graph G) ∝
  cast _ _ (f_equal2 _ Hin Hout) eq_refl
    (ZXvert_of_el_graph (ZX_el_graph_of_map_graph H)).

Definition VertexType : Type := bool * R.

Definition VertexZ (a : R) := (false, a).
Definition VertexX (a : R) := (true, a).

Global Instance R_eq_dec : EqDecision R :=
  Req_dec_T.

Definition VT_eq_dec : EqDecision VertexType := _.

Definition decVT (vt0 vt1 : VertexType) : Decidable.decidable (vt0 = vt1) :=
  match (decide _) with | left H => or_introl H | right H => or_intror H end.

Definition eqb_vt (vt0 vt1 : VertexType) := bool_decide (vt0 = vt1).

Definition reflect_vt (vt0 vt1 : VertexType) : 
  reflect (vt0 = vt1) (eqb_vt vt0 vt1) := bool_decide_reflect _.

Definition empty_graph : ZX_map_graph := {|
  mg_verts := ∅;
  mg_inputs := ∅;
  mg_vert_outputs := ∅;
  mg_vert_edges := ∅;
|}.

Definition Vertex : Type := (Idx * VertexType).

Definition vertices (G : ZX_map_graph) : list Vertex :=
  map_to_list G.(mg_verts).


Definition edges (G : ZX_map_graph) : list Edge :=
  map (fun ab => (Internal ab.1, Internal ab.2, false))
    (elements G.(mg_vert_edges)) ++
  map (fun iv => (Boundary iv.1, Internal iv.2, false))
    (map_to_list G.(mg_vert_inputs)) ++
  map (fun ov => (Internal ov.2, Boundary ov.1, false))
    (map_to_list G.(mg_vert_outputs)) ++
  map (fun io => (Boundary io.1, Boundary io.2, false))
    (map_to_list G.(mg_boundary_inputs)).

Definition add_vertex (idx_v : Vertex) (G : ZX_map_graph) : ZX_map_graph :=
  {|
    mg_verts := <[idx_v.1 := idx_v.2]> G.(mg_verts);
    mg_inputs := G.(mg_inputs);
    mg_vert_outputs := G.(mg_vert_outputs);
    mg_vert_edges := G.(mg_vert_edges);
  |}.

Definition add_edge (e : Edge) (G : ZX_map_graph) : ZX_map_graph :=
  match e with 
  | (Internal v, Internal u, _) =>
    {|
      mg_verts := G.(mg_verts);
      mg_inputs := G.(mg_inputs);
      mg_vert_outputs := G.(mg_vert_outputs);
      mg_vert_edges := {[+ (v, u) +]} ⊎ G.(mg_vert_edges);
    |}
  | (Boundary i, Internal v, _) =>
    {|
      mg_verts := G.(mg_verts);
      mg_inputs := <[i := inl v]> G.(mg_inputs);
      mg_vert_outputs := G.(mg_vert_outputs);
      mg_vert_edges := G.(mg_vert_edges);
    |}
  | (Boundary i, Boundary o, _) =>
    {|
      mg_verts := G.(mg_verts);
      mg_inputs := <[i := inr o]> G.(mg_inputs);
      mg_vert_outputs := G.(mg_vert_outputs);
      mg_vert_edges := G.(mg_vert_edges);
    |}
  | (Internal v, Boundary o, _) =>
    {|
      mg_verts := G.(mg_verts);
      mg_inputs := G.(mg_inputs);
      mg_vert_outputs := <[o := v]> G.(mg_vert_outputs);
      mg_vert_edges := G.(mg_vert_edges);
    |}
  end.


Definition delete_vertex (idx : Idx) (G : ZX_map_graph) : ZX_map_graph :=
  {|
    mg_verts := delete idx G.(mg_verts);
    mg_inputs := G.(mg_inputs);
    mg_vert_outputs := G.(mg_vert_outputs);
    mg_vert_edges := G.(mg_vert_edges);
  |}.

Definition remove_vertex (idx_v : Vertex) (G : ZX_map_graph) : ZX_map_graph :=
  if decide (G.(mg_verts) !! idx_v.1 = Some idx_v.2) then
    delete_vertex idx_v.1 G else G.


Definition remove_edge (e : Edge) (G : ZX_map_graph) : ZX_map_graph :=
  match e with 
  | (Internal v, Internal u, _) =>
    {|
      mg_verts := G.(mg_verts);
      mg_inputs := G.(mg_inputs);
      mg_vert_outputs := G.(mg_vert_outputs);
      mg_vert_edges := G.(mg_vert_edges) ∖ {[+ (v, u) +]};
    |}
  | (Boundary i, Internal v, _) =>
    {|
      mg_verts := G.(mg_verts);
      mg_inputs := if decide (G.(mg_inputs) !! i = Some (inl v))
        then delete i G.(mg_inputs) 
        else G.(mg_inputs);
      mg_vert_outputs := G.(mg_vert_outputs);
      mg_vert_edges := G.(mg_vert_edges);
    |}
  | (Boundary i, Boundary o, _) =>
    {|
      mg_verts := G.(mg_verts);
      mg_inputs := if decide (G.(mg_inputs) !! i = Some (inr o))
        then delete i G.(mg_inputs) 
        else G.(mg_inputs);
      mg_vert_outputs := G.(mg_vert_outputs);
      mg_vert_edges := G.(mg_vert_edges);
    |}
  | (Internal v, Boundary o, _) =>
    {|
      mg_verts := G.(mg_verts);
      mg_inputs := G.(mg_inputs);
      mg_vert_outputs := if decide ((G.(mg_vert_outputs) !! o) = Some v) 
        then delete o G.(mg_vert_outputs)
        else G.(mg_vert_outputs);
      mg_vert_edges := G.(mg_vert_edges);
    |}
  end.

Lemma ZX_map_graph_eq (G H : ZX_map_graph) : 
  G.(mg_verts) = H.(mg_verts) -> 
  G.(mg_inputs) = H.(mg_inputs) ->
  G.(mg_vert_outputs) = H.(mg_vert_outputs) ->
  G.(mg_vert_edges) = H.(mg_vert_edges) ->
  G = H.
Proof.
  by destruct G, H; simpl; intros; f_equal.
Qed.

(* FIXME: This is a false statement!!!!! *)
Lemma add_vertex_commutes (G : ZX_map_graph) (v1 v0 : Vertex) :
  add_vertex v0 (add_vertex v1 G) = add_vertex v1 (add_vertex v0 G).
Proof.
  destruct (decide (v0.1 = v1.1 ∧ v0.2 ≠ v1.2)) as [Hbad | Hne].
  - (* FIXME: This case is false!! *)
    admit.
  - apply ZX_map_graph_eq; [|done..].
    simpl.
    destruct (decide (v0.1 = v1.1)) as [Heq | Hne'].
    + rewrite Heq in *. 
      destruct (decide (v0.2 = v1.2)) as [-> | Hfalse]; [|by firstorder].
      reflexivity.
    + by apply insert_commute.
Admitted.

(* FIXME: This is a false statement!!!!! *)
Lemma remove_add_vertex (G : ZX_map_graph) (v : Vertex) :
  remove_vertex v (add_vertex v G) = G.
Proof.
  destruct (decide (v.1 ∈ dom G.(mg_verts))) as [Hbad | Hne].
  - (* FIXME: This case is false!! *)
    admit.
  - apply ZX_map_graph_eq; [|unfold remove_vertex; simpl; by case_decide..].
    unfold remove_vertex.
    simpl.
    rewrite lookup_insert.
    rewrite if_True by done.
    simpl.
    rewrite delete_insert by by apply not_elem_of_dom in Hne.
    reflexivity.
Admitted.



(* FIXME: This is a false statement!!!!! *)
Lemma remove_add_edge (G : ZX_map_graph) (e : Edge) :
  remove_edge e (add_edge e G) = G.
Proof.
  destruct e as (([i|v], [o|w]), b); simpl;
  apply ZX_map_graph_eq; simpl; try reflexivity.
  - assert (Hi : i ∉ dom G.(mg_inputs)) by admit.
    rewrite lookup_insert.
    rewrite if_True by done.
    rewrite delete_insert by by apply not_elem_of_dom in Hi.
    done.
  - assert (Hi : i ∉ dom G.(mg_inputs)) by admit.
    rewrite lookup_insert.
    rewrite if_True by done.
    rewrite delete_insert by by apply not_elem_of_dom in Hi.
    done.
  - assert (Ho : o ∉ dom G.(mg_vert_outputs)) by admit.
    rewrite lookup_insert.
    rewrite if_True by done.
    rewrite delete_insert by by apply not_elem_of_dom in Ho.
    done.
  - multiset_solver.
Admitted.


End ZXGInstance.










(* Definition set_eq_dec `{FinSet A SA}  *)

(* Definition minverses_dec `{FinMapDom A MA SA} `{FinMapDom B MB SB}
  `{!Elements A SA} `{!FinSet A SA} `{!Elements B SB} `{!FinSet B SB}
  (f : MA B) (g : MB A) : Decision (minverses f g).

  simple apply (fun hdec => dec_of_iff hdec (@iff_sym _ _ $ minverses_restrict f g)).
  apply and_dec.
  Search FinSet headconcl:(RelDecision).
  apply _.
  apply _. *)




(* TODO: Connect with this definition: *)
(* Definition ZXvert_of_WF_map_graph (G : ZX_map_graph) (HG : WF_ZX_map_graph G) : 
  ZXvert G.(mg_insize) G.(mg_outsize) :=
  G.(mg_spider_stack) ⟷ cast _ _ mg_size_pf eq_refl G.(mg_io_diag). *)


(*



Lemma mg_WF_input_edges `{FinSet nat SA}:
  edgeset_dom G.(mg_input_edges) ⊆@{SA}
    seq_set 0 (G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize)).
Proof.
  intros x.
  rewrite elem_of_seq_set_0.
  intros ((i,v) & 
    (i' & v' & Hi' & (Hi & Hv')%pair_eq)%elem_of_map_to_set 
    & [-> | ->])%elem_of_edgeset_dom.
  - simpl.
    apply elem_of_dom_2 in Hi' as Hi'dom.
    rewrite lookup_total_alt in Hi.
    apply dom_omap_subseteq in Hi'dom as Hi'dom'.
    destruct (G.(mg_input_idx) !! i') as [Gi|] eqn:e.
    2: {
      enough (Helemdom : i' ∈ dom G.(mg_input_idx)) by 
        (by rewrite elem_of_dom, e, is_Some_alt in Helemdom).
      unfold mg_input_idx.
      by rewrite dom_natset_idx.
    }
    simpl in Hi.
    pose proof (map_img_natset_idx (SA:=natset) G.(mg_input_set)) as Himg.
    unfold mg_input_set at 2 in Himg.
    rewrite size_dom in Himg.
    fold G.(mg_insize) in Himg.
    enough (Hkey : Gi ∈@{natset} seq_set 0 G.(mg_insize)) by 
      (rewrite elem_of_seq_set_0 in Hkey; lia).
    rewrite <- Himg.
    rewrite elem_of_map_img.
    eauto.
  - simpl.
    enough (Hv : v ∈@{natset} seq_set 0 G.(mg_numspi)) by
      (rewrite elem_of_seq_set in Hv; lia).
    rewrite <- Hv'.
    pose proof (map_img_natset_idx (SA:=natset) G.(mg_vert_set)) as Himg.
    unfold mg_vert_set at 2 in Himg.
    rewrite size_dom in Himg.
    fold G.(mg_numspi) in Himg.
    rewrite <- Himg.
    rewrite elem_of_map_img.
    eexists.
    apply lookup_lookup_total_dom.
    unfold mg_vert_idx.
    rewrite dom_natset_idx.
    apply mg_WF_vert_inputs.
    rewrite elem_of_map_img.
    by exists i'.
Qed.


Lemma mg_WF_output_edges `{FinSet nat SA}:
  edgeset_dom G.(mg_output_edges) ⊆@{SA}
    seq_set 0 (G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize)).
Proof.
  intros x.
  rewrite elem_of_seq_set_0.
  intros ((i,v) & 
    (i' & v' & Hi' & (Hi & Hv')%pair_eq)%elem_of_map_to_set 
    & [-> | ->])%elem_of_edgeset_dom.
  - simpl.
    apply elem_of_dom_2 in Hi' as Hi'dom.
    rewrite lookup_total_alt in Hi.
    rewrite mg_vert_outputs_eq_omap in Hi'dom.
    apply dom_omap_subseteq in Hi'dom as Hi'dom'.
    destruct (G.(mg_output_idx) !! i') as [Gi|] eqn:e.
    2: {
      enough (Helemdom : i' ∈ dom G.(mg_output_idx)) by 
        (by rewrite elem_of_dom, e, is_Some_alt in Helemdom).
      unfold mg_output_idx.
      rewrite dom_natset_idx.
      by unfold mg_output_set.
    }
    simpl in Hi.
    pose proof (map_img_natset_idx (SA:=natset) G.(mg_output_set)) as Himg.
    unfold mg_output_set at 2 in Himg.
    rewrite size_dom in Himg.
    fold G.(mg_outsize) in Himg.
    enough (Hkey : Gi ∈@{natset} seq_set 0 G.(mg_outsize)) by 
      (rewrite elem_of_seq_set_0 in Hkey; lia).
    rewrite <- Himg.
    rewrite elem_of_map_img.
    eauto.
  - simpl.
    enough (Hv : v ∈@{natset} seq_set 0 G.(mg_numspi)) by
      (rewrite elem_of_seq_set in Hv; lia).
    rewrite <- Hv'.
    pose proof (map_img_natset_idx (SA:=natset) G.(mg_vert_set)) as Himg.
    unfold mg_vert_set at 2 in Himg.
    rewrite size_dom in Himg.
    fold G.(mg_numspi) in Himg.
    rewrite <- Himg.
    rewrite elem_of_map_img.
    eexists.
    apply lookup_lookup_total_dom.
    unfold mg_vert_idx.
    rewrite dom_natset_idx.
    apply mg_WF_vert_outputs.
    rewrite elem_of_map_img.
    by exists i'.
Qed.



Lemma mg_WF_io_edges `{FinSet nat SA}:
  edgeset_dom G.(mg_io_edges) ⊆@{SA}
    seq_set 0 (G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize)).
Proof.
  intros x.
  rewrite elem_of_seq_set_0.
  intros ((i,v) & 
    (i' & v' & Hi' & (Hi & Hv')%pair_eq)%elem_of_map_to_set 
    & [-> | ->])%elem_of_edgeset_dom.
  - simpl.
    apply elem_of_dom_2 in Hi' as Hi'dom.
    rewrite lookup_total_alt in Hi.
    apply dom_omap_subseteq in Hi'dom as Hi'dom'.
    destruct (G.(mg_input_idx) !! i') as [Gi|] eqn:e.
    2: {
      enough (Helemdom : i' ∈ dom G.(mg_input_idx)) by 
        (by rewrite elem_of_dom, e, is_Some_alt in Helemdom).
      unfold mg_input_idx.
      by rewrite dom_natset_idx.
    }
    simpl in Hi.
    pose proof (map_img_natset_idx (SA:=natset) G.(mg_input_set)) as Himg.
    unfold mg_input_set at 2 in Himg.
    rewrite size_dom in Himg.
    fold G.(mg_insize) in Himg.
    enough (Hkey : Gi ∈@{natset} seq_set 0 G.(mg_insize)) by 
      (rewrite elem_of_seq_set_0 in Hkey; lia).
    rewrite <- Himg.
    rewrite elem_of_map_img.
    eauto.
  - simpl.
    apply elem_of_dom_2 in Hi' as Hi'dom.
    rewrite lookup_total_alt in Hi.
    apply dom_omap_subseteq in Hi'dom as Hi'dom'.
    destruct (G.(mg_input_idx) !! i') as [Gi|] eqn:e.
    2: {
      enough (Helemdom : i' ∈ dom G.(mg_input_idx)) by 
        (by rewrite elem_of_dom, e, is_Some_alt in Helemdom).
      unfold mg_input_idx. 
      by rewrite dom_natset_idx.
    }
    simpl in Hi.
    enough (G.(mg_output_idx) !!! v' ∈@{natset} seq_set 0 G.(mg_outsize))
      by (rewrite elem_of_seq_set_0 in *; lia).
    apply (elem_of_map_img_2 (SA:=natset)) in Hi' as Hi'img.
    pose proof (map_img_natset_idx (SA:=natset) G.(mg_output_set)) as Himg.
    unfold mg_output_set at 2 in Himg.
    rewrite size_dom in Himg.
    fold G.(mg_outsize) in Himg.
    rewrite <- Himg.
    apply mg_boundary_inputs_img_subseteq in Hi'img.
    rewrite elem_of_map_img.
    exists v'.
    apply lookup_lookup_total_dom.
    unfold mg_output_idx.
    rewrite dom_natset_idx.
    apply Hi'img.
Qed.

Lemma dom_mg_degrees_WF : 
  dom (mg_degrees G) ⊆ seq_set 0 (G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize)).
Proof.
  rewrite dom_mg_degrees_eq_bind_dom_mg_edges.
  rewrite dom_mg_edges_eq.
  rewrite 3!edgeset_dom_union_L.
  rewrite 3!union_subseteq.
  



  apply set_eq => k.
  unfold mg_degrees.
  rewrite gmultiset_elem_of_dom.
  (* Search (_ ∈ (_ ⊎ _)). *)
  rewrite gmultiset_elem_of_disj_union.

  Search dom gmultiset.
  rewrite dom_g

Lemma mg_size_pf
*)

Module Examples.

Notation "merge!" := (union_with (fun _ _ => None)).
(* (fun _ _ => None) What to do with conflicts - but we can't have any! *)

Definition stack_ZX_map_graph_of_WF' (ZXG0 ZXG1 : ZX_map_graph)  
  : ZX_map_graph :=
  (* Assumes ZXG0 and ZXG1 are "WF", in that their vertex, index, 
    and output sets are "dense" (i.e. look like 0, 1, ..., n-1). 
    WARNING: This is NOT the actual meaning that WF_ZX_map_graph will have,
    nor with that predicate include this statement
    This avoids only some composition by some adjustment functions, but 
    is therefore much easier to read. *)
  
  {|
    mg_verts (* : natmap (bool * R) *) := 
      merge! 
        ZXG0.(mg_verts)
        (kmap (Nat.add ZXG0.(mg_numspi)) ZXG1.(mg_verts)) ; 
          (* ^ Shift the vertex indexing by the number of vertices in the first *)
    mg_inputs (* : natmap EdgeType (* verts + outputs *) *) := 
      merge!
        ZXG0.(mg_inputs)
        (  (* Shift indexes of the targets of the input edges *)
          sum_elim 
            (inl ∘ Nat.add ZXG0.(mg_numspi)) 
            (inr ∘ Nat.add ZXG0.(mg_outsize)) 
          <$> 
            kmap (Nat.add ZXG0.(mg_insize)) ZXG1.(mg_inputs) (* Shift, as above *)
        ) ;

    mg_vert_outputs (* : natmap nat (* only verts!! *) *) := 
      merge!
        ZXG0.(mg_vert_outputs)
        (
          Nat.add ZXG0.(mg_numspi) 
            <$> (* Shift indexes of the targets of the output edges *)
          kmap (Nat.add ZXG0.(mg_outsize)) ZXG1.(mg_vert_outputs) (* Shift, as above *)
        ) ;

    mg_vert_edges (* : gmultiset (nat * nat) *) :=
      ZXG0.(mg_vert_edges) ⊎
      (gmultiset_map ((λ f, prod_map f f) (Nat.add ZXG0.(mg_numspi)))
        ZXG1.(mg_vert_edges))
      ;

  |}.


Definition compose_ZX_map_graph_of_WF' (ZXG0 ZXG1 : ZX_map_graph)  
  : ZX_map_graph :=
  (* Assumes ZXG0 and ZXG1 are "WF", in that their vertex, index, 
    and output sets are "dense" (i.e. look like 0, 1, ..., n-1). 
    WARNING: This is NOT the actual meaning that WF_ZX_map_graph will have,
    nor with that predicate include this statement
    This avoids only some composition by some adjustment functions, but 
    is therefore much easier to read. *)
  
  {|
    mg_verts (* : natmap (bool * R) *) := 
      merge! 
        ZXG0.(mg_verts)
        (kmap (Nat.add ZXG0.(mg_numspi)) ZXG1.(mg_verts)) ; 
          (* ^ Shift the vertex indexing by the number of vertices in the first *)

    mg_inputs (* : natmap EdgeType (* verts + outputs *) *) :=
      sum_elim
        inl (* Inputs from ZXG0 to verts stay the same *)
        ( fun o : nat (* ZXG0 output idx *) => 
          (.$ ZXG1.(mg_inputs) !!! o) $
          sum_elim (* cases on where ZXG1 sends the output *)
            (inl ∘ Nat.add ZXG0.(mg_numspi)) (* left is a ZXG1 vertex *)
            inr (* right is a ZXG1 output *)
        )
      <$>
        (ZXG0.(mg_inputs) : natmap (nat + nat)) ;

    mg_vert_outputs (* : natmap nat (* only verts!! *) *) := 
      merge! 
      (Nat.add ZXG0.(mg_numspi) <$> (* Shift output-to-vertex edges *)
        ZXG1.(mg_vert_outputs))
      (map_compose ZXG0.(mg_vert_outputs) ZXG1.(mg_boundary_outputs)) 
        (* We also need an output 
        for the outputs of ZXG0 that get passed through ZXG1 *);

    mg_vert_edges (* : gmultiset (nat * nat) *) :=
      ZXG0.(mg_vert_edges) (* Edges of ZXG0 and... *)
      ⊎ (gmultiset_map ((λ f, prod_map f f) (Nat.add ZXG0.(mg_numspi)))
        ZXG1.(mg_vert_edges)) (* edges of ZXG1 and... *)
      ⊎ (* The connections between ZXG0 and ZXG1's vertices from IO: *)
        gset_to_multiset (map_img $
        (merge 
          (λ inv' outv', 
            inv ← inv'; outv ← outv' ;
            Some (inv, ZXG0.(mg_numspi) + outv))
          ZXG0.(mg_vert_outputs)
          ZXG1.(mg_vert_inputs)
          :> natmap (nat * nat)));

  |}.

End Examples.

