Require Import CoreData.
Require Import CoreRules.
Require Import Bialgebra.
Require Import Gates.

Require Import ZXpermFacts.

Local Open Scope ZX.

Lemma swap_self_inverse : ⨉ ⟷ ⨉ ∝= n_wire 2.
Proof.
  intros.
  by_perm_eq.
Qed.

(* Needs to be diagrammatic *)
Lemma _3_cnot_swap_is_swap : _3_CNOT_SWAP_ ∝[/ (C2 * √2)] ⨉.
Proof.
  set (sqrt2 := √ 2).
  (* step 1 *)
  (* Set Printing Raw Literals. *)
  rewrite cnot_is_swapp_notc at 2.
  (* step 2 *)
  rewrite compose_assoc, <- (compose_assoc _ _ ⨉), 
    <- (compose_assoc _ ⨉).
  rewrite notc_is_notc_r.
  (* step 3 *)
  rewrite <- ! (compose_assoc (_ ⟷ ⨉)).
  zxrewrite bi_algebra_rule_X_over_Z.
  fold sqrt2.
  rewrite Cdiv_unfold, Cinv_inv, Cinv_mult_distr.
  rewrite <- Cmult_assoc, Cinv_l, Cmult_1_r by (subst sqrt2; nonzero).
  (* step 4 *)
  rewrite <- !compose_assoc.
  rewrite (compose_assoc (_ ↕ —)).
  rewrite <- (@stack_compose_distr 1 1 2 2 1 1).
  rewrite wire_removal_l, wire_removal_r, 
    (stack_split_diag (Z 1 2 0) (X 2 1 0)).
  rewrite <- compose_assoc.
  (* step 5 *)
  rewrite <- (n_wire_stack 1 1).
  change 2%nat with (1 + 1)%nat.
  rewrite stack_assoc_back_fwd, cast_id.
  rewrite <- (@stack_compose_distr 1 2 3 1 1 1).
  rewrite (@dominated_Z_spider_fusion_top_left 2 0 1 1).
  rewrite wire_removal_l.
  rewrite stack_assoc_fwd, cast_id.
  rewrite (compose_assoc _ _ (—↕X 2 1 _)).
  rewrite <- (@stack_compose_distr 1 1 1 3 2 1).
  rewrite (@dominated_X_spider_fusion_bot_right 2 0 1 1).
  rewrite Rplus_0_r.
  cbn [Nat.add].
  (* step 6 *)
  rewrite wire_removal_r.
  pose proof (hopf_rule_Z_X_vert 1 1 1 1 0 0 eq_refl) as Hrw.
  rewrite cast_id in Hrw.
  zxrewrite Hrw.
  rewrite Cdiv_unfold, Cinv_inv, Cinv_l by nonzero.
  (* step 7 *)
  rewrite Z_is_wire, X_0_is_wire.
  bundle_wires.
  rewrite nwire_removal_l.
  (* step 8 *)
  zxrefl.
Qed.

Lemma n_stack_1_n_stack : forall {n} (zx : ZX 1 1), (n ↑ zx) ∝= (cast _ _ (eq_sym (Nat.mul_1_r _)) (eq_sym (Nat.mul_1_r _)) (n ⇑ zx)).
Proof.
  intros.
  unfold eq_rect.
  destruct (Nat.mul_1_r n).
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma n_stack_n_stack_1 : forall {n} (zx : ZX 1 1), (n ⇑ zx) ∝= (cast _ _ (Nat.mul_1_r _) (Nat.mul_1_r _) (n ↑ zx)).
Proof.
  intros.
  symmetry.
  unfold eq_sym.
  unfold eq_rect.
  destruct (Nat.mul_1_r n).
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed. 

Lemma n_stack1_compose : forall (zx0 zx1 : ZX 1 1) {n}, 
  n ↑ (zx0 ⟷ zx1) ∝= (n ↑ zx0) ⟷ (n ↑ zx1).
Proof.
  intros.
  induction n.
  - unfold n_stack1.
    symmetry.
    cleanup_zx.
    reflexivity.
  - simpl.
    rewrite <- (stack_compose_distr zx0 zx1).
    rewrite IHn.
    reflexivity.
Qed. 

Lemma H_H_is_wire : □ ⟷ □ ∝= —.
Proof.
  hnf.
  simpl.
  rewrite MmultHH.
  lma.
Qed.

Lemma n_H_composition : forall {n}, 
  (n ↑ □) ⟷ (n ↑ □) ∝= n ↑ —.
Proof.
  intros.
  rewrite <- n_stack1_compose.
  rewrite H_H_is_wire.
  reflexivity.
Qed.

Theorem trivial_cap_cup : 
  ⊂ ⟷ ⊃ ∝[2] ⦰.
Proof.
  split; [|nonzero].
  lma'.
Qed.

Lemma cap_passthrough : forall (zx : ZX 1 1),  
  (⊂ ⟷ (zx ↕ —)) ∝= (⊂ ⟷ (— ↕ zx⊤)).
Proof.
  intros.
  hnf.
  simpl.
  rewrite semantics_transpose_comm.
  Msimpl; simpl.
  unfold kron, Mmult, I, list2D_to_matrix, Matrix.transpose.
  prep_matrix_equality.
  do 4 (try destruct x); do 4 (try destruct y).
  all: C_field_simplify; try lca.
  assert ((S (S (S (S x))) / 2 <? 2) = false)%nat.
  {
    apply Nat.ltb_ge.
    replace (S (S (S (S x))))%nat with (2 * 2 + x)%nat by lia.
    rewrite Nat.div_add_l.
    apply Nat.le_add_r.
    easy.
  }
  rewrite 2 big_sum_0; auto; intros.
  - rewrite H.
    rewrite andb_false_r.
    lca.
  - rewrite WF_ZX; try lca.
    left.
    apply Nat.ltb_ge.
    apply H.
Qed.

Lemma cup_passthrough : forall (zx : ZX 1 1),
  (zx ↕ —) ⟷ ⊃ ∝= (— ↕ zx⊤) ⟷ ⊃.
Proof. transpose_of cap_passthrough. Qed.

Lemma swap_passthrough_1_1 : forall (zx0 : ZX 1 1) (zx1 : ZX 1 1),
  (zx0 ↕ zx1) ⟷ ⨉ ∝= ⨉ ⟷ (zx1 ↕ zx0).
Proof.
  intros. 
  rewrite <- ZXpermFacts.zx_comm_1_1_swap.
  apply (ZXpermFacts.zx_comm_commutes_r zx0 zx1).
Qed.

Lemma Z_commutes_through_swap_t : forall α, 
  ((Z_Spider 1 1 α) ↕ —) ⟷ ⨉ ∝= 
  ⨉ ⟷ (— ↕ (Z_Spider 1 1 α)).
Proof.
  intros.
  rewrite swap_passthrough_1_1.
  easy.
Qed.  

Lemma spiders_commute_through_swap_b : forall (zx0 zx1 : ZX 1 1),
  (— ↕ zx0) ⟷ ⨉ ∝= ⨉ ⟷ (zx0 ↕ —) ->      
  (— ↕ zx1) ⟷ ⨉ ∝= ⨉ ⟷ (zx1 ↕ —) ->
  (— ↕ (zx0 ⟷ zx1)) ⟷ ⨉ ∝= ⨉ ⟷ ((zx0 ⟷ zx1) ↕ —).
Proof.
  intros.
  rewrite swap_passthrough_1_1.
  reflexivity.
Qed.

Lemma spiders_commute_through_swap_t : forall (zx0 zx1 : ZX 1 1),
  (zx0 ↕ —) ⟷ ⨉ ∝= ⨉ ⟷ (— ↕ zx0) ->      
  (zx1 ↕ —) ⟷ ⨉ ∝= ⨉ ⟷ (— ↕ zx1) ->
  ((zx0 ⟷ zx1) ↕ —) ⟷ ⨉ ∝= ⨉ ⟷ (— ↕ (zx0 ⟷ zx1)).
Proof.
  intros.
  rewrite swap_passthrough_1_1.
  reflexivity.
Qed.

Lemma n_box_passthrough :forall {nIn nOut} (zx : ZX nIn nOut),
  (n_box nIn) ⟷ zx ∝= (⊙ zx ⟷ (n_box nOut)).
Proof.
  intros.
  hnf.
  Msimpl.
  simpl.
  rewrite semantics_colorswap_comm.
  rewrite 2 n_box_semantics.
  rewrite Mmult_assoc.
  rewrite <- Mmult_assoc.
  rewrite kron_n_mult.
  rewrite MmultHH.
  rewrite kron_n_I.
  rewrite Mmult_1_l by auto with wf_db.
  easy.
Qed.

Lemma Z_spider_angle_2pi : forall {nIn nOut} α k, Z_Spider nIn nOut α ∝= (Z_Spider nIn nOut (α + IZR (2 * k) * PI)).
Proof.
  intros.
  hnf.
  unfold ZX_semantics, Z_semantics.
  rewrite Cexp_add.
  rewrite Cexp_2nPI.
  rewrite Cmult_1_r.
  Msimpl.
  reflexivity.
Qed.

Lemma X_spider_angle_2pi : forall {nIn nOut} α k, X_Spider nIn nOut α ∝= (X_Spider nIn nOut (α + IZR (2 * k) * PI)).
Proof. intros. colorswap_of (@Z_spider_angle_2pi nIn nOut). Qed.

Require Import DiagramRules.
