Require Import CoreData.
Require Import CoreRules.
Require Import Gates.

Local Open Scope ZX.

Lemma swap_self_inverse : ⨉ ⟷ ⨉ ∝ n_wire 2.
Proof.
  intros.
  prop_exists_nonzero 1.
  Msimpl.
  simpl.
  restore_dims.
  rewrite swap_swap.
  rewrite 2 id_kron.
  easy.
Qed.

(* Needs to be diagrammatic *)
Lemma _3_cnot_swap_is_swap : _3_CNOT_SWAP_ ∝ ⨉.
Proof.
Abort.

Lemma n_stack_1_n_stack : forall {n} (zx : ZX 1 1), (n ↑ zx) ∝ (cast _ _ (eq_sym (Nat.mul_1_r _)) (eq_sym (Nat.mul_1_r _)) (n ⇑ zx)).
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

Lemma n_stack_n_stack_1 : forall {n} (zx : ZX 1 1), (n ⇑ zx) ∝ (cast _ _ (Nat.mul_1_r _) (Nat.mul_1_r _) (n ↑ zx)).
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
  n ↑ (zx0 ⟷ zx1) ∝ (n ↑ zx0) ⟷ (n ↑ zx1).
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

Lemma H_H_is_wire : □ ⟷ □ ∝ —.
Proof.
  prop_exists_nonzero 1.
  simpl.
  rewrite MmultHH.
  lma.
Qed.

Lemma n_H_composition : forall {n}, 
  (n ↑ □) ⟷ (n ↑ □) ∝ n ↑ —.
Proof.
  intros.
  rewrite <- n_stack1_compose.
  rewrite H_H_is_wire.
  reflexivity.
Qed.

Theorem trivial_cap_cup : 
  ⊂ ⟷ ⊃ ∝ ⦰.
Proof. solve_prop 2. Qed.

Lemma cap_passthrough : forall (zx : ZX 1 1),  
  (⊂ ⟷ (zx ↕ —)) ∝ (⊂ ⟷ (— ↕ zx⊤)).
Proof.
  intros.
  prop_exists_nonzero 1.
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
  (zx ↕ —) ⟷ ⊃ ∝ (— ↕ zx⊤) ⟷ ⊃.
Proof. transpose_of cap_passthrough. Qed.

Lemma swap_passthrough_1_1 : forall (zx0 : ZX 1 1) (zx1 : ZX 1 1),
  (zx0 ↕ zx1) ⟷ ⨉ ∝ ⨉ ⟷ (zx1 ↕ zx0).
Proof.
  intros.
  prop_exists_nonzero 1.
  Msimpl; simpl.
  solve_matrix.
  all: rewrite WF_ZX; try lca.
  1-4: left; auto.
  5,7,9,11: right; auto.
  1-4: left.
  5-8: right.
  all: simpl;
       apply le_n_S;
       apply le_n_S;
       apply Nat.le_0_l.
Qed.

Lemma Z_commutes_through_swap_t : forall α, 
  ((Z_Spider 1 1 α) ↕ —) ⟷ ⨉ ∝ 
  ⨉ ⟷ (— ↕ (Z_Spider 1 1 α)).
Proof.
  intros.
  rewrite swap_passthrough_1_1.
  easy.
Qed.  

Lemma spiders_commute_through_swap_b : forall (zx0 zx1 : ZX 1 1),
  (— ↕ zx0) ⟷ ⨉ ∝ ⨉ ⟷ (zx0 ↕ —) ->      
  (— ↕ zx1) ⟷ ⨉ ∝ ⨉ ⟷ (zx1 ↕ —) ->
  (— ↕ (zx0 ⟷ zx1)) ⟷ ⨉ ∝ ⨉ ⟷ ((zx0 ⟷ zx1) ↕ —).
Proof.
  intros.
  rewrite swap_passthrough_1_1.
  reflexivity.
Qed.

Lemma spiders_commute_through_swap_t : forall (zx0 zx1 : ZX 1 1),
  (zx0 ↕ —) ⟷ ⨉ ∝ ⨉ ⟷ (— ↕ zx0) ->      
  (zx1 ↕ —) ⟷ ⨉ ∝ ⨉ ⟷ (— ↕ zx1) ->
  ((zx0 ⟷ zx1) ↕ —) ⟷ ⨉ ∝ ⨉ ⟷ (— ↕ (zx0 ⟷ zx1)).
Proof.
  intros.
  rewrite swap_passthrough_1_1.
  reflexivity.
Qed.

Lemma n_box_passthrough :forall {nIn nOut} (zx : ZX nIn nOut),
  (n_box nIn) ⟷ zx ∝ (⊙ zx ⟷ (n_box nOut)).
Proof.
  intros.
  prop_exists_nonzero 1.
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

Lemma Z_spider_angle_2pi : forall {nIn nOut} α k, Z_Spider nIn nOut α ∝ (Z_Spider nIn nOut (α + IZR (2 * k) * PI)).
Proof.
  intros.
  prop_exists_nonzero 1.
  unfold ZX_semantics, Z_semantics.
  rewrite Cexp_add.
  rewrite Cexp_2nPI.
  rewrite Cmult_1_r.
  Msimpl.
  reflexivity.
Qed.

Lemma X_spider_angle_2pi : forall {nIn nOut} α k, X_Spider nIn nOut α ∝ (X_Spider nIn nOut (α + IZR (2 * k) * PI)).
Proof. intros. colorswap_of (@Z_spider_angle_2pi nIn nOut). Qed.
