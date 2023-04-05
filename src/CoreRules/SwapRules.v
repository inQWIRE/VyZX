Require Import CoreData.
Require Import WireRules.
Require Import CoreAutomation.
Require Import StackComposeRules.
Require Import CastRules.


Lemma swap_compose :
  ⨉ ⟷ ⨉ ∝ n_wire 2.
Proof. solve_prop 1. Qed.

Lemma top_wire_to_bottom_ind : forall n, top_wire_to_bottom (S (S n)) = @Mmult _ (2 ^ (S (S n))) _ ((I 2) ⊗ top_wire_to_bottom (S n)) (swap ⊗ (I (2 ^ n))).
Proof.
  intros.
  induction n.
  - Msimpl.
    simpl.
    Msimpl.
    easy.
  - rewrite IHn.
    simpl.
    apply Mmult_simplify.
    + apply kron_simplify; easy.
    + apply kron_simplify; [easy | ].
      rewrite kron_n_I.
      rewrite id_kron.
      replace (2 ^ n + (2 ^ n + 0))%nat with (2 ^ n * 2)%nat by lia.
      easy.
Qed.


Global Hint Resolve WF_a_swap_semantics : wf_db.

(* Proving correctness of conversion *)

Lemma top_to_bottom_correct : forall n, ZX_semantics (top_to_bottom n) = top_wire_to_bottom n.
Proof.
  intros.
  destruct n; [ reflexivity | ].
  destruct n; [ easy | ].
  induction n.
  - easy.
  - simpl.
    simpl in IHn.
    rewrite <- IHn.
    rewrite n_wire_semantics.
    rewrite kron_n_I.
    rewrite 2 id_kron.
    replace (2 * 2 ^ n)%nat with (2 ^ n * 2)%nat by lia.
    easy.
Qed.

Lemma bottom_to_top_correct : forall n, ZX_semantics (bottom_to_top n) = bottom_wire_to_top n.
Proof.
  intros.
  unfold bottom_to_top.
  unfold bottom_wire_to_top.
  rewrite semantics_transpose_comm.
  rewrite top_to_bottom_correct.
  easy.
Qed.

Lemma a_swap_correct : forall n, ZX_semantics (a_swap n) = a_swap_semantics n.
Proof.
  intros.
  unfold a_swap_semantics.
  destruct n; [ reflexivity | ].
  rewrite <- bottom_to_top_correct.
  rewrite <- top_to_bottom_correct.
  simpl.
  easy.
Qed.

Lemma swap_spec' : swap = ((ket 0 × bra 0)  ⊗ (ket 0 × bra 0) .+ (ket 0 × bra 1)  ⊗ (ket 1 × bra 0)
  .+ (ket 1 × bra 0)  ⊗ (ket 0 × bra 1) .+ (ket 1 × bra 1)  ⊗ (ket 1 × bra 1)).
Proof.
  solve_matrix.
Qed.

Lemma top_to_bottom_grow_l : forall n, 
  top_to_bottom (S (S n)) ∝ (⨉ ↕ n_wire n) ⟷ (— ↕ top_to_bottom (S n)).
Proof. easy. Qed.

Lemma offset_swaps_comm_top_left : 
  ⨉ ↕ — ⟷ (— ↕ ⨉) ∝ 
  — ↕ ⨉ ⟷ (⨉ ↕ —) ⟷ (— ↕ ⨉) ⟷ (⨉ ↕ —).
Proof. solve_prop 1. Qed.

Lemma offset_swaps_comm_bot_right : 
 — ↕ ⨉ ⟷ (⨉ ↕ —)  ∝ 
 ⨉ ↕ — ⟷ (— ↕ ⨉) ⟷ (⨉ ↕ —) ⟷ (— ↕ ⨉). 
Proof. solve_prop 1. Qed.

Lemma bottom_wire_to_top_ind : forall n, bottom_wire_to_top (S (S n)) = @Mmult _ (2 ^ (S (S n))) _ (swap ⊗ (I (2 ^ n))) ((I 2) ⊗ bottom_wire_to_top (S n)).
Proof.
  intros.
  apply transpose_matrices.
  unfold bottom_wire_to_top.
  rewrite Mmult_transpose.
  restore_dims.
  rewrite Matrix.transpose_involutive.
  restore_dims.
  rewrite (kron_transpose 2 2 (2 ^ (S n)) (2 ^ S n)).
  replace (Nat.pow 2 (S (S n)))%nat with ((2 * 2) * (2 ^ n))%nat by (simpl; lia).
  rewrite (kron_transpose  (2 * 2) (2 * 2) (2 ^ n) (2 ^ n) swap (I (2 ^ n))).
  rewrite 2 id_transpose_eq.
  rewrite swap_transpose.
  rewrite Matrix.transpose_involutive.
  restore_dims.
  rewrite (top_wire_to_bottom_ind n).
  easy.
Qed.

Lemma bottom_to_top_grow_r : forall n, 
  bottom_to_top (S (S n)) ∝ (— ↕ bottom_to_top (S n)) ⟷ (⨉ ↕ n_wire n).
Proof.
  intros.
  unfold bottom_to_top.
  simpl.
  rewrite n_wire_transpose.
  easy. 
Qed.

Lemma a_swap_grow : forall n, a_swap (S (S (S n))) ∝ (⨉ ↕ n_wire (S n)) ⟷ (— ↕ a_swap (S (S n))) ⟷ (⨉ ↕ n_wire (S n)). 
Proof.
  intros.
  remember (⨉ ↕ n_wire S n ⟷ (— ↕ a_swap (S (S n))) ⟷ (⨉ ↕ n_wire S n)) as right_side.
  unfold a_swap at 1.
  rewrite bottom_to_top_grow_r.
  rewrite top_to_bottom_grow_l.
  simpl.
  rewrite compose_assoc.
  rewrite stack_wire_distribute_l.
  rewrite <- (compose_assoc (⨉ ↕ (— ↕ n_wire n))).
  rewrite stack_assoc_back.
  rewrite (stack_assoc_back — ⨉ (n_wire n)).
  simpl_casts.
  rewrite <- (@stack_nwire_distribute_r _ _ _ n (⨉ ↕ —) (— ↕ ⨉)).
  rewrite offset_swaps_comm_top_left.
  rewrite bottom_to_top_grow_r.
  rewrite stack_wire_distribute_l.
  rewrite (compose_assoc _ (— ↕ (⨉ ↕ n_wire n))).
  rewrite (stack_assoc_back — ⨉ (n_wire n)).
  simpl_casts.
  rewrite <- (compose_assoc (— ↕ ⨉ ↕ n_wire n)).
  rewrite <- (@stack_nwire_distribute_r _ _ _ n (— ↕ ⨉) (— ↕ ⨉ ⟷ (⨉ ↕ —) ⟷ (— ↕ ⨉) ⟷ (⨉ ↕ —))).
  repeat rewrite <- compose_assoc.
  rewrite <- stack_wire_distribute_l.
  rewrite swap_compose.
  cleanup_zx.
  repeat rewrite stack_nwire_distribute_r.
  rewrite (stack_assoc ⨉ — (n_wire n)).
  rewrite 2 (stack_assoc_back — —).
  simpl_casts.
  rewrite wire_to_n_wire at 1 2 3 7 9 10.
  repeat rewrite n_wire_stack.
  repeat rewrite <- compose_assoc.
  rewrite (nwire_stack_compose_topleft (bottom_to_top (S n)) ⨉).
  rewrite <- nwire_stack_compose_botleft.
  repeat rewrite compose_assoc.
  rewrite (nwire_stack_compose_botleft ⨉ (top_to_bottom_helper n)).
  rewrite <- (nwire_stack_compose_topleft (top_to_bottom_helper n) ⨉).
  simpl.
  rewrite stack_empty_r.
  simpl_casts.
  rewrite 3 (stack_assoc —).
  simpl_casts.
  rewrite Heqright_side.
  repeat rewrite compose_assoc.
  apply compose_simplify; [ easy | ].
  repeat rewrite <- compose_assoc.
  apply compose_simplify; [ | easy ].
  simpl.
  rewrite <- 2 stack_wire_distribute_l.
  apply stack_simplify; [ easy | ].
  rewrite <- bottom_to_top_grow_r.
  easy.
Qed.

Lemma a_swap_2_is_swap : a_swap 2 ∝ ⨉.
Proof.
  solve_prop 1.
Qed.


Lemma a_swap_3_order_indep :
  I 2 ⊗ swap × (swap ⊗ I 2) × (I 2 ⊗ swap) = (swap ⊗ I 2) × (I 2 ⊗ swap) × (swap ⊗ I 2).
Proof.
  (* solve_matrix *) (* Commented out for performance*)
Admitted.

Lemma a_swap_semantics_ind : forall n, a_swap_semantics (S (S (S n))) = swap ⊗ (I (2 ^ (S n))) × (I 2 ⊗ a_swap_semantics (S (S n))) × (swap ⊗ (I (2 ^ (S n)))).
Proof.
  intros.
  rewrite <- 2 a_swap_correct.
  simpl.
  repeat rewrite kron_id_dist_l by shelve.
  restore_dims.
  rewrite <- 2 (kron_assoc (I 2) (I 2) (_)) by shelve.
  repeat rewrite id_kron.
  replace ((2 ^ n + (2 ^ n + 0)))%nat with (2 ^ (S n))%nat by (simpl; lia).
  restore_dims.
  repeat rewrite <- Mmult_assoc.
  restore_dims.
  rewrite (kron_mixed_product swap (I _) (I (2 * 2)) (_)).
  Msimpl.
  repeat rewrite Mmult_assoc.
  restore_dims.
  repeat rewrite Mmult_assoc.
  remember (ZX_semantics (top_to_bottom_helper n) ⊤%ZX) as ZX_tb_t.
  remember (ZX_semantics (top_to_bottom_helper n)) as ZX_tb.
  restore_dims.
  rewrite (kron_mixed_product (I (2 * 2)) ZX_tb_t swap (I (2 ^ (S n)))) .
  Msimpl; [ | shelve].
  rewrite <- (Mmult_1_r _ _ (swap ⊗ ZX_tb)) by shelve.
  rewrite n_wire_transpose.
  rewrite n_wire_semantics.
  rewrite <- 2 kron_assoc by shelve.
  restore_dims.
  repeat rewrite <- Mmult_assoc by shelve.
  rewrite <- 2 kron_id_dist_r by shelve.
  rewrite a_swap_3_order_indep.
  rewrite 2 kron_id_dist_r by shelve.
  repeat rewrite <- Mmult_assoc by shelve.
  restore_dims.
  rewrite (kron_assoc _ (I 2) (I (2 ^ n))) by shelve.
  rewrite id_kron.
  replace (2 * (2 ^ n))%nat with (2 ^ (S n))%nat by (simpl; lia).
  restore_dims.
  repeat rewrite <- Mmult_assoc by shelve.
  rewrite kron_mixed_product.
  Msimpl.
  2,3: shelve.
  restore_dims.
  repeat rewrite Mmult_assoc by shelve.
  restore_dims.
  rewrite kron_mixed_product.
  Msimpl; [ | shelve].
  easy.
Unshelve.
all: subst; auto with wf_db.
all: try (apply WF_kron; try lia; replace (2 ^ n + (2 ^ n + 0))%nat with (2 ^ (S n))%nat by (simpl; lia); auto with wf_db).
  apply WF_mult.
  auto with wf_db.
  apply WF_kron; try lia; replace (2 ^ n + (2 ^ n + 0))%nat with (2 ^ (S n))%nat by (simpl; lia); auto with wf_db.
Qed. 

(* n_swap proofs *)

Opaque a_swap a_swap_semantics. (* For n_swap proofs we don't want a_swap to unfold, instead we use lemmata from above*)

Lemma n_swap_2_is_swap : n_swap 2 ∝ ⨉.
Proof.
  intros.
  simpl.
  simpl_casts.
  cleanup_zx.
  rewrite wire_to_n_wire.
  rewrite n_wire_stack.
  cleanup_zx.
  apply a_swap_2_is_swap.
Qed.

Lemma n_swap_mat_ind_correct : forall n, ZX_semantics (n_swap n) = n_swap_mat_ind n.
Proof.
  intros.
  strong induction n.
  do 2 (destruct n; [ easy | ]).
  assert (n < (S (S n)))%nat by lia.
  specialize (H n H0).
  clear H0.
  simpl.
  simpl_cast_semantics.
  simpl.
  rewrite H.
  rewrite a_swap_correct.
  restore_dims.
  rewrite kron_assoc; auto with wf_db.
Qed.