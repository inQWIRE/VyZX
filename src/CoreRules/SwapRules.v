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



(* Proving correctness of conversion *)

Lemma top_to_bottom_correct : forall n, ⟦ top_to_bottom n ⟧ = top_wire_to_bottom n.
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

Lemma bottom_to_top_correct : forall n, ⟦ bottom_to_top n ⟧ = bottom_wire_to_top n.
Proof.
  intros.
  unfold bottom_to_top.
  unfold bottom_wire_to_top.
  rewrite semantics_transpose_comm.
  rewrite top_to_bottom_correct.
  easy.
Qed.

Lemma a_swap_correct : forall n, ⟦ a_swap n ⟧ = a_swap_semantics n.
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

Lemma top_to_bottom_grow_r : forall n prf prf', 
  top_to_bottom (S (S n)) ∝ cast _ _ prf' prf' (top_to_bottom (S n) ↕ —) ⟷ (cast _ _ prf prf (n_wire n ↕ ⨉)).
Proof.
  intros.
  induction n.
  + simpl; cleanup_zx; simpl_casts.
    bundle_wires.
    cleanup_zx.
    easy.
  + simpl.
    simpl in IHn.
    rewrite IHn at 1.
    simpl_casts. 
    rewrite (stack_assoc — (n_wire n) ⨉).
    simpl_casts.
    erewrite (@cast_stack_distribute
    _ 1 _ 1 _ _ _ _
    _ _ _ _ _ _ — (n_wire n ↕ ⨉)).
    rewrite (cast_id _ _ —).
    erewrite (cast_compose_mid (S (S n)) _ _ (⨉ ↕ n_wire n)).
    erewrite (@cast_stack_distribute
      _ 1 _ 1 _ _ _ _
      _ _ _ _ _ _ — (top_to_bottom_helper n)).
    rewrite cast_id.
    rewrite stack_wire_distribute_r.
    rewrite cast_compose_distribute.
    rewrite stack_wire_distribute_l.
    rewrite <- compose_assoc.
    apply compose_simplify; [ | easy ].
    bundle_wires.
    repeat rewrite cast_id.
    symmetry.
    erewrite (cast_compose_mid (S (S (S n)))).
    simpl_casts.
    apply compose_simplify; [ | rewrite (stack_assoc_back — (top_to_bottom_helper n) —); simpl_casts; easy ].
    eapply (cast_diagrams (2 + (1 + n)) (2 + (1 + n))).
    rewrite cast_contract.
    rewrite (stack_assoc ⨉ (n_wire n) —).
    rewrite cast_contract.
    rewrite cast_stack_distribute.
    bundle_wires.
    rewrite cast_n_wire.
    simpl_casts.
    easy.
Unshelve.
  all: lia.
Qed.
  
Lemma offset_swaps_comm_top_left : 
  ⨉ ↕ — ⟷ (— ↕ ⨉) ∝ 
  — ↕ ⨉ ⟷ (⨉ ↕ —) ⟷ (— ↕ ⨉) ⟷ (⨉ ↕ —).
Proof. (* solve_prop 1. Qed. *) Admitted.

Lemma offset_swaps_comm_bot_right : 
 — ↕ ⨉ ⟷ (⨉ ↕ —)  ∝ 
 ⨉ ↕ — ⟷ (— ↕ ⨉) ⟷ (⨉ ↕ —) ⟷ (— ↕ ⨉). 
Proof. (* solve_prop 1. Qed. *) Admitted.

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


Lemma bottom_to_top_grow_l : forall n prf prf', 
  bottom_to_top (S (S n)) ∝ cast _ _ prf' prf'((cast _ _ prf prf (n_wire n ↕ ⨉)) ⟷ (bottom_to_top (S n) ↕ —)).
Proof.
  intros.
  apply transpose_diagrams.
Opaque top_to_bottom.
  simpl.
  unfold bottom_to_top.
  rewrite cast_transpose.
  simpl.
  repeat rewrite cast_transpose.
  simpl.
  rewrite n_wire_transpose.
  repeat rewrite Proportional.transpose_involutive.
  rewrite top_to_bottom_grow_r.
  rewrite cast_compose_distribute.
  simpl_casts.
  erewrite (cast_compose_mid (S (n + 1))).
  simpl_casts.
  apply compose_simplify; cast_irrelevance.
Unshelve.
all: lia.
Qed.
Transparent top_to_bottom.

Lemma top_to_bottom_transpose : forall n, (top_to_bottom n)⊤ ∝ bottom_to_top n.
Proof.
  intros.
  unfold bottom_to_top.
  easy.
Qed.

Lemma bottom_to_top_transpose : forall n, (bottom_to_top n)⊤ ∝ top_to_bottom n.
Proof.
  intros.
  unfold bottom_to_top.
  rewrite Proportional.transpose_involutive.
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
  bundle_wires.
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
Unshelve.
all: lia.
Qed.

Lemma a_swap_2_is_swap : a_swap 2 ∝ ⨉.
Proof.
  unfold a_swap.
  unfold bottom_to_top.
  simpl.
  cleanup_zx.
  simpl_casts.
  bundle_wires.
  cleanup_zx.
  easy.
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
  remember (⟦ (top_to_bottom_helper n) ⊤%ZX ⟧) as ZX_tb_t.
  remember (⟦ top_to_bottom_helper n ⟧) as ZX_tb.
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

Lemma a_swap_transpose : forall n,
  (a_swap n) ⊤ ∝ a_swap n.
Proof.
  intros.
  strong induction n.
  destruct n; [ easy | ].
  destruct n; [ simpl; cleanup_zx; simpl_casts; easy | ].
  destruct n; [ rewrite a_swap_2_is_swap; easy | ].
  rewrite a_swap_grow.
Local Opaque a_swap.
  simpl.
  repeat rewrite n_wire_transpose.
  rewrite compose_assoc.
  rewrite H by lia.
  easy.
Qed.

(* n_swap proofs *)

Opaque a_swap a_swap_semantics. (* For n_swap proofs we don't want a_swap to unfold, instead we use lemmata from above*)

Lemma n_swap_2_is_swap : n_swap 2 ∝ ⨉.
Proof.
  intros.
  simpl.
  unfold bottom_to_top.
  simpl.
  cleanup_zx.
  simpl_casts.
  bundle_wires.
  cleanup_zx.
  easy.
Qed.

Lemma n_swap_1_is_wire : n_swap 1 ∝ —.
Proof.
  simpl.
  cleanup_zx.
  simpl_casts.
  easy.
Qed.

Lemma n_swap_grow_l : forall n,
  n_swap (S n) ∝ bottom_to_top (S n) ⟷ (— ↕ n_swap n).
Proof.
  induction n.
  - simpl.
    cleanup_zx.
    easy.
  - simpl.
    easy.
Qed.

Lemma n_swap_grow_r : forall n,
  n_swap (S n) ∝ (— ↕ n_swap n) ⟷ top_to_bottom (S n).
Proof.
  induction n.
  - simpl.
    cleanup_zx.
    easy.
  - simpl.
    fold (top_to_bottom (S n)).
    rewrite <- (n_swap_grow_l n).
    rewrite IHn at 1.
    rewrite bottom_to_top_grow_r.
    rewrite stack_wire_distribute_l.
    rewrite (stack_assoc_back — —).
    simpl_casts.
    bundle_wires.
    repeat rewrite compose_assoc.
    rewrite <- (compose_assoc (⨉ ↕ n_wire n)).
    rewrite (nwire_stack_compose_botleft ⨉ (n_swap n)).
    rewrite <- (nwire_stack_compose_topleft (n_swap n) ⨉).
    repeat rewrite <- compose_assoc.
    simpl.
    cleanup_zx.
    simpl_casts.
    rewrite stack_wire_distribute_l.
    repeat rewrite compose_assoc.
    rewrite (stack_assoc_back — — (n_swap _)).
    cleanup_zx.
    simpl_casts.
    easy.
Unshelve.
all: lia.
Qed.

Lemma n_swap_transpose : forall n,
  (n_swap n) ⊤ ∝ n_swap n.
Proof.
  induction n; try easy.
  - simpl.
    rewrite IHn.
    unfold bottom_to_top at 1.
    rewrite Proportional.transpose_involutive.
    rewrite <- n_swap_grow_l.
    rewrite <- n_swap_grow_r.
    easy.
Qed.

#[export] Hint Rewrite
  (fun n => @bottom_to_top_transpose n)
  (fun n => @top_to_bottom_transpose n)
  (fun n => @n_swap_transpose n)
  (fun n => @a_swap_transpose n)
  : transpose_db.

Lemma top_to_bottom_colorswap : forall n,
  ⊙ (top_to_bottom n) ∝ top_to_bottom n.
Proof.
  destruct n; [ easy | ].
  induction n.
  - easy.
  - simpl.
    fold (top_to_bottom (S n)).
    rewrite IHn.
    rewrite n_wire_colorswap.
    easy.
Qed.

Lemma bottom_to_top_colorswap : forall n,
  ⊙ (bottom_to_top n) ∝ bottom_to_top n.
Proof.
  destruct n; [easy | ].
  induction n.
    - easy.
    - unfold bottom_to_top.
      rewrite top_to_bottom_grow_l.
      simpl.
      fold (top_to_bottom (S n)).
      fold (bottom_to_top (S n)).
      rewrite IHn.
      rewrite n_wire_transpose.
      rewrite n_wire_colorswap.
      easy.
Qed.

Lemma a_swap_colorswap : forall n,
  ⊙ (a_swap n) ∝ a_swap n.
Proof.
  induction n.
  - easy.
  - Local Transparent a_swap.
    simpl.
    rewrite bottom_to_top_colorswap.
    rewrite top_to_bottom_colorswap.
    easy.
Qed.

Lemma n_swap_colorswap : forall n,
  ⊙ (n_swap n) ∝ n_swap n.
Proof.
  induction n.
  - easy.
  - simpl.
    rewrite IHn.
    rewrite bottom_to_top_colorswap.
    easy.
Qed.

#[export] Hint Rewrite
  (fun n => @bottom_to_top_colorswap n)
  (fun n => @top_to_bottom_colorswap n)
  (fun n => @a_swap_colorswap n)
  (fun n => @n_swap_colorswap n)
  : colorswap_db.

Lemma swap_pullthrough_top_right_Z_1_1 : forall α, (Z 1 1 α) ↕ — ⟷ ⨉ ∝ ⨉ ⟷ (— ↕ (Z 1 1 α)).
Proof. intros. solve_prop 1. Qed.


Lemma swap_pullthrough_top_right_Z : forall n α prfn prfm, ((Z (S n) 1 α) ↕ —) ⟷ ⨉ ∝ cast _ _ prfn prfm (n_swap _ ⟷ (— ↕ (Z (S n) 1 α))).
Proof.
  intro n.
  induction n; intros.
  - simpl_casts.
    cleanup_zx.
    rewrite n_swap_2_is_swap.
    rewrite swap_pullthrough_top_right_Z_1_1.
    easy.
  - rewrite SpiderInduction.grow_Z_left_2_1 at 1.
    rewrite stack_wire_distribute_r.
    rewrite compose_assoc.
    rewrite IHn.
    simpl_casts.
    rewrite n_swap_grow_l.
    rewrite compose_assoc.
    rewrite (cast_compose_mid_contract _ (S (S n))).
    simpl_casts.
    rewrite (stack_assoc (Z 2 1 _) (n_wire n) —).
    bundle_wires.
    rewrite bottom_to_top_grow_r.
    simpl_casts.
    rewrite (cast_compose_mid (S (S n))).
    erewrite <- (@cast_n_wire (S n)).
    rewrite cast_stack_r.
    rewrite cast_contract.
    simpl_casts.
    erewrite (cast_compose_mid_contract _ (S (S n)) _ _ _ _ _ _ _ (— ↕ bottom_to_top (S n)) (⨉ ↕ n_wire n)).
    simpl_casts.
Abort.


Lemma swap_pullthrough_top_right_X_1_1 : forall α, (X 1 1 α) ↕ — ⟷ ⨉ ∝ ⨉ ⟷ (— ↕ (X 1 1 α)).
Proof. intros. colorswap_of swap_pullthrough_top_right_Z_1_1. Qed.
  

  Lemma ohno : forall prfn prfm, ⦰ ∝ (cast _ _ prfn prfm —).
  Proof.
    intros; exfalso; easy.
  Qed.
