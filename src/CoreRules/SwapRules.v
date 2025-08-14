Require Import QuantumLib.Kronecker QuantumLib.Modulus. 
Require Import CoreData.
Require Import WireRules.
Require Import CoreAutomation.
Require Import StackComposeRules.
Require Import CastRules.
Require Import ZXpermFacts.

Lemma swap_compose :
  ⨉ ⟷ ⨉ ∝= n_wire 2.
Proof. 
  by_perm_eq_nosimpl; by_perm_cell; reflexivity.
Qed.

Global Hint Rewrite swap_compose : cleanup_zx_db.

Lemma top_wire_to_bottom_ind : forall n, top_wire_to_bottom (S (S n)) = 
  @Mmult _ (2 ^ (S (S n))) _ ((I 2) ⊗ top_wire_to_bottom (S n)) (swap ⊗ (I (2 ^ n))).
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
  - cbn.
    simpl in IHn.
    rewrite <- IHn.
    fold (n_wire n).
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
  prep_matrix_equivalence.
  by_cell; lazy; lca.
Qed.

Lemma top_to_bottom_grow_l : forall n, 
  top_to_bottom (S (S n)) = (⨉ ↕ n_wire n) ⟷ (— ↕ top_to_bottom (S n)).
Proof. reflexivity. Qed.

Lemma top_to_bottom_grow_r : forall n prf prf', 
  top_to_bottom (S (S n)) ∝= 
  cast _ _ prf' prf' (top_to_bottom (S n) ↕ —) ⟷ 
    (cast _ _ prf prf (n_wire n ↕ ⨉)).
Proof.
  intros.
  by_perm_eq_nosimpl.
  rewrite perm_of_top_to_bottom_eq.
  cbn.
  rewrite 2!perm_of_zx_cast.
  cbn.
  rewrite perm_of_top_to_bottom_helper_eq, perm_of_n_wire.
  intros i Hi.
  rewrite stack_perms_WF_idn by cleanup_perm.
  rewrite stack_perms_idn_f.
  unfold compose.
  bdestructΩ';
  unfold top_to_bottom_perm; [bdestructΩ'|].
  unfold swap_2_perm, swap_perm.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.



Lemma offset_swaps_comm_top_left : 
  ⨉ ↕ — ⟷ (— ↕ ⨉) ∝=
  — ↕ ⨉ ⟷ (⨉ ↕ —) ⟷ (— ↕ ⨉) ⟷ (⨉ ↕ —).
Proof.
  by_perm_eq_nosimpl.
  by_perm_cell; reflexivity.
Qed.

Lemma offset_swaps_comm_bot_right : 
 — ↕ ⨉ ⟷ (⨉ ↕ —)  ∝=
 ⨉ ↕ — ⟷ (— ↕ ⨉) ⟷ (⨉ ↕ —) ⟷ (— ↕ ⨉). 
Proof. 
  by_perm_eq_nosimpl.
  by_perm_cell; reflexivity.
Qed.

Lemma bottom_wire_to_top_ind : forall n, 
  bottom_wire_to_top (S (S n)) = 
  @Mmult _ (2 ^ (S (S n))) _ (swap ⊗ (I (2 ^ n))) 
    ((I 2) ⊗ bottom_wire_to_top (S n)).
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
  bottom_to_top (S (S n)) = (— ↕ bottom_to_top (S n)) ⟷ (⨉ ↕ n_wire n).
Proof.
  intros.
  unfold bottom_to_top.
  simpl.
  rewrite n_wire_transpose.
  easy. 
Qed.


Lemma bottom_to_top_grow_l : forall n prf prf', 
  bottom_to_top (S (S n)) ∝= cast _ _ prf' prf'((cast _ _ prf prf (n_wire n ↕ ⨉)) ⟷ (bottom_to_top (S n) ↕ —)).
Proof.
  intros.
  apply transpose_diagrams_eq.
  unfold bottom_to_top.
  rewrite cast_transpose.
  cbn -[top_to_bottom].
  repeat rewrite cast_transpose.
  cbn -[top_to_bottom].
  rewrite n_wire_transpose.
  repeat rewrite Proportional.transpose_involutive.
  rewrite top_to_bottom_grow_r.
  rewrite cast_compose_distribute.
  simpl_casts.
  erewrite (cast_compose_mid (S (n + 1))).
  simpl_casts.
  apply compose_simplify_eq; cast_irrelevance.
Unshelve.
all: lia.
Qed.

Lemma top_to_bottom_transpose : forall n, (top_to_bottom n)⊤ = bottom_to_top n.
Proof.
  reflexivity.
Qed.

Lemma bottom_to_top_transpose : forall n, (bottom_to_top n)⊤ = top_to_bottom n.
Proof.
  intros.
  unfold bottom_to_top.
  rewrite Proportional.transpose_involutive_eq.
  easy.
Qed.

Lemma a_swap_grow : forall n, a_swap (S (S (S n))) ∝= 
  (⨉ ↕ n_wire (S n)) ⟷ (— ↕ a_swap (S (S n))) ⟷ (⨉ ↕ n_wire (S n)). 
Proof.
  intros.
  by_perm_eq_nosimpl.
  cbn -[a_swap n_stack1].
  rewrite 2!perm_of_a_swap, perm_of_n_wire.
  rewrite 2!swap_perm_defn by lia.
  rewrite (stack_perms_defn 1).
  rewrite stack_perms_WF_idn by cleanup_perm.
  unfold swap_2_perm, swap_perm.
  intros i Hi.
  unfold compose at 1.
  bdestructΩ'; unfold compose; bdestructΩ'.
Qed.

Lemma a_swap_2_is_swap : a_swap 2 ∝= ⨉.
Proof.
  by_perm_eq_nosimpl; by_perm_cell; reflexivity.
Qed.


Lemma a_swap_3_order_indep :
  I 2 ⊗ swap × (swap ⊗ I 2) × (I 2 ⊗ swap) = 
  (swap ⊗ I 2) × (I 2 ⊗ swap) × (swap ⊗ I 2).
Proof.
  rewrite swap_eq_kron_comm.
  change 2%nat with (2^1)%nat.
  rewrite <- perm_to_matrix_idn.
  rewrite kron_comm_pows2_eq_perm_to_matrix_big_swap.
  restore_dims.
  rewrite <- !perm_to_matrix_of_stack_perms by auto with perm_db.
  restore_dims.
  rewrite <- !perm_to_matrix_compose by auto with perm_db.
  apply perm_to_matrix_eq_of_perm_eq.
  by_perm_cell; reflexivity.
Qed.

Lemma a_swap_semantics_ind : forall n, a_swap_semantics (S (S (S n))) = 
  swap ⊗ (I (2 ^ (S n))) × (I 2 ⊗ a_swap_semantics (S (S n))) × (swap ⊗ (I (2 ^ (S n)))).
Proof.
  intros n.
  rewrite <- a_swap_correct.
  rewrite <- n_wire_semantics.
  change (I 2) with (⟦ — ⟧).
  rewrite <- a_swap_correct.
  change (swap ⊗ ⟦n_wire (S n)⟧) with
    (⟦ ⨉ ↕ n_wire (S n)⟧).
  restore_dims.
  change (⟦ a_swap (S (S (S n))) ⟧ = ⟦
    (⨉ ↕ n_wire (S n)) ⟷ ((— ↕ a_swap (S (S n)))
    ⟷ (⨉ ↕ n_wire (S n))) ⟧).
  rewrite 2!perm_of_zx_permutation_semantics by auto_zxperm.
  apply perm_to_matrix_eq_of_perm_eq.
  cbn [perm_of_zx].
  rewrite perm_of_n_wire, 2!perm_of_a_swap.
  rewrite swap_perm_defn by lia.
  rewrite stack_perms_idn_f, stack_perms_WF_idn by auto_perm.
  unfold swap_2_perm.
  intros k Hk.
  rewrite <- Combinators.compose_assoc.
  unfold compose at 1.
  bdestruct (k =? 0); 
  [unfold swap_perm; bdestructΩ'; 
    unfold compose; bdestructΩ'|].
  bdestruct (k =? 1); 
  [unfold swap_perm; bdestructΩ'; 
    unfold compose; bdestructΩ'|].
  unfold swap_perm.
  simplify_bools_lia_one_kernel.
  unfold compose.
  bdestructΩ'.
Qed. 

Lemma a_swap_transpose : forall n,
  (a_swap n) ⊤ ∝= a_swap n.
Proof.
  by_perm_eq_nosimpl.
  rewrite perm_of_zx_transpose by auto with zxperm_db.
  rewrite perm_of_a_swap.
  bdestruct (n =? 0); [subst; now intros i Hi|].
  rewrite swap_perm_inv' by lia.
  easy.
Qed.

(* n_swap proofs *)

Opaque a_swap a_swap_semantics. (* For n_swap proofs we don't want a_swap to unfold, instead we use lemmata from above*)

Lemma n_swap_2_is_swap : n_swap 2 ∝= ⨉.
Proof.
  by_perm_eq_nosimpl.
  by_perm_cell; reflexivity.
Qed.

Lemma n_swap_1_is_wire : n_swap 1 ∝= —.
Proof.
  by_perm_eq_nosimpl.
  by_perm_cell; reflexivity.
Qed.

Lemma n_swap_grow_l : forall n,
  n_swap (S n) ∝= bottom_to_top (S n) ⟷ (— ↕ n_swap n).
Proof.
  induction n.
  - simpl.
    cleanup_zx.
    easy.
  - reflexivity.
Qed.

Lemma n_swap_grow_r : forall n,
  n_swap (S n) ∝= (— ↕ n_swap n) ⟷ top_to_bottom (S n).
Proof.
  by_perm_eq.
  rewrite !reflect_perm_defn, stack_perms_defn.
  change (S n) with (1 + n)%nat.
  rewrite (rotr_add_l 1 n).
  unfold big_swap_perm, compose.
  intros i Hi.
  bdestructΩ'.
Qed.

Lemma n_swap_transpose : forall n,
  (n_swap n) ⊤ ∝= n_swap n.
Proof.
  intros.
  by_perm_eq.
Qed.

#[export] Hint Rewrite
  (fun n => @bottom_to_top_transpose n)
  (fun n => @top_to_bottom_transpose n)
  (fun n => @n_swap_transpose n)
  (fun n => @a_swap_transpose n)
  : transpose_db.

Lemma top_to_bottom_colorswap : forall n,
  ⊙ (top_to_bottom n) = top_to_bottom n.
Proof.
  intros n.
  now rewrite zxperm_colorswap_eq by auto with zxperm_db.
Qed.

Lemma bottom_to_top_colorswap : forall n,
  ⊙ (bottom_to_top n) = bottom_to_top n.
Proof.
  intros n.
  now rewrite zxperm_colorswap_eq by auto with zxperm_db.
Qed.

Lemma a_swap_colorswap : forall n,
  ⊙ (a_swap n) = a_swap n.
Proof.
  intros n.
  now rewrite zxperm_colorswap_eq by auto with zxperm_db.
Qed.

Lemma n_swap_colorswap : forall n,
  ⊙ (n_swap n) = n_swap n.
Proof.
  intros n.
  now rewrite zxperm_colorswap_eq by auto with zxperm_db.
Qed.

#[export] Hint Rewrite
  (fun n => @bottom_to_top_colorswap n)
  (fun n => @top_to_bottom_colorswap n)
  (fun n => @a_swap_colorswap n)
  (fun n => @n_swap_colorswap n)
  : colorswap_db.

Lemma swap_pullthrough_top_right_Z_1_1 : forall α, (Z 1 1 α) ↕ — ⟷ ⨉ ∝= ⨉ ⟷ (— ↕ (Z 1 1 α)).
Proof. 
  intros.
  rewrite <- zx_comm_1_1_swap.
  now rewrite zx_comm_commutes_r.
Qed.


Lemma swap_pullthrough_top_right_X_1_1 : forall α, 
  (X 1 1 α) ↕ — ⟷ ⨉ ∝= ⨉ ⟷ (— ↕ (X 1 1 α)).
Proof. intros. colorswap_of swap_pullthrough_top_right_Z_1_1. Qed.

