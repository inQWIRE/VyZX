Require Import CoreData.
Require Import WireRules.
Require Import CoreAutomation.
Require Import StackComposeRules.
Require Import CastRules.


Lemma swap_compose :
  ⨉ ⟷ ⨉ ∝ n_wire 2.
Proof. solve_prop 1. Qed.



Fixpoint top_to_bottom_helper (n : nat) : ZX (S n) (S n) :=
  match n with 
  | 0   => Wire
  | S k => Compose (Stack Swap (n_wire k)) (Stack Wire (top_to_bottom_helper k))
  end.

Definition top_to_bottom (n : nat) : ZX n n :=
  match n with
  | 0 => Empty
  | S k => top_to_bottom_helper k
  end.

Definition bottom_to_top (n : nat) : ZX n n :=
  (top_to_bottom n)⊤.

Definition a_swap (n : nat) : ZX n n :=
  match n with
  | 0   => Empty
  | S k => bottom_to_top (S k) ⟷ (— ↕ top_to_bottom k)
  end.

(* Arbitrary Swap Semantics *)

(* A linear mapping which takes | x y1 ... yn > -> | y1 .. yn x > *)
Fixpoint top_wire_to_bottom (n : nat) : Square (2 ^ n) :=
  match n with
  | 0   => I 1
  | S k => match k with
           | 0   => I 2
           | S j => (@Mmult _ (2^n) _) ((I 2) ⊗ (top_wire_to_bottom k)) (swap ⊗ (j ⨂ (I 2)))
           end
  end.

Open Scope matrix_scope.
Definition bottom_wire_to_top (n : nat) : Square (2 ^ n) :=
  (top_wire_to_bottom n)⊤.

Definition a_swap_semantics (n : nat) : Square (2 ^ n) :=
  match n with
  | 0   => I 1
  | S k => (@Mmult _ (2 ^ n) _ ((I 2) ⊗ top_wire_to_bottom (k)) ((bottom_wire_to_top (S k))))
  end.

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

(* Well foundedness of semantics *)

Lemma WF_top_to_bottom (n : nat) : WF_Matrix (top_wire_to_bottom n).
Proof.
  destruct n; try auto with wf_db.
  induction n.
  - simpl; auto with wf_db.
  - simpl. try auto with wf_db.
Qed.

Global Hint Resolve WF_top_to_bottom : wf_db.

Lemma WF_bottom_to_top (n : nat) : WF_Matrix (bottom_wire_to_top n).
Proof. unfold bottom_wire_to_top. auto with wf_db. Qed.

Global Hint Resolve WF_bottom_to_top : wf_db.

Lemma WF_a_swap_semantics (n : nat) :
 WF_Matrix (a_swap_semantics n).
Proof.
  intros.
  unfold a_swap_semantics.
  destruct n; auto with wf_db.
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

Definition n_swap := Z 1 1 0.