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