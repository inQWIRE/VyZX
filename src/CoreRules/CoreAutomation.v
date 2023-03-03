Require Import ComposeRules.
Require Import castRules.
Require Import StackRules.
Require Import WireRules.
Require Import StackComposeRules.

#[export] Hint Rewrite 
  (fun n => @compose_empty_l n)
  (fun n => @compose_empty_r n)
  (fun n => @stack_empty_l n)
  (fun n => @stack_empty_r n) 
  (fun n => @nwire_removal_l n) 
  (fun n => @nwire_removal_r n)
  @wire_removal_l
  @wire_removal_r
  X_0_is_wire
  Z_0_is_wire
  (fun n m o p => @nwire_stack_compose_topleft n m o p)
  (fun n m o p => @nwire_stack_compose_botleft n m o p)
  : cleanup_zx_db.
Ltac cleanup_zx := autorewrite with cleanup_zx_db.

#[export] Hint Rewrite
  (fun n m o p => @cast_colorswap n m o p)
  (fun n => @n_wire_colorswap n)
  (fun n => @n_stack1_colorswap n)
  (fun n m o => @n_stack_colorswap n m o)
  : colorswap_db.

#[export] Hint Rewrite
  (fun n m o p => @cast_transpose n m o p)
  (fun n => @n_wire_transpose n)
  (fun n => @n_stack1_transpose n)
  (fun n => @n_stack_transpose n)
  : transpose_db.

#[export] Hint Rewrite
  (fun n m o p => @cast_adj n m o p)
  : adjoint_db.

Ltac transpose_of H := intros; apply transpose_diagrams; repeat (simpl; autorewrite with transpose_db); apply H.
Ltac adjoint_of H := intros; apply adjoint_diagrams; repeat (simpl; autorewrite with adjoint_db); apply H.
Ltac colorswap_of H := intros; apply colorswap_diagrams; repeat (simpl; autorewrite with colorswap_db); apply H.
