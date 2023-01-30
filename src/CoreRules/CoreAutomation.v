Require Import ComposeRules.
Require Import StackRules.
Require Import WireRules.
Require Import StackComposeRules.

#[export] Hint Rewrite 
  (fun n => @ZX_Compose_Empty_l n)
  (fun n => @ZX_Compose_Empty_r n)
  (fun n => @ZX_Stack_Empty_l n)
  (fun n => @ZX_Stack_Empty_r n) 
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

Ltac transpose_of H := intros; apply transpose_diagrams; simpl; apply H.
Ltac adjoint_of H := intros; apply adjoint_diagrams; simpl; apply H.
Ltac colorswap_of H := intros; apply colorswap_diagrams; simpl; apply H.
