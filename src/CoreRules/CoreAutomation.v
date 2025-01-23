Require Import ComposeRules.
Require Import CastRules.
Require Import StackRules.
Require Import WireRules.
Require Import StackComposeRules.

(** Combine stacks of [n_wire] and [—] ([Wire]), restoring
  [n_wire 1] to [—] at the end. *)
Ltac bundle_wires := 
  rewrite ?wire_to_n_wire, ?n_wire_stack, <- 1?wire_to_n_wire.

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
  box_compose
  (fun n m o p => @nwire_stack_compose_topleft n m o p)
  (fun n m o p => @nwire_stack_compose_botleft n m o p)
  : cleanup_zx_db.

(** Simplify the goal by [autorewrite with cleanup_zx_db], solving
  as many side-conditions as possible with [lia]. *)
Ltac cleanup_zx := auto_cast_eqn (autorewrite with cleanup_zx_db).

#[export] Hint Rewrite
  (fun n m o p => @cast_colorswap n m o p)
  (fun n => @n_wire_colorswap n)
  (fun n => @nstack1_colorswap n)
  (fun n m o => @nstack_colorswap n m o)
  : colorswap_db.

#[export] Hint Rewrite
  (fun n m o p => @cast_transpose n m o p)
  (fun n => @n_wire_transpose n)
  (fun n => @nstack1_transpose n)
  (fun n => @nstack_transpose n)
  : transpose_db.

#[export] Hint Rewrite
  (fun n m o p => @cast_adj n m o p)
  : adjoint_db.

(** Solve the goal by showing it is the transpose of the term/lemma [H]. 
  Specifically, transposes the goal, e.g. by applying [transpose_digrams], 
  simplifies by [autorewrite with transpose_db] and [simpl], and applies [H]. *)
Ltac transpose_of H := 
  intros;
  first [apply transpose_diagrams
   | apply transpose_diagrams_by 
   | apply transpose_diagrams_eq 
   | apply transpose_zx]; 
  repeat (simpl; autorewrite with transpose_db); 
  apply H.

(** Solve the goal by showing it is the adjoint of the term [H]. 
  Specifically, adjoints the goal, e.g. by applying [adjoint_digrams], 
  simplifies by [autorewrite with adjoint_db] and [simpl], and applies [H]. *)
Ltac adjoint_of H := 
  intros;
  first [apply adjoint_diagrams
    | apply adjoint_diagrams_by 
    | apply adjoint_diagrams_eq 
    | apply adjoint_zx]; 
  repeat (simpl; autorewrite with adjoint_db); 
  apply H.

(** Solve the goal by showing it is the colorswap of the term [H]. 
  Specifically, colorswaps the goal, e.g. by applying [colorswap_digrams], 
  simplifies by [autorewrite with colorswap_db] and [simpl], and applies [H]. *)
Ltac colorswap_of H := 
  intros;
  first [apply colorswap_diagrams
   | apply colorswap_diagrams_by 
   | apply colorswap_diagrams_eq 
   | apply colorswap_zx]; 
  repeat (simpl; autorewrite with colorswap_db); 
  apply H.
