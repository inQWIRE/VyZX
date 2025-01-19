Require Import ComposeRules.
Require Import CastRules.
Require Import StackRules.
Require Import WireRules.
Require Import StackComposeRules.

Ltac wire_to_n_wire_safe_aux zx :=
  match zx with
  | ?n ↑ — => idtac (* Guards from recursively unfolding n_wire into (n ↑ (n_wire 1)) *)
  | ?n ↑ ?zx => wire_to_n_wire_safe_aux zx
  | ?zx1 ↕ ?zx2 => wire_to_n_wire_safe_aux zx1; wire_to_n_wire_safe_aux zx2
  | ?zx1 ⟷ ?zx2 => wire_to_n_wire_safe_aux zx1; wire_to_n_wire_safe_aux zx2
  | — => rewrite wire_to_n_wire
  | cast _ _ _ _ ?zx => wire_to_n_wire_safe_aux zx
  | _ => idtac
  end.

Ltac wire_to_n_wire_safe := 
match goal with 
  | [ |- ?zx1 ∝ ?zx2] => try (wire_to_n_wire_safe_aux zx1); try (wire_to_n_wire_safe_aux zx2); repeat rewrite n_stack_n_wire_1_n_wire
end.

Tactic Notation "bundle_wires" := 
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

Ltac transpose_of H := 
  intros;
  first [apply transpose_diagrams
   | apply transpose_diagrams_by 
   | apply transpose_diagrams_eq 
   | apply transpose_zx]; 
  repeat (simpl; autorewrite with transpose_db); 
  apply H.

Ltac adjoint_of H := 
  intros;
  first [apply adjoint_diagrams
    | apply adjoint_diagrams_by 
    | apply adjoint_diagrams_eq 
    | apply adjoint_zx]; 
  repeat (simpl; autorewrite with adjoint_db); 
  apply H.

Ltac colorswap_of H := 
  intros;
  first [apply colorswap_diagrams
   | apply colorswap_diagrams_by 
   | apply colorswap_diagrams_eq 
   | apply colorswap_zx]; 
  repeat (simpl; autorewrite with colorswap_db); 
  apply H.
