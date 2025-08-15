Require Import ZXCore.

(** Definitions involving arbitrary stacks *)

(* TODO: Move n_stack / n_stack1 / n_wire / n_box in here *)

Definition associator n m o : ZX (n + m + o) (n + (m + o)) :=
  cast _ _ eq_refl (Nat.add_assoc _ _ _) (n_wire _).

Definition invassociator n m o : ZX (n + (m + o)) (n + m + o) :=
  cast _ _ (Nat.add_assoc _ _ _) eq_refl (n_wire _).
