Require Import ZXCore.
Require Export QuantumLib.Quantum.

Open Scope ZX_scope.

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

Fixpoint n_swap (n : nat) : ZX n n :=
  match n with 
  | 0 => ⦰ 
  | 1 => —
  | (S (S n)) => a_swap (S (S n)) ⟷ (— ↕ (@cast _ _ (n + 1)%nat (n + 1)%nat (eq_sym (@Nat.add_1_r n)) (eq_sym (@Nat.add_1_r n)) (n_swap n ↕ —)))
  end.
  
  