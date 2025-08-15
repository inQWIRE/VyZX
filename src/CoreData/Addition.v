Require Import ZXCore CapCup States Gadgets Controlizer.
Import Setoid.

Definition zx_plus {n m} (zx0 zx1 : ZX n m) : ZX n m :=
  cast 0 0 (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_0_r _)) ((n + m) ⇑ zx_invsqrt2) ↕
  state_to_proc (state_1 ⟷ sum_controlizer (controlizer zx0) (controlizer zx1)).

Lemma zx_plus_defn {n m} (zx0 zx1 : ZX n m) :
  zx_plus zx0 zx1 = 
  cast 0 0 (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_0_r _)) ((n + m) ⇑ zx_invsqrt2) ↕
  state_to_proc (state_1 ⟷ sum_controlizer (controlizer zx0) (controlizer zx1)).
Proof. reflexivity. Qed.

(* We don't want reduction to unfold zx_plus *)
Global Opaque zx_plus.

Notation "zx0 .+ zx1" := (zx_plus zx0 zx1) 
  (at level 50, left associativity) : ZX_scope.

(* TODO: When/if the [Monoid] typeclass in Qlib no longer requires
  leibnix equality, this can be replaced *)
Fixpoint zx_sum {n m} (f : nat -> ZX n m) k : ZX n m :=
  match k with 
  | O => 0
  | 1 => f O
  | S k' => zx_sum f k' .+ f k'
  end.


Definition state_of_vector {n} (v : Vector (2^n)) : ZX 0 n :=
  zx_sum (fun i => 
    v i O .* f_to_state n (nat_to_funbool n i)) (2^n).

Definition zx_of_matrix {n m} (A : Matrix (2^m) (2^n)) : ZX n m :=
  state_to_proc (state_of_vector 
    (@Mmult _ (2^(n+n)) _ (I (2^n) ⊗ A) (⟦ n_cap n ⟧))).