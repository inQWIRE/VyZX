Require Import ZXCore CapCup States Gadgets Controlizer.
Import Setoid.

(** Definitions about sums of ZX-diagrams, using controlizers *)

(* The sum of two ZX-diagrams, defined using controlizers *)
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
  leibnix equality and uses setoids, this can be replaced *)
(* The indexed sum of a list of ZX-diagrams *)
Fixpoint zx_sum {n m} (f : nat -> ZX n m) k : ZX n m :=
  match k with 
  | O => zx_zero
  | 1 => f O
  | S k' => zx_sum f k' .+ f k'
  end.

(* A ZX-diagram whose semantics are those of a given vector *)
Definition state_of_vector {n} (v : Vector (2^n)) : ZX 0 n :=
  zx_sum (fun i => 
    v i O .* f_to_state n (nat_to_funbool n i)) (2^n).

(* TODO: figure out the exact vector used (mx_to_vec A?). Not critical, 
  but it would be better *)
(* A ZX-diagram whose semantics are those of a given matrix *)
Definition zx_of_matrix {n m} (A : Matrix (2^m) (2^n)) : ZX n m :=
  state_to_proc (state_of_vector 
    (@Mmult _ (2^(n+n)) _ (I (2^n) ⊗ A) (⟦ n_cap n ⟧))).

(* An alternate definition of a ZX-diagram, whose semantic is 
  a given matrix, which does not use the Choi-Jamiolchosky isomorphism *)
Definition zx_of_matrix' {n m} (A : Matrix (2^m) (2^n)) : ZX n m :=
  zx_sum (fun i => 
    zx_sum (fun j => 
    A i j .* 
    ((f_to_state n (nat_to_funbool n j)) ⊤ ⟷ 
    f_to_state m (nat_to_funbool m i))
    )%ZX (2^n)) (2^m).