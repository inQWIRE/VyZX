Require Export ZXCore Proportional.
Require Import CapCup Gadgets.


(* The Choi-Jamiolchosky isomorphism *)

Definition proc_to_state {n m} (zx : ZX n m) : ZX 0 (n + m) :=
  n_cap n ⟷ (n_wire n ↕ zx).

Definition state_to_proc {n m} (zx : ZX 0 (n + m)) : ZX n m :=
  cast _ _ (eq_sym (Nat.add_0_r _)) 
    (eq_sym (Nat.add_assoc _ _ _)) 
    (n_wire n ↕ zx) ⟷ (n_cup n ↕ n_wire m).

Import Setoid. 

Add Parametric Morphism {n m} : (@proc_to_state n m) 
  with signature proportional_by_1 ==> proportional_by_1 as proc_to_state_mor.
Proof.
  unfold proc_to_state.
  now intros czx czx' ->.
Qed.

Add Parametric Morphism {n m} : (@state_to_proc n m) 
  with signature proportional_by_1 ==> proportional_by_1 as state_to_proc_mor.
Proof.
  unfold state_to_proc.
  now intros czx czx' ->.
Qed.



Definition state_0 : ZX 0 1 := zx_invsqrt2 ↕ X 0 1 0.

Lemma state_0_defn' : 
  state_0 = zx_invsqrt2 ↕ X 0 1 0. 
Proof. reflexivity. Qed.

(* Don't want this to reduce, ever. *)
Global Opaque state_0.

Definition state_1 : ZX 0 1 := zx_invsqrt2 ↕ X 0 1 PI.

Lemma state_1_defn' : 
  state_1 = zx_invsqrt2 ↕ X 0 1 PI. 
Proof. reflexivity. Qed.

(* Don't want this to reduce, ever. *)
Global Opaque state_1.

Definition state_plus : ZX 0 1 := zx_invsqrt2 ↕ Z 0 1 0.

Lemma state_plus_defn' : 
  state_plus = zx_invsqrt2 ↕ Z 0 1 0. 
Proof. reflexivity. Qed.
  
(* Don't want this to reduce, ever. *)
Global Opaque state_plus.

Definition state_minus : ZX 0 1 := zx_invsqrt2 ↕ Z 0 1 PI.

Lemma state_minus_defn' : 
  state_minus = zx_invsqrt2 ↕ Z 0 1 PI. 
Proof. reflexivity. Qed.

(* Don't want this to reduce, ever. *)
Global Opaque state_minus.


Definition state_b (b : bool) := if b then state_1 else state_0.

Lemma state_b_defn' b : state_b b = 
  zx_invsqrt2 ↕ X 0 1 (if b then PI else 0).
Proof.
  unfold state_b.
  rewrite state_0_defn', state_1_defn'.
  now destruct b.
Qed.

Fixpoint f_to_state n (f : nat -> bool) : ZX 0 n :=
  match n with 
  | 0 => ⦰
  | S n' => state_b (f O) ↕ f_to_state n' (fun i => f (1 + i)%nat)
  end.



Definition uniform_state n : ZX 0 n :=
  cast _ _ (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_1_r _))
    (n_stack n (Z 0 1 0)).