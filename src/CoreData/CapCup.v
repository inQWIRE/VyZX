Require Import ZXCore.
Require Import Swaps.
Require Export QuantumLib.Quantum.
Require Export QuantumLib.Permutations.

Local Open Scope ZX_scope.

Lemma n_cup_dim : forall n, ((S n) + (S n) = 1 + (n +n) + 1)%nat.
Proof. lia. Qed.

Fixpoint n_cup_unswapped (n : nat) : ZX (n + n) 0 :=
  match n with
  | 0 => ⦰
  | (S n) => @Compose ((S n) + (S n))%nat (2)%nat _ 
              (cast _ _ (n_cup_dim _) (eq_refl) (— ↕ (n_cup_unswapped n) ↕ —))
              ⊃
  end.

Definition n_cup n := (n_swap (n) ↕ n_wire n) ⟷ (n_cup_unswapped n).

Definition n_cap n := (n_cup n) ⊤.

