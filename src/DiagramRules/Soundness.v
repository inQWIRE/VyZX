From QuantumLib Require Complex Matrix RealAux Polar.

From VyZX Require Import CoreRules.

Local Open Scope matrix_scope.

Theorem soundness {n m} (zx0 zx1 : ZX n m) : 
  zx0 ∝ zx1 -> 
  exists c, ⟦ zx0 ⟧ = c .* ⟦ zx1 ⟧ /\ c <> C0.
Proof.
  intros (c & Hc)%propotional_to_prop_by_sig.
  exists c.
  apply Hc.
Qed.