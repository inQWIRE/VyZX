Require Import CoreData.CoreData.
Require Import CoreAutomation.

Lemma cup_Z : ⊃ ∝ 𝒵 2 0 0.
Proof.
  prop_exists_nonzero 1.
  Msimpl; simpl.
  solve_matrix.
  autorewrite with Cexp_db; easy.
Qed.

Lemma cap_Z : ⊂ ∝ 𝒵 0 2 0.
Proof.
  prop_exists_nonzero 1.
  Msimpl; simpl.
  solve_matrix.
  autorewrite with Cexp_db; easy.
Qed.

Lemma cup_X : ⊃ ∝ 𝒳 2 0 0.
Proof. colorswap_of cup_Z. Qed. 

Lemma cap_X : ⊂ ∝ 𝒳 0 2 0.
Proof. colorswap_of cap_Z. Qed. 