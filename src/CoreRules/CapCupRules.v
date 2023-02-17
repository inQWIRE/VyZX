Require Import CoreData.CoreData.
Require Import CoreAutomation.

Lemma Cup_Z : ⊃ ∝ Z 2 0 0.
Proof.
  prop_exists_nonzero 1.
  Msimpl; simpl.
  solve_matrix.
  autorewrite with Cexp_db; easy.
Qed.

Lemma Cap_Z : ⊂ ∝ Z 0 2 0.
Proof.
  prop_exists_nonzero 1.
  Msimpl; simpl.
  solve_matrix.
  autorewrite with Cexp_db; easy.
Qed.

Lemma Cup_X : ⊃ ∝ X 2 0 0.
Proof. colorswap_of Cup_Z. Qed. 

Lemma Cap_X : ⊂ ∝ X 0 2 0.
Proof. colorswap_of Cap_Z. Qed. 