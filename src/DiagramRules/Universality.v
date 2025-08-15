Require Import CoreRules.

(** Universality of ZX-diagrams *)

Theorem universality {n m} : forall (A : Matrix (2^m) (2^n)), WF_Matrix A -> 
  exists (zx : ZX n m), ⟦ zx ⟧ = A.
Proof.
  intros A HA.
  exists (zx_of_matrix A).
  now apply zx_of_matrix_semantics.
Qed.
