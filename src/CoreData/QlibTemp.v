From QuantumLib Require Import Matrix.

Lemma transpose_matrices : forall {n m} (A B : Matrix n m),
  A ⊤ = B ⊤ -> A = B.
Proof.
  intros.
  rewrite <- transpose_involutive.
  rewrite <- H.
  rewrite transpose_involutive.
  easy.
Qed.

Lemma adjoint_matrices : forall {n m} (A B : Matrix n m),
  A † = B † -> A = B.
Proof.
  intros.
  rewrite <- adjoint_involutive.
  rewrite <- H.
  rewrite adjoint_involutive.
  easy.
Qed.
