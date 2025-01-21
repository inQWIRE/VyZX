From QuantumLib Require Import Matrix.
From QuantumLib Require Import Quantum.
Require Import QuantumLib.VectorStates.
Require Import QuantumLib.Permutations.


(* @nocheck name *)
(* Conventional name *)
Lemma Cdiv_0_l c : 0 / c = 0.
Proof. apply Cmult_0_l. Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Cdiv_nonzero_iff (c d : C) : 
  d / c <> 0 <-> c <> 0 /\ d <> 0.
Proof.
  rewrite Cdiv_integral_iff.
  tauto.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Cdiv_nonzero_iff_r (c d : C) : c <> 0 ->
  d / c <> 0 <-> d <> 0.
Proof.
  intros Hc.
  rewrite Cdiv_nonzero_iff.
  tauto.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Cmult_nonzero_iff (c d : C) : 
  c * d <> 0 <-> c <> 0 /\ d <> 0.
Proof.
  rewrite Cmult_integral_iff.
  tauto.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Cinv_div (c d : C) : 
  / (c / d) = d / c.
Proof.
  unfold Cdiv.
  rewrite Cinv_mult_distr, Cinv_inv.
  apply Cmult_comm.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Cdiv_div (b c d : C) : 
  b / (c / d) = b * d / c.
Proof.
  unfold Cdiv at 1.
  rewrite Cinv_div.
  apply Cmult_assoc.
Qed.

Local Open Scope nat_scope.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmult_vec_comm {n} (v u : Vector n) : WF_Matrix u -> WF_Matrix v ->
  v ⊤%M × u = u ⊤%M × v.
Proof.
  intros Hu Hv.
  prep_matrix_equivalence.
  by_cell.
  apply big_sum_eq_bounded.
  intros k Hk.
  unfold transpose.
  lca.
Qed.

Lemma kron_f_to_vec_eq {n m p q : nat} (A : Matrix (2^n) (2^m))
  (B : Matrix (2^p) (2^q)) (f : nat -> bool) : WF_Matrix A -> WF_Matrix B -> 
  A ⊗ B × f_to_vec (m + q) f
  = A × f_to_vec m f ⊗ (B × f_to_vec q (fun k : nat => f (m + k))).
Proof.
  intros.
  prep_matrix_equivalence.
  apply kron_f_to_vec.
Qed.

Lemma equal_on_basis_states_implies_equal' : (* FIXME: Replace 
  equal_on_basis_states_implies_equal with this *)
  forall {m dim : nat} (A B : Matrix m (2 ^ dim)),
  WF_Matrix A -> WF_Matrix B ->
  (forall f : nat -> bool, A × f_to_vec dim f = B × f_to_vec dim f) -> 
  A = B.
Proof.
  intros m dim A B HA HB HAB.
  prep_matrix_equivalence.
  intros i j Hi Hj.
  rewrite 2!(get_entry_with_e_i _ i j) by lia.
  rewrite 2!Mmult_assoc.
  rewrite <- (basis_vector_eq_e_i _ j) by assumption.
  rewrite basis_f_to_vec_alt by assumption.
  now rewrite HAB.
Qed.

Lemma equal_on_conj_basis_states_implies_equal {n m} 
  (A B : Matrix (2 ^ n) (2 ^ m)) : WF_Matrix A -> WF_Matrix B -> 
  (forall f g, (f_to_vec n g) ⊤%M × (A × f_to_vec m f) = 
    (f_to_vec n g) ⊤%M × (B × f_to_vec m f)) -> A = B.
Proof.
  intros HA HB HAB.
  apply equal_on_basis_states_implies_equal'; [auto..|].
  intros f.
  apply transpose_matrices.
  apply equal_on_basis_states_implies_equal'; [auto_wf..|].
  intros g.
  apply transpose_matrices.
  rewrite Mmult_transpose, transpose_involutive, HAB.
  rewrite Mmult_transpose, transpose_involutive.
  reflexivity.
Qed.