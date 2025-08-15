From QuantumLib Require Import Matrix.
From QuantumLib Require Import Quantum.
Require Import QuantumLib.VectorStates.
Require Import QuantumLib.Permutations.

Import Setoid.

(* FIXME: Move to Prelim.v *)
Lemma symmetry_iff {A} {R : relation A} `{Symmetric A R} (x y : A) : 
  R x y <-> R y x.
Proof.
  split; apply symmetry.
Qed.

(* @nocheck name *)
Lemma Cpow_1_l k : C1 ^ k = C1.
Proof.
  induction k; [|simpl; rewrite IHk]; lca.
Qed.

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

(* @nocheck name *)
Lemma Cexp_PI' : Cexp PI = - C1.
Proof. rewrite Cexp_PI; lca. Qed.

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

Lemma equal_on_basis_states_implies_equal_l {dim n}
  (A B : Matrix (2^dim) n) : WF_Matrix A -> WF_Matrix B -> 
  (forall f, (f_to_vec dim f) ⊤%M × A = (f_to_vec dim f) ⊤%M × B) ->
  A = B.
Proof.
  intros HA HB HAB.
  apply transpose_matrices.
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  apply transpose_matrices.
  rewrite 2 Mmult_transpose, 2 transpose_involutive.
  apply HAB.
Qed.


Lemma e_i_transpose_adjoint n i : 
  (@e_i n i) ⊤%M = (e_i i) †%M.
Proof.
  prep_matrix_equality.
  unfold transpose, adjoint, e_i.
  rewrite (if_dist C C).
  now rewrite 2 Cconj_R.
Qed.

(* @nocheck name *)
Lemma Mmult_f_to_vec_l_is_get_row {dim m} (A : Matrix (2^dim) m) f : 
  WF_Matrix A -> 
  (f_to_vec dim f) ⊤%M × A = get_row A (funbool_to_nat dim f).
Proof.
  intros HA.
  rewrite basis_f_to_vec, basis_vector_eq_e_i by apply funbool_to_nat_bound.
  rewrite e_i_transpose_adjoint.
  rewrite <- matrix_by_basis_adjoint by apply funbool_to_nat_bound.
  reflexivity.
Qed.

(* FIXME: Move (I guess to vectorstates?? But b2R shouldn't go there either...) *)
(* @nocheck name *)
Lemma b2R_mult b c : (b2R b * b2R c = b2R (b && c))%R.
Proof.
  destruct b, c; cbn; lra.
Qed.


(* FIXME: Move to Qlib *)
(* @nocheck name *)
Lemma Mmult_n_1 {n} (A : Square n) : WF_Matrix A -> 
  Mmult_n 1 A = A.
Proof.
  intros;
  simpl; now Msimpl.
Qed.
(* @nocheck name *)
Lemma Mmult_n_add {n} k l (A : Square n) : WF_Matrix A -> 
  Mmult_n (k + l) A = Mmult_n k A × Mmult_n l A.
Proof.
  intros HA.
  induction k.
  - simpl.
    now Msimpl.
  - simpl.
    rewrite IHk.
    now rewrite Mmult_assoc.
Qed.
(* @nocheck name *)
Lemma Mmult_n_transpose {n} (k : nat) (A : Square n) : WF_Matrix A ->
  ((Mmult_n k A) ⊤)%M = Mmult_n k (A ⊤)%M.
Proof.
  intros HA.
  induction k.
  - apply id_transpose_eq.
  - simpl.
    rewrite Mmult_transpose, IHk.
    rewrite <- (Mmult_n_1 (A ⊤)%M) at 2 3 by auto_wf. 
    rewrite <- 2 Mmult_n_add by auto_wf.
    now rewrite Nat.add_comm.
Qed.



(* FIXME: Move, perhaps to Qlib.PermutationsBase? *)
Lemma forall_nat_lt_add n m (P : nat -> Prop) :
  (forall k, k < n + m -> P k) <->
  (forall k, k < n -> P k) /\ (forall k, k < m -> P (n + k)).
Proof.
  split; [auto with zarith|].
  intros [Hlow Hhigh] k Hk.
  bdestruct (k <? n); [auto|].
  replace k with (n + (k - n)) by lia.
  auto with zarith.
Qed.

(* FIXME: Move to Qlib *)
(* @nocheck name *)
Lemma WF_Perm_rw {n f g} (Hfg : perm_eq n f g) : 
  WF_Perm n f -> WF_Perm n g -> f = g.
Proof.
  intros Hf Hg.
  now eq_by_WF_perm_eq n.
Qed.

Import Modulus.

(* FIXME: Move to Qlib, in some Permutation* file *)
Lemma big_swap_perm_left p q a : a < p -> 
  big_swap_perm p q a = a + q.
Proof. unfold big_swap_perm; Modulus.bdestructΩ'. Qed.

Lemma big_swap_perm_right p q a : p <= a < p + q -> 
  big_swap_perm p q a = a - p.
Proof. unfold big_swap_perm; Modulus.bdestructΩ'. Qed.

(* FIXME: Move to Qlib.Modulus *)
Lemma div_add_n_r a n (Hn : n <> 0) : 
  (a + n) / n = a / n + 1.
Proof.
  pose proof (Nat.div_mod_eq (a + n) n).
  rewrite Modulus.mod_add_n_r in H.
  pose proof (Nat.div_mod_eq a n).
  nia.
Qed.

Lemma kron_comm_perm_2_n_succ_alt p : 
  perm_eq (2 * (S p)) (kron_comm_perm 2 (S p))
  ( stack_perms 1 (p + S p) idn (stack_perms (S p) p (big_swap_perm 1 p) idn)
    ∘ stack_perms 2 (2 * p) idn (kron_comm_perm 2 p))%prg.
Proof.
  rewrite 2!kron_comm_perm_defn.
  intros k Hk.
  unfold compose at 1.
  bdestruct (k <? 2).
  - rewrite (stack_perms_left (k := k)) by auto.
    rewrite Nat.mod_small, Nat.div_small by auto.
    destruct (ltac:(lia) : k = 0 \/ k = 1) as [-> | ->].
    + rewrite stack_perms_left by lia.
      lia.
    + rewrite stack_perms_right by lia.
      rewrite stack_perms_left by lia.
      rewrite big_swap_perm_left by lia.
      lia.
  - rewrite (stack_perms_right (k := k)) by lia.
    assert (Hkge : 2 <= k) by auto.
    destruct (le_ex_diff_r _ _ Hkge) as [l Hl].
    subst k.
    rewrite add_sub' by lia.
    assert (Hl : l < 2 * p) by lia.
    rewrite (Nat.add_comm 2 l).
    rewrite mod_add_n_r, div_add_n_r by auto.
    assert (l mod 2 < 2) by show_moddy_lt.
    assert (l / 2 < p) by show_moddy_lt.
    assert (l mod 2 * p + l / 2 < 2 * p) by show_moddy_lt.
    rewrite stack_perms_right by lia.
    destruct (ltac:(lia) : l mod 2 = 0 \/ l mod 2 = 1) as [Hlmod | Hlmod];
    rewrite Hlmod.
    + rewrite stack_perms_left by lia.
      rewrite big_swap_perm_right by lia.
      lia.
    + rewrite stack_perms_right by lia.
      lia.
Qed.


(* FIXME: Move *)
(* @nocheck name *)
Lemma Mmult_kron_e_i_I_r {n m1 m2} (A : Matrix n (m1 * m2)) k : 
  WF_Matrix A -> (k < m1)%nat ->
  A × ((e_i k) ⊗ I m2) = 
  make_WF (fun i j => A i (m2 * k + j)%nat).
Proof.
  intros HA Hk.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  intros i j Hi Hj.
  unfold Mmult, kron.
  apply (@big_sum_unique C).
  exists (m2 * k + j)%nat.
  split; [Modulus.show_moddy_lt|].
  split.
  - unfold e_i, I.
    rewrite Nat.mul_comm, Nat.div_add_l by lia.
    rewrite Nat.div_small by lia.
    rewrite Nat.add_0_r.
    Modulus.simplify_bools_lia_one_kernel.
    Modulus.simplify_bools_lia_one_kernel.
    rewrite Cmult_1_l.
    rewrite Modulus.mod_add_l.
    rewrite Nat.eqb_refl.
    Modulus.simpl_bools.
    Modulus.simplify_bools_moddy_lia_one_kernel.
    lca.
  - intros l Hl Hlne.
    unfold e_i, I.
    Modulus.simplify_bools_moddy_lia_one_kernel.
    Modulus.simplify_bools_moddy_lia_one_kernel.
    rewrite (Nat.div_small j), (Nat.mod_small j) by lia.
    rewrite Nat.eqb_refl; Modulus.simpl_bools.
    bdestruct_all; try lca.
    exfalso; apply Hlne.
    subst k j.
    pose proof (Nat.div_mod_eq l m2).
    lia.
Qed.

Lemma qubit0_to_ei : qubit0 = e_i 0.
Proof. 
  lma'.
Qed.

Lemma qubit1_to_ei : qubit1 = e_i 1.
Proof. 
  lma'.
Qed.