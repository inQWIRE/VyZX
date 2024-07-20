Require Import PermutationAuxiliary.
Require Import PermutationAutomation.
Require Import PermutationInstances.
Require Export PermMatrixFacts KronComm.

Lemma perm_to_matrix_rotr_eq_kron_comm : forall n o,
  perm_to_matrix (n + o) (rotr (n + o) n) = kron_comm (2^o) (2^n).
Proof.
  intros n o.
  now rewrite <- kron_comm_pows2_eq_perm_to_matrix_rotr.
Qed.

#[export] Hint Rewrite perm_to_matrix_rotr_eq_kron_comm : perm_inv_db.

Lemma perm_to_matrix_rotr_eq_kron_comm_mat_equiv : forall n o,
  perm_to_matrix (n + o) (rotr (n + o) n) ≡ kron_comm (2^o) (2^n).
Proof.
  intros n o.
  now rewrite perm_to_matrix_rotr_eq_kron_comm.
Qed.

#[export] Hint Resolve 
  perm_to_matrix_rotr_eq_kron_comm_mat_equiv : perm_inv_db.

Lemma perm_to_matrix_rotl_eq_kron_comm : forall n o,
  perm_to_matrix (n + o) (rotl (n + o) n) = kron_comm (2^n) (2^o).
Proof.
  intros n o.
  rewrite <- (perm_to_matrix_eq_of_perm_eq _ _ _ (rotr_inv (n + o) n)).
  rewrite <- perm_to_matrix_transpose_eq by auto with perm_db.
  rewrite perm_to_matrix_rotr_eq_kron_comm. 
  apply kron_comm_transpose.
Qed.

#[export] Hint Rewrite perm_to_matrix_rotl_eq_kron_comm : perm_inv_db.

Lemma perm_to_matrix_rotl_eq_kron_comm_mat_equiv : forall n o,
  perm_to_matrix (n + o) (rotl (n + o) n) ≡ kron_comm (2^n) (2^o).
Proof.
  intros.
  now rewrite perm_to_matrix_rotl_eq_kron_comm.
Qed.

#[export] Hint Resolve 
  perm_to_matrix_rotl_eq_kron_comm_mat_equiv : perm_inv_db.

Lemma perm_to_matrix_swap_block_perm_eq padl padm padr a :
  perm_to_matrix (padl + a + padm + a + padr) 
    (swap_block_perm padl padm a) =
  I (2^padl) ⊗
    (kron_comm (2^a) (2^padm * 2^a) ×
    (kron_comm (2^padm) (2^a) ⊗ I (2^a))) ⊗ 
  I (2^padr).
Proof.
  rewrite (swap_block_perm_decomp_eq padl padr padm a).
  rewrite <- !(Nat.add_assoc padl).
  rewrite 2!perm_to_matrix_of_stack_perms by auto with perm_db.
  rewrite perm_to_matrix_compose by auto with perm_db.
  rewrite perm_to_matrix_of_stack_perms by auto with perm_db.
  rewrite 3!perm_to_matrix_idn.
  rewrite kron_assoc by auto with wf_db.
  f_equal; [show_pow2_le..|].
  f_equal; [show_pow2_le..|].
  rewrite 2!perm_to_matrix_rotr_eq_kron_comm.
  unify_pows_two.
  rewrite (Nat.add_comm a padm).
  easy.
Qed.

#[export] Hint Rewrite perm_to_matrix_swap_block_perm_eq : perm_inv_db.

Lemma perm_to_matrix_rotr_commutes_kron_mat_equiv {n m p q} 
  (A : Matrix (2^n) (2^m)) (B : Matrix (2^p) (2^q)) : 
  @Mmult (2^n*2^p) (2^m*2^q) (2^q*2^m)
  (A ⊗ B) (perm_to_matrix (q + m) (rotr (q + m) q)) ≡
  @Mmult (2^n*2^p) (2^p*2^n) (2^q*2^m)
  (perm_to_matrix (p + n) (rotr (p + n) p)) (B ⊗ A).
Proof.
  unify_pows_two.
  rewrite 2!perm_to_matrix_rotr_eq_kron_comm.
  restore_dims.
  pose proof (kron_comm_commutes_r_mat_equiv (2^n) (2^m)
    (2^p) (2^q) A B) as H.
  rewrite !Nat.pow_add_r.
  apply H.
Qed.

Lemma perm_to_matrix_rotr_commutes_kron {n m p q} 
  (A : Matrix (2^n) (2^m)) (B : Matrix (2^p) (2^q)) : 
  WF_Matrix A -> WF_Matrix B ->
  @Mmult (2^n*2^p) (2^m*2^q) (2^q*2^m)
  (A ⊗ B) (perm_to_matrix (q + m) (rotr (q + m) q)) =
  @Mmult (2^n*2^p) (2^p*2^n) (2^q*2^m)
  (perm_to_matrix (p + n) (rotr (p + n) p)) (B ⊗ A).
Proof.
  unify_pows_two.
  rewrite 2!perm_to_matrix_rotr_eq_kron_comm.
  restore_dims.
  pose proof (kron_comm_commutes_r (2^n) (2^m)
    (2^p) (2^q) A B) as H.
  rewrite !Nat.pow_add_r.
  apply H.
Qed.


Lemma perm_to_matrix_swap_block_perm_natural {padl padm padr a}
  (A : Matrix (2^a) (2^a)) :
  @mat_equiv (2^padl*2^a*2^padm*2^a*2^padr) (2^padl*2^a*2^padm*2^a*2^padr)
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _
    (I (2^padl) ⊗ A ⊗ I (2^padm * 2^a * 2^padr))
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a)))
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _ 
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a))
    (I (2^padl * 2^a * 2^padm) ⊗ A ⊗ I (2^padr))).
Proof.
  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite !Mmult_assoc. 
  rewrite <- !Nat.pow_add_r in *.
  rewrite !basis_f_to_vec_alt by easy.
  rewrite perm_to_matrix_permutes_qubits by 
    apply swap_block_perm_permutation.
  rewrite <- (transpose_involutive _ _ 
    (perm_to_matrix _ (swap_block_perm _ _ _))).
  rewrite <- !Mmult_assoc, <- Mmult_transpose.
  rewrite (perm_to_matrix_transpose_eq
    (swap_block_perm_permutation padl padm padr a)).
  rewrite (perm_to_matrix_eq_of_perm_eq _ _ _
    (swap_block_perm_inv padl padm padr a)).
  rewrite perm_to_matrix_permutes_qubits by 
    apply swap_block_perm_permutation.
  replace (padl+a+padm+a+padr) with (padl+a+(padm+a+padr)) in * by lia.
  rewrite 2!(f_to_vec_split'_eq (padl+a)), 2!(f_to_vec_split'_eq (padl)).
  rewrite !(fun x y => kron_transpose' _ _ x y).
  rewrite !(fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z) by
    (now rewrite ?Nat.pow_add_r; simpl;lia).
  rewrite !Mmult_1_r by auto with wf_db.
  symmetry.
  
  replace (padl+a+(padm+a+padr)) with ((padl+a+padm)+a+padr) in * by lia.
  rewrite 2!(f_to_vec_split'_eq (padl+a+padm+a)), 2!(f_to_vec_split'_eq (_+_+_)).
  rewrite !(fun x y => kron_transpose' _ _ x y).
  rewrite !(fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z) by
    (now rewrite ?Nat.pow_add_r; simpl;lia).
  rewrite !Mmult_1_r by auto with wf_db.
  unfold kron.
  rewrite !Nat.mod_1_r, Nat.Div0.div_0_l.
  rewrite !basis_f_to_vec.
  rewrite !basis_trans_basis.
  rewrite !matrix_conj_basis_eq_lt 
    by show_moddy_lt.
  rewrite !Cmult_if_1_l, !Cmult_if_if_1_r.
  apply f_equal_if.
  - do 4 simplify_bools_moddy_lia_one_kernel.
    apply eq_iff_eq_true.
    rewrite !andb_true_iff, !Nat.eqb_eq.
    rewrite <- !funbool_to_nat_eq_iff.
    split;intros [Hlow Hhigh];
    split.
    + intros k Hk.
      generalize (Hlow k ltac:(lia)).
      unfold swap_block_perm.
      now simplify_bools_lia.
    + intros k Hk.
      unfold swap_block_perm.
      simplify_bools_lia.
      bdestructΩ'.
      * generalize (Hlow (padl+a+k) ltac:(lia)).
        unfold swap_block_perm.
        now simplify_bools_lia.
      * generalize (Hlow (padl + a + k - (a + padm)) ltac:(lia)).
        unfold swap_block_perm.
        simplify_bools_lia.
        intros <-.
        f_equal; lia.
      * apply_with_obligations
          (Hhigh ((padl + a + k) - (padl + a + padm + a)) ltac:(lia));
        f_equal; [lia|].
        unfold swap_block_perm; bdestructΩ'.
    + intros k Hk.
      unfold swap_block_perm.
      simplify_bools_lia.
      bdestructΩ'.
      * generalize (Hlow (k) ltac:(lia)).
        unfold swap_block_perm.
        now simplify_bools_lia.
      * apply_with_obligations 
          (Hhigh ((a + padm) + k - (padl + a)) ltac:(lia));
        f_equal; [|lia].
        unfold swap_block_perm; bdestructΩ'.
      * apply_with_obligations 
          (Hhigh (k - (padl + a)) ltac:(lia));
        f_equal; [|lia].
        unfold swap_block_perm; bdestructΩ'.
    + intros k Hk.
      apply_with_obligations (Hhigh (padm + a + k) ltac:(lia));
      f_equal;
      unfold swap_block_perm;
      bdestructΩ'.
  - f_equal;
    apply Bits.funbool_to_nat_eq;
    intros;
    unfold swap_block_perm;
    bdestructΩ'; f_equal; lia.
  - easy.
Qed.

Lemma perm_to_matrix_swap_block_perm_natural_eq {padl padm padr a}
  (A : Matrix (2^a) (2^a)) (HA : WF_Matrix A) :
  @eq (Matrix (2^padl*2^a*2^padm*2^a*2^padr) (2^padl*2^a*2^padm*2^a*2^padr))
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _
    (I (2^padl) ⊗ A ⊗ I (2^padm * 2^a * 2^padr))
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a)))
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _ 
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a))
    (I (2^padl * 2^a * 2^padm) ⊗ A ⊗ I (2^padr))).
Proof.
  apply mat_equiv_eq; 
  auto using WF_Matrix_dim_change with wf_db.
  apply perm_to_matrix_swap_block_perm_natural.
Qed.

Lemma perm_to_matrix_swap_block_perm_natural_eq_alt {padl padm padr a}
  (A : Matrix (2^a) (2^a)) (HA : WF_Matrix A) :
  @eq (Matrix (2^padl*2^a*2^padm*2^a*2^padr) (2^(padl+a+padm+a+padr)))
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _
    (I (2^padl) ⊗ A ⊗ I (2^padm * 2^a * 2^padr))
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a)))
  (@Mmult (2^padl*2^a*2^padm*2^a*2^padr) (2^padl*2^a*2^padm*2^a*2^padr) _ 
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a))
    (I (2^padl * 2^a * 2^padm) ⊗ A ⊗ I (2^padr))).
Proof.
  generalize (@perm_to_matrix_swap_block_perm_natural_eq 
    padl padm padr a A HA).
  unify_pows_two.
  easy.
Qed.

