Require Import PermutationAutomation.
Require Import PermutationAuxiliary.
Require Import MatEquivSetoid.
Require Import PermutationFacts PermutationInstances.

(* This file contains what was originally MatrixPermBase from the
  ViCAR examples. It has been modified to fix the new perm_eq
  notation, and also includes more results. *)

Lemma perm_mat_permutes_ei_r : forall n f k, (k < n)%nat ->
  (perm_mat n f) × (e_i k) = e_i (f k).
Proof.
  intros n f k Hk.
  rewrite <- mat_equiv_eq_iff by auto with wf_db.
  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  unfold e_i.
  bdestruct (i =? f k).
  - unfold perm_mat, Mmult.
    bdestruct_one; [|lia].
    simpl.
    apply big_sum_unique.
    exists k.
    repeat split; [lia | bdestructΩ'simp | ].
    intros k' Hk' Hk'k'.
    bdestructΩ'simp.
  - simpl.
    unfold perm_mat, Mmult.
    rewrite big_sum_0_bounded; [easy|].
    intros k' Hk'.
    bdestructΩ'simp.
Qed.

Lemma basis_vector_equiv_e_i : forall n k, 
  basis_vector n k ≡ e_i k.
Proof.
  intros n k i j Hi Hj.
  unfold basis_vector, e_i.
  bdestructΩ'simp.
Qed.

Lemma basis_vector_eq_e_i : forall n k, (k < n)%nat ->
  basis_vector n k = e_i k.
Proof.
  intros n k Hk.
  rewrite <- mat_equiv_eq_iff by auto with wf_db.
  apply basis_vector_equiv_e_i.
Qed.

Lemma perm_mat_permutes_basis_vectors_r : forall n f k, (k < n)%nat ->
  (perm_mat n f) × (basis_vector n k) = e_i (f k).
Proof.
  intros n f k Hk.
  rewrite basis_vector_eq_e_i by easy.
  apply perm_mat_permutes_ei_r; easy.
Qed.

Lemma mat_equiv_of_equiv_on_ei : forall {n m} (A B : Matrix n m),
  (forall k, (k < m)%nat -> A × e_i k ≡ B × e_i k) ->
  A ≡ B.
Proof.
  intros n m A B Heq.
  intros i j Hi Hj.
  specialize (Heq j Hj).
  rewrite <- 2!(matrix_by_basis _ _ Hj) in Heq.
  specialize (Heq i O Hi ltac:(lia)).
  unfold get_vec in Heq.
  rewrite Nat.eqb_refl in Heq.
  easy.
Qed.

(* FIXME: Temp; only until pull mx stuff out of ZXExample *)
Lemma vector_eq_basis_comb : forall n (y : Vector n),
  WF_Matrix y -> 
  y = big_sum (G:=Vector n) (fun i => y i O .* @e_i n i) n.
Proof.
  intros n y Hwfy.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  symmetry.
  rewrite Msum_Csum.
  apply big_sum_unique.
  exists i.
  repeat split; try easy.
  - unfold ".*", e_i; bdestructΩ'simp.
  - intros l Hl Hnk.
  unfold ".*", e_i; bdestructΩ'simp.
Qed.

Lemma vector_equiv_basis_comb : forall n (y : Vector n),
  y ≡ big_sum (G:=Vector n) (fun i => y i O .* @e_i n i) n.
Proof.
  intros n y.
  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  symmetry.
  rewrite Msum_Csum.
  apply big_sum_unique.
  exists i.
  repeat split; try easy.
  - unfold ".*", e_i; bdestructΩ'simp.
  - intros l Hl Hnk.
  unfold ".*", e_i; bdestructΩ'simp.
Qed.

Lemma perm_mat_permutes_matrix_r : forall n m f (A : Matrix n m),
  permutation n f ->
  (perm_mat n f) × A ≡ (fun i j => A (perm_inv n f i) j).
Proof.
  intros n m f A Hperm.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite Mmult_assoc, <- 2(matrix_by_basis _ _ Hk).
  rewrite (vector_equiv_basis_comb _ (get_vec _ _)).
  rewrite Mmult_Msum_distr_l.
  erewrite big_sum_eq_bounded.
  2: {
    intros l Hl.
    rewrite Mscale_mult_dist_r, perm_mat_permutes_ei_r by easy.
    reflexivity.
  }
  intros i j Hi Hj; replace j with O by lia; clear j Hj.
  rewrite Msum_Csum.
  unfold get_vec, scale, e_i.
  rewrite Nat.eqb_refl.
  apply big_sum_unique.
  exists (perm_inv n f i).
  repeat split; auto with perm_bounded_db.
  - rewrite (perm_inv_is_rinv_of_permutation n f Hperm i Hi), Nat.eqb_refl.
    bdestructΩ'simp.
  - intros j Hj Hjne.
    bdestruct (i =? f j); [|bdestructΩ'simp].
    exfalso; apply Hjne.
    apply (permutation_is_injective n f Hperm); auto with perm_bounded_db.
    rewrite (perm_inv_is_rinv_of_permutation n f Hperm i Hi); easy.
Qed.

Lemma perm_mat_equiv_of_perm_eq : forall n f g, 
  (perm_eq n f g) ->
  perm_mat n f ≡ perm_mat n g.
Proof.
  intros n f g Heq.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite 2!perm_mat_permutes_ei_r, Heq by easy.
  easy.
Qed.

#[export] Hint Resolve perm_mat_equiv_of_perm_eq : perm_inv_db.

Lemma perm_mat_eq_of_perm_eq : forall n f g, 
  (perm_eq n f g) ->
  perm_mat n f = perm_mat n g.
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  now apply perm_mat_equiv_of_perm_eq.
Qed.

#[export] Hint Resolve perm_mat_eq_of_perm_eq : perm_inv_db.

Lemma perm_mat_equiv_of_perm_eq' : forall n m f g, n = m ->
  (perm_eq n f g) ->
  perm_mat n f ≡ perm_mat m g.
Proof.
  intros; subst n; apply perm_mat_equiv_of_perm_eq; easy.
Qed.

Lemma perm_mat_transpose {n f} (Hf : permutation n f) :
  (perm_mat n f) ⊤ ≡ perm_mat n (perm_inv n f).
Proof.
  intros i j Hi Hj.
  unfold "⊤".
  unfold perm_mat.
  simplify_bools_lia.
  rewrite <- (@perm_inv_eqb_iff n f) by cleanup_perm.
  now rewrite Nat.eqb_sym.
Qed.

Lemma perm_mat_transpose_eq {n f} (Hf : permutation n f) :
  (perm_mat n f) ⊤ = perm_mat n (perm_inv n f).
Proof. 
  apply mat_equiv_eq; auto with wf_db.
  now apply perm_mat_transpose.
Qed.

Lemma perm_mat_permutes_matrix_l : forall n m f (A : Matrix n m),
  permutation m f ->
  A × (perm_mat m f) ≡ (fun i j => A i (f j)).
Proof.
  intros n m f A Hf.
  apply transpose_simplify_mat_equiv_inv.
  rewrite Mmult_transpose, perm_mat_transpose by easy.
  rewrite perm_mat_permutes_matrix_r by auto with perm_db.
  unfold Matrix.transpose.
  intros i j Hi Hj.
  cleanup_perm_inv.
Qed.

Lemma make_WF_equiv n m (A : Matrix n m) : 
  make_WF A ≡ A.
Proof.
  unfold make_WF.
  intros i j Hi Hj.
  bdestructΩ'.
Qed.

Lemma perm_mat_permutes_matrix_l_eq : forall n m f (A : Matrix n m),
  WF_Matrix A ->
  permutation m f ->
  A × (perm_mat m f) = make_WF (fun i j => A i (f j)).
Proof.
  intros n m f A HA Hf.
  apply mat_equiv_eq; auto with wf_db.
  rewrite make_WF_equiv.
  now apply perm_mat_permutes_matrix_l.
Qed.

Lemma perm_mat_permutes_matrix_r_eq : forall n m f (A : Matrix n m),
  WF_Matrix A ->
  permutation n f ->
  (perm_mat n f) × A = make_WF (fun i j => A (perm_inv n f i) j).
Proof.
  intros n m f A HA Hf.
  apply mat_equiv_eq; auto with wf_db.
  rewrite make_WF_equiv.
  now apply perm_mat_permutes_matrix_r.
Qed.

Lemma Mmult_if_r {n m o} (A : Matrix n m) (B B' : Matrix m o) (b : bool) :
  A × (if b then B else B') = 
  if b then A × B else A × B'.
Proof.
  now destruct b.
Qed.

Lemma Mmult_if_l {n m o} (A A' : Matrix n m) (B : Matrix m o) (b : bool) :
  (if b then A else A') × B = 
  if b then A × B else A' × B.
Proof.
  now destruct b.
Qed.

Lemma perm_mat_idn n : 
  perm_mat n idn = I n.
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold perm_mat, I.
  bdestructΩ'.
Qed.

Lemma perm_mat_perm_eq_idn n f :
  perm_eq n f idn ->
  perm_mat n f = I n.
Proof.
  intros Heq.
  rewrite (perm_mat_eq_of_perm_eq n f idn Heq).
  apply perm_mat_idn.
Qed.

Lemma perm_mat_transpose_rinv {n f} (Hf : permutation n f) : 
  (perm_mat n f) × (perm_mat n f) ⊤ = I n.
Proof.
  rewrite perm_mat_transpose_eq by easy.
  rewrite perm_mat_Mmult by auto with perm_db.
  apply perm_mat_perm_eq_idn.
  cleanup_perm_inv.
Qed.

Lemma perm_mat_transpose_linv {n f} (Hf : permutation n f) : 
  (perm_mat n f) ⊤ × (perm_mat n f) = I n.
Proof.
  rewrite perm_mat_transpose_eq by easy.
  rewrite perm_mat_Mmult by auto with perm_db.
  apply perm_mat_perm_eq_idn.
  cleanup_perm_inv.
Qed.

Lemma perm_mat_of_stack_perms n0 n1 f g : 
  perm_bounded n0 f -> perm_bounded n1 g -> 
  perm_mat (n0 + n1) (stack_perms n0 n1 f g) = 
  direct_sum' (perm_mat n0 f) (perm_mat n1 g).
Proof.
  intros Hf Hg.
  apply mat_equiv_eq; auto with wf_db.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite perm_mat_permutes_ei_r by easy.
  rewrite 2!ei_direct_sum_split.
  rewrite Mmult_if_r.
  rewrite (direct_sum'_Mmult _ _ (e_i k) (Zero)).
  rewrite (direct_sum'_Mmult _ _ (@Zero n0 0) (e_i (k - n0))).
  rewrite 2!Mmult_0_r.
  (* rewrite  *)
  bdestruct (k <? n0).
  - rewrite perm_mat_permutes_ei_r, stack_perms_left by easy.
    pose proof (Hf k).
    now bdestructΩ (f k <? n0).
  - rewrite perm_mat_permutes_ei_r, stack_perms_right by lia.
    pose proof (Hg (k - n0)).
    bdestructΩ (g (k - n0) + n0 <? n0).
    now rewrite Nat.add_sub.
Qed.

#[export] Hint Rewrite perm_mat_of_stack_perms
  using auto with perm_bounded_db : perm_cleanup_db.



(* TODO: Put somewhere proper *)
Lemma ei_kron_split k n m :
  @e_i (n*m) k = 
  e_i (k / m) ⊗ e_i (k mod m).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  replace j with 0 by lia.
  unfold e_i, kron.
  do 2 simplify_bools_lia_one_kernel.
  do 2 simplify_bools_moddy_lia_one_kernel.
  rewrite Cmult_if_if_1_l.
  apply f_equal_if; [|easy..].
  now rewrite andb_comm, <- eqb_iff_div_mod_eqb.
Qed.

Lemma ei_kron_join k l n m :
  l < m ->
  @e_i n k ⊗ e_i l =
  @e_i (n*m) (k*m + l).
Proof.
  intros Hl.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  replace j with 0 by lia.
  unfold e_i, kron.
  do 2 simplify_bools_lia_one_kernel.
  do 2 simplify_bools_moddy_lia_one_kernel.
  rewrite Cmult_if_if_1_l.
  apply f_equal_if; [|easy..].
  symmetry.
  rewrite (eqb_iff_div_mod_eqb m).
  rewrite mod_add_l, Nat.div_add_l by lia.
  rewrite (Nat.mod_small l m Hl), (Nat.div_small l m Hl).
  now rewrite Nat.add_0_r, andb_comm.
Qed.

#[export] Hint Extern 100 (_ < _) =>
  show_moddy_lt : perm_bounded_db.

Lemma perm_mat_of_tensor_perms n0 n1 f g : 
  perm_bounded n1 g ->
  perm_mat (n0 * n1) (tensor_perms n0 n1 f g) = 
  perm_mat n0 f ⊗ perm_mat n1 g.
Proof.
  intros Hg.
  apply mat_equiv_eq; auto with wf_db.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite perm_mat_permutes_ei_r by easy.
  symmetry.
  rewrite ei_kron_split.
  restore_dims.
  rewrite kron_mixed_product.
  unfold tensor_perms.
  simplify_bools_lia_one_kernel.
  rewrite 2!perm_mat_permutes_ei_r by show_moddy_lt.
  now rewrite ei_kron_join by cleanup_perm.
Qed.

Lemma perm_mat_inj_mat_equiv n f g 
  (Hf : perm_bounded n f) (Hg : perm_bounded n g) : 
  perm_mat n f ≡ perm_mat n g ->
  perm_eq n f g.
Proof.
  intros Hequiv.
  intros i Hi.
  generalize (Hequiv (f i) i (Hf i Hi) Hi).
  unfold perm_mat.
  pose proof (Hf i Hi).
  pose proof C1_nonzero.
  bdestructΩ'.
Qed.

Lemma perm_mat_inj n f g 
  (Hf : perm_bounded n f) (Hg : perm_bounded n g) : 
  perm_mat n f = perm_mat n g ->
  perm_eq n f g.
Proof.
  rewrite <- mat_equiv_eq_iff by auto with wf_db.
  now apply perm_mat_inj_mat_equiv.
Qed.

Lemma perm_mat_determinant_sqr n f (Hf : permutation n f) : 
	(Determinant (perm_mat n f) ^ 2)%C = 1%R.
Proof.
  simpl.
  Csimpl.
  rewrite Determinant_transpose at 1.
  rewrite Determinant_multiplicative.
  rewrite perm_mat_transpose_linv by easy.
  now rewrite Det_I.
Qed.








Lemma perm_mat_perm_eq_of_proportional n f g : 
	(exists c, perm_mat n f = c .* perm_mat n g /\ c <> 0%R) ->
  perm_bounded n f ->
	perm_eq n f g.
Proof.
	intros (c & Heq & Hc) Hf.
	rewrite <- mat_equiv_eq_iff in Heq by auto with wf_db.
	intros i Hi.
	pose proof (Hf i Hi) as Hfi.
	generalize (Heq (f i) i Hfi Hi).
	unfold perm_mat, scale.
	do 3 simplify_bools_lia_one_kernel.
	rewrite Cmult_if_1_r.
	pose proof C1_nonzero.
	bdestructΩ'.
Qed.

Lemma perm_mat_eq_of_proportional n f g : 
	(exists c, perm_mat n f = c .* perm_mat n g /\ c <> 0%R) ->
  perm_bounded n f ->
	perm_mat n f = perm_mat n g.
Proof.
	intros H Hf.
	apply perm_mat_eq_of_perm_eq.
  now apply perm_mat_perm_eq_of_proportional.
Qed.










Lemma perm_to_matrix_perm_eq n f g : 
  perm_eq n f g ->
  perm_to_matrix n f ≡ perm_to_matrix n g.
Proof.
  intros Hfg.
  apply perm_mat_equiv_of_perm_eq.
  now apply qubit_perm_to_nat_perm_perm_eq.
Qed.

#[export] Hint Resolve perm_to_matrix_perm_eq : perm_inv_db.

Lemma perm_to_matrix_eq_of_perm_eq n f g : 
  perm_eq n f g ->
  perm_to_matrix n f = perm_to_matrix n g.
Proof.
  intros Hfg.
  apply mat_equiv_eq; auto with wf_db.
  now apply perm_to_matrix_perm_eq.
Qed.

#[export] Hint Resolve perm_to_matrix_eq_of_perm_eq : perm_inv_db.

Lemma perm_to_matrix_transpose {n f} (Hf : permutation n f) :
  (perm_to_matrix n f) ⊤ ≡ perm_to_matrix n (perm_inv n f).
Proof.
  unfold perm_to_matrix.
  rewrite perm_mat_transpose by auto with perm_db.
  cleanup_perm_inv.
Qed.

Lemma perm_to_matrix_transpose_eq {n f} (Hf : permutation n f) :
  (perm_to_matrix n f) ⊤ = perm_to_matrix n (perm_inv n f).
Proof. 
  apply mat_equiv_eq; auto with wf_db.
  now apply perm_to_matrix_transpose.
Qed.

Lemma perm_to_matrix_transpose' {n f} (Hf : permutation n f) :
  (perm_to_matrix n f) ⊤ ≡ perm_to_matrix n (perm_inv' n f).
Proof.
  rewrite perm_to_matrix_transpose by easy.
  apply perm_to_matrix_perm_eq.
  cleanup_perm_inv.
Qed.

Lemma perm_to_matrix_transpose_eq' {n f} (Hf : permutation n f) :
  (perm_to_matrix n f) ⊤ = perm_to_matrix n (perm_inv' n f).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  now apply perm_to_matrix_transpose'.
Qed.

Lemma perm_to_matrix_permutes_qubits_l n p f 
  (Hp : permutation n p) : 
  (f_to_vec n f) ⊤ × perm_to_matrix n p =
  (f_to_vec n (fun x => f (perm_inv n p x))) ⊤.
Proof.
  rewrite <- (transpose_involutive _ _ (perm_to_matrix _ _)).
  rewrite <- Mmult_transpose.
  rewrite perm_to_matrix_transpose_eq by easy.
  f_equal.
  apply perm_to_matrix_permutes_qubits.
  now apply perm_inv_permutation.
Qed.

#[export] Hint Resolve perm_to_matrix_perm_eq
  perm_to_matrix_eq_of_perm_eq : perm_inv_db.

Lemma perm_to_matrix_of_stack_perms n0 n1 f g 
  (Hf : permutation n0 f) (Hg : permutation n1 g) : 
  perm_to_matrix (n0 + n1) (stack_perms n0 n1 f g) = 
  perm_to_matrix n0 f ⊗ perm_to_matrix n1 g.
Proof.
  unfold perm_to_matrix.
  rewrite <- perm_mat_of_tensor_perms by cleanup_perm.
  rewrite <- Nat.pow_add_r.
  cleanup_perm.
Qed.

#[export] Hint Rewrite perm_to_matrix_of_stack_perms : perm_cleanup_db.

Lemma perm_to_matrix_idn n : 
  perm_to_matrix n idn = I (2^n).
Proof.
  rewrite <- perm_mat_idn.
  apply perm_mat_eq_of_perm_eq.
  cleanup_perm_inv.
Qed.

Lemma perm_to_matrix_compose n f g : 
  permutation n f -> permutation n g -> 
  perm_to_matrix n (f ∘ g) =
  perm_to_matrix n g × perm_to_matrix n f.
Proof.
  intros Hf Hg.
  unfold perm_to_matrix.
  rewrite perm_mat_Mmult by auto with perm_db.
  now rewrite qubit_perm_to_nat_perm_compose.
Qed.

#[export] Hint Rewrite perm_to_matrix_compose : perm_cleanup_db.

Lemma qubit_perm_to_nat_perm_inj n f g 
  (Hf : perm_bounded n f) : 
  perm_eq (2^n) (qubit_perm_to_nat_perm n f) (qubit_perm_to_nat_perm n g) ->
  perm_eq n f g.
Proof.
  intros H i Hi.
  specialize (H (2^(n - S (f i))) ltac:(apply Nat.pow_lt_mono_r; 
    auto with perm_bounded_db)).
  unfold qubit_perm_to_nat_perm in H.
  rewrite <- funbool_to_nat_eq_iff in H.
  specialize (H i Hi).
  revert H.
  unfold compose.
  rewrite Bits.nat_to_funbool_eq.
  pose proof (Hf i Hi).
  simplify_bools_lia_one_kernel.
  rewrite 2!Nat.pow2_bits_eqb.
  bdestructΩ'.
Qed.

Lemma perm_to_matrix_inj_mat_equiv n f g 
  (Hf : perm_bounded n f) (Hg : perm_bounded n g) :
  perm_to_matrix n f ≡ perm_to_matrix n g ->
  perm_eq n f g.
Proof.
  intros Hequiv.
  apply qubit_perm_to_nat_perm_inj; [easy|].
  apply perm_mat_inj_mat_equiv; [auto with perm_bounded_db..|].
  exact Hequiv.
Qed.

Lemma perm_to_matrix_inj n f g 
  (Hf : perm_bounded n f) (Hg : perm_bounded n g) :
  perm_to_matrix n f = perm_to_matrix n g ->
  perm_eq n f g.
Proof.
  rewrite <- mat_equiv_eq_iff by auto with wf_db.
  now apply perm_to_matrix_inj_mat_equiv.
Qed.


Lemma perm_to_matrix_perm_eq_of_proportional n f g : 
	(exists c, perm_to_matrix n f = 
    c .* perm_to_matrix n g /\ c <> 0%R) ->
  perm_bounded n f ->
	perm_eq n f g.
Proof.
  intros H Hf.
  pose proof (perm_mat_perm_eq_of_proportional _ _ _ H).
  apply qubit_perm_to_nat_perm_inj; auto with perm_bounded_db.
Qed.

Lemma perm_to_matrix_eq_of_proportional n f g : 
	(exists c, perm_to_matrix n f = 
    c .* perm_to_matrix n g /\ c <> 0%R) ->
  perm_bounded n f ->
	perm_to_matrix n f = perm_to_matrix n g.
Proof.
	intros H Hf.
  apply perm_to_matrix_eq_of_perm_eq.
  now apply perm_to_matrix_perm_eq_of_proportional.
Qed.

Definition perm_eq_id_mid (padl padm : nat) (f : nat -> nat) : Prop :=
  forall a, a < padm -> f (padl + a) = padl + a.

Lemma inv_perm_eq_id_mid {padl padm padr f} 
  (Hf : permutation (padl + padm + padr) f)
  (Hfidn : perm_eq_id_mid padl padm f) :
  forall k, k < padl + padm + padr ->
   padl <= f k < padl + padm -> f k = k.
Proof.
  intros k Hk [].
  apply (permutation_is_injective _ _ Hf); [lia..|].
  replace (f k) with (padl + (f k - padl)) by lia.
  (* unfold perm_eq_id_mid in Hfidn. *)
  apply Hfidn; lia.
Qed.

Definition expand_perm_id_mid (padl padm padr : nat) 
  (f : nat -> nat) : nat -> nat :=
  stack_perms padl (padm + padr) idn (rotr (padm + padr) padm) 
  ∘ (stack_perms (padl + padr) padm f idn)
  ∘ stack_perms padl (padm + padr) idn (rotr (padm + padr) padr).

Arguments compose_assoc [_ _ _ _].

Lemma expand_perm_id_mid_compose (f g : nat -> nat) (padl padm padr : nat) 
  (Hf : perm_bounded (padl + padr) f)
  (Hg : perm_bounded (padl + padr) g) :
  expand_perm_id_mid padl padm padr f ∘ expand_perm_id_mid padl padm padr g =
  expand_perm_id_mid padl padm padr (f ∘ g).
Proof.
  unfold expand_perm_id_mid.
  (* cleanup_perm. *)
  rewrite (compose_assoc _ (stack_perms _ _ idn (rotr _ padr))), 
    <- !(compose_assoc _ _ (stack_perms _ _ idn (rotr _ padr))).
  cleanup_perm_inv.
  cleanup_perm.
  rewrite (Nat.add_comm padr padm).
  cleanup_perm.
  rewrite compose_assoc, <- (compose_assoc _ _ (stack_perms _ _ f _)).
  cleanup_perm.
Qed.

Lemma expand_perm_id_mid_eq_of_perm_eq {padl padr f g} 
  (Hfg : perm_eq (padl + padr) f g) padm : 
  expand_perm_id_mid padl padm padr f = expand_perm_id_mid padl padm padr g.
Proof.
  unfold expand_perm_id_mid.
  do 2 f_equal.
  now apply stack_perms_proper_eq.
Qed.

Lemma expand_perm_id_mid_permutation {padl padr f} 
  (Hf : permutation (padl + padr) f) padm : 
  permutation (padl + padm + padr) (expand_perm_id_mid padl padm padr f).
Proof.
  unfold expand_perm_id_mid.
  rewrite <- Nat.add_assoc.
  apply permutation_compose; [|auto with perm_db].
  apply permutation_compose; [auto with perm_db|].
  replace (padl + (padm + padr)) with (padl + padr + padm) by lia.
  auto with perm_db.
Qed.

#[export] Hint Resolve expand_perm_id_mid_permutation : perm_db.

Definition contract_perm_id_mid (padl padm padr : nat) 
  (f : nat -> nat) : nat -> nat :=
  stack_perms padl (padm + padr) idn (rotr (padm + padr) padr) ∘ 
  f ∘ stack_perms padl (padm + padr) idn (rotr (padm + padr) padm).

Lemma contract_expand_perm_perm_eq_inv padl padm padr f 
  (Hf : perm_bounded (padl + padr) f) :
  perm_eq (padl + padr)
    (contract_perm_id_mid padl padm padr 
      (expand_perm_id_mid padl padm padr f)) 
    f.
Proof.
  unfold contract_perm_id_mid, expand_perm_id_mid.
  rewrite !compose_assoc.
  cleanup_perm.
  rewrite (Nat.add_comm padr padm).
  rewrite <- !compose_assoc.
  cleanup_perm.
  rewrite (Nat.add_comm padr padm).
  cleanup_perm.
  intros k Hk.
  now rewrite stack_perms_left by easy.
Qed.

Lemma stack_perms_idn_compose n0 n1 f g 
  (Hg : perm_bounded n1 g) : 
  stack_perms n0 n1 idn (f ∘ g) =
  stack_perms n0 n1 idn f ∘ stack_perms n0 n1 idn g.
Proof.
  cleanup_perm.
Qed.

Lemma stack_perms_compose_idn n0 n1 f g 
  (Hg : perm_bounded n0 g) : 
  stack_perms n0 n1 (f ∘ g) idn =
  stack_perms n0 n1 f idn ∘ stack_perms n0 n1 g idn.
Proof.
  cleanup_perm.
Qed.

Lemma contract_perm_id_mid_compose {padl padm padr f}
  (Hf : perm_bounded (padl + padm + padr) f) g : 
  contract_perm_id_mid padl padm padr g ∘ contract_perm_id_mid padl padm padr f =
  contract_perm_id_mid padl padm padr (g ∘ f).
Proof.
  unfold contract_perm_id_mid.
  rewrite (compose_assoc _ (stack_perms _ _ idn (rotr _ padm))), 
    <- !(compose_assoc _ _ (stack_perms _ _ idn (rotr _ padm))).
  cleanup_perm.
Qed.

Lemma contract_perm_id_mid_permutation_big {padl padm padr f} 
  (Hf : permutation (padl + padm + padr) f) : 
  permutation (padl + padm + padr) (contract_perm_id_mid padl padm padr f).
Proof.
  unfold contract_perm_id_mid.
  rewrite <- Nat.add_assoc in *.
  auto with perm_db.
Qed.

Lemma permutation_of_le_permutation_idn_above n m f :
  permutation n f -> m <= n -> (forall k, m <= k < n -> f k = k) -> 
  permutation m f.
Proof.
  intros Hf Hm Hfid.
  pose proof Hf as Hf'.
  destruct Hf' as [finv Hfinv].
  exists finv.
  intros k Hk; repeat split; try (apply Hfinv; lia).
  - pose proof (Hfinv k ltac:(lia)) as (?&?&?&?).
    bdestructΩ (f k <? m).
    specialize (Hfid (f k) ltac:(lia)).
    pose proof (Hfinv (f k) ltac:(easy)) as Hfinvk.
    rewrite Hfid in Hfinvk. 
    lia.
  - pose proof (Hfinv k ltac:(lia)) as (?&?&?&?).
    bdestructΩ (finv k <? m).
    specialize (Hfid (finv k) ltac:(lia)).
    replace -> (f (finv k)) in Hfid.
    lia.
Qed.

Lemma contract_perm_id_mid_permutation {padl padm padr f}
  (Hf : permutation (padl + padm + padr) f) 
  (Hfid : perm_eq_id_mid padl padm f) : 
  permutation (padl + padr) (contract_perm_id_mid padl padm padr f).
Proof.
  apply (permutation_of_le_permutation_idn_above _ _ _
    (contract_perm_id_mid_permutation_big Hf));
  [lia|].
  intros k [].
  unfold contract_perm_id_mid.
  unfold compose at 1.
  rewrite stack_perms_right by lia.
  rewrite rotr_add_l_eq.
  do 2 simplify_bools_lia_one_kernel.
  unfold compose.
  rewrite (Nat.add_comm _ padl), Hfid by lia.
  rewrite stack_perms_right by lia.
  rewrite rotr_add_r_eq.
  bdestructΩ'.
Qed.

#[export] Hint Resolve contract_perm_id_mid_permutation_big
  contract_perm_id_mid_permutation : perm_db.


Lemma expand_contract_perm_perm_eq_idn_inv {padl padm padr f}
  (Hf : permutation (padl + padm + padr) f) 
  (Hfidn : perm_eq_id_mid padl padm f) :
  perm_eq (padl + padm + padr)
    ((expand_perm_id_mid padl padm padr 
      (contract_perm_id_mid padl padm padr f))) 
    f.
Proof.
  unfold contract_perm_id_mid, expand_perm_id_mid.
  (* rewrite rotr_add_l_eq, rotr_add_r_eq.
  rewrite 2!stack_perms_idn_f, stack_perms_f_idn. *)
  intros k Hk.
  rewrite (stack_perms_idn_f _ _ (rotr _ padr)) at 2.
  unfold compose at 1.

  simplify_bools_lia_one_kernel.
  replace (if ¬ k <? padl then rotr (padm + padr) padr (k - padl) + padl else k)
  with (if ¬ k <? padl then if k <? padl + padm then k + padr else k - padm else k)
    by (rewrite rotr_add_r_eq; bdestructΩ').
  pose proof (inv_perm_eq_id_mid Hf Hfidn k).
  pose proof (Hfidn (k - padl)).
  bdestruct (k <? padl); simpl;
  [|bdestruct (k <? padl + padm); simpl].
  - unfold compose at 1.
    rewrite (@stack_perms_left (padl + padr)) by lia.
    unfold compose at 1.
    rewrite (stack_perms_left (k:=k)) by lia.
    unfold compose.
    rewrite (stack_perms_idn_f _ _ (rotr _ padr)).
    pose proof (permutation_is_bounded _ f Hf k ltac:(easy)).
    simplify_bools_lia_one_kernel.
    rewrite rotr_add_r_eq.
    bdestruct (f k <? padl);
    [simpl; now rewrite stack_perms_left by lia|].
    simpl.
    simplify_bools_lia_one_kernel.
    bdestructΩ'.
    (* replace (f k - padl - padm + padl) with (f k - padm) by lia. *)
    rewrite stack_perms_right by lia.
    rewrite rotr_add_l_eq.
    bdestructΩ'.
  - unfold compose at 1.
    rewrite (@stack_perms_right (padl + padr)) by lia.
    rewrite stack_perms_right by lia.
    rewrite rotr_add_l_eq.
    replace (padl + (k - padl)) with k in * by lia.
    bdestructΩ'.
  - unfold compose at 1.
    rewrite (@stack_perms_left (padl + padr)) by lia.
    unfold compose at 1.
    rewrite (stack_perms_right (k:=k - padm)) by lia.
    rewrite rotr_add_l_eq.
    do 2 simplify_bools_lia_one_kernel.
    replace (k - padm - padl + padm + padl) with k by lia.
    unfold compose.
    rewrite (stack_perms_idn_f _ _ (rotr _ padr)).
    pose proof (permutation_is_bounded _ f Hf k ltac:(easy)).
    simplify_bools_lia_one_kernel.
    rewrite rotr_add_r_eq.
    bdestruct (f k <? padl);
    [simpl; now rewrite stack_perms_left by lia|].
    simpl.
    simplify_bools_lia_one_kernel.
    bdestructΩ'.
    rewrite stack_perms_right by lia.
    bdestructΩ'.
Qed.

