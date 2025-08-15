Require Import CoreData.CoreData.
Require Import ComposeRules.
Require Import CastRules.
Require Import WireRules.
Require Import StackRules.
Require Import SwapRules.
Require Import ZXpermFacts.
Require Import CoreAutomation.
Require Import StackComposeRules.

(** Results about caps and cups, including yanking and 
  pullthrough (both for cap/cup and n_cap/n_cup) *)

Lemma cup_Z : ⊃ ∝= Z 2 0 0.
Proof.
  lma'.
  now rewrite Cexp_0.
Qed.

Lemma cap_Z : ⊂ ∝= Z 0 2 0.
Proof.
  transpose_of cup_Z.
Qed.

Lemma cup_X : ⊃ ∝= X 2 0 0.
Proof. colorswap_of cup_Z. Qed. 

Lemma cap_X : ⊂ ∝= X 0 2 0.
Proof. colorswap_of cap_Z. Qed. 

Lemma n_cup_0_empty : n_cup 0 ∝= ⦰.
Proof.
  etransitivity; [apply compose_empty_r|];
  apply stack_empty_l.
Qed.

Lemma n_cup_1_cup : n_cup 1 ∝= ⊃.
Proof.
  unfold n_cup.
  cbn.
  rewrite stack_empty_r_fwd, 2 cast_id.
  rewrite wire_removal_l.
  bundle_wires.
  now rewrite 2!nwire_removal_l.
Qed.

Lemma n_cap_0_empty : n_cap 0 ∝= ⦰.
Proof.
  transpose_of n_cup_0_empty.
Qed.

Lemma n_cap_1_cap : n_cap 1 ∝= ⊂.
Proof.
  transpose_of n_cup_1_cup.
Qed.

Local Open Scope matrix_scope.
Local Open Scope nat_scope.

Lemma cap_f_to_vec f : 
  ⟦ ⊃ ⟧ × f_to_vec 2 f = 
  (b2R (eqb (f 0) ((f 1))) .* I (2 ^ 0)).
Proof.
  prep_matrix_equivalence.
  unfold scale, kron.
  by_cell;
  destruct (f 0), (f 1); cbv; lca.
Qed.

Lemma n_cup_unswapped_f_to_vec n f : 
  ⟦ n_cup_unswapped n ⟧ × f_to_vec (n + n) f = 
  b2R (forallb (fun k => eqb (f k) ( f (n + n - S k))) (seq 0 n)) .* I (2 ^ 0).
Proof.
  revert f;
  induction n; intros f.
  - cbn. Csimpl. now Msimpl_light.
  - cbn [n_cup_unswapped].
    rewrite zx_compose_spec.
    simpl_cast_semantics.
    rewrite 2!zx_stack_spec.
    replace (S n + S n) with (1 + (n + n) + 1) by lia.
    rewrite Mmult_assoc.
    restore_dims.
    rewrite (@kron_f_to_vec_eq (1 + 0) (1 + (n + n)) 1 1) by auto_wf.
    rewrite (@kron_f_to_vec_eq 1 1 0 (n + n)) by auto_wf.
    rewrite IHn.
    cbn -[f_to_vec seq].
    rewrite Mmult_1_l, Mmult_1_comm by apply (f_to_vec_WF 1).
    rewrite (kron_split_diag (f_to_vec 1 f)) by auto_wf.
    rewrite <- kron_mixed_product, kron_1_r.
    restore_dims.
    rewrite f_to_vec_merge.
    rewrite <- Mmult_assoc.
    rewrite cap_f_to_vec.
    cbn [Nat.ltb Nat.leb].
    rewrite Nat.sub_diag, Nat.add_0_r.
    rewrite kron_1_l, kron_1_r by auto_wf.
    cbn -[seq].
    restore_dims.
    distribute_scale.
    Msimpl_light.
    f_equal.
    unfold b2R.
    rewrite !(if_dist _ _ _ RtoC).
    rewrite Cmult_if_if_1_l.
    apply f_equal_if; [|easy..].
    cbn.
    f_equal; [repeat f_equal; lia|].
    apply eq_iff_eq_true.
    rewrite forallb_seq0, forallb_seq.
    setoid_rewrite eqb_true_iff.
    apply forall_iff.
    intros s.
    apply impl_iff; intros Hs.
    rewrite 2!(Nat.add_comm _ 1).
    cbn.
    replace (S (n + n - S s)) with (n + n - s) by lia.
    reflexivity.
Qed.

Lemma n_cup_f_to_vec n f : 
  ⟦ n_cup n ⟧ × f_to_vec (n + n) f = 
  b2R (forallb (fun k => eqb (f k) ( f (n + k))) (seq 0 n)) .* I (2 ^ 0).
Proof.
  unfold n_cup.
  rewrite zx_compose_spec, zx_stack_spec.
  rewrite n_wire_semantics.
  rewrite perm_of_zx_permutation_semantics by auto with zxperm_db.
  rewrite perm_of_n_swap.
  rewrite Mmult_assoc.
  restore_dims.
  rewrite kron_f_to_vec_eq by auto_wf.
  rewrite perm_to_matrix_permutes_qubits by cleanup_perm.
  rewrite Mmult_1_l by auto_wf.
  rewrite f_to_vec_merge.
  rewrite n_cup_unswapped_f_to_vec.
  f_equal.
  f_equal.
  f_equal.
  apply eq_iff_eq_true.
  rewrite 2!forallb_seq0.
  setoid_rewrite eqb_true_iff.
  split.
  - intros Hf.
    intros s Hs.
    generalize (Hf (n - S s) ltac:(lia)).
    do 2 simplify_bools_lia_one_kernel.
    rewrite reflect_perm_defn by lia.
    rewrite sub_S_sub_S by lia.
    intros ->.
    f_equal; lia.
  - intros Hf.
    intros s Hs.
    generalize (Hf (n - S s) ltac:(lia)).
    do 2 simplify_bools_lia_one_kernel.
    rewrite reflect_perm_defn by lia.
    intros ->.
    f_equal; lia.
Qed.

Lemma f_to_vec_transpose_f_to_vec n f g :
  (f_to_vec n f) ⊤%M × f_to_vec n g = 
  b2R (forallb (fun k => eqb (f k) (g k)) (seq 0 n)) .* I 1.
Proof.
  prep_matrix_equivalence.
  intros [] []; [|lia..]; intros _ _.
  rewrite 2!basis_f_to_vec.
  rewrite basis_trans_basis.
  simplify_bools_moddy_lia_one_kernel.
  unfold scale.
  cbn.
  rewrite Cmult_1_r.
  unfold b2R.
  rewrite (if_dist _ _ _ RtoC).
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite Nat.eqb_eq, forallb_seq0, <- funbool_to_nat_eq_iff.
  now setoid_rewrite eqb_true_iff.
Qed.

Lemma f_to_vec_transpose_f_to_vec' n f g :
  (f_to_vec n f) ⊤%M × f_to_vec n g = 
  (if funbool_to_nat n f =? funbool_to_nat n g then  
    C1 else C0) .* I 1.
Proof.
  rewrite f_to_vec_transpose_f_to_vec.
  f_equal.
  unfold b2R.
  rewrite (if_dist R C).
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite forallb_seq0, Nat.eqb_eq.
  setoid_rewrite eqb_true_iff.
  apply funbool_to_nat_eq_iff.
Qed.

Lemma f_to_vec_transpose_self n f :
  (f_to_vec n f) ⊤%M × f_to_vec n f = 
  I 1.
Proof.
  rewrite f_to_vec_transpose_f_to_vec', Nat.eqb_refl.
  now Msimpl_light.
Qed.


Lemma n_cup_f_to_vec_pullthrough_bot n f : 
  @Mmult _ (2^(n + n)) (2^n) (⟦ n_cup n ⟧) (I (2 ^ n) ⊗ f_to_vec n f) = 
  (f_to_vec n f) ⊤%M.
Proof.
  unify_pows_two.
  apply equal_on_basis_states_implies_equal';
  [auto_wf.. |].
  intros g.
  rewrite <- (kron_1_r _ _ (f_to_vec n g)) at 1.
  rewrite Mmult_assoc.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_l, Mmult_1_r by auto_wf.
  rewrite f_to_vec_transpose_f_to_vec.
  rewrite f_to_vec_merge.
  rewrite n_cup_f_to_vec.
  do 3 f_equal.
  apply eq_iff_eq_true.
  rewrite 2!forallb_seq0.
  apply forall_iff; intros s.
  apply impl_iff; intros Hs.
  do 2 simplify_bools_lia_one_kernel.
  rewrite add_sub'.
  rewrite 2!eqb_true_iff.
  easy.
Qed.

Lemma n_cup_f_to_vec_pullthrough_top n f : 
  @Mmult _ (2^(n + n)) (2^n) (⟦ n_cup n ⟧) (f_to_vec n f ⊗ I (2 ^ n)) = 
  (f_to_vec n f) ⊤%M.
Proof.
  unify_pows_two.
  apply equal_on_basis_states_implies_equal';
  [auto_wf.. |].
  intros g.
  rewrite <- (kron_1_l _ _ (f_to_vec n g)) at 1 by auto_wf.
  rewrite Mmult_assoc.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_l, Mmult_1_r by auto_wf.
  rewrite f_to_vec_transpose_f_to_vec.
  rewrite f_to_vec_merge.
  rewrite n_cup_f_to_vec.
  do 3 f_equal.
  apply eq_iff_eq_true.
  rewrite 2!forallb_seq0.
  apply forall_iff; intros s.
  apply impl_iff; intros Hs.
  do 2 simplify_bools_lia_one_kernel.
  now rewrite add_sub'.
Qed.

Lemma n_cap_f_to_vec_pullthrough_bot n f :
  @Mmult (2^n) (2^(n + n)) _ (I (2 ^ n) ⊗ (f_to_vec n f) ⊤%M) (⟦ n_cap n ⟧) = 
  f_to_vec n f.
Proof.
  apply transpose_matrices.
  rewrite Mmult_transpose.
  restore_dims.
  rewrite Nat.pow_add_r.
  change (@Matrix.transpose (2 ^ n)) with (@Matrix.transpose (2^n * 2^0)).
  rewrite (kron_transpose).
  unfold n_cap.
  rewrite semantics_transpose_comm.
  change (transpose (transpose ?x)) with x.
  rewrite id_transpose_eq.
  unify_pows_two.
  apply n_cup_f_to_vec_pullthrough_bot.
Qed.

Lemma n_cap_f_to_vec_pullthrough_top n f :
  @Mmult (2^n) (2^(n + n)) _ ((f_to_vec n f) ⊤%M ⊗ I (2 ^ n)) (⟦ n_cap n ⟧) = 
  f_to_vec n f.
Proof.
  apply transpose_matrices.
  rewrite Mmult_transpose.
  restore_dims.
  rewrite Nat.pow_add_r.
  change (@Matrix.transpose (2 ^ n)) with (@Matrix.transpose (2^0 * 2^n)).
  rewrite (kron_transpose).
  unfold n_cap.
  rewrite semantics_transpose_comm.
  change (Matrix.transpose (Matrix.transpose ?x)) with x.
  rewrite id_transpose_eq.
  unify_pows_two.
  apply n_cup_f_to_vec_pullthrough_top.
Qed.

Lemma n_cup_matrix_pullthrough_top n m (A : Matrix (2 ^ n) (2 ^ m)) 
  (HA : WF_Matrix A) : 
  @Mmult _ (2^(n + n)) (2^(m + n)) (⟦ n_cup n ⟧) (A ⊗ I (2 ^ n)) = 
  @Mmult _ (2^(m + m)) (2^(m + n)) (⟦ n_cup m ⟧) (I (2 ^ m) ⊗ A ⊤%M).
Proof.
  unify_pows_two.
  apply equal_on_basis_states_implies_equal';
  [auto_wf..|].
  intros f.
  rewrite 2!Mmult_assoc.
  restore_dims.
  rewrite 2!kron_f_to_vec_eq by auto_wf.
  rewrite 2!Mmult_1_l, kron_split_antidiag by auto_wf.
  restore_dims.
  unify_pows_two.
  rewrite <- Mmult_assoc.
  rewrite n_cup_f_to_vec_pullthrough_bot.
  symmetry.
  rewrite kron_split_diag by auto_wf.
  unify_pows_two.
  rewrite <- Mmult_assoc.
  rewrite n_cup_f_to_vec_pullthrough_top.
  rewrite kron_1_l, kron_1_r by auto_wf.
  rewrite <- Mmult_assoc.
  rewrite Mmult_vec_comm, Mmult_transpose by auto_wf.
  easy.
Qed.

Lemma n_cup_matrix_pullthrough_bot n m (A : Matrix (2 ^ n) (2 ^ m)) 
  (HA : WF_Matrix A) : 
  @Mmult _ (2^(n + n)) (2^(n + m)) (⟦ n_cup n ⟧) (I (2 ^ n) ⊗ A) = 
  @Mmult _ (2^(m + m)) (2^(n + m)) (⟦ n_cup m ⟧) (A ⊤%M ⊗ I (2 ^ m)).
Proof.
  now rewrite n_cup_matrix_pullthrough_top, 
    Matrix.transpose_involutive by auto_wf.
Qed.

Open Scope ZX_scope.

Lemma n_cup_pullthrough_top {n m} (zx : ZX n m) : 
  zx ↕ n_wire m ⟷ n_cup m ∝=
  n_wire n ↕ zx ⊤ ⟷ n_cup n.
Proof.
  hnf.
  cbn [ZX_semantics].
  rewrite semantics_transpose_comm, 2!n_wire_semantics.
  apply n_cup_matrix_pullthrough_top.
  auto_wf.
Qed.

Lemma n_cup_pullthrough_bot {n m} (zx : ZX n m) : 
  n_wire m ↕ zx ⟷ n_cup m ∝=  
  zx ⊤ ↕ n_wire n ⟷ n_cup n.
Proof.
  rewrite n_cup_pullthrough_top, Proportional.transpose_involutive.
  easy.
Qed.

Lemma n_cap_pullthrough_top {n m} (zx : ZX n m) : 
  n_cap n ⟷ (zx ↕ n_wire n) ∝=
  n_cap m ⟷ (n_wire m ↕ zx ⊤).
Proof. 
  apply transpose_diagrams_eq.
  cbn -[n_cup].
  unfold n_cap.
  rewrite !Proportional.transpose_involutive, !n_wire_transpose.
  now rewrite n_cup_pullthrough_bot.
Qed.

Lemma n_cap_pullthrough_bot {n m} (zx : ZX n m) : 
  n_cap n ⟷ (n_wire n ↕ zx) ∝=
  n_cap m ⟷ (zx ⊤ ↕ n_wire m).
Proof.
  now rewrite n_cap_pullthrough_top, Proportional.transpose_involutive.
Qed.

Lemma n_cup_inv_n_swap_n_wire : forall n, n_cup n ∝= n_wire n ↕ n_swap n ⟷ n_cup_unswapped n.
Proof.
  intros n.
  rewrite compose_zxperm_l_eq' by auto_zxperm.
  cbn.
  rewrite n_wire_transpose.
  rewrite n_cup_pullthrough_bot, n_swap_transpose.
  rewrite compose_zxperm_l_eq by auto_zxperm.
  cbn.
  rewrite n_wire_transpose.
  now rewrite 2!n_swap_transpose.
Qed.

Lemma n_cup_unswapped_to_n_cup_n_swap_top n : 
	n_cup_unswapped n ∝= 
	n_swap n ↕ n_wire n ⟷ n_cup n.
Proof.
	rewrite compose_zxperm_l_eq' by auto_zxperm.
	now rewrite stack_transpose, n_swap_transpose, n_wire_transpose.
Qed.

Lemma n_cup_unswapped_pullthrough_top {n m} (zx : ZX n m) : 
	zx ↕ n_wire m ⟷ n_cup_unswapped m ∝=
	n_wire n ↕ (n_swap m ⟷ zx ⊤ ⟷ n_swap n) ⟷ n_cup_unswapped n.
Proof.
	rewrite n_cup_unswapped_to_n_cup_n_swap_top.
	rewrite n_cup_pullthrough_top.
	rewrite <- compose_assoc, <- stack_compose_distr, 
		nwire_removal_l, nwire_removal_r, n_swap_transpose.
	rewrite stack_split_antidiag, compose_assoc, n_cup_pullthrough_top.
	rewrite n_cup_inv_n_swap_n_wire.
	now rewrite !stack_nwire_distribute_l, !compose_assoc.
Qed.

Lemma n_cup_unswapped_pullthrough_bot {n m} (zx : ZX n m) : 
	n_wire m ↕ zx ⟷ n_cup_unswapped m ∝=
	(n_swap m ⟷ zx ⊤ ⟷ n_swap n) ↕ n_wire n ⟷ n_cup_unswapped n.
Proof.
	rewrite n_cup_unswapped_to_n_cup_n_swap_top.
	(* rewrite n_cup_pullthrough_top. *)
	rewrite <- compose_assoc, <- stack_compose_distr, 
		nwire_removal_l, nwire_removal_r.
	rewrite stack_split_diag, compose_assoc, n_cup_pullthrough_bot.
	now rewrite !stack_nwire_distribute_r, !compose_assoc.
Qed.

Lemma big_yank_l n prf0 prf1 :   
  (n_cap n ↕ n_wire n) ⟷
  cast _ _ prf0 prf1
    (n_wire n ↕ n_cup n) ∝= n_wire n.
Proof.
  hnf.
  cbn -[n_cup n_cap].
  simpl_cast_semantics.
  cbn -[n_cup n_cap].
  rewrite n_wire_semantics.
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite Mmult_1_l by auto_wf.
  rewrite Mmult_assoc.
  rewrite <- (kron_1_l _ _ (f_to_vec n f)) by auto_wf.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_l, Mmult_1_r by auto_wf.
  rewrite (kron_split_antidiag _ (f_to_vec n f)) by auto_wf.
  rewrite Nat.pow_add_r, <- id_kron.
  rewrite kron_assoc by auto_wf.
  restore_dims.
  unify_pows_two.
  rewrite <- Mmult_assoc.
  restore_dims.
  rewrite kron_mixed_product' by unify_pows_two.
  unify_pows_two.
  rewrite n_cup_f_to_vec_pullthrough_bot.
  rewrite Mmult_1_l, kron_1_r by auto_wf.
  rewrite n_cap_f_to_vec_pullthrough_bot.
  now rewrite kron_1_l by auto_wf.
Qed.

Lemma big_yank_r n prf0 prf1 prf2 : 
  (n_wire n ↕ n_cap n) ⟷
  cast _ _ prf0 prf1
    (n_cup n ↕ n_wire n) ∝= cast _ _ prf2 eq_refl (n_wire n).
Proof.
  apply transpose_diagrams_eq.
  cbn [ZXCore.transpose].
  rewrite 2!cast_transpose.
  cbn [ZXCore.transpose].
  unfold n_cap.
  rewrite Proportional.transpose_involutive.
  fold (n_cap n).
  rewrite n_wire_transpose.
  rewrite cast_compose_l.
  clean_eqns eapply (cast_diagrams_eq n n).
  clean_eqns rewrite cast_contract, 
    cast_compose_distribute, cast_contract, cast_id.
  rewrite (big_yank_l n).
  now clean_eqns rewrite cast_contract, cast_id.
Qed.

Lemma n_cap_n_cup_matrix_pullthrough n m (A : Matrix (2 ^ n) (2 ^ m)) 
  (HA : WF_Matrix A) : 
  I (2 ^ m) ⊗ (⟦ n_cup n ⟧) × (I (2 ^ m) ⊗ A ⊗ I (2 ^ n)) × 
    (⟦ n_cap m ⟧ ⊗ I (2 ^ n)) =
  A ⊤%M.
Proof.
  apply equal_on_basis_states_implies_equal'; 
  [auto_wf..|].
  intros f.
  rewrite <- (kron_1_l _ _ (f_to_vec n f)) at 1 by auto_wf.
  rewrite Mmult_assoc;
  restore_dims.  
  rewrite Mmult_assoc, kron_mixed_product' by unify_pows_two.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite !Mmult_1_l, Mmult_1_r by auto_wf.
  rewrite (kron_split_antidiag (_ × _)), <- id_kron, kron_assoc by auto_wf.
  rewrite kron_1_r.
  restore_dims.
  unify_pows_two.

  rewrite <- Mmult_assoc.
  restore_dims.
  rewrite kron_mixed_product' by unify_pows_two.
  rewrite Mmult_1_r by auto_wf.
  unify_pows_two.
  rewrite n_cup_f_to_vec_pullthrough_bot, <- Mmult_assoc.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_r by auto_wf.
  apply transpose_matrices.
  rewrite !Mmult_transpose.
  change (Matrix.transpose (?A ⊗ ?B)) with ((Matrix.transpose A) ⊗ (Matrix.transpose B)).
  rewrite Mmult_transpose, Matrix.transpose_involutive.
  unfold n_cap.
  rewrite semantics_transpose_comm.
  change (Matrix.transpose (Matrix.transpose ?x)) with x.
  rewrite id_transpose_eq.
  unify_pows_two.
  apply equal_on_basis_states_implies_equal';
  [auto_wf..|].
  intros g.
  rewrite Mmult_assoc.
  rewrite <- (kron_1_r _ _ (f_to_vec m g)).
  restore_dims.
  rewrite kron_mixed_product.
  rewrite kron_1_r.
  rewrite Mmult_1_l, Mmult_1_r by auto_wf.
  rewrite (kron_split_diag (f_to_vec _ _)) by auto_wf.
  unify_pows_two.
  rewrite <- Mmult_assoc.
  rewrite n_cup_f_to_vec_pullthrough_top.
  rewrite kron_1_l by auto_wf.
  now rewrite Mmult_vec_comm by auto_wf.
Qed. 

Lemma n_cap_n_cup_pullthrough n m (A : ZX m n) prf1 prf2 : 
  (n_cap m ↕ n_wire n) ⟷ 
  (n_wire m ↕ A ↕ n_wire n) ⟷
  cast _ _ prf1 prf2 (n_wire m ↕ n_cup n) ∝=
  A ⊤.
Proof.
  rewrite <- stack_nwire_distribute_r.
  rewrite n_cap_pullthrough_bot.
  rewrite stack_nwire_distribute_r, compose_assoc.
  clean_eqns rewrite stack_assoc.
  clean_eqns rewrite cast_compose_l, cast_contract.
  rewrite (cast_compose_r _ _ (A ⊤ ↕ _)), cast_id.
  rewrite <- stack_compose_distr.
  rewrite n_wire_stack, nwire_removal_l, nwire_removal_r.
  rewrite (stack_split_antidiag (A ⊤)).
  clean_eqns rewrite stack_empty_r, 
    (cast_compose_r _ _ (n_wire n ↕ _)), !cast_contract.
  clean_eqns rewrite cast_compose_distribute, 
    cast_contract, cast_id.
  rewrite <- compose_assoc.
  rewrite big_yank_l.
  now cleanup_zx.
Qed.

Global Open Scope ZX_scope.

Lemma n_cup_unswapped_grow_l : forall n prfn prfm, 
  n_cup_unswapped (S n) ∝= cast _ _ prfn prfm (n_wire n ↕ ⊃ ↕ n_wire n) ⟷ 
  n_cup_unswapped n.
Proof.
  intros.
  induction n.
  - simpl.
    rewrite !cast_id.
    cleanup_zx.
    rewrite !cast_id.
    now rewrite wire_to_n_wire, n_wire_stack, nwire_removal_l.
  - simpl.
    fold (n_wire n).
    simpl in IHn.
    rewrite IHn at 1.
    rewrite stack_wire_distribute_l.
    rewrite stack_wire_distribute_r.
    change (— ↕ n_wire n) with (n_wire (1 + n)).
    erewrite <- (@cast_n_wire (n + 1) (1 + n)).
    rewrite <- compose_assoc.
    apply compose_simplify_eq; [ | easy].
    erewrite (cast_compose_mid (S (n + S n))).
    rewrite cast_compose_distribute.
    repeat rewrite cast_contract.
    apply compose_simplify_eq; [ | apply cast_simplify_eq; easy].
    simpl_casts.
    rewrite 2 stack_assoc.
    simpl_casts.
    rewrite wire_to_n_wire, n_wire_stack.
    rewrite 2 stack_assoc_back.
    simpl_casts.
    erewrite <- (@cast_n_wire (n + 1) (S n)) at 2.
    rewrite cast_stack_r.
    rewrite n_wire_stack.
    cast_irrelevance.
Unshelve.
  all: lia.
Qed.

Lemma n_cup_unswapped_colorswap : forall n, 
  ⊙ (n_cup_unswapped n) = n_cup_unswapped n.
Proof. 
  intros.
  induction n; [ easy | ].
  simpl.
  f_equal.
  rewrite cast_colorswap.
  apply cast_simplify_zx.
  simpl.
  rewrite IHn.
  easy.
Qed.

Lemma n_cup_colorswap : forall n, ⊙ (n_cup n) = n_cup n.
Proof. 
  intros.
  unfold n_cup.
  simpl.
  rewrite n_wire_colorswap.
  rewrite n_swap_colorswap.
  rewrite n_cup_unswapped_colorswap.
  easy.
Qed.

Lemma n_cap_unswapped_colorswap : forall n, ⊙ (n_cap_unswapped n) = n_cap_unswapped n.
Proof.
  intros.
  unfold n_cap_unswapped.
  rewrite colorswap_transpose_commute.
  rewrite n_cup_unswapped_colorswap.
  easy.
Qed.

Lemma n_cap_colorswap : forall n, ⊙ (n_cap n) = n_cap n.
Proof. 
  intros.
  unfold n_cap.
  rewrite colorswap_transpose_commute.
  rewrite n_cup_colorswap.
  easy.
Qed.

#[export] Hint Rewrite
  (fun n => @n_cup_colorswap n)
  (fun n => @n_cap_colorswap n)
  (fun n => @n_cup_unswapped_colorswap n)
  (fun n => @n_cap_unswapped_colorswap n)
  : colorswap_db.

Lemma n_cup_unswapped_transpose : forall n, (n_cup_unswapped n)⊤ = n_cap_unswapped n.
Proof.
  reflexivity.
Qed.

Lemma n_cap_unswapped_transpose : forall n, (n_cap_unswapped n)⊤ = n_cup_unswapped n.
Proof.
  intros.
  unfold n_cap_unswapped.
  rewrite Proportional.transpose_involutive_eq.
  easy.
Qed.

Lemma n_cup_transpose : forall n, (n_cup n)⊤ = n_cap n.
Proof.
  reflexivity.
Qed.

Lemma n_cap_transpose : forall n, (n_cap n)⊤ ∝= n_cup n.
Proof.
  intros.
  unfold n_cap.
  rewrite Proportional.transpose_involutive.
  easy.
Qed.

#[export] Hint Rewrite
  (fun n => @n_cup_unswapped_transpose n)
  (fun n => @n_cap_unswapped_transpose n)
  (fun n => @n_cup_transpose n)
  (fun n => @n_cap_transpose n)
  : transpose_db.


Lemma cap_is_n_cup : ⊃ ∝= n_cup 1.
Proof.
  unfold n_cup.
  rewrite n_swap_1_is_wire.
  cbn [n_cup_unswapped].
  rewrite stack_empty_r, 2 cast_id.
  bundle_wires.
  rewrite 2 nwire_removal_l.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.
Lemma cup_is_n_cap : ⊂ ∝= n_cap 1.
Proof. transpose_of (cap_is_n_cup). Qed.

Lemma cap_pullthrough_top_1 (zx zx' : ZX 1 1) : 
  zx ↕ zx' ⟷ ⊃ ∝= — ↕ (zx' ⟷ zx ⊤) ⟷ ⊃.
Proof.
  rewrite <- nwire_stack_compose_topleft, compose_assoc.
  rewrite cap_is_n_cup, wire_to_n_wire, n_cup_pullthrough_top.
  rewrite <- compose_assoc, 
    <- stack_nwire_distribute_l.
  reflexivity.
Qed.

Lemma cap_pullthrough_bot_1 (zx zx' : ZX 1 1) : 
  zx' ↕ zx ⟷ ⊃ ∝= ((zx' ⟷ zx ⊤)) ↕ — ⟷ ⊃.
Proof.
  rewrite cap_pullthrough_top_1, 
    (cap_pullthrough_top_1 (_⟷_)), wire_removal_l.
  cbn.
  now rewrite transpose_involutive_eq.
Qed.

Lemma cup_pullthrough_top_1 (zx zx' : ZX 1 1) : 
  ⊂ ⟷ (zx ↕ zx') ∝= ⊂ ⟷ (— ↕ (zx ⊤ ⟷ zx')).
Proof. transpose_of (cap_pullthrough_top_1 (zx ⊤) (zx' ⊤)). Qed.

Lemma cup_pullthrough_bot_1 (zx zx' : ZX 1 1) : 
  ⊂ ⟷ (zx' ↕ zx) ∝= ⊂ ⟷ ((zx ⊤ ⟷ zx') ↕ —).
Proof. transpose_of (cap_pullthrough_bot_1 (zx ⊤) (zx' ⊤)). Qed.


Lemma cap_pullthrough_top {n m} (zx : ZX n 1) (zx' : ZX m 1) : 
  zx ↕ zx' ⟷ ⊃ ∝= n_wire n ↕ (zx' ⟷ zx ⊤) ⟷ n_cup n.
Proof.
  rewrite <- nwire_stack_compose_topleft, compose_assoc.
  rewrite cap_is_n_cup, n_cup_pullthrough_top.
  rewrite <- compose_assoc, 
    <- stack_nwire_distribute_l.
  reflexivity.
Qed.

Lemma cap_pullthrough_bot {n m} (zx : ZX n 1) (zx' : ZX m 1) : 
  zx' ↕ zx ⟷ ⊃ ∝= (zx' ⟷ zx ⊤) ↕ n_wire n ⟷ n_cup n.
Proof.
  rewrite cap_pullthrough_top, n_cup_pullthrough_top.
  cbn.
  now rewrite transpose_involutive_eq.
Qed.

Lemma cup_pullthrough_top {n m} (zx : ZX 1 n) (zx' : ZX 1 m) : 
  ⊂ ⟷ (zx ↕ zx') ∝= n_cap n ⟷ (n_wire n ↕ (zx ⊤ ⟷ zx')).
Proof. transpose_of (cap_pullthrough_top (zx ⊤) (zx' ⊤)). Qed.

Lemma cup_pullthrough_bot {n m} (zx : ZX 1 n) (zx' : ZX 1 m) : 
  ⊂ ⟷ (zx' ↕ zx) ∝= n_cap n ⟷ ((zx ⊤ ⟷ zx') ↕ n_wire n).
Proof. transpose_of (cap_pullthrough_bot (zx ⊤) (zx' ⊤)). Qed.


Lemma n_cup_plus_decomp n k : 
  n_cup (n + k) ∝=
  zx_invassoc _ _ _ ⟷
  ((zx_assoc n k n ⟷ (n_wire n ↕ zx_comm k n)
    ⟷ zx_invassoc n n k) ↕ n_wire k) ⟷
  zx_assoc (n + n) k k ⟷
  (n_cup n ↕ n_cup k).
Proof.
  apply equal_on_basis_states_implies_equal';
  [auto_wf.. |].
  intros f.
  cbn -[cast n_cup].
  unfold zx_assoc, zx_invassoc.
  simpl_cast_semantics.
  rewrite 6 n_wire_semantics; Msimpl.
  rewrite n_cup_f_to_vec.
  rewrite 3 f_to_vec_split'_eq.
  rewrite Mmult_assoc.
  restore_dims.
  rewrite <- kron_assoc, kron_mixed_product' by 
    solve [auto_wf | unify_pows_two; nia].
  rewrite kron_assoc by auto_wf.
  rewrite (kron_mixed_product' (2^n)) by 
    solve [auto_wf | unify_pows_two; nia].
  rewrite 2 Mmult_1_l by auto_wf.
  rewrite zx_comm_semantics.
  restore_dims.
  rewrite Kronecker.kron_comm_commutes_l by auto_wf.
  rewrite Kronecker.kron_comm_1_l, Mmult_1_r by auto_wf.
  rewrite <- kron_assoc by auto_wf.
  restore_dims.
  rewrite (kron_assoc (_ ⊗ _)) by auto_wf.
  rewrite kron_mixed_product' by 
    solve [auto_wf | unify_pows_two; nia].
  rewrite 2 f_to_vec_merge, 2 n_cup_f_to_vec.
  restore_dims.
  distribute_scale.
  rewrite id_kron.
  f_equal.
  unfold b2R.
  rewrite 3 (if_dist R C), (if_dist C C).
  Csimpl.
  rewrite <- andb_if.
  apply f_equal_if; [|reflexivity..].
  apply Bool.eq_iff_eq_true.
  rewrite andb_true_iff, 3 forallb_seq0.
  setoid_rewrite Bool.eqb_true_iff.
  split.
  - intros Hf.
    split.
    + intros s Hs.
      do 2 simplify_bools_lia_one_kernel.
      rewrite Hf; f_equal; lia.
    + intros s Hs.
      do 2 simplify_bools_lia_one_kernel.
      rewrite Hf; f_equal; lia.
  - intros [Hf0 Hf1].
    intros s Hs.
    bdestruct (s <? n).
    + generalize (Hf1 s ltac:(lia)). 
      do 2 simplify_bools_lia_one_kernel.
      intros ->.
      f_equal; lia.
    + generalize (Hf0 (s - n)%nat ltac:(lia)).
      simplify_bools_lia_one_kernel.
      rewrite Nat.add_comm, Nat.sub_add by lia.
      intros ->.
      simplify_bools_lia_one_kernel.
      f_equal; lia.
Qed.

Lemma n_cup_split_add n m : 
  n_cup (n + m) ∝=
  zx_mid_comm n m n m ⟷
  (n_cup n ↕ n_cup m).
Proof.
  unfold proportional_by_1.
  unfold zx_mid_comm.
  rewrite zx_compose_spec.
  simpl_cast_semantics.
  rewrite 2!zx_stack_spec.
  rewrite n_wire_semantics.
  apply equal_on_basis_states_implies_equal; [now auto_wf..|].
  intros f.
  rewrite n_cup_f_to_vec.
  rewrite Mmult_assoc.
  rewrite (@zx_mid_comm_prf n m n m).
  restore_dims.
  rewrite kron_f_to_vec_eq by auto_wf.
  rewrite zx_stack_spec.
  rewrite n_wire_semantics.
  restore_dims.
  rewrite kron_f_to_vec_eq by auto_wf.
  rewrite 2!Mmult_1_l by auto_wf.
  rewrite zx_comm_semantics.
  rewrite f_to_vec_split'_eq.
  restore_dims.
  rewrite Kronecker.kron_comm_commutes_l by auto_wf.
  rewrite Kronecker.kron_comm_1_l, Mmult_1_r by auto_wf.
  rewrite f_to_vec_merge.
  restore_dims.
  rewrite f_to_vec_merge.
  restore_dims.
  rewrite f_to_vec_merge.
  rewrite <- (@zx_mid_comm_prf n n m m).
  rewrite f_to_vec_split'_eq.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite 2!n_cup_f_to_vec.
  restore_dims.
  distribute_scale.
  rewrite id_kron.
  f_equal.
  rewrite <- RtoC_mult, b2R_mult.
  do 2 f_equal.
  apply eq_iff_eq_true.
  rewrite andb_true_iff, 3!forallb_seq0.
  setoid_rewrite eqb_true_iff.
  rewrite forall_nat_lt_add.
  apply ZifyClasses.and_morph.
  - apply forall_lt_iff.
    intros k Hk.
    do 5 simplify_bools_lia_one_kernel.
    now rewrite add_sub', Nat.add_assoc.
  - apply forall_lt_iff.
    intros k Hk.
    cbn.
    do 4 simplify_bools_lia_one_kernel.
    replace (n + n + k - n - n) with k by lia.
    replace (n + n + (m + k) - (n + (n + m))) with k by lia.
    now rewrite 2!Nat.add_assoc.
Qed.

Lemma n_cup_grow_l n : 
  n_cup (S n) ∝=
  zx_mid_comm 1 n 1 n ⟷
  (⊃ ↕ n_cup n).
Proof.
  change (S n) with (1 + n).
  rewrite n_cup_split_add.
  now rewrite n_cup_1_cup.
Qed.

Lemma n_cap_split_add n m : 
  n_cap (n + m) ∝=
  (n_cap n ↕ n_cap m) ⟷
  zx_mid_comm n n m m.
Proof.
  unfold n_cap.
  rewrite n_cup_split_add.
  rewrite compose_transpose. 
  now rewrite zx_mid_comm_transpose.
Qed.

Lemma n_cup_add_natural {n0 n1 n2 n3 m0 m1} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1)
  (zx2 : ZX n2 m0) (zx3 : ZX n3 m1) : 
  zx0 ↕ zx1 ↕ (zx2 ↕ zx3) ⟷ n_cup (m0 + m1) ∝=
  zx_mid_comm _ _ _ _ ⟷
  ((zx0 ↕ zx2 ⟷ n_cup m0) ↕ (zx1 ↕ zx3 ⟷ n_cup m1)).
Proof.
  rewrite stack_compose_distr.
  rewrite n_cup_split_add.
  rewrite <- 2!compose_assoc.
  now rewrite zx_mid_comm_commutes_r.
Qed.

Lemma n_cap_add_natural {n0 n1 m0 m1 m2 m3} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1)
  (zx2 : ZX n0 m2) (zx3 : ZX n1 m3) : 
  n_cap (n0 + n1) ⟷ (zx0 ↕ zx1 ↕ (zx2 ↕ zx3)) ∝=
  ((n_cap n0 ⟷ (zx0 ↕ zx2)) ↕ (n_cap n1 ⟷ (zx1 ↕ zx3))) ⟷
  zx_mid_comm _ _ _ _.
Proof.
  apply transpose_diagrams_eq.
  rewrite 2!compose_transpose, 3!stack_transpose, n_cap_transpose.
  rewrite n_cup_add_natural.
  rewrite zx_mid_comm_transpose.
  rewrite (@stack_transpose 0 _ 0), 2!compose_transpose, 2!n_cap_transpose.
  reflexivity.
Qed.



Lemma n_stacked_caps_semantics n : 
  ⟦ n_stacked_caps n ⟧ = kron_n n (⟦ ⊃ ⟧).
Proof.
  unfold n_stacked_caps.
  rewrite cast_semantics_dim.
  unfold cast_semantics_dim_eqn.
  apply n_stack_semantics.
Qed.

Lemma n_stacked_cups_semantics n : 
  ⟦ n_stacked_cups n ⟧ = kron_n n (⟦ ⊂ ⟧).
Proof.
  unfold n_stacked_cups.
  rewrite cast_semantics_dim.
  unfold cast_semantics_dim_eqn.
  apply n_stack_semantics.
Qed.


Lemma n_stacked_caps_succ_prf {n} : 
  (S n + S n = 2 + (n + n))%nat.
Proof. lia. Qed.

Lemma n_stacked_caps_succ n : 
  n_stacked_caps (S n) ∝=
  cast _ _ n_stacked_caps_succ_prf eq_refl
    (⊃ ↕ n_stacked_caps n).
Proof.
  unfold n_stacked_caps.
  cbn.
  erewrite cast_stack_r, cast_contract_eq.
  cast_irrelevance.
  Unshelve. all: lia.
Qed.

Lemma n_cup_to_n_stacked_caps n : 
  n_cup n ∝= 
  zx_of_perm _ (kron_comm_perm 2 n) ⟷ n_stacked_caps n.
Proof.
  induction n.
  - unfold n_cup, n_stacked_caps.
    cbn.
    rewrite zx_of_perm_0.
    now rewrite stack_empty_l, cast_id.
  - rewrite n_cup_grow_l.
    rewrite n_stacked_caps_succ.
    rewrite IHn.
    rewrite <- (nwire_removal_l ⊃).
    rewrite stack_compose_distr, <- compose_assoc.
    apply compose_simplify_casted_abs;
    [lia|intros H..].
    + by_perm_eq_nosimpl.
      rewrite perm_of_zx_cast.
      cbn -[Nat.add].
      rewrite perm_of_zx_mid_comm.
      rewrite perm_of_zx_of_perm_eq_WF by 
        (replace (n + n) with (2 * n) by lia; auto_perm).
      rewrite 2!stack_perms_idn_idn.
      rewrite perm_of_zx_of_perm_eq_WF by 
        (replace (S n + S n) with (2 * S n) by lia; auto_perm).
      rewrite (WF_Perm_rw (kron_comm_perm_2_n_succ_alt _)) by auto_perm.
      replace (2 * n) with (n + n) by apply Nat.double_twice.
      apply compose_perm_eq_proper_l; [|split; auto_perm].
      rewrite <- Nat.add_assoc.
      replace (n + 1) with (S n) by lia.
      rewrite stack_perms_assoc.
      now replace (n + S n) with (S n + n) by lia.
    + rewrite cast_contract_eq', cast_id.
      now rewrite nwire_removal_l.
Qed.

Lemma n_stacked_caps_tranpose n : 
  (n_stacked_caps n) ⊤%ZX ∝= n_stacked_cups n.
Proof.
  unfold n_stacked_caps, n_stacked_cups.
  now rewrite cast_transpose, nstack_transpose.
Qed.

Lemma n_stacked_cups_tranpose n : 
  (n_stacked_cups n) ⊤%ZX ∝= n_stacked_caps n.
Proof.
  now rewrite <- n_stacked_caps_tranpose, 
    Proportional.transpose_involutive.
Qed.

Lemma zx_of_perm_transpose n f (Hf : permutation n f) : 
  (zx_of_perm n f) ⊤%ZX ∝=
  zx_of_perm n (perm_inv' n f).
Proof.
  rewrite <- nwire_removal_l.
  rewrite compose_zxperm_r_eq by auto_zxperm.
  rewrite Proportional.transpose_involutive.
  rewrite compose_zx_of_perm by auto_perm.
  rewrite perm_inv'_eq, perm_inv_linv_of_permutation by auto_perm.
  now rewrite zx_of_perm_idn.
Qed.

Lemma n_cap_to_n_stacked_cups n : 
  n_cap n ∝= 
  n_stacked_cups n ⟷ 
  zx_of_perm _ (kron_comm_perm n 2).
Proof. 
  unfold n_cap.
  rewrite n_cup_to_n_stacked_caps.
  rewrite compose_transpose.
  rewrite zx_of_perm_transpose by 
    (replace (n + n) with (2 * n) by lia; auto_perm).
  replace (perm_inv' (n + n)) with (perm_inv' (2 * n)) 
    by (f_equal; lia).
  rewrite kron_comm_perm_inv'.
  now rewrite n_stacked_caps_tranpose.
Qed.



Lemma n_cup_pullthrough_bot' {n n' m} (zx : ZX n m) (zx' : ZX n' m) : 
	zx ↕ zx' ⟷ n_cup m ∝= (zx ⟷ zx' ⊤) ↕ n_wire n' ⟷ n_cup n'.
Proof.
	now rewrite stack_split_diag, compose_assoc, n_cup_pullthrough_bot, 
		<- compose_assoc, <- stack_nwire_distribute_r.
Qed.

Lemma n_cup_pullthrough_top' {n n' m} (zx : ZX n m) (zx' : ZX n' m) : 
	zx ↕ zx' ⟷ n_cup m ∝= n_wire n ↕ (zx' ⟷ zx ⊤) ⟷ n_cup n.
Proof.
	now rewrite stack_split_antidiag, compose_assoc, n_cup_pullthrough_top, 
		<- compose_assoc, <- stack_nwire_distribute_l.
Qed.

Lemma n_cap_pullthrough_bot' {n n' m} (zx : ZX m n) (zx' : ZX m n') : 
	n_cap m ⟷ (zx ↕ zx') ∝= n_cap n' ⟷ ((zx' ⊤ ⟷ zx) ↕ n_wire n').
Proof.
	now rewrite stack_split_antidiag, <- compose_assoc, n_cap_pullthrough_bot, 
		compose_assoc, <- stack_nwire_distribute_r.
Qed.

Lemma n_cap_pullthrough_top' {n n' m} (zx : ZX m n) (zx' : ZX m n') : 
	n_cap m ⟷ (zx ↕ zx') ∝= n_cap n ⟷ (n_wire n ↕ (zx ⊤ ⟷ zx')).
Proof.
	now rewrite stack_split_diag, <- compose_assoc, n_cap_pullthrough_top, 
		compose_assoc, <- stack_nwire_distribute_l.
Qed.