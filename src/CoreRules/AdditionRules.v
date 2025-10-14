Require Import CoreData CapCupRules StackRules StateRules ZXStateRules 
  ChoiJamiolchosky GadgetRules ControlizerRules.
Import Setoid.

(** Rules about the addition of ZX-diagrams, including the 
  correctness of [zx_of_matrix], proving universality *)

Lemma zx_plus_defn' {n m} (zx0 zx1 : ZX n m) : 
  zx0 .+ zx1 ∝= (/√2)^(n+m) .* 
    state_to_proc (state_1 ⟷ 
      sum_controlizer (controlizer zx0) (controlizer zx1)).
Proof.
  rewrite zx_plus_defn.
  rewrite gadget_is_scaled_empty, zx_scale_stack_distr_l, stack_empty_l.
  rewrite const_of_zx_n_stack, const_of_zx_invsqrt2.
  reflexivity.
Qed.

Lemma zx_plus_semantics {n m} (zx0 zx1 : ZX n m) : 
  ⟦ zx0 .+ zx1 ⟧ = 
  (⟦ zx0 ⟧ .+ ⟦ zx1 ⟧)%M.
Proof.
  rewrite zx_plus_defn'.
  rewrite zx_scale_semantics.
  unfold state_to_proc.
  rewrite zx_compose_spec, zx_stack_spec.
  simpl_cast_semantics.
  rewrite zx_stack_spec, 2 n_wire_semantics.
  rewrite sum_controlizer_state_1_semantics by (apply zx_is_controlized).
  rewrite 2 controlizer_state_1.
  rewrite 2 zx_scale_semantics.
  rewrite <- Mscale_plus_distr_r.
  distribute_scale.
  restore_dims.
  unify_pows_two.
  rewrite Mscale_mult_dist_r, Mscale_assoc.
  rewrite <- Cpow_mul_l, Cinv_l, Cpow_1_l, Mscale_1_l by nonzero.
  distribute_plus.
  restore_dims.
  unify_pows_two.
  rewrite Mmult_plus_distr_l.
  etransitivity. 2:{
    rewrite <- (proc_to_state_to_proc zx0), <- (proc_to_state_to_proc zx1).
    unfold state_to_proc.
    unfold state_to_proc.
    rewrite 2 zx_compose_spec, zx_stack_spec.
    simpl_cast_semantics.
    rewrite 2 zx_stack_spec, 2 n_wire_semantics.
    reflexivity.
  }
  reflexivity.
Qed.



Lemma zx_plus_0_l {n m} (zx : ZX n m) : 
  zx_zero .+ zx ∝= zx.
Proof.
  prep_matrix_equivalence.
  rewrite zx_plus_semantics, zx_zero_semantics, Mplus_0_l.
  reflexivity.
Qed.

Lemma zx_plus_0_r {n m} (zx : ZX n m) : 
  zx .+ zx_zero ∝= zx.
Proof.
  prep_matrix_equivalence.
  rewrite zx_plus_semantics, zx_zero_semantics, Mplus_0_r.
  reflexivity.
Qed.

(* TODO: Other distributivities *)

Lemma compose_plus_distr_l {n m o} (zx zx' : ZX n m) (zx1 : ZX m o) : 
	(zx .+ zx') ⟷ zx1 ∝= zx ⟷ zx1 .+ zx' ⟷ zx1.
Proof.
	prep_matrix_equivalence.
	rewrite zx_plus_semantics, 3 zx_compose_spec, zx_plus_semantics.
	now rewrite Mmult_plus_distr_l by auto_wf.
Qed.

Lemma compose_plus_distr_r {n m o} (zx : ZX n m) (zx1 zx1' : ZX m o) : 
	zx ⟷ (zx1 .+ zx1') ∝= zx ⟷ zx1 .+ zx ⟷ zx1'.
Proof.
	prep_matrix_equivalence.
	rewrite zx_plus_semantics, 3 zx_compose_spec, zx_plus_semantics.
	now rewrite Mmult_plus_distr_r by auto_wf.
Qed.

Lemma stack_plus_distr_l {n m o p} (zx zx' : ZX n m) (zx1 : ZX o p) : 
	(zx .+ zx') ↕ zx1 ∝= zx ↕ zx1 .+ zx' ↕ zx1.
Proof.
	prep_matrix_equivalence.
	rewrite zx_plus_semantics, 3 zx_stack_spec, zx_plus_semantics.
	now rewrite kron_plus_distr_r by auto_wf.
Qed.

Lemma stack_plus_distr_r {n m o p} (zx : ZX n m) (zx1 zx1' : ZX o p) : 
	zx ↕ (zx1 .+ zx1') ∝= zx ↕ zx1 .+ zx ↕ zx1'.
Proof.
	prep_matrix_equivalence.
	rewrite zx_plus_semantics, 3 zx_stack_spec, zx_plus_semantics.
	now rewrite kron_plus_distr_l by auto_wf.
Qed.

Lemma zx_scale_plus_distr_r {n m} c (zx0 zx1 : ZX n m) : 
	c .* (zx0 .+ zx1) ∝= c .* zx0 .+ c .* zx1.
Proof.
	prep_matrix_equivalence.
	rewrite zx_plus_semantics, 3 zx_scale_semantics, zx_plus_semantics.
	now rewrite Mscale_plus_distr_r.
Qed.

Lemma zx_scale_plus_distr_l {n m} c d (zx : ZX n m) : 
	(c + d) .* zx ∝= c .* zx .+ d .* zx.
Proof.
	prep_matrix_equivalence.
	rewrite zx_plus_semantics, 3 zx_scale_semantics.
	now rewrite Mscale_plus_distr_l.
Qed.



Lemma zx_plus_comm {n m} (zx0 zx1 : ZX n m) : 
  zx0 .+ zx1 ∝= zx1 .+ zx0.
Proof.
  prep_matrix_equivalence.
  rewrite 2 zx_plus_semantics, Mplus_comm.
  reflexivity.
Qed.

Lemma zx_plus_assoc {n m} (zx0 zx1 zx2 : ZX n m) : 
  zx0 .+ (zx1 .+ zx2) ∝= zx0 .+ zx1 .+ zx2.
Proof.
  prep_matrix_equivalence.
  rewrite 4 zx_plus_semantics, Mplus_assoc.
  reflexivity.
Qed.

(* TODO: Other comm/assoc helpers... *)




Lemma zx_sum_S {n m} (f : nat -> ZX n m) k : 
  zx_sum f (S k) ∝= zx_sum f k .+ f k.
Proof.
  destruct k; [|reflexivity].
  simpl.
  now rewrite zx_plus_0_l.
Qed.



(* TODO: Other morphism instance (proportionality) *)
Add Parametric Morphism {n m} : (@zx_sum n m) with signature
  Morphisms.pointwise_relation nat proportional_by_1 ==> eq ==> proportional_by_1
  as zx_sum_mor.
Proof.
  intros f g Hfg.
  intros k.
  induction k; [reflexivity|].
  now rewrite 2 zx_sum_S, IHk, Hfg.
Qed.

Lemma zx_sum_semantics {n m} (f : nat -> ZX n m) k : 
  ⟦ zx_sum f k ⟧ = big_sum (fun i => ⟦ f i ⟧) k.
Proof.
  induction k.
  - apply zx_zero_semantics.
  - rewrite zx_sum_S.
    cbn.
    rewrite zx_plus_semantics, IHk.
    reflexivity.
Qed.

Lemma state_of_vector_semantics {n} (v : Vector (2^n)) : WF_Matrix v -> 
  ⟦ state_of_vector v ⟧ = v.
Proof.
  intros Hv.
  prep_matrix_equivalence.
  intros i j Hi Hj.
  replace j with O in * by (simpl in Hj; lia); clear j Hj.
  unfold state_of_vector.
  rewrite zx_sum_semantics, Msum_Csum.
  apply big_sum_unique.
  exists i.
  split; [auto|].
  split.
  - rewrite zx_scale_semantics, f_to_state_semantics.
    rewrite <- basis_f_to_vec_alt by auto.
    rewrite basis_vector_eq_e_i by auto.
    unfold scale, e_i.
    bdestructΩ'; lca.
  - intros j Hj Hji.
    rewrite zx_scale_semantics, f_to_state_semantics.
    rewrite <- basis_f_to_vec_alt by auto.
    rewrite basis_vector_eq_e_i by auto.
    unfold scale, e_i.
    bdestructΩ'; lca.
Qed.

Lemma zx_of_matrix_semantics {n m} (A : Matrix (2^m) (2^n)) : WF_Matrix A -> 
  ⟦ zx_of_matrix A ⟧ = A.
Proof.
  intros HA.
  prep_matrix_equivalence.
  unfold zx_of_matrix.
  (* TODO: Lemma state_to_proc_semantics *)
  unfold state_to_proc.
  rewrite zx_compose_spec.
  simpl_cast_semantics.
  rewrite (zx_stack_spec _ _ _ _ (n_wire n)).
  rewrite state_of_vector_semantics by auto_wf.
  rewrite n_wire_semantics, kron_id_dist_l by auto_wf.
  restore_dims. 
  rewrite <- kron_assoc, id_kron by auto_wf.
  unify_pows_two.
  rewrite <- Mmult_assoc.
  rewrite zx_stack_spec, n_wire_semantics.
  restore_dims.
  rewrite <- kron_split_diag by auto_wf.
  rewrite (kron_split_antidiag _ A), kron_1_l by auto_wf.
  rewrite <- (Mmult_1_r _ _ A) at 2 by auto_wf.
  unify_pows_two.
  rewrite Mmult_assoc.
  (* rewrite Nat.add_0_r. *)
  apply mmult_mat_equiv_morph; [reflexivity|].
  generalize (big_yank_r n (Nat.add_assoc _ _ _) eq_refl (Nat.add_0_r _)).
  unfold proportional_by_1.
  cbn [Nat.add].
  simpl_cast_semantics.
  intros H.
  rewrite <- n_wire_semantics.
  etransitivity; [|now rewrite <- H].
  rewrite zx_compose_spec.
  simpl_cast_semantics.
  rewrite zx_stack_spec.
  restore_dims.
  pose proof (zx_stack_spec _ _ _ _ (n_cup n) (n_wire n)) as Hrw.
  cbn [Nat.add] in Hrw.
  rewrite Hrw.
  unify_pows_two.
  reflexivity.
Qed.


Require Import ZXpermFacts.


Lemma zx_of_matrix'_semantics {n m} (A : Matrix (2^m) (2^n)) : WF_Matrix A -> 
  ⟦ zx_of_matrix' A ⟧ = A.
Proof.
  intros HA.
  prep_matrix_equivalence.
  unfold zx_of_matrix'.
  rewrite zx_sum_semantics.
  erewrite big_sum_eq_bounded. 2:{
    intros i Hi.
    rewrite zx_sum_semantics.
    eapply big_sum_eq_bounded.
    intros j Hj.
    rewrite zx_scale_semantics.
    rewrite zx_compose_spec, semantics_transpose_comm.
    rewrite 2 f_to_state_semantics, <- 2 basis_f_to_vec_alt by easy.
    rewrite 2 basis_vector_eq_e_i by easy.
    reflexivity.
  }
  intros i' j' Hi' Hj'.
  rewrite Msum_Csum.
  erewrite big_sum_eq_bounded. 2:{
    intros i Hi.
    rewrite Msum_Csum.
    erewrite big_sum_eq_bounded. 2:{
      intros j Hj.
      unfold scale.
      cbn.
      unfold Matrix.transpose.
      rewrite Cplus_0_l.
      unfold e_i.
      cbn.
      replace_bool_lia (i' <? 2 ^ m) true.
      replace_bool_lia (j' <? 2 ^ n) true.
      rewrite 4 andb_true_r.
      rewrite Kronecker.if_mult_and, Kronecker.if_mult_dist_l.
      rewrite andb_comm, andb_if, (Nat.eqb_sym j'), (Nat.eqb_sym i').
      reflexivity.
    }
    etransitivity; 
    [refine (big_sum_if_eq _ _ j')|].
    replace_bool_lia (j' <? 2 ^ n) true.
    reflexivity.
  }
  etransitivity; 
  [refine (big_sum_if_eq _ _ i')|].
  replace_bool_lia (i' <? 2 ^ m) true.
  reflexivity.
Qed.


Lemma X_0_1_decomp α : 
	X 0 1 α ∝= (1 + Cexp α)/√2 .* state_0 .+ 
		(1 - Cexp α)/√2 .* state_1.
Proof.
	rewrite X_to_Z, compose_empty_l.
	cbn.
	rewrite stack_empty_r_fwd, cast_id.
	prep_matrix_equivalence.
	rewrite zx_plus_semantics, 2 zx_scale_semantics, 
		state_0_semantics, state_1_semantics.
	by_cell; autounfold with U_db; cbn; lca.
Qed.

Lemma Z_0_1_decomp β : Z 0 1 β ∝= state_0 .+ Cexp β .* state_1.
Proof.
	prep_matrix_equivalence.
	rewrite zx_plus_semantics, zx_scale_semantics, 
		state_0_semantics, state_1_semantics.
	by_cell; cbn; lca.
Qed.


Lemma wire_decomp : — ∝= state_0 ⊤ ⟷ state_0 .+ 
  state_1 ⊤ ⟷ state_1.
Proof.
  prep_matrix_equivalence.
  rewrite zx_plus_semantics, 2 zx_compose_spec, 2 semantics_transpose_comm, 
    state_0_semantics, state_1_semantics.
  by_cell; lca.
Qed.

Lemma X_0_2_decomp α : 
  X 0 2 α ∝= (C1 + Cexp α) / C2 .* (state_0 ↕ state_0 .+ state_1 ↕ state_1) .+ 
    (C1 - Cexp α) / C2 .* (state_0 ↕ state_1 .+ state_1 ↕ state_0).
Proof.
  rewrite X_to_Z, compose_empty_l.
  cbn.
  rewrite stack_empty_r_fwd, cast_id.
  prep_matrix_equivalence.
  rewrite zx_plus_semantics, 2 zx_scale_semantics, 2 zx_plus_semantics.
  rewrite 4 (zx_stack_spec 0 1 0 1), state_0_semantics, state_1_semantics.
  by_cell; 
  lazy -[Cplus Cminus Cmult Cdiv Cinv RtoC sqrt 
    Q2R IZR Cexp PI sin cos Copp];
    unfold Cdiv; Csimpl; group_radicals; try lca.
Qed.


Lemma Z_2_1_state_b_bot b α : 
  — ↕ state_b b ⟷ Z 2 1 α ∝= 
  (if b then Cexp α else C1) .* ((state_b b) ⊤ ⟷ state_b b).
Proof.
  rewrite wire_decomp.
  rewrite stack_plus_distr_l, compose_plus_distr_l.
  rewrite <- (compose_empty_l (state_b b)) at 1 2.
  rewrite 2 stack_compose_distr.
  rewrite 2 compose_assoc.
  change state_0 with (state_b false).
  change state_1 with (state_b true).
  rewrite 2 Z_2_1_states_b.
  cbn.
  rewrite 2 stack_empty_r_fwd, 2 cast_id.
  distribute_zxscale.
  destruct b; rewrite zx_scale_0_l, 1?zx_plus_0_r, 1?zx_plus_0_l;
  reflexivity.
Qed.

Lemma Z_2_1_state_b_top b α : 
  state_b b ↕ — ⟷ Z 2 1 α ∝= 
  (if b then Cexp α else C1) .* ((state_b b) ⊤ ⟷ state_b b).
Proof.
  rewrite stack_comm, zx_comm_0_l, cast_id, nwire_removal_l,
    compose_assoc, Z_zx_comm_absorbtion_left.
  apply Z_2_1_state_b_bot.
Qed.

Lemma X_2_1_state_b_bot b α : 
  — ↕ state_b b ⟷ X 2 1 α ∝= 
  (/ √ 2) .* X 1 1 (if b then PI + α else α).
Proof.
  rewrite state_b_defn', gadget_is_scaled_empty, const_of_zx_invsqrt2.
  distribute_zxscale.
  rewrite stack_empty_l.
  rewrite zx_scale_stack_distr_r, zx_scale_compose_distr_l.
  rewrite wire_to_n_wire, dominated_X_spider_fusion_bot_right.
  now destruct b; rewrite ?Rplus_0_l.
Qed.

Lemma X_2_1_state_b_top b α : 
  state_b b ↕ — ⟷ X 2 1 α ∝= 
  (/ √ 2) .* X 1 1 (if b then PI + α else α).
Proof.
  rewrite stack_comm, zx_comm_0_l, cast_id, nwire_removal_l,
    compose_assoc, X_zx_comm_absorbtion_left.
  apply X_2_1_state_b_bot.
Qed.