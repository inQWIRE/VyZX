Require Import CoreData GadgetRules CoreAutomation StackComposeRules.

Open Scope ZX_scope.

(** Rules about states *)

Lemma state_0_defn : 
  state_0 ∝= /√2 .* X 0 1 0. 
Proof.
  rewrite state_0_defn'.
  rewrite gadget_is_scaled_empty; distribute_zxscale.
  rewrite stack_empty_l, const_of_zx_invsqrt2. 
  reflexivity.
Qed.

Lemma state_0_semantics : ⟦ state_0 ⟧ = ∣0⟩.
Proof.
  prep_matrix_equivalence.
  rewrite state_0_defn.
  rewrite zx_scale_semantics.
  compute_matrix (⟦ X 0 1 0 ⟧).
  rewrite kron_1_l by auto_wf.
  rewrite Cexp_0; Csimpl.
  unfold hadamard; simpl.
  rewrite make_WF_equiv.
  by_cell; autounfold with U_db; unfold list2D_to_matrix; simpl;
  [C_field; lca | lca].
Qed.


Lemma state_1_defn : 
  state_1 ∝= /√2 .* X 0 1 PI. 
Proof.
  rewrite state_1_defn'.
  rewrite gadget_is_scaled_empty; distribute_zxscale.
  rewrite stack_empty_l, const_of_zx_invsqrt2. 
  reflexivity.
Qed.

Lemma state_1_semantics : ⟦ state_1 ⟧ = ∣1⟩.
Proof.
  prep_matrix_equivalence.
  rewrite state_1_defn.
  rewrite zx_scale_semantics.
  compute_matrix (⟦ X 0 1 PI ⟧).
  rewrite kron_1_l by auto_wf.
  rewrite Cexp_PI.
  unfold hadamard; simpl.
  rewrite make_WF_equiv.
  by_cell; autounfold with U_db; unfold list2D_to_matrix; simpl;
  [lca | C_field; lca].
Qed.

Lemma state_plus_defn : 
  state_plus ∝= /√2 .* Z 0 1 0. 
Proof.
  rewrite state_plus_defn'.
  rewrite gadget_is_scaled_empty; distribute_zxscale.
  rewrite stack_empty_l, const_of_zx_invsqrt2. 
  reflexivity.
Qed.

Lemma state_plus_semantics : ⟦ state_plus ⟧ = ∣+⟩.
Proof.
  prep_matrix_equivalence.
  rewrite state_plus_defn.
  rewrite zx_scale_semantics.
  compute_matrix (⟦ Z 0 1 0 ⟧).
  rewrite Cexp_0.
  rewrite make_WF_equiv.
  unfold xbasis_plus;
  by_cell; autounfold with U_db; unfold list2D_to_matrix; simpl; lca.
Qed.

Lemma state_minus_defn : 
  state_minus ∝= /√2 .* Z 0 1 PI. 
Proof. 
  rewrite state_minus_defn'.
  rewrite gadget_is_scaled_empty; distribute_zxscale.
  rewrite stack_empty_l, const_of_zx_invsqrt2. 
  reflexivity.
Qed.

Lemma state_minus_semantics : ⟦ state_minus ⟧ = ∣-⟩.
Proof.
  prep_matrix_equivalence.
  rewrite state_minus_defn.
  rewrite zx_scale_semantics.
  compute_matrix (⟦ Z 0 1 PI ⟧).
  rewrite Cexp_PI.
  rewrite make_WF_equiv.
  unfold xbasis_minus;
  by_cell; autounfold with U_db; unfold list2D_to_matrix; simpl; lca.
Qed.


Lemma state_0_colorswap : ⊙ state_0 ∝= state_plus.
Proof.
  rewrite state_0_defn, state_plus_defn.
  rewrite zx_scale_colorswap.
  reflexivity.
Qed.

Lemma state_1_colorswap : ⊙ state_1 ∝= state_minus.
Proof.
  rewrite state_1_defn, state_minus_defn.
  rewrite zx_scale_colorswap.
  reflexivity.
Qed.

Lemma state_plus_colorswap : ⊙ state_plus ∝= state_0.
Proof.
  apply colorswap_diagrams_eq.
  rewrite colorswap_involutive.
  now rewrite state_0_colorswap.
Qed.

Lemma state_minus_colorswap : ⊙ state_minus ∝= state_1.
Proof.
  apply colorswap_diagrams_eq.
  rewrite colorswap_involutive.
  now rewrite state_1_colorswap.
Qed.

#[export] Hint Rewrite state_0_colorswap state_1_colorswap
  state_plus_colorswap state_minus_colorswap : colorswap_db.




Lemma semantics_compose_state_0_l {n} (zx : ZX 1 n) : 
  ⟦ state_0 ⟷ zx ⟧ = get_col (⟦ zx ⟧) 0.
Proof.
  simpl.
  rewrite state_0_semantics.
  rewrite qubit0_to_ei.
  now rewrite matrix_by_basis by lia.
Qed.

Lemma semantics_compose_state_1_l {n} (zx : ZX 1 n) : 
  ⟦ state_1 ⟷ zx ⟧ = get_col (⟦ zx ⟧) 1.
Proof.
  simpl.
  rewrite state_1_semantics.
  rewrite qubit1_to_ei.
  now rewrite matrix_by_basis by lia.
Qed.



Lemma semantics_by_states_1_n {n} (zx : ZX 1 n) : 
  ⟦ zx ⟧ = smash (⟦ state_0 ⟷ zx ⟧) (⟦ state_1 ⟷ zx ⟧).
Proof.
  prep_matrix_equivalence.
  rewrite semantics_compose_state_0_l, semantics_compose_state_1_l.
  intros i j Hi Hj.
  unfold smash, get_col.
  simpl in *.
  destruct j; [|replace j with O in * by lia];
  Modulus.bdestructΩ'.
Qed.

Lemma prop_eq_by_eq_on_states_1_n {n} (zx zx' : ZX 1 n) : 
  state_0 ⟷ zx ∝= state_0 ⟷ zx' ->
  state_1 ⟷ zx ∝= state_1 ⟷ zx' ->
  zx ∝= zx'.
Proof.
  intros H0 H1.
  prep_matrix_equivalence.
  rewrite 2 semantics_by_states_1_n.
  rewrite H0, H1.
  reflexivity.
Qed.

Lemma prop_eq_by_eq_on_states_step {n m} (zx zx' : ZX (S n) m) : 
  state_0 ↕ n_wire n ⟷ zx ∝= state_0 ↕ n_wire n ⟷ zx' ->
  state_1 ↕ n_wire n ⟷ zx ∝= state_1 ↕ n_wire n ⟷ zx' ->
  zx ∝= zx'.
Proof.
  intros H0 H1.
  prep_matrix_equivalence.
  intros i j Hi Hj.
  bdestruct (j <? 2 ^ n).
  - generalize (equal_f (equal_f H0 i) j).
    rewrite 2 zx_compose_spec, zx_stack_spec.
    rewrite state_0_semantics, n_wire_semantics.
    rewrite qubit0_to_ei.
    replace (2 ^ (1 + n))%nat with (2 * (2 ^ n))%nat by (simpl; lia).
    rewrite (Nat.pow_add_r 2 0 n), (Nat.pow_0_r).
    rewrite 2 Mmult_kron_e_i_I_r by solve [restore_dims; auto_wf | lia].
    rewrite 2 make_WF_equiv by lia.
    rewrite Nat.mul_0_r, Nat.add_0_l.
    easy.
  - generalize (equal_f (equal_f H1 i) (j - 2 ^ n)%nat).
    rewrite 2 zx_compose_spec, zx_stack_spec.
    rewrite state_1_semantics, n_wire_semantics.
    rewrite qubit1_to_ei.
    replace (2 ^ (1 + n))%nat with (2 * (2 ^ n))%nat by (simpl; lia).
    rewrite (Nat.pow_add_r 2 0 n), (Nat.pow_0_r).
    rewrite 2 Mmult_kron_e_i_I_r by solve [restore_dims; auto_wf | lia].
    rewrite 2 make_WF_equiv by (simpl in Hj; lia).
    rewrite Nat.mul_1_r.
    rewrite (Nat.add_comm (2^n) (j - _)), Nat.sub_add by lia.
    easy.
Qed.



Lemma prop_eq_by_eq_on_state_b_1_n {n} (zx zx' : ZX 1 n) : 
  (forall b, state_b b ⟷ zx ∝= state_b b ⟷ zx') ->
  zx ∝= zx'.
Proof.
  intros Hb.
  apply prop_eq_by_eq_on_states_1_n.
  - apply (Hb false).
  - apply (Hb true).
Qed.



Lemma prop_eq_by_eq_on_states_b_step {n m} (zx zx' : ZX (S n) m) : 
  (forall b, state_b b ↕ n_wire n ⟷ zx ∝= state_b b ↕ n_wire n ⟷ zx') ->
  zx ∝= zx'.
Proof.
  intros Hb.
  apply prop_eq_by_eq_on_states_step.
  - apply (Hb false).
  - apply (Hb true).
Qed.


Lemma prop_eq_by_eq_on_states {n m} (zx zx' : ZX n m) :
  (forall f, f_to_state n f ⟷ zx ∝= f_to_state n f ⟷ zx') ->
  zx ∝= zx'.
Proof.
  induction n.
  - intros Hf.
    specialize (Hf (fun _ => false)).
    simpl in Hf.
    now rewrite 2 compose_empty_l in Hf.
  - intros Hf.
    apply prop_eq_by_eq_on_states_b_step.
    intros b.
    apply IHn.
    intros f.
    rewrite <- 2 compose_assoc.
    rewrite <- push_out_top.
    generalize (Hf (fun n => match n with | O => b | S n' => f n' end)).
    intros Heq; apply Heq.
Qed.












Lemma state_0_to_b : state_0 = state_b false.
Proof. reflexivity. Qed.

Lemma state_1_to_b : state_1 = state_b true.
Proof. reflexivity. Qed.

Lemma state_b_semantics b : 
  ⟦ state_b b ⟧ = ket b.
Proof.
  destruct b.
  - apply state_1_semantics.
  - apply state_0_semantics.
Qed.


Lemma state_b_state_b_transpose b b' : 
	state_b b ⟷ (state_b b') ⊤ ∝=
	(b2R (eqb b b')) .* ⦰.
Proof.
	prep_matrix_equivalence.
	rewrite zx_compose_spec, semantics_transpose_comm, 
		2 state_b_semantics, zx_scale_semantics.
	by_cell. 
	destruct b, b'; lca.
Qed.

Lemma f_to_state_semantics n f : 
  ⟦ f_to_state n f ⟧ = f_to_vec n f.
Proof.
  revert f;
  induction n; intros f.
  - reflexivity. 
  - cbn [f_to_state].
    rewrite (@zx_stack_spec 0 1 0 n).
    rewrite state_b_semantics.
    rewrite (f_to_vec_split'_eq 1 n).
    rewrite IHn.
    f_equal.
    simpl.
    now rewrite kron_1_l by auto_wf.
Qed.

Lemma f_to_state_split n m f : 
  f_to_state (n + m) f ∝= f_to_state n f ↕ f_to_state m (fun i => f (n + i)%nat).
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite 3 f_to_state_semantics.
  now rewrite f_to_vec_split'_eq.
Qed.

Lemma f_to_state_merge n m f g : 
  f_to_state m f ↕ f_to_state n g ∝=
  f_to_state (m + n) (fun x => if x <? m then f x else g (x - m)%nat).
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite 3 f_to_state_semantics.
  now rewrite f_to_vec_merge.
Qed.


(* Rules about the zero element zx_zero *)


Lemma zx_zero_semantics n m : ⟦@zx_zero n m⟧ = Zero.
Proof.
  rewrite zx_zero_defn.
  rewrite zx_scale_semantics.
  apply Mscale_0_l.
Qed.

Lemma zx_scale_0_l {n m} (zx : ZX n m) : 
  C0 .* zx ∝= zx_zero.
Proof.
  prep_matrix_equivalence.
  rewrite zx_scale_semantics, zx_zero_semantics.
  now rewrite Mscale_0_l.
Qed.

Lemma zx_scale_0_r {n m} c : 
  c .* (@zx_zero n m) ∝= zx_zero.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite Cmult_0_r.
Qed.

Lemma stack_0_l {n0 m0 n1 m1} (zx : ZX n1 m1) : 
  (@zx_zero n0 m0) ↕ zx ∝= zx_zero.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

Lemma stack_0_r {n0 m0 n1 m1} (zx : ZX n0 m0) : 
  zx ↕ (@zx_zero n1 m1) ∝= zx_zero.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

Lemma compose_0_l {n m o} (zx : ZX m o) : 
  (@zx_zero n m) ⟷ zx ∝= zx_zero.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

Lemma compose_0_r {n m o} (zx : ZX n m) : 
  zx ⟷ (@zx_zero m o) ∝= zx_zero.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

Lemma cast_0 n m {n' m'} prfn prfm : 
  cast n m prfn prfm (@zx_zero n' m') = zx_zero.
Proof.
  now subst.
Qed.

Lemma n_stack_zx_zero k n m : k <> O ->
  k ⇑ (@zx_zero n m) ∝= zx_zero.
Proof.
  intros H.
  destruct k; [easy|].
  simpl.
  now rewrite stack_0_l.
Qed.

(* Lemma n_compose_zx_zero k n : k <> O -> 
  n_compose k (@zx_zero n n) ∝= zx_zero.
Proof.
  intros Hk.
  destruct k; [easy|].
  simpl.
  now rewrite compose_0_l.
Qed. *)

Lemma zx_zero_transpose n m : (@zx_zero n m) ⊤ ∝= zx_zero.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

Lemma zx_zero_adjoint n m : (@zx_zero n m) † ∝= zx_zero.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite Cconj_R, zx_scale_0_l.
Qed.

Lemma zx_zero_colorswap n m : ⊙ (@zx_zero n m) ∝= zx_zero.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

#[export] Hint Rewrite zx_zero_transpose : transpose_db.
#[export] Hint Rewrite zx_zero_adjoint : adjoint_db.
#[export] Hint Rewrite zx_zero_colorswap : colorswap_db.

