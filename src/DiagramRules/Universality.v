Require Import QuantumLib.Kronecker.
Require Import CoreData.
Require Import CoreRules.
Require Import Soundness Scalars.


(* FIXME: Move to ZXrules *)
Lemma Z_phase_simplify n m α β : Cexp α = Cexp β -> 
  Z n m α ∝= Z n m β.
Proof.
  intros Heq. 
  hnf.
  simpl.
  unfold Z_semantics.
  rewrite Heq.
  reflexivity.
Qed.

Lemma X_phase_simplify n m α β : Cexp α = Cexp β -> 
  X n m α ∝= X n m β.
Proof.
  intros Heq. 
  colorswap_of (Z_phase_simplify n m α β Heq).
Qed.

Lemma Z_add_2_pi_r n m α : 
  Z n m (α + 2 * PI) ∝= Z n m α.
Proof.
  apply Z_phase_simplify.
  rewrite Cexp_add, Cexp_2PI, Cmult_1_r.
  reflexivity.
Qed.

Lemma X_add_2_pi_r n m α : 
  X n m (α + 2 * PI) ∝= X n m α.
Proof.
  colorswap_of (Z_add_2_pi_r n m α).
Qed.

Lemma Z_add_2_pi_l n m α : 
  Z n m (2 * PI + α) ∝= Z n m α.
Proof.
  apply Z_phase_simplify.
  rewrite Cexp_add, Cexp_2PI, Cmult_1_l.
  reflexivity.
Qed.

Lemma X_add_2_pi_l n m α : 
  X n m (2 * PI + α) ∝= X n m α.
Proof.
  colorswap_of (Z_add_2_pi_l n m α).
Qed.

Lemma Z_2_pi n m :
  Z n m (2 * PI) ∝= Z n m 0.
Proof.
  apply Z_phase_simplify.
  now rewrite Cexp_2PI, Cexp_0.
Qed.

Lemma X_2_pi n m :
  X n m (2 * PI) ∝= X n m 0.
Proof.
  colorswap_of (Z_2_pi n m).
Qed.

Lemma Z_eq_2_pi n m α : α = Rmult 2 PI ->
  Z n m α ∝= Z n m 0.
Proof.
  intros ->.
  apply Z_2_pi.
Qed.

Lemma X_eq_2_pi n m α : α = Rmult 2 PI ->
  X n m α ∝= X n m 0.
Proof.
  intros ->.
  apply X_2_pi.
Qed.

Lemma Z_is_wire : Z 1 1 0 ∝= —.
Proof.
  prep_matrix_equivalence.
  by_cell; unfold I; simpl; 
  now rewrite 1?Cexp_0.
Qed.

Lemma X_is_wire : X 1 1 0 ∝= —.
Proof.
  colorswap_of Z_is_wire.
Qed.



Notation State := (ZX 0 1).


Definition state_0 : State := /√2 .* X 0 1 0.
Lemma state_0_semantics : ⟦ state_0 ⟧ = ∣0⟩.
Proof.
  prep_matrix_equivalence.
  unfold state_0.
  rewrite zx_scale_semantics.
  compute_matrix (⟦ X 0 1 0 ⟧).
  rewrite kron_1_l by auto_wf.
  rewrite Cexp_0; Csimpl.
  unfold hadamard; simpl.
  rewrite make_WF_equiv.
  by_cell; autounfold with U_db; unfold list2D_to_matrix; simpl;
  [C_field; lca | lca].
Qed.

Lemma state_0_defn : 
  state_0 = /√2 .* X 0 1 0. 
Proof. reflexivity. Qed.

(* Don't want this to reduce, ever. *)
Global Opaque state_0.

Definition state_1 : State := /√2 .* X 0 1 PI.
Lemma state_1_semantics : ⟦ state_1 ⟧ = ∣1⟩.
Proof.
  prep_matrix_equivalence.
  unfold state_1.
  rewrite zx_scale_semantics.
  compute_matrix (⟦ X 0 1 PI ⟧).
  rewrite kron_1_l by auto_wf.
  rewrite Cexp_PI.
  unfold hadamard; simpl.
  rewrite make_WF_equiv.
  by_cell; autounfold with U_db; unfold list2D_to_matrix; simpl;
  [lca | C_field; lca].
Qed.

Lemma state_1_defn : 
  state_1 = /√2 .* X 0 1 PI. 
Proof. reflexivity. Qed.

(* Don't want this to reduce, ever. *)
Global Opaque state_1.

Definition state_plus : State := /√2 .* Z 0 1 0.
Lemma state_plus_semantics : ⟦ state_plus ⟧ = ∣+⟩.
Proof.
  prep_matrix_equivalence.
  unfold state_plus.
  rewrite zx_scale_semantics.
  compute_matrix (⟦ Z 0 1 0 ⟧).
  rewrite Cexp_0.
  rewrite make_WF_equiv.
  unfold xbasis_plus;
  by_cell; autounfold with U_db; unfold list2D_to_matrix; simpl; lca.
Qed.

Lemma state_plus_defn : 
  state_plus = /√2 .* Z 0 1 0. 
Proof. reflexivity. Qed.

(* Don't want this to reduce, ever. *)
Global Opaque state_plus.

Definition state_minus : State := /√2 .* Z 0 1 PI.
Lemma state_minus_semantics : ⟦ state_minus ⟧ = ∣-⟩.
Proof.
  prep_matrix_equivalence.
  unfold state_minus.
  rewrite zx_scale_semantics.
  compute_matrix (⟦ Z 0 1 PI ⟧).
  rewrite Cexp_PI.
  rewrite make_WF_equiv.
  unfold xbasis_minus;
  by_cell; autounfold with U_db; unfold list2D_to_matrix; simpl; lca.
Qed.

Lemma state_minus_defn : 
  state_minus = /√2 .* Z 0 1 PI. 
Proof. reflexivity. Qed.

(* Don't want this to reduce, ever. *)
Global Opaque state_minus.

Lemma state_0_colorswap : ⊙ state_0 ∝= state_plus.
Proof.
  rewrite state_0_defn.
  rewrite zx_scale_colorswap.
  reflexivity.
Qed.

Lemma state_1_colorswap : ⊙ state_1 ∝= state_minus.
Proof.
  rewrite state_1_defn.
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


(* @nocheck name *)
Definition NOT : ZX 1 1 := X 1 1 PI.
Lemma not_defn : NOT = X 1 1 PI.
Proof. reflexivity. Qed.
Global Opaque NOT.

Lemma not_state_1 : state_1 ⟷ NOT ∝= state_0.
Proof.
  rewrite state_1_defn, not_defn.
  distribute_zxscale.
  rewrite X_spider_1_1_fusion.
  rewrite X_eq_2_pi by lra.
  now rewrite state_0_defn.
Qed.

Lemma not_state_0 : state_0 ⟷ NOT ∝= state_1.
Proof.
  rewrite state_0_defn, not_defn.
  distribute_zxscale.
  rewrite X_spider_1_1_fusion.
  rewrite Rplus_0_l.
  now rewrite state_1_defn.
Qed.

Lemma not_not: NOT ⟷ NOT ∝= —.
Proof.
  rewrite not_defn.
  rewrite X_spider_1_1_fusion.
  rewrite X_eq_2_pi by lra.
  now rewrite X_is_wire.
Qed.

Definition state_b (b : bool) := if b then state_1 else state_0.

Lemma state_b_defn b : state_b b = /√2 .* X 0 1 (if b then PI else 0).
Proof.
  unfold state_b.
  rewrite state_0_defn, state_1_defn.
  now destruct b.
Qed.

Lemma not_state_b b : state_b b ⟷ NOT ∝= state_b (negb b).
Proof.
  destruct b.
  - apply not_state_1.
  - apply not_state_0.
Qed.


Definition is_controlled_pair {n m} (zx0 zx1 : ZX n m) 
  (czx : ZX (1 + n) (1 + m)) :=
  state_0 ↕ n_wire n ⟷ czx ∝= state_0 ↕ zx0 /\
  state_1 ↕ n_wire n ⟷ czx ∝= state_1 ↕ zx1.

Definition is_controlled {n} (zx : ZX n n) (czx : ZX (1 + n) (1 + n)) :=
  is_controlled_pair (n_wire n) zx czx.

Lemma is_controlled_pair_iff_bool {n m} (zx0 zx1 : ZX n m) czx : 
  is_controlled_pair zx0 zx1 czx <-> forall b : bool,
    state_b b ↕ n_wire n ⟷ czx ∝=
    state_b b ↕ if b then zx1 else zx0.
Proof.
  split.
  - intros [H0 H1] [].
    + apply H1.
    + apply H0.
  - intros Hb.
    split; 
    [generalize (Hb false) | generalize (Hb true)];
    simpl;
    easy.
Qed.

Lemma is_controlled_iff_bool {n} (zx : ZX n n) czx : 
  is_controlled zx czx <-> forall b : bool,
    state_b b ↕ n_wire n ⟷ czx ∝=
    state_b b ↕ if b then zx else n_wire n.
Proof. 
  apply is_controlled_pair_iff_bool.
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

Lemma controlled_pair_semantics {n m} (zx0 zx1 : ZX n m) czx : 
  is_controlled_pair zx0 zx1 czx -> 
  ⟦ czx ⟧ = ⟦ zx0 ⟧ .⊕ ⟦ zx1 ⟧.
Proof.
  unfold is_controlled_pair.
  unfold proportional_by_1.
  cbn [ZX_semantics].
  rewrite state_0_semantics, state_1_semantics, n_wire_semantics.
  rewrite qubit0_to_ei, qubit1_to_ei.
  rewrite 3 Nat.pow_add_r, Nat.pow_0_r.
  (* restore_dims. *)
  rewrite 2 Mmult_kron_e_i_I_r; try solve [restore_dims; auto_wf | simpl; lia].
  intros [Hczx0 Hczx1].
  prep_matrix_equivalence.
  intros i j Hi Hj.
  unfold direct_sum.
  bdestruct (j <? 2 ^ n).
  - generalize (equal_f (equal_f Hczx0 i) j).
    rewrite make_WF_equiv by (simpl in *; lia).
    rewrite Nat.mul_0_r, Nat.add_0_l.
    intros ->.
    unfold kron, e_i.
    assert (i / 2^m < 2)%nat by 
      (change (2^1)%nat with 2%nat in *; Modulus.show_moddy_lt).
    Modulus.simplify_bools_lia_one_kernel.
    rewrite (Nat.div_small j) by lia.
    rewrite Nat.eqb_refl, andb_true_r.
    pose proof (Nat.div_small_iff i (2^m) (Modulus.pow2_nonzero m)).
    bdestruct (i / 2 ^ m =? 0); Csimpl.
    + f_equal; apply Nat.mod_small; lia.
    + symmetry.
      apply (WF_ZX _ _ zx0); lia.
  - generalize (equal_f (equal_f Hczx1 i) (j - 2 ^ n)%nat).
    rewrite make_WF_equiv by (simpl in *; lia).
    rewrite Nat.mul_1_r, (Nat.add_comm (2^n) (j-_)), Nat.sub_add by lia.
    intros ->.
    unfold kron, e_i.
    assert (i / 2^m < 2)%nat by 
      (change (2^1)%nat with 2%nat in *; Modulus.show_moddy_lt).
    Modulus.simplify_bools_lia_one_kernel.
    rewrite (Nat.div_small (j - _)) by (simpl in *; lia).
    rewrite Nat.eqb_refl, andb_true_r.
    pose proof (Nat.div_small_iff i (2^m) (Modulus.pow2_nonzero m)).
    bdestruct (i / 2 ^ m =? 1); Csimpl.
    + Modulus.bdestructΩ'. 
      simpl in *.
      rewrite (Modulus.mod_n_to_2n i) by lia.
      rewrite Nat.mod_small by lia.
      reflexivity.
    + symmetry.
      Modulus.bdestructΩ'.
      apply (WF_ZX _ _ zx0); lia.
Qed.

Lemma is_controlled_pair_swap {n m} (zx0 zx1 : ZX n m) czx : 
  is_controlled_pair zx0 zx1 czx -> 
  is_controlled_pair zx1 zx0 (NOT ↕ n_wire n ⟷ czx ⟷ (NOT ↕ n_wire m)).
Proof.
  rewrite 2 is_controlled_pair_iff_bool.
  intros Hczx.
  intros b.
  rewrite <- 2 compose_assoc.
  rewrite <- stack_nwire_distribute_r.
  rewrite not_state_b, Hczx.
  rewrite <- stack_compose_distr, nwire_removal_r.
  rewrite not_state_b.
  now destruct b.
Qed.


















Definition cnot : ZX 2 2 := 
  √2 .* ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 0)).

Lemma cnot_is_controlled_not: is_controlled NOT cnot.
Proof.
  apply is_controlled_iff_bool.
  intros b.
  unfold cnot.
  rewrite state_b_defn.
  distribute_zxscale.
  rewrite <- compose_assoc.
  rewrite <- stack_compose_distr.
  assert (Hbeq : (if b then PI else 0) = 
    Rmult (INR (if b then 1 else 0)) PI) by (destruct b; simpl; lra).
  rewrite Hbeq.
  rewrite (to_scale X_state_copy).
  (* rewrite Cexp_0, Cminus_diag by lca. *)
  (* Csimpl. *)
  distribute_zxscale.
  rewrite <- Hbeq.
  rewrite cast_id.
  cbn [n_stack].
  rewrite stack_empty_r, cast_id.
  rewrite nwire_removal_l.
  rewrite (stack_assoc (X 0 1 _) (X 0 1 _) —), 
    cast_id.
  rewrite <- (stack_compose_distr (X 0 1 _) — (X 0 1 _ ↕ —)
    (X 2 1 _)).
  rewrite wire_removal_r.
  rewrite wire_to_n_wire.
  rewrite <- X_appendix_rot_l, Rplus_0_r.
  apply zx_scale_simplify_eq; 
  [autorewrite with RtoC_db; rewrite <- RtoC_pow; simpl; now C_field|].
  apply stack_simplify_eq; [reflexivity|].
  destruct b; [reflexivity|].
  now rewrite X_is_wire, wire_to_n_wire.
  Unshelve. all: reflexivity.
Qed.

(* FIX ME: Add when we have diag from Qlib, and move *)
(* Lemma Z_11_semantics α : ⟦ Z 1 1 α ⟧ = 
  diag (make_WF (list2D_to_matrix [[C1];[Cexp α]])).
Proof. *)


Lemma X_to_Z n m α : X n m α ∝= n ↑ □ ⟷ Z n m α ⟷ m ↑ □.
Proof.
  rewrite compose_assoc, <- colorswap_is_bihadamard.
  reflexivity.
Qed.

Lemma Z_to_X n m α : Z n m α ∝= n ↑ □ ⟷ X n m α ⟷ m ↑ □.
Proof.
  colorswap_of (X_to_Z n m α).
Qed.

Lemma Z_11_to_X_11 α : Z 1 1 α ∝= □ ⟷ X 1 1 α ⟷ □.
Proof.
  rewrite Z_to_X.
  simpl.
  rewrite stack_empty_r, cast_id.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma X_11_to_Z_11 α : X 1 1 α ∝= □ ⟷ Z 1 1 α ⟷ □.
Proof.
  colorswap_of (Z_11_to_X_11 α).
Qed.



Lemma Z_11_state_0 α : state_0 ⟷ Z 1 1 α ∝= state_0.
Proof. 
  prep_matrix_equivalence.
  simpl.
  rewrite state_0_semantics.
  compute_matrix (Z_semantics 1 1 α).
  rewrite make_WF_equiv.
  by_cell; autounfold with U_db; unfold list2D_to_matrix; cbn; lca.
Qed.

Lemma Z_11_state_1 α : state_1 ⟷ Z 1 1 α ∝= Cexp α .* state_1.
Proof. 
  prep_matrix_equivalence.
  simpl.
  rewrite zx_scale_semantics, state_1_semantics.
  compute_matrix (Z_semantics 1 1 α).
  rewrite make_WF_equiv.
  by_cell; autounfold with U_db; unfold list2D_to_matrix; cbn; lca.
Qed.

Lemma X_11_state_plus α : state_plus ⟷ X 1 1 α ∝= state_plus.
Proof.
  colorswap_of Z_11_state_0.
Qed.

Lemma X_11_state_minus α : state_minus ⟷ X 1 1 α ∝= Cexp α .* state_minus.
Proof.
  colorswap_of Z_11_state_1.
Qed.

Lemma Z_11_pi_state_plus : state_plus ⟷ Z 1 1 PI ∝= state_minus.
Proof.
  rewrite state_plus_defn.
  distribute_zxscale.
  rewrite Z_spider_1_1_fusion.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma Z_11_pi_state_minus : state_minus ⟷ Z 1 1 PI ∝= state_plus.
Proof.
  rewrite state_minus_defn.
  distribute_zxscale.
  rewrite Z_spider_1_1_fusion.
  rewrite Z_eq_2_pi by lra.
  reflexivity.
Qed.

Lemma X_11_pi_state_0 : state_0 ⟷ X 1 1 PI ∝= state_1.
Proof.
  colorswap_of Z_11_pi_state_plus.
Qed.

Lemma X_11_pi_state_1 : state_1 ⟷ X 1 1 PI ∝= state_0.
Proof.
  colorswap_of Z_11_pi_state_minus.
Qed.






Lemma box_state_0 : state_0 ⟷ □ ∝= state_plus.
Proof.
  prep_matrix_equivalence.
  simpl.
  rewrite state_0_semantics, state_plus_semantics.
  rewrite ket0_equiv.
  rewrite H0_spec.
  by_cell; lca.
Qed.

Lemma box_state_1 : state_1 ⟷ □ ∝= state_minus.
Proof.
  prep_matrix_equivalence.
  simpl.
  rewrite state_1_semantics, state_minus_semantics.
  rewrite ket1_equiv.
  rewrite H1_spec.
  by_cell; lca.
Qed.

Lemma box_state_plus : state_plus ⟷ □ ∝= state_0.
Proof.
  colorswap_of box_state_0.
Qed.

Lemma box_state_minus : state_minus ⟷ □ ∝= state_1.
Proof.
  colorswap_of box_state_1.
Qed.

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

(* FIXME: Move, and use to give general PI copy rule(s) *)
Lemma X_pi_copy_1_1_gen α : 
  X 1 1 PI ⟷ Z 1 1 α ∝= Cexp α .* Z 1 1 (-α) ⟷ X 1 1 PI.
Proof.
  apply prop_eq_by_eq_on_states_1_n; 
    rewrite <- 2 compose_assoc; distribute_zxscale.
  - rewrite X_11_pi_state_0, Z_11_state_0.
    now rewrite Z_11_state_1, X_11_pi_state_0.
  - rewrite X_11_pi_state_1, Z_11_state_1.
    distribute_zxscale.
    rewrite <- Cexp_add, Rplus_opp_r, Cexp_0, zx_scale_1_l.
    now rewrite Z_11_state_0, X_11_pi_state_1.
Qed.

Lemma Z_pi_copy_1_1_gen α : 
  Z 1 1 PI ⟷ X 1 1 α ∝= Cexp α .* X 1 1 (-α) ⟷ Z 1 1 PI.
Proof.
  colorswap_of (X_pi_copy_1_1_gen α).
Qed.

(* FIXME: get proper name and move *)
Lemma Z_pi_copy_1_1_gen_r α : 
  X 0 1 α ⟷ Z 1 1 PI ∝= Cexp α .* X 0 1 (-α).
Proof.
  prep_matrix_equivalence.
  rewrite zx_scale_semantics.
  simpl.
  compute_matrix (X_semantics 0 1 α).
  compute_matrix (X_semantics 0 1 (-α)).
  rewrite kron_1_l by auto_wf.
  simpl.
  autorewrite with C_db.
  compute_matrix (Z_semantics 1 1 PI).
  rewrite Cexp_PI.
  rewrite 3 make_WF_equiv.
  by_cell; autounfold with U_db; cbn; C_field;
  rewrite <- 2? Copp_mult_distr_l, <- Cexp_add, Rplus_opp_r, Cexp_0; lca.
Qed.

Lemma X_pi_copy_1_1_gen_r α : 
  Z 0 1 α ⟷ X 1 1 PI ∝= Cexp α .* Z 0 1 (-α).
Proof.
  colorswap_of (Z_pi_copy_1_1_gen_r α).
Qed.



Definition phasebox α : ZX 1 1 := 
  (Z 0 1 (-α/2) ↕ Z 1 1 (α/2)) ⟷ X 2 1 0 ⟷ Z 1 1 (α/2).

Lemma phasebox_state_0 α : state_0 ⟷ phasebox α ∝= state_plus.
Proof.
  unfold phasebox.
  rewrite <- (stack_empty_l state_0).
  rewrite <- 2 compose_assoc, 
    <- (stack_compose_distr ⦰ (Z 0 1 _) state_0 (Z 1 1 _)).
  rewrite compose_empty_l.
  rewrite Z_11_state_0.
  rewrite push_out_bot, cast_id.
  rewrite (compose_assoc (Z 0 1 _)).
  rewrite state_0_defn.
  distribute_zxscale.
  rewrite zx_scale_compose_distr_l.
  simpl_rewrite (@dominated_X_spider_fusion_bot_right 0 0 1).
  distribute_zxscale.
  rewrite Rplus_0_l.
  rewrite X_is_wire.
  rewrite wire_removal_r.
  rewrite Z_spider_1_1_fusion.
  rewrite 2 Rdiv_unfold, <- Ropp_mult_distr_l, Rplus_opp_l.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma phasebox_state_1 α : state_1 ⟷ phasebox α ∝= /√2 .* Z 0 1 α.
Proof.
  unfold phasebox.
  rewrite <- (stack_empty_l state_1).
  rewrite <- 2 compose_assoc, 
    <- (stack_compose_distr ⦰ (Z 0 1 _) state_1 (Z 1 1 _)).
  rewrite compose_empty_l.
  rewrite Z_11_state_1.
  rewrite push_out_bot, cast_id.
  rewrite (compose_assoc (Z 0 1 _)).
  rewrite state_1_defn.
  distribute_zxscale.
  rewrite zx_scale_compose_distr_l.
  simpl_rewrite (@dominated_X_spider_fusion_bot_right 0 0 1).
  distribute_zxscale.
  rewrite Rplus_0_r.
  rewrite X_pi_copy_1_1_gen_r.
  distribute_zxscale.
  rewrite Z_spider_1_1_fusion.
  apply zx_scale_simplify_eq.
  - C_field.
    rewrite <- Cexp_0, <- Cexp_add; f_equal; lra.
  - apply Z_phase_simplify.
    f_equal.
    lra.
  Unshelve. all: reflexivity. 
Qed.

Lemma phasebox_semantics α : ⟦ phasebox α ⟧ = 
  (/√2 .* make_WF (list2D_to_matrix [[C1 ; C1]; [C1; Cexp α]]))%M.
Proof.
  prep_matrix_equivalence.
  rewrite semantics_by_states_1_n.
  rewrite phasebox_state_0, phasebox_state_1, zx_scale_semantics, state_plus_semantics.
  simpl.
  rewrite make_WF_equiv.
  unfold xbasis_plus;
  by_cell; autounfold with U_db; unfold list2D_to_matrix;
    cbn; lca.
Qed.


Lemma phasebox_state_plus_semantics α : 
  ⟦ state_plus ⟷ phasebox α ⟧ = (qubit0 .+ (1 + Cexp α) / 2 .* qubit1)%M.
Proof.
  prep_matrix_equivalence.
  rewrite zx_compose_spec.
  rewrite phasebox_semantics, state_plus_semantics.
  unfold xbasis_plus.
  rewrite make_WF_equiv.
  unfold list2D_to_matrix;
  by_cell; autounfold with U_db; cbn; Csimpl; group_radicals; lca.
Qed.

Lemma phasebox_state_minus α : 
  state_minus ⟷ phasebox α ∝= (1 - Cexp α) / 2 .* state_1.
Proof.
  prep_matrix_equivalence.
  rewrite zx_compose_spec, zx_scale_semantics.
  rewrite phasebox_semantics, state_minus_semantics, state_1_semantics.
  unfold xbasis_minus.
  rewrite make_WF_equiv.
  unfold list2D_to_matrix;
  by_cell; autounfold with U_db; cbn; Csimpl; group_radicals; lca.
Qed.

Lemma phasebox_pi : phasebox PI ∝= □.
Proof.
  apply prop_eq_by_eq_on_states_1_n.
  - now rewrite phasebox_state_0, box_state_0.
  - rewrite phasebox_state_1, box_state_1.
    reflexivity.
Qed.

Lemma phasebox_alt_form α : phasebox α ∝= 
  Z 1 1 (α/2) ⟷ X 1 2 0 ⟷ (Z 1 0 (-α/2) ↕ Z 1 1 (α/2)).
Proof.
  rewrite pull_out_top, <- compose_assoc.
  unfold phasebox.
  apply compose_simplify_eq; [|reflexivity].
  rewrite push_out_top, 2 compose_assoc.
  apply compose_simplify_eq; [reflexivity|].
  rewrite X_wrap_over_top_left.
  rewrite <- compose_assoc.
  rewrite <- (stack_compose_distr (Z 0 1 _) — (n_wire 1) (X 1 2 _)).
  rewrite wire_removal_r, nwire_removal_l.
  rewrite push_out_top, compose_assoc.
  apply compose_simplify_eq; [reflexivity|].
  rewrite <- (n_wire_stack 1 1).
  rewrite <- wire_to_n_wire.
  rewrite (stack_assoc_back (Z 0 1 _) — — eq_refl eq_refl), cast_id.
  rewrite <- (stack_compose_distr (Z 0 1 _ ↕ —) ⊃ — —).
  apply stack_simplify_eq; [|now rewrite wire_removal_r].
  rewrite (Z_wrap_under_bot_right 0 0).
  rewrite stack_empty_l, cast_id.
  reflexivity.
  Unshelve. all:reflexivity.
Qed.

(* FIXME: Move *)
Lemma n_stack_semantics {n m} (zx : ZX n m) k : 
  ⟦ k ⇑ zx ⟧ = k ⨂ ⟦ zx ⟧.
Proof.
  induction k; [easy|].
  rewrite kron_n_assoc by auto_wf.
  simpl.
  rewrite IHk.
  f_equal; rewrite <- Nat.pow_mul_r; f_equal; lia.
Qed.

Lemma Z_1_S_state_0 n α : state_0 ⟷ Z 1 n α ∝= 
  cast _ _ (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_1_r _)) (n ⇑ state_0).
Proof.
  hnf.
  rewrite semantics_compose_state_0_l.
  simpl_cast_semantics.
  cbn [ZX_semantics].
  replace (get_col (Z_semantics 1 n α) 0) with (@e_i (2^ n) 0). 2:{
    prep_matrix_equivalence.
    by_cell.
    unfold e_i, get_col, Z_semantics.
    simpl.
    pose proof (Modulus.pow2_nonzero n).
    destruct i; simpl; [|now rewrite andb_false_r].
    Modulus.bdestructΩ'.
  }
  rewrite n_stack_semantics, state_0_semantics.
  induction n.
  - lma'. 
  - simpl.
    restore_dims.
    rewrite Nat.pow_1_l.
    simpl in IHn.
    rewrite <- IHn.
    rewrite qubit0_to_ei.
    rewrite ei_kron_join by lia.
    f_equal; lia.
Qed.

Lemma Z_1_S_state_1 n α : state_1 ⟷ Z 1 n α ∝= 
  Cexp α .* 
  cast _ _ (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_1_r _)) (n ⇑ state_1).
Proof.
  hnf.
  rewrite semantics_compose_state_1_l, zx_scale_semantics.
  simpl_cast_semantics.
  cbn [ZX_semantics].
  replace (get_col (Z_semantics 1 n α) 1) with 
    (Cexp α .* @e_i (2^n) (2^n - 1))%M. 2:{
    prep_matrix_equivalence.
    intros i j Hi Hj.
    replace j with O in * by lia; clear j Hj.
    unfold e_i, get_col, Z_semantics, scale.
    rewrite Nat.eqb_refl.
    pose proof (Modulus.pow2_nonzero n).
    bdestruct (i =? 2 ^ n - 1); simpl in *;
    [|destruct i; lca].
    subst.
    Modulus.bdestructΩ';
    lca.
  }
  rewrite n_stack_semantics, state_1_semantics.
  generalize n.
  intros k.
  induction k.
  - lma'. 
  - simpl.
    restore_dims.
    rewrite Nat.pow_1_l.
    simpl in IHk.
    rewrite <- Mscale_kron_dist_l.
    rewrite <- IHk.
    rewrite qubit1_to_ei.
    distribute_scale.
    rewrite ei_kron_join by lia.
    prep_matrix_equivalence.
    intros i j Hi Hj.
    unfold scale.
    f_equal.
    pose proof (Modulus.pow2_nonzero n).
    f_equal; lia.
Qed.


Lemma X_1_S_state_plus n α : state_plus ⟷ X 1 n α ∝= 
  cast _ _ (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_1_r _)) (n ⇑ state_plus).
Proof. 
  colorswap_of (Z_1_S_state_0 n α).
Qed.

Lemma X_1_S_state_minus n α : state_minus ⟷ X 1 n α ∝= 
  Cexp α .* 
  cast _ _ (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_1_r _)) (n ⇑ state_minus).
Proof.
  colorswap_of (Z_1_S_state_1 n α).
Qed.


Lemma Z_1_2_state_0 α : state_0 ⟷ Z 1 2 α ∝= state_0 ↕ state_0.
Proof.
  rewrite Z_1_S_state_0.
  simpl.
  rewrite stack_empty_r, 2 cast_id.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma Z_1_2_state_1 α : state_1 ⟷ Z 1 2 α ∝= Cexp α .* (state_1 ↕ state_1).
Proof.
  rewrite Z_1_S_state_1.
  simpl.
  rewrite stack_empty_r, 2 cast_id.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma X_1_2_state_plus α : state_plus ⟷ X 1 2 α ∝= state_plus ↕ state_plus.
Proof.
  colorswap_of (Z_1_2_state_0 α).
Qed.

Lemma X_1_2_state_1 α : state_minus ⟷ X 1 2 α ∝= 
  Cexp α .* (state_minus ↕ state_minus).
Proof.
  colorswap_of (Z_1_2_state_1 α).
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


Definition c_Z_gate α : ZX 2 2 := 
  √2 .* (Z 1 2 0 ↕ —) ⟷ (— ↕ phasebox α ↕ —) ⟷ (— ↕ Z 2 1 0).

Lemma Z_2_1_0_state_plus_top : state_plus ↕ — ⟷ Z 2 1 0 ∝= /√2 .* —.
Proof.
  rewrite state_plus_defn.
  distribute_zxscale.
  rewrite wire_to_n_wire.
  rewrite (dominated_Z_spider_fusion_top_right 0 0 1).
  rewrite Rplus_0_r, Z_is_wire.
  rewrite wire_to_n_wire.
  reflexivity.
Qed.

Lemma c_Z_gate_is_controlled_phase α : 
  is_controlled (Z 1 1 α) (c_Z_gate α).
Proof.
  split.
  - unfold c_Z_gate.
    distribute_zxscale.
    rewrite <- 2 compose_assoc, <- stack_compose_distr.
    rewrite nwire_removal_l.
    rewrite Z_1_S_state_0, cast_id.
    cbn [n_stack].
    rewrite stack_empty_r, cast_id.
    rewrite <- stack_compose_distr, wire_removal_r.
    rewrite <- (stack_compose_distr state_0 — state_0 (phasebox α)).
    rewrite wire_removal_r.
    rewrite phasebox_state_0.
    rewrite (stack_assoc state_0 state_plus —), cast_id.
    rewrite <- (stack_compose_distr state_0 — (state_plus ↕ —) (Z 2 1 _)).
    rewrite wire_removal_r.
    rewrite Z_2_1_0_state_plus_top.
    rewrite zx_scale_stack_distr_r, zx_scale_assoc.
    rewrite Cinv_r by C_field.
    now rewrite zx_scale_1_l, wire_to_n_wire.
  - unfold c_Z_gate.
    distribute_zxscale.
    rewrite <- 2 compose_assoc, <- stack_compose_distr.
    rewrite nwire_removal_l.
    rewrite Z_1_S_state_1, cast_id.
    distribute_zxscale.
    cbn [n_stack].
    rewrite stack_empty_r, cast_id.
    rewrite <- stack_compose_distr, wire_removal_r.
    rewrite <- (stack_compose_distr state_1 — state_1 (phasebox α)).
    rewrite wire_removal_r.
    rewrite phasebox_state_1.
    distribute_zxscale.
    rewrite zx_scale_stack_distr_l, zx_scale_compose_distr_l.
    rewrite (stack_assoc state_1 (Z 0 1 _) —), cast_id.
    rewrite <- (stack_compose_distr state_1 — (Z 0 1 _ ↕ —) (Z 2 1 _)).
    rewrite wire_removal_r.

    rewrite wire_to_n_wire.
    rewrite (dominated_Z_spider_fusion_top_right 0 0 1).
    rewrite Rplus_0_r.
    distribute_zxscale.
    rewrite Cexp_0, Cmult_1_r, Cinv_r, zx_scale_1_l by C_field.
    reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma c_Z_gate_to_cnot_Z_alt α : 
  c_Z_gate α ∝= 
  cnot ⟷ (— ↕ Z 1 1 (-(α/2))) ⟷ cnot ⟷ (Z 1 1 (α/2) ↕ Z 1 1 (α/2)).
Proof.
  pose proof cnot_is_controlled_not as [Hcnot0 Hcnot1].
  pose proof c_Z_gate_is_controlled_phase as [HCZ0 HCZ1].
  apply prop_eq_by_eq_on_states_step.
  - rewrite HCZ0.
    rewrite <- 3 compose_assoc.
    rewrite Hcnot0.
    change 2%nat with (1 + 1)%nat.
    rewrite <- stack_compose_distr.
    rewrite wire_removal_r, nwire_removal_l.
    rewrite (push_out_top state_0 (Z 1 1 _)).
    rewrite (compose_assoc _ _ cnot).
    rewrite Hcnot0.
    rewrite compose_assoc.
    rewrite <- (stack_compose_distr state_0 (Z 1 1 _) (n_wire 1) (Z 1 1 _)).
    rewrite Z_11_state_0.
    rewrite nwire_removal_l.
    rewrite (push_out_top _ (Z 1 1 _)).
    rewrite <- compose_assoc, Z_spider_1_1_fusion.
    rewrite Rplus_opp_l, Z_is_wire.
    now rewrite wire_removal_l.
  - rewrite HCZ1.
    rewrite <- 3 compose_assoc.
    rewrite Hcnot1.
    change 2%nat with (1 + 1)%nat.
    rewrite <- stack_compose_distr, wire_removal_r.
    rewrite (push_out_top state_1 (_ ⟷ _)).
    rewrite (compose_assoc _ _ cnot).
    rewrite Hcnot1, compose_assoc.
    rewrite <- (stack_compose_distr state_1 (Z 1 1 _) NOT (Z 1 1 _)).
    rewrite Z_11_state_1.
    distribute_zxscale.
    rewrite zx_scale_compose_distr_r.
    rewrite not_defn.
    rewrite 2 X_pi_copy_1_1_gen.
    distribute_zxscale.
    rewrite zx_scale_compose_distr_r, zx_scale_compose_distr_l, 2 zx_scale_assoc.
    rewrite Ropp_involutive.
    rewrite (push_out_top state_1 (_ ⟷ _)).
    rewrite <- 2 compose_assoc.
    rewrite (compose_assoc _ (X 1 1 PI) (Z 1 1 _)).
    rewrite X_pi_copy_1_1_gen.
    distribute_zxscale.
    rewrite Ropp_involutive, <- compose_assoc, 
      (compose_assoc _ (X 1 1 _) (X 1 1 _)).
    rewrite <- not_defn, not_not, wire_removal_r.
    rewrite Z_spider_1_1_fusion.
    rewrite <- zx_scale_1_l.
    apply zx_scale_simplify_eq.
    + rewrite <- 3 Cexp_add.
      rewrite <- Cexp_0.
      f_equal; lra.
    + rewrite push_out_top.
      replace (α / 2 + α / 2)%R with α by lra.
      reflexivity.
Qed.

Lemma c_Z_gate_to_cnot_Z α : 
  c_Z_gate α ∝= 
  (Z 1 1 (α/2) ↕ Z 1 1 (α/2)) ⟷ cnot ⟷ (— ↕ Z 1 1 (-(α/2))) ⟷ cnot.
Proof.
<<<<<<< Updated upstream
  pose proof cnot_is_controlled_notas [Hcnot0 Hcnot1].
=======
  pose proof cnot_is_controlled_not as [Hcnot0 Hcnot1].
>>>>>>> Stashed changes
  pose proof c_Z_gate_is_controlled_phase as [HCZ0 HCZ1].
  apply prop_eq_by_eq_on_states_step.
  - rewrite HCZ0.
    rewrite <- 3 compose_assoc.
    rewrite <- stack_compose_distr.
    rewrite Z_11_state_0, nwire_removal_l.
    rewrite (push_out_top state_0 (Z 1 1 _)).
    rewrite (compose_assoc (Z 1 1 _) _ cnot).
    rewrite Hcnot0.
    rewrite (compose_assoc (Z 1 1 _)).
    rewrite <- (stack_compose_distr state_0 — (n_wire 1) (Z 1 1 _)).
    rewrite wire_removal_r, nwire_removal_l.
    rewrite (push_out_top state_0 (Z 1 1 _)).
    rewrite <- compose_assoc, Z_spider_1_1_fusion.
    rewrite Rplus_opp_r, Z_is_wire, wire_removal_l.
    now rewrite Hcnot0.
  - rewrite HCZ1.
    rewrite <- 3 compose_assoc.
    rewrite <- stack_compose_distr.
    rewrite Z_11_state_1, nwire_removal_l.
    distribute_zxscale.
    rewrite (push_out_top state_1 (Z 1 1 (α/2))).
    rewrite (compose_assoc (Z 1 1 _) _ cnot).
    rewrite Hcnot1.
    rewrite (compose_assoc (Z 1 1 _)).
    rewrite <- (stack_compose_distr state_1 — NOT (Z 1 1 _)).
    rewrite wire_removal_r.
    rewrite (push_out_top state_1 (_ ⟷ Z 1 1 _)).
    rewrite <- compose_assoc.
    rewrite (compose_assoc _ _ cnot), Hcnot1.
    rewrite not_defn.
    rewrite X_pi_copy_1_1_gen.
    distribute_zxscale.
    rewrite zx_scale_compose_distr_l, zx_scale_assoc.
    rewrite <- Cexp_add, Rplus_opp_r, Cexp_0, zx_scale_1_l.
    rewrite Ropp_involutive.
    rewrite (push_out_top state_1 (X 1 1 _)).
    rewrite <- 2 compose_assoc.
    rewrite (compose_assoc _ (X 1 1 PI) (X 1 1 _)).
    rewrite <- not_defn, not_not, wire_removal_r.
    rewrite Z_spider_1_1_fusion.
    rewrite push_out_top.
    apply compose_simplify_eq; [|reflexivity].
    apply Z_phase_simplify.
    f_equal; lra.
Qed.


(* FIXME: Move *)
Lemma not_state_plus : state_plus ⟷ NOT ∝= state_plus.
Proof.
  rewrite not_defn.
  rewrite X_11_state_plus.
  reflexivity.
Qed.

Lemma not_state_minus : state_minus ⟷ NOT ∝= -1 .* state_minus.
Proof.
  rewrite not_defn.
  rewrite X_11_state_minus.
  rewrite Cexp_PI.
  reflexivity.
Qed.

Lemma not_box : NOT ⟷ Box ∝= Box ⟷ Z 1 1 PI.
Proof.
  apply prop_eq_by_eq_on_states_1_n; rewrite <- 2 compose_assoc.
  - rewrite not_state_0, box_state_1, box_state_0, Z_11_pi_state_plus.
    reflexivity.
  - rewrite not_state_1, box_state_1, box_state_0, Z_11_pi_state_minus.
    reflexivity.
Qed.

(* FIXME: Move *)
Lemma is_controlled_alt {n} (zx : ZX n n) czx : 
  is_controlled zx czx <-> 
  (forall (zx' : ZX n n), state_0 ↕ zx' ⟷ czx ∝= state_0 ↕ zx') /\
  (forall (zx' : ZX n n), state_1 ↕ zx' ⟷ czx ∝= state_1 ↕ (zx' ⟷ zx)).
Proof.
  split; intros [H0 H1]; split.
  - intros zx'.
    now rewrite push_out_top, compose_assoc, H0.
  - intros zx'.
    rewrite push_out_top, compose_assoc, H1.
    rewrite push_out_top, (push_out_top _ (_ ⟷ _)).
    now rewrite compose_assoc.
  - apply H0.
  - now rewrite H1, nwire_removal_l.
Qed.



Lemma cnot_cnot : cnot ⟷ cnot ∝= n_wire 2.
Proof.
<<<<<<< Updated upstream
  pose proof cnot_is_controlled_notas [H0 H1]%is_controlled_alt.
=======
  pose proof cnot_is_controlled_not as H01. 
  apply is_controlled_alt in H01 as [H0 H1].
>>>>>>> Stashed changes
  apply prop_eq_by_eq_on_states_step; rewrite <- compose_assoc.
  - now rewrite 2 H0, nwire_removal_r.
  - now rewrite 2 H1, nwire_removal_l, nwire_removal_r, 
      not_not, wire_to_n_wire.
Qed.


Definition c_cnot : ZX 3 3 :=
  c_Z_gate (PI/2) ↕ Box ⟷ 
  (— ↕ ⨉ ⟷ (c_Z_gate (PI/2) ↕ —) ⟷ (— ↕ ⨉)) ⟷
  (— ↕ cnot) ⟷
  (— ↕ ⨉ ⟷ (c_Z_gate (-(PI/2)) ↕ —) ⟷ (— ↕ ⨉)) ⟷
  (— ↕ cnot) ⟷ (n_wire 2 ↕ Box).

Require Import ZXpermFacts.

Lemma c_cnot_is_controlled_cnot : is_controlled cnot c_cnot.
Proof.
  pose proof (c_Z_gate_is_controlled_phase (PI/2)) 
    as Hcz.
  pose proof (c_Z_gate_is_controlled_phase (-(PI/2))) 
    as Hczn.
  pose proof (cnot_is_controlled_not) 
    as Hcnot.
  rewrite is_controlled_iff_bool in Hcz, Hczn, Hcnot.
  apply is_controlled_iff_bool.
  intros b.
  unfold c_cnot.
  assert (Hnwire2 : n_wire 2 ∝= n_wire 1 ↕ n_wire 1). 1: {
    now rewrite n_wire_stack.
  }
  rewrite 9 compose_assoc.
  rewrite <- (compose_assoc (state_b _ ↕ _)).
  etransitivity; [apply compose_simplify_eq; [|reflexivity]|].
  1: {
    rewrite Hnwire2.
    rewrite (stack_assoc_back (state_b b) 
      (n_wire 1) (n_wire 1) eq_refl eq_refl), cast_id.
    rewrite <- (stack_compose_distr (state_b b ↕ n_wire 1) (c_Z_gate _) 
      (n_wire 1) Box).
    rewrite Hcz, nwire_removal_l.
    reflexivity.
  }
  rewrite (stack_assoc (state_b b) _ _), cast_id.
  rewrite <- (compose_assoc (state_b b ↕ _) (— ↕ ⨉)).
  rewrite <- stack_compose_distr.
  rewrite wire_removal_r.
  rewrite <- (compose_assoc (state_b b ↕ _)).
  rewrite push_out_top, (compose_assoc _ (state_b b ↕ n_wire 2)).
  rewrite wire_to_n_wire.
  etransitivity; [apply compose_simplify_eq; [|reflexivity];
    apply compose_simplify_eq; [reflexivity|]|].
  1: {
    rewrite Hnwire2, <- wire_to_n_wire.
    rewrite (stack_assoc_back (state_b b) — —), cast_id.
    rewrite <- (stack_wire_distribute_r (state_b b ↕ —) (c_Z_gate _)).
    rewrite wire_to_n_wire, Hcz.
    rewrite (stack_assoc (state_b b) _ _), cast_id.
    reflexivity.
  }

  rewrite (compose_assoc _ 
    (state_b b ↕ ((if b then Z 1 1 _ else n_wire 1) ↕ n_wire 1))).
  rewrite <- (compose_assoc
    (state_b b ↕ ((if b then Z 1 1 _ else n_wire 1) ↕ n_wire 1))).
  rewrite <- stack_compose_distr.
  rewrite nwire_removal_r.
  rewrite push_out_top.
  rewrite (compose_assoc _ (state_b b ↕ n_wire 2)).
  rewrite <- 2 (@compose_assoc 2 2 2).
  
  rewrite <- (compose_assoc (state_b b ↕ n_wire 2)).
  rewrite <- stack_compose_distr, nwire_removal_r, nwire_removal_l, push_out_top.
  rewrite (compose_assoc cnot), <- (compose_assoc _ cnot).
  rewrite <- (@compose_assoc 2 3 3).
  rewrite <- (@stack_compose_distr 0 1 1 2 2 2), 
    nwire_removal_r, nwire_removal_l, push_out_top.
  rewrite (@compose_assoc 2 2 3 _ ⨉), <- (compose_assoc _ ⨉).
  rewrite <- (@compose_assoc 2 3 3).

  etransitivity; [apply compose_simplify_eq; [reflexivity|];
    apply compose_simplify_eq; [|reflexivity]|].
  1: {
    rewrite Hnwire2, <- wire_to_n_wire.
    rewrite (stack_assoc_back (state_b b) — —), cast_id.
    rewrite <- (stack_wire_distribute_r (state_b b ↕ —) (c_Z_gate _)).
    rewrite wire_to_n_wire, Hczn.
    rewrite (stack_assoc (state_b b) _ _), cast_id.
    reflexivity.
  }

  rewrite push_out_top.
  rewrite (@compose_assoc 2 2 3), <- (@compose_assoc 2 2 2).

  rewrite <- (@compose_assoc 2 3 3), <- (@stack_compose_distr 0 1 1 2 2 2), 
    nwire_removal_r, nwire_removal_l.
  rewrite <- (@compose_assoc 2 3 3), <- (@stack_compose_distr 0 1 1 2 2 2), 
    nwire_removal_r.
  rewrite push_out_top.
  rewrite (@compose_assoc 2 2 3), <- (@compose_assoc 2 2 2).
  etransitivity; [apply compose_simplify_eq; [reflexivity|]|]. 1:{
    rewrite Hnwire2.
    rewrite (@stack_assoc_back 0 1 1 1 1 1), cast_id.
    rewrite <- (@stack_compose_distr 1 2 2 1 1 1), nwire_removal_l.
    rewrite <- (@stack_compose_distr 0 1 1 1 1 1), nwire_removal_l, 
      nwire_removal_r.
    rewrite (@stack_assoc 0 1 1 1 1 1), cast_id.
    rewrite push_out_top.
    reflexivity.
  }
  rewrite <- 2 compose_assoc.
  rewrite (push_out_top (state_b b) (if b then _ else _)).
  apply compose_simplify_eq; [|reflexivity].
  destruct b.
  - rewrite 2 (compose_assoc (Z 1 1 _ ↕ Box)).
    rewrite (@swap_pullthrough_r 1 1), 
      zx_comm_1_1_swap, (compose_assoc _ ⨉ ⨉), swap_compose, nwire_removal_r.
    rewrite 2 (compose_assoc (_ ⟷ cnot)).
    rewrite (@swap_pullthrough_r 1 1), 
      zx_comm_1_1_swap, (compose_assoc _ ⨉ ⨉), swap_compose, nwire_removal_r.
    rewrite <- (@stack_compose_distr 1 1 1 1 1 1).
    rewrite nwire_removal_r.
    rewrite 5 compose_assoc.
<<<<<<< Updated upstream
    pose proof cnot_is_controlled_notas [HCN0 HCN1].
=======
    pose proof cnot_is_controlled_not as [HCN0 HCN1].
>>>>>>> Stashed changes
    apply prop_eq_by_eq_on_states_step.
    + rewrite <- 2 (@compose_assoc 1 2 2 2).
      rewrite <- (@stack_compose_distr 0 1 1 1 1 1).
      rewrite Z_11_state_0, nwire_removal_l, push_out_top.
      rewrite (@compose_assoc 1 1 2 2).
      rewrite 2 HCN0.
      rewrite (@compose_assoc 1 1 2 2), <- (@compose_assoc 1 2).
      rewrite <- (@stack_compose_distr 0 1 1 1 1 1), 
        nwire_removal_l, nwire_removal_r.
      rewrite push_out_top.
      rewrite (@compose_assoc 1 1 2 2), <- (@compose_assoc 1 2).
      rewrite HCN0.
      rewrite <- (@stack_compose_distr 0 1 1 1).
      rewrite nwire_removal_l, nwire_removal_r.
      rewrite push_out_top.
      rewrite <- 2 compose_assoc.
      rewrite (compose_assoc Box), Z_spider_1_1_fusion, Rplus_opp_r, Z_is_wire,
        wire_removal_r, box_compose, wire_removal_l.
      reflexivity.
    + rewrite <- 2 (@compose_assoc 1 2 2 2).
      rewrite <- (@stack_compose_distr 0 1 1 1 1 1).
      rewrite Z_11_state_1, nwire_removal_l, push_out_top.
      distribute_zxscale.
      rewrite zx_scale_compose_distr_r, 2 zx_scale_compose_distr_l.
      rewrite (@compose_assoc 1 1 2 2).
      rewrite 2 HCN1.
      rewrite push_out_top at 1; rewrite <- (compose_assoc _ NOT).
      rewrite (@compose_assoc 1 1 2 2), <- (@compose_assoc 1 2).
      rewrite <- (@stack_compose_distr 0 1 1 1 1 1), 
        nwire_removal_l, nwire_removal_r.
      rewrite push_out_top.
      rewrite (@compose_assoc 1 1 2 2), <- (@compose_assoc 1 2).
      rewrite HCN1.
      rewrite <- (@stack_compose_distr 0 1 1 1).
      rewrite nwire_removal_r.
      rewrite push_out_top.
      rewrite <- 2 compose_assoc.
      rewrite (compose_assoc _ NOT).
      rewrite not_defn.
      rewrite X_pi_copy_1_1_gen, Ropp_involutive.
      rewrite <- (compose_assoc _ _ (X 1 1 _)).
      rewrite (compose_assoc _ (X 1 1 _)), <- (compose_assoc (X 1 1 _)).
      rewrite <- not_defn, not_not, wire_removal_l.
      distribute_zxscale.
      rewrite <- Cexp_add, Rplus_opp_r, Cexp_0, zx_scale_1_l.
      rewrite (compose_assoc Box).
      rewrite Z_spider_1_1_fusion.
      rewrite (push_out_top _ NOT).
      replace (PI / 2 + PI/2)%R with PI by lra.
      rewrite not_defn, X_11_to_Z_11.
      reflexivity.
  - rewrite n_wire_stack, 2 nwire_removal_r. 
    rewrite (compose_assoc _ ⨉ ⨉), swap_compose, nwire_removal_r.
    rewrite (compose_assoc _ ⨉ ⨉), swap_compose, nwire_removal_r.
    rewrite (compose_assoc _ cnot cnot), cnot_cnot, nwire_removal_r.
    rewrite <- (@stack_nwire_distribute_l 1 1 1 1).
    rewrite box_compose, wire_to_n_wire.
    now rewrite n_wire_stack.
  Unshelve. all: reflexivity.
Qed.

Definition c_X_gate α : ZX 2 2 :=
  (— ↕ □) ⟷ c_Z_gate α ⟷ (— ↕ □).

Lemma c_X_gate_is_controlled_phase α : 
  is_controlled (X 1 1 α) (c_X_gate α).
Proof.
  pose proof (c_Z_gate_is_controlled_phase α) as [H0 H1]%is_controlled_alt.
  unfold c_X_gate.
  split; rewrite <- 2 compose_assoc.
  - rewrite <- stack_compose_distr, wire_removal_r, nwire_removal_l.
    rewrite H0.
    rewrite <- (@stack_compose_distr 0 1 1 1), box_compose, 
      wire_removal_r, wire_to_n_wire.
    reflexivity.
  - rewrite <- stack_compose_distr, wire_removal_r, nwire_removal_l.
    rewrite H1.
    rewrite <- (@stack_compose_distr 0 1 1 1).
    rewrite wire_removal_r, X_11_to_Z_11.
    reflexivity.
Qed.



Definition lambda_frac_box α : ZX 1 1 := 
  (X 0 1 0 ⟷ Z 1 0 0) ↕ 
  (((Z 0 2 (-α) ↕ Z 0 2 α ⟷ (▷ ↕ X 2 1 0 ↕ ▷))
     ↕ —) ⟷ Z 4 1 0).

Lemma zx_triangle_semantics_alt : ⟦ ▷ ⟧ = 
  make_WF (list2D_to_matrix [[C1;C0];[C1;C1]]).
Proof.
  rewrite zx_triangle_semantics.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  by_cell; autounfold with U_db; cbn; lca.
Qed.

Lemma Z_0_2_semantics α : 
  Z_semantics 0 2 α = make_WF (list2D_to_matrix [[C1];[C0];[C0];[Cexp α]]).
Proof.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  by_cell; reflexivity.
Qed.

Lemma X_2_1_0_semantics : X_semantics 2 1 0 = 
  make_WF (list2D_to_matrix [[/√2;C0;C0;/√2];[C0;/√2;/√2;C0]]).
Proof.
  rewrite X_semantics_equiv.
  cbn.
  rewrite 4 kron_1_l, Cexp_0, Mscale_1_l by auto_wf.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  unfold xbasis_plus, xbasis_minus, braplus, braminus;
    autounfold with U_db; cbn; by_cell_no_intros; cbn;
    Csimpl; group_radicals; C_field; lca.
Qed.

Lemma Z_4_1_0_semantics : Z_semantics 4 1 0 = make_WF
  (list2D_to_matrix
     [[C1;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0];
      [C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;
       C1]]).
Proof.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  by_cell; [reflexivity..|].
  rewrite Cexp_0.
  reflexivity.
Qed.

Lemma lambda_frac_box_semantics α : 
  ⟦ lambda_frac_box α ⟧ = make_WF (list2D_to_matrix [[C1;C0];[C0;2 * cos α]]).
Proof.
  prep_matrix_equivalence.
  cbn [ZX_semantics lambda_frac_box].
  replace (Z_semantics 1 0 0 × X_semantics 0 1 0) with 
    (√2 .* I 1)%M. 2: {
    prep_matrix_equivalence.
    by_cell; cbn.
    rewrite Cexp_0; Csimpl.
    rewrite kron_1_l by auto_wf; unfold hadamard.
    unfold scale, I.
    cbn.
    C_field.
    lca.
  }
  rewrite Mscale_kron_dist_l.
  rewrite kron_1_l by auto_wf.
  1: match goal with 
    |- context[ Z_semantics (1 + 1 + 1 + 1) _ _ × ?zx] =>
      replace zx with (/√2 .* make_WF (list2D_to_matrix [
        [C1;C0];
        [C0;C1];
        [C1;C0];
        [C0;C1];
        [C0;C0];
        [C0;C0];
        [Cexp α;C0];
        [C0;Cexp α];
        [C1;C0];
        [C0;C1];
        [C2;C0];
        [C0;C2];
        [Cexp (-α);C0];
        [C0;Cexp (-α)];
        [C2 * cos α;C0];
        [C0;C2 * cos α]
      ]))%M
    end. 
  2: {
    prep_matrix_equivalence.
    rewrite zx_triangle_semantics_alt.
    rewrite 2 Z_0_2_semantics.
    rewrite 5 make_WF_equiv at 1.
    rewrite X_2_1_0_semantics.
    rewrite make_WF_equiv.
    rewrite Kronecker.kron_I_r.
    by_cell; autounfold with U_db; unfold list2D_to_matrix; cbn; 
    Csimpl; match goal with | |- ?x = ?x => reflexivity | |- _ => idtac end.
    1,2:rewrite <- Cexp_add, Rplus_opp_l, Cexp_0; C_field; lca.
    1,2: C_field; now rewrite Cexp_minus.
  }
  rewrite Mscale_mult_dist_r, Mscale_assoc, Cinv_r, Mscale_1_l by C_field.
  change (1+1+1+1)%nat with 4%nat. 
  rewrite Z_4_1_0_semantics.
  rewrite 2 make_WF_equiv.
  by_cell; cbn; now Csimpl.
Qed.

Lemma lambda_frac_box_defn α : lambda_frac_box α = 
  (X 0 1 0 ⟷ Z 1 0 0) ↕ 
  (((Z 0 2 (-α) ↕ Z 0 2 α ⟷ (▷ ↕ X 2 1 0 ↕ ▷))
     ↕ —) ⟷ Z 4 1 0).
Proof.
  reflexivity.
Qed.

(* We certainly don't want this mess simplifying! *)
Global Opaque lambda_frac_box.

Lemma lambda_frac_box_state_0 α : state_0 ⟷ lambda_frac_box α ∝= state_0.
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite state_0_semantics, qubit0_to_ei, <- matrix_by_basis by lia.
  rewrite lambda_frac_box_semantics.
  by_cell; reflexivity.
Qed.

Lemma lambda_frac_box_state_1 α : state_1 ⟷ lambda_frac_box α ∝= 
  2 * cos α .* state_1.
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite zx_scale_semantics, state_1_semantics, 
  qubit1_to_ei, <- matrix_by_basis by lia.
  rewrite lambda_frac_box_semantics.
  by_cell; lca.
Qed.

Lemma triangle_state_0 : state_0 ⟷ ▷ ∝= Z 0 1 0.
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite state_0_semantics, zx_triangle_semantics_alt.
  rewrite make_WF_equiv.
  unfold Z_semantics; rewrite Cexp_0;
  by_cell; lca.
Qed.

Lemma triangle_state_1 : state_1 ⟷ ▷ ∝= state_1.
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite zx_triangle_semantics_alt, state_1_semantics.
  rewrite make_WF_equiv.
  by_cell; lca.
Qed.
(* 
Lemma triangle_state_plus : state_plus ⟷ ▷ ∝= [/√2; √2].
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite zx_scale_semantics, zx_triangle_semantics_alt, 
    state_plus_semantics(* , state_0_semantics *).
  rewrite make_WF_equiv.
  unfold xbasis_plus;
  by_cell; 
  autounfold with U_db; cbn; Csimpl; C_field. lca.
Qed. *)


Lemma triangle_state_minus : state_minus ⟷ ▷ ∝= / √2 .* state_0.
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite zx_scale_semantics, zx_triangle_semantics_alt, 
    state_minus_semantics, state_0_semantics.
  rewrite make_WF_equiv.
  unfold xbasis_minus;
  by_cell; 
  autounfold with U_db; lca.
Qed.

(* FIXME: Move *)
Lemma is_controlled_iff_bool_alt {n} (zx : ZX n n) czx : 
  is_controlled zx czx <-> 
  forall b {m} (zx' : ZX m n), state_b b ↕ zx' ⟷ czx ∝= 
    state_b b ↕ (zx' ⟷ if b then zx else n_wire n).
Proof.
  rewrite is_controlled_iff_bool.
  apply forall_iff; intros b.
  split.
  - intros Heq m zx'.
    rewrite push_out_top, compose_assoc, Heq.
    rewrite push_out_top, (push_out_top _ (_ ⟷ _)), <- compose_assoc.
    reflexivity.
  - intros ->.
    now rewrite nwire_removal_l.
Qed.

Lemma hopf_Z_X_rule_base : Z 1 2 0 ⟷ X 2 1 0 ∝= /2 .* (Z 1 0 0 ⟷ X 0 1 0).
Proof.
  prep_matrix_equivalence.
  rewrite zx_scale_semantics.
  cbn.
  rewrite X_2_1_0_semantics.
  compute_matrix (Z_semantics 1 2 0).
  rewrite Cexp_0.
  compute_matrix (X_semantics 0 1 0).
  rewrite kron_1_l, Cexp_0, 2 Cmult_1_r by auto_wf.
  unfold hadamard.
  rewrite Cplus_opp_r.
  replace (C1 / √ 2 + C1 / √2) with (RtoC (√2)) by (C_field; lca).
  compute_matrix (Z_semantics 1 0 0).
  rewrite Cexp_0.
  rewrite 4 make_WF_equiv.
  by_cell; unfold list2D_to_matrix, scale; cbn; Csimpl; C_field.
Qed.


Lemma hopf_Z_X_rule_base_phase α β : Z 1 2 α ⟷ X 2 1 β ∝= 
  /2 .* (Z 1 0 α ⟷ X 0 1 β).
Proof.
  rewrite <- (Rplus_0_r α) at 1.
  rewrite <- Z_spider_1_1_fusion.
  rewrite <- (Rplus_0_l β) at 1.
  rewrite <- X_spider_1_1_fusion.
  rewrite compose_assoc, <- (compose_assoc (Z 1 2 0)).
  rewrite hopf_Z_X_rule_base.
  distribute_zxscale.
  rewrite compose_assoc.
  rewrite X_spider_1_1_fusion, <- compose_assoc, Z_spider_1_1_fusion.
  rewrite Rplus_0_r, Rplus_0_l.
  reflexivity.
Qed.


Lemma hopf_X_Z_rule_base : X 1 2 0 ⟷ Z 2 1 0 ∝= /2 .* (X 1 0 0 ⟷ Z 0 1 0).
Proof.
  colorswap_of (hopf_Z_X_rule_base).
Qed.


Lemma hopf_X_Z_rule_base_phase α β : X 1 2 α ⟷ Z 2 1 β ∝= 
  /2 .* (X 1 0 α ⟷ Z 0 1 β).
Proof.
  colorswap_of (hopf_Z_X_rule_base_phase α β).
Qed.

Lemma not_semantics : ⟦ NOT ⟧ = make_WF (list2D_to_matrix [[C0;C1];[C1;C0]]).
Proof.
  prep_matrix_equivalence.
  rewrite semantics_by_states_1_n.
  rewrite not_state_0, not_state_1.
  rewrite state_0_semantics, state_1_semantics.
  by_cell; reflexivity.
Qed.

Lemma zx_left_triangle_semantics_alt : ⟦ ◁ ⟧ = 
  make_WF (list2D_to_matrix [[C1;C1];[C0;C1]]).
Proof.
  change zx_triangle_left with (▷ ⊤).
  rewrite semantics_transpose_comm.
  rewrite zx_triangle_semantics_alt.
  prep_matrix_equivalence.
  by_cell; reflexivity.
Qed.

(* FIXME: Move to scalars *)
Lemma zx_of_const_to_scaled_empty c : 
  zx_of_const c ∝= c .* ⦰.
Proof.
  prep_matrix_equivalence.
  rewrite zx_of_const_semantics, zx_scale_semantics.
  reflexivity.
Qed.

Lemma lambda_frac_box_is_controlled_scalar α : 
  is_controlled (zx_of_const (2 * cos α)) (lambda_frac_box α).
Proof.
  split; rewrite stack_empty_r, cast_id.
  - now rewrite lambda_frac_box_state_0.
  - rewrite lambda_frac_box_state_1.
    rewrite zx_of_const_to_scaled_empty.
    distribute_zxscale.
    rewrite stack_empty_r, cast_id.
    reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma left_triangle_state_0 : state_0 ⟷ ◁ ∝= state_0.
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite state_0_semantics, zx_left_triangle_semantics_alt.
  rewrite make_WF_equiv.
  by_cell; lca.
Qed.


Lemma left_triangle_state_1 : state_1 ⟷ ◁ ∝= Z 0 1 0.
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite state_1_semantics, zx_left_triangle_semantics_alt.
  rewrite make_WF_equiv.
  unfold Z_semantics; rewrite Cexp_0;
  by_cell; lca.
Qed.

Lemma Z_2_1_0_state_0_top : state_0 ↕ n_wire 1 ⟷ Z 2 1 0 ∝=
  lambda_frac_box (PI/2).
Proof.
  prep_matrix_equivalence.
  cbn; rewrite state_0_semantics, lambda_frac_box_semantics.
<<<<<<< Updated upstream
  rewrite cos_pi2, Cmult_0_r.
=======
  rewrite cos_PI2, Cmult_0_r.
>>>>>>> Stashed changes
  rewrite id_kron, Kronecker.kron_I_r.
  unfold Z_semantics; rewrite Cexp_0;
  by_cell; lca.
Qed.


Lemma Z_2_1_0_state_1_top : state_1 ↕ n_wire 1 ⟷ Z 2 1 0 ∝=
  NOT ⟷ lambda_frac_box (PI/2) ⟷ NOT.
Proof.
  prep_matrix_equivalence.
  cbn; rewrite state_1_semantics, lambda_frac_box_semantics, not_semantics.
  rewrite 2 make_WF_equiv.
<<<<<<< Updated upstream
  rewrite cos_pi2, Cmult_0_r.
=======
  rewrite cos_PI2, Cmult_0_r.
>>>>>>> Stashed changes
  rewrite id_kron, Kronecker.kron_I_r.
  unfold Z_semantics; rewrite Cexp_0;
  by_cell; cbn; lca.
Qed.


Definition c_H_aux : ZX 2 2 :=
  (Z 1 2 0 ↕ Z 1 2 0) ⟷
  (— ↕ ((◁ ↕ □) ⟷ Z 2 1 0) ↕ —) ⟷
  (— ↕ X 2 1 0).

Definition c_H : ZX 2 2 :=
  (lambda_frac_box (acos (/ (2 * √ 2))) ↕ —)  ⟷
  c_H_aux ⟷
  cnot.

Lemma c_H_aux_state_0_top : state_0 ↕ — ⟷ c_H_aux ∝= /2 .* (state_0 ↕ —).
Proof.
  unfold c_H_aux.
  rewrite <- 2 compose_assoc.
  rewrite <- stack_compose_distr, Z_1_S_state_0, cast_id, wire_removal_l.
  cbn.
  rewrite stack_empty_r, cast_id.
  rewrite (@stack_assoc 0 0 1 1 1 2), cast_id,
    (@stack_assoc 1 2 1 1 1 1), cast_id.
  rewrite <- (@stack_compose_distr 0 1 1 1), wire_removal_r.
  rewrite (push_out_top state_0 (Z 1 2 0)).
  rewrite (compose_assoc (Z 1 2 0)), stack_wire_distribute_r,
     <- (compose_assoc (state_0 ↕ n_wire 2)).
  rewrite <- (n_wire_stack 1 1), (@stack_assoc_back 0 1 1 1 1 1), 
    cast_id, <- (@stack_compose_distr 1 2 2 1 1 1), 
    <- (@stack_compose_distr 0 1 1 1 1 1).
  rewrite 2 nwire_removal_l.
  rewrite left_triangle_state_0.
  rewrite <- (@stack_wire_distribute_r 1 2 1).
  rewrite (push_out_top state_0 Box), (compose_assoc Box).
  rewrite Z_2_1_0_state_0_top.
  rewrite <- (@stack_compose_distr 0 1 1 1 2 1).
  rewrite <- (@zx_scale_stack_distr_r 0 1 1 1).
  apply stack_simplify_eq; [now rewrite wire_removal_r|].
  prep_matrix_equivalence.
  rewrite zx_scale_semantics.
  cbn.
  unfold scale.
  rewrite X_2_1_0_semantics.
  rewrite lambda_frac_box_semantics.
<<<<<<< Updated upstream
  rewrite cos_pi2, Cmult_0_r.
=======
  rewrite cos_PI2, Cmult_0_r.
>>>>>>> Stashed changes
  rewrite 2 make_WF_equiv.
  rewrite Kronecker.kron_I_r.
  by_cell; cbn; Csimpl; [ | lca..| rewrite Cexp_0]; C_field.
  Unshelve. all: reflexivity.
Qed.


Lemma c_H_aux_state_1_top : state_1 ↕ — ⟷ c_H_aux ∝= 
  / √2 .* (state_1 ↕ ((* NOT ⟷ *) □ ⟷ NOT)).
Proof.
  unfold c_H_aux.
  rewrite <- 2 compose_assoc.
  rewrite <- stack_compose_distr, Z_1_S_state_1, cast_id, wire_removal_l.
  rewrite Cexp_0, zx_scale_1_l.
  cbn.
  rewrite stack_empty_r, cast_id.
  rewrite (@stack_assoc 0 0 1 1 1 2), cast_id,
    (@stack_assoc 1 2 1 1 1 1), cast_id.
  rewrite <- (@stack_compose_distr 0 1 1 1), wire_removal_r.
  rewrite (push_out_top state_1 (Z 1 2 0)).
  rewrite (compose_assoc (Z 1 2 0)), stack_wire_distribute_r,
     <- (compose_assoc (state_1 ↕ n_wire 2)).
  rewrite <- (n_wire_stack 1 1), (@stack_assoc_back 0 1 1 1 1 1), 
    cast_id, <- (@stack_compose_distr 1 2 2 1 1 1), 
    <- (@stack_compose_distr 0 1 1 1 1 1).
  rewrite 2 nwire_removal_l.
  rewrite left_triangle_state_1.
  rewrite <- (@stack_wire_distribute_r 1 2 1).
  rewrite (push_out_top _ Box), (compose_assoc Box).
  rewrite (@dominated_Z_spider_fusion_top_right 0 0 1).
  cbn [Nat.add].
  rewrite Rplus_0_l.
  rewrite Z_is_wire.
  rewrite wire_removal_r.
  rewrite <- (@stack_compose_distr 0 1 1 1 2 1).
  rewrite <- (@zx_scale_stack_distr_r 0 1 1 1).
  apply stack_simplify_eq; [now rewrite wire_removal_r|].
  prep_matrix_equivalence.
  rewrite zx_scale_semantics.
  cbn.
  rewrite X_2_1_0_semantics.
  rewrite not_semantics.
  rewrite 2 make_WF_equiv.
  by_cell; unfold kron, scale, hadamard; cbn; Csimpl; 
  rewrite 1?Cexp_0; C_field.
  Unshelve. all: reflexivity.
Qed.

Lemma c_H_aux_state_b_top b : state_b b ↕ n_wire 1 ⟷ c_H_aux ∝= 
  state_b b ↕ (if b then /√2 .* (□ ⟷ NOT) else /2 .* —).
Proof.
  rewrite <- wire_to_n_wire.
  destruct b; cbn.
  - rewrite c_H_aux_state_1_top.
    distribute_zxscale.
    reflexivity.
  - rewrite c_H_aux_state_0_top.
    distribute_zxscale.
    reflexivity.
Qed.

Lemma inv_sqrt8_bounds : -1 <= / (2 * √2) <= 1.
Proof.
  assert (0 < / (2 * √2)). 1:{
    pose proof Rlt_sqrt2_0.
    apply Rinv_0_lt_compat.
    lra.
  }
  split; [lra|].
  rewrite <- Rinv_1.
  apply Rinv_le_contravar; [lra|].
  enough (1 <= √2) by lra.
  apply sqrt_ge; lra.
Qed.

Lemma c_H_is_controlled_H : 
  is_controlled □ (2 .* c_H).
Proof.
  unfold c_H.
  rewrite is_controlled_iff_bool.
  intros b.
  pose proof (lambda_frac_box_is_controlled_scalar (acos (/(2*√2))))
    as Hlam.
<<<<<<< Updated upstream
  pose proof cnot_is_controlled_notas Hcnot.
=======
  pose proof cnot_is_controlled_not as Hcnot.
>>>>>>> Stashed changes
  rewrite is_controlled_iff_bool_alt in Hlam.
  rewrite is_controlled_iff_bool_alt in Hcnot.
  rewrite zx_scale_compose_distr_r.
  rewrite <- 2 compose_assoc.
  rewrite wire_to_n_wire.
  rewrite <- (stack_nwire_distribute_r).
  rewrite (stack_empty_r_back (state_b b) eq_refl eq_refl), cast_id at 1.
  rewrite (Hlam b O ⦰).
  rewrite compose_empty_l.
  rewrite (@stack_assoc 0 0 1 1 0 1 _ _ _ eq_refl eq_refl), cast_id.
  rewrite push_out_top.
  rewrite (compose_assoc _ _ c_H_aux).
  rewrite c_H_aux_state_b_top.
  rewrite compose_assoc.
  rewrite Hcnot.
  rewrite (push_out_top (state_b b)), 
    ((push_out_top (state_b b) (if b then _ else _))).
  rewrite <- 2 compose_assoc.
  rewrite <- zx_scale_compose_distr_l.
  apply compose_simplify_eq; [|reflexivity].
  destruct b.
  - rewrite zx_of_const_to_scaled_empty.
    distribute_zxscale.
    rewrite cos_acos by apply inv_sqrt8_bounds.
    rewrite stack_empty_l, nwire_removal_l.
    rewrite zx_scale_compose_distr_l.
    distribute_zxscale.
    rewrite compose_assoc, not_not, wire_removal_r.
    rewrite <- (zx_scale_1_l Box) at 2.
    apply zx_scale_simplify_eq_l.
    autorewrite with RtoC_db.
    C_field.
  - rewrite n_wire_stack, nwire_removal_l, nwire_removal_r.
    rewrite zx_scale_assoc, Cinv_r, zx_scale_1_l by C_field.
    now rewrite wire_to_n_wire.
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


Fixpoint n_compose {n} k (zx : ZX n n) : ZX n n :=
  match k with 
  | O => n_wire n
  | S k' => zx ⟷ (n_compose k' zx)
  end.

Lemma n_compose_add {n} k l (zx : ZX n n) : 
  n_compose (k + l) zx ∝= n_compose k zx ⟷ n_compose l zx.
Proof.
  induction k.
  - simpl.
    now rewrite nwire_removal_l.
  - simpl.
    now rewrite IHk, compose_assoc.
Qed.

Lemma n_compose_1 {n} (zx : ZX n n) : n_compose 1 zx ∝= zx.
Proof. apply nwire_removal_r. Qed.

Lemma n_compose_S_alt {n} k (zx : ZX n n) : 
  n_compose (S k) zx ∝= n_compose k zx ⟷ zx.
Proof.
  rewrite <- (n_compose_1 zx) at 3.
  rewrite <- n_compose_add.
  now rewrite Nat.add_comm.
Qed.

Lemma n_compose_semantics {n} k (zx : ZX n n) : 
  ⟦ n_compose k zx ⟧ = Mmult_n k ⟦ zx ⟧.
Proof.
  induction k; [apply n_wire_semantics|].
  rewrite n_compose_S_alt.
  simpl.
  rewrite IHk.
  reflexivity.
Qed.

Lemma n_compose_triangle_semantics k : 
  ⟦ n_compose k ▷ ⟧ = make_WF (list2D_to_matrix [[C1; C0];[RtoC (INR k); C1]]).
Proof.
  rewrite n_compose_semantics, zx_triangle_semantics_alt.
  induction k.
  - simpl.
    prep_matrix_equivalence.
    by_cell; reflexivity.
  - cbn [Mmult_n].
    rewrite IHk.
    prep_matrix_equivalence.
    rewrite 3 make_WF_equiv.
    rewrite S_INR.
    by_cell; lca.
Qed.


Lemma n_compose_left_triangle_semantics k : 
  ⟦ n_compose k ◁ ⟧ = make_WF (list2D_to_matrix [[C1; RtoC (INR k)];[C0; C1]]).
Proof.
  rewrite n_compose_semantics.
  change (◁) with (▷ ⊤).
  rewrite semantics_transpose_comm, <- Mmult_n_transpose by auto_wf.
  rewrite <- n_compose_semantics, n_compose_triangle_semantics.
  prep_matrix_equivalence.
  by_cell; reflexivity.
Qed.

Definition is_controlled_scalar c (zx : ZX 1 0) :=
  state_0 ⟷ zx ∝= ⦰ /\
  state_1 ⟷ zx ∝= c .* ⦰.

Lemma is_controlled_scalar_iff_bool c (zx : ZX 1 0) : 
  is_controlled_scalar c zx <-> forall b, 
    state_b b ⟷ zx ∝= (if b then c else C1) .* ⦰.
Proof.
  split.
  - intros [H0 H1] []; simpl.
    + now rewrite H1.
    + now rewrite H0, zx_scale_1_l.
  - intros Hb.
    split.
    + now rewrite (Hb false), zx_scale_1_l.
    + now rewrite (Hb true).
Qed.


Lemma controlled_scalar_is_controlled c (zx : ZX 1 0) : 
  is_controlled_scalar c zx -> is_controlled (c .* ⦰) (Z 1 2 0 ⟷ (— ↕ zx)).
Proof.
  intros [H0 H1].
  hnf.
  rewrite 2 stack_empty_r, 2 cast_id, <- 2 compose_assoc.
  rewrite Z_1_2_state_0, Z_1_2_state_1, Cexp_0, zx_scale_1_l.
  rewrite <- 2 (@stack_compose_distr 0 1 1 0 1), 2 wire_removal_r.
  rewrite H0, H1.
  distribute_zxscale.
  rewrite stack_empty_r, cast_id.
  easy.
  Unshelve. all: reflexivity.
Qed.

Lemma Z_11_state_b α b : state_b b ⟷ Z 1 1 α ∝= 
  (if b then Cexp α else C1) .* state_b b.
Proof.
  destruct b.
  - now rewrite Z_11_state_1.
  - now rewrite Z_11_state_0, zx_scale_1_l.
Qed.


Lemma Z_1_2_state_b α b : state_b b ⟷ Z 1 2 α ∝= 
  (if b then Cexp α else C1) .* (state_b b ↕ state_b b).
Proof.
  destruct b.
  - now rewrite Z_1_2_state_1.
  - now rewrite Z_1_2_state_0, zx_scale_1_l.
Qed.


Definition controlled_n k α : ZX 1 0 :=
  Z 1 1 α ⟷ n_compose k ◁ ⟷ Z 1 1 α 
    ⟷ (/√2 .* X 1 0 0).

Lemma controlled_n_is_controlled_scalar k α : 
  is_controlled_scalar (Cexp α * INR k) (controlled_n k α).
Proof.
  rewrite is_controlled_scalar_iff_bool.
  intros b.
  unfold controlled_n.
  rewrite <- 3 compose_assoc, Z_11_state_b.
  distribute_zxscale.
  destruct b; cbn.
  - prep_matrix_equivalence.
    rewrite 2 zx_scale_semantics.
    cbn.
    rewrite n_compose_left_triangle_semantics, state_1_semantics, qubit1_to_ei.
    rewrite <- matrix_by_basis by lia.
    by_cell; autounfold with U_db; cbn; Csimpl.
    rewrite kron_1_l by auto_wf.
    unfold hadamard.
    rewrite Cexp_0.
    C_field.
    lca.
  - prep_matrix_equivalence.
    rewrite 2 zx_scale_semantics.
    cbn.
    rewrite n_compose_left_triangle_semantics, state_0_semantics, qubit0_to_ei.
    rewrite <- matrix_by_basis by lia.
    by_cell; autounfold with U_db; cbn; Csimpl.
    rewrite kron_1_l by auto_wf.
    unfold hadamard.
    rewrite Cexp_0.
    C_field.
    lca.
Qed.

Lemma controlled_scalar_semantics c zx0 : 
  is_controlled_scalar c zx0 -> ⟦ zx0 ⟧ = make_WF (list2D_to_matrix [[C1;c]]).
Proof.
  intros [H0 H1].
  prep_matrix_equivalence.
  rewrite semantics_by_states_1_n.
  rewrite H0, H1.
  rewrite zx_scale_semantics.
  by_cell; cbn; lca.
Qed.

Definition cscalar_sum (zx0 zx1 : ZX 1 0) : ZX 1 0 :=
  Z 1 2 0 ⟷ (◁ ↕ —) ⟷ (cnot) ⟷ (zx0 ↕ zx1).

Lemma cscalar_sum_is_controlled_scalar c d zx0 zx1 : 
  is_controlled_scalar c zx0 -> is_controlled_scalar d zx1 -> 
  is_controlled_scalar (c + d) (cscalar_sum zx0 zx1).
Proof.
  intros H0 H1.
  pose proof H0 as H0'.
  pose proof H1 as H1'.
  rewrite is_controlled_scalar_iff_bool in H0, H1.
  rewrite is_controlled_scalar_iff_bool.
  intros b.
  unfold cscalar_sum.
  (* rewrite zx_scale_compose_distr_r. *)
  (* distribute_zxscale. *)
  (* rewrite zx_scale_compose_distr_r. *)
  rewrite <- 3 compose_assoc.
  rewrite Z_1_2_state_b.
  rewrite 2 zx_scale_compose_distr_l.
  distribute_zxscale.
  rewrite <- (@stack_compose_distr 0 1 1 0 1 1).
  rewrite wire_removal_r.
  prep_matrix_equivalence.
  rewrite Cexp_0, Tauto.if_same, zx_scale_1_l.
  rewrite zx_scale_semantics.
  simpl.
  simpl_rewrite (@controlled_pair_semantics 1 1 _ _ _ (cnot_is_controlled_not)).
  rewrite kron_1_r by auto_wf.
  by_cell.
  unfold scale; cbn; Csimpl.
  rewrite zx_left_triangle_semantics_alt.
  rewrite (controlled_scalar_semantics _ _ H0').
  rewrite (controlled_scalar_semantics _ _ H1').
  rewrite not_semantics.
  destruct b.
  - cbn [state_b].
    rewrite state_1_semantics.
    unfold kron, Mmult; cbn; lca.
  - cbn [state_b].
    rewrite state_0_semantics.
    unfold kron, Mmult; cbn; lca.
Qed.


Definition controlled_half : ZX 1 0 :=
  /2 .* (▷ ⟷ Z 1 0 0).

Lemma controlled_half_is_controlled_scalar : 
  is_controlled_scalar (/2) controlled_half.
Proof.
  split;
  unfold controlled_half; distribute_zxscale; rewrite <- compose_assoc.
  - rewrite triangle_state_0, Z_spider_1_1_fusion.
    prep_matrix_equivalence. 
    rewrite zx_scale_semantics, Z_0_0_semantics.
    rewrite Rplus_0_r, Cexp_0.
    by_cell; cbn; lca.
  - rewrite triangle_state_1.
    prep_matrix_equivalence.
    rewrite 2 zx_scale_semantics.
    simpl.
    rewrite state_1_semantics.
    unfold Z_semantics; rewrite Cexp_0;
    by_cell; lca. 
Qed.

Definition cscalar_prod (zx0 zx1 : ZX 1 0) : ZX 1 0 :=
  Z 1 2 0 ⟷ (zx0 ↕ zx1).

Lemma cscalar_prod_is_controlled_scalar c d zx0 zx1 : 
  is_controlled_scalar c zx0 -> is_controlled_scalar d zx1 ->
  is_controlled_scalar (c * d) (cscalar_prod zx0 zx1).
Proof.
  rewrite 3 is_controlled_scalar_iff_bool.
  intros H0 H1 b.
  unfold cscalar_prod.
  rewrite <- compose_assoc.
  rewrite Z_1_2_state_b, Cexp_0, Tauto.if_same, zx_scale_1_l.
  rewrite <- (@stack_compose_distr 0 1 0 0 1 0).
  rewrite H0, H1.
  distribute_zxscale.
  rewrite stack_empty_l.
  apply zx_scale_simplify_eq_l.
  destruct b; lca.
Qed.

Lemma is_controlled_scalar_by_exists c zx : 
  (exists d, is_controlled_scalar d zx /\ d = c) -> 
  is_controlled_scalar c zx.
Proof.
  now intros (? & ? & ->).
Qed.

Definition controlled_sqrt2 :=
  cscalar_sum (controlled_n 1 (PI/4)) (controlled_n 1 (-(PI/4))).

Lemma controlled_sqrt2_is_controlled : 
  is_controlled_scalar (√2) controlled_sqrt2.
Proof.
  apply is_controlled_scalar_by_exists.
  eexists; split.
  1: eapply cscalar_sum_is_controlled_scalar; 
  apply controlled_n_is_controlled_scalar.
  rewrite 2 Cmult_1_r.
  rewrite Cexp_minus.
<<<<<<< Updated upstream
  rewrite cos_pi4.
=======
  rewrite cos_PI4.
>>>>>>> Stashed changes
  rewrite Rdiv_unfold, Rmult_1_l.
  autorewrite with RtoC_db.
  C_field.
Qed.

Definition controlled_inv_sqrt2 :=
  cscalar_prod controlled_half controlled_sqrt2.

Lemma controlled_inv_sqrt2_is_controlled : 
  is_controlled_scalar (/√2) controlled_inv_sqrt2.
Proof.
  apply is_controlled_scalar_by_exists.
  eexists; split.
  - apply cscalar_prod_is_controlled_scalar.
    + apply controlled_half_is_controlled_scalar.
    + apply controlled_sqrt2_is_controlled.
  - C_field.
Qed.

Definition controlled_cexp r : ZX 1 0 :=
  controlled_n 1 r.

Lemma controlled_cexp_is_controlled r : 
  is_controlled_scalar (Cexp r) (controlled_cexp r).
Proof.
  apply is_controlled_scalar_by_exists.
  eexists; split.
  - apply controlled_n_is_controlled_scalar.
  - lca.
Qed.

Definition controlled_1 : ZX 1 0 := controlled_cexp 0.

Lemma controlled_1_is_controlled : 
  is_controlled_scalar C1 controlled_1.
Proof.
  rewrite <- Cexp_0.
  apply controlled_cexp_is_controlled.
Qed.

Fixpoint controlled_power k (zx : ZX 1 0) :=
  match k with 
  | 0 => controlled_1
  | S k' => cscalar_prod zx (controlled_power k' zx)
  end.

Lemma controlled_power_is_controlled k c zx : 
  is_controlled_scalar c zx -> 
  is_controlled_scalar (c ^ k) (controlled_power k zx).
Proof.
  intros Hzx.
  induction k.
  - simpl.
    apply controlled_1_is_controlled.
  - simpl.
    apply cscalar_prod_is_controlled_scalar; [apply Hzx|].
    apply IHk.
Qed.

Definition controlled_decomp (z : C) : ZX 1 0 :=
  cscalar_prod (cscalar_prod
    (controlled_power (fst (SoundnessC.prop_decomp z)) controlled_sqrt2)
    (cscalar_sum controlled_1 
      (controlled_cexp (fst (snd (SoundnessC.prop_decomp z))))))
    (controlled_cexp (snd (snd (SoundnessC.prop_decomp z)))).

Lemma controlled_decomp_is_controlled z : 
  is_controlled_scalar z (controlled_decomp z).
Proof.
  apply is_controlled_scalar_by_exists.
  eexists; split.
  - apply cscalar_prod_is_controlled_scalar; 
    [apply cscalar_prod_is_controlled_scalar | 
      apply controlled_cexp_is_controlled];
    [apply controlled_power_is_controlled, controlled_sqrt2_is_controlled | 
    apply cscalar_sum_is_controlled_scalar; 
    [apply controlled_1_is_controlled | apply controlled_cexp_is_controlled]].
  - now rewrite <- SoundnessC.prop_equation'.
Qed.

Lemma is_controlled_pair_iff_bool_alt {n m} (zx0 zx1 : ZX n m) czx : 
  is_controlled_pair zx0 zx1 czx <->
  forall b o (zx' : ZX o n), 
  state_b b ↕ zx' ⟷ czx ∝=
  state_b b ↕ (zx' ⟷ if b then zx1 else zx0).
Proof.
  rewrite is_controlled_pair_iff_bool.
  split; intros Hc.
  - intros b o zx'.
    rewrite push_out_top, compose_assoc.
    rewrite Hc.
    rewrite push_out_top, <- compose_assoc.
    rewrite (push_out_top _ (_ ⟷ _)).
    reflexivity.
  - intros b.
    now rewrite Hc, nwire_removal_l.
Qed.

Definition control_stack {n0 m0 n1 m1} 
  (czx0 : ZX (1 + n0) (1 + m0)) (czx1 : ZX (1 + n1) (1 + m1)) : 
  ZX (1 + (n0 + n1)) (1 + (m0 + m1)) :=
  cast (1 + (n0 + n1)) (1 + (m0 + n1)) eq_refl eq_refl (czx0 ↕ n_wire n1) ⟷
  cast _ _ eq_refl eq_refl (
    zx_comm 1 m0 ↕ n_wire n1 ⟷
    cast _ _ (eq_sym (Nat.add_assoc _ _ _)) (eq_sym (Nat.add_assoc _ _ _)) (
      n_wire m0 ↕ czx1
    ) ⟷
    (zx_comm m0 1 ↕ n_wire m1)).

Lemma control_stack_is_controlled_pair {n0 m0 n1 m1} 
  (zx00 zx01 : ZX n0 m0) (zx10 zx11 : ZX n1 m1) czx0 czx1 : 
  is_controlled_pair zx00 zx01 czx0 -> 
  is_controlled_pair zx10 zx11 czx1 -> 
  is_controlled_pair (zx00 ↕ zx10) (zx01 ↕ zx11) (control_stack czx0 czx1).
Proof.
  rewrite 2 is_controlled_pair_iff_bool_alt.
  intros Hc0 Hc1.
  rewrite is_controlled_pair_iff_bool.
  intros b.
  unfold control_stack.
  rewrite <- compose_assoc.
  rewrite <- n_wire_stack, stack_assoc_back.
  rewrite cast_compose_eq_mid_join.
  rewrite <- (@stack_nwire_distribute_r n0 (1 + n0) (1 + m0) n1).
  rewrite (Hc0 b n0), nwire_removal_l.
  rewrite cast_compose_eq_mid_join.
  rewrite <- 2 compose_assoc.
  rewrite <- stack_nwire_distribute_r, zx_comm_commutes_r.
  rewrite stack_nwire_distribute_r, (compose_assoc (zx_comm 0 n0 ↕ _)).
  rewrite stack_assoc, cast_compose_eq_mid_join.
  rewrite <- stack_compose_distr, Hc1, nwire_removal_r, nwire_removal_l.
  rewrite <- stack_assoc, compose_assoc.
  rewrite <- stack_compose_distr, nwire_removal_r.
  rewrite zx_comm_commutes_r.
  rewrite <- stack_compose_distr, <- compose_assoc, zx_comm_cancel, 
    2 nwire_removal_l.
  rewrite <- (@stack_assoc_back 0 n0 n1 1 m0 m1).
  now destruct b.
  Unshelve. all: reflexivity || lia.
Qed.


Lemma triangle_transpose : ▷ ⊤ = ◁.
Proof. reflexivity. Qed.

Lemma left_triangle_transpose : ◁ ⊤ = ▷.
Proof. apply (transpose_involutive_eq ▷). Qed.

#[export] Hint Rewrite triangle_transpose left_triangle_transpose : transpose_db.

Lemma X_1_0_state_0 α : state_0 ⟷ X 1 0 α ∝= (1 + Cexp α)/ √2 .* ⦰.
Proof.
  prep_matrix_equivalence.
  simpl.
  rewrite zx_scale_semantics.
  rewrite state_0_semantics, qubit0_to_ei, <- matrix_by_basis by lia.
  by_cell; cbn; unfold kron, hadamard, I, scale; cbn;
    C_field.
Qed.

Lemma X_1_0_state_1 α : state_1 ⟷ X 1 0 α ∝= (1 - Cexp α)/ √2 .* ⦰.
Proof.
  prep_matrix_equivalence.
  simpl.
  rewrite zx_scale_semantics.
  rewrite state_1_semantics, qubit1_to_ei, <- matrix_by_basis by lia.
  by_cell; cbn; unfold kron, hadamard, I, scale; cbn;
    C_field.
Qed.

Lemma X_1_0_0_state_0 : state_0 ⟷ X 1 0 0 ∝= √2 .* ⦰.
Proof.
  rewrite X_1_0_state_0.
  rewrite Cexp_0.
  apply zx_scale_simplify_eq_l; C_field; lca.
Qed.

Lemma X_1_0_0_state_1 : state_1 ⟷ X 1 0 0 ∝= 0 .* ⦰.
Proof.
  rewrite X_1_0_state_1.
  rewrite Cexp_0.
  apply zx_scale_simplify_eq_l; C_field; lca.
Qed.



Lemma Z_0_1_X_1_0 α β : Z 0 1 α ⟷ X 1 0 β ∝= 
  (1 + Cexp α + Cexp β - Cexp (α + β))/√2 .* ⦰.
Proof.
  prep_matrix_equivalence.
  rewrite zx_scale_semantics.
  by_cell; cbn; unfold kron, hadamard, I, scale; cbn; 
     C_field; rewrite Cexp_add; lca.
Qed.

Lemma Z_0_1_0_X_1_0_0 : Z 0 1 0 ⟷ X 1 0 0 ∝= √2 .* ⦰.
Proof.
  rewrite Z_0_1_X_1_0, Rplus_0_r, Cexp_0.
  apply zx_scale_simplify_eq_l.
  C_field; lca.
Qed.

Lemma X_0_1_0_triangle : X 0 1 0 ⟷ ▷ ∝= √2 .* Z 0 1 0.
Proof.
  apply transpose_diagrams_eq.
  rewrite zx_scale_transpose.
  simpl.
  rewrite triangle_transpose.
  apply prop_eq_by_eq_on_states_1_n; 
    rewrite <- compose_assoc; distribute_zxscale.
  - rewrite left_triangle_state_0, Z_1_S_state_0.
    simpl.
    rewrite cast_id.
    now rewrite X_1_0_0_state_0.
  - rewrite left_triangle_state_1, Z_1_S_state_1.
    simpl.
    rewrite cast_id.
    rewrite Z_0_1_0_X_1_0_0, Cexp_0, zx_scale_1_l.
    reflexivity.
Qed.

Lemma X_1_0_0_left_triangle : X 0 1 0 ⟷ ◁ ∝= X 0 1 0.
Proof.
  apply transpose_diagrams_eq.
  cbn; autorewrite with transpose_db.
  apply prop_eq_by_eq_on_states_1_n; 
    rewrite <- compose_assoc.
  - rewrite triangle_state_0.
    rewrite Z_0_1_0_X_1_0_0, X_1_0_0_state_0.
    reflexivity.
  - now rewrite triangle_state_1.
Qed.

Lemma X_0_1_pi_triangle : X 0 1 PI ⟷ ▷ ∝= X 0 1 PI.
Proof.
  apply transpose_diagrams_eq.
  simpl.
  rewrite triangle_transpose.
  apply prop_eq_by_eq_on_states_1_n; 
    rewrite <- compose_assoc.
  - now rewrite left_triangle_state_0.
  - rewrite left_triangle_state_1.
    rewrite X_1_0_state_1, Z_0_1_X_1_0.
    rewrite Rplus_0_l, Cexp_PI, Cexp_0.
    apply zx_scale_simplify_eq_l.
    f_equal; lca.
Qed.

Lemma X_1_0_pi_left_triangle : X 0 1 PI ⟷ ◁ ∝= √2 .* Z 0 1 0.
Proof.
  apply transpose_diagrams_eq.
  cbn; rewrite left_triangle_transpose, zx_scale_transpose; cbn.
  apply prop_eq_by_eq_on_states_1_n; 
    rewrite <- compose_assoc; distribute_zxscale.
  - rewrite triangle_state_0.
    rewrite Z_0_1_X_1_0.
    rewrite Z_1_S_state_0.
    simpl.
    rewrite cast_id.
    rewrite Rplus_0_l, Cexp_PI, Cexp_0.
    apply zx_scale_simplify_eq_l.
    C_field; lca.
  - rewrite triangle_state_1.
    rewrite X_1_0_state_1, Z_1_S_state_1, Cexp_PI, Cexp_0.
    distribute_zxscale.
    rewrite cast_id; simpl.
    apply zx_scale_simplify_eq_l; C_field; lca.
Qed.

Definition uniform_state n : ZX 0 n :=
  cast _ _ (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_1_r _))
    (n_stack n (Z 0 1 0)).

Lemma uniform_state_split n m : 
  uniform_state (n + m) ∝= uniform_state n ↕ uniform_state m.
Proof.
  unfold uniform_state.
  rewrite nstack_split, cast_contract.
  simpl_casts.
  reflexivity.
  Unshelve. all:lia.
Qed.

Definition is_controlled_state {n} (czx : ZX 1 n) :=
  state_0 ⟷ czx ∝= uniform_state n.

Definition proc_to_state {n m} (zx : ZX n m) : ZX 0 (n + m) :=
  n_cap n ⟷ (n_wire n ↕ zx).

Definition state_to_proc {n m} (zx : ZX 0 (n + m)) : ZX n m :=
  cast _ _ (eq_sym (Nat.add_0_r _)) 
    (eq_sym (Nat.add_assoc _ _ _)) 
    (n_wire n ↕ zx) ⟷ (n_cup n ↕ n_wire m).

Import Setoid. 

Add Parametric Morphism {n m} : (@proc_to_state n m) 
  with signature proportional_by_1 ==> proportional_by_1 as proc_to_state_mor.
Proof.
  unfold proc_to_state.
  now intros czx czx' ->.
Qed.

Add Parametric Morphism {n m} : (@state_to_proc n m) 
  with signature proportional_by_1 ==> proportional_by_1 as state_to_proc_mor.
Proof.
  unfold state_to_proc.
  now intros czx czx' ->.
Qed.

Lemma proc_to_state_to_proc {n m} (zx : ZX n m) : 
  state_to_proc (proc_to_state zx) ∝= zx.
Proof.
  unfold state_to_proc, proc_to_state.
  rewrite n_cap_pullthrough_bot.
  rewrite stack_nwire_distribute_l.
  rewrite cast_compose_distribute, compose_assoc.
  rewrite stack_assoc_back, cast_contract.

  rewrite (cast_compose_l _ _ _ (_ ↕ _)), cast_id. 
  rewrite <- stack_nwire_distribute_r.
  rewrite n_cup_pullthrough_bot, transpose_involutive_eq.
  rewrite stack_nwire_distribute_r.
  rewrite cast_compose_distribute, stack_assoc, cast_contract.
  rewrite <- compose_assoc.
  rewrite cast_compose_eq_mid_join.
  rewrite <- stack_compose_distr, nwire_removal_l.
  rewrite push_out_bot, cast_compose_distribute, cast_contract.
  rewrite compose_assoc, (cast_compose_l _ _ (_ ↕ _)), cast_contract.
  rewrite n_wire_stack, nwire_removal_r.
  rewrite big_yank_r.
  rewrite cast_compose_l.
  rewrite 2 cast_contract.
  rewrite 2 cast_id, nwire_removal_r.
  reflexivity.
  Unshelve. all: lia.
Qed.


Lemma state_to_proc_to_state {n m} (zx : ZX 0 (n + m)) : 
  proc_to_state (state_to_proc zx) ∝= zx.
Proof.
  unfold state_to_proc, proc_to_state.
  rewrite stack_nwire_distribute_l.
  rewrite cast_stack_r, stack_assoc_back, cast_contract.
  rewrite <- compose_assoc, n_wire_stack.
  rewrite cast_compose_r, push_out_bot, <- compose_assoc, 
    cast_compose_eq_mid_join, nwire_removal_r.
  rewrite <- (push_out_bot zx (n_cap n)).
  rewrite <- nwire_stack_compose_topleft, cast_compose_distribute, 
  compose_assoc.
  rewrite <- n_wire_stack, stack_assoc_back, cast_contract.
  rewrite cast_id.
  rewrite (cast_compose_l _ _ (_ ↕ n_wire m)), cast_id.
  rewrite (stack_assoc_back (n_wire n) (n_cup n) (n_wire m)), cast_contract.
  rewrite cast_stack_distribute, cast_id.
  rewrite <- stack_nwire_distribute_r, big_yank_l.
  rewrite stack_empty_l, n_wire_stack, nwire_removal_r.
  reflexivity.
  Unshelve. all: lia.
Qed.

Lemma zx_scale_proc_to_state {n m} (zx : ZX n m) c : 
  proc_to_state (c .* zx) ∝= c .* proc_to_state zx.
Proof.
  unfold proc_to_state; distribute_zxscale.
  reflexivity.
Qed.

Lemma zx_scale_state_to_proc {n m} (zx : ZX 0 (n + m)) c : 
  state_to_proc (c .* zx) ∝= c .* state_to_proc zx.
Proof.
  unfold state_to_proc.
  rewrite zx_scale_stack_distr_r, zx_scale_cast.
  distribute_zxscale.
  reflexivity.
Qed.

#[export] Hint Rewrite 
  @zx_scale_proc_to_state @zx_scale_state_to_proc : zxscale_db.

Lemma colorswap_proc_to_state {n m} (zx : ZX n m) : 
  ⊙ (proc_to_state zx) ∝= proc_to_state (⊙ zx).
Proof.
  unfold proc_to_state; cbn [color_swap]; 
  autorewrite with colorswap_db.
  reflexivity.
Qed.

Lemma colorswap_state_to_proc {n m} (zx : ZX 0 (n + m)) : 
  ⊙ (state_to_proc zx) ∝= state_to_proc (⊙ zx).
Proof.
  unfold state_to_proc; cbn [color_swap]; 
  autorewrite with colorswap_db.
  cbn [color_swap].
  autorewrite with colorswap_db.
  reflexivity.
Qed.

#[export] Hint Rewrite 
  @colorswap_proc_to_state @colorswap_state_to_proc : colorswap_db.

Definition is_controlized {n m} (zx : ZX n m) (czx : ZX 1 (n + m)) :=
  is_controlled_state czx /\
  zx ∝= (/√2)^ (n + m) .* 
    state_to_proc (state_1 ⟷ czx).

Add Parametric Morphism {n} : (@is_controlled_state n) with signature
  proportional_by_1 ==> iff as is_controlled_state_mor.
Proof.
  unfold is_controlled_state.
  now intros ? ? ->.
Qed.


Add Parametric Morphism {n m} : (@is_controlized n m) with signature
  proportional_by_1 ==> proportional_by_1 ==> iff as is_controlized_mor.
Proof.
  unfold is_controlized.
  intros ? ? Hrw ? ? ->.
  now rewrite Hrw.
Qed.

(* FIXME: Move!!!! *)

Section StrongInductionT.

  Local Open Scope nat_scope.
  Variable P : nat -> Type.

  (** The stronger inductive hypothesis given in strong induction. The standard
  [nat ] induction principle provides only n = pred m, with [P 0] required
  separately. *)
(* @nocheck name *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

(* @nocheck name *)
  Lemma P0 : P 0.
  Proof.
    apply IH; intros.
    exfalso; inversion H.
  Qed.

  Hint Resolve P0 : strong_ind_db.

  Lemma pred_increasing : forall n m,
      n <= m ->
      Nat.pred n <= Nat.pred m.
  Proof.
    induction n; cbn; intros.
    - apply Nat.le_0_l.
    - induction H; subst; cbn; eauto.
      destruct m; eauto.
  Qed.

  Hint Resolve le_S_n : strong_ind_db.

  (** * Strengthen the induction hypothesis. *)

  (* @nocheck name *)
  Local Lemma strong_induction_all_T : forall n,
      (forall m, m <= n -> P m).
  Proof.
    induction n.
    - intros m Hm.
      replace m with 0 by (now inversion Hm).
      apply P0.
    - intros m Hm.
      bdestruct (m =? S n).
      + subst.
        apply IH.
        intros; apply IHn; lia.
      + apply IHn; lia.
  Qed.

  (* @nocheck name *)
  Theorem strong_induction_T : forall n, P n.
  Proof.
    eauto using strong_induction_all_T.
  Qed.

End StrongInductionT.

Lemma Z_0_1_copy β : Z 0 1 0 ⟷ X 1 1 β ∝= Z 0 1 0.
Proof.
  prep_matrix_equivalence.
  by_cell; cbn; unfold kron, hadamard; cbn; 
    rewrite Cexp_0; C_field; lca.
Qed.

Lemma X_0_1_copy β : X 0 1 0 ⟷ Z 1 1 β ∝= X 0 1 0.
Proof.
  colorswap_of (Z_0_1_copy β).
Qed.

Lemma Z_0_0_to_scalar β : Z 0 0 β ∝= (1 + Cexp β) .* ⦰.
Proof.
  prep_matrix_equivalence; rewrite zx_scale_semantics; 
  by_cell; lca.
Qed.

Lemma X_0_0_to_scalar β : X 0 0 β ∝= (1 + Cexp β) .* ⦰.
Proof. colorswap_of (Z_0_0_to_scalar β). Qed.

Lemma proc_to_state_Z n m α : proc_to_state (Z n m α) ∝=
  Z 0 (n + m) α.
Proof.
  unfold proc_to_state.
  now rewrite <- Z_n_wrap_over_l_base.
Qed.

Lemma state_to_proc_Z n m α : state_to_proc (Z 0 (n + m) α) ∝=
  Z n m α.
Proof.
  now rewrite <- proc_to_state_Z, proc_to_state_to_proc.
Qed.

Local Opaque proc_to_state state_to_proc.
Lemma proc_to_state_X n m α : proc_to_state (X n m α) ∝=
  X 0 (n + m) α.
Proof. colorswap_of (proc_to_state_Z n m α). Qed.
Lemma state_to_proc_X n m α : state_to_proc (X 0 (n + m) α) ∝=
  X n m α.
Proof. colorswap_of (state_to_proc_Z n m α). Qed.
Local Transparent proc_to_state state_to_proc.


Definition X_1_0_controlizer β : ZX 1 (1 + 0) := 
  (Z 1 2 0 ⟷ ((◁ ⟷ Z 1 0 0) ↕ (NOT ⟷ ◁ ⟷ X 1 1 β))).

Lemma X_1_0_is_controlized β : 
  is_controlized (X 1 0 β) 
    (X_1_0_controlizer β).
Proof.
  unfold X_1_0_controlizer.
  split.
  - unfold is_controlled_state.
    rewrite <- compose_assoc, Z_1_2_state_0.
    rewrite <- (@stack_compose_distr 0 1 0 0 1 1).
    rewrite <- 3 compose_assoc.
    rewrite left_triangle_state_0, Z_1_S_state_0.
    simpl; rewrite cast_id, stack_empty_l.
    rewrite not_state_0.
    rewrite left_triangle_state_1.
    unfold uniform_state.
    cbn.
    rewrite stack_empty_r, 2 cast_id.
    now rewrite Z_0_1_copy.
  - rewrite <- compose_assoc, Z_1_2_state_1.
    rewrite Cexp_0, zx_scale_1_l.
    rewrite <- (@stack_compose_distr 0 1 0 0 1 1).
    rewrite <- 3 compose_assoc.
    rewrite left_triangle_state_1, Z_spider_1_1_fusion, Rplus_0_r.
    rewrite Z_0_0_to_scalar, Cexp_0.
    rewrite not_state_1, left_triangle_state_0.
    rewrite state_0_defn.
    distribute_zxscale.
    simpl.
    rewrite zx_scale_state_to_proc.
    rewrite stack_empty_l, X_spider_1_1_fusion, Rplus_0_l.
    rewrite state_to_proc_X.
    distribute_zxscale.
    rewrite <- zx_scale_1_l at 1.
    apply zx_scale_simplify_eq_l.
    C_field; lca.
  Unshelve. all: reflexivity.
Qed.

Definition X_1_2_controlizer : ZX 1 (1 + 2) :=
  (Z 1 2 0 ⟷ ((◁ ⟷ Z 1 0 0 ⟷ Z 0 0 0) ↕ (▷ ⟷ X 1 3 PI))).

Lemma X_1_2_is_controlized : 
  is_controlized (X 1 2 0) 
    X_1_2_controlizer.
Proof.
  unfold X_1_2_controlizer.
  split.
  - unfold is_controlled_state.
    rewrite <- compose_assoc, Z_1_2_state_0,
      <- (@stack_compose_distr 0 1 0 0 1 3).
    rewrite <- 3 compose_assoc.
    rewrite left_triangle_state_0, Z_1_S_state_0.
    unfold uniform_state; simpl.
    rewrite stack_empty_r, 3 cast_id, compose_empty_l.
    rewrite Z_0_0_to_scalar, Cexp_0.
    distribute_zxscale.
    rewrite stack_empty_l.
    rewrite triangle_state_0.
    (* TODO: use full copy, when we have it *)


    prep_matrix_equivalence.
    rewrite zx_scale_semantics.
    simpl.
    compute_matrix (Z_semantics 0 1 0).
    rewrite X_semantics_equiv.
    unfold X_dirac_semantics.
    unfold xbasis_minus, xbasis_plus, braminus, braplus;
    by_cell; autounfold with U_db; cbn; 
      rewrite 1?Cexp_0, 1?Cexp_PI; C_field; lca.
  - rewrite <- compose_assoc.
    rewrite Z_1_2_state_1, Cexp_0, zx_scale_1_l,
       <- (@stack_compose_distr 0 1 0 0 1 3), <- 3 compose_assoc.
    rewrite left_triangle_state_1, Z_spider_1_1_fusion, Rplus_0_r.
    rewrite Z_0_0_to_scalar, Cexp_0.
    distribute_zxscale.
    rewrite compose_empty_l, stack_empty_l.
    rewrite triangle_state_1.
    rewrite state_1_defn.
    simpl.
    distribute_zxscale.
    rewrite zx_scale_state_to_proc, X_spider_1_1_fusion, state_to_proc_X.
    distribute_zxscale.
    rewrite <- zx_scale_1_l at 1.
    rewrite (X_eq_2_pi _ _ (_ + _)) by lra.
    apply zx_scale_simplify_eq_l.
    C_field; lca.
  Unshelve. all: reflexivity.
Qed.

Lemma X_1_n_state_0 {n} α : state_0 ⟷ X 1 n α ∝= /√2 .* X 0 n α.
Proof.
  rewrite state_0_defn.
  distribute_zxscale.
  now rewrite X_spider_1_1_fusion, Rplus_0_l.
Qed.

Lemma X_1_n_state_1 {n} α : state_1 ⟷ X 1 n α ∝= 
  /√2 .* X 0 n (PI + α).
Proof.
  rewrite state_1_defn.
  distribute_zxscale.
  now rewrite X_spider_1_1_fusion.
Qed.

Lemma Z_1_n_state_plus {n} α : state_plus ⟷ Z 1 n α ∝= /√2 .* Z 0 n α.
Proof.
  colorswap_of (@X_1_n_state_0 n α).
Qed.

Lemma Z_1_n_state_minus {n} α : state_minus ⟷ Z 1 n α ∝= /√2 .* Z 0 n (PI + α).
Proof.
  colorswap_of (@X_1_n_state_1 n α).
Qed.

(* FIXME: Move to Scalars.v *)
Definition const_of_zx (zx : ZX 0 0) : C :=
  ⟦ zx ⟧ O O.
Lemma gadget_is_scaled_empty (zx : ZX 0 0) : 
  zx ∝= const_of_zx zx .* ⦰.
Proof.
  prep_matrix_equivalence.
  rewrite zx_scale_semantics.
  by_cell; symmetry; apply Cmult_1_r.
Qed.
Lemma const_of_empty : const_of_zx ⦰ = 1.
Proof. reflexivity. Qed.
Lemma const_of_scale zx c : const_of_zx (c .* zx) = c * const_of_zx zx.
Proof.
  unfold const_of_zx.
  now rewrite zx_scale_semantics.
Qed.

Add Parametric Morphism : const_of_zx 
  with signature proportional_by_1 ==> eq as const_of_zx_mor.
Proof.
  intros zx zx' Hzx.
  unfold const_of_zx.
  now rewrite Hzx.
Qed.

(* FIXME: Move to CapCupRules.v *)
(* FIXME: Swap for n_cup/n_cap swap *)
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

Lemma const_of_zx_X_0_2_Z_1_0_Z_1_0_gen α β γ : 
  const_of_zx (X 0 2 α ⟷ (Z 1 0 β ↕ Z 1 0 γ)) = 
  /2 * (Cexp (α + β + γ) - Cexp (α + β) - Cexp (α + γ)
    + Cexp (β + γ) + Cexp α + Cexp β + Cexp γ + 1).
Proof.
  rewrite 4 Cexp_add.
  cbn; autounfold with U_db; cbn; 
  C_field.
Qed.

Lemma n_stack_compose {n m o} k (zx0 : ZX n m) (zx1 : ZX m o) : 
  k ⇑ (zx0 ⟷ zx1) ∝= k ⇑ zx0 ⟷ k ⇑ zx1.
Proof.
  induction k.
  - simpl; now rewrite compose_empty_l.
  - simpl.
    rewrite IHk, <- stack_compose_distr.
    reflexivity.
Qed.

Lemma const_of_zx_stack (zx0 zx1 : ZX 0 0) : 
  const_of_zx (zx0 ↕ zx1) = const_of_zx zx0 * const_of_zx zx1.
Proof.
  reflexivity.
Qed.

Lemma const_of_zx_compose (zx0 zx1 : ZX 0 0) : 
  const_of_zx (zx0 ⟷ zx1) = const_of_zx zx0 * const_of_zx zx1.
Proof.
  unfold const_of_zx; cbn; lca.
Qed.

Lemma const_of_zx_n_stack (zx : ZX 0 0) k prf0 prf1 : 
  const_of_zx (cast _ _ prf0 prf1 (n_stack k zx)) = 
  const_of_zx zx ^ k.
Proof.
  induction k.
  - rewrite cast_id; reflexivity.
  - simpl.
    change O with (0+0)%nat.
    erewrite (@cast_stack_distribute _ 0 _ 0 _ 0 _ 0 _ _ _ _ _ _ zx (k ⇑ zx)).
    rewrite const_of_zx_stack, cast_id, IHk.
    reflexivity.
  Unshelve. all: lia.
Qed.


Lemma uniform_state_scalar n : 
  const_of_zx (uniform_state n ⟷ (uniform_state n) ⊤) = 2 ^ n.
Proof.
  unfold uniform_state.
  rewrite cast_transpose, nstack_transpose; cbn [ZXCore.transpose].
  rewrite cast_compose_eq_mid_join.
  rewrite <- n_stack_compose.
  rewrite const_of_zx_n_stack, Z_spider_1_1_fusion, Rplus_0_l.
  rewrite Z_0_0_to_scalar, Cexp_0.
  unfold const_of_zx.
  f_equal.
  rewrite zx_scale_semantics.
  cbn; lca.
Qed.

(* @nocheck name *)
Lemma Cpow_1_l k : C1 ^ k = C1.
Proof.
  induction k; [|simpl; rewrite IHk]; lca.
Qed.

Lemma is_controlized_iff_alt {n m} (zx : ZX n m) (czx : ZX 1 (n + m)) : 
  is_controlized zx czx <->
  (is_controlled_state czx /\
  state_1 ⟷ czx ∝= (√ 2) ^ (n + m) .* proc_to_state zx).
Proof.
  apply Modulus.and_iff_distr_l.
  intros _.
  split.
  - intros ->.
    distribute_zxscale.
    rewrite state_to_proc_to_state.
    rewrite <- Cpow_mul_l, Cinv_r, Cpow_1_l by nonzero.
    now rewrite zx_scale_1_l.
  - intros ->.
    distribute_zxscale.
    rewrite proc_to_state_to_proc.
    rewrite <- Cpow_mul_l, Cinv_l, Cpow_1_l by nonzero.
    now rewrite zx_scale_1_l.
Qed.

(* FIXME: Move to Scalars *)
Lemma zx_scale_eq_1_l {n m} c (zx : ZX n m) : c = C1 -> 
  c .* zx ∝= zx.
Proof.
  intros ->; apply zx_scale_1_l.
Qed.

Lemma comp_conlzr_prf1 {n m k} : (n + m + (m + k))%nat = (n + (m + m) + k)%nat.
Proof. lia. Qed.

Lemma comp_conlzr_prf2 {n k} : (n + k)%nat = (n + 0 + k)%nat.
Proof. lia. Qed.

Definition compose_controlizer {n m k} (czx0 : ZX 1 (n + m)) 
  (czx1 : ZX 1 (m + k)) : 
  ZX 1 (n + k) :=
  (/2) ^ m .*
  Z 1 2 0 ⟷ (czx0 ↕ czx1) ⟷
  cast _ _ comp_conlzr_prf1 comp_conlzr_prf2
    (n_wire n ↕ n_cup m ↕ n_wire k).


Lemma compose_is_controlized {n m k} (zx0 : ZX n m) (zx1 : ZX m k) 
  czx0 czx1 : is_controlized zx0 czx0 -> is_controlized zx1 czx1 -> 
  is_controlized (zx0 ⟷ zx1) (compose_controlizer czx0 czx1).
Proof.
  intros H0 H1.
  pose proof H0 as [H00 H01].
  pose proof H1 as [H10 H11].
  pose proof H0 as [_ H01']%is_controlized_iff_alt.
  pose proof H1 as [_ H11']%is_controlized_iff_alt.
  split.
  - unfold is_controlled_state in *.
    unfold compose_controlizer.
    distribute_zxscale.
    rewrite <- 2 compose_assoc.
    rewrite Z_1_2_state_0.
    rewrite <- (@stack_compose_distr 0 1 _ 0 1 _).
    rewrite H00, H10.
    rewrite 2 uniform_state_split.
    rewrite (@stack_assoc 0 0 0), (@stack_assoc_back 0 0 0 m).
    simpl_casts.
    rewrite stack_assoc_back, cast_contract.
    rewrite cast_compose_eq_mid_join.
    rewrite <- 2 stack_compose_distr.
    rewrite 2 nwire_removal_r.
    rewrite <- (@nwire_stack_compose_topleft 0 0 m m), compose_assoc.
    rewrite n_cup_pullthrough_top, n_cup_0_empty, compose_empty_r.
    rewrite 2 stack_empty_l.
    rewrite gadget_is_scaled_empty, uniform_state_scalar.
    rewrite zx_scale_stack_distr_r, zx_scale_stack_distr_l.
    rewrite zx_scale_cast, zx_scale_assoc.
    rewrite stack_empty_r.
    simpl_casts.
    rewrite <- (zx_scale_1_l (uniform_state (n + k))).
    apply zx_scale_simplify_eq; [|now rewrite uniform_state_split].
    rewrite <- Cpow_mul_l, Cinv_l by nonzero.
    now rewrite Cpow_1_l.
  - 
    unfold compose_controlizer.
    distribute_zxscale.
    rewrite <- 2 compose_assoc.
    rewrite Z_1_2_state_1, Cexp_0, zx_scale_1_l.
    rewrite <- (@stack_compose_distr 0 1 _ 0 1 _).
    rewrite H01', H11'.
    distribute_zxscale.
    rewrite zx_scale_compose_distr_l.
    distribute_zxscale.
    rewrite zx_scale_eq_1_l. 2:{
      rewrite 3 Cpow_add_r.
      C_field_simplify.
      rewrite <- (Cmult_assoc _ (_^m) (_^m)).
      rewrite <- Cpow_mul_l, Csqrt2_sqrt.
      rewrite <- (Cmult_assoc _ (_^m) (_^m)).
      rewrite <- Cpow_mul_l, Cinv_l, Cpow_1_l, Cmult_1_r by nonzero.
      rewrite <- (Cmult_assoc _ (_^k) (_^k)).
      rewrite <- Cpow_mul_l, Cinv_l, Cpow_1_l, Cmult_1_r by nonzero.
      rewrite <- Cpow_mul_l, Cinv_l, Cpow_1_l by nonzero.
      reflexivity.
    }
    unfold state_to_proc, proc_to_state at 1.
    rewrite <- (nwire_stack_compose_topleft (proc_to_state zx1)).
    rewrite n_cap_pullthrough_bot.
    rewrite stack_nwire_distribute_r.
    rewrite 2 compose_assoc.
    rewrite <- n_wire_stack, (@stack_assoc_back (m + m)),
      (stack_assoc (zx0⊤)).
    simpl_casts.
    rewrite cast_compose_eq_mid_join.
    rewrite <- stack_nwire_distribute_r.
    rewrite 2 n_wire_stack, nwire_stack_compose_botleft.
    rewrite <- (nwire_stack_compose_topleft _ (zx0 ⊤)).
    rewrite stack_nwire_distribute_r.
    rewrite <- compose_assoc.
    rewrite stack_empty_r, cast_stack_l.
    rewrite cast_compose_distribute, cast_contract.
    rewrite <- compose_assoc.
    rewrite stack_nwire_distribute_l, cast_compose_distribute.
    rewrite compose_assoc, cast_stack_r, cast_contract.
    rewrite stack_assoc_back, cast_contract.
    rewrite (cast_compose_l _ _ _ (n_cup n ↕ _)), cast_id.
    rewrite <- stack_nwire_distribute_r.
    rewrite <- n_cup_pullthrough_top.
    rewrite stack_nwire_distribute_r, cast_compose_distribute.
    rewrite <- compose_assoc.
    rewrite cast_compose_l, (stack_assoc zx0), 2 cast_contract.
    rewrite (cast_compose_r _ _ (n_wire n ↕ _)), cast_id.
    rewrite cast_contract.
    rewrite cast_stack_distribute, cast_id.
    rewrite <- stack_compose_distr, nwire_removal_l.
    rewrite push_out_bot, compose_assoc, cast_compose_distribute, cast_contract.
    rewrite stack_empty_l.
    rewrite <- n_wire_stack, stack_assoc_back.
    rewrite (cast_compose_l _ _ (_ ↕ _)), cast_contract.
    erewrite (cast_stack_distribute _ _ _ _ _ _ _ (n_wire k)), cast_id.
    rewrite <- stack_nwire_distribute_r.
    erewrite (change_cast (0 + (m + k)) (m + 0 + k) (m + k) (m + k)).
    erewrite (cast_stack_distribute _ _ _ _ _ _ _ (n_wire k)).
    rewrite (cast_compose_distribute _ m), 2 cast_id, cast_contract.
    rewrite (big_yank_l m).
    rewrite n_wire_stack, nwire_removal_r.
    rewrite (cast_compose_r _ _ (proc_to_state zx1)), cast_id, nwire_removal_r.
    rewrite cast_contract, cast_id.
    rewrite compose_assoc, cast_compose_l.
    change (0 + k)%nat with k.
    rewrite cast_compose_distribute, cast_id.
    apply compose_simplify_eq; [reflexivity|].
    rewrite cast_contract.
    rewrite <- (proc_to_state_to_proc zx1) at 1.
    unfold state_to_proc.
    rewrite cast_compose_distribute, cast_id, cast_contract.
    reflexivity.
  Unshelve. all: lia.
Qed.

(* FIXME: Move *)
Definition zx_assoc n m o : ZX (n + m + o) (n + (m + o)) :=
  cast _ _ eq_refl (Nat.add_assoc _ _ _) (n_wire _).

Lemma zx_assoc_nat_l {n m o n' m' o'} 
  (zx0 : ZX n n') (zx1 : ZX m m') (zx2 : ZX o o') : 
  zx_assoc n m o ⟷ (zx0 ↕ (zx1 ↕ zx2)) ∝=
  zx0 ↕ zx1 ↕ zx2 ⟷ zx_assoc n' m' o'.
Proof.
  rewrite stack_assoc_back.
  unfold zx_assoc.
  rewrite cast_compose_eq_mid_join, nwire_removal_l.
  rewrite cast_compose_r, cast_id, nwire_removal_r.
  reflexivity.
  Unshelve. all: lia.
Qed.

Lemma zx_assoc_nat_r {n m o n' m' o'} 
  (zx0 : ZX n n') (zx1 : ZX m m') (zx2 : ZX o o') : 
  zx0 ↕ zx1 ↕ zx2 ⟷ zx_assoc n' m' o' ∝= 
  zx_assoc n m o ⟷ (zx0 ↕ (zx1 ↕ zx2)).
Proof.
  now rewrite zx_assoc_nat_l.
Qed.


Definition zx_invassoc n m o : ZX (n + (m + o)) (n + m + o) :=
  cast _ _ (Nat.add_assoc _ _ _) eq_refl (n_wire _).

Lemma zx_invassoc_nat_l {n m o n' m' o'} 
  (zx0 : ZX n n') (zx1 : ZX m m') (zx2 : ZX o o') : 
  zx_invassoc n m o ⟷ (zx0 ↕ zx1 ↕ zx2) ∝=
  (zx0 ↕ (zx1 ↕ zx2)) ⟷ zx_invassoc n' m' o'.
Proof.
  rewrite stack_assoc_back.
  unfold zx_invassoc.
  rewrite cast_compose_eq_mid_join, nwire_removal_r.
  rewrite cast_compose_l, cast_id, nwire_removal_l.
  reflexivity.
  Unshelve. all: lia.
Qed.

Lemma zx_invassoc_nat_r {n m o n' m' o'} 
  (zx0 : ZX n n') (zx1 : ZX m m') (zx2 : ZX o o') : 
  (zx0 ↕ (zx1 ↕ zx2)) ⟷ zx_invassoc n' m' o' ∝=
  zx_invassoc n m o ⟷ (zx0 ↕ zx1 ↕ zx2) .
Proof.
  now rewrite zx_invassoc_nat_l.
Qed.

Lemma zx_invassoc_linv n m o : 
  zx_invassoc n m o ⟷ zx_assoc n m o ∝= n_wire _.
Proof.
  unfold zx_assoc, zx_invassoc.
  rewrite cast_compose_eq_mid_join, nwire_removal_r.
  rewrite cast_n_wire.
  reflexivity.
Qed.

Lemma zx_invassoc_rinv n m o : 
  zx_assoc n m o ⟷ zx_invassoc n m o ∝= n_wire _.
Proof.
  unfold zx_assoc, zx_invassoc.
  rewrite cast_compose_eq_mid_join, nwire_removal_r.
  rewrite cast_id.
  reflexivity.
Qed.

(* FIXME: Move to ZXpermFacts *)
Lemma zx_comm_0_0 : zx_comm 0 0 ∝= ⦰.
Proof.
  by_perm_eq.
Qed.

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

Lemma cast_to_compose_zx_assoc_l {n m o p} (zx : ZX (n + (m + o)) p) prf1 prf2 :
  cast (n + m + o) p prf1 prf2 zx ∝=
  zx_assoc n m o ⟷ zx.
Proof.
  unfold zx_assoc.
  rewrite cast_compose_l, cast_id, nwire_removal_l.
  cast_irrelevance.
Qed.

Lemma cast_to_compose_zx_invassoc_l {n m o p} (zx : ZX (n + m + o) p) prf1 prf2 :
  cast (n + (m + o)) p prf1 prf2 zx ∝=
  zx_invassoc n m o ⟷ zx.
Proof.
  unfold zx_invassoc.
  rewrite cast_compose_l, cast_id, nwire_removal_l.
  cast_irrelevance.
Qed.


Definition stack_controlizer {n m k l} (czx0 : ZX 1 (n + m)) 
  (czx1 : ZX 1 (k + l)) : 
  ZX 1 ((n + k) + (m + l)) :=
  Z 1 2 0 ⟷ (czx0 ↕ czx1) ⟷
  zx_invassoc (n + m) k l ⟷
  ((zx_assoc n m k 
    ⟷ (n_wire n ↕ zx_comm m k)
    ⟷ zx_invassoc n k m) ↕ n_wire l) ⟷
  zx_assoc (n + k) m l.

Lemma stack_is_controlized {n m k l} (zx0 : ZX n m) (zx1 : ZX k l) 
  czx0 czx1 : is_controlized zx0 czx0 -> is_controlized zx1 czx1 -> 
  is_controlized (zx0 ↕ zx1) (stack_controlizer czx0 czx1).
Proof.
  intros H0 H1.
  pose proof H0 as [H00 H01].
  pose proof H1 as [H10 H11].
  pose proof H0 as [_ H01']%is_controlized_iff_alt.
  pose proof H1 as [_ H11']%is_controlized_iff_alt.
  split.
  - unfold is_controlled_state in *.
    unfold stack_controlizer.
    rewrite <- 4 compose_assoc.
    rewrite Z_1_2_state_0, <- (@stack_compose_distr 0 1 _ 0 1 _).
    rewrite H00, H10.
    rewrite 5 uniform_state_split.
    rewrite (@zx_invassoc_nat_r 0 0 0).
    unfold zx_invassoc at 1; rewrite cast_id, nwire_removal_l.
    rewrite <- (@stack_compose_distr 0 _ _ 0), nwire_removal_r.
    rewrite <- 2 compose_assoc.
    rewrite (@zx_assoc_nat_r 0 0 0).
    unfold zx_assoc at 1; rewrite cast_id, nwire_removal_l.
    rewrite <- (@stack_compose_distr 0 _ _ 0).
    rewrite nwire_removal_r, (@zx_comm_commutes_r 0 _ 0).
    rewrite zx_comm_0_0, compose_empty_l.
    rewrite (@zx_invassoc_nat_r 0 0 0).
    unfold zx_invassoc at 1; rewrite cast_id, nwire_removal_l.
    rewrite (@zx_assoc_nat_r 0 0 0).
    unfold zx_assoc at 1; rewrite cast_id, nwire_removal_l.
    reflexivity.
  - unfold stack_controlizer.
    rewrite <- 4 compose_assoc.
    rewrite Z_1_2_state_1, (zx_scale_eq_1_l (Cexp 0)), 
      <- (@stack_compose_distr 0 1 _ 0 1 _) by (apply Cexp_0).
    rewrite H01', H11'.
    distribute_zxscale.
    rewrite zx_scale_compose_distr_l.
    distribute_zxscale.
    rewrite zx_scale_eq_1_l. 2: {
      rewrite <- Cpow_add_r.
      replace (k + l + (n + m))%nat with (n + k + (m + l))%nat by lia.
      rewrite <- Cpow_mul_l, Cinv_l, Cpow_1_l by nonzero; easy.
    }
    unfold proc_to_state.
    rewrite stack_compose_distr, (compose_assoc (n_cap n ↕ n_cap k)).
    rewrite zx_invassoc_nat_r.
    rewrite (compose_assoc _ (_ ⟷ _)), (compose_assoc _ (_↕_↕_)).
    rewrite <- stack_compose_distr, nwire_removal_r.
    rewrite <- 2 (compose_assoc (_↕_↕_)).
    rewrite zx_assoc_nat_r.
    rewrite (compose_assoc (zx_assoc _ _ _)).
    rewrite <- stack_nwire_distribute_l, zx_comm_commutes_r, 
      stack_nwire_distribute_l.
    rewrite 4 compose_assoc, zx_invassoc_nat_r.
    rewrite <- (nwire_removal_l zx1).
    rewrite <- 4 compose_assoc.
    rewrite stack_compose_distr, <- compose_assoc.

    rewrite compose_assoc, zx_assoc_nat_r, <- compose_assoc.
    unfold state_to_proc.
    rewrite stack_nwire_distribute_l, cast_compose_distribute.
    rewrite stack_assoc_back, cast_contract.
    rewrite compose_assoc.
    rewrite (cast_compose_l _ _ _ (n_cup _ ↕ n_wire _)).
    rewrite cast_id.
    rewrite 2 n_wire_stack.
    rewrite nwire_stack_compose_topleft, nwire_removal_l.
    rewrite <- (nwire_stack_compose_botleft _ (zx0 ↕ _)).
    rewrite cast_compose_distribute, cast_id, stack_empty_l.
    rewrite <- compose_assoc.
    rewrite <- nwire_removal_l  at 1.
    apply compose_simplify_eq; [symmetry|reflexivity].
    rewrite n_cup_plus_decomp.
    rewrite cast_to_compose_zx_invassoc_l.
    rewrite cast_compose_l, cast_id.

    unfold zx_assoc, zx_invassoc; simpl_casts.
    rewrite cast_compose_l, nwire_removal_l, cast_contract.
    rewrite cast_compose_l,  cast_contract.
    rewrite cast_compose_l, nwire_removal_l, cast_contract.
    rewrite cast_compose_l, nwire_removal_l, cast_contract.
    rewrite cast_compose_l, cast_contract.
    rewrite cast_compose_r, cast_contract.
    rewrite cast_compose_r, nwire_removal_r, cast_contract.
    rewrite cast_compose_r, nwire_removal_r, cast_contract.
    rewrite cast_compose_r, nwire_removal_r, cast_contract.
    rewrite cast_contract.
    rewrite cast_compose_r, nwire_removal_r, cast_contract.
    rewrite cast_compose_r, nwire_removal_r, cast_contract.
    rewrite cast_compose_l, 2 cast_contract.
    rewrite ! cast_compose_l, !cast_contract.
    rewrite ! cast_compose_r, !cast_contract.
    rewrite ! cast_stack_l, ! cast_contract.
    rewrite ! cast_stack_r, !cast_contract.
    rewrite ! cast_compose_l, nwire_removal_l, ! cast_contract.
    rewrite 2 cast_stack_l, 2 cast_id.
    rewrite cast_compose_distribute, stack_nwire_distribute_r.
    rewrite ! cast_compose_distribute.
    rewrite 2  cast_contract.
    rewrite cast_stack_l.
    rewrite <- compose_assoc.
    rewrite cast_compose_l.
    rewrite stack_nwire_distribute_l, compose_assoc.
    rewrite cast_stack_r, 2 cast_contract.
    rewrite <- n_wire_stack.
    rewrite 2 stack_assoc_back, cast_stack_l, 2 cast_contract.
    rewrite stack_assoc_back, cast_contract.
    rewrite (stack_assoc (n_wire n) (n_wire k) (n_wire n)), 2 cast_stack_l, cast_contract.
    rewrite (stack_assoc (_ ↕ _) (n_wire k) (n_wire n)), cast_stack_l, cast_contract.
    rewrite 2 cast_compose_eq_mid_join.
    rewrite <- 3 stack_compose_distr, 2 nwire_removal_l, 2 n_wire_stack, 
      nwire_removal_l, nwire_removal_r.
    
    apply equal_on_basis_states_implies_equal';
    [auto_wf.. |].
    intros f.
    simpl_cast_semantics.
    cbn -[n_cup n_cap].
    simpl_cast_semantics.
    cbn -[n_cup n_cap].

    rewrite 3 n_wire_semantics, 2 zx_comm_semantics.
    rewrite <- (kron_1_r _ _ (f_to_vec (n+k) f)).
    restore_dims.
    rewrite Mmult_1_l by auto_wf.
    rewrite Mmult_assoc.
    restore_dims.
    rewrite Mmult_assoc.
    restore_dims.
    rewrite kron_mixed_product, Mmult_1_r, Mmult_1_l by auto_wf.
    rewrite (kron_split_diag (f_to_vec _ _)) by auto_wf.
    etransitivity. 1: {
      apply (f_equal2 Mmult); [reflexivity|].
      etransitivity; [symmetry; restore_dims; unify_pows_two; apply Mmult_assoc|].
      restore_dims.
      apply (f_equal2 Mmult); [|reflexivity].
      rewrite 4 Nat.pow_add_r, <- 3 id_kron.
      rewrite f_to_vec_split'_eq.
      restore_dims.
      rewrite (kron_assoc (f_to_vec n f)) by auto_wf.
      rewrite <- (kron_assoc (f_to_vec k _)) by auto_wf.
      rewrite (kron_assoc _ (I (2^n)) (I (2^k))) by auto_wf.
      restore_dims.
      rewrite <- (kron_assoc (f_to_vec k _)) by auto_wf.
      rewrite <- (kron_assoc (f_to_vec n f)) by auto_wf.
      restore_dims. 
      rewrite kron_mixed_product' by (unify_pows_two; f_equal; lia).
      Msimpl.
      rewrite <- (kron_assoc (f_to_vec n f)) by auto_wf.
      restore_dims.
      rewrite kron_mixed_product' by (unify_pows_two; f_equal; lia).
      rewrite kron_mixed_product' by (unify_pows_two; f_equal; lia).
      rewrite id_kron.
      Msimpl.

      rewrite kron_comm_commutes_l by auto_wf.
      rewrite <- (Mmult_1_r _ _ (f_to_vec n f)) by auto_wf.
      rewrite <- kron_mixed_product.
      rewrite <- (Mmult_1_l _ _ (kron_comm (2^k) (2^n))) by auto_wf.
      rewrite <- kron_mixed_product.
      
      rewrite kron_id_dist_r by auto_wf.
      reflexivity.
    }
    restore_dims.
    unify_pows_two.
    rewrite <- 2 Mmult_assoc.
    restore_dims.
    rewrite <- kron_assoc by auto_wf.
    rewrite (Nat.pow_add_r 2 k n), <- id_kron.
    restore_dims.
    rewrite (kron_assoc _ (f_to_vec k _)) by auto_wf.
    restore_dims.
    rewrite <- (kron_assoc (f_to_vec k _)) by auto_wf.
    restore_dims. 

    rewrite (kron_assoc _ _ (I (2^k))) by auto_wf.
    rewrite (kron_assoc _ (I (2^n)) (I (2^k))) by auto_wf.
    restore_dims.
    rewrite <- (kron_assoc (_⊗_) (_⊗_) (_⊗_)) by auto_wf.
    restore_dims. 
    rewrite kron_mixed_product', Mmult_1_l by 
      solve [auto_wf | unify_pows_two; f_equal; lia].
    restore_dims.
    rewrite (kron_mixed_product' _ _ _ _ _ _ _ _ _ _ _ (⟦n_cup n⟧))
      by (unify_pows_two; lia).
    restore_dims.
    unify_pows_two.
    rewrite (n_cup_matrix_pullthrough_top n 0) by auto_wf.
    restore_dims.
    rewrite ! Nat.mul_1_l.
    rewrite (n_cup_matrix_pullthrough_top k 0) by auto_wf.
    rewrite n_cup_0_empty.
    cbn [ZX_semantics].
    Msimpl.
    rewrite kron_assoc by auto_wf.
    rewrite <- (kron_assoc _ (I _) (I _)) by auto_wf.
    restore_dims.
    rewrite <- (kron_assoc _ _ (I _)) by auto_wf.
    restore_dims.
    rewrite kron_mixed_product' by (unify_pows_two; lia).

    rewrite (kron_mixed_product' _ _ _ _ _ _ _ _ _ _ _ (_ ⊤)%M)
       by (unify_pows_two; lia).
    rewrite kron_comm_1_r, Mmult_1_r by auto_wf.
    restore_dims.
    rewrite Mmult_1_r by auto_wf.
    rewrite kron_comm_commutes_r by auto_wf.
    rewrite kron_comm_1_l.
    restore_dims.
    rewrite Mmult_1_l by auto_wf.
    rewrite 2 kron_assoc by auto_wf.
    restore_dims.
    rewrite <- (kron_assoc (_ ⊤%M)) by auto_wf.
    restore_dims.
    rewrite kron_mixed_product' by unify_pows_two.
    rewrite <- 2 n_cup_transpose, 2 semantics_transpose_comm.
    rewrite <- id_transpose_eq, <- kron_transpose.
    restore_dims.
    unify_pows_two.
    rewrite <- Mmult_transpose.
    restore_dims.
    unify_pows_two.
    rewrite (n_cup_matrix_pullthrough_top n 0) by auto_wf.
    rewrite n_cup_0_empty.
    Msimpl.
    rewrite transpose_involutive.
    rewrite <- id_transpose_eq, <- kron_transpose.
    restore_dims.
    unify_pows_two.
    rewrite <- Mmult_transpose.
    restore_dims.
    unify_pows_two.
    rewrite (n_cup_matrix_pullthrough_top k 0) by auto_wf.
    rewrite n_cup_0_empty.
    Msimpl.
    rewrite transpose_involutive.
    rewrite <- f_to_vec_split'_eq.
    reflexivity.
  Unshelve. all: lia.
Qed.

Lemma proc_to_state_state {n} (zx : ZX 0 n) : 
  proc_to_state zx ∝= zx.
Proof.
  unfold proc_to_state.
  rewrite n_cap_0_empty.
  cleanup_zx.
  reflexivity.
Qed.

Lemma is_controlled_state_cast {n m} (zx : ZX 1 n) prf (H : m = n) : 
  is_controlled_state (cast _ _ prf H zx) <->
  is_controlled_state zx.
Proof.
  subst n.
  rewrite cast_id.
  reflexivity.
Qed.

(* FIXME: Move *)
Lemma cast_backwards_eq :
  forall {n0 m0 n1 m1} prfn prfm prfn' prfm' (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  cast n1 m1 prfn prfm zx0 ∝= zx1 <->
  cast n0 m0 prfn' prfm' zx1 ∝= zx0.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma is_controlized_of_eq_proc_to_state {n m n' m'} 
  (zx : ZX n m) (zx' : ZX n' m') (Heq : (n + m = n' + m')%nat) czx czx': 
  proc_to_state zx ∝= cast _ _ eq_refl Heq (proc_to_state zx') ->
  czx ∝= cast _ _ eq_refl Heq czx' ->
  is_controlized zx czx -> is_controlized zx' czx'.
Proof.
  intros Hzx Hczx [H0 H1]%is_controlized_iff_alt.
  rewrite is_controlized_iff_alt.
  split.
  - rewrite Hczx in H0.
    rewrite is_controlled_state_cast in H0.
    apply H0.
  - symmetry in Hczx.
    rewrite cast_backwards_eq in Hczx.
    rewrite <- Hczx, cast_compose_r, cast_id.
    rewrite H1.
    symmetry in Hzx.
    rewrite cast_backwards_eq in Hzx.
    rewrite <- Hzx.
    rewrite zx_scale_cast.
    rewrite Heq at 1.
    reflexivity.
  Unshelve. all: lia.
Qed.

Lemma controlled_scalar_is_controlized_scaled_empty c czx : 
  is_controlled_scalar c czx -> 
  is_controlized (c .* ⦰) czx.
Proof.
  intros [H0 H1].
  split.
  - unfold is_controlled_state.
    rewrite H0.
    unfold uniform_state; cbn.
    now rewrite cast_id.
  - simpl.
    rewrite H1.
    rewrite zx_scale_state_to_proc.
    distribute_zxscale; rewrite Cmult_1_l.
    apply zx_scale_simplify_eq_r.
    unfold state_to_proc.
    rewrite cast_id, n_cup_0_empty.
    simpl.
    now rewrite stack_empty_l, compose_empty_l.
Qed.


Lemma controlled_decomp_is_controlized_scaled_empty c : 
  is_controlized (c .* ⦰) (controlled_decomp c).
Proof. 
  apply controlled_scalar_is_controlized_scaled_empty.
  apply controlled_decomp_is_controlled.
Qed.

Lemma X_0_2_pi_to_cup_not: X 0 2 PI ∝= ⊂ ⟷ (— ↕ NOT).
Proof.
  (* rewrite cup_pullthrough_bot_1. *)
  rewrite cap_X, not_defn.
  rewrite wire_to_n_wire.
  rewrite (@dominated_X_spider_fusion_bot_left 1 0 1).
  rewrite Rplus_0_r.
  reflexivity.
Qed.

(* @nocheck name *)
Lemma Mmult_not_l {n} (A : Matrix 2 n) : WF_Matrix A -> 
  ⟦ NOT ⟧ × A = make_WF (fun i j => get_row A (1 - i) O j).
Proof.
  intros HA.
  prep_matrix_equivalence.
  rewrite not_semantics, 2 make_WF_equiv.
  intros i j Hi Hj.
  destruct i; [|replace i with 0%nat in * by (simpl in Hi; lia)];
  cbn; lca.
Qed.

(* FIXME: Move *)
Lemma prop_eq_by_eq_on_state_b_1_n {n} (zx zx' : ZX 1 n) : 
  (forall b, state_b b ⟷ zx ∝= state_b b ⟷ zx') ->
  zx ∝= zx'.
Proof.
  intros Hb.
  apply prop_eq_by_eq_on_states_1_n.
  - apply (Hb false).
  - apply (Hb true).
Qed.

Lemma triangle_state_b b : state_b b ⟷ ▷ ∝= if b then state_1 else Z 0 1 0.
Proof.
  destruct b.
  - apply triangle_state_1.
  - apply triangle_state_0.
Qed.

Lemma left_triangle_state_b b : state_b b ⟷ ◁ ∝= if b then Z 0 1 0 else state_0.
Proof.
  destruct b.
  - apply left_triangle_state_1.
  - apply left_triangle_state_0.
Qed.

(* FIXME: Move *)
Lemma n_stack_1 {n m} (zx : ZX n m) : 1 ⇑ zx ∝= 
  cast _ _ (Nat.mul_1_l _) (Nat.mul_1_l _) zx.
Proof.
  simpl.
  rewrite stack_empty_r.
  reflexivity.
Qed.
Lemma n_stack_1' {n m} (zx : ZX n m) prfn prfm : cast _ _ prfn prfm (1 ⇑ zx) ∝= 
  zx.
Proof.
  now rewrite n_stack_1, cast_contract, cast_id.
  Unshelve. all: reflexivity.
Qed.

Lemma Z_1_2_triangle_cancel : Z 1 2 0 ⟷ (◁ ↕ ▷) ⟷ Z 2 1 0 ∝= —.
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  rewrite <- 2 compose_assoc.
  rewrite Z_1_2_state_b, Cexp_0, zx_scale_eq_1_l by (now destruct b).
  rewrite <- (@stack_compose_distr 0 1 1 0 1 1).
  rewrite triangle_state_b, left_triangle_state_b.
  rewrite wire_removal_r.
  destruct b.
  - rewrite stack_split_antidiag, compose_assoc, 
    dominated_Z_spider_fusion_top_right, stack_empty_l.
    rewrite Rplus_0_r.
    rewrite Z_is_wire, wire_removal_r.
    reflexivity.
  - rewrite stack_split_diag, compose_assoc, 
    dominated_Z_spider_fusion_bot_right, stack_empty_r, cast_id.
    rewrite Rplus_0_r.
    rewrite Z_is_wire, wire_removal_r.
    reflexivity.
  Unshelve. all: reflexivity.
Qed.
  

Definition box_controlizer : ZX 1 (1 + 1) :=
  (Z 1 2 0 ⟷ ((X 1 2 PI ⟷ (Z 1 0 (-(PI/4)) ↕ Z 1 0 (PI/4)) ⟷ 
    Z 0 0 0) ↕
    (X 1 2 PI ⟷ ((◁ ⟷ Z 1 2 0 ⟷ (— ↕ ◁)) ↕ —) ⟷ 
    (— ↕ (Z 2 1 0 ⟷ □))))).

Lemma box_is_controlized : 
  is_controlized □ 
    box_controlizer.
Proof.
  unfold box_controlizer.
  rewrite Z_0_0_to_scalar, Cexp_0.
  rewrite zx_scale_compose_distr_r.
  distribute_zxscale.
  rewrite zx_scale_compose_distr_r.
  replace (C1 + C1) with C2 by lca.
  split.
  - unfold is_controlled_state.
    rewrite zx_scale_compose_distr_r.
    rewrite <- compose_assoc.
    rewrite Z_1_2_state_0.
    simpl.
    rewrite <- (@stack_compose_distr 0 1 0 0 1 2).
    rewrite <- 3 compose_assoc.
    rewrite X_1_n_state_0. distribute_zxscale.
    rewrite compose_empty_r.
    rewrite gadget_is_scaled_empty, const_of_zx_X_0_2_Z_1_0_Z_1_0_gen.
    distribute_zxscale.
    rewrite zx_scale_assoc.
    rewrite stack_empty_l.
    group_radicals.
    rewrite Cmult_assoc.
    etransitivity; [apply zx_scale_simplify_eq_l|]. 1:{
      instantiate (1 := (2)).
      rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Cexp_0.
      rewrite 2 Cexp_add, Cexp_PI, Cexp_neg, Cexp_PI4.
      group_radicals.
      replace (RtoC (-1)) with (- C1) by lca.
      C_field; [lca|].
      split; [nonzero | split; [nonzero|]].
      intros H%(f_equal fst); simpl in H; lra.
    }
    unfold uniform_state; cbn.
    rewrite stack_empty_r, 2 cast_id.
    rewrite <- compose_assoc.
    rewrite X_1_n_state_0.
    distribute_zxscale.
    rewrite X_0_2_pi_to_cup_not.
    rewrite 2 (compose_assoc ⊂), <- (@stack_compose_distr 1 1 2 1 1 1).
    rewrite wire_removal_l, wire_removal_r.
    rewrite <- (compose_assoc ⊂).
    rewrite (@cup_pullthrough_top 2 1).
    rewrite 2 compose_assoc.
    rewrite <- (n_wire_stack 1 1), (@stack_assoc 1 1 _ 1 1), cast_id.
    rewrite <- (@stack_compose_distr 1 1 1 3 2 1).
    rewrite wire_removal_r.
    rewrite <- wire_to_n_wire.
    prep_matrix_equivalence.
    rewrite zx_scale_semantics.
    rewrite zx_compose_spec.
    rewrite (@zx_stack_spec 1 1 3 1).
    rewrite zx_compose_spec.
    rewrite (@zx_stack_spec 1 1 2 1).
    rewrite (zx_compose_spec _ _ _ _ NOT).
    rewrite semantics_transpose_comm.
    change (@Compose 1 1 2) with (@Compose 1 1 (1+1)).
    change (@Compose 1 2 2) with (@Compose 1 2 (1+1)).
    compute_matrix ((* @Mmult (2^1) (2^1) (2^2) 
      (make_WF (list2D_to_matrix [[C0; C1]; [C1; C0]])) *) 
      (@ZX_semantics 1 2 (◁ ⟷ (Z 1 2 0 ⟷ (— ↕ ◁))))).
    rewrite zx_left_triangle_semantics_alt;
    rewrite (kron_I_l_eq (make_WF _)) by auto_wf; cbn -[n_cap Nat.pow].
    Csimpl.
    rewrite Mmult_not_l by auto_wf.
    (* FIXME: Move *)
    Ltac simpl_mult := 
      lazymatch goal with 
      |- context [ ?A × ?B ] => 
        let PA := fresh "PA" in 
        set (PA := A);
        unfold Mmult at 1
      end.

    rewrite Cexp_0.
    compute_matrix (@Mmult (2^1) (2^1) (2^2) hadamard (Z_semantics 2 1 0)).
    rewrite Cexp_0; Csimpl.
    replace (@ZX_semantics 0 4 (n_cap 2)) with 
      (@make_WF 16 1 (fun i _ => if i mod 5 =? 0 then C1 else C0)).
    2: {
      (* apply mat_equiv_eq; [auto_wf | apply (WF_ZX 0 4) |]. *)
      prep_matrix_equivalence.
      rewrite make_WF_equiv.
      unfold n_cap.
      rewrite semantics_transpose_comm.
      unfold n_cup, n_cup_unswapped.
      rewrite 2 cast_id_eq.
      assert (Hrw : — ↕ ⦰ ↕ — ∝= n_wire 2) by by_perm_eq.
      rewrite zx_compose_spec, zx_stack_spec.
      rewrite n_swap_2_is_swap.
      rewrite n_wire_semantics.
      rewrite zx_compose_spec.
      rewrite (zx_stack_spec 3 1 1 1 _ —).
      rewrite (zx_stack_spec 1 1 2 0).
      cbn [Nat.add] in *.
      rewrite zx_compose_spec, Hrw.
      rewrite n_wire_semantics, Mmult_1_r by auto_wf.
      cbn.
      rewrite kron_I_r, kron_I_l_eq by 
        (apply show_WF_list2D_to_matrix; reflexivity).
      rewrite kron_I_r.
      by_cell; cbn -[INR]; lca.
    }
    rewrite 2 make_WF_equiv.
    rewrite (make_WF_equiv 16 1).
    simpl_mult.
    change (2^4)%nat with 16%nat.

    cbn [big_sum Nat.divmod Nat.modulo Nat.eqb snd Nat.sub].
    intros i j Hi Hj.
    unfold scale.
    rewrite 12 Cmult_0_r, 12 Cplus_0_r, 4 Cmult_1_r, Cplus_0_l.
    revert i j Hi Hj.
    by_cell_no_intros; subst PA; 
      unfold transpose, make_WF, kron; cbn; Csimpl;
    rewrite ?Cexp_0; C_field.
  - rewrite zx_scale_compose_distr_r.
    distribute_zxscale.
    rewrite <- compose_assoc, Z_1_2_state_1, Cexp_0, zx_scale_1_l.
    rewrite compose_empty_r.


    rewrite <- (@stack_compose_distr 0 1 0 0 1 2).
    rewrite <- 3 compose_assoc.
    rewrite X_1_n_state_1. distribute_zxscale.
    rewrite X_eq_2_pi by lra.
    rewrite <- cap_X.
    rewrite (@cup_pullthrough_top 0 0), n_cap_0_empty, 
      compose_empty_l, stack_empty_l.
    cbn [ZXCore.transpose].
    rewrite Z_spider_1_1_fusion.
    rewrite Z_0_0_to_scalar, Rplus_opp_l, Cexp_0.
    distribute_zxscale; rewrite stack_empty_l.

    rewrite (@zx_scale_state_to_proc 1 1).
    distribute_zxscale.
    (* rewrite cup_pullthrough_top. *)
    symmetry.
    rewrite zx_scale_eq_1_l by (simpl; C_field; lca).
    (* rewrite <- (proc_to_state_to_proc Box) at 2. *)
    (* apply state_to_proc_mor. *)
    (* unfold proc_to_state. *)
    (* rewrite n_cap_1_cap, <- wire_to_n_wire. *)
    rewrite (compose_assoc ◁), stack_wire_distribute_r, <- compose_assoc.
    rewrite cup_pullthrough_top_1, wire_removal_r, left_triangle_transpose.
    rewrite (compose_assoc ⊂), <- (@stack_compose_distr 1 1 2 1 1 1).
    rewrite wire_removal_l, wire_removal_r.
    rewrite <- (wire_removal_l ▷).
    rewrite stack_compose_distr, <- compose_assoc.
    rewrite <- n_cap_1_cap, wire_to_n_wire.
    rewrite <- (Z_n_wrap_under_l_base 1 2).
    rewrite compose_assoc, (@stack_assoc 1 1 1 1), cast_id,
      <- (@stack_nwire_distribute_l 2 2 1 1).
    unfold state_to_proc.
    rewrite cast_id, n_cup_1_cup.
    rewrite (@stack_nwire_distribute_l 0 3 _ 1).
    rewrite compose_assoc, (@stack_assoc_back 1 1 2 1 1 1), 
      cast_id, n_wire_stack.
    rewrite <- (@stack_split_antidiag 2 0 2 1).
    rewrite (pull_out_top ⊃), <- 2 compose_assoc.
    rewrite <- wire_to_n_wire.
    rewrite <- (Z_wrap_over_top_left 0 2).
    rewrite <- 2 compose_assoc, Z_1_2_triangle_cancel, wire_removal_l.
    reflexivity.
  Unshelve. all: reflexivity.
Qed.

(* FIXME: Move *)
Lemma symmetry_iff {A} {R : relation A} `{Symmetric A R} (x y : A) : 
  R x y <-> R y x.
Proof.
  split; apply symmetry.
Qed.

Lemma state_to_proc_diagrams {n m} (zx zx' : ZX 0 (n + m)) : 
  state_to_proc zx ∝= state_to_proc zx' ->
  zx ∝= zx'.
Proof.
  intros H%proc_to_state_mor.
  now rewrite 2 state_to_proc_to_state in H.
Qed.

Lemma proc_to_state_diagrams {n m} (zx zx' : ZX n m) : 
  proc_to_state zx ∝= proc_to_state zx' ->
  zx ∝= zx'.
Proof.
  intros H%state_to_proc_mor.
  now rewrite 2 proc_to_state_to_proc in H.
Qed.

Lemma state_to_proc_diagrams_iff {n m} (zx zx' : ZX 0 (n + m)) : 
  state_to_proc zx ∝= state_to_proc zx' <->
  zx ∝= zx'.
Proof.
  split; [apply state_to_proc_diagrams | now intros ->].
Qed.

Lemma proc_to_state_diagrams_iff {n m} (zx zx' : ZX n m) : 
  proc_to_state zx ∝= proc_to_state zx' <->
  zx ∝= zx'.
Proof.
  split; [apply proc_to_state_diagrams | now intros ->].
Qed.

Lemma state_to_proc_eq_l {n m} (zx : ZX 0 (n + m)) zx' : 
  state_to_proc zx ∝= zx' <-> zx ∝= proc_to_state zx'.
Proof.
  rewrite <- (proc_to_state_to_proc zx') at 1.
  apply state_to_proc_diagrams_iff.
Qed.

Lemma state_to_proc_eq_r {n m} zx (zx' : ZX 0 (n + m)) : 
  zx ∝= state_to_proc zx' <-> proc_to_state zx ∝= zx'.
Proof.
  rewrite <- (proc_to_state_to_proc zx) at 1.
  apply state_to_proc_diagrams_iff.
Qed.

Lemma proc_to_state_eq_l {n m} zx (zx' : ZX 0 (n + m)) : 
  proc_to_state zx ∝= zx' <-> zx ∝= state_to_proc zx'.
Proof.
  rewrite <- (state_to_proc_to_state zx') at 1.
  apply proc_to_state_diagrams_iff.
Qed.

Lemma proc_to_state_eq_r {n m} (zx : ZX 0 (n + m)) zx' : 
  zx ∝= proc_to_state zx' <-> state_to_proc zx ∝= zx'.
Proof.
  rewrite <- (state_to_proc_to_state zx) at 1.
  apply proc_to_state_diagrams_iff.
Qed.

Lemma proc_to_state_n_wire n : proc_to_state (n_wire n) ∝= n_cap n.
Proof.
  unfold proc_to_state.
  rewrite n_wire_stack, nwire_removal_r.
  reflexivity.
Qed.

Lemma state_to_proc_n_cap n : state_to_proc (n_cap n) ∝= n_wire n.
Proof.
  rewrite state_to_proc_eq_l, proc_to_state_n_wire.
  reflexivity.
Qed.

Lemma proc_to_state_alt {n m} (zx : ZX n m) : 
  proc_to_state zx ∝= n_cap m ⟷ ((zx ⊤) ↕ n_wire m).
Proof.
  unfold proc_to_state.
  apply n_cap_pullthrough_bot.
Qed.

Lemma proc_to_state_effect {n} (zx : ZX n 0) : 
  proc_to_state zx ∝= zx⊤ ↕ ⦰.
Proof.
  unfold proc_to_state.
  rewrite n_cap_pullthrough_bot, n_cap_0_empty, compose_empty_l.
  reflexivity.
Qed.

Lemma state_to_proc_n_cup n : proc_to_state (n_cup n) ∝= n_cap n ↕ ⦰.
Proof.
  apply proc_to_state_effect.
Qed.

(* 
Lemma X_phase_0_controlizer {n m} : 
  is_controlized (X n m 0) 
    (Z 1 2 0 ⟷ ((◁ ⟷ Z 1 0 0 ⟷ Z 0 0 0) ↕ (▷ ⟷ X 1 (n + m) PI))).
Proof.
  split.
  - unfold is_controlled_state.
    rewrite <- compose_assoc, Z_1_2_state_0,
      <- (@stack_compose_distr 0 1 0 0 1 (n + m)).
    rewrite <- 3 compose_assoc.
    rewrite left_triangle_state_0, Z_1_S_state_0.
    rewrite cast_id, compose_empty_l.
    rewrite Z_0_0_to_scalar, Cexp_0.
    distribute_zxscale.
    rewrite stack_empty_l.
    rewrite triangle_state_0.
    (* TODO: use full copy, when we have it *)


    prep_matrix_equivalence.
    rewrite zx_scale_semantics.
    simpl.
    compute_matrix (Z_semantics 0 1 0).
    rewrite X_semantics_equiv.
    unfold X_dirac_semantics.
    unfold xbasis_minus, xbasis_plus, braminus, braplus;
    by_cell; autounfold with U_db; cbn; 
      rewrite 1?Cexp_0, 1?Cexp_PI; C_field; lca.
  - rewrite <- compose_assoc.
    rewrite Z_1_2_state_1, Cexp_0, zx_scale_1_l,
       <- (@stack_compose_distr 0 1 0 0 1 3), <- 3 compose_assoc.
    rewrite left_triangle_state_1, Z_spider_1_1_fusion, Rplus_0_r.
    rewrite Z_0_0_to_scalar, Cexp_0.
    distribute_zxscale.
    rewrite compose_empty_l, stack_empty_l.
    rewrite triangle_state_1.
    rewrite state_1_defn.
    simpl.
    distribute_zxscale.
    rewrite zx_scale_state_to_proc, X_spider_1_1_fusion, state_to_proc_X.
    distribute_zxscale.
    rewrite <- zx_scale_1_l at 1.
    rewrite (X_eq_2_pi _ _ (_ + _)) by lra.
    apply zx_scale_simplify_eq_l.
    C_field; lca.
  Unshelve. all: reflexivity.
Qed. *)

(* FIXME: Make better when we have constant matrices in Qlib *)
Lemma uniform_state_semantics n : ⟦ uniform_state n ⟧ = make_WF (fun _ _ => C1).
Proof.
  induction n.
  - prep_matrix_equivalence.
    unfold uniform_state.
    rewrite cast_id_eq.
    by_cell; reflexivity.
  - prep_matrix_equivalence. 
    simpl_rewrite (uniform_state_split 1 n).
    rewrite (zx_stack_spec 0 1 0 n).
    rewrite IHn.
    replace (⟦ uniform_state 1 ⟧) with (@make_WF 2 1 (fun _ _ => C1)).
    2: {
      prep_matrix_equivalence.
      unfold uniform_state.
      rewrite n_stack_1'.
      by_cell; cbn; rewrite 1?Cexp_0; reflexivity.
    }
    rewrite 3 make_WF_equiv.
    intros i j Hi Hj; unfold kron; lca.
Qed.

Lemma const_of_zx_X_0_1_Z_1_0_gen α β : 
  const_of_zx (X 0 1 α ⟷ Z 1 0 β) = 
  (1 + Cexp α + Cexp β - Cexp (α + β)) / √2.
Proof.
  unfold const_of_zx.
  cbn.
  rewrite kron_1_l by auto_wf.
  unfold hadamard.
  rewrite Cexp_add.
  C_field.
Qed.

Lemma const_of_zx_X_0_1_0_Z_1_0_0 : 
  const_of_zx (X 0 1 0 ⟷ Z 1 0 0) = √2.
Proof.
  rewrite const_of_zx_X_0_1_Z_1_0_gen.
  rewrite Rplus_0_l, Cexp_0.
  C_field; lca.
Qed.

Definition cupcap_controlizer : ZX 1 2 := 
  Z 1 2 0 ⟷ ((◁ ⟷ Z 1 0 0 ⟷ X 0 1 0 ⟷ Z 1 0 0) ↕ 
    (▷ ⟷ X 1 2 PI)).

Lemma cup_is_controlized : 
  is_controlized ⊂ 
  cupcap_controlizer.
Proof.
  unfold cupcap_controlizer.
  split.
  - unfold is_controlled_state.
    rewrite <- compose_assoc, Z_1_2_state_0,
      <- (@stack_compose_distr 0 1 0 0 1 2).
    rewrite <- 4 compose_assoc.
    rewrite compose_assoc, (gadget_is_scaled_empty (X 0 1 0 ⟷_)).
    distribute_zxscale.
    rewrite compose_empty_r, left_triangle_state_0, Z_1_S_state_0.
    rewrite cast_id, stack_empty_l.
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    rewrite triangle_state_0.
    (* TODO: use full copy, when we have it *)

    prep_matrix_equivalence.
    rewrite zx_scale_semantics.
    rewrite zx_compose_spec.
    rewrite <- (n_stack_1' (Z 0 1 0) _ _ : uniform_state 1 ∝= _).
    rewrite 2 uniform_state_semantics.
    simpl.
    rewrite X_semantics_equiv.
    unfold X_dirac_semantics.
    rewrite 2 make_WF_equiv.
    unfold xbasis_minus, xbasis_plus, braminus, braplus;
    by_cell; autounfold with U_db; cbn; 
      rewrite 1?Cexp_PI; C_field; try lca.
  - rewrite <- compose_assoc.
    rewrite Z_1_2_state_1, Cexp_0, zx_scale_1_l,
       <- (@stack_compose_distr 0 1 0 0 1 2), <- 4 compose_assoc.
    rewrite left_triangle_state_1, Z_spider_1_1_fusion, Rplus_0_r.
    rewrite Z_0_0_to_scalar, Cexp_0.
    distribute_zxscale.
    rewrite compose_empty_l.
    rewrite triangle_state_1.
    rewrite X_1_n_state_1.
    rewrite gadget_is_scaled_empty, const_of_zx_X_0_1_0_Z_1_0_0.
    distribute_zxscale.
    rewrite stack_empty_l.
    rewrite X_eq_2_pi by lra.
    rewrite <- cap_X.
    rewrite zx_scale_state_to_proc, zx_scale_assoc.
    rewrite zx_scale_eq_1_l by (simpl; C_field; lca).
    rewrite state_to_proc_eq_r.
    rewrite proc_to_state_state.
    reflexivity.
Qed.

Lemma cap_is_controlized : 
  is_controlized ⊃ 
  cupcap_controlizer.
Proof.
  refine (is_controlized_of_eq_proc_to_state _ _ 
    (eq_refl : (0 + 2 = 2 + 0)%nat) _ _ _ _ 
    (cup_is_controlized)); [|reflexivity].
  cbn.
  rewrite proc_to_state_state.
  rewrite proc_to_state_effect, stack_empty_r, cast_id.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma const_of_zx_Z_gen α : 
  const_of_zx (Z 0 0 α) = 1 + Cexp α.
Proof. reflexivity. Qed.

Lemma const_of_zx_Z_0 : 
  const_of_zx (Z 0 0 0) = 2.
Proof. cbn; rewrite Cexp_0; lca. Qed.

Lemma uniform_state_fold n prf1 prf2 : 
  cast _ _ prf1 prf2 (n ⇑ Z 0 1 0) ∝= uniform_state n.
Proof.
  cast_irrelevance.
Qed.

Lemma uniform_state_defn n : 
  uniform_state n ∝= cast _ _ (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_1_r _))
    (n_stack n (Z 0 1 0)).
Proof.
  reflexivity.
Qed.

Lemma uniform_state_compose_zx_of_perm_r n f : permutation n f -> 
  uniform_state n ⟷ zx_of_perm n f ∝= uniform_state n.
Proof.
  intros Hf.
  prep_matrix_equivalence.
  cbn.
  rewrite zx_of_perm_semantics by auto.
  rewrite uniform_state_semantics.
  unfold perm_to_matrix.
  rewrite make_WF_equiv.
  rewrite perm_mat_permutes_matrix_r by auto_perm.
  reflexivity.
Qed.

(* @nocheck name *)
Lemma uniform_state_compose_ZXperm_r {n m} (zx : ZX n m) : 
  ZXperm zx -> 
  uniform_state n ⟷ zx ∝= uniform_state m.
Proof.
  intros Hzx.
  pose proof Hzx as <-%zxperm_square.
  rewrite <- zx_of_perm_of_zx_square by auto.
  apply uniform_state_compose_zx_of_perm_r.
  auto_zxperm.
Qed.

(* FIXME: Move to CastRules.v*)
(* FIXME: Move *)
Lemma stack_empty_r_fwd {n m} (zx : ZX n m) : 
  zx ↕ ⦰ ∝=
  cast _ _ (Nat.add_0_r _) (Nat.add_0_r _) zx.
Proof. apply stack_empty_r. Qed.
Lemma cast_stack_l_fwd {n0 m0 n0' m0' n1 m1} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfn prfm :
  cast n0' m0' prfn prfm zx0 ↕ zx1 ∝=
  cast _ _ (f_equal (fun k => k + n1)%nat prfn)
    (f_equal (fun k => k + m1)%nat prfm)
    (zx0 ↕ zx1).
Proof. now subst. Qed.
Lemma cast_stack_r_fwd {n0 m0 n1 m1 n1' m1'} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfn prfm :
  zx0 ↕ cast n1' m1' prfn prfm zx1 ∝=
  cast _ _ (f_equal (Nat.add n0) prfn)
    (f_equal (Nat.add m0) prfm)
    (zx0 ↕ zx1).
Proof. now subst. Qed.
(* FIXME: Move *)
Lemma stack_assoc_fwd {n0 n1 n2 m0 m1 m2} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2) :
  zx0 ↕ zx1 ↕ zx2 ∝= 
  cast _ _ (eq_sym (Nat.add_assoc _ _ _)) 
    (eq_sym (Nat.add_assoc _ _ _))
  (zx0 ↕ (zx1 ↕ zx2)).
Proof. apply stack_assoc. Qed.
Lemma stack_assoc_back_fwd {n0 n1 n2 m0 m1 m2} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2) :
  zx0 ↕ (zx1 ↕ zx2) ∝= 
  cast _ _ (Nat.add_assoc _ _ _)
    (Nat.add_assoc _ _ _)
  (zx0 ↕ zx1 ↕ zx2).
Proof. apply stack_assoc_back. Qed.
(* FIXME: Move *)
Lemma cast_compose_eq_mid_join n m o n' m' o' 
	(Hn : n' = n) (Hm Hm' : m' = m) (Ho : o' = o)
	(zx0 : ZX n m) (zx1 : ZX m o) : 
	cast n' m' Hn Hm zx0 ⟷ cast m' o' Hm' Ho zx1 =
	cast n' o' Hn Ho (zx0 ⟷ zx1).
Proof.
	subst.
	now rewrite (Peano_dec.UIP_nat _ _ Hm' eq_refl).
Qed.
Lemma cast_compose_l_eq_mid {n m o n'} (zx0 : ZX n m) (zx1 : ZX m o) 
  prfn prfm : 
  cast n' m prfn prfm zx0 ⟷ zx1 ∝=
  cast n' o prfn eq_refl (zx0 ⟷ zx1).
Proof.
  subst.
  now rewrite cast_id.
Qed.
Lemma cast_compose_r_eq_mid {n m o o'} (zx0 : ZX n m) (zx1 : ZX m o) 
  prfm prfo : 
  zx0 ⟷ cast m o' prfm prfo zx1 ∝=
  cast n o' eq_refl prfo (zx0 ⟷ zx1).
Proof.
  subst.
  now rewrite cast_id.
Qed.
Lemma cast_compose_distribute_l_eq_mid {n m o n'} (zx0 : ZX n m) (zx1 : ZX m o)
  prfn prfo : 
  cast n' o prfn prfo (zx0 ⟷ zx1) ∝=
  cast n' m prfn eq_refl zx0 ⟷ zx1.
Proof.
  subst; now rewrite cast_id.
Qed.
Lemma cast_compose_distribute_r_eq_mid {n m o o'} (zx0 : ZX n m) (zx1 : ZX m o)
  prfn prfo : 
  cast n o' prfn prfo (zx0 ⟷ zx1) ∝=
  zx0 ⟷ cast m o' eq_refl prfo zx1.
Proof.
  subst; now rewrite cast_id.
Qed.
(* FIXME: Move *)
Lemma cast_contract_eq {n0 m0 n1 m1 n2 m2}
  (zx : ZX n0 m0) prfn01 prfm01 prfn12 prfm12 : 
  cast n2 m2 prfn12 prfm12 (cast n1 m1 prfn01 prfm01 zx) = 
  cast n2 m2 (eq_trans prfn12 prfn01) (eq_trans prfm12 prfm01) zx.
Proof.
  now subst.
Qed.

(* FIXME: Move to ZXpermFacts.v *)
Lemma perm_of_zx_comm n m : 
  perm_of_zx (zx_comm n m) = big_swap_perm m n.
Proof.
  apply perm_of_zx_of_perm_cast_eq_WF; auto_perm.
Qed.
#[export] Hint Rewrite perm_of_zx_comm : perm_of_zx_cleanup_db.
Lemma zx_comm_0_l n : zx_comm 0 n ∝=
  cast _ _ eq_refl (Nat.add_0_r n) (n_wire n).
Proof.
  by_perm_eq_nosimpl.
  rewrite perm_of_zx_cast, perm_of_n_wire.
  rewrite perm_of_zx_comm.
  now rewrite big_swap_perm_0_r.
Qed.
Lemma zx_comm_0_r n : zx_comm n 0 ∝=
  cast _ _ (Nat.add_0_r n) eq_refl (n_wire n).
Proof.
  by_perm_eq_nosimpl.
  rewrite perm_of_zx_cast, perm_of_n_wire.
  rewrite perm_of_zx_comm.
  now rewrite big_swap_perm_0_l.
Qed.
Lemma zx_of_perm_0 f : zx_of_perm 0 f ∝= ⦰.
Proof. by_perm_eq. Qed.
Local Open Scope nat_scope.
Lemma zx_mid_comm_prf {a b c d} : 
  a + b + (c + d) = a + (b + c) + d.
Proof. lia. Qed.
Definition zx_mid_comm n0 n1 m0 m1 : 
  ZX (n0 + n1 + (m0 + m1)) (n0 + m0 + (n1 + m1)) :=
  (cast _ _ zx_mid_comm_prf zx_mid_comm_prf
  (n_wire _ ↕ zx_comm n1 m0 ↕ n_wire m1)).
Lemma zx_mid_comm_commutes_r {n0 m0 n1 m1 n2 m2 n3 m3}
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1)
  (zx2 : ZX n2 m2) (zx3 : ZX n3 m3) : 
  ((zx0 ↕ zx1) ↕ (zx2 ↕ zx3)) ⟷ zx_mid_comm m0 m1 m2 m3 ∝=
  zx_mid_comm n0 n1 n2 n3 ⟷ ((zx0 ↕ zx2) ↕ (zx1 ↕ zx3)).
Proof.
  unfold zx_mid_comm.
  rewrite stack_assoc_back_fwd, (stack_assoc_fwd zx0), cast_stack_l_fwd.
  rewrite cast_contract_eq, cast_compose_eq_mid_join.
  symmetry.
  rewrite stack_assoc_back_fwd, (stack_assoc_fwd zx0), cast_stack_l_fwd.
  rewrite cast_contract_eq, cast_compose_eq_mid_join.
  apply cast_simplify_eq.
  rewrite <- 4!stack_compose_distr.
  rewrite 2!nwire_removal_l, 2!nwire_removal_r, zx_comm_commutes_r.
  reflexivity.
Qed.
Lemma zx_mid_comm_transpose n0 n1 m0 m1 : 
  (zx_mid_comm n0 n1 m0 m1) ⊤%ZX ∝=
  zx_mid_comm n0 m0 n1 m1.
Proof.
  unfold zx_mid_comm.
  rewrite cast_transpose, 2!stack_transpose, 
    2!n_wire_transpose, zx_comm_transpose.
  reflexivity.
Qed.
Lemma zx_mid_comm_0_first a b c : 
  zx_mid_comm 0 a b c ∝=
  cast _ _ (Nat.add_assoc _ _ _ ) (Nat.add_assoc _ _ _ ) 
    (zx_comm a b ↕ n_wire c).
Proof.
  unfold zx_mid_comm.
  rewrite stack_empty_l.
  cast_irrelevance.
Qed.
Lemma zx_mid_comm_0_second a b c : 
  zx_mid_comm a 0 b c ∝=
  cast _ _ zx_mid_comm_prf eq_refl (n_wire _).
Proof.
  unfold zx_mid_comm.
  rewrite zx_comm_0_l.
  rewrite cast_stack_r_fwd, cast_stack_l_fwd.
  rewrite cast_contract_eq.
  rewrite 2!n_wire_stack.
  cast_irrelevance.
Qed.
Lemma zx_mid_comm_0_third a b c : 
  zx_mid_comm a b 0 c ∝=
  cast _ _ eq_refl (@zx_mid_comm_prf a 0 b c) (n_wire _).
Proof.
  unfold zx_mid_comm.
  rewrite zx_comm_0_r.
  rewrite cast_stack_r_fwd, cast_stack_l_fwd.
  rewrite cast_contract_eq.
  rewrite 2!n_wire_stack.
  cast_irrelevance.
Qed.
Lemma zx_mid_comm_0_fourth_prf {a b c} : a + b + (c + 0) = a + (b + c).
Proof. lia. Qed.
Lemma zx_mid_comm_0_fourth a b c : 
  zx_mid_comm a b c 0 ∝= 
   cast _ _ zx_mid_comm_0_fourth_prf zx_mid_comm_0_fourth_prf
    (n_wire a ↕ zx_comm b c).
Proof.
  unfold zx_mid_comm.
	rewrite stack_empty_r_fwd, cast_contract_eq.
  cast_irrelevance.
Qed.
Lemma zx_mid_comm_zxperm a b c d : ZXperm (zx_mid_comm a b c d).
Proof.
  unfold zx_mid_comm.
  auto_zxperm.
Qed.
#[export] Hint Resolve zx_mid_comm_zxperm : zxperm_db.
Lemma perm_of_zx_mid_comm a b c d : 
  perm_of_zx (zx_mid_comm a b c d) = 
  stack_perms (a + b + c) d 
    (stack_perms a (b + c) idn (big_swap_perm c b)) idn.
Proof.
  unfold zx_mid_comm.
  rewrite perm_of_zx_cast.
  cbn.
  rewrite 2!perm_of_n_wire, perm_of_zx_comm.
  now rewrite Nat.add_assoc.
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

(* FIXME: Move (I guess to vectorstates?? But b2R shouldn't go there either...) *)
(* @nocheck name *)
Lemma b2R_mult b c : (b2R b * b2R c = b2R (b && c))%R.
Proof.
  destruct b, c; cbn; lra.
Qed.


(* FIXME: Move, to CastRules? Or maybe ComposeRules? *)
Lemma compose_simplify_casted {n m m' o} 
  (zx0 : ZX n m) (zx1 : ZX m o) (zx0' : ZX n m') (zx1' : ZX m' o) 
  (Hm : m = m') : 
  zx0 ∝= cast _ _ eq_refl Hm zx0' ->
  zx1 ∝= cast _ _ Hm eq_refl zx1' ->
  zx0 ⟷ zx1 ∝= zx0' ⟷ zx1'.
Proof.
  subst.
  now intros -> ->.
Qed.
Lemma compose_simplify_casted_abs {n m m' o : nat} 
  (zx0 : ZX n m) (zx1 : ZX m o) 
  (zx0' : ZX n m') (zx1' : ZX m' o) (Hm : m = m') : 
  (forall Hm', zx0 ∝= cast _ _ eq_refl Hm' zx0') ->
  (forall Hm', zx1 ∝= cast _ _ Hm' eq_refl zx1') ->
  zx0 ⟷ zx1 ∝= zx0' ⟷ zx1'.
Proof.
  subst.
  intros H H'.
  now rewrite (H eq_refl), (H' eq_refl).
Qed.

(* FIXME: Move to CapCupRules.v *)
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
Lemma n_cup_unswapped_grow_l : forall n prfn prfm, 
  n_cup_unswapped (S n) ∝= cast _ _ prfn prfm (n_wire n ↕ ⊃ ↕ n_wire n) ⟷ n_cup_unswapped n.
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
    rewrite 3 stack_assoc_back.
    simpl_casts.
    rewrite <- (@cast_n_wire (n + 1) (1 + n)) at 2.
    rewrite cast_stack_r.
    simpl.
    rewrite (stack_assoc (— ↕ n_wire n ↕ ⊃) (n_wire n) —).
    rewrite <- n_wire_stack.
    simpl_casts.
    now rewrite <- wire_to_n_wire.
Unshelve.
  all: lia.
Qed.
Lemma n_stacked_pf_1 {n} : (n + n = n * 2)%nat. Proof. lia. Qed.
Lemma n_stacked_pf_2 {n} : (0 = n * 0)%nat. Proof. lia. Qed.
Definition n_stacked_caps n : ZX (n + n) 0 :=
  cast _ _ n_stacked_pf_1 n_stacked_pf_2 (n ⇑ ⊃).
Definition n_stacked_cups n : ZX 0 (n + n) :=
  cast _ _ n_stacked_pf_2 n_stacked_pf_1 (n ⇑ ⊂).
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
(* FIXME: Move to Qlib *)
(* @nocheck name *)
Lemma WF_Perm_rw {n f g} (Hfg : perm_eq n f g) : 
  WF_Perm n f -> WF_Perm n g -> f = g.
Proof.
  intros Hf Hg.
  now eq_by_WF_perm_eq n.
Qed.
(* FIXME: Move to Qlib *)
Lemma big_swap_perm_left p q a : a < p -> 
  big_swap_perm p q a = a + q.
Proof. unfold big_swap_perm; bdestructΩ'. Qed.
Lemma big_swap_perm_right p q a : p <= a < p + q -> 
  big_swap_perm p q a = a - p.
Proof. unfold big_swap_perm; bdestructΩ'. Qed.
(* FIXME: Move to Qlib.Modulus *)
Lemma div_add_n_r a n (Hn : n <> 0) : 
  (a + n) / n = a / n + 1.
Proof.
  pose proof (Nat.div_mod_eq (a + n) n).
  rewrite mod_add_n_r in H.
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
    + rewrite cast_contract_eq, cast_id.
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

Definition swap_controlizer : ZX 1 (2 + 2) :=
  (Z 1 3 0 ⟷ (Z 0 0 0 ↕ (◁ ⟷ Z 1 0 0) ↕ (◁ ⟷ Z 1 0 0) ↕ 
    (X 1 1 PI ⟷ Z 1 2 0 ⟷ ((◁ ⟷ X 1 2 0) ↕ (◁ ⟷ X 1 2 0))
    ⟷ (— ↕ (⨉ ↕ — ⟷ (— ↕ ⨉)))) )).

Lemma swap_is_controlized : 
  is_controlized ⨉  
    swap_controlizer.
Proof.
  unfold swap_controlizer.
  rewrite gadget_is_scaled_empty, const_of_zx_Z_0.
  distribute_zxscale; rewrite stack_empty_l.
  rewrite zx_scale_compose_distr_r.
  split.
  - unfold is_controlled_state.
    rewrite zx_scale_compose_distr_r.
    rewrite <- compose_assoc.
    rewrite Z_1_S_state_0.
    cbn.
    rewrite stack_empty_r, cast_id, (@stack_assoc_back 0 0 0 1 1 1), 2 cast_id.
    rewrite <- (@stack_compose_distr 0 2 0 0 1 4).
    rewrite <- (@stack_compose_distr 0 1 0 0 1 0).
    rewrite <- 2 compose_assoc, left_triangle_state_0, Z_1_S_state_0.
    cbn.
    rewrite cast_id, 2 stack_empty_l.
    rewrite <- 2 compose_assoc.
    rewrite <- not_defn, not_state_0.
    rewrite Z_1_S_state_1.
    rewrite (zx_scale_eq_1_l (Cexp 0)) by apply Cexp_0.
    cbn.
    rewrite stack_empty_r, 2 cast_id.
    rewrite <- (@stack_compose_distr 0 1 2 0 1 2).
    rewrite <- compose_assoc.
    rewrite left_triangle_state_1.
    rewrite (to_scale Z_state_0_copy).
    distribute_zxscale.
    rewrite zx_scale_compose_distr_l, zx_scale_assoc.
    rewrite zx_scale_eq_1_l by 
      (autorewrite with RtoC_db; rewrite <- RtoC_pow;
      simpl; C_field).
    
    rewrite <- uniform_state_defn, <- uniform_state_split.
    now rewrite uniform_state_compose_ZXperm_r by auto_zxperm.
  - rewrite zx_scale_compose_distr_r.
    distribute_zxscale.
    rewrite <- compose_assoc.
    rewrite Z_1_S_state_1.
    rewrite Cexp_0, zx_scale_1_l.
    cbn -[Cpow].
    rewrite stack_empty_r, cast_id, (@stack_assoc_back 0 0 0 1 1 1), 2 cast_id.
    rewrite <- (@stack_compose_distr 0 2 0 0 1 4).
    rewrite <- (@stack_compose_distr 0 1 0 0 1 0).
    rewrite <- 2 compose_assoc, left_triangle_state_1. 
    rewrite Z_spider_1_1_fusion, Rplus_0_r.
    rewrite (gadget_is_scaled_empty (Z 0 0 0)).
    rewrite const_of_zx_Z_0.
    distribute_zxscale.
    rewrite zx_scale_stack_distr_l, 2 stack_empty_l.
    cbn -[Cpow].
    rewrite zx_scale_state_to_proc.
    distribute_zxscale.
    rewrite <- 2 compose_assoc.
    rewrite <- not_defn, not_state_1.
    rewrite Z_1_S_state_0.
    cbn -[Cpow].
    rewrite stack_empty_r, 2 cast_id.
    rewrite <- (@stack_compose_distr 0 1 2 0 1 2).
    rewrite <- compose_assoc.
    rewrite left_triangle_state_0.
    rewrite X_1_n_state_0.
    distribute_zxscale.
    rewrite zx_scale_compose_distr_l, zx_scale_state_to_proc, zx_scale_assoc.
    rewrite zx_scale_eq_1_l by 
      (simpl; C_field).
    rewrite <- cap_X.
    rewrite state_to_proc_eq_r.
    unfold proc_to_state.
    rewrite n_cap_to_n_stacked_cups.
    unfold n_stacked_cups.
    cbn; rewrite stack_empty_r, 2 cast_id.
    rewrite compose_assoc. 
    apply compose_simplify_eq; [reflexivity|].
    change 4 with (2 * 2).
    by_perm_eq.
    by_perm_cell; reflexivity.
  Unshelve. all: lia.
Qed.

Definition wire_controlizer : ZX 1 (1 + 1) :=
  compose_controlizer box_controlizer box_controlizer.

Lemma wire_is_controlized : 
  is_controlized — wire_controlizer.
Proof.
  rewrite <- box_compose.
  apply compose_is_controlized; apply box_is_controlized.
Qed.

Lemma const_of_zx_invsqrt2 : const_of_zx zx_invsqrt2 = /√2.
Proof.
  unfold const_of_zx.
  rewrite zx_invsqrt2_semantics.
  lca.
Qed.

Definition half_controlizer : ZX 1 (0 + 0) :=
  (zx_invsqrt2 ↕ zx_invsqrt2) ↕ (▷ ⟷ Z 1 0 0).

Lemma half_is_controlized : is_controlized (/ C2 .* ⦰) half_controlizer.
Proof.
  apply controlled_scalar_is_controlized_scaled_empty.
  unfold half_controlizer.
  unfold is_controlled_scalar.
  rewrite (gadget_is_scaled_empty zx_invsqrt2).
  rewrite zx_scale_stack_distr_l, zx_scale_stack_distr_r, zx_scale_assoc, 
    zx_scale_stack_distr_l, 2 stack_empty_l.
  rewrite const_of_zx_invsqrt2.
  rewrite <- Cinv_mult_distr, Csqrt2_sqrt.
  apply controlled_half_is_controlled_scalar.
Qed.

Definition two_controlizer : ZX 1 (0 + 0) :=
  ◁ ⟷ Z 1 0 0.

Lemma two_is_controlized : is_controlized (C2 .* ⦰) two_controlizer.
Proof.
  apply controlled_scalar_is_controlized_scaled_empty.
  unfold two_controlizer.
  unfold is_controlled_scalar.
  rewrite <- 2 compose_assoc.
  rewrite left_triangle_state_0, left_triangle_state_1.
  rewrite Z_1_S_state_0, Z_spider_1_1_fusion.
  split; [now rewrite cast_id|].
  rewrite Rplus_0_r, Z_0_0_to_scalar.
  apply zx_scale_simplify_eq_l.
  rewrite Cexp_0; lca.
Qed.

Definition empty_controlizer : ZX 1 0 := 
  stack_controlizer half_controlizer two_controlizer.

Lemma empty_is_controlized : is_controlized ⦰ empty_controlizer.
Proof.
  rewrite <- zx_scale_1_l.
  eapply is_controlized_mor; [ | reflexivity|].
  1: {
    instantiate (1 := (/C2 .* ⦰) ↕ (C2 .* ⦰)).
    distribute_zxscale.
    rewrite stack_empty_l.
    now rewrite zx_scale_eq_1_l by C_field.
  }
  unfold empty_controlizer.
  apply (@stack_is_controlized 0 0 0 0).
  - apply half_is_controlized.
  - apply two_is_controlized.
Qed.

Fixpoint n_stack_controlizer {n m} k (czx : ZX 1 (n + m)) : ZX 1 (k * n + k * m) :=
  match k with
  | 0 => empty_controlizer
  | S k' => stack_controlizer czx (n_stack_controlizer k' czx)
  end.

Lemma n_stack_is_controlized {n m} k (zx : ZX n m) czx : 
  is_controlized zx czx -> is_controlized (k ⇑ zx) (n_stack_controlizer k czx).
Proof.
  intros Hzx.
  induction k.
  - apply empty_is_controlized.
  - apply (stack_is_controlized _ _ _ _ Hzx IHk).
Qed.

Fixpoint n_stack1_controlizer k (czx : ZX 1 (1 + 1)) : ZX 1 (k + k) :=
  match k with
  | 0 => empty_controlizer
  | S k' => stack_controlizer czx (n_stack1_controlizer k' czx)
  end.

Lemma n_stack1_is_controlized k (zx : ZX 1 1) czx : 
  is_controlized zx czx -> is_controlized (k ↑ zx) (n_stack1_controlizer k czx).
Proof.
  intros Hzx.
  induction k.
  - apply empty_is_controlized.
  - apply (stack_is_controlized _ _ _ _ Hzx IHk).
Qed.

Definition n_wire_controlizer n : ZX 1 (n + n) :=
  n_stack1_controlizer n wire_controlizer.

Lemma n_wire_is_controlized n : 
  is_controlized (n_wire n) (n_wire_controlizer n).
Proof.
  apply n_stack1_is_controlized, wire_is_controlized.
Qed.

Lemma is_controlized_cast_l {n m n' m'} zx czx (prfn : n = n') (prfm : m = m') : 
  is_controlized (cast _ _ prfn prfm zx) czx <-> 
  is_controlized zx (cast _ _ eq_refl (eq_sym (f_equal2 Nat.add prfn prfm)) czx).
Proof.
  subst.
  now rewrite 2 cast_id_eq.
Qed.

Lemma proc_to_state_colorswap {n m} (zx : ZX n m) : 
  ⊙ (proc_to_state zx) ∝= proc_to_state (⊙ zx).
Proof.
  unfold proc_to_state.
  cbn -[n_cup].
  autorewrite with colorswap_db.
  reflexivity.
Qed.

Lemma state_to_proc_colorswap {n m} (zx : ZX 0 (n + m)) : 
  ⊙ (state_to_proc zx) ∝= state_to_proc (⊙ zx).
Proof.
  unfold state_to_proc.
  cbn -[n_cup].
  autorewrite with colorswap_db.
  cbn -[n_cup].
  autorewrite with colorswap_db.
  reflexivity.
Qed.

#[export] Hint Rewrite @proc_to_state_colorswap 
  @state_to_proc_colorswap : colorswap_db.


Definition X_2_1_controlizer : ZX 1 (2 + 1) := X_1_2_controlizer.

Lemma X_2_1_is_controlized : 
  is_controlized (X 2 1 0) X_2_1_controlizer.
Proof.
  refine (is_controlized_of_eq_proc_to_state _ _ 
    (eq_refl : (1 + 2 = 2 + 1)%nat) _ _ _ _ 
    (X_1_2_is_controlized)); [|reflexivity].
  cbn.
  rewrite 2 proc_to_state_X.
  reflexivity.
Qed.

Definition X_0_1_controlizer β : ZX 1 (0 + 1) := X_1_0_controlizer β.

Lemma X_0_1_is_controlized β : 
  is_controlized (X 0 1 β) (X_0_1_controlizer β).
Proof.
  refine (is_controlized_of_eq_proc_to_state _ _ 
    (eq_refl : (1 + 0 = 0 + 1)%nat) _ _ _ _ 
    (X_1_0_is_controlized β)); [|reflexivity].
  cbn.
  rewrite 2 proc_to_state_X.
  reflexivity.
Qed.


Fixpoint X_S_0_controlizer n β : ZX 1 (S n + 0) :=
  match n with 
  | 0 => X_1_0_controlizer β
  | S n' => compose_controlizer
    (stack_controlizer X_2_1_controlizer (n_wire_controlizer n'))
    (X_S_0_controlizer n' β)
  end.

Lemma X_S_0_is_controlled β n : 
  is_controlized (X (S n) 0 β) (X_S_0_controlizer n β).
Proof.
  induction n.
  - apply X_1_0_is_controlized.
  - rewrite grow_X_top_left.
    cbn.
    apply compose_is_controlized.
    + apply (@stack_is_controlized 2 1 n n).
      * apply X_2_1_is_controlized.
      * apply n_wire_is_controlized.
    + apply IHn.
Qed.

Fixpoint X_0_S_controlizer n β : ZX 1 (0 + S n) :=
  match n with 
  | 0 => X_0_1_controlizer β
  | S n' => compose_controlizer
    (X_0_S_controlizer n' β)
    (stack_controlizer X_1_2_controlizer (n_wire_controlizer n'))
  end.

Lemma X_0_S_is_controlized β n : 
  is_controlized (X 0 (S n) β) (X_0_S_controlizer n β).
Proof.
  induction n.
  - apply X_0_1_is_controlized.
  - rewrite grow_X_top_right.
    cbn.
    apply compose_is_controlized.
    + apply IHn.
    + apply (@stack_is_controlized 1 2 n n).
      * apply X_1_2_is_controlized.
      * apply n_wire_is_controlized.
Qed.

(* TODO: Make this not depend on the non-effective controlled_decomp *)
Definition X_0_n_controlizer n β : ZX 1 n :=
  match n with 
  | 0 => 
    compose_controlizer (X_0_1_controlizer β) 
      (X_1_0_controlizer 0)
  | S n' => X_0_S_controlizer n' β
  end.

Lemma X_0_0_is_Z_0_0 β : X 0 0 β ∝= Z 0 0 β.
Proof.
  change ((⊙ (Z 0 0 β)) ∝= Z 0 0 β).
  rewrite colorswap_is_bihadamard.
  simpl.
  now rewrite compose_empty_l, compose_empty_r.
Qed.

Lemma Z_0_0_is_X_0_0 β : Z 0 0 β ∝= X 0 0 β.
Proof.
  colorswap_of (X_0_0_is_Z_0_0 β).
Qed.

Lemma const_of_zx_X_gen β : const_of_zx (X 0 0 β) = (C1 + Cexp β)%C.
Proof.
  rewrite X_0_0_is_Z_0_0.
  apply const_of_zx_Z_gen.
Qed. 

Lemma X_0_n_is_controlized n β : 
  is_controlized (X 0 n β) (X_0_n_controlizer n β).
Proof.
  destruct n; simpl.
  - rewrite <- (Rplus_0_r β) at 1.
    rewrite <- X_spider_1_1_fusion.
    apply compose_is_controlized.
    + apply X_0_1_is_controlized.
    + apply X_1_0_is_controlized.
  - apply X_0_S_is_controlized.
Qed.

Definition X_controlizer n m β : ZX 1 (n + m) :=
  X_0_n_controlizer (n + m) β.

Lemma X_is_controlized n m β : 
  is_controlized (X n m β) (X_controlizer n m β).
Proof.
  refine (is_controlized_of_eq_proc_to_state _ _ 
    (eq_refl : 0 + (n + m) = (n + m)) _ _ _ _ 
    (X_0_n_is_controlized (n + m) β)); [|reflexivity].
  cbn.
  now rewrite 2 proc_to_state_X.
Qed.

Definition Z_controlizer n m β : ZX 1 (n + m) :=
  compose_controlizer (compose_controlizer
    (n_stack1_controlizer n box_controlizer)
    (X_controlizer n m β))
    (n_stack1_controlizer m box_controlizer).

Lemma Z_is_controlized n m β : 
  is_controlized (Z n m β) 
    (Z_controlizer n m β).
Proof.
  rewrite Z_to_X.
  unfold Z_controlizer.
  apply compose_is_controlized; [apply compose_is_controlized|].
  - apply n_stack1_is_controlized, box_is_controlized.
  - apply X_is_controlized.
  - apply n_stack1_is_controlized, box_is_controlized.
Qed.

Fixpoint controlizer {n m} (zx : ZX n m) : ZX 1 (n + m) :=
  match zx with
  | ⦰ => empty_controlizer
  | — => wire_controlizer
  | □ => box_controlizer
  | ⊂ => cupcap_controlizer
  | ⊃ => cupcap_controlizer
  | ⨉ => swap_controlizer
  | X n m α => X_controlizer n m α
  | Z n m α => Z_controlizer n m α
  | zx0 ↕ zx1 => stack_controlizer (controlizer zx0) (controlizer zx1)
  | zx0 ⟷ zx1 => compose_controlizer (controlizer zx0) (controlizer zx1)
  end.

Lemma zx_is_controlized {n m} (zx : ZX n m) : 
  is_controlized zx (controlizer zx).
Proof.
  induction zx; cbn.
  - apply empty_is_controlized.
  - apply cup_is_controlized.
  - apply cap_is_controlized.
  - apply swap_is_controlized.
  - apply wire_is_controlized.
  - apply box_is_controlized.
  - apply X_is_controlized.
  - apply Z_is_controlized.
  - now apply stack_is_controlized.
  - now apply compose_is_controlized.
Qed.


Lemma nn_n2 {n:nat} : n + n = n * 2. Proof. lia. Qed.
Definition sum_controlizer {n} (c0 c1 : ZX 1 n) : ZX 1 n :=
  (X 0 1 0 ⟷ Z 1 0 0) ↕
  (
    Z 1 2 0 ⟷ (X 1 2 0 ↕ ◁) ⟷ (— ↕ Z 2 1 0) ⟷
    (c0 ↕ c1)
  ) ⟷
  zx_of_perm_cast (n + n) (n * 2) (kron_comm_perm 2 n) nn_n2 ⟷
  n ⇑ Z 2 1 0 ⟷
  cast _ _ (Nat.mul_1_r n) eq_refl (n_wire n).

Lemma cast_uniform_state n n' prf0 prf : 
  cast 0 n' prf0 prf (uniform_state n) = uniform_state n'.
Proof.
  subst; now rewrite cast_id_eq.
Qed.

Lemma n_stack_mul {n m} k l (zx : ZX n m) : 
  (k * l) ⇑ zx ∝=
  cast _ _ (eq_sym (Nat.mul_assoc _ _ _)) (eq_sym (Nat.mul_assoc _ _ _))
  (k ⇑ (l ⇑ zx)).
Proof.
  induction k.
  - simpl.
    now rewrite cast_id.
  - simpl.
    rewrite nstack_split, IHk.
    simpl_casts.
    reflexivity.
  Unshelve. all: lia.
Qed.

Lemma Z_2_1_state_11 : state_1 ↕ state_1 ⟷ Z 2 1 0 ∝ state_1.
Proof.
  rewrite push_out_top, compose_assoc.
  rewrite Z_2_1_0_state_1_top.
  rewrite <- 2 compose_assoc.
  rewrite not_state_1, lambda_frac_box_state_0, not_state_0.
  reflexivity.
Qed.

Lemma Z_2_1_state_00 : state_0 ↕ state_0 ⟷ Z 2 1 0 ∝ state_0.
Proof.
  rewrite push_out_top, compose_assoc.
  rewrite Z_2_1_0_state_0_top.
  rewrite lambda_frac_box_state_0.
  reflexivity.
Qed.



Lemma sum_controlizer_is_controlled_state {n} (c0 c1 : ZX 1 n) :
  is_controlled_state c0 -> is_controlled_state c1 -> 
  is_controlled_state (sum_controlizer c0 c1).
Proof.
  unfold is_controlled_state.
  intros H0 H1.
  unfold sum_controlizer.
  rewrite gadget_is_scaled_empty, const_of_zx_X_0_1_Z_1_0_gen.
  distribute_zxscale.
  rewrite zx_scale_compose_distr_r.
  rewrite stack_empty_l.
  rewrite Rplus_0_r, Cexp_0, Cminus_unfold, <- Cplus_assoc, Cplus_opp_r, Cplus_0_r.
  rewrite <- 6 compose_assoc.
  rewrite Z_1_2_state_0.
  rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
  rewrite X_1_n_state_0, left_triangle_state_0.
  distribute_zxscale; rewrite 3 zx_scale_compose_distr_l.
  distribute_zxscale.
  rewrite zx_scale_eq_1_l by (C_field; lca).
  rewrite <- cap_X.
  rewrite (stack_split_antidiag ⊂), stack_empty_l.
  rewrite (compose_assoc state_0).
  rewrite <- (Z_wrap_over_top_right 1 1).
  rewrite Z_1_2_state_0.
  rewrite <- (@stack_compose_distr 0 1 n 0 1 n).
  rewrite H0, H1.
  rewrite <- uniform_state_split.
  unfold zx_of_perm_cast.
  (* rewrite (cast_compose_r _ _ (uniform_state _)). *)
  rewrite cast_compose_r_eq_mid.
  rewrite uniform_state_compose_zx_of_perm_r by
    (cbn; replace (n+n) with (n*2) by lia; auto_perm).
  rewrite cast_uniform_state.
  unfold uniform_state.
  rewrite n_stack_mul, cast_contract, cast_compose_l_eq_mid.
  rewrite <- n_stack_compose.
  cbn.
  rewrite stack_empty_r, cast_id.
  rewrite <- (Z_add_l 0 0), 2 Rplus_0_r.
  rewrite cast_compose_r, nwire_removal_r.
  rewrite 2 cast_contract.
  cast_irrelevance.
  Unshelve. all: lia.
Qed.


Lemma Z_2_1_semantics_f_to_vec f :
  ⟦ Z 2 1 0 ⟧ × f_to_vec 2 f = 
  if eqb (f 0) (f 1) then e_i (Nat.b2n (f 0)) else Zero.
Proof.
  apply mat_equiv_eq; [auto_wf|bdestruct_one; auto_wf|].
  by_cell; cbn; Csimpl.
  - destruct (f 0), (f 1); unfold kron; cbn; lca.
  - rewrite Cexp_0, Cmult_1_l.
    destruct (f 0), (f 1); unfold kron; cbn; lca.
Qed.


Lemma Z_2_1_semantics_f_to_vec_l f :
  (f_to_vec 1 f) ⊤%M × ⟦ Z 2 1 0 ⟧ = 
  (f_to_vec 2 (fun i => f (i / 2))) ⊤%M.
Proof.
  prep_matrix_equivalence.
  by_cell; cbn; Csimpl; rewrite kron_1_l, 1?Cexp_0 by auto_wf;
  unfold transpose; destruct (f 0); cbn; lca.
Qed.

Lemma n_stack_Z_2_1_semantics_f_to_vec_l f k :
  (f_to_vec k f) ⊤%M × ⟦ k ⇑ Z 2 1 0 ⟧ = 
  (f_to_vec (k * 2) (fun i => f (i / 2))) ⊤%M.
Proof.
  revert f;
  induction k; intros f.
  - simpl.
    now Msimpl.
  - change (S k) with (1 + k). 
    rewrite (f_to_vec_split'_eq 1 k).
    rewrite (kron_transpose' (f_to_vec 1 f) (f_to_vec k _)).
    change ((1 + k) ⇑ ?x) with (x ↕ k ⇑ x).
    change ((1 + k) * 2) with (2 + k * 2).
    change ((1 + k) * 1) with (1 + k * 1).
    rewrite zx_stack_spec.
    restore_dims.
    rewrite kron_mixed_product' by (first [reflexivity | now rewrite Nat.mul_1_r]).
    rewrite Z_2_1_semantics_f_to_vec_l.
    rewrite IHk.
    rewrite <- kron_transpose.
    f_equal; [unify_pows_two|].
    rewrite f_to_vec_merge.
    apply f_to_vec_eq.
    intros i Hi.
    bdestructΩ'.
    f_equal.
    replace i with ((i - 2) + 2) at 2 by lia.
    rewrite div_add_n_r; lia.
Qed.

Lemma permed_n_stack_Z_2_1_semantics_f_to_vec_l f n : 
  (f_to_vec n f) ⊤%M × ⟦ zx_of_perm (n * 2) (kron_comm_perm 2 n) ⟷ n ⇑ Z 2 1 0 ⟧ = 
  (f_to_vec n f) ⊤%M ⊗ (f_to_vec n f) ⊤%M.
Proof.
  rewrite zx_compose_spec.
  replace (@Mmult 1 (2^n) (2^n*2^n)) with 
    (@Mmult 1 (2^n) (2^(n*2)))
    by (unify_pows_two; do 2 f_equal; lia).
  replace (@Mmult (2^(n*1))) with 
    (@Mmult (2^n))
    by (do 2 f_equal; lia).
  rewrite <- Mmult_assoc.
  rewrite n_stack_Z_2_1_semantics_f_to_vec_l.
  rewrite zx_of_perm_semantics by auto_perm.
  rewrite perm_to_matrix_permutes_qubits_l by auto_perm.
  rewrite <- kron_transpose, f_to_vec_merge.
  f_equal; [unify_pows_two|].
  replace (n + n) with (n * 2) by lia.
  apply f_to_vec_eq.
  intros i Hi.
  rewrite Nat.mul_comm.
  rewrite kron_comm_perm_inv, kron_comm_perm_defn by lia.
  rewrite Nat.div_add_l, Nat.div_div, Nat.div_small, Nat.add_0_r by lia.
  bdestruct (i <? n).
  - rewrite Nat.mod_small by lia.
    reflexivity.
  - rewrite Modulus.mod_n_to_2n by lia.
    reflexivity.
Qed.

(* @nocheck name *)
Lemma Cexp_PI' : Cexp PI = - C1.
Proof. rewrite Cexp_PI; lca. Qed.
Lemma sum_controlizer_state_1_step1 {n} (c0 c1 : ZX 1 n) :
  state_1 ⟷ sum_controlizer c0 c1 ∝=
  X 0 2 PI ⟷ (c0 ↕ c1)
  ⟷ cast _ _ nn_n2 (eq_sym (Nat.mul_1_r n)) 
    (zx_of_perm (n * 2) (kron_comm_perm 2 n) ⟷ n ⇑ Z 2 1 0).
Proof.
  unfold sum_controlizer.
  rewrite gadget_is_scaled_empty, const_of_zx_X_0_1_Z_1_0_gen.
  distribute_zxscale.
  rewrite zx_scale_compose_distr_r.
  rewrite stack_empty_l.
  rewrite Rplus_0_r, Cexp_0, Cminus_unfold, <- Cplus_assoc, Cplus_opp_r, Cplus_0_r.
  rewrite <- 6 compose_assoc.
  rewrite Z_1_2_state_1, Cexp_0, zx_scale_1_l.
  rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
  rewrite X_1_n_state_1, left_triangle_state_1, Rplus_0_r.
  distribute_zxscale; rewrite 3 zx_scale_compose_distr_l.
  distribute_zxscale.
  rewrite push_out_bot, cast_id.
  rewrite (compose_assoc (X 0 2 _) (n_wire 2 ↕_)).
  rewrite <- (n_wire_stack 1 1), (@stack_assoc 1 1 0 1 1 1), cast_id.
  rewrite <- (@stack_compose_distr 1 1 1 1 2 1).
  rewrite (dominated_Z_spider_fusion_bot_right 0 0 1 1), wire_removal_r.
  rewrite Rplus_0_r, Z_is_wire, wire_to_n_wire, n_wire_stack, nwire_removal_r.
  (* rewrite X_0_2_pi_to_cup_not. *)
  (* rewrite (compose_assoc (X 0 2 _)). *)
  (* rewrite wire_removal_l. *)
  rewrite zx_scale_eq_1_l by (C_field; lca).
  unfold zx_of_perm_cast.
  rewrite cast_zx_of_perm_natural_r.
  rewrite compose_assoc, (cast_compose_r _ _ (_ ⇑ _)), 
    nwire_removal_r, cast_contract.
  rewrite compose_assoc.
  rewrite cast_compose_eq_mid_join.
  apply compose_simplify_eq; [reflexivity|].
  cast_irrelevance.
  Unshelve. all: lia.
Qed.

(* Lemma sum_controlizer_state_1_step1 {n} (c0 c1 : ZX 1 n) :
  state_1 ⟷ sum_controlizer c0 c1 ∝=
  ⊂ ⟷ (c0 ↕ (NOT ⟷ c1))
  ⟷ cast _ _ nn_n2 (eq_sym (Nat.mul_1_r n)) 
    (zx_of_perm (n * 2) (kron_comm_perm 2 n) ⟷ n ⇑ Z 2 1 0).
Proof.
  unfold sum_controlizer.
  rewrite gadget_is_scaled_empty, const_of_zx_X_0_1_Z_1_0_gen.
  distribute_zxscale.
  rewrite zx_scale_compose_distr_r.
  rewrite stack_empty_l.
  rewrite Rplus_0_r, Cexp_0, Cminus_unfold, <- Cplus_assoc, Cplus_opp_r, Cplus_0_r.
  rewrite <- 6 compose_assoc.
  rewrite Z_1_2_state_1, Cexp_0, zx_scale_1_l.
  rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
  rewrite X_1_n_state_1, left_triangle_state_1, Rplus_0_r.
  distribute_zxscale; rewrite 3 zx_scale_compose_distr_l.
  distribute_zxscale.
  rewrite push_out_bot, cast_id.
  rewrite (compose_assoc (X 0 2 _)).
  rewrite <- (n_wire_stack 1 1), (@stack_assoc 1 1 0 1 1 1), cast_id.
  rewrite <- (@stack_compose_distr 1 1 1 1 2 1).
  rewrite (dominated_Z_spider_fusion_bot_right 0 0 1 1), wire_removal_r.
  rewrite Rplus_0_r, Z_is_wire, wire_to_n_wire, n_wire_stack, nwire_removal_r.
  rewrite X_0_2_pi_to_cup_not.
  rewrite (compose_assoc ⊂), <- (@stack_compose_distr 1 1 n 1 1 n).
  rewrite wire_removal_l.
  rewrite zx_scale_eq_1_l by (C_field; lca).
  unfold zx_of_perm_cast.
  rewrite cast_zx_of_perm_natural_r.
  rewrite compose_assoc, (cast_compose_r _ _ (_ ⇑ _)), 
    nwire_removal_r, cast_contract.
  rewrite compose_assoc.
  rewrite cast_compose_eq_mid_join.
  apply compose_simplify_eq; [reflexivity|].
  cast_irrelevance.
  Unshelve. all: lia.
Qed. *)

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

(* @nocheck name *)
Lemma X_0_2_pi_mult_l_to_sum (u v : Matrix 1 2) : WF_Matrix u -> WF_Matrix v -> 
  u ⊗ v × ⟦ X 0 2 PI ⟧ = 
  (u × e_i 1 × (v × e_i 0) .+ v × e_i 1 × (u × e_i 0)).
Proof.
  intros Hu Hv.
  prep_matrix_equivalence.
  rewrite <- 4 matrix_by_basis by lia.
  by_cell.
  cbn;
  unfold kron, hadamard, Mplus; cbn; Csimpl; 
  rewrite Cexp_PI';
  C_field; lca.
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

(* @nocheck name *)
Lemma Mmult_f_to_vec_uniform_state n f : 
  (f_to_vec n f) ⊤%M × ⟦ uniform_state n ⟧ = I 1.
Proof.
  rewrite Mmult_f_to_vec_l_is_get_row by auto_wf.
  prep_matrix_equivalence.
  rewrite uniform_state_semantics.
  by_cell.
  cbn.
  apply make_WF_equiv; [apply funbool_to_nat_bound | lia].
Qed.

Lemma sum_controlizer_state_1_semantics {n} (c0 c1 : ZX 1 n) :
  is_controlled_state c0 -> is_controlled_state c1 -> 
  ⟦ state_1 ⟷ sum_controlizer c0 c1 ⟧ = 
  ⟦ state_1 ⟷ c0 ⟧ .+ ⟦ state_1 ⟷ c1 ⟧.
Proof.
  intros H0 H1.
  unfold is_controlled_state, proportional_by_1 in H0, H1.
  rewrite sum_controlizer_state_1_step1.
  apply equal_on_basis_states_implies_equal_l; [auto_wf..|].
  intros f.
  rewrite zx_compose_spec, <- Mmult_assoc.
  simpl_cast_semantics.
  rewrite Nat.pow_add_r.
  rewrite permed_n_stack_Z_2_1_semantics_f_to_vec_l.
  rewrite 3 zx_compose_spec.
  unify_pows_two.
  rewrite <- Mmult_assoc, (zx_stack_spec 1 n 1 n).
  restore_dims.
  rewrite kron_mixed_product.
  rewrite X_0_2_pi_mult_l_to_sum by auto_wf.
  rewrite 2 (Mmult_assoc _ _ (e_i 0)).
  cbn in H0, H1.
  rewrite state_0_semantics, qubit0_to_ei in H0, H1.
  rewrite H0, H1.
  rewrite Mmult_f_to_vec_uniform_state.
  Msimpl.
  distribute_plus.
  rewrite state_1_semantics, qubit1_to_ei.
  now rewrite 2 Mmult_assoc.
Qed.

Lemma controlizer_state_0 {n m} (zx : ZX n m) : 
  state_0 ⟷ controlizer zx ∝= uniform_state (n + m).
Proof.
  apply zx_is_controlized.
Qed.

Lemma controlizer_state_1 {n m} (zx : ZX n m) :
  state_1 ⟷ controlizer zx ∝= √2 ^ (n + m) .* proc_to_state zx.
Proof.
  pose proof (zx_is_controlized zx) as [_ Hrw]%is_controlized_iff_alt.
  apply Hrw.
Qed.

(* TODO: Other morphism instance (proportionality) *)
Add Parametric Morphism {n m} : (@controlizer n m) with signature
  proportional_by_1 ==> proportional_by_1 as controlizer_mor.
Proof.
  intros zx zx' Hzx.
  apply prop_eq_by_eq_on_states_1_n.
  - now rewrite 2 controlizer_state_0.
  - rewrite 2 controlizer_state_1.
    now rewrite Hzx.
Qed.

(* TODO: Other morphism instance (proportionality) *)
Add Parametric Morphism {n} : (@sum_controlizer n) with signature
  proportional_by_1 ==> proportional_by_1 ==> 
    proportional_by_1 as sum_controlizer_mor.
Proof.
  intros czx0 czx0' Hczx0 czx1 czx1' Hczx1.
  unfold sum_controlizer.
  now rewrite Hczx0, Hczx1.
Qed.



(* TODO: Make state_1 not use zx_scale (but rather zx_invsqrt) internally, 
  so that this can be fully effective (minus the casts, of course...) *)
Definition zx_plus {n m} (zx0 zx1 : ZX n m) : ZX n m :=
  cast 0 0 (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_0_r _)) ((n + m) ⇑ zx_invsqrt2) ↕
  state_to_proc (state_1 ⟷ sum_controlizer (controlizer zx0) (controlizer zx1)).

Lemma zx_plus_defn {n m} (zx0 zx1 : ZX n m) :
  zx_plus zx0 zx1 = 
  cast 0 0 (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_0_r _)) ((n + m) ⇑ zx_invsqrt2) ↕
  state_to_proc (state_1 ⟷ sum_controlizer (controlizer zx0) (controlizer zx1)).
Proof. reflexivity. Qed.

(* We don't want reduction to unfold zx_plus *)
Global Opaque zx_plus.

Notation "zx0 .+ zx1" := (zx_plus zx0 zx1) 
  (at level 50, left associativity) : ZX_scope.

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


(* TODO: Other morphism instance (proportionality) *)
Add Parametric Morphism {n m} : (@zx_plus n m) with signature
  proportional_by_1 ==> proportional_by_1 ==> proportional_by_1 as zx_plus_mor.
Proof.
  intros zx0 zx0' Hzx0 zx1 zx1' Hzx1.
  rewrite 2 zx_plus_defn.
  now rewrite Hzx0, Hzx1.
Qed.



Fixpoint f_to_state n (f : nat -> bool) : ZX 0 n :=
  match n with 
  | 0 => ⦰
  | S n' => state_b (f 0) ↕ f_to_state n' (fun i => f (1 + i))
  end.

Lemma state_b_semantics b : 
  ⟦ state_b b ⟧ = ket (Nat.b2n b).
Proof.
  destruct b.
  - apply state_1_semantics.
  - apply state_0_semantics.
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
  f_to_state (n + m) f ∝= f_to_state n f ↕ f_to_state m (fun i => f (n + i)).
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite 3 f_to_state_semantics.
  now rewrite f_to_vec_split'_eq.
Qed.

Lemma f_to_state_merge n m f g : 
  f_to_state m f ↕ f_to_state n g ∝=
  f_to_state (m + n) (fun x => if x <? m then f x else g (x - m)).
Proof.
  prep_matrix_equivalence.
  cbn.
  rewrite 3 f_to_state_semantics.
  now rewrite f_to_vec_merge.
Qed.

(* NB: Can be made effective using [Z 0 0 PI] for [0] *)
Definition zx_zero {n m} : ZX n m :=
  C0 .* Z n m 0.

Lemma zx_zero_defn n m : zx_zero = C0 .* Z n m 0.
Proof.
  reflexivity.
Qed.

(* Don't unfold zx_zero *)
Global Opaque zx_zero.

Notation "0" := zx_zero : ZX_scope.

Local Open Scope ZX_scope.

Lemma zx_zero_semantics n m : ⟦@zx_zero n m⟧ = Zero.
Proof.
  rewrite zx_zero_defn.
  rewrite zx_scale_semantics.
  apply Mscale_0_l.
Qed.

Lemma zx_scale_0_l {n m} (zx : ZX n m) : 
  C0 .* zx ∝= 0.
Proof.
  prep_matrix_equivalence.
  rewrite zx_scale_semantics, zx_zero_semantics.
  now rewrite Mscale_0_l.
Qed.

Lemma zx_scale_0_r {n m} c : 
  c .* (@zx_zero n m) ∝= 0.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite Cmult_0_r.
Qed.

Lemma stack_0_l {n0 m0 n1 m1} (zx : ZX n1 m1) : 
  (@zx_zero n0 m0) ↕ zx ∝= 0.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

Lemma stack_0_r {n0 m0 n1 m1} (zx : ZX n0 m0) : 
  zx ↕ (@zx_zero n1 m1) ∝= 0.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

Lemma compose_0_l {n m o} (zx : ZX m o) : 
  (@zx_zero n m) ⟷ zx ∝= 0.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

Lemma compose_0_r {n m o} (zx : ZX n m) : 
  zx ⟷ (@zx_zero m o) ∝= 0.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

Lemma cast_0 n m {n' m'} prfn prfm : 
  cast n m prfn prfm (@zx_zero n' m') = 0.
Proof.
  now subst.
Qed.

Lemma n_stack_zx_zero k n m : k <> O ->
  k ⇑ (@zx_zero n m) ∝= 0.
Proof.
  intros H.
  destruct k; [easy|].
  simpl.
  now rewrite stack_0_l.
Qed.

Lemma n_compose_zx_zero k n : k <> O -> 
  n_compose k (@zx_zero n n) ∝= zx_zero.
Proof.
  intros Hk.
  destruct k; [easy|].
  simpl.
  now rewrite compose_0_l.
Qed.

Lemma zx_zero_transpose n m : (@zx_zero n m) ⊤ ∝= 0.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

Lemma zx_zero_adjoint n m : (@zx_zero n m) † ∝= 0.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite Cconj_R, zx_scale_0_l.
Qed.

Lemma zx_zero_colorswap n m : ⊙ (@zx_zero n m) ∝= 0.
Proof.
  rewrite zx_zero_defn.
  distribute_zxscale.
  now rewrite zx_scale_0_l.
Qed.

#[export] Hint Rewrite zx_zero_transpose : transpose_db.
#[export] Hint Rewrite zx_zero_adjoint : adjoint_db.
#[export] Hint Rewrite zx_zero_colorswap : colorswap_db.



Lemma zx_plus_0_l {n m} (zx : ZX n m) : 
  0 .+ zx ∝= zx.
Proof.
  prep_matrix_equivalence.
  rewrite zx_plus_semantics, zx_zero_semantics, Mplus_0_l.
  reflexivity.
Qed.

Lemma zx_plus_0_r {n m} (zx : ZX n m) : 
  zx .+ 0 ∝= zx.
Proof.
  prep_matrix_equivalence.
  rewrite zx_plus_semantics, zx_zero_semantics, Mplus_0_r.
  reflexivity.
Qed.

(* TODO: Other distributivities *)

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

(* TODO: When/if the [Monoid] typeclass in Qlib no longer requires
  leibnix equality, this can be replaced *)
Fixpoint zx_sum {n m} (f : nat -> ZX n m) k : ZX n m :=
  match k with 
  | O => 0
  | 1 => f O
  | S k' => zx_sum f k' .+ f k'
  end.

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


Definition state_of_vector {n} (v : Vector (2^n)) : ZX 0 n :=
  zx_sum (fun i => 
    v i O .* f_to_state n (nat_to_funbool n i)) (2^n).

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

Definition zx_of_matrix {n m} (A : Matrix (2^m) (2^n)) : ZX n m :=
  state_to_proc (state_of_vector 
    (@Mmult _ (2^(n+n)) _ (I (2^n) ⊗ A) (⟦ n_cap n ⟧))).

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


Theorem universality {n m} : forall (A : Matrix (2^m) (2^n)), WF_Matrix A -> 
  exists (zx : ZX n m), ⟦ zx ⟧ = A.
Proof.
  intros A HA.
  exists (zx_of_matrix A).
  now apply zx_of_matrix_semantics.
Qed.







