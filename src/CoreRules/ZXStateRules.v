Require Export CoreData StackComposeRules CoreAutomation 
  StateRules CastRules CapCupRules ZXRules GadgetRules 
  SemanticsComp ScalarSemanticsComp ZXpermFacts.

(** Results about states that use lemmas from ZXRules *)

(* Assorted results about states of Z / X spiders *)

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
  now rewrite <- state_minus_defn.
Qed.

Lemma Z_11_pi_state_minus : state_minus ⟷ Z 1 1 PI ∝= state_plus.
Proof.
  rewrite state_minus_defn.
  distribute_zxscale.
  rewrite Z_spider_1_1_fusion.
  rewrite Z_eq_2_PI by lra.
  now rewrite <- state_plus_defn.
Qed.

Lemma X_11_pi_state_0 : state_0 ⟷ X 1 1 PI ∝= state_1.
Proof.
  colorswap_of Z_11_pi_state_plus.
Qed.

Lemma X_11_pi_state_1 : state_1 ⟷ X 1 1 PI ∝= state_0.
Proof.
  colorswap_of Z_11_pi_state_minus.
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


Lemma Z_1_n_state0 n α : state_0 ⟷ Z 1 n α ∝= 
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

Lemma Z_1_n_state1 n α : state_1 ⟷ Z 1 n α ∝= 
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


Lemma X_1_n_stateplus n α : state_plus ⟷ X 1 n α ∝= 
  cast _ _ (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_1_r _)) (n ⇑ state_plus).
Proof. 
  colorswap_of (Z_1_n_state0 n α).
Qed.

Lemma X_1_n_stateminus n α : state_minus ⟷ X 1 n α ∝= 
  Cexp α .* 
  cast _ _ (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_1_r _)) (n ⇑ state_minus).
Proof.
  colorswap_of (Z_1_n_state1 n α).
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

Lemma X_1_n_state_b {n} α b : 
	state_b b ⟷ X 1 n α ∝= / √2 .* X 0 n (if b then PI + α else α).
Proof.
	destruct b.
	- apply X_1_n_state_1.
	- apply X_1_n_state_0.
Qed.

Lemma Z_1_n_state_plus {n} α : state_plus ⟷ Z 1 n α ∝= /√2 .* Z 0 n α.
Proof.
  colorswap_of (@X_1_n_state_0 n α).
Qed.

Lemma Z_1_n_state_minus {n} α : state_minus ⟷ Z 1 n α ∝= /√2 .* Z 0 n (PI + α).
Proof.
  colorswap_of (@X_1_n_state_1 n α).
Qed.

Lemma Z_1_2_state_0 α : state_0 ⟷ Z 1 2 α ∝= state_0 ↕ state_0.
Proof.
  rewrite Z_1_n_state0.
  simpl.
  rewrite stack_empty_r, 2 cast_id.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma Z_1_2_state_1 α : state_1 ⟷ Z 1 2 α ∝= Cexp α .* (state_1 ↕ state_1).
Proof.
  rewrite Z_1_n_state1.
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


Lemma Z_0_0_to_scalar β : Z 0 0 β ∝= (1 + Cexp β) .* ⦰.
Proof.
  prep_matrix_equivalence; rewrite zx_scale_semantics; 
  by_cell; lca.
Qed.

Lemma X_0_0_to_scalar β : X 0 0 β ∝= (1 + Cexp β) .* ⦰.
Proof. colorswap_of (Z_0_0_to_scalar β). Qed.

  

Lemma X_2_1_states_b b b' α : 
	state_b b ↕ state_b b' ⟷ X 2 1 α ∝=
	/C2 .* X 0 1 (if b ⊕ b' then (α + PI) else α).
Proof.
	rewrite 2 state_b_defn'.
	rewrite gadget_is_scaled_empty, const_of_zx_invsqrt2;
	distribute_zxscale.
	rewrite 2 stack_empty_l.
	cbn.
	distribute_zxscale.
	rewrite <- Cinv_mult_distr, Csqrt2_sqrt, zx_scale_compose_distr_l.
	apply zx_scale_simplify_eq_r.
	rewrite <- (X_add_l 0 0).
	apply X_phase_simplify.
	destruct b, b'; cbn; 
	rewrite 1?Rplus_0_l, 1?Rplus_0_r, 
		2?Cexp_add, 1?Cexp_PI'; lca.
Qed.




(* Results about states of certain other diagrams, such as NOT and □ *)

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
  rewrite X_eq_2_PI by lra.
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
  rewrite X_eq_2_PI by lra.
  now rewrite X_is_wire.
Qed.

Lemma not_state_b b : state_b b ⟷ NOT ∝= state_b (negb b).
Proof.
  destruct b.
  - apply not_state_1.
  - apply not_state_0.
Qed.

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

Lemma not_semantics : ⟦ NOT ⟧ = make_WF (list2D_to_matrix [[C0;C1];[C1;C0]]).
Proof.
  prep_matrix_equivalence.
  rewrite semantics_by_states_1_n.
  rewrite not_state_0, not_state_1.
  rewrite state_0_semantics, state_1_semantics.
  by_cell; reflexivity.
Qed.

(* TODO: Figure out what to do with this *)
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


(* @nocheck name *)
Lemma X_0_2_PI_to_cup_not: X 0 2 PI ∝= ⊂ ⟷ (— ↕ NOT).
Proof.
  (* rewrite cup_pullthrough_bot_1. *)
  rewrite cap_X, not_defn.
  rewrite wire_to_n_wire.
  rewrite (@dominated_X_spider_fusion_bot_left 1 0 1).
  rewrite Rplus_0_r.
  reflexivity.
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



Lemma not_box : NOT ⟷ Box ∝= Box ⟷ Z 1 1 PI.
Proof.
  apply prop_eq_by_eq_on_states_1_n; rewrite <- 2 compose_assoc.
  - rewrite not_state_0, box_state_1, box_state_0, Z_11_pi_state_plus.
    reflexivity.
  - rewrite not_state_1, box_state_1, box_state_0, Z_11_pi_state_minus.
    reflexivity.
Qed.


Lemma not_Z_state_b n β b : 
	state_b b ⟷ NOT ⟷ Z 1 n β ∝=
	(if b then C1 else Cexp β) .* 
  cast _ _ (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_1_r _)) (n ⇑ state_b (negb b)).
Proof.
	destruct b; cbn.
	- now rewrite not_state_1, Z_1_n_state0, zx_scale_1_l.
	- now rewrite not_state_0, Z_1_n_state1.
Qed.

Lemma if_b_not_state_0 (b : bool) : 
	state_0 ⟷ (if b then NOT else —) ∝=
	state_b b.
Proof.
	destruct b.
	- apply not_state_0.
	- apply wire_removal_r.
Qed.

Lemma if_b_not_state_1 (b : bool) : 
	state_1 ⟷ (if b then NOT else —) ∝=
	state_b (negb b).
Proof.
	destruct b.
	- apply not_state_1.
	- apply wire_removal_r.
Qed.

Lemma if_b_not_state_b (b b' : bool) : 
	state_b b' ⟷ (if b then NOT else —) ∝=
	state_b (b' ⊕ b).
Proof.
	destruct b'.
	- apply if_b_not_state_1.
	- rewrite if_b_not_state_0; now destruct b.
Qed.



(* Results about the uniform state *)

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

Lemma cast_uniform_state n n' prf0 prf : 
  cast 0 n' prf0 prf (uniform_state n) = uniform_state n'.
Proof.
  subst; now rewrite cast_id_eq.
Qed.

Lemma uniform_state_split n m : 
  uniform_state (n + m) ∝= uniform_state n ↕ uniform_state m.
Proof.
  unfold uniform_state.
  rewrite nstack_split, cast_contract.
  simpl_casts.
  reflexivity.
  Unshelve. all:lia.
Qed.

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

(* Results about states of triangles, and their interactions with 
  other diagrams *)

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

Lemma Z_1_2_state_b α b : state_b b ⟷ Z 1 2 α ∝= 
  (if b then Cexp α else C1) .* (state_b b ↕ state_b b).
Proof.
  destruct b.
  - now rewrite Z_1_2_state_1.
  - now rewrite Z_1_2_state_0, zx_scale_1_l.
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


Lemma Z_2_1_semantics_f_to_vec_l f :
  (f_to_vec 1 f) ⊤%M × ⟦ Z 2 1 0 ⟧ = 
  (f_to_vec 2 (fun i => f (i / 2)%nat)) ⊤%M.
Proof.
  prep_matrix_equivalence.
  by_cell; cbn; Csimpl; rewrite kron_1_l, 1?Cexp_0 by auto_wf;
  unfold transpose; destruct (f O); cbn; lca.
Qed.

Lemma n_stack_Z_2_1_semantics_f_to_vec_l f k :
  (f_to_vec k f) ⊤%M × ⟦ k ⇑ Z 2 1 0 ⟧ = 
  (f_to_vec (k * 2) (fun i => f (i / 2)))%nat ⊤%M.
Proof.
  revert f;
  induction k; intros f.
  - simpl.
    now Msimpl.
  - change (S k) with (1 + k)%nat. 
    rewrite (f_to_vec_split'_eq 1 k).
    rewrite (kron_transpose' (f_to_vec 1 f) (f_to_vec k _)).
    change ((1 + k) ⇑ ?x) with (x ↕ k ⇑ x).
    change ((1 + k) * 2)%nat with (2 + k * 2)%nat.
    change ((1 + k) * 1)%nat with (1 + k * 1)%nat.
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
    replace i with ((i - 2) + 2)%nat at 2 by lia.
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
  replace (n + n)%nat with (n * 2)%nat by lia.
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

Lemma Z_1_n_state_b b n α : 
  state_b b ⟷ Z 1 n α ∝= 
  (if b then Cexp α else C1) .* 
  cast _ _ (eq_sym (Nat.mul_0_r _)) (eq_sym (Nat.mul_1_r _)) 
  (n ⇑ state_b b).
Proof.
  destruct b.
  - apply Z_1_n_state1.
  - rewrite zx_scale_1_l.
    apply Z_1_n_state0.
Qed.

Lemma box_decomposition_Z_X_Z : □ ∝= 
  (C1 - Ci) / √ 2 .*
  (Z 1 1 (PI/2) ⟷ X 1 1 (PI/2) ⟷ Z 1 1 (PI/2)).
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b0.
  distribute_zxscale.
  rewrite <- 2 compose_assoc.
  rewrite Z_1_n_state_b, n_stack_1'.
  distribute_zxscale.
  rewrite X_1_n_state_b.
  distribute_zxscale.
  apply transpose_diagrams_eq.
  rewrite zx_scale_transpose.
  cbn.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b1.
  distribute_zxscale.
  rewrite <- 2 compose_assoc.
  rewrite Z_1_n_state_b, n_stack_1'.
  distribute_zxscale.
  rewrite X_1_n_state_b, X_0_0_to_scalar.
  distribute_zxscale.
  rewrite (if_dist R R), 3 (if_dist R C).
  rewrite 2 Cexp_add, Cexp_PI', Cexp_PI2.
  prep_matrix_equivalence.
  rewrite zx_scale_semantics.
  cbn.
  rewrite semantics_transpose_comm.
  rewrite 2state_b_semantics.
  by_cell.
  cbn.
  unfold scale.
  destruct b0, b1; cbn; C_field; lca.
Qed.

Lemma box_decomposition_X_Z_X : □ ∝= 
  (C1 - Ci) / √ 2 .*
  (X 1 1 (PI/2) ⟷ Z 1 1 (PI/2) ⟷ X 1 1 (PI/2)).
Proof.
  colorswap_of box_decomposition_Z_X_Z.
Qed.