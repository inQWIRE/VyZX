From QuantumLib Require Import Kronecker. 
Require Import CoreData SemanticsComp SwapRules ScalarSemanticsComp ZXStateRules ChoiJamiolchosky.


Lemma is_controlled_state_cast {n m} (zx : ZX 1 n) prf (H : m = n) : 
  is_controlled_state (cast _ _ prf H zx) <->
  is_controlled_state zx.
Proof.
  subst n.
  rewrite cast_id.
  reflexivity.
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

Lemma is_controlized_cast_l {n m n' m'} zx czx (prfn : n = n') (prfm : m = m') : 
  is_controlized (cast _ _ prfn prfm zx) czx <-> 
  is_controlized zx (cast _ _ eq_refl (eq_sym (f_equal2 Nat.add prfn prfm)) czx).
Proof.
  subst.
  now rewrite 2 cast_id_eq.
Qed.


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

Lemma is_controlled_scalar_by_exists c zx : 
  (exists d, is_controlled_scalar d zx /\ d = c) -> 
  is_controlled_scalar c zx.
Proof.
  now intros (? & ? & ->).
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
    rewrite X_0_2_PI_to_cup_not.
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
    rewrite X_eq_2_PI by lra.
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
    rewrite compose_empty_r, left_triangle_state_0, Z_1_n_state0.
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
    rewrite X_eq_2_PI by lra.
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
    rewrite Z_1_n_state0.
    cbn.
    rewrite stack_empty_r, cast_id, (@stack_assoc_back 0 0 0 1 1 1), 2 cast_id.
    rewrite <- (@stack_compose_distr 0 2 0 0 1 4).
    rewrite <- (@stack_compose_distr 0 1 0 0 1 0).
    rewrite <- 2 compose_assoc, left_triangle_state_0, Z_1_n_state0.
    cbn.
    rewrite cast_id, 2 stack_empty_l.
    rewrite <- 2 compose_assoc.
    rewrite <- not_defn, not_state_0.
    rewrite Z_1_n_state1.
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
    rewrite Z_1_n_state1.
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
    rewrite Z_1_n_state0.
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
    rewrite perm_of_zx_of_perm_eq by (change 4%nat with (2*2)%nat; auto_perm).
    by_perm_cell; reflexivity.
  Unshelve. all: lia.
Qed.


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
    rewrite left_triangle_state_0, Z_1_n_state0.
    simpl; rewrite cast_id, stack_empty_l.
    rewrite <- not_defn, not_state_0.
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
    rewrite <- not_defn, not_state_1, left_triangle_state_0.
    rewrite state_0_defn.
    distribute_zxscale.
    simpl.
    rewrite zx_scale_state_to_proc.
    rewrite stack_empty_l, X_spider_1_1_fusion, Rplus_0_l.
    rewrite X_state_to_proc.
    distribute_zxscale.
    rewrite <- zx_scale_1_l at 1.
    apply zx_scale_simplify_eq_l.
    C_field; lca.
  Unshelve. all: reflexivity.
Qed.

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
    rewrite left_triangle_state_0, Z_1_n_state0.
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
    rewrite zx_scale_state_to_proc, X_spider_1_1_fusion, X_state_to_proc.
    distribute_zxscale.
    rewrite <- zx_scale_1_l at 1.
    rewrite (X_eq_2_PI _ _ (_ + _)) by lra.
    apply zx_scale_simplify_eq_l.
    C_field; lca.
  Unshelve. all: reflexivity.
Qed.

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
    rewrite Matrix.transpose_involutive.
    rewrite <- id_transpose_eq, <- kron_transpose.
    restore_dims.
    unify_pows_two.
    rewrite <- Mmult_transpose.
    restore_dims.
    unify_pows_two.
    rewrite (n_cup_matrix_pullthrough_top k 0) by auto_wf.
    rewrite n_cup_0_empty.
    Msimpl.
    rewrite Matrix.transpose_involutive.
    rewrite <- f_to_vec_split'_eq.
    reflexivity.
  Unshelve. all: lia.
Qed.



Lemma wire_is_controlized : 
  is_controlized — wire_controlizer.
Proof.
  rewrite <- box_compose.
  apply compose_is_controlized; apply box_is_controlized.
Qed.

Lemma controlled_half_defn : 
  controlled_half ∝= / C2 .* (▷ ⟷ Z 1 0 0).
Proof.
  unfold controlled_half.
  rewrite (gadget_is_scaled_empty zx_half), 
    const_of_zx_half.
  distribute_zxscale.
  now rewrite stack_empty_l.
Qed. 


Lemma controlled_half_is_controlled_scalar : 
  is_controlled_scalar (/2) controlled_half.
Proof.
  split;
  rewrite controlled_half_defn;
  distribute_zxscale;
  rewrite <- compose_assoc.
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
  rewrite <- controlled_half_defn.
  apply controlled_half_is_controlled_scalar.
Qed.

Lemma two_is_controlized : is_controlized (C2 .* ⦰) two_controlizer.
Proof.
  apply controlled_scalar_is_controlized_scaled_empty.
  unfold two_controlizer.
  unfold is_controlled_scalar.
  rewrite <- 2 compose_assoc.
  rewrite left_triangle_state_0, left_triangle_state_1.
  rewrite Z_1_n_state0, Z_spider_1_1_fusion.
  split; [now rewrite cast_id|].
  rewrite Rplus_0_r, Z_0_0_to_scalar.
  apply zx_scale_simplify_eq_l.
  rewrite Cexp_0; lca.
Qed.

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


Lemma n_stack_is_controlized {n m} k (zx : ZX n m) czx : 
  is_controlized zx czx -> is_controlized (k ⇑ zx) (n_stack_controlizer k czx).
Proof.
  intros Hzx.
  induction k.
  - apply empty_is_controlized.
  - apply (stack_is_controlized _ _ _ _ Hzx IHk).
Qed.

Lemma n_stack1_is_controlized k (zx : ZX 1 1) czx : 
  is_controlized zx czx -> is_controlized (k ↑ zx) (n_stack1_controlizer k czx).
Proof.
  intros Hzx.
  induction k.
  - apply empty_is_controlized.
  - apply (stack_is_controlized _ _ _ _ Hzx IHk).
Qed.

Lemma n_wire_is_controlized n : 
  is_controlized (n_wire n) (n_wire_controlizer n).
Proof.
  apply n_stack1_is_controlized, wire_is_controlized.
Qed.

Lemma X_2_1_is_controlized : 
  is_controlized (X 2 1 0) X_2_1_controlizer.
Proof.
  refine (is_controlized_of_eq_proc_to_state _ _ 
    (eq_refl : (1 + 2 = 2 + 1)%nat) _ _ _ _ 
    (X_1_2_is_controlized)); [|reflexivity].
  cbn.
  rewrite 2 X_proc_to_state.
  reflexivity.
Qed.

Lemma X_0_1_is_controlized β : 
  is_controlized (X 0 1 β) (X_0_1_controlizer β).
Proof.
  refine (is_controlized_of_eq_proc_to_state _ _ 
    (eq_refl : (1 + 0 = 0 + 1)%nat) _ _ _ _ 
    (X_1_0_is_controlized β)); [|reflexivity].
  cbn.
  rewrite 2 X_proc_to_state.
  reflexivity.
Qed.

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

Lemma X_is_controlized n m β : 
  is_controlized (X n m β) (X_controlizer n m β).
Proof.
  refine (is_controlized_of_eq_proc_to_state _ _ 
    (eq_refl : (O + (n + m) = (n + m))%nat) _ _ _ _ 
    (X_0_n_is_controlized (n + m) β)); [|reflexivity].
  cbn.
  now rewrite 2 X_proc_to_state.
Qed.

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
  rewrite cast_compose_r_eq_mid.
  rewrite uniform_state_compose_zx_of_perm_r by
    (cbn; replace (n+n)%nat with (n*2)%nat by lia; auto_perm).
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

Lemma sum_controlizer_state_1_semantics {n} (c0 c1 : ZX 1 n) :
  is_controlled_state c0 -> is_controlled_state c1 -> 
  ⟦ state_1 ⟷ sum_controlizer c0 c1 ⟧ = 
  (⟦ state_1 ⟷ c0 ⟧ .+ ⟦ state_1 ⟷ c1 ⟧)%M.
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
  rewrite X_0_2_PI_mult_l_to_sum by auto_wf.
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

Import Setoid.

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


Add Parametric Morphism {n} : (@sum_controlizer n) with signature
  proportional_by_1 ==> proportional_by_1 ==> 
    proportional_by_1 as sum_controlizer_mor.
Proof.
  intros czx0 czx0' Hczx0 czx1 czx1' Hczx1.
  unfold sum_controlizer.
  now rewrite Hczx0, Hczx1.
Qed.


Add Parametric Morphism {n m} : (@zx_plus n m) with signature
  proportional_by_1 ==> proportional_by_1 ==> proportional_by_1 as zx_plus_mor.
Proof.
  intros zx0 zx0' Hzx0 zx1 zx1' Hzx1.
  rewrite 2 zx_plus_defn.
  now rewrite Hzx0, Hzx1.
Qed.