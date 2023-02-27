Require Import CoreData.CoreData.
Require Import CoreRules.CoreRules.
Require Import Gates.Gates.

Lemma ZX_SWAP_self_inverse : ⨉ ⟷ ⨉ ∝ nWire 2.
Proof.
  intros.
  prop_exists_nonzero 1.
  Msimpl.
  simpl.
  restore_dims.
  rewrite swap_swap.
  rewrite 2 id_kron.
  easy.
Qed.

(* Needs to be diagrammatic *)
Lemma ZX_3_CNOT_SWAP_is_swap : _3_CNOT_SWAP_ ∝ ⨉.
Proof.
Abort.

Lemma nStack_1_nStack : forall {n} (zx : ZX 1 1), (n ↑ zx) ∝ (Cast _ _ (eq_sym (Nat.mul_1_r _)) (eq_sym (Nat.mul_1_r _)) (n ⇑ zx)).
Proof.
  intros.
  unfold eq_rect.
  destruct (Nat.mul_1_r n).
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma nStack_nStack_1 : forall {n} (zx : ZX 1 1), (n ⇑ zx) ∝ (Cast _ _ (Nat.mul_1_r _) (Nat.mul_1_r _) (n ↑ zx)).
Proof.
  intros.
  symmetry.
  unfold eq_sym.
  unfold eq_rect.
  destruct (Nat.mul_1_r n).
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed. 

Lemma nStack1_compose : forall (zx0 zx1 : ZX 1 1) {n}, 
  n ↑ (zx0 ⟷ zx1) ∝ (n ↑ zx0) ⟷ (n ↑ zx1).
Proof.
  intros.
  induction n.
  - unfold nStack1.
    symmetry.
    cleanup_zx.
    reflexivity.
  - simpl.
    rewrite <- (ZX_Stack_Compose_distr zx0 zx1).
    rewrite IHn.
    reflexivity.
Qed. 

Lemma ZX_H_H_is_Wire : □ ⟷ □ ∝ —.
Proof.
  prop_exists_nonzero 1.
  simpl.
  rewrite MmultHH.
  lma.
Qed.

Lemma nH_composition : forall {n}, 
  (n ↑ □) ⟷ (n ↑ □) ∝ n ↑ —.
Proof.
  intros.
  rewrite <- nStack1_compose.
  rewrite ZX_H_H_is_Wire.
  reflexivity.
Qed.

Theorem trivial_cap_cup : 
  ⊂ ⟷ ⊃ ∝ ⦰.
Proof. solve_prop 2. Qed.

Lemma Cap_passthrough : forall (zx : ZX 1 1),  
  (⊂ ⟷ (zx ↕ —)) ∝ (⊂ ⟷ (— ↕ zx⊤)).
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  rewrite ZX_semantics_transpose_comm.
  Msimpl; simpl.
  unfold kron, Mmult, I, list2D_to_matrix, Matrix.transpose.
  prep_matrix_equality.
  do 4 (try destruct x); do 4 (try destruct y).
  all: C_field_simplify; try lca.
  assert ((S (S (S (S x))) / 2 <? 2) = false)%nat.
  {
    apply Nat.ltb_ge.
    replace (S (S (S (S x))))%nat with (2 * 2 + x)%nat by lia.
    rewrite Nat.div_add_l.
    apply Nat.le_add_r.
    easy.
  }
  rewrite 2 big_sum_0; auto; intros.
  - rewrite H.
    rewrite andb_false_r.
    lca.
  - rewrite WF_ZX; try lca.
    left.
    apply Nat.ltb_ge.
    apply H.
Qed.

Lemma Cup_passthrough : forall (zx : ZX 1 1),
  (zx ↕ —) ⟷ ⊃ ∝ (— ↕ zx⊤) ⟷ ⊃.
Proof. transpose_of Cap_passthrough. Qed.

Lemma Swap_passthrough_1_1 : forall (zx0 : ZX 1 1) (zx1 : ZX 1 1),
  (zx0 ↕ zx1) ⟷ ⨉ ∝ ⨉ ⟷ (zx1 ↕ zx0).
Proof.
  intros.
  prop_exists_nonzero 1.
  Msimpl; simpl.
  solve_matrix.
  all: rewrite WF_ZX; try lca.
  1-4: left; auto.
  5,7,9,11: right; auto.
  1-4: left.
  5-8: right.
  all: simpl;
       apply le_n_S;
       apply le_n_S;
       apply Nat.le_0_l.
Qed.

Lemma Z_commutes_through_swap_t : forall α, 
  ((Z_Spider 1 1 α) ↕ —) ⟷ ⨉ ∝ 
  ⨉ ⟷ (— ↕ (Z_Spider 1 1 α)).
Proof.
  intros.
  rewrite Swap_passthrough_1_1.
  easy.
Qed.  

Lemma Spiders_commute_through_swap_b : forall (zx0 zx1 : ZX 1 1),
  (— ↕ zx0) ⟷ ⨉ ∝ ⨉ ⟷ (zx0 ↕ —) ->      
  (— ↕ zx1) ⟷ ⨉ ∝ ⨉ ⟷ (zx1 ↕ —) ->
  (— ↕ (zx0 ⟷ zx1)) ⟷ ⨉ ∝ ⨉ ⟷ ((zx0 ⟷ zx1) ↕ —).
Proof.
  intros.
  rewrite Swap_passthrough_1_1.
  reflexivity.
Qed.

Lemma Spiders_commute_through_swap_t : forall (zx0 zx1 : ZX 1 1),
  (zx0 ↕ —) ⟷ ⨉ ∝ ⨉ ⟷ (— ↕ zx0) ->      
  (zx1 ↕ —) ⟷ ⨉ ∝ ⨉ ⟷ (— ↕ zx1) ->
  ((zx0 ⟷ zx1) ↕ —) ⟷ ⨉ ∝ ⨉ ⟷ (— ↕ (zx0 ⟷ zx1)).
Proof.
  intros.
  rewrite Swap_passthrough_1_1.
  reflexivity.
Qed.

Lemma nBox_passthrough :forall {nIn nOut} (zx : ZX nIn nOut),
  (nBox nIn) ⟷ zx ∝ (⊙ zx ⟷ (nBox nOut)).
Proof.
  intros.
  prop_exists_nonzero 1.
  Msimpl.
  simpl.
  rewrite ZX_semantics_Colorswap_comm.
  rewrite 2 nBox_semantics.
  rewrite Mmult_assoc.
  rewrite <- Mmult_assoc.
  rewrite kron_n_mult.
  rewrite MmultHH.
  rewrite kron_n_I.
  rewrite Mmult_1_l by auto with wf_db.
  easy.
Qed.

Lemma Z_Spider_angle_2PI : forall {nIn nOut} α k, Z_Spider nIn nOut α ∝ (Z_Spider nIn nOut (α + IZR (2 * k) * PI)).
Proof.
  intros.
  prop_exists_nonzero 1.
  unfold ZX_semantics, Z_semantics.
  rewrite Cexp_add.
  rewrite Cexp_2nPI.
  rewrite Cmult_1_r.
  Msimpl.
  reflexivity.
Qed.

Lemma X_Spider_angle_2PI : forall {nIn nOut} α k, X_Spider nIn nOut α ∝ (X_Spider nIn nOut (α + IZR (2 * k) * PI)).
Proof. intros. colorswap_of (@Z_Spider_angle_2PI nIn nOut). Qed.
