From VyZX Require Export ZXCore.
From VyZX Require Import SemanticCore.
From VyZX Require Export Proportional.

Local Open Scope ZX_scope.

(* Associativity *)

Lemma ZX_Compose_assoc : forall {nIn nMid1 nMid2 nOut}
  (zx1 : ZX nIn nMid1) (zx2 : ZX nMid1 nMid2) (zx3 : ZX nMid2 nOut),
  zx1 ⟷ zx2 ⟷ zx3 ∝ zx1 ⟷ (zx2 ⟷ zx3).
Proof.
  intros.
  prep_proportional.
  prop_exist_non_zero 1.
  simpl.
  Msimpl.
  rewrite Mmult_assoc.
  lma.
Qed.

Lemma ZX_Stack_assoc : 
  forall {nIn1 nIn2 nIn3 nOut1 nOut2 nOut3}
    (zx1 : ZX nIn1 nOut1) (zx2 : ZX nIn2 nOut2) (zx3 : ZX nIn3 nOut3),
    (zx1 ↕ zx2) ↕ zx3 ∝ zx1 ↕ (zx2 ↕ zx3).
Proof.
  intros.
  prep_proportional.
  prop_exist_non_zero 1.  
  simpl.
  Msimpl.
  rewrite kron_assoc; auto with wf_db.
Qed.

(* Distributivity *)

Lemma ZX_Stack_Compose_distr : 
  forall {nIn1 nMid12 nIn3 nOut2 nMid34 nOut4}
    (zx1 : ZX nIn1 nMid12) (zx2 : ZX nMid12 nOut2) (zx3 : ZX nIn3 nMid34) (zx4 : ZX nMid34 nOut4),
    (zx1 ⟷ zx2) ↕ (zx3 ⟷ zx4) ∝ (zx1 ↕ zx3) ⟷ (zx2 ↕ zx4).
Proof.
  intros.
  prep_proportional.
  prop_exist_non_zero 1.

  Msimpl.
  unfold Compose.
  simpl.
Admitted.
  (* apply kron_mixed_product.
  reflexivity.
Qed. *)

(* Empty diagram removal *)

Lemma ZX_Stack_Empty_l : forall {nIn nOut} (zx : ZX nIn nOut),
  ⦰ ↕ zx ∝ zx.
Proof.
  intros.
  prep_proportional.
  prop_exist_non_zero 1.
  simpl.
  rewrite kron_1_l; try auto with wf_db.
  lma.
Qed.

Lemma ZX_Stack_Empty_r : forall {nIn nOut : nat} (zx : ZX nIn nOut),
  zx ↕ ⦰ ∝ zx.
Proof.
  intros.
  prep_proportional.
  prop_exist_non_zero 1.
  simpl.
  Msimpl.
  reflexivity.
Qed.

Lemma ZX_Compose_Empty_r : forall {nIn} (zx : ZX nIn 0),
  zx ⟷ ⦰ ∝ zx.
Proof. 
  intros.
  prep_proportional.
  prop_exist_non_zero 1.
  simpl.
  Msimpl.
  reflexivity.
Qed.
  
Lemma ZX_Compose_Empty_l : forall {nOut} (zx : ZX 0 nOut),
  ⦰ ⟷ zx ∝ zx.
Proof. 
  intros.
  prep_proportional.
  prop_exist_non_zero 1.
  simpl. 
  Msimpl.
  reflexivity.
Qed.

(* Automation *)

#[export] Hint Rewrite 
  (fun n => @ZX_Compose_Empty_l n)
  (fun n => @ZX_Compose_Empty_r n)
  (fun n => @ZX_Stack_Empty_l n)
  (fun n => @ZX_Stack_Empty_r n) : remove_empty_db.

Ltac remove_empty := autorewrite with remove_empty_db.

(* Spider Induction *)

(* The first part that is necessary to prove spider edge count induction is the 
   ability to split spiders off to the side. We only need to prove this one, 
   the others follow through transposes *)

Lemma Grow_Z_Left_1 : forall {n} α,
  Z_Spider (S (S n)) 1 α ∝ ((Z_Spider 2 1 0) ↕ (nWire n)) ⟷ (Z_Spider (S n) 1 α).
Proof.
  assert ( pow2Pos : forall n, exists m, (2^n = S m)%nat ).
  { induction n;
    [ simpl; exists 0%nat; reflexivity |
      destruct IHn; simpl; rewrite H; exists (S (x + x)); lia ]. }
  assert ( eqb_succ_f : forall j, j =? S j = false ).
  { induction j; auto. }
  assert ( div_1_comp : forall i, ((S (i + i) / S i) = 1)%nat).
  { intros.
    replace (S (i + i))%nat with (2 * (S i) - 1)%nat by lia.
    assert (S i <> 0)%nat by easy.
    assert (2 * S i - 1 < S i * 2)%nat by lia.
    specialize (Nat.div_lt_upper_bound (2 * S i - 1) (S i) (2) H H0).
    intros.
    assert (0 < S i <= 2 * S i - 1)%nat by lia.
    specialize (Nat.div_str_pos (2 * S i - 1) (S i) H2).
    intros.
    destruct((2 * S i - 1) / S i)%nat.
    - contradict H3; lia.
    - destruct n; auto.
      contradict H1; lia. }
  assert ( div_3_comp : forall i, ((S (S (S (i + i + (i + i)))) / S i) = 3)%nat).
  { intros.
    replace (S (S (S (i + i + (i + i)))))%nat with (4 * (S i) - 1)%nat by lia.
    assert (S i <> 0)%nat by easy.
    assert (4 * S i - 1 < S i * 4)%nat by lia.
    specialize (Nat.div_lt_upper_bound (4 * S i - 1) (S i) (4) H H0).
    intros.
    assert (S i * 3 <= 4 * S i - 1)%nat by lia.
    specialize (Nat.div_le_lower_bound (4 * S i - 1) (S i) 3 H H2).
    intros.
    destruct ((4 * S i - 1) / S i)%nat; [ contradict H3; lia | ];
    destruct n; [ contradict H3; lia | ];
    destruct n; [ contradict H3; lia | ];
    destruct n; [ auto | contradict H1; lia ]. }
  assert ( mod_2_comp : forall i, ((S (i + i)) mod (S i) = i)%nat ).
  { intros. 
    rewrite plus_n_Sm.
    rewrite Nat.add_mod by lia.
    rewrite Nat.mod_same by lia.
    rewrite plus_0_r.
    rewrite Nat.mod_mod by lia.
    apply Nat.mod_small; lia. }
  assert ( mod_4_comp : forall i, ((S (S (S (i + i + (i + i))))) mod (S i) = i)%nat ).
  { intros. 
    replace (S (S (S (i + i + (i + i))))) with ((S i) + ((S i) + ((S i) + i)))%nat by lia.
    repeat (rewrite Nat.add_mod by lia;
            rewrite Nat.mod_same by lia;
            rewrite plus_0_l).
    repeat rewrite Nat.mod_mod by lia.
    apply Nat.mod_small; lia. }
  intros.
  prep_proportional.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  rewrite nWire_semantics.
  unfold Mmult.
  prep_matrix_equality.
  destruct (pow2Pos n) as [m Hm].
  assert (mltSm : (m < S m)%nat) by lia.
  apply Nat.ltb_lt in mltSm.
  unfold Z_semantics.
  simpl.
  rewrite Hm.
  rewrite plus_0_r.
  rewrite <- plus_n_Sm.
  simpl.
  rewrite plus_0_r.
  repeat rewrite <- plus_n_Sm.
  bdestruct (x =? 1); bdestruct (y =? S (S (S (m + m + (m + m))))).
  - rewrite H, H0.
    simpl.
    rewrite big_sum_0_bounded by (
      intros; apply Nat.lt_lt_succ_r in H1;
      apply Nat.lt_neq in H1;
      rewrite <- Nat.eqb_neq in H1;
      rewrite H1;
      lca).
    rewrite eqb_succ_f.
    rewrite Nat.eqb_refl.
    C_field_simplify.
    unfold kron.
    rewrite div_1_comp, div_3_comp, mod_2_comp, mod_4_comp.
    unfold I; simpl.
    rewrite Nat.eqb_refl.
    rewrite mltSm.
    rewrite Cexp_0.
    lca.
  - simpl.
    rewrite H.
    rewrite big_sum_0_bounded by (
      intros; apply Nat.lt_lt_succ_r in H1;
      apply Nat.lt_neq in H1;
      rewrite <- Nat.eqb_neq in H1;
      rewrite H1;
      lca).
    rewrite eqb_succ_f.
    rewrite Nat.eqb_refl.
    C_field_simplify.
    unfold kron.
    rewrite div_1_comp.
    rewrite Nat.eqb_refl.
    rewrite mod_2_comp.
    unfold I.
    bdestruct (y / S m =? 3); bdestruct (m =? y mod S m); try lca.
    contradict H0.
    rewrite (Nat.div_mod_eq y (S m)).
    rewrite H1, <- H2; lia.
  - simpl.
    rewrite H0.
    unfold kron.
    unfold I.
    rewrite div_1_comp, div_3_comp, mod_2_comp, mod_4_comp.
    repeat rewrite Nat.eqb_refl.
    rewrite big_sum_0_bounded. 
    + rewrite mltSm.
      destruct x; [ | lca ].
      destruct m; lca.
    + intros.
      destruct x, x0; lca.
  - simpl.
    unfold kron, I.
    rewrite div_1_comp, mod_2_comp.
    destruct x,y,m; try lca.
    + repeat rewrite Cmult_0_l.
      replace (S m + S m)%nat with (S (S (m + m)))%nat by lia.
      rewrite <- big_sum_extend_l.
      simpl.
      repeat rewrite Nat.sub_diag.
      simpl.
      rewrite big_sum_0; intros; lca.
    + rewrite Cmult_0_l.
      rewrite Nat.div_1_r.
      lca.
    + rewrite big_sum_0; try lca.
      intros.
      destruct x,y.
      * simpl.
        rewrite Nat.sub_diag.
        replace (match m with
           | 0 => S m
           | S l => m - l
           end)%nat with 1%nat by (destruct m; lia).
        lca.
      * destruct (S (S y) / (S (S m)))%nat eqn:E; try lca.
        rewrite Nat.div_small_iff in E by auto.
        rewrite (Nat.mod_small (S (S y))) by auto.
        repeat rewrite Nat.mod_0_l by auto.
        lca.
      * lca.
      * lca.
    + rewrite big_sum_0; intros; lca.
    + rewrite big_sum_0; intros; lca.
Qed.

Lemma Grow_Z_Right_1 : forall {n} α,
  Z_Spider 1 (S (S n)) α ∝ (Z_Spider 1 (S n) α) ⟷ ((Z_Spider 1 2 0) ↕ (n ↑ Wire)).
Proof.
  intros.
  replace (Z_Spider 1 (S (S n))%nat α) with ((Z_Spider (S (S n))%nat 1 α)⊤) by reflexivity.
  rewrite Grow_Z_Left_1.
  simpl.
  unfold nWire.
  rewrite nstack1_transpose.
  rewrite transpose_wire.
  reflexivity.
Qed.


Lemma WrapOver : forall n m α,
  Z (S n) m α ∝ (Wire ↕ Z n (S m) α) ⟷ (Cup ↕ nWire m).
Proof.
  intros.
  prep_proportional.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  rewrite nWire_semantics.
Admitted.

Lemma SpiderFusion : forall t m b α β,
  @Sequence _ _ _ _ (Nat.add_assoc _ _ _) (nWire t ↕ Z ((S m) + b) ((S m) + b) α) (Z (t + (S m)) (t + (S m)) β ↕ nWire b) ∝
  Z (t + (S m) + b) (t + (S m) + b) (α + β)%R.
Proof.
  intros.
  prep_proportional.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  repeat rewrite nWire_semantics.
  prep_matrix_equality.
  bdestruct (x =? 0); bdestruct (y =? 0).
  - simpl. 
    unfold Mmult, kron; simpl.
    rewrite H, H0.
    simpl.
    rewrite <- plus_n_Sm.
    simpl.
    repeat rewrite Nat.mod_0_l by (apply Nat.pow_nonzero; auto).
    repeat rewrite Nat.div_0_l by (apply Nat.pow_nonzero; auto).
    repeat rewrite plus_0_r.
    destruct (2 ^ (t + m + b))%nat eqn:E; [ contradict E; apply Nat.pow_nonzero; easy | ].
    repeat rewrite Nat.mod_0_l by (apply Nat.pow_nonzero; auto).
    simpl.
    repeat rewrite Nat.mod_0_l by (apply Nat.pow_nonzero; auto).
    repeat rewrite Nat.mod_0_l by (apply Nat.pow_nonzero; auto).
    rewrite <- big_sum_extend_l.
  - simpl.
  

