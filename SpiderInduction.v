Require Import VyZX.ZXCore.
Require Import VyZX.Proportional.

(* Spider Induction *)

(* The first part that is necessary to prove spider edge count induction is the 
   ability to split spiders off to the side. We only need to prove this one, 
   the others follow through transposes *)

Lemma Grow_Z_Left_1 : forall {n} α,
  Z (S (S n)) 1 α ∝ 
  (Z 2 1 0 ↕ nWire n) ⟷ Z (S n) 1 α.
Proof.
  assert ( pow2Pos : forall n, exists m, (2^n = S m)%nat ).
  { induction n;
    [ simpl; exists 0%nat; reflexivity |
      destruct IHn; simpl; rewrite H; exists (S (x + x)); lia ]. }
  assert ( eqb_succ_f : forall j, (j =? S j)%nat = false ).
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
  simpl.
  prop_exists_nonzero 1.
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
  bdestruct (x =? 1)%nat; bdestruct (y =? S (S (S (m + m + (m + m)))))%nat.
  - rewrite H, H0.
    simpl.
    rewrite big_sum_0_bounded by 
      (intros;
      apply Nat.lt_lt_succ_r in H1;
      apply Nat.lt_neq in H1;
      rewrite <- Nat.eqb_neq in H1;
      rewrite H1;
      lca).
    rewrite eqb_succ_f.
    rewrite Cmult_0_l.
    rewrite Nat.eqb_refl.
    rewrite Cplus_0_l.
    unfold kron.
    rewrite div_1_comp.
    rewrite div_3_comp.
    rewrite mod_2_comp.
    rewrite mod_4_comp.
    rewrite Cexp_0.
    unfold I.
    repeat rewrite Nat.eqb_refl.
    rewrite mltSm.
    lca.
  - simpl.
    rewrite H.
    rewrite big_sum_0_bounded by 
      (intros; apply Nat.lt_lt_succ_r in H1;
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
    bdestruct (y / S m =? 3)%nat; bdestruct (m =? y mod S m)%nat; try lca.
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
  Z 1 (S (S n)) α ∝ 
  Z 1 (S n) α ⟷ (Z 1 2 0 ↕ nWire n).
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

