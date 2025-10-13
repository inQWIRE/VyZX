Require Import CoreData.CoreData.

Open Scope ZX_scope.

(* Spider Induction *)

(* The first part that is necessary to prove spider edge count induction is the 
   ability to split spiders off to the side. We only need to prove this one, 
   the others follow through transposes *)

Lemma grow_Z_left_2_1 : forall {n} α,
  Z (S (S n)) 1 α ∝= 
  (Z 2 1 0 ↕ n_wire n) ⟷ Z (S n) 1 α.
Proof.
  assert ( pow2Pos : forall n, exists m, (2^n = S m)%nat ).
  { intros n. 
    enough (2 ^ n <> O)%nat.
    + destruct (2 ^ n)%nat; [easy | eexists; easy].
    + apply Modulus.pow2_nonzero. }
  assert ( eqb_succ_f : forall j, (j =? S j)%nat = false ).
  { intros. Modulus.bdestructΩ'. }
  assert ( div_1_comp : forall i, ((S (i + i) / S i) = 1)%nat).
  { intros.
    rewrite Kronecker.div_eq_iff; lia. }
  assert ( div_3_comp : forall i, 
                        ((S (S (S (i + i + (i + i)))) / S i) = 3)%nat).
  { intros.
    rewrite Kronecker.div_eq_iff; lia. }
  assert ( mod_2_comp : forall i, ((S (i + i)) mod (S i) = i)%nat ).
  { intros. 
    rewrite plus_n_Sm.
    rewrite Modulus.mod_add_n_r.
    apply Nat.mod_small; lia. }
  assert ( mod_4_comp : forall i, 
                        ((S (S (S (i + i + (i + i))))) mod (S i) = i)%nat ).
  { intros. 
    replace (S (S (S (i + i + (i + i))))) 
      with (i + S i + S i + S i)%nat by lia.
    rewrite !Modulus.mod_add_n_r.
    apply Nat.mod_small; lia. }
  intros.
  unfold proportional_by_1.
  simpl.
  rewrite n_wire_semantics.
  unfold Mmult.
  prep_matrix_equality.
  destruct (pow2Pos n) as [m Hm].
  assert (mltSm : (m < S m)%nat) by lia.
  apply Nat.ltb_lt in mltSm.
  unfold Z_semantics.
  simpl.
  rewrite Hm.
  rewrite Nat.add_0_r.
  rewrite <- plus_n_Sm.
  simpl.
  rewrite Nat.add_0_r.
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
        cbn.
        rewrite Nat.sub_diag.
        cbn.
        lca.
      * lca.
      * lca.
    + rewrite big_sum_0; intros; lca.
    + rewrite big_sum_0; intros; lca.
Qed.

Lemma grow_Z_right_1_2 : forall {n} α,
  Z 1 (S (S n)) α ∝= 
  Z 1 (S n) α ⟷ (Z 1 2 0 ↕ n_wire n).
Proof.
  intros.
  replace (Z_Spider 1 (S (S n))%nat α) 
    with ((Z_Spider (S (S n))%nat 1 α)⊤) by reflexivity.
  rewrite grow_Z_left_2_1.
  simpl.
  rewrite n_wire_transpose.
  reflexivity.
Qed.

Lemma grow_Z_right_bot_1_2_base : forall α,
  Z 1 3 α ∝= Z 1 2 α ⟷ (— ↕ Z 1 2 0).
Proof. 
  intros.
  unfold proportional_by_1.
  lma'. 
  unfold Z_semantics, kron;
  cbn.
  rewrite Cexp_0.
  lca.
Qed.

Lemma Z_wrap_over_top_right_base : forall n α,
  (— ↕ Z n 2 α) ⟷ (Cap ↕ —) ∝= Z (S n) 1 α.
Proof.
  intros.
  prep_matrix_equivalence.
  cbn [ZX_semantics].
  rewrite Kronecker.kron_I_l, Kronecker.kron_I_r.
  intros i j Hi Hj.
  unfold Mmult.
  unfold Z_semantics at 2.
  destruct i as [|[]]; [..|cbn in Hi; lia].
  - rewrite Nat.Div0.mod_0_l.
    cbn [Nat.add].
    change (0 =? 2 ^ 1 - 1) with false.
    rewrite andb_false_l.
    destruct j.
    + apply big_sum_unique.
      exists O.
      split; [pose proof (Modulus.pow2_nonzero 3); lia|].
      rewrite !Nat.Div0.div_0_l, !Nat.Div0.mod_0_l, Nat.eqb_refl.
      split; [cbn; destruct n; lca|].
      intros k Hk Hknz.
      destruct k; [easy|].
      do 7 (try destruct k; cbn; [cbn; lca|]).
      cbn in *; lia.
    + apply (@big_sum_0_bounded C).
      intros k Hk.
      rewrite Nat.Div0.div_0_l.
      cbn [Nat.pow Nat.mul Nat.add] in *.
      do 8 (try destruct k); try apply Cmult_0_l; [..|lia];
      rewrite Modulus.if_true by reflexivity.
      * rewrite !Nat.Div0.div_0_l, Nat.Div0.mod_0_l.
        rewrite Nat.eqb_sym.
        Modulus.bdestructΩ'; [|lca].
        rewrite Nat.div_small_iff in * by Modulus.show_nonzero.
        rewrite Nat.mod_small by easy.
        apply Cmult_1_l.
      * change (6 / 4)%nat with 1%nat; change (4 / 2)%nat with 2%nat.
        change (6 mod 4) with (2)%nat.
        Modulus.bdestructΩ'; apply Cmult_0_r.
  - rewrite Nat.eqb_refl, andb_true_l.
    bdestruct (j =? 2 ^ (1 + n) - 1).
    + apply big_sum_unique.
      assert (j / 2 ^ n < 2)%nat by 
        (apply Nat.Div0.div_lt_upper_bound; cbn in *; lia).
      destruct (j / 2 ^ n)%nat as [|one] eqn:e;
      [rewrite Nat.div_small_iff in e; cbn in *; lia|].
      destruct one; [|lia].
      exists 7%nat.
      split; [cbn; lia|].
      rewrite 2!Modulus.if_true by reflexivity.
      change (7 mod 2 ^ 2) with 3%nat.
      rewrite Modulus.mod_n_to_2n by (cbn in *; lia).
      subst j.
      split; [cbn; Modulus.bdestructΩ'; lca|].
      intros k Hk Hk7.
      cbn [Nat.pow Nat.mul Nat.add Nat.sub] in *.
      do 8 (try destruct k); try apply Cmult_0_l; [..|lia];
      rewrite Modulus.if_true by reflexivity; [|easy].
      apply Cmult_0_r.
    + apply (@big_sum_0_bounded C).
      intros k Hk.
      cbn [Nat.pow Nat.mul Nat.add Nat.sub] in *.
      do 8 (try destruct k); try apply Cmult_0_l; [..|lia];
      rewrite Modulus.if_true by reflexivity; rewrite Cmult_1_l; 
      Modulus.bdestructΩ'.
      change (7 mod 4) with 3%nat.
      assert (~ (j < 2 ^ n)%nat) by 
        (rewrite <- Nat.div_small_iff by Modulus.show_nonzero; 
        replace <- (j / 2 ^ n)%nat; easy).
      cbn.
      rewrite Modulus.mod_n_to_2n by lia.
      Modulus.bdestructΩ'.
Qed.

Lemma Z_wrap_over_top_right_0 : forall n α,
  (— ↕ Z n 1 α) ⟷ Cap ∝= Z (S n) 0 α.
Proof.
  intros.
  unfold proportional_by_1.
  cbn.
  unfold Z_semantics, kron, Mmult.
  prep_matrix_equality.
  replace (2 ^ S n)%nat with (2 ^ n + 2 ^ n)%nat by (simpl; lia).
  remember (2 ^ n)%nat as m.
  assert (Hm : (m <> 0)%nat).
  { rewrite Heqm. apply Nat.pow_nonzero. easy. }
  assert (Hm_div : (((m + m - 1) / m) = 1)%nat).
  { 
    replace (m + m - 1)%nat with (1 * m + (m - 1))%nat by lia.
    rewrite Nat.div_add_l by assumption.
    rewrite Nat.div_small by lia.
    lia.
  }
  assert (Hm_mod : ((m + m - 1) mod m = m - 1)%nat).
  { 
    replace (m + m - 1)%nat with (m + (m - 1))%nat by lia.
    rewrite Nat.Div0.add_mod by auto.
    rewrite Nat.Div0.mod_same by auto.
    simpl.
    repeat rewrite Nat.mod_small; lia.
  }
  bdestruct (x =? 0)%nat; bdestruct (y =? m + m - 1)%nat.
  - rewrite H, H0.
    simpl.
    rewrite Hm_mod.
    rewrite Hm_div.
    rewrite Nat.eqb_refl.
    simpl.
    unfold list2D_to_matrix, I.
    simpl.
    Csimpl.
    destruct m; [ contradict Hm; lia | ].
    simpl.
    rewrite <- plus_n_Sm.
    lca.
  - rewrite H.
    simpl.
    unfold list2D_to_matrix, I.
    simpl.
    bdestruct (y / m =? 1)%nat; bdestruct (y mod m =? m - 1)%nat.
    + rewrite H1.
      simpl.
      contradict H0.
      specialize (Nat.div_mod_eq y m); intros.
      rewrite H0.
      rewrite H1, H2.
      lia.
    + rewrite H1.
      Csimpl.
      destruct y; [ contradict H1 | ].
      rewrite Nat.Div0.div_0_l.
      lia.
      lca.
    + destruct (y / m)%nat eqn:E; try lca.
      Csimpl.
      destruct y.
      * rewrite Nat.Div0.mod_0_l.
        destruct n; auto.
      * destruct (S y mod m) eqn:Ey.
        assert (contra : (S y <> 0)%nat) by lia.
        contradict contra.
        specialize (Nat.div_mod_eq (S y) m).
        intros.
        rewrite H3.
        rewrite Ey, E.
        lia.
        lca.
      * Csimpl.
        destruct n0; [ contradict H1; easy | ].
        simpl.
        destruct y; [|lca].
        contradict E.
        rewrite Nat.Div0.div_0_l.
        lia.
    + Csimpl.
      destruct y.
      * rewrite Nat.Div0.div_0_l, Nat.Div0.mod_0_l.
        destruct n; lca.
      * specialize (Nat.div_mod_eq (S y) m); intros.
        destruct (S y / m)%nat, (S y mod m)%nat; try lca.
        lia.
  - destruct x.
    + rewrite H0.
      simpl.
      unfold list2D_to_matrix, I.
      simpl.
      rewrite Hm_div, Hm_mod.
      simpl.
      destruct m; simpl.
      * lia.
      * rewrite Nat.sub_0_r.
        rewrite <- plus_n_Sm.
        rewrite Nat.eqb_refl.
        lca.
    + simpl.
      Csimpl.
      rewrite H0.
      rewrite Hm_div.
      rewrite Hm_mod.
      rewrite Nat.eqb_refl.
      destruct x; lca.
  - rewrite andb_false_r.
    destruct x,y.
    + simpl.
      unfold list2D_to_matrix, I.
      simpl.
      rewrite Nat.Div0.div_0_l, Nat.Div0.mod_0_l; lia.
    + simpl.
      unfold list2D_to_matrix, I.
      simpl.
      Csimpl.
      specialize (Nat.div_mod_eq (S y) m).
      intros.
      bdestruct (S y / m =? 0)%nat; bdestruct (S y mod m =? 0); exfalso; lia.
    + destruct x; lca.
    + destruct x; lca.
Qed.

Lemma Z_wrap_over_top_left_0 : forall n α,
  Cup ⟷ (— ↕ Z 1 n α) ∝= Z 0 (S n) α.
Proof.
  intros.
  apply transpose_diagrams_eq.
  simpl.
  apply Z_wrap_over_top_right_0.
Qed.

(** Inducts on [n] and specializes the case where [n = 1]. Useful for 
  induction on spiders where both the [n = 0] and [n = 1] cases are 
  special, whereas normal induction has only [n = 0] as base case. *)
Ltac spider_induction n := induction n; [ | destruct n ].
