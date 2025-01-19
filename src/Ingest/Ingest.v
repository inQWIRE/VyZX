Require Import SQIR.UnitarySem.
Require Import SQIR.Equivalences.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Kronecker.
Require Import CoreData.
Require Import CoreRules.
Require Import Gates.
Require Import ZXPad.


Local Open Scope ZX_scope.

(* Conversion  to base ZX diagrams *)

(* Proving correctness of conversion *)

Lemma a_swap_sem_base : forall n, a_swap_semantics (S (S n)) = uc_eval (@SWAP (S (S n)) 0 (S n)).
Proof.
  intros.
  assert (forall (q q' : Vector 2), WF_Matrix q -> WF_Matrix q' -> 
    swap × (I 2 ⊗ (q × q'†%M)) × swap = (q × q'†%M) ⊗ I 2).
  {
    intros.
    rewrite swap_eq_kron_comm.
    rewrite Kronecker.kron_comm_commutes_l by auto_wf.
    rewrite Mmult_assoc, Kronecker.kron_comm_mul_inv.
    apply Mmult_1_r; auto_wf.
  }
  induction n.
  - simpl.
    rewrite denote_swap.
    unfold ueval_swap.
    simpl.
    rewrite !kron_1_r.
    unfold Swaps.bottom_wire_to_top.
    unfold Swaps.top_wire_to_bottom.
    rewrite unfold_pad.
    simpl.
    rewrite id_kron.
    rewrite Mmult_transpose.
    rewrite id_transpose_eq.
    rewrite kron_1_r.
    replace 4%nat with (2 * 2)%nat by lia.
    rewrite swap_transpose.
    rewrite Mmult_1_l, Mmult_1_r, kron_1_l, kron_1_r by auto_wf.
    apply swap_spec'.
  - rewrite a_swap_semantics_ind.
    rewrite IHn.
    (* simpl. *)
    rewrite 2 denote_swap.
    unfold ueval_swap.
    cbn [Nat.ltb Nat.leb].
    
    rewrite Nat.sub_0_r.
    rewrite 2 unfold_pad.
    replace (S n - 1)%nat with (n)%nat by lia.
    replace (0 + (1 + n + 1))%nat with (S (S n)) by lia.
    replace ((0 + (1 + (S (S n) - 0 - 1) + 1)))%nat with (S (S (S n))) by lia.
    rewrite 2!Nat.leb_refl.
    rewrite 2!Nat.sub_diag.
    change (2^0)%nat with (S O).
    replace (S (S n) - 0 - 1)%nat with (S n) by lia.
    cbn -[Nat.pow].
    (* rewrite kron_1_l by (auto 100 using WF_Matrix_dim_change with wf_db). auto_wf.
    Msimpl. *)
    restore_dims.
    replace (0 <=? n) with true by easy.
    Msimpl.
    replace (2 ^ S n)%nat with (2 * 2 ^ n)%nat by (cbn; lia).
    (* rewrite <- id_kron, <- kron_assoc by auto_wf. *)
    (* restore_dims. *)
    rewrite !(kron_assoc _ (I (2^n))) by auto_wf.
    restore_dims.
    distribute_plus.
    rewrite <- !(kron_assoc (I 2)) by auto_wf.
    restore_dims.
    rewrite !kron_mixed_product' by lia.
    rewrite swap_eq_kron_comm.
    rewrite !kron_comm_commutes_l by auto_wf.
    rewrite !(Mmult_assoc _ (kron_comm 2 2)).
    rewrite kron_comm_mul_inv.
    Msimpl.
    rewrite <- id_kron.
    rewrite !kron_assoc by auto_wf.
    restore_dims.
    easy. 
Qed.

Lemma uc_eval_swap_grow : forall n x y, (x < (S (S n)))%nat -> (y < x)%nat ->
uc_eval (@SWAP (S (S n)) x y) = I (2 ^ y) ⊗ uc_eval (@SWAP (S x - y) 0 (x - y)) ⊗ I (2 ^ (S (S n) - (S x))).
Proof.
  intros.
  rewrite denote_swap.
  unfold ueval_swap.
  bdestruct (x <? y); try lia. 
  bdestruct (y <? x); try lia.
  rewrite unfold_pad.
  simpl.
  assert (exists c, x - y = S c)%nat.
  {
    destruct (x - y)%nat eqn:Hcontra; [ | eauto ].
    contradict Hcontra.
    apply Nat.sub_gt; easy.
  }
  destruct H3.
  rewrite H3.
  rewrite Sn_minus_1.
  rewrite Nat.add_1_r.
  rewrite <- H3.
  rewrite <- (Nat.sub_succ_l y x); try lia.
  replace (y + (S x - y))%nat with (S x) by lia.
  assert (Htriv : (S x <= S (S n))%nat) by lia.
  bdestruct (S x <=? S (S n)); try (exfalso; lia).
  clear H4 Htriv.
  rewrite denote_swap.
  unfold ueval_swap.
  bdestruct (0 <? x - y); try (exfalso; lia).
  rewrite unfold_pad.
  simpl.
  destruct y.
  - repeat rewrite Nat.sub_0_r.
    rewrite Nat.sub_0_r in H3.
    rewrite H3.
    rewrite Sn_minus_1.
    rewrite Nat.add_1_r.
    rewrite Nat.leb_refl.
    Msimpl.
    replace (S (S x0) - S (S x0))%nat with 0%nat by lia.
    replace ((2 ^ 0 * (1 * (2 * 2 ^ x0 * 2) * 2 ^ 0))%nat) 
      with (2 ^ 0 * (2 * 2 ^ x0 * 2))%nat by (simpl; lia).
    apply kron_simplify; try easy.
    rewrite kron_1_r.
    easy.
  - destruct x; try (exfalso; lia).
    destruct (S x - y)%nat eqn:Hc; try (exfalso; lia).
    rewrite Nat.sub_0_r.
    replace (S x - S y - 1 + 1)%nat with (S x - S y)%nat by lia.
    replace (S x - S y)%nat with n0 by lia.
    rewrite Nat.leb_refl.
    restore_dims.
    rewrite kron_1_l by auto_wf.
    assert (x - y = S x0)%nat by lia.
    assert (x - y = n0)%nat by lia.
    replace (2 ^ S y * (1 * (2 * 2 ^ (n0 - 1) * 2) * 2 ^ (S n0 - S n0)))%nat 
      with (2 ^ S y * (2 * 2 ^ x0 * 2))%nat; [ | shelve ].
    apply kron_simplify; try easy.
    rewrite Nat.sub_diag.
    rewrite kron_1_r.
    restore_dims.
    replace ((2 * 2 ^ (n0 - 1) * 2)%nat) 
      with (2 * 2 ^ x0 * 2)%nat; [ | shelve ].
    apply kron_simplify; try easy.
    rewrite <- H6.
    rewrite H5.
    rewrite Sn_minus_1.
    easy.
Unshelve.
  all: rewrite <- H6; rewrite H5; rewrite Sn_minus_1.
  1: rewrite Nat.sub_diag.
  all: simpl; lia.
Qed.

Lemma cnot_dim_conv : forall n m dim, (n <? m = true) -> (m <? dim = true) -> dim = (n + (m - n) + (dim - m))%nat.
Proof.
  intros.
  rewrite (Nat.add_comm n (m - n)).
  rewrite (Nat.sub_add n m).
  rewrite Nat.add_comm.
  rewrite Nat.sub_add.
  easy.
  all: bdestruct (n <? m); try (exfalso; lia);
  bdestruct (m <? dim); try (exfalso; lia). 
  all: apply Nat.lt_le_incl; easy.
Qed.

Lemma cast_dim_conv : forall n, (1 <? n%nat = true) -> (n = 2 + (n - 2))%nat.
Proof.
  intros.
  assert (n >= 2)%nat.
  { 
    apply leb_complete in H; lia.
  }
  lia.
Qed.

Lemma add_2_r : forall n, (S (S n)) = (n + 2)%nat.
Proof. intros. lia. Qed.

Lemma add_2_l : forall n, (S (S n)) = (2 + n)%nat.
Proof. intros. lia. Qed.

Definition base_cnot n0 (cnot : ZX 2 2) : ZX (S (S n0)) (S (S n0)).
Proof.
  apply (@Compose _ (S (S n0)) _).
  apply (@Compose _ (S (S n0)) _).
  * apply pad_bot_1.
    apply a_swap.
  * apply (cast _ _ (add_2_r n0) (add_2_r n0)). 
    apply (pad_top n0).
    apply cnot.
  * apply pad_bot_1.
    apply a_swap.
Defined.

Definition base_cnot_1 n0 (cnot : ZX 2 2) : ZX (S (S n0)) (S (S n0)).
Proof.
  apply (@Compose _ (S (S n0)) _).
  apply (@Compose _ (S (S n0)) _).
  * apply (pad_top 1).
    apply a_swap.
  * apply (cast _ _ (add_2_l n0) (add_2_l n0)).
    apply (pad_bot n0).
    apply cnot.
  * apply (pad_top 1).
    apply a_swap.
Defined.

Definition unpadded_cnot (base_cnot : forall n0 : nat, ZX 2 2 -> ZX (S (S n0)) (S (S n0))) (cnot : ZX 2 2) (n m : nat) : ZX (m - n) (m - n) :=
  match (m - n)%nat with
  | S (S (S n0)) => base_cnot (S n0) cnot
  | 2%nat => cnot
  | 1%nat => —
  | 0%nat => ⦰
  end.

Lemma swap_pad : forall n, uc_eval (@SWAP (S (S n)) 0 n) = uc_eval (@SWAP (S n) 0 n) ⊗ I 2.
Proof.
  intros.
  rewrite 2 denote_swap_alt.
  unfold pad_swap.
  unfold pad_ctrl.
  bdestruct (0 <? n).
  - bdestruct (n <? 0); try (exfalso; lia).
    repeat rewrite unfold_pad.
    simpl.
    replace (n - 0 - 1 + 1)%nat with n by lia.
    bdestruct (n <=? S n); try (exfalso; lia).
    destruct n; try (exfalso; lia).
    replace (S n - 0 - 1)%nat with (n) by lia.
    replace (S n - n)%nat with 1%nat by lia.
    simpl.
    rewrite Nat.leb_refl.
    rewrite Nat.sub_diag.
    rewrite !kron_1_r.
    restore_dims.
    rewrite 2!(kron_id_dist_r 2) by auto_wf.
    easy.
  - destruct n; try (exfalso; lia).
    bdestruct (0 <? 0); try (exfalso; lia).
    lma.
Qed.

Lemma swap_pad' : forall n, uc_eval (@SWAP (S (S n)) (S n) 1) = (I 2) ⊗ uc_eval (@SWAP (S n) n 0).
Proof.
  intros.
  rewrite 2 denote_swap_alt.
  unfold pad_swap.
  unfold pad_ctrl.
  bdestruct (S n <? 1); try (exfalso; lia).
  bdestruct (1 <? S n); try (exfalso; lia).
  bdestruct (0 <? n);
  bdestruct (n <? 0); try (exfalso; lia).
  - repeat rewrite unfold_pad.
    simpl.
    replace (n - 0 - 1 + 1)%nat with n by lia.
    bdestruct (n <=? n); try (exfalso; lia).
    destruct n; try (exfalso; lia).
    replace (S n - 0 - 1)%nat with (n) by lia.
    replace (S n - n)%nat with 1%nat by lia.
    (* simpl. *)
    rewrite Nat.sub_diag.
    restore_dims.
    (* simpl. *)
    rewrite !kron_1_l by auto_wf.
    Msimpl.
    restore_dims.
    rewrite 2 kron_id_dist_l; auto with wf_db.
  - destruct n; try (exfalso; lia).
    bdestruct (0 <? 0); try (exfalso; lia).
    lma.
Qed.

Lemma unpadded_cnot_simpl_args_sem : forall n m cnot base_cnot, ⟦ unpadded_cnot base_cnot cnot 0 (m - n ) ⟧ = ⟦ unpadded_cnot base_cnot cnot n m ⟧.
Proof.
  intros.
  unfold unpadded_cnot.
  rewrite Nat.sub_0_r; simpl_casts.
  destruct (m - n)%nat; [ easy | ].
  destruct n0; easy.
Qed.

Lemma unpadded_cnot_simpl_args : forall n m cnot base_cnot, (unpadded_cnot base_cnot cnot 0 (m - n)) ∝= cast _ _ (Nat.sub_0_r _) (Nat.sub_0_r _) (unpadded_cnot base_cnot cnot n m).
Proof.
  intros.
  hnf; Msimpl.
  simpl_cast_semantics.
  apply unpadded_cnot_simpl_args_sem.
Qed.

Notation unpadded_cnot_t := (unpadded_cnot base_cnot _CNOT_).
Notation unpadded_cnot_b := (unpadded_cnot base_cnot_1 _CNOT_inv_).

Lemma unpadded_cnot_t_sem_equiv : forall n, / (√ 2)%R .* uc_eval (@CNOT (S (S n)) 0 (S n)) = ⟦ unpadded_cnot_t 0 (S (S n)) ⟧.
Proof.
  intros.
  assert (HSwapSSn : forall n, uc_eval (@SWAP (S (S (S n))) 0 (S n)) = ⟦ (pad_bot_1 (a_swap (S (S n)))) ⟧ ).
  {
    intros.
    unfold pad_bot_1, pad_bot.
    rewrite swap_pad.
    cbn -[a_swap].
    restore_dims.
    simpl_cast_semantics.
    cbn -[a_swap].
    rewrite a_swap_correct.
    rewrite a_swap_sem_base.
    Msimpl.
    easy.
  }
  destruct n.
  - unfold unpadded_cnot.
    pose proof cnot_l_is_cnot.
    simpl; simpl in H.
    rewrite H.
    rewrite denote_cnot.
    rewrite unfold_ueval_cnot.
    simpl.
    rewrite unfold_pad.
    simpl.
    Msimpl.
    rewrite <- cnot_decomposition.
    apply Mscale_simplify; easy.
  - rewrite <- (SWAP_extends_CNOT _ (S n) _); try lia.
    Opaque a_swap.
    simpl.
    unfold pad_bot, pad_top.
    rewrite <- Mscale_mult_dist_r.
    rewrite <- Mscale_mult_dist_l.
    apply Mmult_simplify; [ | apply Mmult_simplify ].
    + apply HSwapSSn.
    + rewrite denote_cnot.
      rewrite unfold_ueval_cnot.
      bdestruct (S n <? S (S n)); try (lia; exfalso).
      rewrite unfold_pad.
      bdestruct (S n + (1 + (S (S n) - S n - 1) + 1) <=? S (S (S n)))%nat; [ | exfalso; fold Nat.add in H0; lia ].
      replace ((S (S (S n)) - (S n + (1 + (S (S n) - S n - 1) + 1))))%nat with 0%nat by lia.
      Msimpl.
      simpl_cast_semantics.
      simpl.
      restore_dims.
      replace (I 2 ⊗ X_semantics 2 1 0 × (Z_semantics 1 2 0 ⊗ I 2)) with (⟦ ((Z 1 2 0 ↕ — ⟷ (— ↕ (X) 2 1 0))) ⟧) by easy.
      rewrite cnot_l_is_cnot.
      rewrite <- cnot_decomposition.
      rewrite 2 kron_assoc; try auto with wf_db.
      autorewrite with scalar_move_db.
      destruct n.
      * simpl.
        repeat rewrite kron_1_l; try auto with wf_db.
        repeat rewrite kron_1_r; try auto with wf_db.
      * replace (S n - n - 1)%nat with 0%nat by lia.
        apply Mscale_simplify; [ | easy ].
        fold (n_wire (S n)).
        rewrite n_wire_semantics.
        repeat rewrite id_kron.
        replace (2 ^ S n + (2 ^ S n + 0))%nat with (2 * 2 ^ S n)%nat by lia.
        apply kron_simplify; try easy.
        Msimpl.
        simpl.
        easy.
    + apply HSwapSSn.
Qed.

Lemma unpadded_cnot_b_sem_equiv : forall n, / (√ 2)%R .* uc_eval (@CNOT (S (S n)) (S n) 0) = ⟦ unpadded_cnot_b 0 (S (S n )) ⟧.
Proof.
  intros.
  assert (Hhh : hadamard ⊗ I 2 × (I 2 ⊗ hadamard) = hadamard ⊗ hadamard).
  {
    rewrite kron_mixed_product.
    Msimpl.
    easy.
  }
  assert (HSwapSSn : forall n, uc_eval (@SWAP (S (S (S n))) (S (S n)) 1) = I 2 ⊗ ⟦ a_swap (S (S n)) ⟧).
  {
    intros.
    rewrite swap_pad'.
    simpl.
    rewrite a_swap_correct.
    rewrite a_swap_sem_base.
    Msimpl.
    rewrite SWAP_symmetric; try lia.
    easy.
  }
  destruct n.
  - unfold unpadded_cnot.
    simpl.
    Msimpl.
    rewrite <- H_swaps_CNOT.
    restore_dims.
    simpl.
    rewrite denote_cnot.
    repeat rewrite denote_H.
    rewrite unfold_ueval_cnot.
    simpl.
    unfold pad_u.
    repeat rewrite unfold_pad.
    simpl.
    Msimpl.
    restore_dims.
    rewrite Hhh.
    repeat rewrite <- Mmult_assoc.
    rewrite Hhh.
    repeat rewrite Mmult_assoc.
    rewrite <- Mscale_mult_dist_r.
    apply Mmult_simplify; [ easy | ].
    repeat rewrite <- Mmult_assoc.
    rewrite <- Mscale_mult_dist_l.
    apply Mmult_simplify; [ | easy ].
    rewrite cnot_decomposition.
    restore_dims.
    rewrite <- cnot_l_is_cnot.
    simpl.
    easy.
  - rewrite <- (SWAP_extends_CNOT _ 1 _); try lia.
    Opaque a_swap.
    simpl.
    unfold pad_bot_1, pad_bot, pad_top.
    rewrite <- Mscale_mult_dist_r.
    rewrite <- Mscale_mult_dist_l.
    apply Mmult_simplify; [ | apply Mmult_simplify ].
    + Msimpl.
      apply HSwapSSn.
    + rewrite <- H_swaps_CNOT.
      simpl_cast_semantics.
      simpl.
      repeat rewrite denote_H.
      rewrite denote_cnot.
      rewrite unfold_ueval_cnot.
      simpl.
      unfold pad_u.
      repeat rewrite unfold_pad.
      simpl.
      Msimpl.
      fold (n_wire n).
      rewrite n_wire_semantics.
      rewrite id_kron.
      replace (2 ^ n + (2 ^ n + 0))%nat with (2 * 2 ^ n)%nat by lia.
      remember (2 ^ n)%nat as n2.
      replace (2 * n2 + (2 * n2 + 0))%nat with (2 * 2 * n2)%nat by lia.
      rewrite 2 (kron_id_dist_r (2 * n2)); try auto with wf_db.
      rewrite <- Mscale_mult_dist_r.
      restore_dims.
      rewrite <- Mscale_mult_dist_r.
      restore_dims.
      rewrite <- Mscale_mult_dist_l.
      restore_dims.
      rewrite <- Hhh.
      restore_dims.
      rewrite 2 (kron_id_dist_r (2 * n2)); try auto with wf_db.
      repeat rewrite Mmult_assoc.
      replace ((2 * 2 * (2 * n2))%nat) with (2 * (2 * 2 * n2))%nat by lia.
      apply Mmult_simplify; [ rewrite kron_assoc; try auto with wf_db;  rewrite id_kron; repeat rewrite Nat.mul_assoc; easy | ].
      apply Mmult_simplify; [ easy | ].
      replace (2 ^ 1 * 2 * (2 * n2))%nat with (2 * (2 * 2 * n2))%nat by (simpl; lia).
      replace (2 * 2 ^ 1 * (2 * n2))%nat with (2 * (2 * 2 * n2))%nat by (simpl; lia).
      repeat rewrite <- Mmult_assoc.
      apply Mmult_simplify; [ | easy ].
      apply Mmult_simplify; [ | rewrite kron_assoc; try auto with wf_db; rewrite id_kron; repeat rewrite Nat.mul_assoc; easy ].
      restore_dims.
      rewrite <- Mscale_kron_dist_l.
      repeat rewrite <- kron_assoc; try auto with wf_db.
      rewrite <- (kron_id_dist_r (2 * n2)%nat); try auto with wf_db.
      apply kron_simplify; [ | easy ].
      rewrite cnot_decomposition.
      rewrite <- cnot_l_is_cnot.
      simpl.
      easy.
    + Msimpl.
      apply HSwapSSn.
Qed.

Lemma lt_when_not_eq_gt : forall {m n}, (n <? m) = false -> (n =? m = false) -> (m <? n) = true.
Proof.
  intros.
  apply Nat.ltb_lt.
  apply Nat.ltb_ge in H.
  apply Nat.eqb_neq in H0.
  bdestruct (m <? n); lia.
Qed.

Definition cnot_n_m_ingest {dim} (n m : nat) : ZX (n + (S m - n) + (dim - (m + 1))) (n + (S m - n) + (dim - (m + 1))) :=
  (if n <? m then
    padbt (unpadded_cnot_t _ _)
  else 
    (n_wire _)
  ).

Lemma cnot_n_m_dim : forall {dim n m}, (n <? m = true)%nat -> (m <? dim = true)%nat -> (n + (S m - n) + (dim - (m + 1)))%nat = dim.
Proof.
  intros. apply Nat.ltb_lt in H, H0. lia.
Defined.

Lemma cnot_m_n_dim : forall {dim n m}, (m <? n = true)%nat -> (n <? dim = true)%nat -> (m + (S n - m) + (dim - (n + 1)))%nat = dim.
Proof.
  intros. apply Nat.ltb_lt in H, H0. lia.
Defined.

Lemma cnot_dim : forall {dim n m}, (m <? dim = true)%nat -> (n <? dim = true)%nat -> ((min m n) + (S (max m n) - (min m n)) + (dim - ((max m n) + 1)))%nat = dim.
Proof.
  intros. apply Nat.ltb_lt in H, H0. lia.
Defined.

Definition cnot_m_n_ingest {dim} (n m : nat) : ZX (m + (S n - m) + (dim - (n + 1))) (m + (S n - m) + (dim - (n + 1))) :=
    (if m <? n then
      padbt (unpadded_cnot_b _ _)
    else 
      (n_wire _)
    ).
  
Definition cnot_ingest {dim} (n m : nat) : ZX dim dim.
Proof.
  destruct (Sumbool.sumbool_of_bool (n <? m)) as [ Hnltm | _ ].
  - destruct (Sumbool.sumbool_of_bool (m <? dim)) as [ Hmltdim | _ ].
    + apply (cast _ _ (eq_sym (cnot_n_m_dim Hnltm Hmltdim)) (eq_sym (cnot_n_m_dim Hnltm Hmltdim))).
      apply cnot_n_m_ingest.
    + apply (n_wire dim).
  - destruct (Sumbool.sumbool_of_bool (m <? n)) as [ Hmltn | _ ].
    + destruct (Sumbool.sumbool_of_bool (n <? dim)) as [ Hnltdim | _ ].
      * apply (cast _ _ (eq_sym (cnot_m_n_dim Hmltn Hnltdim)) (eq_sym (cnot_m_n_dim Hmltn Hnltdim))).
        apply cnot_m_n_ingest.
      * apply (n_wire dim).
    + apply (n_wire dim).
Defined.

Lemma cnot_n_m_equiv : forall dim n m, (n < dim)%nat -> (m < dim)%nat -> (n < m)%nat -> / (√ 2)%R .* uc_eval (@CNOT dim n m) = ⟦ @cnot_n_m_ingest dim n m ⟧.
Proof.
  intros.
  rewrite denote_cnot.
  unfold ueval_cnot.
  unfold pad_ctrl.
  repeat rewrite unfold_pad.
  unfold cnot_n_m_ingest.
  bdestruct (n <? m); 
    try (exfalso; lia).
  replace (n + (1 + (m - n - 1) + 1))%nat with (S m) by lia.
  bdestruct (S m <=? dim); try (exfalso; lia).
  rewrite pad_bot_top_semantics.
  repeat rewrite kron_assoc; try auto with wf_db; [| shelve].
  rewrite <- unpadded_cnot_simpl_args_sem.
  rewrite Nat.sub_succ_l; try lia.
  destruct (m - n)%nat eqn:Hmn1; try (exfalso; lia).
  pose proof (unpadded_cnot_t_sem_equiv n0) as H_unpad_n0.
  rewrite <- H_unpad_n0.
  autorewrite with scalar_move_db.
  restore_dims.
  rewrite denote_cnot.
  unfold ueval_cnot.
  unfold pad_ctrl.
  repeat rewrite unfold_pad.
  unfold cnot_n_m_ingest.
  simpl.
  rewrite Nat.sub_0_r, 2 Nat.add_1_r.
  simpl. 
  rewrite Nat.leb_refl.
  rewrite Nat.sub_diag.
  Msimpl.
  restore_dims.
  replace ((2 ^ n * (2 * 2 ^ n0 * 2 * 2 ^ (dim - S m)))%nat) with (2 ^ n * (2 * (2 ^ n0 * 2) * 2 ^ (dim - S m)))%nat by lia.
  apply Mscale_simplify; [ | easy ].
  replace ((2 * 2 ^ n0 * 2 * 2 ^ (dim - S m))%nat) with (2 * (2 ^ n0 * 2) * 2 ^ (dim - S m))%nat by lia.
  apply kron_simplify; try easy.
  repeat rewrite kron_assoc; auto with wf_db.
Unshelve. 
  + replace (2 * 2 ^ (m - n - 1) * 2)%nat with (2 ^ (1 + (m - n - 1) + 1))%nat.
    auto with wf_db.
    rewrite <- Nat.pow_succ_r; try lia.
    rewrite Nat.mul_comm.
    rewrite <- Nat.pow_succ_r; try lia.
    rewrite Nat.add_1_r.
    easy.
Qed.

Lemma cnot_m_n_equiv : forall dim n m, (n < dim)%nat -> (m < dim)%nat -> (m < n)%nat -> / (√ 2)%R .* uc_eval (@CNOT dim n m) = ⟦ @cnot_m_n_ingest dim n m ⟧.
Proof.
  intros.
  rewrite denote_cnot.
  unfold ueval_cnot.
  unfold pad_ctrl.
  repeat rewrite unfold_pad.
  unfold cnot_m_n_ingest.
  bdestruct (n <? m); 
    try (exfalso; lia).
  bdestruct (m <? n); 
    try (exfalso; lia).
  replace (m + (1 + (n - m - 1) + 1))%nat with (S n) by lia.
  bdestruct (S n <=? dim); try (exfalso; lia).
  rewrite pad_bot_top_semantics.
  repeat rewrite kron_assoc; try auto with wf_db; [| shelve].
  rewrite <- unpadded_cnot_simpl_args_sem.
  rewrite Nat.sub_succ_l; try lia.
  destruct (n - m)%nat eqn:Hmn1; try (exfalso; lia).
  pose proof (unpadded_cnot_b_sem_equiv n0) as H_unpad_n0.
  rewrite <- H_unpad_n0.
  autorewrite with scalar_move_db.
  restore_dims.
  rewrite denote_cnot.
  unfold ueval_cnot.
  unfold pad_ctrl.
  repeat rewrite unfold_pad.
  unfold cnot_n_m_ingest.
  simpl.
  rewrite Nat.sub_0_r, 2 Nat.add_1_r.
  simpl. 
  rewrite Nat.leb_refl.
  rewrite Nat.sub_diag.
  Msimpl.
  restore_dims.
  replace (2 ^ m * (2 * 2 ^ n0 * 2 * 2 ^ (dim - S n)))%nat with (2 ^ m * (2 * (2 ^ n0 * 2) * 2 ^ (dim - S n)))%nat by lia.
  apply Mscale_simplify; [ | easy ].
  replace (2 * 2 ^ n0 * 2 * 2 ^ (dim - S n))%nat with (2 * (2 ^ n0 * 2) * 2 ^ (dim - S n))%nat by lia.
  apply kron_simplify; try easy.
  repeat rewrite kron_assoc; auto with wf_db.
Unshelve. 
  + replace (2 * 2 ^ (n - m - 1) * 2)%nat with (2 ^ (1 + (n - m - 1) + 1))%nat.
    auto with wf_db.
    rewrite <- Nat.pow_succ_r; try lia.
    rewrite Nat.mul_comm.
    rewrite <- Nat.pow_succ_r; try lia.
    rewrite Nat.add_1_r.
    easy.
Qed.

Lemma cnot_ingest_correct : forall dim n m, (n < dim)%nat -> (m < dim)%nat -> (m <> n)%nat -> / (√ 2)%R .* uc_eval (@CNOT dim n m) = ⟦ @cnot_ingest dim n m ⟧.
Proof.
  intros.
  unfold cnot_ingest.
  destruct (dec (n <? m)).
  - destruct (dec (m <? dim)).
    + simpl_cast_semantics.
      rewrite cnot_n_m_equiv; try easy.
      apply Nat.ltb_lt; easy.
    + apply Nat.ltb_nlt in e0.
      contradiction.
  - destruct (dec (m <? n)).
    + destruct (dec (n <? dim)).
      * simpl_cast_semantics.
        rewrite cnot_m_n_equiv; try easy.
        apply Nat.ltb_lt; easy.
      * apply Nat.ltb_nlt in e1.
        contradiction.
    + exfalso.
      apply Nat.ltb_nlt in e, e0; lia.
Qed.

Definition gate_ingest' dim (zx : ZX 1 1) n : ZX (n + 1 + (dim - (n + 1))) (n + 1 + (dim - (n + 1))) := padbt zx.

Lemma gate_ingest_dim : forall n dim, (n <? dim = true)%nat -> ((n + 1 + (dim - (n + 1))) = dim)%nat.
Proof.
  intros. apply Nat.ltb_lt in H. lia.
Qed.

Definition gate_ingest dim (zx : ZX 1 1) (n : nat) : ZX dim dim.
Proof.
  destruct (Sumbool.sumbool_of_bool (n <? dim)) as [ H | _ ].
  - apply (cast _ _ (eq_sym (gate_ingest_dim _ _ H)) (eq_sym (gate_ingest_dim _ _ H))).
    apply gate_ingest'.
    exact zx.
  - apply (n_wire dim).
Defined.

Lemma gate_ingest_correct : forall n dim (zx : ZX 1 1) (A : Matrix 2 2), (n < dim)%nat -> ⟦ zx ⟧ = A -> pad_u dim n A = ⟦ @gate_ingest dim zx n ⟧.
Proof.
  intros.
  unfold gate_ingest.
  destruct (dec (n <? dim)); [ | apply Nat.ltb_nlt in e; lia ].
  simpl_cast_semantics.
  unfold pad_u.
  rewrite unfold_pad.
  bdestruct (n + 1 <=? dim); try (exfalso; lia).
  simpl.
  rewrite 2 n_wire_semantics.
  rewrite H0.
  easy.
Qed.

Definition H_ingest {dim} n := gate_ingest dim □ n.
Definition X_ingest {dim} n := gate_ingest dim (_X_) n.
Definition Rz_ingest {dim} n α := gate_ingest dim (_Rz_ α) n.

Lemma H_ingest_correct : forall {dim} n, (n < dim)%nat -> @uc_eval dim (H n) = ⟦ @H_ingest dim n ⟧.
Proof.
  intros.
  rewrite denote_H.
  apply gate_ingest_correct; easy.
Qed.

Lemma X_ingest_correct : forall {dim} n, (n < dim)%nat -> @uc_eval dim (SQIR.X n) = ⟦ @X_ingest dim n ⟧.
Proof.
  intros.
  rewrite denote_X.
  apply gate_ingest_correct; [ easy | ].
  apply X_is_X.
Qed.

Lemma Rz_ingest_correct : forall {dim} n α, (n < dim)%nat -> @uc_eval dim (SQIR.Rz α n) = ⟦ @Rz_ingest dim n α ⟧.
Proof.
  intros.
  rewrite denote_Rz.
  apply gate_ingest_correct; [ easy | ].
  apply _Rz_is_Rz.
Qed.

(* @nocheck name *)
Lemma SKIP_is_n_wire : forall dim, uc_eval (@SKIP (S dim)) = ⟦ n_wire (S dim) ⟧.
Proof.
  intros.
  rewrite denote_SKIP; try lia.
  rewrite n_wire_semantics; easy.
Qed. 

Require Import VOQC.RzQGateSet.

Fixpoint ingest {dim} (u : ucom (RzQGateSet.U) dim) : ZX dim dim :=
  match u with
  | uapp1 URzQ_H n => H_ingest n
  | uapp1 URzQ_X n => X_ingest n
  | uapp1 (URzQ_Rz α) n => Rz_ingest n (Q2R α * PI)%R
  | uapp2 _ n m => cnot_ingest n m
  | useq u1 u2 => ingest u1 ⟷ ingest u2
  | _ => (n_wire dim)
  end.

Local Open Scope ucom_scope.

(* @nocheck name *)
(* Sticking with SQIR conventions *)
Fixpoint RzQToBaseUCom {dim} (u : ucom (RzQGateSet.U) dim) : base_ucom dim :=
  match u with
  | uapp1 URzQ_H n => SQIR.H n
  | uapp1 URzQ_X n => SQIR.X n
  | uapp1 (URzQ_Rz α) n => SQIR.Rz (Q2R α * PI)%R n
  | uapp2 _ n m => SQIR.CNOT n m
  | useq u1 u2 => RzQToBaseUCom u1; RzQToBaseUCom u2
  | _ => SKIP
  end.

Definition ingest_list {n dim} (u : RzQGateSet.U n) (qs : list nat) (pf : List.length qs = n) : ZX dim dim :=
  match u with
  | URzQ_H     => H_ingest (List.nth O qs O) 
  | URzQ_X     => X_ingest (List.nth O qs O)
  | URzQ_Rz a  => Rz_ingest (List.nth O qs O) (Q2R a * PI)%R 
  | URzQ_CNOT  => cnot_ingest (List.nth O qs O) (List.nth (S O) qs O)
  end.

Theorem ingest_list_to_base_correct : forall {n dim} (u : RzQGateSet.U n) (qs : list nat) (pf : List.length qs = n),
  (bounded_list qs dim /\ List.NoDup qs) -> (* Proved equiv to well-typedness *)
   exists c, c .* @uc_eval dim (@to_base n dim u qs pf) = ⟦ @ingest_list _ dim u qs pf ⟧ /\ c <> C0.
Proof.
  intros.
  induction u.
  1-3: exists C1; split; [Msimpl | nonzero]; do 2 (destruct qs; try easy); simpl.
  1: apply H_ingest_correct.
  2: apply X_ingest_correct.
  3: apply Rz_ingest_correct.
  all: destruct H; unfold bounded_list in H.
  1-3: apply H; left; easy. 
  - exists (/ (√ 2)%R )%C; split; [ | apply nonzero_div_nonzero; apply Csqrt2_neq_0 ].
    do 3 (destruct qs; try easy).
    simpl.
    apply cnot_ingest_correct.
    + apply H; left; easy.
    + apply H; right; left; easy.
    + inversion H0.
      unfold not in H3.
      unfold In in H3.
      apply Classical_Prop.not_or_and in H3.
      destruct H3.
      easy.
Qed.

Theorem ingest_correct : forall {dim} (u : ucom (RzQGateSet.U) dim), uc_well_typed u -> exists (c : C), c .* uc_eval (RzQToBaseUCom u) = ⟦ ingest u ⟧ /\ (c <> C0).
Proof.
  intros.
  induction u.
  - inversion H.
    simpl.
    specialize (IHu1 H2).
    specialize (IHu2 H3).
    destruct IHu1, IHu2.
    destruct H4, H5.
    exists (x * x0)%C; split; [ | apply Cmult_neq_0; assumption ].
    rewrite <- H4.
    rewrite <- H5.
    rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    rewrite Mscale_assoc.
    easy.
  - simpl.
    exists C1; split; [ | nonzero ].
    Msimpl.
    inversion H.
    subst.
    clear H.
    destruct u.
    + apply H_ingest_correct.
      assumption.
    + apply X_ingest_correct.
      assumption.
    + apply Rz_ingest_correct.
      assumption.
    + destruct dim; [ exfalso; lia | ].
      apply SKIP_is_n_wire.
  - inversion H.
    subst.
    simpl.
    exists (/ (√2)%R)%C; split; [ | apply nonzero_div_nonzero; apply Csqrt2_neq_0 ].
    rewrite cnot_ingest_correct; congruence.
  - simpl.
    exists C1; split; [ | nonzero ].
    Msimpl.    
    destruct dim; [ exfalso; inversion H; lia | ].
    apply SKIP_is_n_wire.
Qed.

  

Close Scope matrix_scope.
