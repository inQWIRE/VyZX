Require Import SQIR.UnitarySem.
Require Import SQIR.Equivalences.
Require Import CoreData.
Require Import CoreRules.
Require Import Gates.
Require Import GateRules.
Require Import ZXPad.
Require Import QuantumLib.Quantum.


Open Scope ZX_scope.

Fixpoint ZX_1_1_pad {dim} : nat -> ZX 1 1 -> ZX dim dim :=
  fun n zx =>
    match dim with
    | 0   => ⦰
    | S k => match n with
             | 0 => zx ↕ (nWire k)
             | S m => — ↕ (@ZX_1_1_pad k m zx)
             end
    end.

(* Conversion  to base ZX diagrams *)

Fixpoint ZX_top_to_bottom_helper (n : nat) : ZX (S n) (S n) :=
  match n with 
  | 0   => Wire
  | S k => Compose (Stack Swap (nWire k)) (Stack Wire (ZX_top_to_bottom_helper k))
  end.

Definition ZX_top_to_bottom (n : nat) : ZX n n :=
  match n with
  | 0 => Empty
  | S k => ZX_top_to_bottom_helper k
  end.

Definition ZX_bottom_to_top (n : nat) : ZX n n :=
  (ZX_top_to_bottom n)⊤.

Definition A_Swap_ZX (n : nat) : ZX n n :=
  match n with
  | 0   => Empty
  | S k => ZX_top_to_bottom (S k)
    ⟷ Cast  (S k) (S k) (eq_sym (Nat.add_1_r k)) (eq_sym (Nat.add_1_r k)) (ZX_bottom_to_top k ↕ —)
  end.

(* Arbitrary Swap Semantics *)

(* A linear mapping which takes | x y1 ... yn > -> | y1 .. yn x > *)
Fixpoint Top_wire_to_bottom (n : nat) : Square (2 ^ n) :=
  match n with
  | 0   => I 1
  | S k => match k with
           | 0   => I 2
           | S j => (@Mmult _ (2^n) _) ((I 2) ⊗ (Top_wire_to_bottom k)) (swap ⊗ (j ⨂ (I 2)))
           end
  end.

Open Scope matrix_scope.
Definition Bottom_wire_to_top (n : nat) : Square (2 ^ n) :=
  (Top_wire_to_bottom n)⊤.

Definition A_Swap_semantics (n : nat) : Square (2 ^ n) :=
  match n with
  | 0   => I 1
  | S k => (@Mmult _ (2 ^ n) _ ((Bottom_wire_to_top k) ⊗ (I 2)) (Top_wire_to_bottom (S k)))
  end.

Lemma Top_wire_to_bottom_ind : forall n, Top_wire_to_bottom (S (S n)) = @Mmult _ (2 ^ (S (S n))) _ ((I 2) ⊗ Top_wire_to_bottom (S n)) (swap ⊗ (I (2 ^ n))).
Proof.
  intros.
  induction n.
  - Msimpl.
    simpl.
    Msimpl.
    easy.
  - rewrite IHn.
    simpl.
    apply Mmult_simplify.
    + apply kron_simplify; easy.
    + apply kron_simplify; [easy | ].
      rewrite kron_n_I.
      rewrite id_kron.
      replace (2 ^ n + (2 ^ n + 0))%nat with (2 ^ n * 2)%nat by lia.
      easy.
Qed.

(* Well foundedness of semantics *)

Lemma WF_Top_to_bottom (n : nat) : WF_Matrix (Top_wire_to_bottom n).
Proof.
  destruct n; try auto with wf_db.
  induction n.
  - simpl; auto with wf_db.
  - simpl. try auto with wf_db.
Qed.

Global Hint Resolve WF_Top_to_bottom : wf_db.

Lemma WF_Bottom_to_top (n : nat) : WF_Matrix (Bottom_wire_to_top n).
Proof. unfold Bottom_wire_to_top. auto with wf_db. Qed.

Global Hint Resolve WF_Bottom_to_top : wf_db.

Lemma WF_A_Swap_semantics (n : nat) :
 WF_Matrix (A_Swap_semantics n).
Proof.
  intros.
  unfold A_Swap_semantics.
  destruct n; auto with wf_db.
Qed.

Global Hint Resolve WF_A_Swap_semantics : wf_db.

(* Proving correctness of conversion *)

Lemma Top_to_bottom_correct : forall n, ZX_semantics (ZX_top_to_bottom n) = Top_wire_to_bottom n.
Proof.
  intros.
  destruct n; [ reflexivity | ].
  destruct n; [ easy | ].
  induction n.
  - easy.
  - simpl.
    simpl in IHn.
    rewrite <- IHn.
    rewrite nWire_semantics.
    rewrite kron_n_I.
    rewrite 2 id_kron.
    replace (2 * 2 ^ n)%nat with (2 ^ n * 2)%nat by lia.
    easy.
Qed.

Lemma Bottom_to_top_correct : forall n, ZX_semantics (ZX_bottom_to_top n) = Bottom_wire_to_top n.
Proof.
  intros.
  unfold ZX_bottom_to_top.
  unfold Bottom_wire_to_top.
  rewrite ZX_semantics_transpose_comm.
  rewrite Top_to_bottom_correct.
  easy.
Qed.

Lemma A_Swap_Correct : forall n, ZX_semantics (A_Swap_ZX n) = A_Swap_semantics n.
Proof.
  intros.
  unfold A_Swap_semantics.
  destruct n; [ reflexivity | ].
  destruct n.
  - simpl.
    rewrite Cast_semantics.
    simpl.
    unfold Bottom_wire_to_top.
    simpl.
    rewrite id_transpose_eq.
    easy.
  - rewrite <- Bottom_to_top_correct.
    rewrite <- Top_to_bottom_correct.
    simpl.
    rewrite (@Cast_semantics _ _ (S (S n)) (S (S n)) _ _ (ZX_bottom_to_top (S n) ↕ —)).
    easy.
Qed.

Lemma swap_transpose : (swap)⊤ = swap.
Proof. unfold transpose; solve_matrix. Qed.

Lemma WF_test : forall n, WF_Matrix (swap ⊗ (I (2 ^ (S n))) × ((I 2) ⊗ A_Swap_semantics (S (S n))) × (swap ⊗ (I (2 ^ (S n))))).
Proof.
  intros.
  apply WF_mult.
  apply WF_mult.
  apply WF_kron; auto with wf_db.
  apply WF_kron; auto with wf_db.
  1-2: simpl; lia.
  auto with wf_db.
Qed.

Lemma ZX_A_swap_grow : forall n, A_Swap_ZX (S (S (S n))) ∝ (⨉ ↕ nWire (S n)) ⟷ (— ↕ A_Swap_ZX (S (S n))) ⟷ (⨉ ↕ nWire (S n)). 
Proof.
  intros.
  unfold A_Swap_ZX.
  simpl_casts.
  simpl.
  repeat rewrite ZX_Compose_assoc.
  apply ZX_Compose_simplify; [ easy | ].
  simpl.
  remember (— ↕ ZX_top_to_bottom_helper n) as TBN1.
  remember (⨉ ↕ nWire n) as swap_nW.
  repeat rewrite stack_wire_distribute_l.
  repeat rewrite ZX_Compose_assoc.
  apply ZX_Compose_simplify; [ easy | ].
  apply ZX_Compose_simplify; [ easy | ].
  unfold ZX_bottom_to_top.
  simpl.
  rewrite nWire_transpose.
  remember (ZX_top_to_bottom_helper n) as TBN.
  rewrite cast_symm.
  prop_exists_nonzero 1.
  simpl.
  simpl_cast_semantics.
  simpl.
  simpl_cast_semantics.
  rewrite nWire_semantics.
  rewrite kron_id_dist_r; try auto with wf_db; [| shelve].
  Msimpl.
  replace ((2 * 2 ^ S (n + 1)))%nat with (2 * 2 ^ S n * 2)%nat by shelve.
  replace (2 * 2 * (2 * 2 ^ n))%nat with (2 * 2 * 2 ^ n * 2)%nat by (simpl; lia).
  apply Mmult_simplify.
  rewrite kron_assoc; auto with wf_db.
  2: shelve.
  rewrite 2 id_kron.
  rewrite (Nat.mul_comm 2 (2 ^ n)).
  easy.
Unshelve.
  1,2: lia.
  1,3: subst; auto with wf_db.
  - replace (2 ^ n + (2 ^ n + 0))%nat with (2 ^ ( S n))%nat by (simpl; lia).
    apply WF_kron; try lia; auto with wf_db.
  - simpl. restore_dims. rewrite <- kron_assoc; auto with wf_db.
  - rewrite Nat.add_1_r; simpl.
    ring.
Qed.

Lemma A_swap_ind : forall n, A_Swap_semantics (S (S (S n))) = swap ⊗ (I (2 ^ (S n))) × (I 2 ⊗ A_Swap_semantics (S (S n))) × (swap ⊗ (I (2 ^ (S n)))).
Proof.
  intros.
  unfold A_Swap_semantics.
  unfold Bottom_wire_to_top.
  rewrite 3 Top_wire_to_bottom_ind.
  remember (Top_wire_to_bottom (S n)) as TB.
  rewrite Mmult_transpose.
  rewrite kron_id_dist_r; auto with wf_db.
  restore_dims.
  repeat rewrite <- Mmult_assoc.
  replace (2 ^ S (S n))%nat with ((2 * 2 * 2 ^ n))%nat.
  rewrite kron_transpose.
  rewrite swap_transpose.
  rewrite id_transpose_eq.
  rewrite kron_assoc; try auto with wf_db.
  rewrite (id_kron (2 ^ n) 2).
  replace (2 * (2 * 2 * 2 ^ n))%nat with (2 * 2 ^ S n * 2)%nat.
  replace (2 * 2 * 2 ^ S n)%nat with (2 * 2 * 2 ^ n * 2)%nat.
  repeat rewrite Mmult_assoc.
  apply Mmult_simplify.
  + replace (2 ^ (S n))%nat with (2 ^ n * 2)%nat.
    easy.
    rewrite Nat.mul_comm.
    simpl.
    easy.
  + repeat rewrite kron_id_dist_l; try auto with wf_db.
    repeat rewrite kron_id_dist_r; try auto with wf_db.
    replace (I 2 ⊗ ((TB) ⊤ ⊗ I 2)) with ((I 2 ⊗ TB) ⊤ ⊗ I 2).
    rewrite <- kron_id_dist_l.
    simpl.
    restore_dims.
    rewrite Mmult_assoc.
    easy.
  all: try (subst; auto with wf_db).
  - try (apply WF_kron; try auto with wf_db; simpl; lia).
  - rewrite kron_transpose.
    rewrite id_transpose_eq.
    rewrite kron_assoc; subst; auto with wf_db.
  - rewrite Nat.mul_comm; apply WF_mult; apply WF_kron; try auto with wf_db; simpl; lia.
  - apply WF_kron; try auto with wf_db; simpl; lia.
    + simpl; lia.
    + simpl; lia.
    + simpl; lia.
    + apply WF_transpose; apply WF_kron; try (simpl; lia); auto with wf_db.      
    + apply WF_transpose; apply WF_kron; try (simpl; lia); subst; auto with wf_db.
Qed.

Local Open Scope ucom_scope.
Lemma swap_spec' : swap = ((ket 0 × bra 0)  ⊗ (ket 0 × bra 0) .+ (ket 0 × bra 1)  ⊗ (ket 1 × bra 0)
.+ (ket 1 × bra 0)  ⊗ (ket 0 × bra 1) .+ (ket 1 × bra 1)  ⊗ (ket 1 × bra 1)).
Proof.
  solve_matrix.
Qed.

Fixpoint Swap_ind dim n : base_ucom dim :=
  match n with
  | 0%nat => @SWAP dim 0 1
  | (S n0) => (@SWAP dim (S (S n0)) (S n0)) ; (Swap_ind dim n0); (@SWAP dim (S (S n0)) (S n0))
  end.

Lemma Swap_ind_eq : forall n dim, (S n < dim)%nat -> (1 < dim)%nat -> uc_eval (Swap_ind dim n) = uc_eval (@SWAP dim 0 (S n)).
Proof.
  intros.
  induction n; [ easy | ].
  simpl.
  rewrite IHn; try lia.
  rewrite 3 denote_swap.
  unfold ueval_swap.
  bdestruct (S (S n) <? S n); try (exfalso; lia).
  bdestruct (S n <? (S (S n))); try (exfalso; lia).
  simpl.
  repeat rewrite unfold_pad.
  destruct n.
  - simpl.
    destruct dim; try lia. 
    destruct dim; try lia. 
    destruct dim; try lia.
    simpl.
    Msimpl.
    rewrite Nat.add_0_r.
    rewrite Nat.sub_0_r.
    replace (2 ^ dim + 2 ^ dim)%nat with (2 * 2 ^dim)%nat by lia.
    rewrite <- id_kron.
    rewrite <- kron_assoc; try auto with wf_db.
    rewrite <- Mmult_assoc.
    remember (I 2 ⊗ _) as A.
    remember (_ ⊗ I 2) as B.
    restore_dims.
    rewrite <- 2 kron_id_dist_r.
    apply kron_simplify; try easy.
Admitted.


Lemma A_swap_sem_base : forall n, A_Swap_semantics (S (S n)) = uc_eval (@SWAP (S (S n)) 0 (S n)).
Proof.
  intros.
  induction n.
  - simpl.
    rewrite denote_swap.
    unfold ueval_swap.
    simpl.
    gridify.
    unfold Bottom_wire_to_top.
    unfold Top_wire_to_bottom.
    rewrite unfold_pad.
    simpl.
    gridify.
    solve_matrix.
  - rewrite A_swap_ind.
    rewrite <- Swap_ind_eq; try lia.
    rewrite IHn.
    simpl.
    rewrite Swap_ind_eq; try lia.
    rewrite (denote_swap _ (S _) (S _)).
    unfold ueval_swap.
    bdestruct (S (S n) <? S n)%nat; try (exfalso; lia).
    bdestruct (S n <? S (S n))%nat; try (exfalso; lia).
    rewrite unfold_pad.
    replace ((S (S n) - S n - 1))%nat with 0%nat by lia.
    repeat rewrite Nat.add_0_r.
    repeat rewrite Nat.add_1_r.
    replace (S n + 2)%nat with (S (S (S n)))%nat by lia.
    rewrite Nat.leb_refl.
    rewrite Nat.sub_diag.
    simpl.
    Msimpl.
Admitted.

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
    Msimpl.
    easy.
  - destruct x; try (exfalso; lia).
    destruct (S x - y)%nat eqn:Hc; try (exfalso; lia).
    rewrite Nat.sub_0_r.
    replace (S x - S y - 1 + 1)%nat with (S x - S y)%nat by lia.
    replace (S x - S y)%nat with n0 by lia.
    rewrite Nat.leb_refl.
    Msimpl.
    assert (x - y = S x0)%nat by lia.
    assert (x - y = n0)%nat by lia.
    replace (2 ^ S y * (1 * (2 * 2 ^ (n0 - 1) * 2) * 2 ^ (S n0 - S n0)))%nat 
      with (2 ^ S y * (2 * 2 ^ x0 * 2))%nat; [ | shelve ].
    apply kron_simplify; try easy.
    rewrite Nat.sub_diag. 
    Msimpl.
    replace ((2 * 2 ^ (n0 - 1) * 2 * 2 ^ 0)%nat) 
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
  rewrite <- (le_plus_minus n m).
  rewrite <- (le_plus_minus).
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
    apply A_Swap_ZX.
  * apply (Cast _ _ (add_2_r n0) (add_2_r n0)). 
    apply (pad_top n0).
    apply cnot.
  * apply pad_bot_1.
    apply A_Swap_ZX.
Defined.

Definition base_cnot_1 n0 (cnot : ZX 2 2) : ZX (S (S n0)) (S (S n0)).
Proof.
  apply (@Compose _ (S (S n0)) _).
  apply (@Compose _ (S (S n0)) _).
  * apply (pad_top 1).
    apply A_Swap_ZX.
  * apply (Cast _ _ (add_2_l n0) (add_2_l n0)).
    apply (pad_bot n0).
    apply cnot.
  * apply (pad_top 1).
    apply A_Swap_ZX.
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
    simpl.
    Msimpl.
    restore_dims.
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
    simpl.
    rewrite Nat.sub_diag.
    simpl.
    Msimpl.
    restore_dims.
    rewrite 2 kron_id_dist_l; try auto with wf_db.
  - destruct n; try (exfalso; lia).
    bdestruct (0 <? 0); try (exfalso; lia).
    lma.
Qed.

Lemma unpadded_cnot_simpl_args_sem : forall n m cnot base_cnot, ZX_semantics (unpadded_cnot base_cnot cnot 0 (m - n)) = ZX_semantics (unpadded_cnot base_cnot cnot n m).
Proof.
  intros.
  unfold unpadded_cnot.
  rewrite Nat.sub_0_r; simpl_casts.
  destruct (m - n)%nat; [ easy | ].
  destruct n0; easy.
Qed.

Lemma unpadded_cnot_simpl_args : forall n m cnot base_cnot, (unpadded_cnot base_cnot cnot 0 (m - n)) ∝ Cast _ _ (Nat.sub_0_r _) (Nat.sub_0_r _) (unpadded_cnot base_cnot cnot n m).
Proof.
  intros.
  prop_exists_nonzero 1%C; Msimpl.
  simpl_cast_semantics.
  apply unpadded_cnot_simpl_args_sem.
Qed.

Notation unpadded_cnot_t := (unpadded_cnot base_cnot _CNOT_).
Notation unpadded_cnot_b := (unpadded_cnot base_cnot_1 _CNOT_inv_).

Lemma unpadded_cnot_t_sem_equiv : forall n, / √ 2 .* uc_eval (@CNOT (S (S n)) 0 (S n)) = ZX_semantics (unpadded_cnot_t 0 (S (S n))).
Proof.
  intros.
  assert (HSwapSSn : forall n, uc_eval (@SWAP (S (S (S n))) 0 (S n)) = ZX_semantics (pad_bot_1 (A_Swap_ZX (S (S n))))).
  {
    intros.
    Opaque A_Swap_ZX.
    simpl.
    unfold pad_bot_1, pad_bot.
    rewrite swap_pad.
    simpl.
    restore_dims.
    simpl_cast_semantics.
    simpl.
    rewrite A_Swap_Correct.
    rewrite A_swap_sem_base.
    Msimpl.
    easy.
    Transparent A_Swap_ZX.
  }
  destruct n.
  - unfold unpadded_cnot.
    pose proof ZX_CNOT_l_is_cnot.
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
    Opaque A_Swap_ZX.
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
      replace (I 2 ⊗ X_semantics 2 1 0 × (Z_semantics 1 2 0 ⊗ I 2)) with (ZX_semantics (((Z) 1 2 0 ↕ — ⟷ (— ↕ (X) 2 1 0)))) by easy.
      rewrite ZX_CNOT_l_is_cnot.
      rewrite <- cnot_decomposition.
      rewrite 2 kron_assoc; try auto with wf_db.
      autorewrite with scalar_move_db.
      destruct n.
      * simpl.
        repeat rewrite kron_1_l; try auto with wf_db.
        repeat rewrite kron_1_r; try auto with wf_db.
      * replace (S n - n - 1)%nat with 0%nat by lia.
        apply Mscale_simplify; [ | easy ].
        rewrite nWire_semantics.
        repeat rewrite id_kron.
        replace (2 ^ S n + (2 ^ S n + 0))%nat with (2 * 2 ^ S n)%nat by lia.
        apply kron_simplify; try easy.
        Msimpl.
        simpl.
        easy.
    + apply HSwapSSn.
Qed.

Lemma unpadded_cnot_b_sem_equiv : forall n, / √ 2 .* uc_eval (@CNOT (S (S n)) (S n) 0) = ZX_semantics (unpadded_cnot_b 0 (S (S n))).
Proof.
  intros.
  assert (Hhh : hadamard ⊗ I 2 × (I 2 ⊗ hadamard) = hadamard ⊗ hadamard).
  {
    rewrite kron_mixed_product.
    Msimpl.
    easy.
  }
  assert (HSwapSSn : forall n, uc_eval (@SWAP (S (S (S n))) (S (S n)) 1) = I 2 ⊗ ZX_semantics (A_Swap_ZX (S (S n)))).
  {
    intros.
    rewrite swap_pad'.
    simpl.
    rewrite A_Swap_Correct.
    rewrite A_swap_sem_base.
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
    rewrite <- ZX_CNOT_l_is_cnot.
    simpl.
    easy.
  - rewrite <- (SWAP_extends_CNOT _ 1 _); try lia.
    Opaque A_Swap_ZX.
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
      rewrite nWire_semantics.
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
      rewrite <- ZX_CNOT_l_is_cnot.
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

Definition CNOT_n_m_ingest {dim} (n m : nat) : ZX (n + (S m - n) + (dim - (m + 1))) (n + (S m - n) + (dim - (m + 1))) :=
  (if n <? m then
    padbt (unpadded_cnot_t _ _)
  else 
    (nWire _)
  ).

Lemma CNOT_n_m_dim : forall {dim n m}, (n <? m = true)%nat -> (m <? dim = true)%nat -> (n + (S m - n) + (dim - (m + 1)))%nat = dim.
Proof.
  intros. apply Nat.ltb_lt in H, H0. lia.
Defined.

Lemma CNOT_m_n_dim : forall {dim n m}, (m <? n = true)%nat -> (n <? dim = true)%nat -> (m + (S n - m) + (dim - (n + 1)))%nat = dim.
Proof.
  intros. apply Nat.ltb_lt in H, H0. lia.
Defined.

Lemma CNOT_dim : forall {dim n m}, (m <? dim = true)%nat -> (n <? dim = true)%nat -> ((min m n) + (S (max m n) - (min m n)) + (dim - ((max m n) + 1)))%nat = dim.
Proof.
  intros. apply Nat.ltb_lt in H, H0. lia.
Defined.

Definition CNOT_m_n_ingest {dim} (n m : nat) : ZX (m + (S n - m) + (dim - (n + 1))) (m + (S n - m) + (dim - (n + 1))) :=
    (if m <? n then
      padbt (unpadded_cnot_b _ _)
    else 
      (nWire _)
    ).
  
Definition CNOT_ingest {dim} (n m : nat) : ZX dim dim.
Proof.
  destruct (Sumbool.sumbool_of_bool (n <? m)) as [ Hnltm | _ ].
  - destruct (Sumbool.sumbool_of_bool (m <? dim)) as [ Hmltdim | _ ].
    + apply (Cast _ _ (eq_sym (CNOT_n_m_dim Hnltm Hmltdim)) (eq_sym (CNOT_n_m_dim Hnltm Hmltdim))).
      apply CNOT_n_m_ingest.
    + apply (nWire dim).
  - destruct (Sumbool.sumbool_of_bool (m <? n)) as [ Hmltn | _ ].
    + destruct (Sumbool.sumbool_of_bool (n <? dim)) as [ Hnltdim | _ ].
      * apply (Cast _ _ (eq_sym (CNOT_m_n_dim Hmltn Hnltdim)) (eq_sym (CNOT_m_n_dim Hmltn Hnltdim))).
        apply CNOT_m_n_ingest.
      * apply (nWire dim).
    + apply (nWire dim).
Defined.

Lemma CNOT_n_m_equiv : forall dim n m, (n < dim)%nat -> (m < dim)%nat -> (n < m)%nat -> / √ 2 .* uc_eval (@CNOT dim n m) = ZX_semantics (@CNOT_n_m_ingest dim n m).
Proof.
  intros.
  rewrite denote_cnot.
  unfold ueval_cnot.
  unfold pad_ctrl.
  repeat rewrite unfold_pad.
  unfold CNOT_n_m_ingest.
  bdestruct (n <? m); 
    try (exfalso; lia).
  replace (n + (1 + (m - n - 1) + 1))%nat with (S m) by lia.
  bdestruct (S m <=? dim); try (exfalso; lia).
  rewrite pad_bot_top_semantics.
  repeat rewrite kron_assoc; try auto with wf_db; [| shelve].
  rewrite <- unpadded_cnot_simpl_args_sem.
  rewrite <- minus_Sn_m; try lia.
  destruct (m - n)%nat eqn:Hmn1; try (exfalso; lia).
  pose proof (unpadded_cnot_t_sem_equiv n0) as H_unpad_n0.
  rewrite <- H_unpad_n0.
  autorewrite with scalar_move_db.
  restore_dims.
  rewrite denote_cnot.
  unfold ueval_cnot.
  unfold pad_ctrl.
  repeat rewrite unfold_pad.
  unfold CNOT_n_m_ingest.
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

Lemma CNOT_m_n_equiv : forall dim n m, (n < dim)%nat -> (m < dim)%nat -> (m < n)%nat -> / √ 2 .* uc_eval (@CNOT dim n m) = ZX_semantics (@CNOT_m_n_ingest dim n m).
Proof.
  intros.
  rewrite denote_cnot.
  unfold ueval_cnot.
  unfold pad_ctrl.
  repeat rewrite unfold_pad.
  unfold CNOT_m_n_ingest.
  bdestruct (n <? m); 
    try (exfalso; lia).
  bdestruct (m <? n); 
    try (exfalso; lia).
  replace (m + (1 + (n - m - 1) + 1))%nat with (S n) by lia.
  bdestruct (S n <=? dim); try (exfalso; lia).
  rewrite pad_bot_top_semantics.
  repeat rewrite kron_assoc; try auto with wf_db; [| shelve].
  rewrite <- unpadded_cnot_simpl_args_sem.
  rewrite <- minus_Sn_m; try lia.
  destruct (n - m)%nat eqn:Hmn1; try (exfalso; lia).
  pose proof (unpadded_cnot_b_sem_equiv n0) as H_unpad_n0.
  rewrite <- H_unpad_n0.
  autorewrite with scalar_move_db.
  restore_dims.
  rewrite denote_cnot.
  unfold ueval_cnot.
  unfold pad_ctrl.
  repeat rewrite unfold_pad.
  unfold CNOT_n_m_ingest.
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

Lemma CNOT_ingest_correct : forall dim n m, (n < dim)%nat -> (m < dim)%nat -> (m <> n)%nat -> / √ 2 .* uc_eval (@CNOT dim n m) = ZX_semantics (@CNOT_ingest dim n m).
Proof.
  intros.
  unfold CNOT_ingest.
  destruct (dec (n <? m)).
  - destruct (dec (m <? dim)).
    + simpl_cast_semantics.
      rewrite CNOT_n_m_equiv; try easy.
      apply Nat.ltb_lt; easy.
    + apply Nat.ltb_nlt in e0.
      contradiction.
  - destruct (dec (m <? n)).
    + destruct (dec (n <? dim)).
      * simpl_cast_semantics.
        rewrite CNOT_m_n_equiv; try easy.
        apply Nat.ltb_lt; easy.
      * apply Nat.ltb_nlt in e1.
        contradiction.
    + exfalso.
      apply Nat.ltb_nlt in e, e0; lia.
Qed.

Definition Gate_ingest' dim (zx : ZX 1 1) n : ZX (n + 1 + (dim - (n + 1))) (n + 1 + (dim - (n + 1))) := padbt zx.

Lemma Gate_ingest_dim : forall n dim, (n <? dim = true)%nat -> ((n + 1 + (dim - (n + 1))) = dim)%nat.
Proof.
  intros. apply Nat.ltb_lt in H. lia.
Qed.

Definition Gate_ingest dim (zx : ZX 1 1) (n : nat) : ZX dim dim.
Proof.
  destruct (Sumbool.sumbool_of_bool (n <? dim)) as [ H | _ ].
  - apply (Cast _ _ (eq_sym (Gate_ingest_dim _ _ H)) (eq_sym (Gate_ingest_dim _ _ H))).
    apply Gate_ingest'.
    exact zx.
  - apply (nWire dim).
Defined.

Lemma Gate_ingest_correct : forall n dim (zx : ZX 1 1) (A : Matrix 2 2), (n < dim)%nat -> ZX_semantics zx = A -> pad_u dim n A = ZX_semantics (@Gate_ingest dim zx n).
Proof.
  intros.
  unfold Gate_ingest.
  destruct (dec (n <? dim)); [ | apply Nat.ltb_nlt in e; lia ].
  simpl_cast_semantics.
  unfold pad_u.
  rewrite unfold_pad.
  bdestruct (n + 1 <=? dim); try (exfalso; lia).
  simpl.
  rewrite 2 nWire_semantics.
  rewrite H0.
  easy.
Qed.

Definition H_ingest {dim} n := Gate_ingest dim □ n.
Definition X_ingest {dim} n := Gate_ingest dim (_X_) n.
Definition Rz_ingest {dim} n α := Gate_ingest dim (_Rz_ α) n.

Lemma H_ingest_correct : forall {dim} n, (n < dim)%nat -> @uc_eval dim (H n) = ZX_semantics (@H_ingest dim n).
Proof.
  intros.
  rewrite denote_H.
  apply Gate_ingest_correct; easy.
Qed.

Lemma X_ingest_correct : forall {dim} n, (n < dim)%nat -> @uc_eval dim (SQIR.X n) = ZX_semantics (@X_ingest dim n).
Proof.
  intros.
  rewrite denote_X.
  apply Gate_ingest_correct; [ easy | ].
  apply ZX_X_is_X.
Qed.

Lemma Rz_ingest_correct : forall {dim} n α, (n < dim)%nat -> @uc_eval dim (SQIR.Rz α n) = ZX_semantics (@Rz_ingest dim n α).
Proof.
  intros.
  rewrite denote_Rz.
  apply Gate_ingest_correct; [ easy | ].
  apply ZX_Rz_is_Rz.
Qed.

Lemma SKIP_is_nWire : forall dim, uc_eval (@SKIP (S dim)) = ZX_semantics (nWire (S dim)).
Proof.
  intros.
  rewrite denote_SKIP; try lia.
  rewrite nWire_semantics; easy.
Qed. 

Require Import VOQC.RzQGateSet.

Fixpoint ingest {dim} (u : ucom (RzQGateSet.U) dim) : ZX dim dim :=
  match u with
  | uapp1 URzQ_H n => H_ingest n
  | uapp1 URzQ_X n => X_ingest n
  | uapp1 (URzQ_Rz α) n => Rz_ingest n (Q2R α)
  | uapp2 _ n m => CNOT_ingest n m
  | useq u1 u2 => ingest u1 ⟷ ingest u2
  | _ => (nWire dim)
  end.

Fixpoint RzQToBaseUCom {dim} (u : ucom (RzQGateSet.U) dim) : base_ucom dim :=
  match u with
  | uapp1 URzQ_H n => SQIR.H n
  | uapp1 URzQ_X n => SQIR.X n
  | uapp1 (URzQ_Rz α) n => SQIR.Rz (Q2R α) n
  | uapp2 _ n m => SQIR.CNOT n m
  | useq u1 u2 => RzQToBaseUCom u1; RzQToBaseUCom u2
  | _ => SKIP
  end.

Theorem ingest_correct : forall {dim} (u : ucom (RzQGateSet.U) dim), uc_well_typed u -> exists (c : C), c .* uc_eval (RzQToBaseUCom u) = ZX_semantics (ingest u) /\ (c <> C0).
Proof.
  intros.
  induction u.
  - inversion H.
    simpl.
    specialize (IHu1 H2).
    specialize (IHu2 H3).
    destruct IHu1, IHu2.
    destruct H4, H5.
    exists (x * x0)%C; split; [ |  apply Cmult_neq_0; assumption ].
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
      apply SKIP_is_nWire.
  - inversion H.
    subst.
    simpl.
    exists (/ √2)%C; split; [ | apply nonzero_div_nonzero; apply Csqrt2_neq_0 ].
    rewrite CNOT_ingest_correct; congruence.
  - simpl.
    exists C1; split; [ | nonzero ].
    Msimpl.    
    destruct dim; [ exfalso; inversion H; lia | ].
    apply SKIP_is_nWire.
Qed.

  

Close Scope matrix_scope.
