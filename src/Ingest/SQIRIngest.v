Require Import SQIR.UnitarySem.
Require Import SQIR.Equivalences.
Require Import CoreData.
Require Import CoreRules.
Require Import Gates.
Require Import GateRules.
Require Import ZXPad.
Require Import QuantumLib.Quantum.

Search (uc_eval (CNOT _ _)).
Search "swap".

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
    solve_matrix.
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
Proof. solve_matrix. Qed.

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
  Search (— ↕ _).
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
    rewrite IHn.
    simpl.
    rewrite 2 denote_swap_alt.
    unfold ueval_swap.
    unfold pad_swap.
    unfold pad_ctrl.
    bdestruct (0 <? S n); [ clear H | easy ].
    bdestruct (0 <? S (S n)); [ clear H | easy ].
    bdestruct ((S n) <? 0); [ easy | clear H ].
    bdestruct (S (S n) <? 0); [ easy | clear H ].
    rewrite 4 unfold_pad.
    simpl.
    rewrite Nat.sub_0_r.
    rewrite Nat.add_1_r.
    rewrite Nat.leb_refl.
    rewrite Nat.sub_diag.
    Msimpl.
    rewrite Nat.add_0_r.
    rewrite swap_spec'.
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

Definition unpadded_cnot (cnot : ZX 2 2) (n m : nat) : ZX (m - n) (m - n) :=
  match (m - n)%nat with
  | S (S n0) => base_cnot n0 cnot
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

Lemma unpadded_cnot_t_sem_equiv : forall n, exists c, uc_eval (@CNOT (S (S (S n))) 0 (S (S n))) = c .* ZX_semantics (unpadded_cnot _CNOT_ 0 (S (S (S n)))) /\ c <> 0.
Proof.
  intros; eexists; split; [ | shelve ].
  rewrite <- (SWAP_extends_CNOT _ (S n) _); try lia.
  Opaque A_Swap_ZX.
  simpl.
  unfold pad_bot_1, pad_bot, pad_top.
  rewrite <- Mscale_mult_dist_r.
  rewrite <- Mscale_mult_dist_l.
  apply Mmult_simplify; [ | apply Mmult_simplify ].
  - rewrite swap_pad.
    simpl.
    restore_dims.
    simpl_cast_semantics.
    simpl.
    rewrite A_Swap_Correct.
    rewrite A_swap_sem_base.
    Msimpl.
    restore_dims.
    easy.
  - rewrite denote_cnot.
    rewrite unfold_ueval_cnot.
    bdestruct (S n <? S (S n)); try (lia; exfalso).
    rewrite unfold_pad.
    bdestruct (S n + (1 + (S (S n) - S n - 1) + 1) <=? S (S (S n)))%nat; [ | shelve ].
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
    rewrite <- (Mscale_1_l _ _ (_ ⊗ _)).
    destruct n.
    + simpl.
      repeat rewrite kron_1_l; try auto with wf_db.
      repeat rewrite kron_1_r; try auto with wf_db.
      apply Mscale_simplify; [ easy | ].
      rewrite Cinv_r; [ easy | ].
      apply Csqrt2_neq_0.
    + replace (S n - n - 1)%nat with 0%nat by lia.
      apply Mscale_simplify; [ | rewrite Cinv_r; [ easy | ]; apply Csqrt2_neq_0 ].
      rewrite nWire_semantics.
      repeat rewrite id_kron.
      replace (2 ^ S n + (2 ^ S n + 0))%nat with (2 * 2 ^ S n)%nat by lia.
      apply kron_simplify; try easy.
      Msimpl.
      simpl.
      easy.
    Unshelve.
  * apply Csqrt2_neq_0.
  * exfalso.
    simpl.
    fold Nat.add in H0.
    replace (n + (1 + (S (S n) - S n - 1) + 1) )%nat with (S (S n)) in H0 by lia.
    lia.
  - rewrite swap_pad.
    simpl.
    restore_dims.
    simpl_cast_semantics. 
    simpl.
    rewrite A_Swap_Correct.
    rewrite A_swap_sem_base.
    Msimpl.
    restore_dims.
    easy.
Qed.

Lemma lt_when_not_eq_gt : forall {m n}, (n <? m) = false -> (n =? m = false) -> (m <? n) = true.
Proof.
  intros.
  apply Nat.ltb_lt.
  apply Nat.ltb_ge in H.
  apply Nat.eqb_neq in H0.
  bdestruct (m <? n); lia.
Qed.

Definition translate_CNOT {dim} (n m : nat) : ZX (n + (m - n) + (dim - m)) (n + (m - n) + (dim - m)) :=
  if n =? m then 
    (nWire _)
  else 
    (if n <? m then
      pad_bot _ (pad_top _ (unpadded_cnot _CNOT_ _ _))
    else 
      pad_bot _ (pad_top _ (unpadded_cnot _CNOT_inv_ _ _))
    ).
Print translate_CNOT.

Lemma CNOT_equiv : forall dim n m, (n < dim)%nat -> (m < dim)%nat -> n <> m -> uc_eval (@CNOT dim n m) = ZX_semantics (@translate_CNOT dim n m).
Proof.
  intros.
  rewrite denote_cnot.
  unfold ueval_cnot.
  unfold pad_ctrl.
  repeat rewrite unfold_pad.
  unfold translate_CNOT.
  bdestruct (n =? m);
    bdestruct (n <? m); 
    bdestruct (m <? n); 
    try (exfalso; lia).
  - replace (n + (1 + (m - n - 1) + 1))%nat with (S m) by lia.
    bdestruct (S m <=? dim); try (exfalso; lia).
    rewrite pad_bot_top_semantics.
    repeat rewrite kron_assoc; try auto with wf_db; [|shelve].
    replace (2 ^ (m - n) * 2 ^ (dim - m))%nat with (2 ^ (1 + (m - n - 1) + 1) * 2 ^ (dim - S m))%nat by shelve.
    apply kron_simplify; try easy.
    repeat rewrite <- kron_assoc; try auto with wf_db.
Abort.



        


Close Scope matrix_scope.
