Require Import ZX.
Require Import Gates.
Require Import GateRules.
Require Import Rules.
Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.VectorStates.
From VyZX Require Import Proportional.

Local Open Scope ZX_scope.

Module ColorSwapDef.

  Fixpoint ColorSwap {nIn nOut} (zx : ZX nIn nOut) : ZX nIn nOut := 
    match zx with
    | X_Spider n m α  => Z_Spider n m α
    | Z_Spider n m α  => X_Spider n m α
    | zx1 ↕ zx2   => (⊙ zx1) ↕ (⊙ zx2)
    | zx1 ⟷ zx2 => (⊙ zx1) ⟷ (⊙ zx2)
    | otherwise => otherwise
    end.

End ColorSwapDef.

Definition bi_hadamard {nIn nOut} (zx : ZX nIn nOut) : ZX nIn nOut :=
  (nIn ↑ ZX_H) ⟷ zx ⟷ (nOut ↑ ZX_H).


Lemma hadamard_color_change_Z : forall {nIn nOut} α, 
  (nIn ↑ □) ⟷ (Z_Spider nIn nOut α) ∝ (X_Spider nIn nOut α) ⟷ (nOut ↑ □).
Proof.
  intros.
  prop_exist_non_zero (Cexp (PI / 4 * (INR nIn - INR nOut))).
  simpl.
  rewrite 2 nStack1_n_kron.
  rewrite ZX_H_is_H.
  repeat rewrite Mscale_kron_n_distr_r.
  repeat rewrite Cexp_pow; simpl.
  rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_r.
  repeat rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  restore_dims.
  rewrite <- Cexp_add.
  rewrite <- Rmult_plus_distr_l.
  replace ((INR nIn - INR nOut + INR nOut))%R with (INR nIn) by lra.
  apply Mscale_simplify; try reflexivity.
  unfold X_semantics.
  rewrite <- 2 Mmult_assoc.
  rewrite kron_n_mult.
  rewrite MmultHH.
  rewrite kron_n_I.
  rewrite Mmult_1_l; try auto with wf_db.
Qed.

Lemma hadamard_color_change_X : forall {nIn nOut} α, 
  (nIn ↑ □) ⟷ (X_Spider nIn nOut α) ∝ (Z_Spider nIn nOut α) ⟷ (nOut ↑ □).
Proof.
  intros.
  prop_exist_non_zero (Cexp (PI / 4 * (INR nIn - INR nOut))).
  simpl.
  rewrite 2 nStack1_n_kron.
  rewrite ZX_H_is_H.
  repeat rewrite Mscale_kron_n_distr_r.
  repeat rewrite Cexp_pow; simpl.
  rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_r.
  repeat rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  restore_dims.
  rewrite <- Cexp_add.
  rewrite <- Rmult_plus_distr_l.
  replace ((INR nIn - INR nOut + INR nOut))%R with (INR nIn) by lra.
  apply Mscale_simplify; try reflexivity.
  unfold X_semantics.
  rewrite 2 Mmult_assoc.
  rewrite kron_n_mult.
  rewrite MmultHH.
  rewrite kron_n_I.
  rewrite Mmult_1_r; try auto with wf_db.
Qed.

Lemma bi_hadamard_color_change_Z : forall {nIn nOut} α, 
  (nIn ↑ □) ⟷ (Z_Spider nIn nOut α) ⟷ (nOut ↑ □) ∝ 
  X_Spider nIn nOut α.
Proof.
  intros.
  rewrite hadamard_color_change_Z.
  rewrite ZX_Compose_assoc.
  rewrite nH_composition.
  rewrite nwire_r.
  reflexivity.
Qed.

Lemma bi_hadamard_color_change_X : forall {nIn nOut} α, 
  (nIn ↑ □) ⟷ (X_Spider nIn nOut α) ⟷ (nOut ↑ □) ∝ 
  Z_Spider nIn nOut α.
Proof.
  intros.
  rewrite hadamard_color_change_X.
  rewrite ZX_Compose_assoc.
  rewrite nH_composition.
  rewrite nwire_r.
  reflexivity.
Qed.

Lemma ColorSwap_isBiHadamard : forall {nIn nOut} (zx : ZX nIn nOut),
    ⊙ zx ∝ BiHadamard zx.
Proof.
  intros; unfold BiHadamard.
  induction zx.
  - remove_empty.
    reflexivity.
  - rewrite bi_hadamard_color_change_X.
    reflexivity.
  - rewrite bi_hadamard_color_change_Z.
    reflexivity.
  - remove_empty.
    simpl.
    remove_empty.
    rewrite stack_wire_pad_l_r.
    rewrite nWire_1_Wire.
    rewrite ZX_Stack_Compose_distr.
    rewrite <- ZX_Compose_assoc.
    rewrite <- H_comm_cap.
    rewrite ZX_Compose_assoc.
    rewrite  <- (ZX_Stack_Compose_distr ZX_H ZX_H).
    rewrite ZX_H_H_is_Wire.
    rewrite Wire_Compose.
    rewrite <- nWire_2_Stack_Wire.
    rewrite nwire_r.
    reflexivity.
  - remove_empty.
    simpl.
    remove_empty.
    rewrite stack_wire_pad_l_r.
    rewrite nWire_1_Wire.
    rewrite ZX_Stack_Compose_distr.
    rewrite ZX_Compose_assoc.
    rewrite H_comm_cup.
    rewrite <- ZX_Compose_assoc.
    rewrite <- (ZX_Stack_Compose_distr — —).
    rewrite ZX_H_H_is_Wire.
    rewrite Wire_Compose.
    rewrite <- nWire_2_Stack_Wire.
    rewrite nwire_l.
    reflexivity.
  - simpl.
    remove_empty.
    symmetry.
    prop_exist_non_zero (4 *
    (Cexp (PI / 4) * / √ 2 * (Cexp (PI / 4) * / √ 2) *
     (Cexp (PI / 4) * / √ 2 * (Cexp (PI / 4) * / √ 2)))).
    Msimpl.
    simpl.
    rewrite ZX_H_is_H.
    solve_matrix.
    apply Cmult_neq_0; [ nonzero | ].
    apply Cmult_neq_0; apply Cmult_neq_0; apply Cmult_neq_0; try nonzero.
    all: apply nonzero_div_nonzero; nonzero.
  - simpl.
    rewrite IHzx1.
    rewrite IHzx2.
    rewrite 2 nH_Plus_Stack.
    rewrite 2 ZX_Stack_Compose_distr.
    reflexivity.
  - simpl.
    rewrite IHzx1.
    rewrite IHzx2.
    rewrite 3 ZX_Compose_assoc.
    rewrite <- (ZX_Compose_assoc (nMid ↑ □)).
    rewrite nH_composition.
    rewrite nwire_l.
    rewrite 2 ZX_Compose_assoc.
    reflexivity.
Qed.

Fixpoint LeftColumnOutput {nIn nOut} (zx : ZX nIn nOut) : nat :=
  match zx with
  | Empty => 0
  | Z_Spider nIn nOut α => nOut 
  | X_Spider nIn nOut α => nOut
  | Cap => 2
  | Cup => 0
  | Swap => 2
  | Stack zx1 zx2 => LeftColumnOutput zx1 + LeftColumnOutput zx2
  | Compose zx1 zx2 => LeftColumnOutput zx1
  end.

Fixpoint LeftColumn {nIn nOut} (zx : ZX nIn nOut) :
  ZX nIn (LeftColumnOutput zx) :=
  match zx as z in (ZX zIn zOut) return (ZX zIn (LeftColumnOutput z)) with
  | ⦰ => ⦰
  | X_Spider nIn0 nOut0 α => X_Spider nIn0 nOut0 α
  | Z_Spider nIn0 nOut0 α => Z_Spider nIn0 nOut0 α
  | ⊂ => ⊂
  | ⊃ => ⊃
  | ⨉ => ⨉
  | Stack zx0 zx1 =>
       LeftColumn zx0 ↕ LeftColumn zx1
  | Compose zx0 zx1 =>
      LeftColumn zx0
  end.

Fixpoint ShaveLeft {nIn nOut} (zx : ZX nIn nOut) : ZX (LeftColumnOutput zx) nOut :=
  match zx as z in (ZX zIn zOut) return (ZX (LeftColumnOutput z) zOut) with
  | X_Spider nIn0 nOut0 α | Z_Spider nIn0 nOut0 α => nOut0 ↑ —
  | ⦰ | ⊃ => ⦰
  | Stack zx0 zx1 => ShaveLeft zx0 ↕ ShaveLeft zx1
  | Compose zx0 zx1 => ShaveLeft zx0 ⟷ zx1
  | _ => 2 ↑ —
  end.

Lemma LeftColumnComposeShaveLeft {nIn nOut} : forall (zx : ZX nIn nOut),
  zx ∝ (LeftColumn zx) ⟷ (ShaveLeft zx).
Proof.
  induction zx.
  - remove_empty. reflexivity.
  - simpl. remove_wire. reflexivity.
  - simpl. remove_wire. reflexivity.
  - simpl. remove_empty. 
    rewrite <- nWire_2_Stack_Wire.
    remove_wire.
    reflexivity.
  - simpl. remove_empty. reflexivity.
  - simpl. remove_empty.
    rewrite <- nWire_2_Stack_Wire.
    remove_wire.
    reflexivity.
  - simpl.
    rewrite <- ZX_Stack_Compose_distr.
    rewrite <- IHzx1.
    rewrite <- IHzx2.
    reflexivity.
  - simpl.
    rewrite <- ZX_Compose_assoc.
    rewrite <- IHzx1.
    reflexivity.
Qed.


