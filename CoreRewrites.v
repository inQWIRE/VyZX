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
  forall {n1 m1 o2 n3 m2 o4}
    (zx1 : ZX n1 m1) (zx2 : ZX m1 o2) (zx3 : ZX n3 m2) (zx4 : ZX m2 o4),
    (zx1 ⟷ zx2) ↕ (zx3 ⟷ zx4) ∝ (zx1 ↕ zx3) ⟷ (zx2 ↕ zx4).
Proof.
  intros.
  prep_proportional.
  prop_exist_non_zero 1.
  Msimpl.
  simpl.
  show_dimensions.
  repeat rewrite Nat.pow_add_r.
  rewrite kron_mixed_product.
  reflexivity.
Qed.

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
Admitted.


