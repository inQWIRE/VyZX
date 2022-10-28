From VyZX Require Export ZXCore.
From VyZX Require Import SemanticCore.
From VyZX Require Export Proportional.

Local Open Scope ZX_scope.

(* Associativity *)

Lemma ZX_Compose_assoc : forall {n m0 m1 o}
  (zx1 : ZX n m0) (zx2 : ZX m0 m1) (zx3 : ZX m1 o),
  zx1 ⟷ zx2 ⟷ zx3 ∝ zx1 ⟷ (zx2 ⟷ zx3).
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  Msimpl.
  rewrite Mmult_assoc.
  lma.
Qed.

Lemma ZX_Stack_assoc : 
  forall {n0 n1 n2 m0 m1 m2}
    (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2),
    (zx0 ↕ zx1) ↕ zx2 ∝ Cast ((n0 + n1) + n2) ((m0 + m1) + m2) (eq_sym(Nat.add_assoc _ _ _)) (eq_sym(Nat.add_assoc _ _ _)) 
                        (zx0 ↕ (zx1 ↕ zx2)).
Proof.                                                      
  intros.
  prop_exist_non_zero 1.  
  simpl.
  Msimpl.
  rewrite kron_assoc; auto with wf_db.
Qed.

Lemma cast_id :
  forall {n m} (zx : ZX n m),
    zx ∝ Cast n m eq_refl eq_refl zx.
Proof.
  intros; subst.
  prop_exist_non_zero 1.
  simpl; lma.
Qed.

Lemma cast_contract :
  forall {n0 m0 n1 m1 n2 m2} prfn01 prfm01 prfn12 prfm12 (zx : ZX n0 m0),
    Cast n2 m2 prfn12 prfm12 
      (Cast n1 m1 prfn01 prfm01
        zx) ∝
    Cast n2 m2 (eq_trans prfn12 prfn01) (eq_trans prfm12 prfm01) 
      zx.
Proof.
  intros; subst.
  prop_exist_non_zero 1.
  simpl; lma.
Qed.

Lemma cast_swap :
  forall {n0 m0 n1 m1} prfn prfm (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
    Cast n1 m1 prfn prfm zx0 ∝ zx1 <->
    zx0 ∝ Cast n0 m0 (eq_sym prfn) (eq_sym prfm) zx1.
Proof.
  intros.
  split; intros.
  - subst.
    rewrite <- H.
    rewrite <- 2 cast_id.
    easy.
  - subst.
    rewrite H.
    rewrite <- 2 cast_id.
    easy.
Qed.

Lemma cast_backwards :
  forall {n0 m0 n1 m1} prfn prfm (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
    Cast n1 m1 prfn prfm zx0 ∝ zx1 <->
    Cast n0 m0 (eq_sym prfn) (eq_sym prfm) zx1 ∝ zx0.
Proof.
  intros.
  split; symmetry; subst. 
  apply cast_swap; easy.
  rewrite <- H.
  rewrite <- 2 cast_id.
  easy.
Qed.

Lemma Test : forall n m (zx0 : ZX n m) (zx1 : ZX n m),
  zx0 ∝ zx1.
Proof.
  intros.
  unfold proportional.
  replace n with (S n - 1)%nat at 2 by lia.
  replace m with (S m - 1)%nat at 2 by lia.
Admitted.

(* Distributivity *)

Lemma ZX_Stack_Compose_distr : 
  forall {n1 m1 o2 n3 m2 o4}
    (zx1 : ZX n1 m1) (zx2 : ZX m1 o2) (zx3 : ZX n3 m2) (zx4 : ZX m2 o4),
    (zx1 ⟷ zx2) ↕ (zx3 ⟷ zx4) ∝ (zx1 ↕ zx3) ⟷ (zx2 ↕ zx4).
Proof.
  intros.
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
    prop_exist_non_zero 1.
  simpl.
  rewrite kron_1_l; try auto with wf_db.
  lma.
Qed.

Lemma ZX_Stack_Empty_r : forall {n m : nat} (zx : ZX n m),
  zx ↕ ⦰ ∝ 
    Cast (n + 0) (m + 0) (Nat.add_0_r _) (Nat.add_0_r _) zx.
Proof.
  intros.
  prop_exist_non_zero 1.
  simpl.
  Msimpl.
  reflexivity.
Qed.

Lemma ZX_Compose_Empty_r : forall {nIn} (zx : ZX nIn 0),
  zx ⟷ ⦰ ∝ zx.
Proof. 
  intros.
    prop_exist_non_zero 1.
  simpl.
  Msimpl.
  reflexivity.
Qed.
  
Lemma ZX_Compose_Empty_l : forall {nOut} (zx : ZX 0 nOut),
  ⦰ ⟷ zx ∝ zx.
Proof. 
  intros.
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
    prop_exist_non_zero 1.
  Msimpl.
  simpl.
  rewrite nWire_semantics.
Admitted.

Lemma SpiderFusion : forall top mid bot input output α β,
  (nWire top ↕ Z input (S mid + bot) α) ⟷  
    (Cast (top + (S mid + bot)) (output + bot) (Nat.add_assoc _ _ _) eq_refl ((Z (top + S mid) output β) ↕ nWire bot)) ∝
    Z (top + input) (output + bot) β.
Proof.
  intros.
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
Admitted.


