From VyZX Require Export ZXCore.
From VyZX Require Import SemanticCore.
From VyZX Require Export Proportional.
From VyZX Require Export CastRules.
From VyZX Require Export SpiderInduction.

Local Open Scope ZX_scope.

(* Associativity *)

Lemma ZX_Compose_assoc : forall {n m0 m1 o}
  (zx1 : ZX n m0) (zx2 : ZX m0 m1) (zx3 : ZX m1 o),
  zx1 ⟷ zx2 ⟷ zx3 ∝ zx1 ⟷ (zx2 ⟷ zx3).
Proof.
  intros.
  prop_exists_nonzero 1.
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
  prop_exists_nonzero 1.  
  simpl.
  Msimpl.
  rewrite (@Cast_semantics (n0 + (n1 + n2)) _ ((n0 + n1) + n2)%nat).
  rewrite kron_assoc; auto with wf_db.
Qed.

Lemma ZX_Stack_assoc_back : 
  forall {n0 n1 n2 m0 m1 m2}
    (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2),
    zx0 ↕ (zx1 ↕ zx2) ∝ Cast (n0 + (n1 + n2)) (m0 + (m1 + m2)) (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _) 
                        ((zx0 ↕ zx1) ↕ zx2).
Proof.                                                      
  intros.
  prop_exists_nonzero 1.  
  simpl.
  Msimpl.
  rewrite (@Cast_semantics ((n0 + n1) + n2) _ (n0 + (n1 + n2))%nat).
  simpl; restore_dims.
  rewrite kron_assoc; auto with wf_db.
Qed.

(* Distributivity *)

Lemma ZX_Stack_Compose_distr : 
  forall {n1 m1 o2 n3 m2 o4}
    (zx1 : ZX n1 m1) (zx2 : ZX m1 o2) (zx3 : ZX n3 m2) (zx4 : ZX m2 o4),
    (zx1 ⟷ zx2) ↕ (zx3 ⟷ zx4) ∝ (zx1 ↕ zx3) ⟷ (zx2 ↕ zx4).
Proof.
  intros.
  prop_exists_nonzero 1.
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
  prop_exists_nonzero 1.
  simpl.
  rewrite kron_1_l; try auto with wf_db.
  lma.
Qed.

Lemma ZX_Stack_Empty_r : forall {n m : nat} (zx : ZX n m),
  zx ↕ ⦰ ∝ 
    Cast (n + 0) (m + 0) (Nat.add_0_r _) (Nat.add_0_r _) zx.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  Msimpl.
  rewrite (@Cast_semantics n m (n + 0) (m + 0)).
  reflexivity.
Qed.

Lemma ZX_Compose_Empty_r : forall {nIn} (zx : ZX nIn 0),
  zx ⟷ ⦰ ∝ zx.
Proof. 
  intros.
  prop_exists_nonzero 1.
  simpl.
  Msimpl.
  reflexivity.
Qed.
  
Lemma ZX_Compose_Empty_l : forall {nOut} (zx : ZX 0 nOut),
  ⦰ ⟷ zx ∝ zx.
Proof. 
  intros.
  prop_exists_nonzero 1.
  simpl. 
  Msimpl.
  reflexivity.
Qed.

Lemma nwire_removal_l: forall {n nOut} (zx : ZX n nOut), (n ↑ —) ⟷ zx ∝ zx.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  rewrite nWire_semantics.
  Msimpl.
  reflexivity.
Qed.

Lemma wire_removal_l : forall {nOut} (zx : ZX 1 nOut), — ⟷ zx ∝ zx.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  Msimpl.
  reflexivity.
Qed.

Lemma wire_removal_r : forall {nIn} (zx : ZX nIn 1), zx ⟷ — ∝ zx.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  Msimpl.
  reflexivity.
Qed.

Lemma nwire_removal_r: forall {n nIn} (zx : ZX nIn n), zx ⟷ (n ↑ —) ∝ zx.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  replace (n ↑ —) with (nWire n) by easy.
  rewrite nWire_semantics.
  Msimpl.
  reflexivity.
Qed.

Lemma nwire_stack_compose_topleft : forall {topIn botIn topOut botOut} (zx0 : ZX botIn botOut) (zx1 : ZX topIn topOut),
  ((nWire topIn) ↕ zx0) ⟷ (zx1 ↕ (nWire botOut)) ∝ 
  (zx1 ↕ zx0).
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  repeat rewrite nWire_semantics.
  Msimpl.
  easy.
Qed.

Lemma nwire_stack_compose_botleft : forall {topIn botIn topOut botOut} (zx0 : ZX botIn botOut) (zx1 : ZX topIn topOut),
  (zx0 ↕ (nWire topIn)) ⟷ ((nWire botOut) ↕ zx1) ∝ 
  (zx0 ↕ zx1).
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  repeat rewrite nWire_semantics.
  Msimpl.
  easy.
Qed.

Lemma Z_0_is_wire : Z 1 1 0 ∝ —.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  unfold Z_semantics.
  autorewrite with Cexp_db.
  solve_matrix.
  assert (forall x y, (x =? 0) && (y =? 0) = (x =? y) && (x <=? 0))%nat.
  {
    intros.
    bdestruct (x0 <=? 0).
    - apply Nat.le_0_r in H; subst.
      rewrite Nat.eqb_refl, andb_true_r, andb_true_l.
      destruct y0; easy.
    - rewrite andb_false_r.
      destruct x0; easy.
  }
  rewrite H.
  easy.
Qed.

Lemma Z_2_0_0_is_cap : Z 2 0 0 ∝ ⊃.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
  apply Cexp_0.
Qed.

Lemma Z_0_2_0_is_cup : Z 0 2 0 ∝ ⊂.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
  apply Cexp_0.
Qed.

Lemma yank_r : 
  (⊂ ↕ —) ⟷ (— ↕ ⊃) ∝ —.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
Qed.

Lemma yank_l : 
  (— ↕ ⊂) ⟷ (⊃ ↕ —) ∝ —.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
Qed.

Lemma X_0_is_wire : X 1 1 0 ∝ —.
Proof.
  (* TODO: Waiting on colorswap *)
Admitted.

(* Automation *)

#[export] Hint Rewrite 
  (fun n => @ZX_Compose_Empty_l n)
  (fun n => @ZX_Compose_Empty_r n)
  (fun n => @ZX_Stack_Empty_l n)
  (fun n => @ZX_Stack_Empty_r n) 
  (fun n => @nwire_removal_l n) 
  (fun n => @nwire_removal_r n)
  @wire_removal_l
  @wire_removal_r
  X_0_is_wire
  Z_0_is_wire
  (fun n m o p => @nwire_stack_compose_topleft n m o p)
  (fun n m o p => @nwire_stack_compose_botleft n m o p)
  : cleanup_zx_db.

Ltac cleanup_zx := autorewrite with cleanup_zx_db.

Lemma wire_to_nWire : 
  — ∝ nWire 1.
Proof.
  simpl.
  cleanup_zx.
  simpl_casts.
  easy.
Qed.

Lemma nStack1_r_dim : forall n,
  (S n = n + 1)%nat.
Proof. lia. Qed.

Lemma nStack1_l : forall n (zx : ZX 1 1),
  (S n) ↑ zx ∝ zx ↕ (n ↑ zx).
Proof. easy. Qed.

Lemma nStack1_r : forall n (zx : ZX 1 1), 
  (S n) ↑ zx ∝ 
  Cast (S n) (S n) (nStack1_r_dim _) (nStack1_r_dim _) ((n ↑ zx) ↕ zx).
Proof.
  induction n.
  - intros.
    simpl.
    simpl_casts.
    cleanup_zx.
    simpl_casts.
    easy.
  - intros.
    rewrite nStack1_l.
    rewrite IHn at 1.
    rewrite cast_stack_r.
    simpl.
    simpl_casts.
    rewrite ZX_Stack_assoc_back.
    simpl_casts.
    easy.
Qed.

Lemma stack_wire_distribute_l : forall {n m o} (zx0 : ZX n m) (zx1 : ZX m o),
  — ↕ (zx0 ⟷ zx1) ∝ (— ↕ zx0) ⟷ (— ↕ zx1).
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl; Msimpl; easy.
Qed.

Lemma stack_wire_distribute_r : forall {n m o} (zx0 : ZX n m) (zx1 : ZX m o),
  (zx0 ⟷ zx1) ↕ —  ∝ (zx0 ↕ —) ⟷ (zx1 ↕ —).
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl; Msimpl; easy.
Qed.

Lemma stack_nwire_distribute_l : forall {n m o p} (zx0 : ZX n m) (zx1 : ZX m o),
  nWire p ↕ (zx0 ⟷ zx1) ∝ (nWire p ↕ zx0) ⟷ (nWire p ↕ zx1).
Proof.
  intros.
  induction p.
  - cleanup_zx.
    easy.
  - rewrite nStack1_l.
    rewrite (ZX_Stack_assoc — (nWire p) zx0).
    rewrite (ZX_Stack_assoc — (nWire p) zx1).
    simpl_casts.
    rewrite <- (stack_wire_distribute_l (nWire p ↕ zx0) (nWire p ↕ zx1)).
    rewrite <- IHp.
    rewrite ZX_Stack_assoc_back.
    simpl_casts.
    easy.
Qed.

Lemma stack_nwire_distribute_r : forall {n m o p} (zx0 : ZX n m) (zx1 : ZX m o),
  (zx0 ⟷ zx1) ↕ nWire p ∝ (zx0 ↕ nWire p) ⟷ (zx1 ↕ nWire p).
Proof.
  intros.
  induction p.
  - cleanup_zx.
    eapply (cast_diagrams n o).
    repeat rewrite cast_contract.
    rewrite cast_id.
    rewrite cast_compose_distribute.
    simpl_casts.
    erewrite (cast_compose_mid m _ ($ n, m + 0 $ zx0)).
    simpl_casts.
    easy.
    Unshelve.
    all: lia.
  - rewrite nStack1_r.
    repeat rewrite cast_stack_r.
    eapply (cast_diagrams (n + (p + 1)) (o + (p + 1))).
    rewrite cast_contract.
    rewrite cast_id.
    rewrite cast_compose_distribute.
    simpl_casts.
    erewrite (cast_compose_mid (m + (p + 1)) _ ($ n + (p + 1), m + (S p) $ zx0 ↕ (nWire p ↕ —))).
    simpl_casts.
    rewrite 3 ZX_Stack_assoc_back.
    eapply (cast_diagrams (n + p + 1) (o + p + 1)).
    rewrite cast_contract.
    rewrite cast_id.
    rewrite cast_compose_distribute.
    rewrite 2 cast_contract.
    erewrite (cast_compose_mid (m + p + 1) _ ($ n + p + 1, m + (p + 1) $ zx0 ↕ nWire p ↕ —)).
    simpl_casts.
    rewrite <- stack_wire_distribute_r.
    rewrite <- IHp.
    easy.
    Unshelve.
    all: lia.
Qed.

(* Lemma nWire_collapse_r : forall {n0 n1 m1} (zx0 : ZX n0 0) (zx1 : ZX n1 m1),
   (zx0 ↕ nWire n1) ⟷ zx1 ∝ zx0 ↕ zx1. *)

Lemma nstack1_split : forall n m (zx : ZX 1 1),
  (n + m) ↑ zx ∝ 
  (n ↑ zx) ↕ (m ↑ zx).
Proof.
  intros.
  induction n.
  - simpl. cleanup_zx. easy.
  - simpl.
    rewrite IHn.
    rewrite (ZX_Stack_assoc zx).
    simpl_casts.
    reflexivity.
Qed.

Lemma nstack_split : forall n m {nIn mOut} (zx : ZX nIn mOut),
  (n + m) ⇑ zx ∝ 
  Cast _ _ (Nat.mul_add_distr_r _ _ _) (Nat.mul_add_distr_r _ _ _) ((n ⇑ zx) ↕ (m ⇑ zx)).
Proof.
  intros.
  dependent induction n.
  - simpl. simpl_casts.
    cleanup_zx. easy.
  - simpl.
    rewrite IHn.
    simpl.
    simpl_casts.
    rewrite ZX_Stack_assoc.
    simpl_casts.
    reflexivity.
Qed.

Lemma Grow_Z_Left : forall (nIn nOut : nat) α,
  Z (S (S nIn)) nOut α ∝  
  (Z 2 1 0) ↕ (nWire nIn) ⟷ (Z (S nIn) nOut α).
Proof.
  intros.
  replace α%R with (0 + α)%R at 1 by lra.
  simpl.
  rewrite <- Z_spider_1_1_fusion.
  simpl.
  rewrite Grow_Z_Left_2_1.
  rewrite ZX_Compose_assoc.
  rewrite Z_spider_1_1_fusion.
  replace (0+α)%R with α%R by lra.
  reflexivity.
Qed.

Lemma Grow_Z_Right : forall (nIn nOut : nat) α,
  Z nIn (S (S nOut)) α ∝ 
  (Z nIn (S nOut) α) ⟷ ((Z_Spider 1 2 0) ↕ (nWire nOut)).
Proof.
  intros.
  replace α%R with (0 + α)%R at 1 by lra.
  rewrite <- Z_spider_1_1_fusion.
  simpl.
  rewrite Grow_Z_Right_1_2.
  rewrite <- ZX_Compose_assoc.
  rewrite Z_spider_1_1_fusion.
  replace (0+α)%R with α%R by lra.
  reflexivity.
Qed.

Lemma WrapOver_L : forall n m α,
  Z (S n) m α ∝ (Wire ↕ Z n (S m) α) ⟷  (Cup ↕ nWire m).
Proof.
  induction m.
  - intros.
    rewrite <- WrapOver_Right_Top_0.
    cleanup_zx.
    simpl_casts.
    reflexivity.
  - intros.
    destruct m.
    + rewrite <- WrapOver_Right_Top_Base.
      rewrite wire_to_nWire at 2.
      reflexivity.
    + rewrite Grow_Z_Right.
      rewrite IHm.
      rewrite <- (ZX_Stack_Empty_l (Z 1 2 0 ↕ (m ↑ —))).
      fold (nWire m).
      replace ⦰ with (nWire 0) by auto.
      specialize (nwire_stack_compose_botleft ⊃ (Z 1 2 0 ↕ nWire m)); intros.
      simpl in H.
      rewrite ZX_Compose_assoc.
      rewrite H.
      clear H.
      specialize (nwire_stack_compose_topleft (Z 1 2 0 ↕ nWire m) ⊃); intros.
      rewrite <- H.
      clear H.
      rewrite <- ZX_Compose_assoc.
      rewrite Grow_Z_Right.
      rewrite ZX_Compose_assoc.
      replace (nWire 2) with (— ↕ (— ↕ ⦰)) by auto.
      cleanup_zx.
      simpl_casts.
      rewrite (ZX_Stack_assoc — — _).
      simpl_casts.
      rewrite <- ZX_Compose_assoc.
      rewrite <- (stack_wire_distribute_l 
        ((Z) n (S m) α ⟷ ((Z) 1 2 0 ↕ (m ↑ —))) 
        (— ↕ ((Z) 1 2 0 ↕ nWire m))).
      rewrite ZX_Compose_assoc.
      fold (nWire m).
      rewrite ZX_Stack_assoc_back.
      simpl_casts.
      rewrite <- (ZX_Stack_Compose_distr (Z 1 2 0) (— ↕ Z 1 2 0) (nWire m) (nWire m)).
      rewrite <- Grow_Z_Right_Bot_1_2_Base.
      rewrite Grow_Z_Right.
      rewrite ZX_Stack_Compose_distr.
      rewrite <- ZX_Compose_assoc.
      rewrite <- Grow_Z_Right.
      rewrite (ZX_Stack_assoc (Z 1 2 0) (1 ↑ —) (m ↑ —)).
      simpl_casts.
      rewrite <- nstack1_split.
      rewrite <- (Grow_Z_Right n (S m)).
      easy.
Qed.

Ltac transpose_of H := intros; apply transpose_diagrams; simpl; apply H.
Ltac adjoint_of H := intros; apply adjoint_diagrams; simpl; apply H.


Lemma WrapOver_R : forall n m α,
  Z n (S m) α ∝ (Cap ↕ nWire n) ⟷ (Wire ↕ Z (S n) m α).
Proof. 
  intros. apply transpose_diagrams. simpl. 
  rewrite nstack1_transpose. rewrite transpose_wire.
  apply WrapOver_L.
Qed.

Lemma Z_2_1_through_cap : forall α, 
  Z 2 1 α ↕ — ⟷ ⊃ ∝ (— ↕ — ↕ Z 1 2 α) ⟷  (— ↕ ⊃ ↕ —) ⟷ ⊃.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  Msimpl.
  solve_matrix.
Qed.

Lemma Grow_Z_Left_1_2 : forall {n m} α,
  Z (S n) (S m) α ∝ 
  (Z 1 2 0 ↕ nWire n) ⟷ (— ↕ Z (S n) m α).
Proof.
  intros.
  rewrite WrapOver_R.
  rewrite Grow_Z_Left.
  rewrite (nstack1_split 1 n).
  fold (nWire n). fold (nWire 1).
  rewrite stack_wire_distribute_l.
  rewrite <- ZX_Compose_assoc.
  rewrite (ZX_Stack_assoc_back ⊂ (nWire 1) (nWire n)).
  rewrite (ZX_Stack_assoc_back — (Z 2 1 0) (nWire n)).
  simpl_casts.
  rewrite <- (ZX_Stack_Compose_distr (⊂ ↕ nWire 1) (— ↕ Z 2 1 0) (nWire n) (nWire n)).
  rewrite <- WrapOver_R.
  cleanup_zx.
  easy.
Qed.

Lemma Grow_Z_Right_2_1 : forall {n m} α,
  Z (S n) (S m) α ∝ 
  (— ↕ Z n (S m) α) ⟷ (Z 2 1 0 ↕ nWire m).
Proof.
  intros.
  apply transpose_diagrams.
  simpl.
  rewrite nstack1_transpose.
  rewrite transpose_wire.
  apply Grow_Z_Left_1_2.
Qed.

Lemma Grow_Z_Left_Bot_2_1 : forall {n m} α,
  Z (n + 2) m α ∝ 
  (nWire n ↕ Z 2 1 0) ⟷ (Z (n + 1) m α).
Proof.
  intros.
  induction n.
  - simpl.
    cleanup_zx.
    rewrite Z_spider_1_1_fusion.
    rewrite Rplus_0_l.
    reflexivity.
  - destruct n.
    + simpl.
      cleanup_zx.
      simpl_casts.
      rewrite (WrapOver_L 1 m).
      rewrite <- ZX_Compose_assoc.
      rewrite <- stack_wire_distribute_l.
      rewrite Z_spider_1_1_fusion.
      rewrite Rplus_0_l.
      rewrite <- WrapOver_L.
      easy.
    + rewrite (Grow_Z_Left (n + 1)).
      rewrite <- ZX_Compose_assoc.
      rewrite (nstack1_split 2 n).
      rewrite (ZX_Stack_assoc (nWire 2) (nWire n) (Z 2 1 0)).
      simpl_casts.
      rewrite <- (ZX_Stack_Compose_distr (nWire 2) _ (nWire n ↕ (Z 2 1 0)) _).
      cleanup_zx.
      rewrite <- nwire_stack_compose_botleft.
      rewrite ZX_Compose_assoc.
      rewrite ZX_Stack_assoc_back.
      simpl_casts.
      rewrite <- nstack1_split.
      rewrite <- IHn.
      rewrite <- (Grow_Z_Left (n + 2)).
      simpl.
      easy.
Qed.

Lemma Grow_Z_Right_Bot_1_2 : forall {n m} α,
  Z n (m + 2) α ∝ 
  (Z n (m + 1) α) ⟷ (nWire m ↕ Z 1 2 0).
Proof.
  intros.
  apply transpose_diagrams.
  simpl.
  rewrite nstack1_transpose.
  rewrite transpose_wire.
  apply Grow_Z_Left_Bot_2_1.
Qed.

Lemma Grow_Z_Left_Bot_dim : forall n,
  (n + 1 + 1 = n + 2)%nat.
Proof. lia. Qed.
Opaque Grow_Z_Left_Bot_dim.

Opaque Cast.

Ltac solve_prop c := 
  prop_exists_nonzero c; simpl; Msimpl; 
  unfold X_semantics; unfold Z_semantics; simpl; solve_matrix; 
  autorewrite with Cexp_db; lca.

Lemma Grow_Z_Left_Bot_1_2 : forall {n m} α,
  Z (n + 1) (m + 1) α ∝
  Cast (n + 1) (n + 1 + 1) (eq_refl) (Grow_Z_Left_Bot_dim _) (nWire n ↕ Z 1 2 0) ⟷ (Z (n + 1) m α ↕ —).
Proof.
  induction n; intros.
  - simpl_casts.
    cleanup_zx.
    eapply (cast_diagrams 1 (m + 1)).
    simpl_casts.
    simpl.
    induction m.
    + solve_prop 1.
    + destruct m.
      * solve_prop 1.
      * rewrite (Grow_Z_Right 1 m).
        rewrite stack_wire_distribute_r.
        rewrite <- ZX_Compose_assoc.
        rewrite <- IHm.
        rewrite wire_to_nWire at 2.
        rewrite (ZX_Stack_assoc (Z 1 2 0) (nWire m)).
        simpl_casts.
        rewrite <- nstack1_split.
        simpl.
        rewrite <- Grow_Z_Right.
        easy.
  - simpl.
    destruct n.
    + simpl.
      simpl_casts.
      cleanup_zx.
      simpl_casts.
      simpl in IHn.
      induction m.
      * solve_prop 1.
      * simpl.
        destruct m.
        -- solve_prop 1.
        -- rewrite (Grow_Z_Right 2 m).
           rewrite stack_wire_distribute_r.
           rewrite <- ZX_Compose_assoc.
           rewrite <- IHm.
           rewrite wire_to_nWire at 2.
           rewrite (ZX_Stack_assoc (Z 1 2 0) (nWire m) (nWire 1)).
           simpl_casts.
           rewrite <- nstack1_split.
           simpl.
           admit.
    + rewrite cast_compose_l.
      simpl_casts.
      rewrite (ZX_Stack_assoc — (nWire (S n))).
      simpl_casts.
      eapply (cast_diagrams (1 + ((S n) + 1)) (m + 1)).
      rewrite cast_compose_distribute.
      simpl_casts.
      erewrite (cast_compose_mid (S (S n + 1) + 1)).
      simpl_casts.
      simpl.
      erewrite (cast_stack_bot _ _ — (nWire (S n) ↕ Z 1 2 0)).
      rewrite (Grow_Z_Left (n + 1) m).
      simpl in IHn.
Admitted.

Lemma Z_1_2_1_fusion : forall α β,
  (Z 1 2 α ⟷ Z 2 1 β) ∝ (Z 1 1 (α + β)).
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
  autorewrite with Cexp_db.
  lca.
Qed.

Lemma nWire_S_l : forall n,
  nWire (S n) ∝ — ↕ nWire n.
Proof. intros. easy. Qed.

Lemma Z_Absolute_Fusion : forall {n m o} α β,
  (Z n (S m) α ⟷ Z (S m) o β) ∝
  Z n o (α + β).
Proof.
  intros.
  induction m.
  - apply Z_spider_1_1_fusion.
  - rewrite Grow_Z_Right, Grow_Z_Left.
    rewrite ZX_Compose_assoc.
    rewrite <- (ZX_Compose_assoc ((Z 1 2 0) ↕ (m ↑ —))
                                 ((Z 2 1 0) ↕ (m ↑ —))
                                  (Z (S m) o β)) .
    rewrite <- ZX_Stack_Compose_distr.
    rewrite Z_1_2_1_fusion.
    rewrite Rplus_0_l.
    rewrite Z_0_is_wire.
    cleanup_zx.
    apply IHm.
Qed.

Lemma cap_absorb_dim : forall n m,
  (n + 0 + m = n + m)%nat.
Proof. lia. Qed.

Opaque Cast.

Lemma Z_Cap_absord_base : forall α,
  Z 1 2 α ⟷ ⊃ ∝ Z 1 0 α.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  Msimpl.
  unfold Z_semantics.
  simpl.
  solve_matrix.
Qed.

Lemma Z_rot_l : forall n m α,
  Z (S n) m α ∝ Z 1 1 α ↕ nWire n ⟷ Z (S n) m 0.
Proof.
  assert (Z_rot_passthrough : forall α, 
    (Z 1 1 α ↕ — ⟷ Z 2 1 0) ∝ Z 2 1 0 ⟷ Z 1 1 α).
    { solve_prop 1. }
  induction n; intros.
  - cleanup_zx.
    simpl_casts.
    rewrite Z_spider_1_1_fusion.
    rewrite Rplus_0_r.
    easy.
  - simpl.
    rewrite (Grow_Z_Left n m 0).
    rewrite <- ZX_Compose_assoc.
    rewrite (ZX_Stack_assoc_back (Z 1 1 α) —).
    simpl_casts.
    rewrite <- (ZX_Stack_Compose_distr (Z 1 1 α ↕ —) (Z 2 1 0) (nWire n)).
    cleanup_zx.
    rewrite Z_rot_passthrough.
    rewrite stack_nwire_distribute_r.
    rewrite ZX_Compose_assoc.
    rewrite <- IHn.
    rewrite <- (Grow_Z_Left n).
    easy.
Qed.

Lemma Z_appendix_rot_l : forall n m α,
  Z n m α ∝ (Z 0 1 α ↕ nWire n) ⟷ Z (S n) m 0.
Proof.
  assert (Z_appendix_base : forall α,
    (Z 0 1 α ↕ — ⟷ Z 2 1 0) ∝ Z 1 1 α).
    { solve_prop 1. }
  induction n; intros.
  - cleanup_zx.
    simpl_casts.
    rewrite Z_spider_1_1_fusion.
    rewrite Rplus_0_r.
    easy.
  - rewrite Grow_Z_Left.
    simpl.
    rewrite (ZX_Stack_assoc_back (Z 0 1 α) —).
    simpl_casts.
    rewrite <- ZX_Compose_assoc.
    rewrite <- (@stack_nwire_distribute_r _ _ _ n (Z 0 1 α ↕ —) (Z 2 1 0)).
    rewrite Z_appendix_base.
    rewrite <- Z_rot_l.
    easy.
Qed.

Lemma Z_appendix_rot_r : forall n m α,
  Z n m α ∝ Z n (S m) 0 ⟷ (Z 1 0 α ↕ nWire m).
Proof. 
  intros.
  apply transpose_diagrams.
  simpl.
  rewrite nstack1_transpose.
  rewrite transpose_wire.
  apply Z_appendix_rot_l.
Qed.

Lemma Z_appendix_top_l : forall n m α,
  Z n m α ∝ (Z 0 1 0 ↕ nWire n) ⟷ Z (S n) m α.
Proof.
  induction n; intros.
  - cleanup_zx.
    simpl_casts.
    rewrite Z_spider_1_1_fusion.
    rewrite Rplus_0_l.
    easy.
  - rewrite Grow_Z_Left.
    rewrite <- ZX_Compose_assoc.
    fold (nWire n).
    rewrite nWire_S_l.
    rewrite (ZX_Stack_assoc_back (Z 0 1 0) (—) (nWire n)).
    simpl_casts.
    rewrite <- (ZX_Stack_Compose_distr (Z 0 1 0 ↕ —) (Z 2 1 0) (nWire n)).
    rewrite Grow_Z_Left_1_2.
    rewrite <- ZX_Compose_assoc.
    rewrite <- wire_to_nWire.
    rewrite <- (ZX_Stack_Compose_distr (Z 0 1 0) _ _ _).
    rewrite Z_spider_1_1_fusion.
    rewrite Rplus_0_l.
    cleanup_zx.
    rewrite Z_2_0_0_is_cap.
    rewrite Z_0_2_0_is_cup.
    rewrite yank_r.
    cleanup_zx.
    easy.
Qed.

Lemma Z_appendix_top_r : forall n m α,
  Z n m α ∝  Z n (S m) α ⟷ (Z 1 0 0 ↕ nWire m).
Proof.
  intros.
  apply transpose_diagrams.
  simpl.
  cleanup_zx.
  rewrite nstack1_transpose.
  rewrite transpose_wire.
  fold (nWire m).
  rewrite <- (Z_appendix_top_l m n).
  easy.
Qed.

Lemma Z_Wrap_Under_R_base : forall α,
  Z 1 2 α ∝  (— ↕ ⊂) ⟷ (Z 2 1 α ↕ —).
Proof.
  intros.
  simpl.
  prop_exists_nonzero 1.
  simpl; Msimpl.
  unfold Z_semantics; simpl.
  solve_matrix.
Qed.

Lemma Z_Wrap_Under_L_base : forall α,
  Z 2 1 α ∝ (Z 1 2 α ↕ —) ⟷ (— ↕ ⊃).
Proof. transpose_of Z_Wrap_Under_R_base. Qed.

Lemma Z_Cap_absorb : forall n m0 m1 α,
  Z n (m0 + 2 + m1) α ⟷ (nWire m0 ↕ ⊃ ↕ nWire m1) ∝ 
  (Z n (m0 + 0 + m1) α).
Proof.
  intros.
  induction m0.
  - simpl.
    cleanup_zx.
    rewrite Grow_Z_Right.
    rewrite ZX_Compose_assoc.
    rewrite <- (ZX_Stack_Compose_distr (Z 1 2 0) ⊃ (nWire m1) (nWire m1)).
    rewrite Z_Cap_absord_base.
    cleanup_zx.
    rewrite <- Z_appendix_top_r.
    easy.
  - destruct m0.
    + simpl.
      rewrite Grow_Z_Right.
      rewrite ZX_Compose_assoc.
      rewrite nWire_S_l.
      rewrite (ZX_Stack_assoc_back (Z 1 2 0) —).
      simpl_casts.
      rewrite <- (ZX_Stack_Compose_distr (Z 1 2 0 ↕ —) (nWire 1 ↕ ⊃) (nWire m1)).
      rewrite <- wire_to_nWire.
      rewrite <- Z_Wrap_Under_L_base.
      cleanup_zx.
      rewrite Grow_Z_Right.
      rewrite ZX_Compose_assoc.
      rewrite <- (ZX_Stack_Compose_distr (Z 1 2 0) (Z 2 1 0) (nWire m1) _).
      cleanup_zx.
      rewrite Z_Absolute_Fusion.
      rewrite Rplus_0_l.
      cleanup_zx.
      easy.
    + simpl.
      rewrite Grow_Z_Right.
      rewrite (ZX_Stack_assoc_back — —).
      simpl_casts.
      rewrite ZX_Compose_assoc.
      rewrite (ZX_Stack_assoc (— ↕ —)).
      simpl_casts.
      rewrite (ZX_Stack_assoc (— ↕ —)).
      simpl_casts.
      rewrite <- (ZX_Stack_Compose_distr (Z 1 2 0) (— ↕ —) 
                             (nWire (m0 + 2 + m1)) (nWire m0 ↕ ⊃ ↕ nWire m1)).
      rewrite wire_to_nWire at 2.
      rewrite <- nWire_S_l.
      cleanup_zx.
      rewrite <- nwire_stack_compose_topleft.
      rewrite <- wire_to_nWire.
      rewrite ZX_Stack_assoc_back.
      simpl_casts.
      rewrite ZX_Stack_assoc_back.
      simpl_casts.
      rewrite <- nWire_S_l.
      rewrite <- ZX_Compose_assoc.
      rewrite IHm0.
      rewrite <- Grow_Z_Right.
      easy.
Qed.

Lemma Grow_Z_Top_Left_by : forall n {m o α},
  Z (n + m) o α ∝
  (Z n 1 0 ↕ nWire m) ⟷ Z (S m) o α.
Proof.
  induction n; intros.
  - simpl.
    rewrite <- (Z_appendix_top_l m).
    easy.
  - intros.
    simpl.
    destruct n.
    + simpl.
      cleanup_zx.
      easy.
    + rewrite Grow_Z_Left.
      rewrite stack_nwire_distribute_r.
      rewrite ZX_Compose_assoc.
      rewrite <- IHn.
      rewrite (ZX_Stack_assoc (Z 2 1 0) (nWire n) (nWire m)).
      simpl_casts.
      rewrite <- nstack1_split.
      rewrite <- (Grow_Z_Left (n + m)).
      easy.
Qed.

Lemma Grow_Z_Top_Right_by : forall {n} m {o α},
  Z n (m + o) α ∝
  Z n (S o) α ⟷ (Z 1 m 0 ↕ nWire o).
Proof.
  intros.
  apply transpose_diagrams.
  simpl.
  rewrite nstack1_transpose.
  rewrite transpose_wire.
  apply Grow_Z_Top_Left_by.
Qed.

Lemma Grow_Z_Bot_Left_by : forall n {m o α},
  Z (n + m) o α ∝ 
  (nWire n ↕ Z m 1 0) ⟷ Z (n + 1) o α.
Proof.
  induction n; intros.
  - simpl.
    cleanup_zx.
    rewrite Z_spider_1_1_fusion.
    rewrite Rplus_0_l.
    easy.
  - destruct n. 
    + simpl.
      cleanup_zx.
      simpl_casts.
      rewrite (WrapOver_L 1 o).
      rewrite <- ZX_Compose_assoc.
      rewrite <- stack_wire_distribute_l.
      rewrite Z_spider_1_1_fusion.
      rewrite Rplus_0_l.
      rewrite <- WrapOver_L.
      easy.
    + simpl. 
      rewrite (Grow_Z_Left (n + 1) o).
      rewrite <- ZX_Compose_assoc.
      rewrite (ZX_Stack_assoc_back — —).
      simpl_casts.
      rewrite (ZX_Stack_assoc (— ↕ —)).
      simpl_casts.
      rewrite <- (ZX_Stack_Compose_distr (— ↕ —) (Z 2 1 0) (nWire n ↕ Z m 1 0)).
      cleanup_zx.
      rewrite <- nwire_stack_compose_botleft.
      rewrite ZX_Stack_assoc_back.
      simpl_casts.
      rewrite <- nstack1_split.
      rewrite ZX_Compose_assoc.
      rewrite <- (IHn m o α).
      simpl.
      rewrite wire_to_nWire at 1.
      rewrite wire_to_nWire at 2.
      rewrite <- nstack1_split.
      cleanup_zx.
      rewrite <- (Grow_Z_Left (n + m)).
      easy.
Qed.

Lemma Grow_Z_Bot_Right_by : forall {n m} o {α},
  Z n (m + o) α ∝ 
  Z n (m + 1) α ⟷ (nWire m ↕ Z 1 o 0).
Proof.
  intros.
  apply transpose_diagrams.
  simpl.
  rewrite nstack1_transpose.
  rewrite transpose_wire.
  apply Grow_Z_Bot_Left_by.
Qed.

Lemma WrapUnder_dim : forall n, 
  (n + 1 + 1 = n + 2)%nat.
Proof. lia. Qed.

Lemma WrapUnder_L_base : forall α,
  Z 0 1 α ∝
  ⊂ ⟷ (Z 1 0 α ↕ —).
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl; Msimpl.
  unfold Z_semantics.
  gridify.
  solve_matrix.
Qed.

Lemma WrapUnder_L_ind :
  (— ↕ ⊂) ⟷ (Z 2 1 0 ↕ —) ∝ Z 1 2 0.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl; Msimpl.
  unfold Z_semantics.
  simpl.
  solve_matrix.
Qed.

Lemma WrapUnder_L : forall n m α,
  Z n (m + 1) α ∝ 
  (Cast n (n + 1 + 1) (eq_sym (plus_0_r _)) (WrapUnder_dim _) 
        (nWire n ↕ Cap)) ⟷ Z (n + 1) m α ↕ —.
Proof.
  induction n; intros.
  - simpl.
    simpl_casts.
    cleanup_zx.
    induction m.
    + simpl.
      prop_exists_nonzero 1. 
      simpl; Msimpl.
      unfold Z_semantics.
      solve_matrix.
    + simpl.
      destruct m.
      * simpl.
        rewrite (Grow_Z_Top_Right_by 1).
        prop_exists_nonzero 1.
        simpl; Msimpl.
        unfold Z_semantics.
        simpl.
        solve_matrix.
        rewrite Cexp_0.
        lca.
      * rewrite Grow_Z_Right.
        rewrite stack_wire_distribute_r.
        rewrite <- ZX_Compose_assoc.
        rewrite <- IHm.
        rewrite wire_to_nWire at 2.
        rewrite (ZX_Stack_assoc (Z 1 2 0) (nWire m)).
        simpl_casts.
        rewrite <- nstack1_split.
        simpl.
        rewrite <- Grow_Z_Right.
        easy.
  - destruct n.
    + simpl.
      simpl_casts.
      cleanup_zx.
      simpl_casts.
      simpl in IHn.
      rewrite Grow_Z_Left.
      cleanup_zx.
      simpl_casts.
      rewrite stack_wire_distribute_r.
      rewrite wire_to_nWire.
Admitted.


Lemma Z_add_r : forall {n} m o {α},
  Z n (m + o) α ∝ Z n 2 α ⟷ (Z 1 m 0 ↕ Z 1 o 0).
Proof.
  intros.
  induction m.
  - simpl.
    rewrite <- nwire_stack_compose_botleft.
    rewrite <- ZX_Compose_assoc.
    cleanup_zx.
    rewrite <- (Grow_Z_Top_Right_by 0).
    simpl.
    rewrite Z_Absolute_Fusion.
    rewrite Rplus_0_r.
    easy.
  - destruct m.
    + simpl.
      cleanup_zx.
      rewrite wire_to_nWire.
      rewrite <- (@Grow_Z_Bot_Right_by n 1 o α).
      easy.
    + simpl.
      rewrite (Grow_Z_Right 1 m).
      rewrite <- (nwire_removal_r (Z 1 o 0)).
      rewrite ZX_Stack_Compose_distr.
      rewrite <- ZX_Compose_assoc.
      rewrite <- IHm.
      rewrite (ZX_Stack_assoc (Z 1 2 0) (nWire m) (nWire o)).
      simpl_casts.
      rewrite <- nstack1_split.
      rewrite <- (Grow_Z_Right n (m + o)).
      easy.
Qed.

Lemma Z_add_l : forall n m {o α},
  Z (n + m) o α ∝ (Z n 1 0 ↕ Z m 1 0) ⟷ Z 2 o α.
Proof. intros. transpose_of (@Z_add_r o n m). Qed.

Lemma dominant_spider_fusion_r : forall n m0 m1 o α β,
  Z n ((S m0) + m1) α ⟷ (Z (S m0) o β ↕ nWire m1) ∝ 
  Z n (o + m1) (α + β).
Proof.
  intros.
  rewrite Z_add_r.
  repeat rewrite ZX_Compose_assoc.
  rewrite <- (ZX_Stack_Compose_distr (Z 1 (S m0) 0)).
  rewrite Z_Absolute_Fusion.
  rewrite Rplus_0_l.
  cleanup_zx.
  rewrite (Z_appendix_rot_r 1 o β).
  rewrite <- (nwire_removal_r (Z 1 m1 0)).
  rewrite ZX_Stack_Compose_distr.
  rewrite <- ZX_Compose_assoc.
  rewrite <- Z_add_r.
  rewrite (ZX_Stack_assoc (Z 1 0 β) (nWire o)).
  simpl_casts.
  rewrite <- nstack1_split.
  simpl.
  rewrite <- (Rplus_0_r α) at 1.
  rewrite <- Z_spider_1_1_fusion.
  rewrite ZX_Compose_assoc.
  rewrite <- Z_appendix_rot_r.
  rewrite Z_spider_1_1_fusion.
  easy.
Qed.

Lemma SpiderFusion : forall top mid bot input output α β,
  (nWire top ↕ Z input (S mid + bot) α) ⟷  
    (Cast (top + (S mid + bot)) (output + bot) (Nat.add_assoc _ _ _) eq_refl ((Z (top + S mid) output β) ↕ nWire bot)) ∝
    Z (top + input) (output + bot) (α + β).
Proof.
  intros.
  simpl_casts.
  induction mid.
  - simpl.
    induction top.
    + simpl.
      cleanup_zx.
      simpl_casts.
      induction bot.
      * simpl.
Admitted.
