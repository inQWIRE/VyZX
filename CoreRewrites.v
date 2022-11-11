From VyZX Require Export ZXCore.
From VyZX Require Import SemanticCore.
From VyZX Require Export Proportional.
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

Lemma cast_id :
  forall {n m} prfn prfm (zx : ZX n m),
    Cast n m prfn prfm zx ∝ zx.
Proof.
  intros; subst.
  prop_exists_nonzero 1.
  rewrite Cast_semantics.
  simpl; lma.
Qed.

Lemma cast_compose :
  forall {n n' m m' o} prfn prfm (zx0 : ZX n m) (zx1 : ZX m' o),
    Cast n' m' prfn prfm zx0 ⟷ zx1 ∝ Cast n' o prfn eq_refl (zx0 ⟷ Cast m o (eq_sym prfm) eq_refl zx1).
Proof. Admitted.

Lemma cast_stack_l : forall {nTop nTop' mTop mTop' nBot mBot} eqnTop eqmTop 
                            (zxTop : ZX nTop mTop) (zxBot : ZX nBot mBot),
  (Cast nTop' mTop' eqnTop eqmTop zxTop) ↕ zxBot ∝ 
  Cast (nTop' + nBot) (mTop' + mBot)  
       (f_equal2_plus _ _ _ _ (eqnTop) eq_refl)
       (f_equal2_plus _ _ _ _ (eqmTop) eq_refl)
       (zxTop ↕ zxBot).
Proof.
  intros.
  subst.
  repeat rewrite cast_id.
  reflexivity.
Qed.

Lemma cast_stack_r : forall {nTop mTop nBot nBot' mBot mBot'} eqnBot eqmBot 
                            (zxTop : ZX nTop mTop) (zxBot : ZX nBot mBot),
  zxTop ↕ (Cast nBot' mBot' eqnBot eqmBot zxBot) ∝ 
  Cast (nTop + nBot') (mTop + mBot')  
       (f_equal2_plus _ _ _ _ eq_refl eqnBot)
       (f_equal2_plus _ _ _ _ eq_refl eqmBot)
       (zxTop ↕ zxBot).
Proof.
  intros.
  subst.
  repeat rewrite cast_id.
  reflexivity.
Qed.

Lemma cast_simplify :
  forall {n n' m m'} prfn0 prfm0 prfn1 prfm1  (zx0 zx1 : ZX n m),
  zx0 ∝ zx1 ->
  Cast n' m' prfn0 prfm0 zx0 ∝ Cast n' m' prfn1 prfm1 zx1.
Proof. intros; subst. rewrite H. 
  prop_exists_nonzero 1.
  Msimpl.
  repeat rewrite Cast_semantics.
  reflexivity.
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
  prop_exists_nonzero 1.
  simpl; lma.
Qed.

Lemma cast_symm :
  forall {n0 m0 n1 m1} prfn prfm prfn' prfm' (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
    Cast n1 m1 prfn prfm zx0 ∝ zx1 <->
    zx0 ∝ Cast n0 m0 prfn' prfm' zx1.
Proof.
  intros.
  split; intros.
  - subst.
    rewrite cast_id.
    rewrite cast_id in H.
    easy.
  - subst.
    rewrite cast_id.
    rewrite cast_id in H.
    easy.
Qed.


Lemma cast_backwards :
  forall {n0 m0 n1 m1} prfn prfm prfn' prfm' (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
    Cast n1 m1 prfn prfm zx0 ∝ zx1 <->
    Cast n0 m0 prfn' prfm' zx1 ∝ zx0.
Proof.
  intros.
  split; symmetry; subst. 
  rewrite cast_id.
  rewrite cast_id in H.
  auto.
  rewrite cast_id.
  rewrite cast_id in H.
  easy.
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
  replace (n ↑ —) with (nWire n) by easy.
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
  unfold nWire.
  simpl.
  cleanup_zx.
  rewrite cast_id.
  easy.
Qed.

Lemma stack_wire_distribute : forall {n m o} (zx0 : ZX n m) (zx1 : ZX m o),
  — ↕ (zx0 ⟷ zx1) ∝ (— ↕ zx0) ⟷ (— ↕ zx1).
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl; Msimpl; easy.
Qed.

(* Lemma nWire_collapse_r : forall {n0 n1 m1} (zx0 : ZX n0 0) (zx1 : ZX n1 m1), *)
(*   (zx0 ↕ nWire n1) ⟷ zx1 ∝ zx0 ↕ zx1. *)

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
    rewrite cast_id.
    reflexivity.
Qed.

Lemma nstack_split : forall n m {nIn mOut} (zx : ZX nIn mOut),
  (n + m) ⇑ zx ∝ 
  Cast _ _ (Nat.mul_add_distr_r _ _ _) (Nat.mul_add_distr_r _ _ _) ((n ⇑ zx) ↕ (m ⇑ zx)).
Proof.
  intros.
  dependent induction n.
  - simpl. rewrite cast_id.
    cleanup_zx. easy.
  - simpl.
    rewrite IHn.
    simpl.
    rewrite cast_stack_r.
    rewrite <- cast_symm.
    rewrite cast_contract.
    rewrite ZX_Stack_assoc.
    apply cast_simplify.
    reflexivity.
    Unshelve.
    all: lia.
Qed.

Lemma Grow_Z_Left : forall (nIn nOut : nat) α,
  Z (S (S nIn)) nOut α ∝  
  (Z 2 1 0) ↕ (nIn ↑ Wire) ⟷ (Z (S nIn) nOut α).
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
  (Z nIn (S nOut) α) ⟷ ((Z_Spider 1 2 0) ↕ (nOut ↑ Wire)).
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
    rewrite cast_id.
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
      rewrite cast_id.
      rewrite (ZX_Stack_assoc — — _).
      rewrite cast_id.
      rewrite <- ZX_Compose_assoc.
      rewrite <- (stack_wire_distribute 
        ((Z) n (S m) α ⟷ ((Z) 1 2 0 ↕ (m ↑ —))) 
        (— ↕ ((Z) 1 2 0 ↕ nWire m))).
      rewrite ZX_Compose_assoc.
      fold (nWire m).
      rewrite ZX_Stack_assoc_back.
      rewrite cast_id.
      rewrite <- (ZX_Stack_Compose_distr (Z 1 2 0) (— ↕ Z 1 2 0) (nWire m) (nWire m)).
      rewrite <- Grow_Z_Right_Bot_1_2_Base.
      rewrite Grow_Z_Right.
      rewrite ZX_Stack_Compose_distr.
      rewrite <- ZX_Compose_assoc.
      rewrite <- Grow_Z_Right.
      unfold nWire.
      rewrite (ZX_Stack_assoc (Z 1 2 0) (1 ↑ —) (m ↑ —)).
      rewrite cast_id.
      rewrite <- nstack1_split.
      fold (nWire (1 + m)).
      rewrite <- (Grow_Z_Right n (S m)).
      easy.
Qed.

Ltac transpose_of H := intros; apply transpose_diagrams; simpl; apply H.
Ltac adjoint_of H := intros; apply adjoint_diagrams; simpl; apply H.

Lemma Z_2_1_through_cap : forall α, 
  Z 2 1 α ↕ — ⟷ ⊃ ∝ (— ↕ — ↕ Z 1 2 α) ⟷  (— ↕ ⊃ ↕ —) ⟷ ⊃.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  Msimpl.
  solve_matrix.
Qed.

Lemma Grow_Z_Left_1_2 : forall {n} α,
  Z (S n) 2 α ∝ 
  (Z 1 2 0 ↕ nWire n) ⟷ (— ↕ Z (S n) 1 α).
Proof.
  induction n;
  intros.
  - cleanup_zx.
    rewrite cast_id.
    prop_exists_nonzero 1.
    Msimpl; simpl.
    solve_matrix.
    rewrite Cexp_0.
    lca.
  - 
Admitted.

Lemma dominant_spider_fusion : forall midbot input midtop output α β,
  Z input (midtop + (S midbot)) α ⟷ (nWire midtop ↕ Z (S midbot) output β) ∝
  Z input (midtop + output) (α + β).
Proof.
  induction midbot; intros.
  - induction midtop.
    + simpl.
      cleanup_zx.
      apply Z_spider_1_1_fusion.
    + simpl.
      destruct midtop.
      * simpl.
Admitted.

Lemma SpiderFusion : forall top mid bot input output α β,
  (nWire top ↕ Z input (S mid + bot) α) ⟷  
    (Cast (top + (S mid + bot)) (output + bot) (Nat.add_assoc _ _ _) eq_refl ((Z (top + S mid) output β) ↕ nWire bot)) ∝
    Z (top + input) (output + bot) (α + β).
Proof.
  intros.
  induction mid.
  - simpl.
    induction top.
    + simpl.
      cleanup_zx.
      rewrite cast_id.
      induction bot.
      * simpl.
Admitted.
