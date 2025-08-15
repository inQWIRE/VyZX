Require Import CoreData.CoreData.
Require Import CastRules.
Require Import SpiderInduction.
Require Export StackRules.
Require Export WireRules.
Require Export ComposeRules.

(** Rules relating stack and compose *)

Local Open Scope ZX_scope.
Lemma nwire_stack_compose_topleft : forall {topIn botIn topOut botOut} 
                       (zx0 : ZX botIn botOut) (zx1 : ZX topIn topOut),
  ((n_wire topIn) ↕ zx0) ⟷ (zx1 ↕ (n_wire botOut)) ∝= 
  (zx1 ↕ zx0).
Proof.
  intros.
  now rewrite <- stack_compose_distr, nwire_removal_l, nwire_removal_r.
Qed.

Lemma nwire_stack_compose_botleft : forall {topIn botIn topOut botOut} 
                       (zx0 : ZX botIn botOut) (zx1 : ZX topIn topOut),
  (zx0 ↕ (n_wire topIn)) ⟷ ((n_wire botOut) ↕ zx1) ∝= 
  (zx0 ↕ zx1).
Proof.
  intros.
  now rewrite <- stack_compose_distr, nwire_removal_l, nwire_removal_r.
Qed.

Lemma stack_split_diag {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) : 
  zx0 ↕ zx1 ∝= zx0 ↕ n_wire o ⟷ (n_wire m ↕ zx1).
Proof.
  now rewrite <- stack_compose_distr, nwire_removal_l, nwire_removal_r.
Qed.

Lemma stack_split_antidiag {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) : 
  zx0 ↕ zx1 ∝= (n_wire n ↕ zx1) ⟷ (zx0 ↕ n_wire p).
Proof.
  now rewrite <- stack_compose_distr, nwire_removal_l, nwire_removal_r.
Qed.

Lemma push_out_top : forall {nIn nOut nOutAppendix} 
  (appendix : ZX 0 nOutAppendix) (zx : ZX nIn nOut), 
  appendix ↕ zx ∝= zx ⟷ (appendix ↕ (n_wire nOut)).
Proof.
  intros.
  rewrite <- (stack_empty_l zx) at 2.
  rewrite (nwire_stack_compose_topleft zx appendix).
  easy.
Qed.

Lemma push_out_bot : forall {nIn nOut nOutAppendix} 
  (appendix : ZX 0 nOutAppendix) (zx : ZX nIn nOut) prfn prfm, 
  zx ↕ appendix ∝= (cast _ _ prfn prfm zx) ⟷ ((n_wire nOut) ↕ appendix).
Proof.
  intros.
  rewrite <- stack_empty_r.
  now rewrite <- stack_compose_distr, compose_empty_l, nwire_removal_r.
Qed.

Lemma pull_out_top : forall {nIn nOut nInAppendix} 
  (appendix : ZX nInAppendix 0) (zx : ZX nIn nOut), 
  appendix ↕ zx ∝= (appendix ↕ (n_wire nIn)) ⟷ zx.
Proof.
  intros.
  rewrite <- (stack_empty_l zx) at 2.
  rewrite (nwire_stack_compose_botleft appendix zx).
  easy.
Qed.

Lemma pull_out_bot : forall {nIn nOut nInAppendix} 
  (appendix : ZX nInAppendix 0) (zx : ZX nIn nOut) prfn prfm, 
  zx ↕ appendix ∝= ((n_wire nIn) ↕ appendix) ⟷ (cast _ _ prfn prfm zx).
Proof.
  intros.
  rewrite <- stack_empty_r.
  rewrite <- stack_compose_distr.
  now rewrite nwire_removal_l, compose_empty_r.
Qed.

Lemma disconnected_stack_compose_l : forall {n m} 
  (zxIn : ZX n 0) (zxOut : ZX 0 m) prfn prfm, 
  zxIn ↕ zxOut ∝= cast _ _ prfn prfm (zxIn ⟷ zxOut).
Proof.
  intros.
  rewrite <- (compose_empty_l zxOut) at 1.
  rewrite <- (compose_empty_r zxIn) at 1.
  rewrite stack_compose_distr.
  rewrite stack_empty_l.
  auto_cast_eqn (rewrite stack_empty_r).
  rewrite cast_compose_l. 
  simpl_casts.
  easy.
Qed.

Lemma disconnected_stack_compose_r : forall {n m} (zxIn : ZX n 0) (zxOut : ZX 0 m) prfn prfm, 
  zxOut ↕ zxIn ∝= cast _ _ prfn prfm (zxIn ⟷ zxOut).
Proof.
  intros.
  rewrite <- (compose_empty_l zxOut) at 1.
  rewrite <- (compose_empty_r zxIn) at 1.
  rewrite stack_compose_distr.
  rewrite stack_empty_l.
  auto_cast_eqn (rewrite stack_empty_r).
  rewrite cast_compose_r.
  simpl_casts.
  easy.
Qed.


Lemma n_stack_compose {n m o} k (zx0 : ZX n m) (zx1 : ZX m o) : 
  k ⇑ (zx0 ⟷ zx1) ∝= k ⇑ zx0 ⟷ k ⇑ zx1.
Proof.
  induction k.
  - simpl; now rewrite compose_empty_l.
  - simpl.
    rewrite IHk, <- stack_compose_distr.
    reflexivity.
Qed.


Lemma n_stack1_compose k (zx0 : ZX 1 1) (zx1 : ZX 1 1) : 
  k ↑ (zx0 ⟷ zx1) ∝= k ↑ zx0 ⟷ k ↑ zx1.
Proof.
  induction k.
  - simpl; now rewrite compose_empty_l.
  - simpl.
    rewrite IHk, <- (@stack_compose_distr 1 1 1 k k).
    reflexivity.
Qed.

(* Rules about associator and invassociator *)

Lemma associator_nat_l {n m o n' m' o'} 
  (zx0 : ZX n n') (zx1 : ZX m m') (zx2 : ZX o o') : 
  associator n m o ⟷ (zx0 ↕ (zx1 ↕ zx2)) ∝=
  zx0 ↕ zx1 ↕ zx2 ⟷ associator n' m' o'.
Proof.
  rewrite stack_assoc_back.
  unfold associator.
  rewrite cast_compose_eq_mid_join, nwire_removal_l.
  rewrite cast_compose_r, cast_id, nwire_removal_r.
  reflexivity.
  Unshelve. all: lia.
Qed.

Lemma associator_nat_r {n m o n' m' o'} 
  (zx0 : ZX n n') (zx1 : ZX m m') (zx2 : ZX o o') : 
  zx0 ↕ zx1 ↕ zx2 ⟷ associator n' m' o' ∝= 
  associator n m o ⟷ (zx0 ↕ (zx1 ↕ zx2)).
Proof.
  now rewrite associator_nat_l.
Qed.


Lemma invassociator_nat_l {n m o n' m' o'} 
  (zx0 : ZX n n') (zx1 : ZX m m') (zx2 : ZX o o') : 
  invassociator n m o ⟷ (zx0 ↕ zx1 ↕ zx2) ∝=
  (zx0 ↕ (zx1 ↕ zx2)) ⟷ invassociator n' m' o'.
Proof.
  rewrite stack_assoc_back.
  unfold invassociator.
  rewrite cast_compose_eq_mid_join, nwire_removal_r.
  rewrite cast_compose_l, cast_id, nwire_removal_l.
  reflexivity.
  Unshelve. all: lia.
Qed.

Lemma invassociator_nat_r {n m o n' m' o'} 
  (zx0 : ZX n n') (zx1 : ZX m m') (zx2 : ZX o o') : 
  (zx0 ↕ (zx1 ↕ zx2)) ⟷ invassociator n' m' o' ∝=
  invassociator n m o ⟷ (zx0 ↕ zx1 ↕ zx2) .
Proof.
  now rewrite invassociator_nat_l.
Qed.

Lemma invassociator_linv n m o : 
  invassociator n m o ⟷ associator n m o ∝= n_wire _.
Proof.
  unfold associator, invassociator.
  rewrite cast_compose_eq_mid_join, nwire_removal_r.
  rewrite cast_n_wire.
  reflexivity.
Qed.

Lemma invassociator_rinv n m o : 
  associator n m o ⟷ invassociator n m o ∝= n_wire _.
Proof.
  unfold associator, invassociator.
  rewrite cast_compose_eq_mid_join, nwire_removal_r.
  rewrite cast_id.
  reflexivity.
Qed.


Lemma cast_to_compose_associator_l {n m o p} (zx : ZX (n + (m + o)) p) prf1 prf2 :
  cast (n + m + o) p prf1 prf2 zx ∝=
  associator n m o ⟷ zx.
Proof.
  unfold associator.
  rewrite cast_compose_l, cast_id, nwire_removal_l.
  cast_irrelevance.
Qed.

Lemma cast_to_compose_invassociator_l {n m o p} (zx : ZX (n + m + o) p) prf1 prf2 :
  cast (n + (m + o)) p prf1 prf2 zx ∝=
  invassociator n m o ⟷ zx.
Proof.
  unfold invassociator.
  rewrite cast_compose_l, cast_id, nwire_removal_l.
  cast_irrelevance.
Qed.