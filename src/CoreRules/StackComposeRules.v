Require Import CoreData.CoreData.
Require Import CastRules.
Require Import SpiderInduction.
Require Export StackRules.
Require Export WireRules.
Require Export ComposeRules.

Local Open Scope ZX_scope.
Lemma nwire_stack_compose_topleft : forall {topIn botIn topOut botOut} 
                       (zx0 : ZX botIn botOut) (zx1 : ZX topIn topOut),
  ((n_wire topIn) ↕ zx0) ⟷ (zx1 ↕ (n_wire botOut)) ∝= 
  (zx1 ↕ zx0).
Proof.
  intros.
  unfold proportional_by_1.
  cbn.
  rewrite 2!n_wire_semantics.
  restore_dims.
  rewrite kron_mixed_product.
  now Msimpl.
Qed.

Lemma nwire_stack_compose_botleft : forall {topIn botIn topOut botOut} 
                       (zx0 : ZX botIn botOut) (zx1 : ZX topIn topOut),
  (zx0 ↕ (n_wire topIn)) ⟷ ((n_wire botOut) ↕ zx1) ∝= 
  (zx0 ↕ zx1).
Proof.
  intros.
  unfold proportional_by_1.
  cbn.
  rewrite 2!n_wire_semantics.
  restore_dims.
  rewrite kron_mixed_product.
  now Msimpl.
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