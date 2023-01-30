Require Import CoreData.CoreData.
Require Import CastRules.
Require Import SpiderInduction.
Require Export StackRules.
Require Export ComposeRules.

Local Open Scope ZX_scope.
Lemma nwire_stack_compose_topleft : forall {topIn botIn topOut botOut} 
                       (zx0 : ZX botIn botOut) (zx1 : ZX topIn topOut),
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

Lemma nwire_stack_compose_botleft : forall {topIn botIn topOut botOut} 
                       (zx0 : ZX botIn botOut) (zx1 : ZX topIn topOut),
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
