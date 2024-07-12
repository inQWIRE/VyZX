Require Export CoreData.CoreData.
Require Import CastRules.
Require Import SpiderInduction.

Local Open Scope ZX_scope.
Lemma compose_assoc : forall {n m0 m1 o}
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

(* Distributivity *)

Lemma stack_compose_distr : 
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

Lemma compose_simplify : forall {n m o}
  (zx1 zx3 : ZX n m) (zx2 zx4 : ZX m o),
  zx1 ∝ zx3 -> zx2 ∝ zx4 -> zx1 ⟷ zx2 ∝ zx3 ⟷ zx4.
Proof.
  intros.
  rewrite H, H0.
  easy.
Qed.


Lemma compose_transpose : forall {n m o} (zx1 : ZX n m) (zx2 : ZX m o), (zx1 ⟷ zx2) ⊤ ∝ (zx2⊤ ⟷ zx1⊤).
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl.
	lma.
Qed.

(* Empty diagram removal *)


Lemma compose_empty_r : forall {nIn} (zx : ZX nIn 0),
  zx ⟷ ⦰ ∝ zx.
Proof. 
  intros.
  prop_exists_nonzero 1.
  simpl.
  Msimpl.
  reflexivity.
Qed.

Lemma compose_empty_l : forall {nOut} (zx : ZX 0 nOut),
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
  rewrite n_wire_semantics.
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
  replace (n ↑ —) with (n_wire n) by easy.
  rewrite n_wire_semantics.
  Msimpl.
  reflexivity.
Qed.