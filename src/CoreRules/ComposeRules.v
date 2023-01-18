From VyZX Require Export ZXCore.
From VyZX Require Import SemanticCore.
From VyZX Require Export Proportional.
From VyZX Require Export CastRules.
From VyZX Require Export SpiderInduction.

Local Open Scope ZX_scope.
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
