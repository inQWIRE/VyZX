Require Import ZX.
Require Import Gates.
Require Import GateRules.
Require Import Rules.
Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.VectorStates.
From VyZX Require Import Proportional.

Section Demo.

Lemma ZX_Stack_Compose_distr : 
  forall {nIn1 nMid12 nIn3 nOut2 nMid34 nOut4}
    (zx1 : ZX nIn1 nMid12) (zx2 : ZX nMid12 nOut2) (zx3 : ZX nIn3 nMid34) (zx4 : ZX nMid34 nOut4),
    (zx1 ⟷ zx2) ↕ (zx3 ⟷ zx4) ∝ (zx1 ↕ zx3) ⟷ (zx2 ↕ zx4).
Proof.
  intros.
  unfold proportional, proportional_general.
  exists 1.
  split.
  - simpl.
    Msimpl_light.
    (* A ⊗ B × (C ⊗ D) = A × C ⊗ (B × D) *)
    rewrite kron_mixed_product. 
    reflexivity.
  - nonzero.
Restart.
  intros; prop_exist_non_zero 1; simpl; Msimpl; easy.
Qed.

Reserved Notation "n ↑ zx" (at level 41).
Fixpoint nStack1 n (zx : ZX 1 1) : ZX n n :=
  match n with
  | 0 => ⦰
  | S n' => zx ↕ (n' ↑ zx)
  end
  where "n ↑ zx" := (nStack1 n zx).

Lemma nStack1_compose : forall (zx0 zx1 : ZX 1 1) {n}, 
  n ↑ (zx0 ⟷ zx1) ∝ (n ↑ zx0) ⟷ (n ↑ zx1).
Proof.
  intros.
  induction n.
  - unfold nStack1.
    remove_empty.
    reflexivity.
  - simpl.
    rewrite <- (ZX_Stack_Compose_distr zx0 zx1).
    rewrite IHn.
    reflexivity.
Qed. 