Require Export CoreData.CoreData.
Require Import CastRules.
Require Import SpiderInduction.

Local Open Scope ZX_scope.
Lemma compose_assoc : forall {n m0 m1 o}
  (zx1 : ZX n m0) (zx2 : ZX m0 m1) (zx3 : ZX m1 o),
  zx1 ⟷ zx2 ⟷ zx3 ∝= zx1 ⟷ (zx2 ⟷ zx3).
Proof.
  intros.
  symmetry. 
  exact (Mmult_assoc _ _ _).
Qed.

(* Distributivity *)

Lemma stack_compose_distr : 
forall {n1 m1 o2 n3 m2 o4}
  (zx1 : ZX n1 m1) (zx2 : ZX m1 o2) (zx3 : ZX n3 m2) (zx4 : ZX m2 o4),
  (zx1 ⟷ zx2) ↕ (zx3 ⟷ zx4) ∝= (zx1 ↕ zx3) ⟷ (zx2 ↕ zx4).
Proof.
  intros.
  symmetry.
  unfold proportional_by_1.
  cbn.
  restore_dims.
  exact (kron_mixed_product _ _ _ _).
Qed.

Lemma compose_simplify_eq : forall {n m o}
  (zx1 zx3 : ZX n m) (zx2 zx4 : ZX m o),
  zx1 ∝= zx3 -> zx2 ∝= zx4 -> zx1 ⟷ zx2 ∝= zx3 ⟷ zx4.
Proof.
  now intros * -> ->.
Qed.

Lemma compose_simplify : forall {n m o}
  (zx1 zx3 : ZX n m) (zx2 zx4 : ZX m o),
  zx1 ∝ zx3 -> zx2 ∝ zx4 -> zx1 ⟷ zx2 ∝ zx3 ⟷ zx4.
Proof.
  now intros * -> ->.
Qed.


Lemma compose_transpose_eq : forall {n m o} (zx1 : ZX n m) (zx2 : ZX m o), 
  (zx1 ⟷ zx2) ⊤ = (zx2⊤ ⟷ zx1⊤).
Proof.
  reflexivity.
Qed.

Lemma compose_transpose : forall {n m o} (zx1 : ZX n m) (zx2 : ZX m o), 
  (zx1 ⟷ zx2) ⊤ ∝= (zx2⊤ ⟷ zx1⊤).
Proof.
  reflexivity.
Qed.

(* Empty diagram removal *)


Lemma compose_empty_r : forall {nIn} (zx : ZX nIn 0),
  zx ⟷ ⦰ ∝= zx.
Proof. 
  intros.
  apply (Mmult_1_l _ _).
  auto_wf.
Qed.

Lemma compose_empty_l : forall {nOut} (zx : ZX 0 nOut),
  ⦰ ⟷ zx ∝= zx.
Proof. 
  intros.
  apply (Mmult_1_r _ _).
  auto_wf.
Qed.

Lemma nwire_removal_l: forall {n nOut} (zx : ZX n nOut), 
  n_wire n ⟷ zx ∝= zx.
Proof.
  intros.
  unfold proportional_by_1.
  cbn.
  now rewrite n_wire_semantics, Mmult_1_r by auto_wf.
Qed.

Lemma nwire_removal_r: forall {n nIn} (zx : ZX nIn n), zx ⟷ n_wire n ∝= zx.
Proof.
  intros.
  unfold proportional_by_1.
  cbn.
  now rewrite n_wire_semantics, Mmult_1_l by auto_wf.
Qed.

Lemma wire_removal_l : forall {nOut} (zx : ZX 1 nOut), — ⟷ zx ∝= zx.
Proof.
  intros.
  apply (Mmult_1_r _ _).
  auto_wf.
Qed.

Lemma wire_removal_r : forall {nIn} (zx : ZX nIn 1), zx ⟷ — ∝= zx.
Proof.
  intros.
  apply (Mmult_1_l _ _).
  auto_wf.
Qed.