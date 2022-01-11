Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.VectorStates.
Require Export ZX.
Require Export Gates.
Require Export GateRules.
Require Export Rules.
Require Export Proportional.
Require Import Setoid.

Local Declare Scope H_ZX_scope.
Local Open Scope H_ZX_scope.

Local Open Scope R_scope.
Inductive H_ZX : nat -> nat -> Type :=
  | H_Empty : H_ZX 0 0
  | H_Z_Spider nIn nOut (α : R) : H_ZX nIn nOut
  | H_Cap : H_ZX 0 2
  | H_Cup : H_ZX 2 0
  | H_Stack {nIn0 nIn1 nOut0 nOut1} (zx0 : H_ZX nIn0 nOut0) (zx1 : H_ZX nIn1 nOut1) :
        H_ZX (nIn0 + nIn1) (nOut0 + nOut1)
  | H_Compose {nIn nMid nOut} (zx0 : H_ZX nIn nMid) (zx1 : H_ZX nMid nOut) : H_ZX nIn nOut.
Local Close Scope R_scope.

Notation "⦰H" := H_Empty. (* \revemptyset *)
Notation "⊂H'" := H_Cap. (* \subset *)
Notation "⊃H'" := H_Cup. (* \supset *)
Infix "⟷H" := H_Compose (left associativity, at level 40). (* \longleftrightarrow *)
Infix "↕H" := H_Stack (left associativity, at level 40). (* \updownarrow *)

Fixpoint H_ZX_semantics {nIn nOut} (zx : H_ZX nIn nOut) : 
  Matrix (2 ^ nOut) (2 ^nIn) := 
  match zx with
  | H_Empty => ZX_semantics Empty
  | H_Z_Spider nIn nOut α => ZX_semantics (Z_Spider nIn nOut α)
  | H_Cap => ZX_semantics Cap
  | H_Cup => ZX_semantics Cup
  | H_Stack zx0 zx1 => (H_ZX_semantics zx0) ⊗ (H_ZX_semantics zx1)
  | @H_Compose _ nMid _ zx0 zx1 => (H_ZX_semantics zx1) × (nMid ⨂ hadamard) × (H_ZX_semantics zx0)
  end.

Fixpoint H_ZX_to_ZX {nIn nOut} (zx : H_ZX nIn nOut) : ZX nIn nOut :=
  match zx with
  | H_Empty => Empty
  | H_Z_Spider nIn nOut α => (Z_Spider nIn nOut α)
  | H_Cap => Cap
  | H_Cup => Cup
  | H_Stack zx0 zx1 => Stack (H_ZX_to_ZX zx0) (H_ZX_to_ZX zx1)
  | H_Compose zx0 zx1 => (H_ZX_to_ZX zx0) ⥈ (H_ZX_to_ZX zx1)
  end.

Lemma WF_H_ZX : forall nIn nOut (zx : H_ZX nIn nOut), WF_Matrix (H_ZX_semantics zx).
Proof.
  intros.
  induction zx; try (simpl; auto 10 with wf_db);
    apply WF_list2D_to_matrix;
    try easy; (* case list of length 4 *)
    try intros; simpl in H; repeat destruct H; try discriminate; try (subst; easy). (* Case of 4 lists length 1 *)
Qed.

Global Hint Resolve WF_H_ZX : wf_db.

Definition H_proportional {nIn nOut} (zx0 : H_ZX nIn nOut) (zx1 : H_ZX nIn nOut) :=
  proportional_general H_ZX_semantics zx0 zx1.

Infix "∝H" := H_proportional (at level 70).

Lemma H_proportional_refl : forall {nIn nOut} (zx : H_ZX nIn nOut), zx ∝H zx.
Proof.
  intros.
  apply proportional_general_refl.
Qed.

Lemma H_proportional_symm : forall {nIn nOut} (zx0 zx1 : H_ZX nIn nOut),
  zx0 ∝H zx1 -> zx1 ∝H zx0.
Proof.
  intros.
  apply proportional_general_symm; assumption.
Qed.

Lemma H_proportional_trans : forall {nIn nOut} (zx0 zx1 zx2 : H_ZX nIn nOut),
  zx0 ∝H zx1 -> zx1 ∝H zx2 -> zx0 ∝H zx2.
Proof.
  intros.
  apply (proportional_general_trans _ _ _ H_ZX_semantics zx0 zx1 zx2); assumption.
Qed.

Add Parametric Relation (nIn nOut : nat) : (H_ZX nIn nOut) (@H_proportional nIn nOut)
  reflexivity proved by H_proportional_refl
  symmetry proved by H_proportional_symm
  transitivity proved by H_proportional_trans
  as zx_prop_equiv_rel.

Lemma H_stack_compat :
  forall nIn0 nOut0 nIn1 nOut1,
    forall zx0 zx1 : H_ZX nIn0 nOut0, zx0 ∝H zx1 ->
    forall zx2 zx3 : H_ZX nIn1 nOut1, zx2 ∝H zx3 ->
    zx0 ↕H zx2 ∝H zx1 ↕H zx3.
Proof.
  intros.
  destruct H; destruct H; destruct H0; destruct H0.
  exists (x * x0).
  split.
  - simpl; rewrite H; rewrite H0.
    lma.
  - apply Cmult_neq_0; try assumption.
Qed.

Add Parametric Morphism (nIn0 nOut0 nIn1 nOut1 : nat) : (@H_Stack nIn0 nIn1 nOut0 nOut1)
  with signature (@H_proportional nIn0 nOut0) ==> (@H_proportional nIn1 nOut1) ==> 
                 (@H_proportional (nIn0 + nIn1) (nOut0 + nOut1)) as H_stack_mor.
Proof. apply H_stack_compat; assumption. Qed.

Local Open Scope C_scope.

Theorem H_ZX_to_ZX_consistent : forall nIn nOut (zx : H_ZX nIn nOut),
  exists (θ : R), H_ZX_semantics zx = (Cexp θ) .* (ZX_semantics (H_ZX_to_ZX zx)).
Proof.
  intros.
  induction zx; try (exists 0%R; autorewrite with Cexp_db; Msimpl; simpl; reflexivity).
  - destruct IHzx1, IHzx2.
    simpl.
    rewrite H, H0.
    autorewrite with scalar_move_db.
    exists (x0+x)%R.
    replace ((2 ^ (nIn0 + nIn1))%nat) with (2 ^ nIn0 * 2 ^ nIn1)%nat by (rewrite Nat.pow_add_r; reflexivity).
    replace ((2 ^ (nOut0 + nOut1))%nat) with (2 ^ nOut0 * 2 ^ nOut1)%nat by (rewrite Nat.pow_add_r; reflexivity).
    apply Mscale_simplify; try reflexivity.
    rewrite Cexp_add; reflexivity.
  - simpl.
    rewrite nStack1_n_kron.
    rewrite ZX_H_is_H.
    rewrite Mscale_kron_n_distr_r.
    rewrite Cexp_pow.
    destruct IHzx1, IHzx2.
    rewrite H, H0.
    autorewrite with scalar_move_db.
    exists ((x + x0) + - (PI / 4 * INR nMid))%R.
    rewrite Mscale_assoc.
    repeat rewrite <- Mmult_assoc.
    apply Mscale_simplify; try reflexivity.
    rewrite Cexp_add.
    rewrite <- Cmult_assoc.
    rewrite Cexp_mul_neg_l.
    rewrite Cexp_add.
    lca.
Qed.

Fixpoint nStack1_H n (zx : H_ZX 1 1) := 
  match n with
  | 0 => H_Empty
  | S n' => H_Stack (zx) (nStack1_H n' zx)
  end.
Notation "n ↑H zx" := (nStack1_H n zx) (at level 41).

Lemma nStack1_H_nStack1 : forall (zx : H_ZX 1 1) n,
  ZX_semantics (H_ZX_to_ZX (nStack1_H n zx)) = ZX_semantics (nStack1 n (H_ZX_to_ZX zx)).
Proof.
  induction n.
  - reflexivity.
  - simpl.
    apply kron_simplify; try reflexivity.
    assumption.
Qed.

Definition H_Wire := (H_Z_Spider 1 1 0).

Lemma H_wire_identity_semantics : H_ZX_semantics H_Wire = I 2.
Proof.
  intros.
  simpl.
  unfold_spider.
  rewrite Cexp_0.
  Msimpl.
  solve_matrix.
Qed.

Global Opaque H_Wire.

Definition H_nWire n := nStack1_H n H_Wire.

Lemma H_nWire_identity : forall n, H_ZX_semantics (H_nWire n) = I (2 ^ n).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite H_wire_identity_semantics.
    restore_dims.
    replace (2 ^ n + (2 ^ n + 0))%nat with (2 * 2 ^n)%nat by lia.
    rewrite <- id_kron.
    rewrite <- IHn.
    reflexivity.
Qed.

Definition H_ZX_H : H_ZX 1 1 := H_Compose (H_Wire) (H_Wire).

Lemma H_ZX_H_is_H : H_ZX_semantics H_ZX_H = hadamard.
Proof.
  intros.
  simpl.
  rewrite H_wire_identity_semantics.
  lma.
Qed.

Lemma ZX_H_to_ZX_hadamard :  □ ∝ (H_ZX_to_ZX H_ZX_H).
Proof.
  intros.
  simpl.
  unfold hadamard_edge.
  simpl.
  remove_empty.
  remove_wire.
  reflexivity.
Qed.

Global Opaque H_ZX_H.

Fixpoint ZX_to_H_ZX {nIn nOut} (zx : ZX nIn nOut) : H_ZX nIn nOut :=
  match zx with
  | Empty => H_Empty
  | X_Spider nIn nOut α => (H_Compose (H_nWire nIn) (H_Compose (H_Z_Spider nIn nOut α) (H_nWire nOut)))
  | Z_Spider nIn nOut α => (H_Z_Spider nIn nOut α)
  | Cap => H_Cap
  | Cup => H_Cup
  | Stack zx0 zx1 => H_Stack (ZX_to_H_ZX zx0) (ZX_to_H_ZX zx1)
  | @Compose _ nMid _ zx0 zx1 => H_Compose (ZX_to_H_ZX zx0) (H_Compose (H_nWire nMid) (ZX_to_H_ZX zx1))
  end.

Theorem ZX_to_H_ZX_consistent : forall nIn nOut (zx : ZX nIn nOut),
  exists θ, ZX_semantics zx = (Cexp θ) .* (H_ZX_semantics (ZX_to_H_ZX zx)).
Proof.
  intros.
  induction zx; try (exists 0%R; autorewrite with Cexp_db; Msimpl; simpl; reflexivity) (* non compositional cases *); 
    try destruct IHzx1, IHzx2 (* Stack / Compose *).
  - simpl. (* X_Spider *)
    exists 0%R.
    rewrite Cexp_0.
    Msimpl.
    unfold_spider.
    rewrite 2 H_nWire_identity.
    Msimpl; try repeat apply WF_mult; try apply WF_plus; try apply WF_scale; try apply WF_mult; restore_dims; try auto with wf_db.
    rewrite Mmult_plus_distr_l; try auto with wf_db.
    rewrite Mmult_plus_distr_r; try auto with wf_db.
    repeat rewrite <- Mmult_assoc.
    rewrite kron_n_mult.
    rewrite (Mmult_assoc _ _ (nIn ⨂ _)).
    restore_dims.
    rewrite kron_n_mult.
    repeat rewrite ket2bra.
    repeat rewrite hadamard_sa.
    apply Mplus_simplify; try reflexivity.
    autorewrite with scalar_move_db.
    apply Mscale_simplify; try reflexivity.
    rewrite <- Mmult_assoc.
    restore_dims.
    rewrite Mmult_assoc.
    restore_dims.
    rewrite 2 kron_n_mult.
    reflexivity.
  - simpl. (* Stack *)
    rewrite H, H0.
    exists (x0 + x)%R.
    autorewrite with scalar_move_db.
    replace ((2 ^ (nIn0 + nIn1))%nat) with (2 ^ nIn0 * 2 ^ nIn1)%nat by (rewrite Nat.pow_add_r; reflexivity).
    replace ((2 ^ (nOut0 + nOut1))%nat) with (2 ^ nOut0 * 2 ^ nOut1)%nat by (rewrite Nat.pow_add_r; reflexivity).
    apply Mscale_simplify; try reflexivity.
    rewrite Cexp_add; reflexivity.
  - simpl. (* Compose *)
    rewrite H, H0.
    rewrite H_nWire_identity.
    Msimpl; try auto 10 with wf_db.
    exists (x + x0)%R.
    autorewrite with scalar_move_db.
    apply Mscale_simplify; try (rewrite Cexp_add; reflexivity).
    apply Mmult_simplify; try reflexivity.
    rewrite Mmult_assoc.
    rewrite kron_n_mult.
    rewrite MmultHH.
    rewrite kron_n_I.
    Msimpl.
    reflexivity.
Qed.

Lemma Cexp_Cexp_neg : forall n m (A B : Matrix n m), (exists θ, A = (Cexp θ) .* B) -> (exists θ', B = (Cexp (θ')) .* A).
Proof.
  intros.
  destruct H.
  exists (-x)%R.
  rewrite H.
  rewrite Mscale_assoc.
  rewrite <- Cexp_add.
  rewrite Rplus_opp_l.
  autorewrite with Cexp_db.
  lma.
Qed.

Theorem ZX_to_H_ZX_consistent' : forall nIn nOut (zx : ZX nIn nOut),
  exists θ, (H_ZX_semantics (ZX_to_H_ZX zx)) = (Cexp θ) .* (ZX_semantics zx).
Proof.
  intros.
  apply Cexp_Cexp_neg.
  apply ZX_to_H_ZX_consistent.
Qed.

Theorem H_ZX_to_ZX_consistent' : forall nIn nOut (zx : H_ZX nIn nOut),
  exists θ, (ZX_semantics (H_ZX_to_ZX zx)) = (Cexp θ) .* (H_ZX_semantics zx).
Proof.
  intros.
  apply Cexp_Cexp_neg.
  apply H_ZX_to_ZX_consistent.
Qed.

Lemma ZX_to_H_ZX_compat : forall nIn nOut (zx0 zx1 : ZX nIn nOut), 
  zx0 ∝ zx1 -> (ZX_to_H_ZX zx0) ∝H (ZX_to_H_ZX zx1).
Proof.
  intros.
  destruct H.
  destruct H.
  unfold H_proportional.
  unfold proportional_general.
  assert (exists θ, (H_ZX_semantics (ZX_to_H_ZX zx0)) = (Cexp θ) .* (ZX_semantics zx0)) by apply ZX_to_H_ZX_consistent'.
  assert (exists θ, (H_ZX_semantics (ZX_to_H_ZX zx1)) = (Cexp θ) .* (ZX_semantics zx1)) by apply ZX_to_H_ZX_consistent'.
  destruct H1, H2.
  rewrite H1.
  rewrite H2.
  rewrite H.
  exists (Cexp x0 * x * Cexp (-x1))%C.
  split.
  - rewrite 2 Mscale_assoc.
    apply Mscale_simplify; try reflexivity.
    rewrite <- Cmult_assoc.
    rewrite <- Cexp_add.
    rewrite Rplus_opp_l.
    rewrite Cexp_0.
    lca.
  - repeat apply Cmult_neq_0; try nonzero.
    assumption.
Qed.

Lemma H_ZX_to_ZX_compat : forall nIn nOut (zx0 zx1 : H_ZX nIn nOut), 
  zx0 ∝H zx1 -> (H_ZX_to_ZX zx0) ∝ (H_ZX_to_ZX zx1).
Proof.
  intros.
  destruct H.
  destruct H.
  unfold proportional.
  unfold proportional_general.
  assert (exists θ, (ZX_semantics (H_ZX_to_ZX zx0)) = (Cexp θ) .* (H_ZX_semantics zx0)) by apply H_ZX_to_ZX_consistent'.
  assert (exists θ, (ZX_semantics (H_ZX_to_ZX zx1)) = (Cexp θ) .* (H_ZX_semantics zx1)) by apply H_ZX_to_ZX_consistent'.
  destruct H1, H2.
  rewrite H1.
  rewrite H2.
  rewrite H.
  exists (Cexp x0 * x * Cexp (-x1))%C.
  split.
  - rewrite 2 Mscale_assoc.
    apply Mscale_simplify; try reflexivity.
    rewrite <- Cmult_assoc.
    rewrite <- Cexp_add.
    rewrite Rplus_opp_l.
    rewrite Cexp_0.
    lca.
  - repeat apply Cmult_neq_0; try nonzero.
    assumption.
Qed.

Add Parametric Relation (nIn nOut : nat) : (H_ZX nIn nOut) (@H_proportional nIn nOut)
  reflexivity proved by H_proportional_refl
  symmetry proved by H_proportional_symm
  transitivity proved by H_proportional_trans
  as H_ZX_prop_equiv_rel.

Add Parametric Morphism (nIn nOut : nat) : (@ZX_to_H_ZX nIn nOut)
  with signature (@proportional nIn nOut) ==> (@H_proportional nIn nOut) as ZX_to_H_ZX_mor.
Proof. apply ZX_to_H_ZX_compat. Qed.

Add Parametric Morphism (nIn nOut : nat) : (@H_ZX_to_ZX nIn nOut)
  with signature (@H_proportional nIn nOut) ==> (@proportional nIn nOut) as H_ZX_to_ZX_mor.
Proof. apply H_ZX_to_ZX_compat. Qed. 


Lemma H_nStack1_compat :
  forall n,
    forall zx0 zx1 : H_ZX 1 1, zx0 ∝H zx1 ->
    n ↑H zx0 ∝H n ↑H zx1.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite H.
    reflexivity.
Qed.

Add Parametric Morphism (n : nat) : (nStack1_H n)
  with signature (@H_proportional 1 1) ==> 
                 (@H_proportional n n) as H_nstack1_mor.
Proof. apply H_nStack1_compat. Qed.

Lemma H_compose_compat :
  forall nIn nMid nOut,
    forall zx0 zx1 : H_ZX nIn  nMid, zx0 ∝H zx1 ->
    forall zx2 zx3 : H_ZX nMid nOut, zx2 ∝H zx3 ->
    (H_Compose zx0 zx2) ∝H (H_Compose zx1 zx3).
Proof.
  intros.
  destruct H; destruct H; destruct H0; destruct H0.
  simpl.
  exists (x * x0).
  split.
  - simpl; rewrite H; rewrite H0.
    rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    restore_dims.
    rewrite Mscale_mult_dist_l.
    rewrite Mscale_assoc.
    reflexivity.
  - apply Cmult_neq_0; try assumption.
Qed.

Add Parametric Morphism (nIn nMid nOut : nat)  : (@H_Compose nIn nMid nOut)
  with signature (@H_proportional nIn nMid) ==> (@H_proportional nMid nOut) ==> 
                 (@H_proportional nIn nOut) as H_compose_mor.
Proof. apply H_compose_compat; assumption. Qed.

Lemma ZX_H_ZX_matrix_compat : forall {nIn nOut} (zx : ZX nIn nOut) (M : Matrix (2 ^ nIn) (2 ^ nOut)), 
  (exists (c : C), ZX_semantics zx = c .* M /\ c <> C0) -> (exists c, H_ZX_semantics (ZX_to_H_ZX zx) = c .* M /\ c <> C0).
Proof.
  intros.
  assert (exists θ, (H_ZX_semantics (ZX_to_H_ZX zx)) = (Cexp θ) .* (ZX_semantics zx)) by apply ZX_to_H_ZX_consistent'.
  destruct H0.
  rewrite H0.
  destruct H.
  destruct H.
  rewrite H.
  exists (Cexp x * x0).
  split; try (apply Cmult_neq_0; try assumption; try nonzero).
  rewrite <- Mscale_assoc.
  reflexivity.
Qed.

Lemma H_ZX_ZX_matrix_compat : forall {nIn nOut} (zx : H_ZX nIn nOut) (M : Matrix (2 ^ nIn) (2 ^ nOut)), 
  (exists c, H_ZX_semantics zx = c .* M /\ c <> C0) -> (exists c, ZX_semantics (H_ZX_to_ZX zx) = c .* M /\ c <> C0).
Proof.
  intros.
  assert (exists θ, (ZX_semantics (H_ZX_to_ZX zx)) = (Cexp θ) .* (H_ZX_semantics zx)) by apply H_ZX_to_ZX_consistent'.
  destruct H0.
  rewrite H0.
  destruct H.
  destruct H.
  rewrite H.
  exists (Cexp x * x0).
  split; try (apply Cmult_neq_0; try assumption; try nonzero).
  rewrite <- Mscale_assoc.
  reflexivity.
Qed.

Local Transparent Wire.
Lemma ZX_to_H_ZX_wire : H_ZX_semantics (ZX_to_H_ZX —) = I 2.
Proof.
  intros.
  unfold Wire.
  simpl.
  unfold_spider.
  autorewrite with Cexp_db.
  Msimpl.
  solve_matrix.
Qed.

Local Transparent H_Wire.
Local Transparent H_nWire.
Local Transparent nWire.

Lemma H_nWire_ZX_to_H_ZX_nWire : forall n, (H_nWire n) ∝H (ZX_to_H_ZX (nWire n)).
Proof.
  intros.
  induction n; try reflexivity.
  unfold H_nWire.
  simpl.
  unfold H_nWire in IHn.
  rewrite IHn.
  rewrite <- IHn.
  unfold nWire.
  unfold H_Wire.
  unfold H_Wire, nWire in IHn.
  rewrite <- IHn.
  reflexivity.
Qed.
Local Opaque H_nWire.
Local Opaque nWire.

Lemma ZX_H_to_ZX_Wire :  — ∝ (H_ZX_to_ZX H_Wire).
Proof.
  intros.
  unfold proportional.
  simpl.
  unfold Wire.
  reflexivity.
Qed.

Local Opaque H_Wire.
Local Opaque Wire.

Local Transparent H_ZX_H.

Lemma ZX_H_H_ZX_sem : exists c, H_ZX_semantics (ZX_to_H_ZX □) = c .* hadamard /\ c <> C0.
Proof.
  apply ZX_H_ZX_matrix_compat.
  rewrite ZX_H_is_H.
  prop_exist_non_zero (Cexp (PI / 4)).
Qed.
Local Opaque H_ZX_H.


Lemma nHadamard_H_semantics : forall n, exists c, H_ZX_semantics (ZX_to_H_ZX (n ↑ □)) = c .* n ⨂ hadamard /\ c <> C0.
Proof.
  intros.
  induction n; try (prop_exist_non_zero 1%R; lma).
  simpl.
  destruct IHn.
  assert (exists c, H_ZX_semantics (ZX_to_H_ZX □) = c .* hadamard /\ c <> C0) by apply ZX_H_H_ZX_sem.
  destruct H, H0.
  destruct H0.
  exists (x * x0); split; try (apply Cmult_neq_0; assumption).
  rewrite H.
  rewrite H0.
  autorewrite with scalar_move_db.
  replace (hadamard) with (1 ⨂ hadamard) by (simpl; remove_empty; Msimpl; reflexivity).
  restore_dims.
  replace ((2 ^ 1 * (2 ^ 1) ^ n))%nat with (((2 ^ 1) ^ n * 2 ^ 1)%nat) by lia.
  apply Mscale_simplify; try reflexivity.
  replace (n ⨂ (1 ⨂ hadamard)) with (n ⨂ hadamard) by (simpl; remove_empty; Msimpl; reflexivity).
  rewrite <- kron_n_m_split; try auto with wf_db.
  rewrite <- kron_n_m_split; try auto with wf_db.
  apply n_kron_simplify; try reflexivity.
  lia.
Qed.

Lemma H_ZX_ZX_involutive : forall nIn nOut (zx : H_ZX nIn nOut), ZX_to_H_ZX (H_ZX_to_ZX zx) ∝H zx.
Proof.
  intros.
  unfold H_proportional, proportional_general.
  induction zx; try (prop_exist_non_zero 1%R; autorewrite with Cexp_db; Msimpl; simpl; reflexivity) (* non compositional cases *); 
    try (destruct IHzx1, IHzx2 (* Stack / Compose *); simpl; destruct H, H0).
  - simpl.
    exists (x0 * x); split; try (apply Cmult_neq_0; assumption).
    rewrite H, H0.
    autorewrite with scalar_move_db.
    reflexivity.
  - rewrite H_nWire_identity.
    Msimpl.
    assert (forall n, exists c, H_ZX_semantics (ZX_to_H_ZX (n ↑ □)) = c .* n ⨂ hadamard /\ c <> C0) by exact nHadamard_H_semantics.
    specialize (H3 nMid).
    destruct H3.
    destruct H3.
    rewrite H3.
    autorewrite with scalar_move_db.
    rewrite kron_n_mult.
    rewrite MmultHH.
    rewrite kron_n_I.
    Msimpl.
    rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc (nMid ⨂ hadamard) _ _).
    rewrite kron_n_mult.
    rewrite MmultHH.
    rewrite kron_n_I.
    Msimpl.
    rewrite H, H0.
    autorewrite with scalar_move_db.
    exists (x1 * x * x0); split; try (apply Cmult_neq_0; try apply Cmult_neq_0; assumption).
    reflexivity.
Qed.

Lemma ZX_ZX_H_Wire_involutive : forall n, H_ZX_to_ZX (ZX_to_H_ZX (nWire n)) ∝ nWire n.
Proof.
  intros.
  assert (exists (c : C), H_ZX_semantics (ZX_to_H_ZX (nWire (n))) = c .* I (2 ^ (n)) /\ c <> C0).
  {
    apply ZX_H_ZX_matrix_compat.
    prop_exist_non_zero 1%R.
    Msimpl.
    apply nwire_identity_semantics.
  }
  assert (exists (c : C), ZX_semantics (H_ZX_to_ZX (ZX_to_H_ZX (nWire (n)))) = c .* I (2 ^ (n)) /\ c <> C0).
  {
    apply H_ZX_ZX_matrix_compat.
    apply H.
  }
  destruct H0.
  destruct H0.
  exists x; split; try assumption.
  rewrite nwire_identity_semantics.
  rewrite H0.
  reflexivity.
Qed.

Lemma ZX_H_ZX_involutive : forall nIn nOut (zx : ZX nIn nOut), H_ZX_to_ZX (ZX_to_H_ZX zx) ∝ zx.
Proof.
  intros.
  induction zx; try (prop_exist_non_zero 1%R; autorewrite with Cexp_db; Msimpl; simpl; reflexivity) (* non compositional cases *); 
  try (destruct IHzx1, IHzx2 (* Stack / Compose *); simpl; destruct H, H0).
  - simpl.
    rewrite 2 H_nWire_ZX_to_H_ZX_nWire.
    rewrite 2 ZX_ZX_H_Wire_involutive.
    exists (Cexp (PI / 4) ^ nOut * Cexp (PI / 4) ^ nIn); split; try (rewrite 2 Cexp_pow; apply Cmult_neq_0; nonzero).
    simpl.
    repeat rewrite nStack1_n_kron.
    rewrite ZX_H_is_H.
    rewrite 2 nwire_identity_semantics.
    Msimpl.
    unfold_spider.
    rewrite Mmult_plus_distr_l; try auto with wf_db.
    rewrite Mmult_plus_distr_r; try auto with wf_db.
    repeat rewrite <- Mmult_assoc.
    rewrite kron_n_mult.
    rewrite (Mmult_assoc _ _ (nIn ⨂ _)).
    restore_dims.
    rewrite kron_n_mult.
    repeat rewrite ket2bra.
    repeat rewrite hadamard_sa.
    repeat rewrite Mscale_kron_n_distr_r.
    autorewrite with scalar_move_db.
    repeat rewrite Mscale_kron_n_distr_r.
    repeat rewrite <- Mscale_assoc.
    rewrite 2 Mscale_plus_distr_r.
    apply Mplus_simplify.
    + restore_dims.
      autorewrite with scalar_move_db.
      rewrite <- Mscale_assoc.
      rewrite <- Mscale_mult_dist_l.
      rewrite <- Mscale_mult_dist_r.
      rewrite <- Mscale_mult_dist_l.
      reflexivity.
    + autorewrite with scalar_move_db.
      apply Mscale_simplify; try lca.
      rewrite <- Mmult_assoc.
      rewrite kron_n_mult.
      rewrite Mmult_assoc.
      restore_dims.
      rewrite kron_n_mult.
      reflexivity.
  - exists (x0 * x); split; try (apply Cmult_neq_0; assumption).
    simpl.
    rewrite H.  
    rewrite H0.
    autorewrite with scalar_move_db.
    reflexivity.
  - simpl.
    assert (exists (c : C), ZX_semantics (H_ZX_to_ZX (H_nWire (nMid))) = c .* I (2 ^ (nMid)) /\ c <> C0).
    {
      apply H_ZX_ZX_matrix_compat.
      rewrite H_nWire_identity.
      prop_exist_non_zero 1%R.
      lma.
    }
    destruct H3.
    destruct H3.
    exists (x * x1 * x0 * Cexp (PI / 4) ^ nMid * Cexp (PI / 4) ^ nMid); split; 
      try (repeat apply Cmult_neq_0; try assumption; try (rewrite Cexp_pow; nonzero)) (* non zero constant *).
    simpl.
    rewrite H, H0, H3.
    rewrite nStack1_n_kron.
    rewrite ZX_H_is_H.
    repeat rewrite Mscale_kron_n_distr_r.
    autorewrite with scalar_move_db.
    Msimpl.
    rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc _ (nMid ⨂ _) (ZX_semantics _)).
    rewrite kron_n_mult.
    rewrite MmultHH.
    rewrite kron_n_I.
    Msimpl.
    reflexivity.
Qed.
