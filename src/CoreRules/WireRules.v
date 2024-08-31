Require Import CoreData.CoreData.
Require Import StackRules.
Require Import CastRules.

Local Open Scope ZX_scope.

Lemma Z_0_is_wire : Z 1 1 0 ∝ —.
Proof.
  intros.
  prop_exists_nonzero 1.
  rewrite Mscale_1_l.
  lma'.
  apply Cexp_0.
Qed.

Lemma Z_2_0_0_is_cap : Z 2 0 0 ∝ ⊃.
Proof.
  prop_exists_nonzero 1.
  rewrite Mscale_1_l.
  lma'.
  apply Cexp_0.
Qed.

Lemma Z_0_2_0_is_cup : Z 0 2 0 ∝ ⊂.
Proof.
  prop_exists_nonzero 1.
  rewrite Mscale_1_l.
  lma'.
  apply Cexp_0.
Qed.

Lemma yank_r : 
  (⊂ ↕ —) ⟷ (— ↕ ⊃) ∝ —.
Proof.
  prop_exists_nonzero 1.
  rewrite Mscale_1_l.
  lma'.
Qed.

Lemma yank_l : 
  (— ↕ ⊂) ⟷ (⊃ ↕ —) ∝ —.
Proof.
  prop_exists_nonzero 1.
  rewrite Mscale_1_l.
  lma'.
Qed.

Lemma n_wire_stack : forall n m, n_wire n ↕ n_wire m ∝ n_wire (n + m).
Proof. 
  prop_exists_nonzero 1. 
  simpl. 
  rewrite 3 n_wire_semantics, id_kron.
  Msimpl.
  rewrite Nat.pow_add_r.
  easy.
Qed.

Lemma X_0_is_wire : X 1 1 0 ∝ —.
Proof.
  apply colorswap_diagrams.
  simpl.
  apply Z_0_is_wire.
Qed.

Lemma stack_nwire_distribute_r : forall {n m o p} (zx0 : ZX n m) (zx1 : ZX m o),
(zx0 ⟷ zx1) ↕ n_wire p ∝ (zx0 ↕ n_wire p) ⟷ (zx1 ↕ n_wire p).
Proof.
  intros.
  prop_exists_nonzero 1.
  rewrite Mscale_1_l.
  cbn.
  rewrite n_wire_semantics.
  restore_dims.
  apply kron_id_dist_r; auto_wf.
Qed.

Lemma wire_to_n_wire : 
  — ∝ n_wire 1.
Proof.
  simpl.
  auto_cast_eqn (rewrite stack_empty_r).
  now rewrite cast_id.
Qed.

Lemma wire_transpose : —⊤ ∝ —.
Proof. easy. Qed.

Lemma n_wire_transpose : forall n, (n_wire n)⊤ = n_wire n.
Proof.
  intros.
  induction n.
  - easy.
  - simpl.
    rewrite IHn.
    easy.
Qed. 

Lemma n_wire_colorswap : forall n, ⊙ (n_wire n) = n_wire n.
Proof.
  intros.
  induction n.
  - easy.
  - simpl.
    rewrite IHn.
    easy.
Qed.

Lemma wire_loop : — ∝ (⊂ ↕ —) ⟷ (— ↕ ⨉) ⟷ (⊃ ↕ —).
Proof.
  prop_exists_nonzero 1.
  rewrite Mscale_1_l.
  prep_matrix_equivalence.
  cbn.
  rewrite <- (make_WF_equiv _ _ (list2D_to_matrix _)).
  rewrite <- (make_WF_equiv _ _ (list2D_to_matrix (_ :: _ :: _))).
  match goal with |- _ ≡ ?B => compute_matrix B end.
  now by_cell.
Qed.

Lemma n_stack_n_wire_1_n_wire : forall n, n ↑ (n_wire 1) ∝ n_wire n.
Proof.
  intros. rewrite <- wire_to_n_wire. easy.
Qed.

Lemma n_wire_grow_r : forall n prfn prfm, n_wire (S n) ∝ cast _ _ prfn prfm (n_wire n ↕ —).
Proof.
  intros.
  rewrite wire_to_n_wire at 3.
  rewrite n_wire_stack.
  rewrite (@cast_n_wire (n + 1) (S n) prfn prfm).
  easy.
Qed.

Lemma box_compose : □ ⟷ □ ∝ —.
Proof.
  prop_exists_nonzero 1.
  Msimpl.
  simpl.
  rewrite MmultHH.
  easy.
Qed.