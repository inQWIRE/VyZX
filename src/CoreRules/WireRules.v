Require Import CoreData.CoreData.
Require Import StackRules.
Require Import castRules.

Local Open Scope ZX_scope.

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

Lemma Z_2_0_0_is_cap : Z 2 0 0 ∝ ⊃.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
  apply Cexp_0.
Qed.

Lemma Z_0_2_0_is_cup : Z 0 2 0 ∝ ⊂.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
  apply Cexp_0.
Qed.

Lemma yank_r : 
  (⊂ ↕ —) ⟷ (— ↕ ⊃) ∝ —.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
Qed.

Lemma yank_l : 
  (— ↕ ⊂) ⟷ (⊃ ↕ —) ∝ —.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
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
  induction p.
  - repeat rewrite stack_empty_r.
    eapply (cast_diagrams n o).
    repeat rewrite cast_contract.
    rewrite cast_id.
    rewrite cast_compose_distribute.
    simpl_casts.
    erewrite (cast_compose_mid m _ ($ n, m + 0 ::: zx0 $)).
    simpl_casts.
    easy.
    Unshelve.
    all: lia.
  - rewrite n_stack1_r.
    repeat rewrite cast_stack_r.
    eapply (cast_diagrams (n + (p + 1)) (o + (p + 1))).
    rewrite cast_contract.
    rewrite cast_id.
    rewrite cast_compose_distribute.
    simpl_casts.
    erewrite (cast_compose_mid (m + (p + 1)) _ 
                  ($ n + (p + 1), m + (S p) ::: zx0 ↕ (n_wire p ↕ —)$)).
    simpl_casts.
    rewrite 3 stack_assoc_back.
    eapply (cast_diagrams (n + p + 1) (o + p + 1)).
    rewrite cast_contract.
    rewrite cast_id.
    rewrite cast_compose_distribute.
    rewrite 2 cast_contract.
    erewrite (cast_compose_mid (m + p + 1) _ 
                  ($ n + p + 1, m + (p + 1) ::: zx0 ↕ n_wire p ↕ — $)).
    simpl_casts.
    rewrite <- stack_wire_distribute_r.
    rewrite <- IHp.
    easy.
    Unshelve.
    all: lia.
Qed.

Lemma wire_to_n_wire : 
  — ∝ n_wire 1.
Proof.
  simpl.
  rewrite stack_empty_r.
  simpl_casts.
  easy.
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
  Msimpl; simpl.
  solve_matrix.
Qed.