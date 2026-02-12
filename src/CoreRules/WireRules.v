Require Import CoreData.CoreData.
Require Import StackRules.
Require Import CastRules.

Local Open Scope ZX_scope.

(** Rules relating to wires ([—]) and [n_wire]s *)

Lemma Z_0_is_wire : Z 1 1 0 ∝= —.
Proof.
  lma'.
  now rewrite Cexp_0.
Qed.

Lemma Z_2_0_0_is_cap : Z 2 0 0 ∝= ⊃.
Proof.
  lma'.
  now rewrite Cexp_0.
Qed.

Lemma Z_0_2_0_is_cup : Z 0 2 0 ∝= ⊂.
Proof.
  lma'.
  now rewrite Cexp_0.
Qed.

Lemma yank_r : 
  (⊂ ↕ —) ⟷ (— ↕ ⊃) ∝= —.
Proof.
  lma'.
Qed.

Lemma yank_l : 
  (— ↕ ⊂) ⟷ (⊃ ↕ —) ∝= —.
Proof.
  lma'.
Qed.

Lemma n_wire_stack : forall n m, 
  n_wire n ↕ n_wire m ∝= n_wire (n + m).
Proof.
  intros n m.
  unfold proportional_by_1.
  cbn.
  rewrite 3!n_wire_semantics.
  rewrite id_kron.
  now unify_pows_two.
Qed.

Lemma X_0_is_wire : X 1 1 0 ∝= —.
Proof.
  apply colorswap_diagrams_eq.
  simpl.
  apply Z_0_is_wire.
Qed.

Lemma wire_to_n_wire : 
  — ∝= n_wire 1.
Proof.
  symmetry.
  apply nstack1_1.
Qed.

Lemma wire_transpose : —⊤ = —.
Proof. reflexivity. Qed.

Lemma n_wire_colorswap : forall n, ⊙ (n_wire n) = n_wire n.
Proof.
  intros.
  apply nstack1_colorswap.
Qed.

Lemma wire_loop : — ∝= (⊂ ↕ —) ⟷ (— ↕ ⨉) ⟷ (⊃ ↕ —).
Proof.
  unfold proportional_by_1.
  prep_matrix_equivalence.
  cbn.
  rewrite 2!Kronecker.kron_I_r, Kronecker.kron_I_l.
  by_cell; cbn; lca.
Qed.

Lemma n_stack_n_wire_1_n_wire : forall n, n ↑ (n_wire 1) ∝= n_wire n.
Proof.
  intros. rewrite <- wire_to_n_wire. reflexivity.
Qed.

Import Setoid.

Lemma ereflexivity {A} {R : relation A} `{!Reflexive R} x y : x = y -> R x y.
Proof.
  now intros ->.
Qed.

Lemma n_wire_grow_r : forall n, n_wire (S n) ∝= 
  cast _ _ (Nat.add_comm 1 n) (ltac:(lia) : 1 + n = n + 1)%nat (n_wire n ↕ —).
Proof.
  intros.
  rewrite wire_to_n_wire.
  rewrite n_wire_stack.
  now rewrite cast_n_wire.
Qed.

Lemma box_compose : □ ⟷ □ ∝= —.
Proof.
  apply MmultHH.
Qed.