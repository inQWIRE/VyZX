Require Import CoreData.
Require Import CoreRules.

Definition pad_bot {n m} pad (zx : ZX n m) : ZX (n + pad) (m + pad) := zx ↕ (nWire pad).

Definition pad_top {n m} pad (zx : ZX n m) : ZX (pad + n) (pad + m) := (nWire pad) ↕ zx.

Definition pad_bot_1 {n m} (zx : ZX n m) : ZX (S n) (S m) := cast _ _ (eq_sym (Nat.add_1_r n)) (eq_sym (Nat.add_1_r m)) (pad_bot 1 zx).

Notation padbt zx := (pad_bot _ (pad_top _ zx)).
Notation padtb zx := (pad_top _ (pad_bot _ zx)).

Lemma pad_top_contract : forall {n m} (zx : ZX n m) pad1 pad2, pad_top pad1 (pad_top pad2 zx) ∝ cast (pad1 + (pad2 + n)) (pad1 + (pad2 + m)) (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _) (pad_top (pad1 + pad2) zx).
Proof.
  intros.
  unfold pad_top.
  rewrite ZX_Stack_assoc_back.
  simpl_casts.
  rewrite nWire_stack.
  easy.
Qed.

Lemma pad_bot_1_simpl : forall {n m} (zx : ZX n m), pad_bot 1 zx ∝ cast _ _ (Nat.add_1_r n) (Nat.add_1_r m) (pad_bot_1 zx).
Proof.
  intros.
  unfold pad_bot_1.
  simpl_casts.
  easy.
Qed.

Lemma pad_bot_contract : forall {n m} (zx : ZX n m) pad1 pad2, pad_bot pad2 (pad_bot pad1 zx) ∝ cast (n + pad1 + pad2) (m + pad1 + pad2) (eq_sym (Nat.add_assoc _ _ _)) (eq_sym (Nat.add_assoc _ _ _)) (pad_bot (pad1 + pad2) zx).
Proof.
  intros.
  unfold pad_bot.
  rewrite ZX_Stack_assoc.
  simpl_casts.
  rewrite nWire_stack.
  easy.
Qed.

Lemma pad_top_bot_comm : forall {n m} (zx : ZX n m) padT padB, (pad_top padT (pad_bot padB zx)) ∝ cast (padT + (n + padB)) (padT + (m + padB)) (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _) (pad_bot padB (pad_top padT zx)).
Proof.
  intros.
  unfold pad_top, pad_bot.
  rewrite ZX_Stack_assoc_back.
  simpl_casts.
  easy.
Qed.


Lemma pad_bot_top_comm : forall {n m} (zx : ZX n m) padT padB, (pad_bot padB (pad_top padT zx)) ∝ cast (padT + n + padB) (padT + m + padB) (eq_sym (Nat.add_assoc _ _ _)) (eq_sym (Nat.add_assoc _ _ _)) (pad_top padT (pad_bot padB zx)).
Proof.
  intros.
  unfold pad_top, pad_bot.
  rewrite ZX_Stack_assoc.
  simpl_casts.
  easy.
Qed.

Lemma pad_top_bot_semantics : forall {n m} (zx : ZX n m) padT padB, ZX_semantics (pad_top padT (pad_bot padB zx)) = I (2 ^ padT) ⊗ (ZX_semantics zx) ⊗ I (2 ^ padB).
Proof.
  intros. simpl. rewrite 2 nWire_semantics. rewrite kron_assoc; auto with wf_db.
Qed.

Lemma pad_bot_top_semantics : forall {n m} (zx : ZX n m) padT padB, ZX_semantics (pad_bot padB (pad_top padT zx)) = I (2 ^ padT) ⊗ (ZX_semantics zx) ⊗ I (2 ^ padB).
Proof.
  intros. simpl. rewrite 2 nWire_semantics. easy.
Qed.