Require Import CoreData.
Require Import CoreRules.

Definition pad_bot {n m} pad (zx : ZX n m) : ZX (n + pad) (m + pad) := zx ↕ (n_wire pad).

Definition pad_top {n m} pad (zx : ZX n m) : ZX (pad + n) (pad + m) := (n_wire pad) ↕ zx.

Definition pad_bot_1 {n m} (zx : ZX n m) : ZX (S n) (S m) := cast _ _ (eq_sym (Nat.add_1_r n)) (eq_sym (Nat.add_1_r m)) (pad_bot 1 zx).

Notation padbt zx := (pad_bot _ (pad_top _ zx)).
Notation padtb zx := (pad_top _ (pad_bot _ zx)).

Lemma pad_top_contract : forall {n m} (zx : ZX n m) pad1 pad2 prfn prfm, 
  pad_top pad1 (pad_top pad2 zx)  ∝= cast (pad1 + (pad2 + n)) (pad1 + (pad2 + m)) prfn prfm (pad_top (pad1 + pad2) zx).
Proof.
  intros.
  unfold pad_top.
  rewrite stack_assoc_back.
  simpl_casts.
  bundle_wires.
  easy.
Unshelve.
all: lia.
Qed.

Lemma pad_bot_1_simpl : forall {n m} (zx : ZX n m) prfn prfm, 
  pad_bot 1 zx ∝= cast _ _ prfn prfm (pad_bot_1 zx).
Proof.
  intros.
  unfold pad_bot_1.
  simpl_casts.
  easy.
Qed.

Lemma pad_bot_contract : forall {n m} (zx : ZX n m) pad1 pad2 prfn prfm, pad_bot pad2 (pad_bot pad1 zx) ∝= cast (n + pad1 + pad2) (m + pad1 + pad2) prfn prfm (pad_bot (pad1 + pad2) zx).
Proof.
  intros.
  unfold pad_bot.
  rewrite stack_assoc.
  simpl_casts.
  bundle_wires.
  easy.
Unshelve.
all: lia.
Qed.

Lemma pad_top_bot_comm : forall {n m} (zx : ZX n m) padT padB prfn prfm, 
  (pad_top padT (pad_bot padB zx)) ∝= cast (padT + (n + padB)) (padT + (m + padB)) prfn prfm (pad_bot padB (pad_top padT zx)).
Proof.
  intros.
  unfold pad_top, pad_bot.
  rewrite stack_assoc_back.
  simpl_casts.
  easy.
Unshelve.
all: lia.
Qed.


Lemma pad_bot_top_comm : forall {n m} (zx : ZX n m) padT padB prfn prfm, 
  (pad_bot padB (pad_top padT zx)) ∝= cast (padT + n + padB) (padT + m + padB) prfn prfm (pad_top padT (pad_bot padB zx)).
Proof.
  intros.
  unfold pad_top, pad_bot.
  rewrite stack_assoc.
  simpl_casts.
  easy.
Unshelve.
all: lia.
Qed.

Lemma pad_top_bot_semantics : forall {n m} (zx : ZX n m) padT padB, ⟦ pad_top padT (pad_bot padB zx) ⟧ = I (2 ^ padT) ⊗ (⟦ zx ⟧) ⊗ I (2 ^ padB).
Proof.
  intros. simpl. rewrite 2 n_wire_semantics. rewrite kron_assoc; auto with wf_db.
Qed.

Lemma pad_bot_top_semantics : forall {n m} (zx : ZX n m) padT padB, ⟦ pad_bot padB (pad_top padT zx) ⟧ = I (2 ^ padT) ⊗ (⟦ zx ⟧) ⊗ I (2 ^ padB).
Proof.
  intros. simpl. rewrite 2 n_wire_semantics. easy.
Qed.