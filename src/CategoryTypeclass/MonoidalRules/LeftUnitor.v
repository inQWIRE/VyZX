Require Import CoreData.
Require Import CoreRules.

Definition zx_left_unitor {n} := 
    cast (0 + n) n (Nat.add_0_l n) (eq_refl n) (n_wire n).

Definition zx_inv_left_unitor {n} := 
    cast n (0 + n) (eq_refl n) (Nat.add_0_l n) (n_wire n).

Lemma zx_left_inv_compose : forall {n},
    zx_left_unitor ⟷ zx_inv_left_unitor ∝ n_wire (0 + n).
Proof.
    intros. 
    unfold zx_left_unitor. unfold zx_inv_left_unitor.
    simpl_casts. cleanup_zx. reflexivity.
Qed.

Lemma zx_inv_left_compose : forall {n}, 
    zx_inv_left_unitor ⟷ zx_left_unitor ∝ n_wire n.
Proof.
    intros. 
    unfold zx_left_unitor. unfold zx_inv_left_unitor.
    simpl_casts. cleanup_zx. reflexivity.
Qed.

Lemma zx_left_unitor_cohere : forall {n m} (zx : ZX n m), 
    zx_left_unitor ⟷ zx ∝ (n_wire 0) ↕ zx ⟷ zx_left_unitor.
Proof.
    intros.
    unfold zx_left_unitor.
    simpl_casts.
    rewrite nwire_removal_l.
    rewrite stack_empty_l.
    rewrite nwire_removal_r.
    reflexivity.
Qed.