Require Import CoreData.
Require Import CoreRules.

Definition zx_right_unitor {n} := 
    cast (n + 0) n (Nat.add_0_r n) (eq_refl n) (n_wire n).

Definition zx_inv_right_unitor {n} := 
    cast n (n + 0) (eq_refl n) (Nat.add_0_r n) (n_wire n).

Lemma zx_right_inv_compose : forall {n},
    zx_right_unitor ⟷ zx_inv_right_unitor ∝ n_wire (n + 0).
Proof.
    intros.
    unfold zx_right_unitor. unfold zx_inv_right_unitor.
    rewrite cast_compose_l.
    cleanup_zx. simpl_casts. reflexivity.
Qed.

Lemma zx_inv_right_compose : forall {n},
    zx_inv_right_unitor ⟷ zx_right_unitor ∝ n_wire n.
Proof.
    intros.
    unfold zx_right_unitor. unfold zx_inv_right_unitor.
    rewrite cast_compose_r.
    cleanup_zx. simpl_casts. reflexivity.
Qed.

Lemma zx_right_unitor_cohere : forall {n m} (zx : ZX n m), 
    zx_right_unitor ⟷ zx ∝ zx ↕ (n_wire 0) ⟷ zx_right_unitor.
Proof.
    intros.
    unfold zx_right_unitor; cleanup_zx.
    rewrite <- cast_compose_mid_contract.
    cleanup_zx.
    rewrite cast_compose_l; simpl_casts.
    rewrite nwire_removal_l.
    reflexivity.
    Unshelve. all: easy.
Qed.