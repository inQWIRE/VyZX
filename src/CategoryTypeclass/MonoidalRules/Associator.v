Require Import CoreData.
Require Import CoreRules.

Definition zx_associator {n m o} :=
    let l := (n + m + o)%nat in
    let r := (n + (m + o))%nat in
    let assoc := Nat.add_assoc n m o in
        cast l r (eq_refl l) assoc (n_wire l).

Definition zx_inv_associator {n m o} :=
    let l := (n + (m + o))%nat in
    let r := (n + m + o)%nat in
    let assoc := Nat.add_assoc n m o in 
        cast l r (eq_refl l) (eq_sym assoc) (n_wire l).

Lemma zx_associator_inv_compose : forall {n m o},
    zx_associator ⟷ zx_inv_associator ∝ n_wire (n + m + o).
Proof.
    intros.
    unfold zx_associator. unfold zx_inv_associator.
    rewrite cast_compose_r. 
    cleanup_zx. simpl_casts.
    reflexivity.
Qed.

Lemma zx_inv_associator_compose : forall {n m o},
    zx_inv_associator ⟷ zx_associator ∝ n_wire (n + (m + o)).
Proof.
    intros.
    unfold zx_associator. unfold zx_inv_associator.
    rewrite cast_compose_l.
    cleanup_zx. simpl_casts.
    reflexivity.
Qed.

Lemma zx_associator_cohere : forall {n m o p q r} 
    (zx0 : ZX n m) (zx1 : ZX o p) (zx2 : ZX q r),
    zx_associator ⟷ (zx0 ↕ (zx1 ↕ zx2)) 
    ∝ (zx0 ↕ zx1 ↕ zx2) ⟷ zx_associator.
Proof.
    intros. 
    unfold zx_associator.
    repeat rewrite cast_compose_r.
    simpl_casts. cleanup_zx.
    rewrite cast_compose_l.
    cleanup_zx. simpl_casts.
    rewrite stack_assoc.
    reflexivity.
Qed.