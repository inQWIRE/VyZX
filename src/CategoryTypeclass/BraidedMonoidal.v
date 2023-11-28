Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import Monoidal.
Require Import MonoidalRules.

Local Open Scope Cat.

Class BraidedMonoidalCategory (C : Type) `{MonoidalCategory C} : Type := {
    braiding {A B : C} : A × B ~> B × A;
    inv_braiding {A B : C} : B × A ~> A × B;
    braiding_inv_compose {A B : C} : braiding ∘ inv_braiding ≃ identity (A × B);
    inv_braiding_compose {A B : C} : inv_braiding ∘ braiding ≃ identity (B × A);

    hexagon_1 {A B M : C} : 
        (braiding ⊗ identity M) ∘ associator ∘ (identity B ⊗ braiding)
        ≃ associator ∘ (@braiding A (B × M)) ∘ associator;

    hexagon_2 {A B M : C} : (inv_braiding ⊗ identity M) ∘ associator ∘ (identity B ⊗ inv_braiding)
        ≃ associator ∘ (@inv_braiding (B × M) A) ∘ associator;
}.

Definition zx_braiding {n m} :=
    let l := (n + m)%nat in
    let r := (m + n)%nat in
        cast l r (eq_refl l) (Nat.add_comm m n) (n_top_to_bottom n m).

Definition zx_inv_braiding {n m} :=
    let l := (m + n)%nat in
    let r := (n + m)%nat in
        cast l r (eq_refl l) (Nat.add_comm n m) (n_top_to_bottom m n).

Lemma n_wire_2 : — ↕ — ∝ n_wire 2.
Proof.
    simpl. cleanup_zx.
    simpl_casts. reflexivity.
Qed.

Lemma zx_braiding_inv_compose : forall {n m},
    zx_braiding ⟷ zx_inv_braiding ∝ n_wire (n + m).
Proof.
    unfold zx_braiding. unfold zx_inv_braiding.
    unfold n_top_to_bottom. 
    induction n.
    - induction m.
      + simpl_casts. unfold n_box. 
        cleanup_zx. simpl. reflexivity.
      + rewrite cast_compose_l.
        simpl_casts. cleanup_zx.
        unfold n_top_to_bottom_helper.
Admitted.

Lemma zx_inv_braiding_compose : forall {n m},
    zx_inv_braiding ⟷ zx_braiding ∝ n_wire (m + n).
Proof.
Admitted.

Lemma hexagon_lemma_1 : forall {n m o}, 
    (zx_braiding ↕ n_wire o) ⟷ zx_associator ⟷ (n_wire m ↕ zx_braiding)
    ∝ zx_associator ⟷ (@zx_braiding n (m + o)) ⟷ zx_associator.
Proof.
    intros.
    unfold zx_braiding. unfold zx_associator.
    simpl_casts.
    repeat rewrite cast_compose_l.
    repeat rewrite cast_compose_r.
    simpl_casts.
Admitted.

Lemma hexagon_lemma_2 : forall {n m o},
    (zx_inv_braiding ↕ n_wire o) ⟷ zx_associator ⟷ (n_wire m ↕ zx_inv_braiding)
    ∝ zx_associator ⟷ (@zx_inv_braiding (m + o) n) ⟷ zx_associator.
Proof.
Admitted.

#[export] Instance ZXBraidedMonoidalCategory : BraidedMonoidalCategory nat := {
    braiding := @zx_braiding;
    inv_braiding := @zx_inv_braiding;
    braiding_inv_compose := @zx_braiding_inv_compose;
    inv_braiding_compose := @zx_inv_braiding_compose;

    hexagon_1 := @hexagon_lemma_1;
    hexagon_2 := @hexagon_lemma_2;
}.

Local Close Scope Cat.