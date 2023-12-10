Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import Monoidal.
Require Import MonoidalRules.
Require Import BraidedMonoidal.
Require Import SymmetricMonoidal.

Local Open Scope Cat.

Reserved Notation "A ★" (at level 0).

(* A compact closed category is a right autonomous symmetric monoidal category *)
Class CompactClosedCategory (C : Type) `{SymmetricMonoidalCategory C} : Type := {
    dual (A : C) : C
        where "A ★" := (dual A);
    unit {A : C} : I ~> A ★ × A;
    counit {A : C} : A × A ★ ~> I;

    (* triangle_1 {A : C} : 
        inv_right_unitor ∘ (identity A ⊗ unit) ∘ inv_associator 
        ∘ (counit ⊗ identity A) ∘ left_unitor ≃ identity A; *)

    (* triangle_2 {A : C} : 
        inv_left_unitor ∘ (unit ⊗ identity A ★) ∘ associator 
        ∘ (identity A ★ ⊗ counit) ∘ right_unitor ≃ identity A ★; *)
}.

Notation "A ★" := (dual A) : Cat_scope.

Lemma zx_triangle_1 : forall n,
    zx_inv_right_unitor ⟷ (n_wire n ↕ n_cap n) ⟷ zx_inv_associator
    ⟷ (n_cup n ↕ n_wire n) ⟷ zx_left_unitor ∝ n_wire n.
Proof.
    intros.
    unfold zx_inv_right_unitor.
    unfold zx_inv_associator.
    unfold zx_left_unitor.
    simpl_casts. cleanup_zx.
    rewrite cast_compose_l. 
    simpl_casts. cleanup_zx.
    rewrite cast_compose_r.
    cleanup_zx. simpl_casts.
    unfold n_cap. unfold n_cup.
    destruct n.
    - simpl. cleanup_zx. simpl_casts.
      cleanup_zx. easy.
    - rewrite n_swap_grow_l.
      simpl. 
Admitted.

#[export] Instance ZXCompactClosedCategory : CompactClosedCategory nat := {
    dual n := n;
    unit n := n_cap n;
    counit n := n_cup n;
}.

Local Close Scope Cat.
