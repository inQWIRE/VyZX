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

    triangle_1 {A : C} : 
        inv_right_unitor ∘ (identity A ⊗ unit) ∘ inv_associator 
        ∘ (counit ⊗ identity A) ∘ left_unitor ≃ identity A;

    triangle_2 {A : C} : 
        inv_left_unitor ∘ (unit ⊗ identity A ★) ∘ associator 
        ∘ (identity A ★ ⊗ counit) ∘ right_unitor ≃ identity A ★;
}.

Notation "A ★" := (dual A) : Cat_scope.

Lemma n_yank_l : forall n {prf1 prf2},
    cast n (n + n + n) prf1 prf2 (n_wire n ↕ n_cap n) 
    ⟷ (n_cup n ↕ n_wire n) ∝ n_wire n.
Proof.
    induction n.
    - intros.
      rewrite n_cap_0_empty.
      rewrite n_cup_0_empty.
      simpl_casts.
      cleanup_zx. simpl.
      simpl_casts. cleanup_zx.
      easy.
    - intros.
Admitted.

Lemma n_yank_r : forall n {prf1 prf2 prf3 prf4},
    cast n n prf3 prf4 (cast n (n + (n + n)) prf1 prf2 (n_cap n ↕ n_wire n)
    ⟷ (n_wire n ↕ n_cup n)) ∝ n_wire n.
Proof.
    induction n.
    - intros.
      rewrite n_cap_0_empty.
      rewrite n_cup_0_empty.
      simpl_casts.
      cleanup_zx. simpl.
      simpl_casts. cleanup_zx.
      easy.
    - intros.
Admitted.

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
    rewrite n_yank_l.
    reflexivity.
Qed.

Lemma zx_triangle_2 : forall n,
    zx_inv_left_unitor ⟷ (n_cap n ↕ n_wire n) ⟷ zx_associator
    ⟷ (n_wire n ↕ n_cup n) ⟷ zx_right_unitor ∝ n_wire n.
Proof.
    intros.
    unfold zx_inv_left_unitor.
    unfold zx_associator.
    unfold zx_right_unitor.
    simpl_casts. cleanup_zx.
    rewrite cast_compose_r.
    simpl_casts. cleanup_zx.
    rewrite cast_compose_r.
    simpl_casts. cleanup_zx.
    rewrite n_yank_r.
    reflexivity.
Qed.

#[export] Instance ZXCompactClosedCategory : CompactClosedCategory nat := {
    dual n := n;
    unit n := n_cap n;
    counit n := n_cup n;
    triangle_1 := zx_triangle_1;
    triangle_2 := zx_triangle_2;
}.

Local Close Scope Cat.
