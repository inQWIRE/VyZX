Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import Monoidal.
Require Import BraidedMonoidal.

Local Open Scope Cat.

Class SymmetricMonoidalCategory (C : Type) `{BraidedMonoidalCategory C} : Type := {
    symmetry {A B : C} : (@braiding C H H0 H1 A B) ≃ inv_braiding;
}.

Lemma braiding_symmetry : forall n m, 
    @zx_braiding n m ∝ @zx_inv_braiding m n.
Proof. Admitted.

#[export] Instance ZXSymmetricMonoidalCategory : SymmetricMonoidalCategory nat := {
    symmetry := braiding_symmetry;
}.

Local Close Scope Cat.
