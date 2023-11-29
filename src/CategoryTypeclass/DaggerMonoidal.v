Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import Dagger.
Require Import Monoidal.

Local Open Scope Cat.

Class DaggerMonoidalCategory (C : Type) 
    `{DaggerCategory C} `{MonoidalCategory C} : Type := {

    (* dagger_compat {A B M N : C} {f : A ~> M} {g : B ~> N} :
        @adjoint C H H0 (@tensor C H1 H2 A B) (@tensor C H1 H2 M N) (@tensor_morph C H H2 A B M N f g) ≃ adjoint (f ⊗ g); *)
}.

Local Close Scope Cat.
