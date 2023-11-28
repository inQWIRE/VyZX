Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import Dagger.
Require Import Monoidal.

Local Open Scope Cat.

Class DaggerMonoidalCategory (C : Type) 
    `{DaggerCategory C} `{MonoidalCategory C} : Type := {

    (* dagger_compat {A B N M : C} {f : A ~> M} {g : B ~> N} :
        (f ⊗ g) † ≃ f † ⊗ g †; *)
}.

Local Close Scope Cat.
