Require Import Category.
Require Import Dagger.
Require Import Monoidal.
Require Import BraidedMonoidal.
Require Import DaggerMonoidal.
Require Import SymmetricMonoidal.

Local Open Scope Cat.

Class DaggerSymmetricMonoidalCategory (C : Type) 
    `{!Category C} `{!DaggerCategory C} `{!MonoidalCategory C} 
    `{!DaggerMonoidalCategory C} `{!BraidedMonoidalCategory C} 
    `{!SymmetricMonoidalCategory C}: Type := {}.

#[export] Instance ZXDaggerSymmetricMonoidalCategory : DaggerSymmetricMonoidalCategory nat := {}.

Local Close Scope Cat.