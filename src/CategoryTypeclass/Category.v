Require Import CoreData.
Require Import CoreRules.

Declare Scope Cat_scope.
Delimit Scope Cat_scope with Cat.

Local Open Scope Cat.
(* 
    (f ⊗ g)%Cat
    (f ⊗ g)%ZX
 *)

Reserved Notation "A ~> B" (at level 50).
Reserved Notation "f ≃ g" (at level 60).
Reserved Notation "A ≅ B" (at level 60).

(* 
    Might use these to abstract out the equality relations.
        
    Definition relation (A : Type) := A -> A -> Prop.
    Definition reflexive {A : Type} (R : relation A) :=
        forall a : A, R a a.
    Definition transitive {A: Type} (R: relation A) :=
        forall a b c : A, (R a b) -> (R b c) -> (R a c).
    Definition symmetric {A: Type} (R: relation A) :=
        forall a b : A, (R a b) -> (R b a).
    Definition equivalence {A : Type} (R : relation A) := 
        (reflexive R) /\ (symmetric R) /\ (transitive R). 
*)

Class Category (C : Type) : Type := {
    morphism : C -> C -> Type
        where "A ~> B" := (morphism A B) : Cat_scope;

    equiv {A B : C} (f g : A ~> B) : Prop 
        where "f ≃ g" := (equiv f g) : Cat_scope;
    equiv_symm {A B : C} {f g : A ~> B} : 
        f ≃ g -> g ≃ f;
    equiv_trans {A B : C} {f g h : A ~> B} :
        f ≃ g -> g ≃ h -> f ≃ h;
    equiv_refl {A B : C} {f : A ~> B} :
        f ≃ f;

    obj_equiv (A B : C) : Prop 
        where "A ≅ B" := (obj_equiv A B) : Cat_scope;
    obj_equiv_symm {A B : C} : 
        A ≅ B -> B ≅ A;
    obj_equiv_trans {A B M : C} :
        A ≅ B -> B ≅ M -> A ≅ M;
    obj_equiv_refl {A : C} :
        A ≅ A;

    identity (A : C) : A ~> A;

    compose {A B M : C} : 
        (A ~> B) -> (B ~> M) -> (A ~> M) 
        where "f ∘ g" := (compose g f) : Cat_scope;

    left_id {A B : C} {f : A ~> B} : (identity B) ∘ f ≃ f;
    right_id {A B : C} {f : A ~> B} : f ∘ (identity A) ≃ f;
    assoc {A B M N : C}
        {f : A ~> B} {g : B ~> M} {h : M ~> N} : 
        h ∘ (g ∘ f) ≃ (h ∘ g) ∘ f;
}.

Notation "A ~> B" := (morphism A B) : Cat_scope.
Notation "f ≃ g" := (equiv f g) : Cat_scope. (* \simeq *)
Notation "A ≅ B" := (obj_equiv A B) : Cat_scope. (* \cong *)
Notation "f ∘ g" := (compose g f) : Cat_scope. (* \circ *)

#[export] Instance ZXCategory : Category nat := {
    morphism := ZX;

    equiv := @proportional;
    equiv_symm := @proportional_symm;
    equiv_trans := @proportional_trans;
    equiv_refl := @proportional_refl;

    obj_equiv := eq;
    obj_equiv_symm := @eq_sym nat;
    obj_equiv_trans := @eq_trans nat;
    obj_equiv_refl := @eq_refl nat;

    identity n := n_wire n;

    compose := @Compose;

    left_id _ _ := nwire_removal_r;
    right_id := @nwire_removal_l;
    assoc := @ComposeRules.compose_assoc;
}.

Local Close Scope Cat.