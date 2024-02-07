Require Import Category.
Require Import Monoidal.

Local Open Scope Cat.

Lemma compose_simplify_general : forall {C : Type} {Cat : Category C}
    {A B M : C} (f1 f3 : A ~> B) (f2 f4 : B ~> M),
    f1 ≃ f3 -> f2 ≃ f4 -> (f1 ∘ f2) ≃ (f3 ∘ f4).
Proof.
    intros.
    rewrite H, H0.
    reflexivity.
Qed.

Lemma stack_simplify_general : forall {C : Type} 
    {Cat : Category C} {MonCat : MonoidalCategory C}
    {A B M N : C} (f1 f3 : A ~> B) (f2 f4 : M ~> N),
    f1 ≃ f3 -> f2 ≃ f4 -> (f1 ⊗ f2) ≃ (f3 ⊗ f4).
Proof.
    intros.
    rewrite H, H0.
    reflexivity.
Qed.

Lemma nwire_stack_compose_topleft_general : forall {C : Type}
    {Cat : Category C} {MonCat : MonoidalCategory C}
    {topIn botIn topOut botOut : C} 
    (f0 : botIn ~> botOut) (f1 : topIn ~> topOut),
    ((c_identity topIn) ⊗ f0) ∘ (f1 ⊗ (c_identity botOut)) ≃ (f1 ⊗ f0).
Proof.
    intros.
    rewrite <- bifunctor_comp.
    rewrite left_unit; rewrite right_unit.
    easy.
Qed.

Local Close Scope Cat.
