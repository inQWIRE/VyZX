Require Import Category.
Require Import Monoidal.

Lemma compose_simplify_general : forall {C : Type} (Cat : Category C) 
    {n m o : C} (m1 m3 : morphism n m) (m2 m4 : morphism m o),
    equiv m1 m3 -> equiv m2 m4 -> equiv (compose m1 m2) (compose m3 m4).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma stack_simplify_general : forall {C : Type} 
  {Cat : Category C} (MonCat : MonoidalCategory C) 
  {n1 o1 n2 o2 : C} (m1 m3 : morphism n1 o1) (m2 m4 : morphism n2 o2),
  equiv m1 m3 -> equiv m2 m4 -> equiv (tensor_morph m1 m2) (tensor_morph m3 m4).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.