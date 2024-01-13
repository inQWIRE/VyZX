Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import MonoidalRules.
Require Import Setoid.

Local Open Scope Cat.

Class MonoidalCategory (C : Type) `{Category C} : Type := {
    tensor : C -> C -> C
        where "A × B" := (tensor A B);
    I : C;

    tensor_morph {A B M N : C} : 
        (A ~> M) -> (B ~> N) -> (A × B) ~> (M × N)
        where "f ⊗ g" := (tensor_morph f g);
    tensor_morph_compat {A B M N : C} : 
        forall (f g : A ~> B), f ≃ g ->
        forall (h j : M ~> N), h ≃ j ->
        f ⊗ h ≃ g ⊗ j;
    
    (* These are all isomorphisms *)
    associator {A B M : C} : (A × B) × M ~> A × (B × M);
    inv_associator {A B M : C} : A × (B × M) ~> (A × B) × M;
    associator_inv_compose {A B M : C} : associator ∘ inv_associator
        ≃ identity ((A × B) × M);
    inv_associator_compose {A B M : C} : inv_associator ∘ associator 
        ≃ identity (A × (B × M));

    left_unitor {A : C} : I × A ~> A;
    inv_left_unitor {A : C} : A ~> I × A;
    left_inv_compose {A : C} : 
        left_unitor ∘ inv_left_unitor ≃ identity (I × A);
    inv_left_compose {A : C} : 
        inv_left_unitor ∘ left_unitor ≃ identity A;

    right_unitor {A : C} : A × I ~> A;
    inv_right_unitor {A : C} : A ~> A × I;
    right_inv_compose {A : C} : 
        right_unitor ∘ inv_right_unitor ≃ identity (A × I);
    inv_right_compose {A : C} : 
        inv_right_unitor ∘ right_unitor ≃ identity A;

    bifunctor_id {A B : C} : 
        identity A ⊗ identity B ≃ identity (A × B);
    bifunctor_comp {A B M N P Q : C} 
        {f : A ~> B} {g : B ~> M}
        {h : N ~> P} {k : P ~> Q} : 
        (f ∘ g) ⊗ (h ∘ k) ≃ (f ⊗ h) ∘ (g ⊗ k);

    (* Coherence conditions for α, λ, ρ *)
    associator_cohere {A B M N P Q : C} 
        {f : A ~> B} {g : M ~> N} {h : P ~> Q} : 
        associator ∘ (f ⊗ (g ⊗ h)) ≃ ((f ⊗ g) ⊗ h) ∘ associator;
    left_unitor_cohere {A B : C} {f : A ~> B} : 
        left_unitor ∘ f ≃ (identity I ⊗ f) ∘ left_unitor;
    right_unitor_cohere {A B : C} {f : A ~> B} : 
        right_unitor ∘ f ≃ (f ⊗ identity I) ∘ right_unitor;

    (* Commutative diagrams *)
    triangle {A B : C} : 
        associator ∘ (identity A ⊗ left_unitor)
        ≃ right_unitor ⊗ identity B;
    pentagon {A B M N : C} : 
        (associator ⊗ identity N) ∘ associator ∘ (identity A ⊗ associator)
        ≃ @associator (A × B) M N ∘ associator;
}.

Notation "A × B" := (tensor A B) : Cat_scope. (* \times *)
Notation "f ⊗ g" := (tensor_morph f g) : Cat_scope. (* \otimes *) 

Lemma triangle_lemma : forall {n m}, 
    zx_associator ⟷ (n_wire n ↕ zx_left_unitor) ∝ 
    zx_right_unitor ↕ n_wire m.
Proof.
    intros.
    unfold zx_associator.
    unfold zx_right_unitor.
    unfold zx_left_unitor.
    simpl_casts.
    repeat rewrite n_wire_stack.
    cleanup_zx.
    simpl_casts.
    reflexivity.
Qed.

Lemma pentagon_lemma : forall {n m o p}, 
    (zx_associator ↕ n_wire p) ⟷ zx_associator ⟷ (n_wire n ↕ zx_associator)
    ∝ (@zx_associator (n + m) o p) ⟷ zx_associator.
Proof.
    intros.
    unfold zx_associator.
    simpl_casts.
    repeat rewrite n_wire_stack.
    repeat rewrite cast_compose_l.
    repeat rewrite cast_compose_r.
    cleanup_zx; simpl_casts; reflexivity.
Qed.

Add Parametric Morphism {C : Type} 
  {Cat : Category C} (MonCat : MonoidalCategory C)
  (n0 m0 n1 m1 : C) : tensor_morph
  with signature 
    (@Category.equiv C Cat n0 m0) ==> 
    (@Category.equiv C Cat n1 m1) ==> 
    Category.equiv as stack_mor.
Proof. apply tensor_morph_compat; assumption. Qed.

#[export] Instance ZXMonoidalCategory : MonoidalCategory nat := {
    tensor := Nat.add;
    I := 0;

    tensor_morph _ _ _ _ := Stack;
    tensor_morph_compat := stack_compat;

    associator := @zx_associator;
    inv_associator := @zx_inv_associator;
    associator_inv_compose := @zx_associator_inv_compose;
    inv_associator_compose := @zx_inv_associator_compose;

    left_unitor := @zx_left_unitor;
    inv_left_unitor := @zx_inv_left_unitor;
    left_inv_compose := @zx_left_inv_compose;
    inv_left_compose := @zx_inv_left_compose;

    right_unitor := @zx_right_unitor;
    inv_right_unitor := @zx_inv_right_unitor;
    right_inv_compose := @zx_right_inv_compose;
    inv_right_compose := @zx_inv_right_compose;

    bifunctor_id := n_wire_stack;
    bifunctor_comp := @stack_compose_distr;

    associator_cohere := @zx_associator_cohere;
    left_unitor_cohere := @zx_left_unitor_cohere;
    right_unitor_cohere := @zx_right_unitor_cohere;

    triangle := @triangle_lemma;
    pentagon := @pentagon_lemma;
}.

Local Close Scope Cat.
