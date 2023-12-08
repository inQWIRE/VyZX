Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import Dagger.
Require Import Monoidal.
Require Import MonoidalRules.

Local Open Scope Cat.

Class DaggerMonoidalCategory (C : Type) 
    `{!Category C} `{!DaggerCategory C} `{!MonoidalCategory C} : Type := {
    dagger_compat {A B M N : C} {f : A ~> M} {g : B ~> N} :
        f † ⊗ g † ≃ (f ⊗ g) †;

    associator_unitary_r {A B M : C} : 
        associator ∘ associator † ≃ identity (A × B × M);
    associator_unitary_l {A B M : C} : 
        associator † ∘ associator ≃ identity (A × (B × M));
        (* left/right unitors are unitary *)
}.

Lemma zx_dagger_compat : forall {n n' m m'} 
    (zx0: ZX n m) (zx1 : ZX n' m'),
    zx0 †%ZX ↕ zx1 †%ZX ∝ (zx0 ↕ zx1) †%ZX.
Proof.
    intros.
    unfold ZXCore.adjoint.
    simpl.
    reflexivity.
Qed.

Lemma zx_associator_unitary_r : forall {n m o},
    zx_associator ⟷ zx_associator †%ZX ∝ n_wire (n + m + o).
Proof.
    intros. 
    unfold zx_associator.
    rewrite cast_adj. 
    rewrite nwire_adjoint.
    rewrite cast_compose_mid.
    simpl_casts.
    rewrite nwire_removal_r.
    reflexivity.
    Unshelve. all: lia.
Qed.

Lemma zx_associator_unitary_l : forall {n m o},
    zx_associator †%ZX ⟷ zx_associator ∝ n_wire (n + (m + o)).
Proof.
    intros.
    unfold zx_associator. 
    rewrite cast_adj.
    rewrite nwire_adjoint.
    rewrite cast_compose_mid.
    simpl_casts.
    rewrite nwire_removal_r.
    reflexivity.
    Unshelve. all: lia.
Qed.

#[export] Instance ZXDaggerMonoidalCategory : DaggerMonoidalCategory nat := {
    dagger_compat := @zx_dagger_compat;
    associator_unitary_l := @zx_associator_unitary_l;
    associator_unitary_r := @zx_associator_unitary_r;
}.

Local Close Scope Cat.
