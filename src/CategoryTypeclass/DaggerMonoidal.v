Require Import CoreData.
Require Import CoreRules.
Require Import Permutation.
Require Import PermutationRules.
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

    left_unitor_unitary_r {A : C} : 
        left_unitor ∘ left_unitor † ≃ identity (I × A);
    left_unitor_unitary_l {A : C} : 
        left_unitor † ∘ left_unitor ≃ identity A;

    right_unitor_unitary_r {A : C} : 
        right_unitor ∘ right_unitor † ≃ identity (A × I);
    right_unitor_unitary_l {A : C} :
        right_unitor † ∘ right_unitor ≃ identity A;
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

Lemma zx_left_unitor_unitary_r : forall {n},
    zx_left_unitor ⟷ zx_left_unitor †%ZX ∝ n_wire (0 + n).
Proof.
    intros. unfold zx_left_unitor.
    simpl_casts. cleanup_zx.
    rewrite nwire_adjoint.
    reflexivity.
Qed.

Lemma zx_left_unitor_unitary_l : forall {n},
    zx_left_unitor †%ZX ⟷ zx_left_unitor ∝ n_wire n.
Proof.
    intros. unfold zx_left_unitor.
    simpl_casts. cleanup_zx.
    rewrite nwire_adjoint.
    reflexivity.
Qed.

Lemma zx_right_unitor_unitary_r : forall {n},
    zx_right_unitor ⟷ zx_right_unitor †%ZX ∝ n_wire (n + 0).
Proof.
    intros. unfold zx_right_unitor.
    rewrite cast_compose_mid. simpl_casts.
    rewrite nwire_adjoint.
    cleanup_zx. 
    rewrite cast_n_wire.
    reflexivity.
    Unshelve. all: lia.
Qed.

Lemma zx_right_unitor_unitary_l : forall {n},
    zx_right_unitor †%ZX ⟷ zx_right_unitor ∝ n_wire n.
Proof.
    intros. unfold zx_right_unitor.
    rewrite cast_compose_mid. simpl_casts.
    rewrite nwire_adjoint.
    cleanup_zx. 
    reflexivity.
    Unshelve. all: lia.
Qed.

#[export] Instance ZXDaggerMonoidalCategory : DaggerMonoidalCategory nat := {
    dagger_compat := @zx_dagger_compat;

    associator_unitary_r := @zx_associator_unitary_r;
    associator_unitary_l := @zx_associator_unitary_l;
    left_unitor_unitary_r := @zx_left_unitor_unitary_r;
    left_unitor_unitary_l := @zx_left_unitor_unitary_l;
    right_unitor_unitary_r := @zx_right_unitor_unitary_r;
    right_unitor_unitary_l := @zx_right_unitor_unitary_l;
}.

Local Close Scope Cat.
