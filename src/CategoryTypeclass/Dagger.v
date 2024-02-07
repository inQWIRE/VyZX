Require Import CoreData.
Require Import CoreRules.
Require Import Category.

Local Open Scope Cat.

Reserved Notation "f †" (at level 0).

Class DaggerCategory (C : Type) `{Category C} : Type := {
    adjoint {A B : C} (f : A ~> B) : B ~> A
        where "f †" := (adjoint f);

    involutive {A B : C} {f : A ~> B} : f † † ≃ f;

    preserves_id {A : C} : (c_identity A) † ≃ c_identity A;

    contravariant {A B M : C} {f : A ~> B} {g : B ~> M} :
        (f ∘ g) † ≃ g † ∘ f †;
}.

Notation "f †" := (adjoint f) : Cat_scope. (* \dag *)

Lemma nwire_adjoint : forall n, (n_wire n) †%ZX ∝ n_wire n.
Proof.
    intros.
    induction n; try easy.
    - intros.
      unfold ZXCore.adjoint.
      simpl.
      unfold ZXCore.adjoint in IHn.
      rewrite IHn.
      reflexivity.
Qed.

Lemma compose_adjoint : forall {n m o}
    (zx0 : ZX n m) (zx1 : ZX m o), 
    (zx0 ⟷ zx1) †%ZX ∝ zx1 †%ZX ⟷ zx0 †%ZX.
Proof.
    intros; easy.
Qed.

#[export] Instance ZXDaggerCategory : DaggerCategory nat := {
    adjoint := @ZXCore.adjoint;
    involutive := @Proportional.adjoint_involutive;
    preserves_id := nwire_adjoint;
    contravariant := @compose_adjoint;
}.

Local Close Scope Cat.
