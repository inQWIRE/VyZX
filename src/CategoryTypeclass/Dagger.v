Require Import CoreData.
Require Import CoreRules.
Require Import Category.

Reserved Notation "f ‡" (at level 30).

Class DaggerCategory (C : Type) `{Category C} : Type := {
    adjoint {A B : C} (f : A ~> B) : B ~> A
        where "f ‡" := (adjoint f);

    involutive {A B : C} {f : A ~> B} : f ‡ ‡ ≃ f;

    preserves_id {A : C} : (identity A) ‡ ≃ identity A;

    (* contravariant {A B M : C} {f : A ~> B} {g : B ~> M} :
        (g ∘ f) ‡ ≃ f ‡ ∘ g ‡; *)
}.

Notation "f ‡" := (adjoint f). (* \ddag *)

Lemma nwire_adjoint : forall n, (n_wire n) † ∝ n_wire n.
Proof.
    intros.
    unfold ZXCore.adjoint.
    unfold ZXCore.transpose.
    unfold ZXCore.conjugate.
    destruct n.
Admitted.

#[export] Instance ZXDaggerCategory : DaggerCategory nat := {
    adjoint := @ZXCore.adjoint;
    involutive := @Proportional.adjoint_involutive;
    preserves_id := @nwire_adjoint;
}.

Search ((n_wire _) ⊼).
Search (n_wire 0).
Search (ZXCore.conjugate).