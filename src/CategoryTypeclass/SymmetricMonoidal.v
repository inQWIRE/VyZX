Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import Monoidal.
Require Import BraidedMonoidal.

Local Open Scope Cat.

Class SymmetricMonoidalCategory (C : Type) `{BraidedMonoidalCategory C} : Type := {
    symmetry {A B : C} : (@braiding C H H0 H1 A B) ≃ inv_braiding;
}.

Lemma compose_braiding : forall {n m},
    zx_braiding ⟷ zx_braiding ∝ zx_inv_braiding ⟷ @zx_braiding m n 
    -> @zx_braiding n m ∝ zx_inv_braiding.
Proof.
Admitted.

Lemma braiding_symmetry : forall n m, 
    @zx_braiding n m ∝ @zx_inv_braiding m n.
Proof.
    intros.
    apply compose_braiding.
    rewrite zx_inv_braiding_compose.
    unfold zx_braiding.
    rewrite cast_compose_l.
    simpl_casts.
    unfold n_top_to_bottom.
    fold (n_compose_top m (m + n)).
    rewrite cast_fn_eq_dim.
    unfold n_compose_top.
    rewrite n_compose_m_compose.
    rewrite n_compose_n_top_to_bottom.
    reflexivity.
Qed.

#[export] Instance ZXSymmetricMonoidalCategory : SymmetricMonoidalCategory nat := {
    symmetry := braiding_symmetry;
}.

Local Close Scope Cat.
