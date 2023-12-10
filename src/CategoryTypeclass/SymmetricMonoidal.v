Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import Monoidal.
Require Import BraidedMonoidal.

Local Open Scope Cat.

Class SymmetricMonoidalCategory (C : Type) `{BraidedMonoidalCategory C} : Type := {
    symmetry {A B : C} : (@braiding C H H0 H1 A B) ≃ inv_braiding;
}.

Lemma n_top_to_bottom_is_bottom_to_top : forall {n m},
    n_top_to_bottom n m ∝ n_bottom_to_top m n.
Proof.
    unfold n_bottom_to_top. 
    unfold bottom_to_top.
    unfold n_top_to_bottom.
    induction n.
    - intros.
      rewrite n_compose_0.
      simpl.
      rewrite <- n_compose_transpose.
      rewrite n_compose_n_top_to_bottom.
      rewrite n_wire_transpose.
      reflexivity.
    - intros.
      rewrite n_compose_grow_l.
      assert ((S n + m)%nat = (n + S m)%nat) by lia.
      assert (top_to_bottom (S n + m) 
        ∝ cast (S n + m) (S n + m) H H (top_to_bottom (n + S m))) 
        by (rewrite cast_fn_eq_dim; reflexivity).
      rewrite H0.
      rewrite cast_n_compose.
      rewrite IHn.
      rewrite <- cast_n_compose.
      rewrite <- H0.
      rewrite n_compose_grow_l.
      rewrite <- cast_transpose.
      rewrite <- H0.
      fold (bottom_to_top (S n + m)).
      rewrite <- compose_assoc.
      rewrite top_to_bottom_to_top. cleanup_zx.
      reflexivity.
Qed.

Lemma braiding_symmetry : forall n m, 
    @zx_braiding n m ∝ @zx_inv_braiding m n.
Proof.
    intros.
    unfold zx_braiding. unfold zx_inv_braiding.
    apply cast_compat.
    rewrite n_top_to_bottom_is_bottom_to_top.
    reflexivity.
Qed.

#[export] Instance ZXSymmetricMonoidalCategory : SymmetricMonoidalCategory nat := {
    symmetry := braiding_symmetry;
}.

Local Close Scope Cat.
