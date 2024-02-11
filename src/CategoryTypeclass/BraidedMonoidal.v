Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import Monoidal.
Require Import MonoidalRules.
Require Import Permutation.
Require Import PermutationRules.

Local Open Scope Cat.

Class BraidedMonoidalCategory (C : Type) `{MonoidalCategory C} : Type := {
    braiding {A B : C} : A × B ~> B × A;
    inv_braiding {A B : C} : B × A ~> A × B;
    braiding_inv_compose {A B : C} : braiding ∘ inv_braiding ≃ identity (A × B);
    inv_braiding_compose {A B : C} : inv_braiding ∘ braiding ≃ identity (B × A);

    hexagon_1 {A B M : C} : 
        (braiding ⊗ identity M) ∘ associator ∘ (identity B ⊗ braiding)
        ≃ associator ∘ (@braiding A (B × M)) ∘ associator;

    hexagon_2 {A B M : C} : (inv_braiding ⊗ identity M) ∘ associator ∘ (identity B ⊗ inv_braiding)
        ≃ associator ∘ (@inv_braiding (B × M) A) ∘ associator;
}.

Definition zx_braiding {n m} :=
    let l := (n + m)%nat in
    let r := (m + n)%nat in
        cast l r (eq_refl l) (Nat.add_comm m n) (n_top_to_bottom n m).

Definition zx_inv_braiding {n m} :=
    let l := (m + n)%nat in
    let r := (n + m)%nat in
        cast l r (eq_refl l) (Nat.add_comm n m) (n_bottom_to_top n m).

Definition n_compose_bot n m := n_compose n (bottom_to_top m).
Definition n_compose_top n m := n_compose n (top_to_bottom m).

Lemma n_top_to_bottom_zxperm : forall {n m}, 
    ZXperm (n + m) (n_top_to_bottom n m).
Proof.
    unfold n_top_to_bottom.
    auto with zxperm_db.
Qed.

Lemma n_bottom_to_top_zxperm : forall {n m}, 
    ZXperm (n + m) (n_bottom_to_top m n).
Proof.
    unfold n_bottom_to_top.
    auto with zxperm_db.
Qed.

#[export] Hint Resolve n_top_to_bottom_zxperm n_bottom_to_top_zxperm : zxperm_db.

Lemma perm_of_n_top_to_bottom : forall n m,
    perm_of_zx (n_top_to_bottom n m) = rotr (n + m) n.
Proof.
    intros.
    unfold n_top_to_bottom.
    cleanup_perm_of_zx.
    reflexivity.
Qed.

Lemma perm_of_n_bottom_to_top : forall n m,
    perm_of_zx (n_bottom_to_top n m) = rotl (n + m) n.
Proof.
    intros.
    unfold n_bottom_to_top.
    cleanup_perm_of_zx.
    rewrite Nat.add_comm.
    reflexivity.
Qed.

#[export] Hint Rewrite perm_of_n_top_to_bottom perm_of_n_bottom_to_top : perm_of_zx_cleanup_db.


Lemma zx_braiding_inv_compose : forall {n m},
    zx_braiding ⟷ zx_inv_braiding ∝ n_wire (n + m).
Proof.
    intros.
    unfold zx_braiding, zx_inv_braiding.
    prop_perm_eq.
Qed.

Lemma zx_inv_braiding_compose : forall {n m},
    zx_inv_braiding ⟷ zx_braiding ∝ n_wire (m + n).
Proof.
    intros.
    unfold zx_braiding, zx_inv_braiding.
    prop_perm_eq.
    (* intros. 
    unfold zx_inv_braiding, zx_braiding.
    rewrite cast_compose_mid, 2!cast_cast_eq, cast_id_eq.
    prop_perm_eq.
    constructor; auto with zxperm_db.
    unfold zx_braiding. unfold zx_inv_braiding.
    unfold n_top_to_bottom. 
    unfold n_bottom_to_top.
    rewrite cast_compose_mid.
    simpl_casts.
    fold (n_compose_top n (n + m)).
    rewrite cast_fn_eq_dim.
    rewrite n_compose_bottom_compose_top.
    reflexivity.
    Unshelve. 
    all: rewrite (Nat.add_comm n m); easy. *)
Qed.

Lemma S_lemma : forall {n m},
    (S n + m)%nat = (n + S m)%nat.
Proof. lia. Qed.




Lemma hexagon_lemma_1_helper : forall {n m o o'} prf1 prf2 prf3 prf4,
    n_top_to_bottom n m ↕ n_wire o
    ⟷ cast (n + m + o) o' prf1 prf2 (n_wire m ↕ n_top_to_bottom n o)
    ∝ cast (n + m + o) o' prf3 prf4 (n_top_to_bottom n (m + o)).
Proof.
    intros. (* unfold n_top_to_bottom.  *)
    prop_perm_eq.
    unfold n_top_to_bottom.
    solve_modular_permutation_equalities.
Qed.

Lemma hexagon_lemma_1 : forall {n m o}, 
    (zx_braiding ↕ n_wire o) ⟷ zx_associator ⟷ (n_wire m ↕ zx_braiding)
    ∝ zx_associator ⟷ (@zx_braiding n (m + o)) ⟷ zx_associator.
Proof.
    intros.
    unfold zx_braiding. unfold zx_associator.
    simpl_casts.
    prop_perm_eq.
    solve_modular_permutation_equalities.
Qed.

Lemma hexagon_lemma_2_helper : forall {n m o o'} prf1 prf2 prf3 prf4,
    n_bottom_to_top m n ↕ n_wire o
    ⟷ cast (n + m + o) o' prf1 prf2 (n_wire m ↕ n_bottom_to_top o n)
    ∝ cast (n + m + o) o' prf3 prf4 (n_bottom_to_top (m + o) n).
Proof.
    intros.
    prop_perm_eq.
    solve_modular_permutation_equalities.
Qed.

Lemma hexagon_lemma_2 : forall {n m o},
    (zx_inv_braiding ↕ n_wire o) ⟷ zx_associator ⟷ (n_wire m ↕ zx_inv_braiding)
    ∝ zx_associator ⟷ (@zx_inv_braiding (m + o) n) ⟷ zx_associator.
Proof.
    intros.
    unfold zx_inv_braiding. unfold zx_associator.
    simpl_casts.
    prop_perm_eq.
    solve_modular_permutation_equalities.
Qed.

#[export] Instance ZXBraidedMonoidalCategory : BraidedMonoidalCategory nat := {
    braiding := @zx_braiding;
    inv_braiding := @zx_inv_braiding;
    braiding_inv_compose := @zx_braiding_inv_compose;
    inv_braiding_compose := @zx_inv_braiding_compose;

    hexagon_1 := @hexagon_lemma_1;
    hexagon_2 := @hexagon_lemma_2;
}.

Local Close Scope Cat.