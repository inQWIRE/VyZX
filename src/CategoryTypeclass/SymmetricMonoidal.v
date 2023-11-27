Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import Monoidal.

Class SymmetricMonoidalCategory (C : Type) `{MonoidalCategory C} : Type := {
    braiding {A B : C} : A ⊠ B ~> B ⊠ A;
    inv_braiding {A B : C} : B ⊠ A ~> A ⊠ B;
    braiding_iso {A B : C} : A ⊠ B ≅ B ⊠ A;

    hexagon_1 {A B M : C} : 
        (identity B ◇ braiding) ∘ inv_associator ∘ (braiding ◇ identity M)
        ≃ inv_associator ∘ (@braiding A (B ⊠ M)) ∘ inv_associator;

    (* hexagon_2 {A B M : C} : (identity B ◇ inv_braiding) ∘ inv_associator ∘ (inv_braiding ◇ identity M)
        ≃ inv_associator ∘ (@inv_braiding (B ⊠ M) A) ∘ inv_associator; *)

    (* Braiding is symmetric *)
    (* symmetry {A B : C} : @braiding A B ≃ @inv_braiding B A; *)
}.


Definition zx_braiding {n m} :=
    let l := (n + m)%nat in
    let r := (m + n)%nat in
        cast l r (eq_refl l) (Nat.add_comm m n) (b_swap n m).

Definition zx_inv_braiding {n m} :=
    let l := (m + n)%nat in
    let r := (n + m)%nat in
        cast l r (eq_refl l) (Nat.add_comm n m) (b_swap m n).

Lemma b_swap_wires_r : forall {n m o},
    (b_swap n m) ↕ (n_wire o) ∝ b_swap (n + m) o.
Proof.
    intros.
    unfold b_swap.
    simpl.
    destruct n.
    - rewrite n_wire_stack.
      destruct m.
Admitted.

Compute (top_to_bottom_helper 3).

Lemma b_swap_wires_l : forall {n m o},
    (n_wire n) ↕ (b_swap m o) ∝ b_swap n (m + o).
Proof.
Admitted.

Lemma hexagon_lemma_1 : forall {n m o}, 
    (zx_braiding ↕ n_wire o) ⟷ (ZX_inv_associator ⟷ (n_wire m ↕ zx_braiding))
    ∝ ZX_inv_associator ⟷ ((@zx_braiding n (m + o)) ⟷ ZX_inv_associator).
Proof.
    unfold zx_braiding. unfold ZX_inv_associator. intros.
    simpl_casts.
    repeat rewrite <- ComposeRules.compose_assoc.
    rewrite b_swap_wires_l. rewrite b_swap_wires_r.
    repeat rewrite cast_compose_r.
    repeat rewrite nwire_removal_r.
    repeat rewrite cast_compose_l.
    rewrite nwire_removal_l.
    simpl_casts.

    (* rewrite <- cast_compose_partial_contract_r. *)
    (* rewrite cast_compose_r. *)
    repeat rewrite cast_compose_distribute.
    simpl_casts.
Admitted.

#[export] Instance ZXSymmetricMonoidalCategory : SymmetricMonoidalCategory nat := {
    braiding := @zx_braiding;
    inv_braiding := @zx_inv_braiding;
    braiding_iso := Nat.add_comm;

    hexagon_1 := @hexagon_lemma_1;
}.