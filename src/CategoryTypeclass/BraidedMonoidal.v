Require Import CoreData.
Require Import CoreRules.
Require Import Category.
Require Import Monoidal.
Require Import MonoidalRules.

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

Lemma zx_braiding_inv_compose : forall {n m},
    zx_braiding ⟷ zx_inv_braiding ∝ n_wire (n + m).
Proof.
    intros.
    unfold zx_braiding. unfold zx_inv_braiding.
    unfold n_top_to_bottom. 
    unfold n_bottom_to_top.
    rewrite cast_compose_mid.
    simpl_casts.
    fold (n_compose_bot n (m + n)).
    rewrite cast_fn_eq_dim.
    rewrite n_compose_top_compose_bottom.
    reflexivity.
    Unshelve. 
    all: rewrite (Nat.add_comm n m); easy.
Qed.

Lemma zx_inv_braiding_compose : forall {n m},
    zx_inv_braiding ⟷ zx_braiding ∝ n_wire (m + n).
Proof.
    intros. 
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
    all: rewrite (Nat.add_comm n m); easy.
Qed.

Lemma S_lemma : forall {n m},
    (S n + m)%nat = (n + S m)%nat.
Proof. lia. Qed.

Lemma hexagon_lemma_1_helper : forall {n m o o'} prf1 prf2 prf3 prf4,
    n_top_to_bottom n m ↕ n_wire o
    ⟷ cast (n + m + o) o' prf1 prf2 (n_wire m ↕ n_top_to_bottom n o)
    ∝ cast (n + m + o) o' prf3 prf4 (n_top_to_bottom n (m + o)).
Proof.
    unfold n_top_to_bottom.
    induction n.
    - intros.
      rewrite 3 n_compose_0.
      rewrite 2 n_wire_stack.
      cleanup_zx.
      assert (n_wire (m + (0 + o)) ∝ n_wire (0 + (m + o))) by easy.
      rewrite H. simpl_casts. reflexivity.
    - intros.
      rewrite 1 n_compose_grow_l.
      assert (top_to_bottom (S n + m) 
        ∝ cast (S n + m) (S n + m) S_lemma S_lemma (top_to_bottom (n + S m))) 
        by (rewrite cast_fn_eq_dim; reflexivity).
      rewrite H.
      rewrite cast_n_compose.
      rewrite <- cast_compose_mid_contract. simpl_casts.

      rewrite 1 n_compose_grow_r.
      rewrite stack_nwire_distribute_l.
      assert (top_to_bottom (S n + o) 
        ∝ cast (S n + o) (S n + o) S_lemma S_lemma (top_to_bottom (n + S o)))
        by (rewrite cast_fn_eq_dim; reflexivity).
      rewrite H0.
      rewrite cast_n_compose.
      rewrite cast_compose_mid_contract. simpl_casts.
      rewrite <- compose_assoc.
      rewrite cast_compose_l. simpl_casts.
      rewrite cast_compose_l. simpl_casts.
      rewrite stack_nwire_distribute_r.
      rewrite (compose_assoc (top_to_bottom (n + S m) ↕ n_wire o)).
Admitted.

Lemma hexagon_lemma_1 : forall {n m o}, 
    (zx_braiding ↕ n_wire o) ⟷ zx_associator ⟷ (n_wire m ↕ zx_braiding)
    ∝ zx_associator ⟷ (@zx_braiding n (m + o)) ⟷ zx_associator.
Proof.
    intros.
    unfold zx_braiding. unfold zx_associator.
    simpl_casts.
    rewrite cast_compose_l. simpl_casts.
    rewrite compose_assoc.
    rewrite cast_compose_l. simpl_casts.
    cleanup_zx. simpl_casts.    
    rewrite cast_compose_l. 
    simpl_casts. cleanup_zx.
    rewrite cast_compose_l. simpl_casts.
    rewrite (cast_compose_r _ _ _ (n_wire (m + o + n))).
    cleanup_zx. simpl_casts.
    rewrite hexagon_lemma_1_helper.
    reflexivity.
    Unshelve. all: lia.
Qed.

Lemma hexagon_lemma_2 : forall {n m o},
    (zx_inv_braiding ↕ n_wire o) ⟷ zx_associator ⟷ (n_wire m ↕ zx_inv_braiding)
    ∝ zx_associator ⟷ (@zx_inv_braiding (m + o) n) ⟷ zx_associator.
Proof.
    intros.
    unfold zx_inv_braiding. unfold zx_associator.
    simpl_casts.
    rewrite cast_compose_l. simpl_casts.
    rewrite compose_assoc.
    rewrite cast_compose_l. simpl_casts.
    cleanup_zx. simpl_casts.
    rewrite cast_compose_l.
    simpl_casts. cleanup_zx.
    rewrite cast_compose_l. simpl_casts.
    rewrite (cast_compose_r _ _ _ (n_wire (m + o + n))).
    cleanup_zx. simpl_casts.
Admitted.

#[export] Instance ZXBraidedMonoidalCategory : BraidedMonoidalCategory nat := {
    braiding := @zx_braiding;
    inv_braiding := @zx_inv_braiding;
    braiding_inv_compose := @zx_braiding_inv_compose;
    inv_braiding_compose := @zx_inv_braiding_compose;

    hexagon_1 := @hexagon_lemma_1;
    hexagon_2 := @hexagon_lemma_2;
}.

Local Close Scope Cat.