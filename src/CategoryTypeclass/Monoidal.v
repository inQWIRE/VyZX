Require Import CoreData.
Require Import CoreRules.
Require Import Category.

Reserved Notation "A ⊠ B" (at level 40).
Reserved Notation "f ◇ g" (at level 40).

Class MonoidalCategory (C : Type) `{Category C} : Type := {
    tensor : C -> C -> C
        where "A ⊠ B" := (tensor A B);
    I : C;

    tensor_morph {A B M N : C} : 
        (A ~> M) -> (B ~> N) -> (A ⊠ B) ~> (M ⊠ N)
        where "f ◇ g" := (tensor_morph f g);
    
    (* These are all isomorphisms *)
    associator {A B M : C} : A ⊠ (B ⊠ M) ~> (A ⊠ B) ⊠ M;
    inv_associator {A B M : C} : (A ⊠ B) ⊠ M ~> A ⊠ (B ⊠ M);
    associator_iso {A B M : C} : A ⊠ (B ⊠ M) ≅ (A ⊠ B) ⊠ M;

    left_unitor {A : C} : I ⊠ A ~> A;
    inv_left_unitor {A : C} : A ~> I ⊠ A;
    left_unitor_iso {A : C} : I ⊠ A ≅ A;

    right_unitor {A : C} : A ⊠ I ~> A;
    inv_right_unitor {A : C} : A ~> A ⊠ I;
    right_unitor_iso {A : C} : A ⊠ I ≅ A;

    bifunctor_id {A B : C} : 
        identity A ◇ identity B ≃ identity (A ⊠ B);
    bifunctor_comp {A B M N P Q : C} 
        {g : A ~> M} {f : B ~> N}
        {k : M ~> P} {h : N ~> Q} : 
        (k ◇ h) ∘ (g ◇ f) ≃ (k ∘ g) ◇ (h ∘ f);

    (* Verify α, λ, ρ are natural transformations *)
    associator_natural {A B M N P Q : C} 
        {f : A ~> B} {g : M ~> N } {h : P ~> Q} : 
        associator ∘ (f ◇ (g ◇ h)) ≃ ((f ◇ g) ◇ h) ∘ associator;
    left_unitor_natural {A B : C} {f : A ~> B} : 
        f ∘ left_unitor ≃ left_unitor ∘ (identity I ◇ f);
    right_unitor_natural {A B : C} {f : A ~> B} : 
        f ∘ right_unitor ≃ right_unitor ∘ (f ◇ identity I);

    (* Commutative diagrams *)
    triangle {A B : C} : 
        (identity A ◇ left_unitor) ∘ inv_associator 
        ≃ right_unitor ◇ identity B;
    pentagon {A B M N : C} : 
        (identity A ◇ inv_associator) ∘ inv_associator 
            ∘ (inv_associator ◇ identity N) 
        ≃ inv_associator ∘ @inv_associator (A ⊠ B) M N;
}.

Notation "A ⊠ B" := (tensor A B). (* \boxtimes *)
Notation "f ◇ g" := (tensor_morph f g). (* \Diamond *)

Definition ZX_associator {n m o} :=
    let l := (n + (m + o))%nat in
    let r := ((n + m) + o)%nat in
    let assoc := Nat.add_assoc n m o in
        cast l r (eq_refl l) (eq_sym assoc) (n_wire l).

Definition ZX_inv_associator {n m o} :=
    let l := ((n + m) + o)%nat in
    let r := (n + (m + o))%nat in
    let assoc := Nat.add_assoc n m o in 
        cast l r (eq_refl l) assoc (n_wire l).

Lemma associator_lemma : forall {n m o p q r} 
    (zx0 : ZX n m) (zx1 : ZX o p) (zx2 : ZX q r),
    (zx0 ↕ (zx1 ↕ zx2)) ⟷ ZX_associator 
    ∝ ZX_associator ⟷ ((zx0 ↕ zx1) ↕ zx2).
Proof.
    intros. 
    unfold ZX_associator.
    rewrite cast_compose_l.
    rewrite cast_compose_r.
    cleanup_zx; simpl_casts.
    rewrite stack_assoc.
    reflexivity.
Qed.

Definition ZX_left_unitor {n} := 
    cast (0 + n) n (Nat.add_0_l n) (eq_refl n) (n_wire n).

Definition ZX_inv_left_unitor {n} := 
    cast n (0 + n) (eq_refl n) (Nat.add_0_l n) (n_wire n).

Lemma left_unitor_lemma : forall {n m} (zx : ZX n m), 
    ZX_left_unitor ⟷ zx ∝ (n_wire 0) ↕ zx ⟷ ZX_left_unitor.
Proof.
    intros.
    unfold ZX_left_unitor.
    simpl_casts.
    rewrite nwire_removal_l.
    rewrite stack_empty_l.
    rewrite nwire_removal_r.
    reflexivity.
Qed.

Definition ZX_right_unitor {n} := 
    cast (n + 0) n (Nat.add_0_r n) (eq_refl n) (n_wire n).

Definition ZX_inv_right_unitor {n} := 
    cast n (n + 0) (eq_refl n) (Nat.add_0_r n) (n_wire n).

Lemma right_unitor_lemma : forall {n m} (zx : ZX n m), 
    ZX_right_unitor ⟷ zx ∝ zx ↕ (n_wire 0) ⟷ ZX_right_unitor.
Proof.
    intros.
    unfold ZX_right_unitor; cleanup_zx.
    rewrite <- cast_compose_mid_contract.
    cleanup_zx.
    rewrite cast_compose_l; simpl_casts.
    rewrite nwire_removal_l.
    reflexivity.
    Unshelve.
    easy.
    easy.
Qed.

Lemma triangle_lemma : forall {n m}, 
    ZX_inv_associator ⟷ (n_wire n ↕ ZX_left_unitor) ∝ 
    ZX_right_unitor ↕ n_wire m.
Proof.
    intros.
    unfold ZX_inv_associator.
    unfold ZX_right_unitor.
    unfold ZX_left_unitor.
    simpl_casts.
    repeat rewrite <- nstack1_split.
    cleanup_zx.
    simpl_casts.
    reflexivity.
Qed.

Lemma pentagon_lemma : forall {n m o p}, 
    (ZX_inv_associator ↕ n_wire p) ⟷ 
        (ZX_inv_associator ⟷ (n_wire n ↕ ZX_inv_associator)) 
    ∝ (@ZX_inv_associator (n + m) o p) ⟷ ZX_inv_associator.
Proof.
    intros.
    unfold ZX_inv_associator.
    rewrite <- ComposeRules.compose_assoc.
    simpl_casts.
    repeat rewrite n_wire_stack.
    repeat rewrite cast_compose_l.
    repeat rewrite cast_compose_r.
    repeat rewrite nwire_removal_r.
    simpl_casts; reflexivity.
Qed.

#[export] Instance ZXMonoidalCategory : MonoidalCategory nat := {
    tensor := Nat.add;
    I := 0;

    tensor_morph _ _ _ _ := Stack;

    associator := @ZX_associator;
    inv_associator := @ZX_inv_associator;
    associator_iso := Nat.add_assoc;

    left_unitor := @ZX_left_unitor;
    inv_left_unitor := @ZX_inv_left_unitor;
    left_unitor_iso := Nat.add_0_l;

    right_unitor := @ZX_right_unitor;
    inv_right_unitor := @ZX_inv_right_unitor;
    right_unitor_iso := Nat.add_0_r;

    bifunctor_id := n_wire_stack;
    bifunctor_comp _ _ _ _ _ _ g f k h := 
        equiv_symm (stack_compose_distr g k f h);

    associator_natural := @associator_lemma;
    left_unitor_natural := @left_unitor_lemma;
    right_unitor_natural := @right_unitor_lemma;

    triangle := @triangle_lemma;
    pentagon := @pentagon_lemma;
}.
