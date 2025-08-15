Require Import ZXCore Proportional CapCup Stacks ZXperm States Gadgets ZXperm.
Import Setoid.


Definition is_controlled_scalar c (zx : ZX 1 0) :=
  state_0 ⟷ zx ∝= ⦰ /\
  state_1 ⟷ zx ∝= c .* ⦰.

Add Parametric Morphism c : (@is_controlled_scalar c) with signature
  proportional_by_1 ==> iff as is_controlled_scalar_mor.
Proof.
  unfold is_controlled_scalar.
  now intros ? ? ->.
Qed.

Definition is_controlled_state {n} (czx : ZX 1 n) :=
  state_0 ⟷ czx ∝= uniform_state n.

Add Parametric Morphism {n} : (@is_controlled_state n) with signature
  proportional_by_1 ==> iff as is_controlled_state_mor.
Proof.
  unfold is_controlled_state.
  now intros ? ? ->.
Qed.

Definition is_controlized {n m} (zx : ZX n m) (czx : ZX 1 (n + m)) :=
  is_controlled_state czx /\
  zx ∝= (/√2)^ (n + m) .* 
    state_to_proc (state_1 ⟷ czx).

Add Parametric Morphism {n m} : (@is_controlized n m) with signature
  proportional_by_1 ==> proportional_by_1 ==> iff as is_controlized_mor.
Proof.
  unfold is_controlized.
  intros ? ? Hrw ? ? ->.
  now rewrite Hrw.
Qed.


(* TODO: We can remove this, I believe *)
Definition controlled_half : ZX 1 0 :=
  zx_half ↕ (▷ ⟷ Z 1 0 0).



Definition box_controlizer : ZX 1 (1 + 1) :=
  (Z 1 2 0 ⟷ ((X 1 2 PI ⟷ (Z 1 0 (-(PI/4)) ↕ Z 1 0 (PI/4)) ⟷ 
    Z 0 0 0) ↕
    (X 1 2 PI ⟷ ((◁ ⟷ Z 1 2 0 ⟷ (— ↕ ◁)) ↕ —) ⟷ 
    (— ↕ (Z 2 1 0 ⟷ □))))).


Definition cupcap_controlizer : ZX 1 2 := 
  Z 1 2 0 ⟷ ((◁ ⟷ Z 1 0 0 ⟷ X 0 1 0 ⟷ Z 1 0 0) ↕ 
    (▷ ⟷ X 1 2 PI)).

Definition swap_controlizer : ZX 1 (2 + 2) :=
  (Z 1 3 0 ⟷ (Z 0 0 0 ↕ (◁ ⟷ Z 1 0 0) ↕ (◁ ⟷ Z 1 0 0) ↕ 
    (X 1 1 PI ⟷ Z 1 2 0 ⟷ ((◁ ⟷ X 1 2 0) ↕ (◁ ⟷ X 1 2 0))
    ⟷ (— ↕ (⨉ ↕ — ⟷ (— ↕ ⨉)))) )).


Definition X_1_0_controlizer β : ZX 1 (1 + 0) := 
  (Z 1 2 0 ⟷ ((◁ ⟷ Z 1 0 0) ↕ (X 1 1 PI ⟷ ◁ ⟷ X 1 1 β))).

Definition X_1_2_controlizer : ZX 1 (1 + 2) :=
  (Z 1 2 0 ⟷ ((◁ ⟷ Z 1 0 0 ⟷ Z 0 0 0) ↕ (▷ ⟷ X 1 3 PI))).

Lemma comp_conlzr_prf1 {n m k} : (n + m + (m + k))%nat = (n + (m + m) + k)%nat.
Proof. lia. Qed.

Lemma comp_conlzr_prf2 {n k} : (n + k)%nat = (n + 0 + k)%nat.
Proof. lia. Qed.



Definition compose_controlizer {n m k} (czx0 : ZX 1 (n + m)) 
  (czx1 : ZX 1 (m + k)) : 
  ZX 1 (n + k) :=
  (/2) ^ m .*
  Z 1 2 0 ⟷ (czx0 ↕ czx1) ⟷
  cast _ _ comp_conlzr_prf1 comp_conlzr_prf2
    (n_wire n ↕ n_cup m ↕ n_wire k).


Definition stack_controlizer {n m k l} (czx0 : ZX 1 (n + m)) 
  (czx1 : ZX 1 (k + l)) : 
  ZX 1 ((n + k) + (m + l)) :=
  Z 1 2 0 ⟷ (czx0 ↕ czx1) ⟷
  zx_invassoc (n + m) k l ⟷
  ((zx_assoc n m k 
    ⟷ (n_wire n ↕ zx_comm m k)
    ⟷ zx_invassoc n k m) ↕ n_wire l) ⟷
  zx_assoc (n + k) m l.


Definition wire_controlizer : ZX 1 (1 + 1) :=
  compose_controlizer box_controlizer box_controlizer.


Definition half_controlizer : ZX 1 (0 + 0) :=
  (zx_invsqrt2 ↕ zx_invsqrt2) ↕ (▷ ⟷ Z 1 0 0).

Definition two_controlizer : ZX 1 (0 + 0) :=
  ◁ ⟷ Z 1 0 0.

Definition empty_controlizer : ZX 1 0 := 
  stack_controlizer half_controlizer two_controlizer.


Fixpoint n_stack_controlizer {n m} k (czx : ZX 1 (n + m)) : ZX 1 (k * n + k * m) :=
  match k with
  | 0 => empty_controlizer
  | S k' => stack_controlizer czx (n_stack_controlizer k' czx)
  end.

Fixpoint n_stack1_controlizer k (czx : ZX 1 (1 + 1)) : ZX 1 (k + k) :=
  match k with
  | 0 => empty_controlizer
  | S k' => stack_controlizer czx (n_stack1_controlizer k' czx)
  end.

Definition n_wire_controlizer n : ZX 1 (n + n) :=
  n_stack1_controlizer n wire_controlizer.


Definition X_2_1_controlizer : ZX 1 (2 + 1) := X_1_2_controlizer.

Definition X_0_1_controlizer β : ZX 1 (0 + 1) := X_1_0_controlizer β.

Fixpoint X_S_0_controlizer n β : ZX 1 (S n + 0) :=
  match n with 
  | 0 => X_1_0_controlizer β
  | S n' => compose_controlizer
    (stack_controlizer X_2_1_controlizer (n_wire_controlizer n'))
    (X_S_0_controlizer n' β)
  end.

Fixpoint X_0_S_controlizer n β : ZX 1 (0 + S n) :=
  match n with 
  | 0 => X_0_1_controlizer β
  | S n' => compose_controlizer
    (X_0_S_controlizer n' β)
    (stack_controlizer X_1_2_controlizer (n_wire_controlizer n'))
  end.

Definition X_0_n_controlizer n β : ZX 1 n :=
  match n with 
  | 0 => 
    compose_controlizer (X_0_1_controlizer β) 
      (X_1_0_controlizer 0)
  | S n' => X_0_S_controlizer n' β
  end.

Definition X_controlizer n m β : ZX 1 (n + m) :=
  X_0_n_controlizer (n + m) β.

Definition Z_controlizer n m β : ZX 1 (n + m) :=
  compose_controlizer (compose_controlizer
    (n_stack1_controlizer n box_controlizer)
    (X_controlizer n m β))
    (n_stack1_controlizer m box_controlizer).

Fixpoint controlizer {n m} (zx : ZX n m) : ZX 1 (n + m) :=
  match zx with
  | ⦰ => empty_controlizer
  | — => wire_controlizer
  | □ => box_controlizer
  | ⊂ => cupcap_controlizer
  | ⊃ => cupcap_controlizer
  | ⨉ => swap_controlizer
  | X n m α => X_controlizer n m α
  | Z n m α => Z_controlizer n m α
  | zx0 ↕ zx1 => stack_controlizer (controlizer zx0) (controlizer zx1)
  | zx0 ⟷ zx1 => compose_controlizer (controlizer zx0) (controlizer zx1)
  end.



Lemma nn_n2 {n:nat} : (n + n = n * 2)%nat. Proof. lia. Qed.
Definition sum_controlizer {n} (c0 c1 : ZX 1 n) : ZX 1 n :=
  (X 0 1 0 ⟷ Z 1 0 0) ↕
  (
    Z 1 2 0 ⟷ (X 1 2 0 ↕ ◁) ⟷ (— ↕ Z 2 1 0) ⟷
    (c0 ↕ c1)
  ) ⟷
  zx_of_perm_cast (n + n) (n * 2) (kron_comm_perm 2 n) nn_n2 ⟷
  n ⇑ Z 2 1 0 ⟷
  cast _ _ (Nat.mul_1_r n) eq_refl (n_wire n).
