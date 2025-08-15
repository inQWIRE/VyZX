Require Import ZXCore Proportional.

From QuantumLib Require Complex Matrix RealAux Polar.

Import Setoid.

(** Results about gadgets, i.e. [ZX 0 0]'s, including a definition 
  [zx_of_const] giving an arbitrary constant as a gadget *)

(* There are several functions we don't need or want exposed as
  part of the main module, as they are just facts about C. If 
  they were less ZX-specific, they could go in QuantumLib. *)
Module ScalarC.

Import Polar Modulus.

Definition prop_lb (z : C) : nat := 
  (BinInt.Z.to_nat (Int_part (ln (Cmod z / 2) / ln (√2))%R%C) + 1)%nat.

(* Decomposition assuming |z| <= 2 *)
Definition small_decomp (z : C) : R * R :=
  let a := acos ((Cmod z)^2 / 2 - 1) in
  (a, get_arg (z / (1 + Cexp a))).

Definition prop_decomp (z : C) : nat * (R * R) :=
  (prop_lb z, small_decomp (z / (√2 ^ prop_lb z))).

End ScalarC.

(* Some specific values as gadgets *)

Definition zx_sqrt2 : ZX 0 0 :=
  Z 0 1 0 ⟷ X 1 0 PI.
Lemma zx_sqrt2_defn : zx_sqrt2 =
  Z 0 1 0 ⟷ X 1 0 PI.
Proof. reflexivity. Qed.
(* We don't ever want reduction to unfold zx_sqrt2 *)
#[global]
Opaque zx_sqrt2.

Definition zx_invsqrt2 : ZX 0 0 :=
  X 0 3 0 ⟷ Z 3 0 0.
Lemma zx_invsqrt2_defn : zx_invsqrt2 =
  X 0 3 0 ⟷ Z 3 0 0.
Proof. reflexivity. Qed.
(* We don't ever want reduction to unfold zx_invsqrt2 *)
#[global]
Opaque zx_invsqrt2.

Definition zx_half : ZX 0 0 := zx_invsqrt2 ↕ zx_invsqrt2.
Lemma zx_half_defn : zx_half = zx_invsqrt2 ↕ zx_invsqrt2.
Proof. reflexivity. Qed.
(* We don't ever want reduction to unfold zx_half *)
#[global]
Opaque zx_half.


Definition zx_two : ZX 0 0 := Z 0 0 0.
Lemma zx_two_defn : zx_two = Z 0 0 0.
Proof. reflexivity. Qed.
(* We don't ever want reduction to unfold zx_two *)
#[global]
Opaque zx_two.


Definition zx_cexp (r : R) : ZX 0 0 :=
  X 0 1 r ⟷ Z 1 0 PI ⟷ zx_invsqrt2.
Lemma zx_cexp_defn (r : R) : zx_cexp r =
  X 0 1 r ⟷ Z 1 0 PI ⟷ zx_invsqrt2.
Proof. reflexivity. Qed.
(* We don't ever want reduction to unfold zx_cexp *)
#[global]
Opaque zx_cexp.

(* Gadget representing √2 ^ n as a diagram *)
Fixpoint zx_nsqrt2 (n : nat) : ZX 0 0 :=
  match n with 
  | 0 => Empty
  | S n' => zx_sqrt2 ⟷ zx_nsqrt2 n'
  end.

Import ScalarC.

(* Gadget representing the scalar z as a ZX-diagram *)
Definition zx_of_const (z : C) : ZX 0 0 :=
  zx_nsqrt2 (fst (prop_decomp z)) ⟷
  Z 0 0 (fst (snd (prop_decomp z))) ⟷
  zx_cexp (snd (snd (prop_decomp z))).

Lemma zx_of_const_defn (z : C) : zx_of_const z = 
  zx_nsqrt2 (fst (prop_decomp z)) ⟷
  Z 0 0 (fst (snd (prop_decomp z))) ⟷
  zx_cexp (snd (snd (prop_decomp z))).
Proof. reflexivity. Qed.
(* We don't ever want reduction to unfold zx_of_const *)
#[global]
Opaque zx_of_const.

(* Get the constant associated to a gadget. We will 
  show this is an inverse to zx_of_const. *)
Definition const_of_zx (zx : ZX 0 0) : C :=
  ⟦ zx ⟧ O O.

Add Parametric Morphism : const_of_zx 
  with signature proportional_by_1 ==> eq as const_of_zx_mor.
Proof.
  intros zx zx' Hzx.
  unfold const_of_zx.
  now rewrite Hzx.
Qed.

(* A diagram scaling [zx] by [c], so that [⟦ c.* zx ⟧ = c .* ⟦ zx ⟧] *)
Definition zx_scale {n m} (c : C) (zx : ZX n m) : ZX n m :=
  zx_of_const c ↕ zx.

Notation "c '.*' zx" := (zx_scale c zx) 
  (at level 40, left associativity) : ZX_scope.

Lemma zx_scale_defn {n m} c (zx : ZX n m) : c .* zx = zx_of_const c ↕ zx.
Proof. reflexivity. Qed.

Lemma zx_scale_fun_defn : @zx_scale = fun n m c zx => zx_of_const c ↕ zx.
Proof. reflexivity. Qed.

(* We really don't want zx_scale to reduce, as that'll be messy
  (especially with dimensions!) *)
#[global] Opaque zx_scale.

Add Parametric Morphism {n m} c : (@zx_scale n m c) with signature 
  proportional_by_1 ==> proportional_by_1 as zx_scale_prop_by_1_mor.
Proof.
  rewrite zx_scale_fun_defn.
  intros zx0 zx1 ->.
  reflexivity.
Qed.

Add Parametric Morphism {n m} c : (@zx_scale n m c) with signature 
  proportional ==> proportional as zx_scale_mor.
Proof.
  rewrite zx_scale_fun_defn.
  intros zx0 zx1 ->.
  reflexivity.
Qed.




(* NB: Can be made effective using [Z 0 0 PI] for [0] *)
(* A diagram representing the zero element *)
Definition zx_zero {n m} : ZX n m :=
  C0 .* Z n m 0.

Lemma zx_zero_defn n m : zx_zero = C0 .* Z n m 0.
Proof.
  reflexivity.
Qed.

(* Don't unfold zx_zero *)
Global Opaque zx_zero.

(* May add this back later *)
(* Notation "0" := zx_zero : ZX_scope. *)