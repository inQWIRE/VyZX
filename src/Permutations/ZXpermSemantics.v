Require Import ZXCore.
Require Import CastRules.
Require Export ZXperm.
Require Import ZXpermAutomation.
Require Import QuantumLib.Permutations QuantumLib.Modulus.
Import CoreData.Proportional.

(** Core proofs of semantics of [ZXperm]s in terms of their
  underlying permutations *)

Local Open Scope nat. 

Lemma zxperm_square {n m} (zx : ZX n m) : 
  ZXperm zx -> n = m.
Proof.
  intros H; induction H; lia.
Qed.

Lemma zxperm_square_induction 
  (P : forall {n m : nat}, ZX n m -> Prop)
  (Pempty : P Empty)
  (Pwire : P Wire)
  (Pswap : P Swap)
  (Pstack : forall n m (zx0 : ZX n n) (zx1 : ZX m m), 
    ZXperm zx0 -> ZXperm zx1 -> 
    P zx0 -> P zx1 -> P (zx0 ↕ zx1))
  (Pcompose : forall n (zx0 zx1 : ZX n n),
    ZXperm zx0 -> ZXperm zx1 ->
    P zx0 -> P zx1 -> P (zx0 ⟷ zx1)) : 
    forall {n m} (zx : ZX n m), ZXperm zx -> P zx.
Proof.
  intros n m zx Hzx.
  induction Hzx;
  [assumption..| |].
  - pose proof (zxperm_square zx0 ltac:(auto)) as H0eq.
    pose proof (zxperm_square zx1 ltac:(auto)) as H1eq.
    gen zx0 zx1.
    revert H0eq H1eq.
    intros [] [].
    auto.
  - pose proof (zxperm_square zx0 ltac:(auto)) as H0eq.
    pose proof (zxperm_square zx1 ltac:(auto)) as H1eq.
    gen zx0 zx1.
    revert H0eq H1eq.
    intros [] [].
    auto.
Qed.

Lemma perm_of_zx_permutation {n m} (zx : ZX n m) : 
  ZXperm zx -> permutation n (perm_of_zx zx).
Proof.
  intros H.
  induction H using zxperm_square_induction; 
  show_permutation.
Qed.

#[export] Hint Resolve perm_of_zx_permutation : perm_db.
#[export] Hint Extern 4 (permutation _ (perm_of_zx _)) =>
  apply perm_of_zx_permutation;
  solve [auto with zxperm_db] : perm_db.

#[export] Hint Constructors ZXperm : zxperm_db.

Lemma empty_permutation_semantics : ⟦ Empty ⟧ = zxperm_to_matrix 0 Empty.
Proof. lma'. Qed.

Lemma wire_permutation_semantics : ⟦ Wire ⟧ = zxperm_to_matrix 1 Wire.
Proof. lma'. Qed.

Lemma swap_2_perm_semantics : ⟦ Swap ⟧ = zxperm_to_matrix 2 Swap.
Proof. lma'. Qed.

Lemma if_dist2 {T1 T2 T3 : Type} (f : T1 -> T2 -> T3) 
  (b1 b2 : bool) x1 x2 x3 x4  :
  f (if b1 then x1 else x2) (if b2 then x3 else x4) = 
  if b1 && b2 then f x1 x3 else 
    (if b1 then f x1 x4 else 
    (if b2 then f x2 x3 else f x2 x4)).
Proof. 
  now destruct b1, b2. 
Qed.

Lemma stack_perms_semantics {n0 n1 m0 m1}
  {zx0 : ZX n0 m0} {zx1 : ZX n1 m1} (H0 : n0 = m0) (H1 : n1 = m1) 
  (Hzx0 : ⟦ zx0 ⟧ = zxperm_to_matrix n0 zx0) 
  (Hzx1 : ⟦ zx1 ⟧ = zxperm_to_matrix n1 zx1) 
  (Hzx0perm : permutation n0 (perm_of_zx zx0))
  (Hzx1perm : permutation n1 (perm_of_zx zx1)) : 
  ⟦ zx0 ↕ zx1 ⟧ = zxperm_to_matrix (n0 + n1) (zx0 ↕ zx1).
Proof.
  simpl.
  subst.
  rewrite perm_to_matrix_of_stack_perms by easy. 
  now f_equal.
Qed.

Lemma compose_permutation_semantics {n m o} {zx0 : ZX n m} {zx1 : ZX m o}
  (H0 : n = m)
  (Hzx0 : ⟦ zx0 ⟧ = zxperm_to_matrix n zx0)
  (Hzx1 : ⟦ zx1 ⟧ = zxperm_to_matrix m zx1) 
  (Hzx0perm : permutation n (perm_of_zx zx0))
  (Hzx1perm : permutation m (perm_of_zx zx1)) :
  ⟦ zx0 ⟷ zx1 ⟧ = zxperm_to_matrix n (zx0 ⟷ zx1).
Proof.
  simpl.
  subst.
  rewrite perm_to_matrix_compose by auto with perm_db.
  now rewrite Hzx0, Hzx1.
Qed.

Lemma cast_permutations_semantics {n0 n1} {zx : ZX n0 n0} 
  (Hn : n1 = n0)
  (Hzx : ⟦ zx ⟧ = zxperm_to_matrix n1 zx) :
  ⟦ cast _ _ Hn Hn zx ⟧ = zxperm_to_matrix n1 (cast _ _ Hn Hn zx).
Proof. subst; rewrite ?cast_id_eq; easy. Qed.

Lemma perm_of_zx_permutation_semantics {n m} (zx : ZX n m) : 
  ZXperm zx -> ⟦ zx ⟧ = zxperm_to_matrix n zx.
Proof.
  intros H.
  induction H using zxperm_square_induction.
  - apply empty_permutation_semantics.
  - apply wire_permutation_semantics.
  - apply swap_2_perm_semantics.
  - eapply stack_perms_semantics; auto with perm_db.
  - apply compose_permutation_semantics; auto with perm_db.
Qed.

(* ... which enables the main result: *)

Lemma prop_eq_of_equal_perm {n m} {zx0 zx1 : ZX n m}
	(Hzx0 : ZXperm zx0) (Hzx1 : ZXperm zx1)
	(Hperm : perm_of_zx zx0 = perm_of_zx zx1) :
	zx0 ∝= zx1.
Proof.
  hnf.
	rewrite (perm_of_zx_permutation_semantics zx0 Hzx0),
		(perm_of_zx_permutation_semantics zx1 Hzx1).
	f_equal; easy.
Qed.

Lemma prop_eq_of_perm_eq {n m} {zx0 zx1 : ZX n m}
	(Hzx0 : ZXperm zx0) (Hzx1 : ZXperm zx1)
	(Hperm : perm_eq n (perm_of_zx zx0) (perm_of_zx zx1)) :
	zx0 ∝= zx1.
Proof.
  pose proof (zxperm_square zx0 Hzx0); subst.
  hnf.
	rewrite (perm_of_zx_permutation_semantics zx0 Hzx0),
		(perm_of_zx_permutation_semantics zx1 Hzx1).
  now apply perm_to_matrix_eq_of_perm_eq. 
Qed.

(* TODO: split intro prop_perm_eq and prop_perm_eqΩ *)

Ltac to_prop_eq_then tac :=
  lazymatch goal with 
  | |- _ ∝ _ => 
    apply proportional_of_by_1; tac
  | |- _ ∝[_] _ =>
    zxrefl; only 1: tac
  | |- _ ∝= _ => tac
  | |- _ => tac
  end.

Ltac prop_perm_eq_nosimpl_base :=
  intros;
  (* Goal: zx0 ∝= zx1 *)
  apply prop_eq_of_equal_perm; [
  (* New goals: *)
    (*1: ZXperm _ zx0 *) auto 10 with zxperm_db |
    (*2: ZXperm _ zx1*) auto 10 with zxperm_db |
    (*3: perm_of_zx zx0 = perm_of_zx zx1*) 
  ].

Ltac prop_perm_eq_nosimpl :=
  to_prop_eq_then prop_perm_eq_nosimpl_base.

Ltac prop_perm_eq_base :=
  intros;
  autounfold with zxperm_db;
  simpl_casts;
  simpl_permlike_zx;
  (* __cast_prop_sides_to_square; *)
  (* Goal: zx0 ∝ zx1 *)
  apply prop_eq_of_equal_perm; [
  (* New goals: *)
    (*1: ZXperm _ zx0 *) auto 10 with zxperm_db |
    (*2: ZXperm _ zx1*) auto 10 with zxperm_db |
    (*3: perm_of_zx zx0 = perm_of_zx zx1*) cleanup_perm_of_zx; try easy; try lia
  ].

Ltac prop_perm_eq :=
  to_prop_eq_then prop_perm_eq_base.

(* TODO: switch all over to this: *)
Ltac by_perm_eq_base :=
  intros;
  autounfold with zxperm_db;
  simpl_casts;
  simpl_permlike_zx;
  (* __cast_prop_sides_to_square; *)
  (* Goal: zx0 ∝ zx1 *)
  apply prop_eq_of_perm_eq; [
  (* New goals: *)
    (*1: ZXperm _ zx0 *) auto 100 with zxperm_db |
    (*2: ZXperm _ zx1*) auto 100 with zxperm_db |
    (*3: forall k, k < n -> perm_of_zx zx0 k = perm_of_zx zx1 k *) 
    cleanup_perm_of_zx; try easy; try lia
  ].

Ltac by_perm_eq := to_prop_eq_then by_perm_eq_base.

Ltac by_perm_eq_nosimpl_base :=
  intros;
  autounfold with zxperm_db;
  (* Goal: zx0 ∝ zx1 *)
  apply prop_eq_of_perm_eq; [
  (* New goals: *)
    (*1: ZXperm _ zx0 *) auto 100 with zxperm_db |
    (*2: ZXperm _ zx1*) auto 100 with zxperm_db |
    
  ].

Ltac by_perm_eq_nosimpl := to_prop_eq_then by_perm_eq_nosimpl_base.

