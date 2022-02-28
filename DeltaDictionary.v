Require Export externals.QuantumLib.Prelim.
Require Import Coq.Arith.Peano_dec.

Module DeltaDict.

Definition tuple_leb (a : (nat * nat)) (b : (nat * nat)) : bool :=
  match a, b with
  | (a1, a2), (b1, b2) => if a1 <? b1 then true else 
                                  (if a1 =? b1 then a2 <? b2 else false)
  end.

Definition tuple_eqb (a : (nat * nat)) (b : (nat * nat)) : bool :=
  match a, b with
  | (a1, a2), (b1, b2) => (a1 =? b1) && (a2 =? b2) 
  end.

Lemma tuple_eqb_refl : forall (a : (nat * nat)), tuple_eqb a a = true.
Proof.
  intros.
  destruct a.
  simpl.
  rewrite 2 Nat.eqb_refl.
  easy.
Qed.

Notation "a <?? b" := (tuple_leb a b) (at level 35).
Notation "a =?? b" := (tuple_eqb a b) (at level 35).

Inductive delta_dict {A : Set} : (option (nat * nat)) -> Set :=
  | DD_None : delta_dict None
  | DD_Singleton (from to : nat) : forall (a : A), delta_dict (Some (from, to))
  | DD_Concat (from to : nat) : forall from2 to2 (a : A), (from2, to2) <?? (from, to) = true -> delta_dict (Some (from2, to2)) -> delta_dict (Some (from, to)).

Fixpoint toList {A : Set} {n} (dd : @delta_dict A n) : list ((nat * nat) * A) :=
  match dd with
  | DD_None => []
  | DD_Singleton from to a => [((from, to), a)]
  | DD_Concat from to _ _ a _ dd' => ((from, to), a) :: (toList dd')
  end.

Fixpoint lookup {A : Set} {n} (dd : @delta_dict A n) key : option A :=
  match dd with
  | DD_None => None
  | DD_Singleton from to a => if key =?? (from, to) then Some a else None
  | DD_Concat from to _ _ a _ dd' => if key =?? (from, to) then Some a else lookup dd' key
  end.

Lemma lookup_toList : forall {A : Set} {n} (dd : @delta_dict A n) key a,
                      lookup dd key = Some a -> In (key, a) (toList dd).
Proof.
  intros.
  generalize dependent key.
  generalize dependent a.
  induction dd; intros.
  - exfalso.
    simpl in H.
    discriminate H.
  - simpl in H.
    destruct key as [from' to'].
    bdestruct (from' =? from); bdestruct (to' =? to).
    all : simpl in H.
    2-4: exfalso.
    2 : rewrite <- Nat.eqb_neq in H1.
    3,4 : rewrite <- Nat.eqb_neq in H0.
    2 : rewrite H1 in H; rewrite andb_false_r in H.
    3,4 : rewrite H0 in H.
    2-4 : discriminate H.
    subst.
    rewrite 2 Nat.eqb_refl in H.
    simpl in H.
    inversion H. 
    subst.
    simpl.
    left.
    easy.
  - simpl in H. 
    simpl.
    destruct key as [from' to'].
    bdestruct (from' =? from); bdestruct (to' =? to).
    2-4: simpl in H.
    2 : rewrite <- Nat.eqb_neq in H1.
    3,4 : rewrite <- Nat.eqb_neq in H0.
    2 : rewrite H1 in H; rewrite andb_false_r in H.
    3,4 : rewrite H0 in H.
    2-4: right.
    2-4: apply IHdd.
    2-4: assumption.
    + subst.
      left.
      rewrite tuple_eqb_refl in H.
      inversion H.
      subst.
      easy.
Qed. 