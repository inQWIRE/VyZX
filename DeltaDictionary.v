Require Export externals.QuantumLib.Prelim.
Require Import Coq.Arith.Peano_dec.

Module DeltaDict.

Inductive delta_dict {A : Set} : (option nat) -> Set :=
  | DD_None : delta_dict None
  | DD_Singleton (n : nat) : forall (a : A), delta_dict (Some n)
  | DD_Concat (n2 : nat) : forall n1 (a : A), n1 < n2 -> delta_dict (Some n1) -> delta_dict (Some n2).

Fixpoint toList {A : Set} {n} (dd : @delta_dict A n) : list (nat * A) :=
  match dd with
  | DD_None => []
  | DD_Singleton n a => [(n, a)]
  | DD_Concat n2 _ a _ dd' => (n2, a) :: (toList dd')
  end.

Fixpoint lookup {A : Set} {n} (dd : @delta_dict A n) key : option A :=
  match dd with
  | DD_None => None
  | DD_Singleton n a => if key =? n then Some a else None
  | DD_Concat n2 _ a _ dd' => if key =? n2 then Some a else lookup dd' key
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
    bdestruct (key =? n); [ | discriminate H].
    inversion H. 
    subst.
    simpl.
    left.
    easy.
  - simpl in H. 
    simpl.
    bdestruct (key =? n2).
    + left.
      inversion H.
      subst.
      easy.
    + right.
      apply IHdd.
      assumption.
Qed. 