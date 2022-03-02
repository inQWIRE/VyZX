Require Export externals.QuantumLib.Prelim.

Inductive BinaryTree (A : Type) :  nat -> nat -> Type :=
  | Empty : forall m, BinaryTree A m m
  | Leaf n (val : A) : BinaryTree A n n 
  | Node {minl maxl minr maxr} 
                     (left : BinaryTree A minl maxl)
                     (right : BinaryTree A minr maxr) :
                     maxl < minr -> BinaryTree A minl maxr.

Arguments Empty {A}%type_scope _.
Arguments Leaf {A}%type_scope _ _.
Arguments Node {A}%type_scope {minl} {maxl} {minr} {maxr} _ _ {Hlt}.

Lemma BinaryTree_bounds : forall {A : Type} {n m : nat} (bt : BinaryTree A n m),
  n <= m.
Proof.
  intros.
  induction bt.
  - reflexivity.
  - reflexivity.
  - apply Nat.lt_le_incl in l.
    transitivity maxl; [ assumption | ].
    transitivity minr; assumption.
Qed.

Fixpoint lookup {A : Type} {min max : nat} (n : nat) (bt : BinaryTree A min max) : option A :=
  match bt with
  | Empty _     => None
  | Leaf m val => if n =? m then Some val else None
  | @Node _ minl maxl minr maxr lft rgt _ => 
      if n <=? maxl then lookup n lft
      else lookup n rgt
  end.

Definition KeyIn {A : Type} 
          (n : nat) {min max : nat} 
          (bt : BinaryTree A min max) := exists a, lookup n bt = Some a.

Lemma insertHelper {n m : nat} : n <> m -> m <= n -> m < n.
Proof.
  intros.
  destruct (le_lt_or_eq m n H0).
  - assumption.
  - symmetry in H1.
    contradiction.
Qed.

Fixpoint insert {A : Type} (n : nat) (a : A) {lft rgt : nat} 
                (bt : BinaryTree A lft rgt) : BinaryTree A (min lft n) (max rgt n).
Proof.
  destruct bt.
  - bdestruct (n =? m).
    + rewrite H, Nat.min_id, Nat.max_id.
      exact (Leaf m a).
    + bdestruct (n <? m).
      * rewrite Nat.min_r; [ | apply Nat.lt_le_incl; assumption ].
        rewrite Nat.max_l; [ | apply Nat.lt_le_incl; assumption ].
        apply (@Node _ _ _ _ _ (Leaf n a) (Empty m) H0).
      * rewrite Nat.min_l; [ | apply H0 ].
        rewrite Nat.max_r; [ | apply H0 ].
        apply (@Node _ _ _ _ _ (Empty m) (Leaf n a) (insertHelper H H0)).
  - bdestruct (n =? n0).
    + rewrite H, Nat.min_id, Nat.max_id.
      exact (Leaf n0 a).
    + bdestruct (n <? n0).
      * rewrite Nat.min_r; [ | apply Nat.lt_le_incl; assumption ].
        rewrite Nat.max_l; [ | apply Nat.lt_le_incl; assumption ].
        apply (@Node _ _ _ _ _ (Leaf n a) (Leaf n0 val) H0).
      * rewrite Nat.min_l; [ | apply H0 ].
        rewrite Nat.max_r; [ | apply H0 ].
        apply (@Node _ _ _ _ _ (Leaf n0 val) (Leaf n a) (insertHelper H H0)).
  - bdestruct (n <=? maxl). 
    + (* Left insertion *)
      rewrite Nat.max_l. 
      * assert (leftInsert : BinaryTree A (Init.Nat.min minl n) (Init.Nat.max maxl n)).
        { apply insert; [ apply a | apply bt1 ]. }
        assert (Hlt : Init.Nat.max maxl n < minr).
        { rewrite Nat.max_l; assumption. }
        apply (@Node _ _ _ _ _ leftInsert bt2 Hlt).
      * transitivity maxl; [ assumption | ].
        apply Nat.lt_le_incl in l.
        transitivity minr; [ assumption | ].
        apply (BinaryTree_bounds bt2).
    + (* Right insertion *)
      rewrite Nat.min_l.
      * assert (rightInsert : BinaryTree A (Init.Nat.min minr n) (Init.Nat.max maxr n)).
        { exact (insert A n a bt2).


