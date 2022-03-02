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

Notation "<[]>" := (Empty 0).

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

Notation "key !! m" := (lookup key m) (at level 20).
Notation "key ?? m" := (KeyIn key m) (at level 20).

Lemma neq_le_is_lt {n m : nat} : n <> m -> m <= n -> m < n.
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
        apply (@Node _ _ _ _ _ (Empty m) (Leaf n a) (neq_le_is_lt H H0)).
  - bdestruct (n =? n0).
    + rewrite H, Nat.min_id, Nat.max_id.
      exact (Leaf n0 a).
    + bdestruct (n <? n0).
      * rewrite Nat.min_r; [ | apply Nat.lt_le_incl; assumption ].
        rewrite Nat.max_l; [ | apply Nat.lt_le_incl; assumption ].
        apply (@Node _ _ _ _ _ (Leaf n a) (Leaf n0 val) H0).
      * rewrite Nat.min_l; [ | apply H0 ].
        rewrite Nat.max_r; [ | apply H0 ].
        apply (@Node _ _ _ _ _ (Leaf n0 val) (Leaf n a) (neq_le_is_lt H H0)).
  - bdestruct (n <=? maxl). 
    + (* Left insertion *)
      rewrite Nat.max_l. 
      * assert (leftInsert : BinaryTree A (Init.Nat.min minl n) (Init.Nat.max maxl n)) 
          by exact (insert A n a minl maxl bt1).
        assert (Hlt : Init.Nat.max maxl n < minr).
        { rewrite Nat.max_l; assumption. }
        apply (@Node _ _ _ _ _ leftInsert bt2 Hlt).
      * transitivity maxl; [ assumption | ].
        apply Nat.lt_le_incl in l.
        transitivity minr; [ assumption | ].
        apply (BinaryTree_bounds bt2).
    + (* Right insertion *)
      rewrite Nat.min_l.
      * assert (rightInsert : BinaryTree A (Init.Nat.min minr n) (Init.Nat.max maxr n)) 
          by exact (insert A n a minr maxr bt2).
      assert (Hlt : maxl < Init.Nat.min minr n).
      { apply Nat.min_glb_lt; assumption. }
      apply (@Node _ _ _ _ _ bt1 rightInsert Hlt).
      * apply Nat.lt_le_incl in H.
        transitivity maxl; [ | assumption].
        apply (BinaryTree_bounds bt1).
Defined.

Notation "<[ ( key , val ) ++ m ]>" := (insert key val m).

Lemma insert_lookup : forall {A n m} (bt : BinaryTree A n m) key val,
  key !! <[ (key, val) ++ bt ]> = Some val.
Proof.
  intros.
  generalize dependent key.
  generalize dependent val.
  induction bt; intros.
  - unfold insert.
    destruct (beq_reflect key m);
    unfold eq_rect_r.
    + simpl_eqs.
      rewrite Nat.eqb_refl.
      reflexivity.
    + destruct (blt_reflect key m); simpl_eqs.
      * rewrite Nat.leb_refl, Nat.eqb_refl.
        reflexivity.
      * bdestruct (key <=? m).
        -- exfalso.
           apply le_lt_or_eq in H.
           destruct H; contradiction.
        -- rewrite Nat.eqb_refl.
           reflexivity.
  - unfold insert.
    destruct (beq_reflect key n);
    unfold eq_rect_r.
    + simpl_eqs.
      rewrite Nat.eqb_refl.
      reflexivity.
    + destruct (blt_reflect key n); simpl_eqs.
      * rewrite Nat.leb_refl, Nat.eqb_refl.
        reflexivity.
      * bdestruct (key <=? n).
        -- exfalso.
           apply le_lt_or_eq in H.
           destruct H; contradiction.
        -- rewrite Nat.eqb_refl.
           reflexivity.
  - unfold insert. 
    destruct (ble_reflect key maxl);
    unfold eq_rect_r;
    simpl_eqs.
    + bdestruct (key <=? Init.Nat.max maxl key).
      * apply IHbt1.
      * exfalso.
        rewrite Nat.max_l in H; [ | assumption ].
        contradict H.
        Search (not (gt _ _)).
        apply le_not_gt.
        assumption.
    + bdestruct (key <=? maxl).
      * congruence.
      * apply IHbt2.
Qed.

Corollary insert_KeyIn : forall {A n m} (bt : BinaryTree A n m) key val,
  key ?? <[ (key, val) ++ bt ]>.
Proof.
  intros.
  unfold KeyIn.
  exists val.
  apply insert_lookup.
Qed.

