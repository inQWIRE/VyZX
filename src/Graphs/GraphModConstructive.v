Require Import Proportional.
Require Import ZXCore.
Require Import List.
Require Import Nat.
Require Import Decidable.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.FSets.FSetInterface.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Structures.OrderedType.



Module ZXG.

  Module ZXVert.
    
    Inductive Vertex := 
    | zsp (n : nat) (r : R)
    | xsp (n : nat) (r : R).

    Definition vertex_id (x : Vertex) : nat :=
      match x with 
      | zsp n r => n
      | xsp n r => n
      end.

    Definition vertex_rot (x : Vertex) : R :=
      match x with 
      | zsp n r => r
      | xsp n r => r
      end.

    Definition lt (x y : ZXVert.Vertex) :=
    match x, y with
    | ZXVert.zsp n0 r0, ZXVert.zsp n1 r1 => 
      (n0 = n1 /\ r0 < r1) \/ (n0 < n1)%nat
    | ZXVert.xsp n0 r0, ZXVert.xsp n1 r1 => 
      (n0 = n1 /\ r0 < r1) \/ (n0 < n1)%nat
    | ZXVert.zsp _ _, ZXVert.xsp _ _ => True
    | ZXVert.xsp _ _, ZXVert.zsp _ _ => False
    end.

  End ZXVert.

  Module OTVertex <: OrderedType.

    Definition t := ZXVert.Vertex.

    Definition eq (x y : ZXVert.Vertex) := x = y.

    Definition eq_equiv : Equivalence eq.
    Proof.
      constructor.
      - constructor.
      - intros x y H.
        rewrite H.
        reflexivity.
      - intros x y z H0 H1.
        rewrite H0, H1.
        reflexivity. Defined.

    Definition lt := ZXVert.lt.

    Definition lt_strorder : StrictOrder lt.
    Proof.
      constructor.
      - intros x.
        destruct x.
        + intros [ [Hn Hr] | Hn ].
          * apply (Rlt_irrefl r).
            assumption.
          * apply (Nat.lt_irrefl n).
            assumption.
        + intros [ [Hn Hr] | Hn].
          * apply (Rlt_irrefl r).
            assumption.
          * apply (Nat.lt_irrefl n).
            assumption.
      - intros [] [] []; try auto; try contradiction.
        intros [[]|] [[]|]; subst; simpl;
          try (right; assumption).
        + left.
          split; auto.
          apply (Rlt_trans r r0); assumption.
        + right.
          apply (Nat.lt_trans n n0); assumption.
        + intros [[]|] [[]|]; subst; simpl;
          try (right; assumption).
          * left.
            split; auto.
            apply (Rlt_trans r r0); assumption.
          * right.
            apply (Nat.lt_trans n n0); assumption. Defined.
  
    Definition lt_compat : Proper (eq==>eq==>iff) lt.
    Proof.
      constructor.
      rewrite H.
      rewrite H0.
      auto.
      rewrite H.
      rewrite H0.
      auto. Defined.

    Definition compare : forall x y : ZXVert.Vertex,
      Compare ZXVert.lt eq x y.
    Proof.
      intros.
      destruct x,y.
      - remember (n ?= n0).
        destruct c.
        + remember (total_order_T r r0).
          destruct s.
          destruct s.
          * apply LT.
            simpl.
            left.
            split; auto.
            apply Nat.compare_eq.
            symmetry.
            assumption.
          * subst.
            apply EQ.
            symmetry in Heqc.
            apply Nat.compare_eq in Heqc.
            subst.
            reflexivity.
          * apply GT.
            simpl.
            left.
            split; auto.
            symmetry in Heqc.
            apply Nat.compare_eq in Heqc.
            symmetry.
            assumption.
        + apply LT.
          simpl.
          symmetry in Heqc.
          apply nat_compare_Lt_lt in Heqc.
          right; assumption.
        + apply GT.
          simpl.
          symmetry in Heqc.
          apply nat_compare_Gt_gt in Heqc.
          right.
          auto.
      - simpl.
        apply LT.
        constructor.
      - simpl.
        apply GT.
        constructor.
      - remember (n ?= n0).
        destruct c.
        + remember (total_order_T r r0).
          destruct s.
          destruct s.
          * apply LT.
            simpl.
            left.
            split; auto.
            apply Nat.compare_eq.
            symmetry.
            assumption.
          * subst.
            apply EQ.
            symmetry in Heqc.
            apply Nat.compare_eq in Heqc.
            subst.
            reflexivity.
          * apply GT.
            simpl.
            left.
            split; auto.
            symmetry in Heqc.
            apply Nat.compare_eq in Heqc.
            symmetry.
            assumption.
        + apply LT.
          simpl.
          symmetry in Heqc.
          apply nat_compare_Lt_lt in Heqc.
          right; assumption.
        + apply GT.
          simpl.
          symmetry in Heqc.
          apply nat_compare_Gt_gt in Heqc.
          right.
          auto.
    Defined.

    Lemma eq_dec : forall (x y : ZXVert.Vertex),
      { x = y } + { x <> y}.
    Proof.
      intros [n r | n r] [n0 r0 | n0 r0].
      - destruct (Nat.eq_dec n n0); subst.
        + destruct (total_order_T r r0).
          destruct s.
          * right.
            intros contra.
            inversion contra.
            apply (Rlt_irrefl r).
            subst; assumption.
          * subst; left; reflexivity.
          * right.
            intros contra.
            inversion contra.
            apply (Rlt_irrefl r).
            subst; assumption.
        + right.
          intros contra.
          apply n1.
          inversion contra.
          reflexivity.
    - right.
      easy.
    - right.
      easy.
    - destruct (Nat.eq_dec n n0); subst.
        + destruct (total_order_T r r0).
          destruct s.
          * right.
            intros contra.
            inversion contra.
            apply (Rlt_irrefl r).
            subst; assumption.
          * subst; left; reflexivity.
          * right.
            intros contra.
            inversion contra.
            apply (Rlt_irrefl r).
            subst; assumption.
        + right.
          intros contra.
          apply n1.
          inversion contra.
          reflexivity. Qed.

    Definition eq_refl : forall x : ZXVert.Vertex,
      x = x.
    Proof. reflexivity. Qed.

    Definition eq_sym : forall x y : ZXVert.Vertex,
      x = y -> y = x.
    Proof.
      intros; subst; auto. Qed.

    Definition eq_trans : forall x y z : ZXVert.Vertex,
      x = y -> y = z -> x = z.
    Proof. intros; subst; auto. Qed.

    Lemma lt_trans : forall x y z : ZXVert.Vertex,
      lt x y -> lt y z -> lt x z.
    Proof.
    intros [] [] []; try auto; try contradiction.
        intros [[]|] [[]|]; subst; simpl;
          try (right; assumption).
        + left.
          split; auto.
          apply (Rlt_trans r r0); assumption.
        + right.
          apply (Nat.lt_trans n n0); assumption.
        + intros [[]|] [[]|]; subst; simpl;
          try (right; assumption).
          * left.
            split; auto.
            apply (Rlt_trans r r0); assumption.
          * right.
            apply (Nat.lt_trans n n0); assumption. Defined.

    Lemma lt_not_eq : forall x y : ZXVert.Vertex,
      lt x y -> x <> y.
    Proof.
      intros x y.
      destruct x, y; try easy; intros [[H0 H]| H]; subst;
        intros contra;
        contradict H;
        inversion contra; subst.
      - apply Rlt_irrefl.
      - apply Nat.lt_irrefl.
      - apply Rlt_irrefl.
      - apply Nat.lt_irrefl. Qed.


  End OTVertex.

  Module VertexSet := FSetAVL.Make OTVertex.

End ZXG.