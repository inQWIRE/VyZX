Require Export Setoid.
Require Export Morphisms.

From Coq Require Export ZArith.
Ltac Zify.zify_post_hook ::= PreOmega.Z.div_mod_to_equations.

(* Require Import PermutationAutomation. *)
From QuantumLib Require Import Matrix.

(* This file was originally MatrixExampleBase from the ViCAR examples. 
  It contains instances relating to the Setoid of mat_equiv, especially 
  proofs that many of the common operations respect this relation. 
  It also contains a redefinition of direct_sum, called direct_sum' 
  which now respects mat_equiv. *)

Open Scope matrix_scope.

Definition direct_sum' {n m o p : nat} (A : Matrix n m) (B : Matrix o p) :
  Matrix (n+o) (m+p) :=
  (fun i j => if (i <? n) && (j <? m) then A i j
  else if (¬ (i <? n) || (j <? m)) && (i <? n+o) && (j <? m+p) then B (i-n) (j-m)
  else C0)%nat.

#[export] Hint Unfold direct_sum' : U_db.

Notation "A .⊕' B" := (direct_sum' A B) 
  (at level 50, left associativity): matrix_scope.

Lemma direct_sum'_WF : forall {n m o p : nat} (A : Matrix n m) (B : Matrix o p),
  WF_Matrix (A .⊕' B).
Proof.
  intros n m o p A B i j [Hi | Hj];
  unfold direct_sum'; now bdestruct_all.
Qed.
#[export] Hint Resolve direct_sum'_WF : wf_db.

Lemma direct_sum'_eq_direct_sum : forall {n m o p : nat}
  (A : Matrix n m) (B : Matrix o p), WF_Matrix A -> WF_Matrix B ->
  A .⊕' B = A .⊕ B.
Proof.
  intros n m o p A B HA HB.
  apply mat_equiv_eq; [|apply WF_direct_sum|]; auto with wf_db.
  intros i j Hi Hj.
  unfold direct_sum, direct_sum'.
  bdestruct_all; try lia + easy;
  rewrite HA by lia; easy.
Qed.

Lemma direct_sum'_simplify_mat_equiv {n m o p} : forall (A B : Matrix n m) 
  (C D : Matrix o p), A ≡ B -> C ≡ D -> direct_sum' A C ≡ direct_sum' B D.
Proof.
  intros A B C D HAB HCD i j Hi Hj.
  unfold direct_sum'.
  bdestruct (i <? n);
  bdestruct (j <? m); simpl; [rewrite HAB | | |]; try easy.
  bdestruct_all; try lia + easy; rewrite HCD by lia; easy.
Qed.

Lemma direct_sum'_Mmult {n m o p q r} (A : Matrix n m) (B : Matrix p q)
  (C : Matrix m o) (D : Matrix q r) : 
  (A .⊕' B) × (C .⊕' D) = (A × C) .⊕' (B × D).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold direct_sum'.
  bdestruct_all; simpl.
  - unfold Mmult.
    rewrite big_sum_sum.
    rewrite Cplus_comm.
    rewrite big_sum_0_bounded by
      (intros; now bdestruct_all; Csimpl).
    Csimpl.
    apply big_sum_eq_bounded.
    intros k Hk.
    now bdestruct_all; simpl; Csimpl.
  - unfold Mmult.
    rewrite big_sum_0_bounded; [easy|].
    intros k Hk.
    now bdestruct_all; simpl; Csimpl.
  - unfold Mmult.
    rewrite big_sum_0_bounded; [easy|].
    intros k Hk.
    now bdestruct_all; simpl; Csimpl.
  - unfold Mmult.
    rewrite big_sum_sum.
    rewrite big_sum_0_bounded by
      (intros; now bdestruct_all; Csimpl).
    Csimpl.
    apply big_sum_eq_bounded.
    intros k Hk.
    bdestruct_all; simpl; Csimpl.
    do 2 f_equal; lia.
Qed.

Lemma direct_sum'_Mmult_mat_equiv {n m o p q r} 
  (A : Matrix n m) (B : Matrix p q)
  (C : Matrix m o) (D : Matrix q r) : 
  (A .⊕' B) × (C .⊕' D) ≡ (A × C) .⊕' (B × D).
Proof.
  now rewrite direct_sum'_Mmult.
Qed.

Lemma WF_Matrix_monotone {n m} (A : Matrix n m) n' m' : 
  WF_Matrix A -> (n <= n')%nat -> (m <= m')%nat -> 
  @WF_Matrix n' m' A.
Proof.
  intros Ha Hn Hm i j Hij.
  apply Ha; lia.
Qed.

Lemma WF_Matrix_if {n m} (A B : Matrix n m) (b : bool) :
  WF_Matrix A -> WF_Matrix B -> 
  WF_Matrix (if b then A else B).
Proof.
  now destruct b.
Qed.

#[export] Hint Resolve WF_Matrix_if : wf_db.

Lemma direct_sum_0_r {n m} (A : Matrix n m) o p :
  WF_Matrix A -> 
  @direct_sum' n m o p A Zero = A.
Proof.
  intros HA.
  apply mat_equiv_eq; 
  [auto with wf_db| 
   eapply WF_Matrix_monotone; auto with wf_db; lia| ].
  intros i j Hi Hj.
  unfold direct_sum', Zero.
  bdestruct_all; simpl; [easy|..];
  symmetry; apply HA; lia.
Qed.

Lemma direct_sum_Mscale {n m p q} (A : Matrix n m) 
  (B : Matrix p q) (c : C) : 
  (c .* A) .⊕' (c .* B) = c .* (A .⊕' B).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  autounfold with U_db.
  bdestruct_all; simpl; now Csimpl.
Qed.

Lemma ei_direct_sum_split n m k : 
  @e_i (n + m) k = 
  (if k <? n then 
    @e_i n k .⊕' @Zero m 0
  else 
    @Zero n 0 .⊕' @e_i m (k - n)).
Proof.
  apply mat_equiv_eq; eauto using WF_Matrix_dim_change with wf_db.
  intros i j Hi Hj.
  replace j with O by lia.
  autounfold with U_db.
  simpl.
  bdestructΩ (i <? n + m).
  bdestruct_all; easy.
Qed.



Lemma mat_equiv_sym : forall {n m : nat} (A B : Matrix n m),
  A ≡ B -> B ≡ A.
Proof.
  intros n m A B HAB i j Hi Hj.
  rewrite HAB by easy.
  easy.
Qed.

Lemma mat_equiv_trans : forall {n m : nat} (A B C : Matrix n m),
  A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  intros n m A B C HAB HBC i j Hi Hj.
  rewrite HAB, HBC by easy.
  easy.
Qed.

Add Parametric Relation {n m} : (Matrix n m) mat_equiv
  reflexivity proved by (mat_equiv_refl _ _)
  symmetry proved by (mat_equiv_sym)
  transitivity proved by (mat_equiv_trans)
  as mat_equiv_rel.

Lemma mat_equiv_eq_iff {n m} : forall (A B : Matrix n m),
  WF_Matrix A -> WF_Matrix B -> A ≡ B <-> A = B.
Proof.
  intros; split; try apply mat_equiv_eq; 
  intros; try subst A; easy.
Qed.

Lemma Mmult_simplify_mat_equiv : forall {n m o} 
  (A B : Matrix n m) (C D : Matrix m o),
  A ≡ B -> C ≡ D -> A × C ≡ B × D.
Proof.
  intros n m o A B C D HAB HCD.
  intros i j Hi Hj.
  unfold Mmult.
  apply big_sum_eq_bounded.
  intros k Hk.
  rewrite HAB, HCD by easy.
  easy.
Qed.

Add Parametric Morphism {n m o} : (@Mmult n m o)
  with signature (@mat_equiv n m) ==> (@mat_equiv m o) ==> (@mat_equiv n o)
  as mmult_mat_equiv_morph.
Proof. intros; apply Mmult_simplify_mat_equiv; easy. Qed.

Lemma kron_simplify_mat_equiv {n m o p} : forall (A B : Matrix n m) 
  (C D : Matrix o p), A ≡ B -> C ≡ D -> A ⊗ C ≡ B ⊗ D.
Proof.
  intros A B C D HAB HCD i j Hi Hj.
  unfold kron.
  rewrite HAB, HCD; try easy.
  1,2: apply Nat.mod_upper_bound; lia.
  1,2: apply Nat.div_lt_upper_bound; lia.
Qed.

Add Parametric Morphism {n m o p} : (@kron n m o p) 
  with signature (@mat_equiv n m) ==> (@mat_equiv o p) 
    ==> (@mat_equiv (n*o) (m*p)) as kron_mat_equiv_morph.
Proof. intros; apply kron_simplify_mat_equiv; easy. Qed.

Lemma Mplus_simplify_mat_equiv : forall {n m} 
  (A B C D : Matrix n m),
  A ≡ B -> C ≡ D -> A .+ C ≡ B .+ D.
Proof.
  intros n m A B C D HAB HCD. 
  intros i j Hi Hj; unfold ".+"; 
  rewrite HAB, HCD; try easy. 
Qed.

Add Parametric Morphism {n m} : (@Mplus n m)
  with signature (@mat_equiv n m) ==> (@mat_equiv n m) ==> (@mat_equiv n m)
  as Mplus_mat_equiv_morph.
Proof. intros; apply Mplus_simplify_mat_equiv; easy. Qed.

Lemma scale_simplify_mat_equiv : forall {n m} 
  (x y : C) (A B : Matrix n m), 
  x = y -> A ≡ B -> x .* A ≡ y .* B.
Proof.
  intros n m x y A B Hxy HAB i j Hi Hj.
  unfold scale.
  rewrite Hxy, HAB; easy.
Qed.

Add Parametric Morphism {n m} : (@scale n m)
  with signature (@eq C) ==> (@mat_equiv n m) ==> (@mat_equiv n m)
  as scale_mat_equiv_morph.
Proof. intros; apply scale_simplify_mat_equiv; easy. Qed.

Lemma Mopp_simplify_mat_equiv : forall {n m} (A B : Matrix n m), 
  A ≡ B -> Mopp A ≡ Mopp B.
Proof.
  intros n m A B HAB i j Hi Hj.
  unfold Mopp, scale.
  rewrite HAB; easy.
Qed.

Add Parametric Morphism {n m} : (@Mopp n m)
  with signature (@mat_equiv n m) ==> (@mat_equiv n m)
  as Mopp_mat_equiv_morph.
Proof. intros; apply Mopp_simplify_mat_equiv; easy. Qed.

Lemma Mminus_simplify_mat_equiv : forall {n m} 
  (A B C D : Matrix n m),
  A ≡ B -> C ≡ D -> Mminus A C ≡ Mminus B D.
Proof.
  intros n m A B C D HAB HCD. 
  intros i j Hi Hj; unfold Mminus, Mopp, Mplus, scale;
  rewrite HAB, HCD; try easy. 
Qed.

Add Parametric Morphism {n m} : (@Mminus n m)
  with signature (@mat_equiv n m) ==> (@mat_equiv n m) ==> (@mat_equiv n m)
  as Mminus_mat_equiv_morph.
Proof. intros; apply Mminus_simplify_mat_equiv; easy. Qed.

Lemma dot_simplify_mat_equiv : forall {n} (A B : Vector n) 
  (C D : Vector n), A ≡ B -> C ≡ D -> dot A C = dot B D.
Proof.
  intros n A B C D HAB HCD.
  apply big_sum_eq_bounded.
  intros k Hk.
  rewrite HAB, HCD; unfold "<"%nat; easy.
Qed.

Add Parametric Morphism {n} : (@dot n)
  with signature (@mat_equiv n 1) ==> (@mat_equiv n 1) ==> (@eq C)
  as dot_mat_equiv_morph.
Proof. intros; apply dot_simplify_mat_equiv; easy. Qed.

Add Parametric Morphism {n m o p} : (@direct_sum' n m o p) 
  with signature (@mat_equiv n m) ==> (@mat_equiv o p) 
    ==> (@mat_equiv (n+o) (m+p)) as direct_sum'_mat_equiv_morph.
Proof. intros; apply direct_sum'_simplify_mat_equiv; easy. Qed.

(* Search (Matrix ?n ?m -> ?Matrix ?n ?m). *)
Lemma transpose_simplify_mat_equiv {n m} : forall (A B : Matrix n m),
  A ≡ B -> A ⊤ ≡ B ⊤.
Proof.
  intros A B HAB i j Hi Hj.
  unfold transpose; auto.
Qed.

Lemma transpose_simplify_mat_equiv_inv {n m} : forall (A B : Matrix n m),
  A ⊤ ≡ B ⊤ -> A ≡ B.
Proof. 
  intros A B HAB i j Hi Hj.
  unfold transpose in *; auto.
Qed.

Add Parametric Morphism {n m} : (@transpose n m)
  with signature (@mat_equiv n m) ==> (@mat_equiv m n)
  as transpose_mat_equiv_morph.
Proof. intros; apply transpose_simplify_mat_equiv; easy. Qed.

Lemma adjoint_simplify_mat_equiv {n m} : forall (A B : Matrix n m),
  A ≡ B -> A † ≡ B †.
Proof.
  intros A B HAB i j Hi Hj.
  unfold adjoint;
  rewrite HAB by easy; easy.
Qed.

Add Parametric Morphism {n m} : (@adjoint n m)
  with signature (@mat_equiv n m) ==> (@mat_equiv m n)
  as adjoint_mat_equiv_morph.
Proof. intros; apply adjoint_simplify_mat_equiv; easy. Qed.

Lemma trace_of_mat_equiv : forall n (A B : Square n),
  A ≡ B -> trace A = trace B.
Proof.
  intros n A B HAB.
  (* unfold trace. *)
  apply big_sum_eq_bounded; intros i Hi.
  rewrite HAB; auto.
Qed.

Add Parametric Morphism {n} : (@trace n)
  with signature (@mat_equiv n n) ==> (eq)
  as trace_mat_equiv_morph.
Proof. intros; apply trace_of_mat_equiv; easy. Qed.


Lemma Mmult_assoc_mat_equiv : forall {n m o p}
  (A : Matrix n m) (B : Matrix m o) (C : Matrix o p),
  A × B × C ≡ A × (B × C).
Proof.
  intros n m o p A B C.
  rewrite Mmult_assoc.
  easy.
Qed.

Lemma mat_equiv_equivalence : forall {n m}, 
  equivalence (Matrix n m) mat_equiv.
Proof.
  intros n m.
  constructor.
  - intros A. apply (mat_equiv_refl).
  - intros A; apply mat_equiv_trans.
  - intros A; apply mat_equiv_sym.
Qed.



Lemma big_sum_mat_equiv : forall {o p} (f g : nat -> Matrix o p)
  (Eq_on: forall x : nat, f x ≡ g x) (n : nat), big_sum f n ≡ big_sum g n.
Proof.
  intros o p f g Eq_on n.
  induction n.
  - easy.
  - simpl.
    rewrite IHn, Eq_on; easy.
Qed.

Add Parametric Morphism {n m} : (@big_sum (Matrix n m) (M_is_monoid n m))
  with signature 
  (pointwise_relation nat (@mat_equiv n m)) ==> (@eq nat) ==> 
  (@mat_equiv n m)
  as big_sum_mat_equiv_morph.
Proof. intros f g Eq_on k. apply big_sum_mat_equiv; easy. Qed.