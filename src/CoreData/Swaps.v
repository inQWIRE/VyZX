Require Import ZXCore.
Require Import StrongInduction.
Require Export QuantumLib.Quantum.
Require Export QuantumLib.Permutations.

Open Scope ZX_scope.

Fixpoint top_to_bottom_helper (n : nat) : ZX (S n) (S n) :=
  match n with 
  | 0   => Wire
  | S k => Compose (Stack Swap (n_wire k)) (Stack Wire (top_to_bottom_helper k))
  end.

Definition top_to_bottom (n : nat) : ZX n n :=
  match n with
  | 0 => Empty
  | S k => top_to_bottom_helper k
  end.

Definition bottom_to_top (n : nat) : ZX n n :=
  (top_to_bottom n)⊤.

Definition a_swap (n : nat) : ZX n n :=
  match n with
  | 0   => Empty
  | S k => bottom_to_top (S k) ⟷ (— ↕ top_to_bottom k)
  end.

(* Arbitrary Swap Semantics *)

(* A linear mapping which takes | x y1 ... yn > -> | y1 .. yn x > *)
Fixpoint top_wire_to_bottom (n : nat) : Square (2 ^ n) :=
  match n with
  | 0   => I 1
  | S k => match k with
           | 0   => I 2
           | S j => (@Mmult _ (2^n) _) ((I 2) ⊗ (top_wire_to_bottom k)) (swap ⊗ (j ⨂ (I 2)))
           end
  end.

Open Scope matrix_scope.
Definition bottom_wire_to_top (n : nat) : Square (2 ^ n) :=
  (top_wire_to_bottom n)⊤.

(* Well foundedness of semantics *)

Lemma WF_top_to_bottom (n : nat) : WF_Matrix (top_wire_to_bottom n).
Proof.
  destruct n; try auto with wf_db.
  induction n.
  - simpl; auto with wf_db.
  - simpl. try auto with wf_db.
Qed.

Global Hint Resolve WF_top_to_bottom : wf_db.

Lemma WF_bottom_to_top (n : nat) : WF_Matrix (bottom_wire_to_top n).
Proof. unfold bottom_wire_to_top. auto with wf_db. Qed.

Global Hint Resolve WF_bottom_to_top : wf_db.

Definition a_swap_semantics (n : nat) : Square (2 ^ n) :=
  match n with
  | 0   => I 1
  | S k => (@Mmult _ (2 ^ n) _ ((I 2) ⊗ top_wire_to_bottom (k)) ((bottom_wire_to_top (S k))))
  end.

Lemma WF_a_swap_semantics (n : nat) :
  WF_Matrix (a_swap_semantics n).
Proof.
  intros.
  unfold a_swap_semantics.
  destruct n; auto with wf_db.
Qed.
 
Global Hint Resolve WF_a_swap_semantics : wf_db.

Fixpoint n_swap (n : nat) : ZX n n :=
  match n with
  | 0 => ⦰
  | (S n) => bottom_to_top (S n) ⟷ (— ↕ n_swap n)
  end.
  
Fixpoint n_swap_mat_ind (n : nat) : Matrix (2 ^ n) (2 ^ n) :=
  match n with
  | 0 => I 1
  | 1 => I 2
  | S (S n) => @Mmult _ (2 ^ (S (S n))) _ (((I 2) ⊗ n_swap_mat_ind n ⊗ (I 2))) (a_swap_semantics (S (S n)))
  end.

Lemma WF_n_swap_mat_ind : forall n, WF_Matrix (n_swap_mat_ind n).
Proof.
  intros.
  strong induction n.
  do 2 (destruct n; [ simpl; auto with wf_db | ]).
  assert (n < (S (S n)))%nat by lia.
  specialize (H n H0); clear H0.
  simpl.
  destruct n.
  apply WF_mult.
  + apply WF_kron; try lia.
    apply WF_kron; try lia.
    1-3: auto with wf_db.
  + apply WF_mult; [ auto with wf_db | ].
    replace (2 ^ 0 + (2 ^ 0 + 0) + (2 ^ 0 + (2 ^ 0 + 0) + 0))%nat with (2 ^ 2)%nat by (simpl; lia).
    auto with wf_db.
  + apply WF_mult; auto with wf_db.
    apply WF_mult; auto with wf_db.
    replace (2 ^ S n + (2 ^ S n + 0) + (2 ^ S n + (2 ^ S n + 0) + 0))%nat with (2 ^ (S (S (S n))))%nat by (simpl; lia).
    auto with wf_db.
Qed.

Fixpoint n_swap_mat (n : nat) : Matrix (2 ^ n) (2 ^ n) :=
  match n with
  | 0 => I 1
  | (S n) => (I 2 ⊗ (n_swap_mat n)) × bottom_wire_to_top (S n)
  end.
  
Lemma WF_n_swap_mat : forall n, WF_Matrix (n_swap_mat n).
Proof. 
  intros.
  induction n; try auto with wf_db.
  simpl.
  unfold bottom_wire_to_top.
  auto with wf_db.
Qed.

    