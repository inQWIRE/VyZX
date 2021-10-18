Require Import Coq.Vectors.Fin.
Require Import externals.QuantumLib.Quantum.

Definition permutation (n : nat) := list((Fin.t n) * (Fin.t n)).

Definition trivial_permutation n : permutation n := [].

Definition perm_to_mat {n} (σ : permutation n) : Square (2 ^ n) := I (2 ^ n) (*TODO*).

Theorem WF_permutation : forall n (σ : permutation n), WF_Matrix (perm_to_mat σ).
Proof.
  intros.
  apply WF_I. 
Qed.

Global Hint Resolve WF_permutation : wf_db.


Local Open Scope R_scope.
Inductive ZX : nat -> nat -> Type :=
  | Wire : ZX 1 1
  | X_Spider {nIn nOut} (α : R) : ZX nIn nOut
  | Z_Spider {nIn nOut} (α : R) : ZX nIn nOut
  | Cap : ZX 0 2
  | Cup : ZX 2 0
  | Stack {nIn0 nIn1 nOut0 nOut1} (zx0 : ZX nIn0 nOut0) (zx1 : ZX nIn1 nOut1) :
      ZX (nIn0 + nIn1) (nOut0 + nOut1)
  | Compose {nIn nMid nOut} (zx0 : ZX nIn nMid) (σ : permutation nMid) 
     (zx1 : ZX nMid nOut) : ZX nIn nOut
  | Scale {nIn nOut} (c : C) (zx : ZX nIn nOut) : ZX nIn nOut.
Local Close Scope R_scope.

Definition Direct_Compose {nIn nMid nOut} (zx0 : ZX nIn nMid) (zx1 : ZX nMid nOut) := Compose zx0 (trivial_permutation nMid) zx1.

Definition bra_ket_MN (bra: Matrix 1 2) (ket : Vector 2) {n m} : Matrix (2 ^ m) (2 ^ n) := 
  (m ⨂ ket) × (n ⨂ bra).
Transparent bra_ket_MN. 

Definition Spider_Semantics_Impl (bra0 bra1 : Matrix 1 2) (ket0 ket1 : Vector 2) (α : R) {n m : nat} : Matrix (2 ^ m) (2 ^ n) :=
  (bra_ket_MN bra0 ket0) .+ (Cexp α) .* (bra_ket_MN bra1 ket1). 
Transparent Spider_Semantics_Impl.

Fixpoint ZX_semantics {nIn nOut} (zx : ZX nIn nOut) : Matrix (2 ^ nOut) (2 ^ nIn) := 
  match zx with
  | Wire => I 2
  | X_Spider α => Spider_Semantics_Impl (hadamard × (ket 0))† (hadamard × (ket 1))† (hadamard × (ket 0)) (hadamard × (ket 1)) α
  | Z_Spider α => Spider_Semantics_Impl (bra 0) (bra 1) (ket 0) (ket 1) α
  | Cup => list2D_to_matrix [[C1;C0;C0;C1]]
  | Cap => list2D_to_matrix [[C1];[C0];[C0];[C1]]  
  | Stack zx0 zx1 => (ZX_semantics zx0) ⊗ (ZX_semantics zx1)
  | Compose zx0 σ zx1 => (ZX_semantics zx1) × (perm_to_mat σ) × (ZX_semantics zx0)
  | Scale c zx => c .*  (ZX_semantics zx)
  end.
  
Theorem WF_ZX : forall nIn nOut (zx : ZX nIn nOut), WF_Matrix (ZX_semantics zx).
Proof.
  intros.
  induction zx; try (simpl; auto 10 with wf_db).
  - unfold Spider_Semantics_Impl, bra_ket_MN; try apply WF_plus; try apply WF_scale; apply WF_mult; try restore_dims; try auto with wf_db.
  - unfold Spider_Semantics_Impl, bra_ket_MN; try apply WF_plus; try apply WF_scale; apply WF_mult; try restore_dims; try auto with wf_db.
  - apply WF_list2D_to_matrix.
    + easy.
    + intros.
      simpl in H; repeat destruct H; try discriminate; try (subst; easy).
  - apply WF_list2D_to_matrix.
    + easy.
    + intros.
      simpl in H; destruct H; try discriminate; try (subst; easy).
Qed.

Global Hint Resolve WF_ZX : wf_db.

Lemma wire_stack_identity : ZX_semantics (Stack Wire Wire) = I 4.
Proof.
    apply id_kron.
Qed.

Definition ZX_H := Scale (Cexp (PI / 4)) (Direct_Compose (@Z_Spider 1 1 (PI/2)) (Direct_Compose (@X_Spider 1 1 (PI/2)) (@Z_Spider 1 1 (PI/2)))).

Lemma ZX_H_is_H : ZX_semantics ZX_H = hadamard.
Proof.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN, perm_to_mat.
  (* just a matter of solving C eqns*)
  admit.
Admitted.

Definition ZX_CNOT_l := Scale ((√ 2)%R) (Direct_Compose (Stack (@Z_Spider 1 2 0%R) Wire) (Stack Wire (@X_Spider 2 1 0%R))).

Lemma ZX_CNOT_is_cnot : ZX_semantics ZX_CNOT_l = cnot.
Proof.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN, perm_to_mat.
    (* just a matter of solving C eqns*) simpl.
  admit.
Admitted.

