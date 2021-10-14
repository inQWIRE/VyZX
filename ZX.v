Require Import Coq.Vectors.Fin.
Require Import externals.QuantumLib.Quantum.

Definition permutation (n : nat) := list((Fin.t n) * (Fin.t n)).

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
     (zx1 : ZX nMid nOut) : ZX nIn nOut.
Local Close Scope R_scope.

Definition bra_ket_NM (bra: Matrix 1 2) (ket : Vector 2) {n m} : Matrix (2 ^ n) (2 ^ m) := 
  (n ⨂ ket) × (m ⨂ bra).
Transparent bra_ket_NM. 

Definition Spider_Semantics_Impl (bra0 bra1 : Matrix 1 2) (ket0 ket1 : Vector 2) (α : R) {n m : nat} : Matrix (2 ^ n) (2 ^ m) :=
  (bra_ket_NM bra0 ket0) .+ (Cexp α) .* (bra_ket_NM bra1 ket1). 
Transparent Spider_Semantics_Impl.

Fixpoint ZX_semantics {nIn nOut} (zx : ZX nIn nOut) : Matrix (2 ^ nIn) (2 ^ nOut) := 
  match zx with
  | Wire => I 2
  | X_Spider α => Spider_Semantics_Impl (hadamard × (ket 0))† (hadamard × (ket 1))† (hadamard × (ket 0)) (hadamard × (ket 1)) α
  | Z_Spider α => Spider_Semantics_Impl (bra 0) (bra 1) (ket 0) (ket 1) α
  | Cap => list2D_to_matrix [[C1;C0;C0;C1]]
  | Cup => list2D_to_matrix [[C1];[C0];[C0];[C1]]  
  | Stack zx0 zx1 => (ZX_semantics zx0) ⊗ (ZX_semantics zx1)
  | Compose zx0 σ zx1 => (ZX_semantics zx0) × (perm_to_mat σ) × (ZX_semantics zx1)
  end.
  
Theorem WF_ZX : forall nIn nOut (zx : ZX nIn nOut), WF_Matrix (ZX_semantics zx).
Proof.
  intros.
  induction zx; try (simpl; auto 10 with wf_db).
  - unfold Spider_Semantics_Impl, bra_ket_NM; try apply WF_plus; try apply WF_scale; apply WF_mult; try restore_dims; try auto with wf_db.
  - unfold Spider_Semantics_Impl, bra_ket_NM; try apply WF_plus; try apply WF_scale; apply WF_mult; try restore_dims; try auto with wf_db.
  - apply WF_list2D_to_matrix.
    + easy.
    + intros.
      simpl in H; destruct H; try discriminate; try (subst; easy).
  - apply WF_list2D_to_matrix.
    + easy.
    + intros.
      simpl in H; repeat destruct H; try discriminate; try (subst; easy).
Qed.
