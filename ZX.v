Require Import Coq.Vectors.Fin.
Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.Proportional.

Declare Scope ZX_scope.
Local Open Scope ZX_scope.

Local Open Scope R_scope.
Inductive ZX : nat -> nat -> Type :=
  | Empty : ZX 0 0
  | X_Spider nIn nOut (α : R) : ZX nIn nOut
  | Z_Spider nIn nOut (α : R) : ZX nIn nOut
  | Cap : ZX 0 2
  | Cup : ZX 2 0
  | Stack {nIn0 nIn1 nOut0 nOut1} (zx0 : ZX nIn0 nOut0) (zx1 : ZX nIn1 nOut1) :
      ZX (nIn0 + nIn1) (nOut0 + nOut1)
  | Compose {nIn nMid nOut} (zx0 : ZX nIn nMid) (zx1 : ZX nMid nOut) : ZX nIn nOut.
Local Close Scope R_scope.

Definition bra_ket_MN (bra: Matrix 1 2) (ket : Vector 2) {n m} : Matrix (2 ^ m) (2 ^ n) := 
  (m ⨂ ket) × (n ⨂ bra).
Transparent bra_ket_MN. 

Lemma WF_bra_ket_MN : forall n m bra ket, WF_Matrix bra -> WF_Matrix ket -> WF_Matrix (@bra_ket_MN bra ket n m).
Proof.
  intros.
  unfold bra_ket_MN.
  apply WF_mult; restore_dims; apply WF_kron_n; assumption.
Qed.

Definition Spider_semantics (bra0 bra1 : Matrix 1 2) (ket0 ket1 : Vector 2) (α : R) {n m : nat} : Matrix (2 ^ m) (2 ^ n) :=
  (bra_ket_MN bra0 ket0) .+ (Cexp α) .* (bra_ket_MN bra1 ket1). 
Transparent Spider_semantics.

Lemma WF_Spider_semantics : forall n m bra0 bra1 ket0 ket1 α, 
                                WF_Matrix bra0 -> WF_Matrix bra1 -> WF_Matrix ket0 -> WF_Matrix ket1 -> 
                                WF_Matrix (@Spider_semantics bra0 bra1 ket0 ket1 α n m).
Proof.
  intros.
  unfold Spider_semantics.
  apply WF_plus; restore_dims; try apply WF_scale; apply WF_bra_ket_MN; assumption.
Qed.

Global Hint Resolve WF_Spider_semantics WF_bra_ket_MN : wf_db.

Fixpoint ZX_semantics {nIn nOut} (zx : ZX nIn nOut) : 
  Matrix (2 ^ nOut) (2 ^nIn) := 
  match zx with
  | Empty => I 1
  | X_Spider _ _ α => Spider_semantics (hadamard × (ket 0))† (hadamard × (ket 1))† (hadamard × (ket 0)) (hadamard × (ket 1)) α
  | Z_Spider _ _ α => Spider_semantics (bra 0) (bra 1) (ket 0) (ket 1) α
  | Cup => list2D_to_matrix [[C1;C0;C0;C1]]
  | Cap => list2D_to_matrix [[C1];[C0];[C0];[C1]]  
  | Stack zx0 zx1 => (ZX_semantics zx0) ⊗ (ZX_semantics zx1)
  | Compose zx0 zx1 => (ZX_semantics zx1) × (ZX_semantics zx0)
  end.

Ltac unfold_spider := unfold Spider_semantics, bra_ket_MN; try (simpl; Msimpl).

Theorem WF_ZX : forall nIn nOut (zx : ZX nIn nOut), WF_Matrix (ZX_semantics zx).
Proof.
  intros.
  induction zx; try (simpl; auto 10 with wf_db);
    apply WF_list2D_to_matrix;
    try easy; (* case list of length 4 *)
    try intros; simpl in H; repeat destruct H; try discriminate; try (subst; easy). (* Case of 4 lists length 1 *)
Qed.

Global Hint Resolve WF_ZX : wf_db.

Definition Wire : ZX 1 1 := Z_Spider _ _ 0.

Theorem wire_identity_semantics : ZX_semantics Wire = I 2.
Proof.
  simpl.
  unfold_spider.
  autorewrite with Cexp_db.
  rewrite Mscale_1_l.
  unfold kron_n.
  repeat rewrite kron_1_l; try auto with wf_db.
  solve_matrix.
Qed.

Global Opaque Wire.

Global Hint Resolve wire_identity_semantics : zx_sem_db.

Fixpoint nStack {nIn nOut} n (zx : ZX nIn nOut) : ZX (n * nIn) (n * nOut) :=
  match n with
  | 0 => Empty
  | S n' => Stack zx (nStack n' zx)
  end.

Fixpoint nStack1 n (zx : ZX 1 1) : ZX n n :=
  match n with
  | 0 => Empty
  | S n' => Stack zx (nStack1 n' zx)
  end.

Lemma nStack1_n_kron : forall n (zx : ZX 1 1), ZX_semantics (nStack1 n zx) = n ⨂ ZX_semantics zx.
Proof.
  intros.
  induction n.
  - unfold nStack. reflexivity.
  - simpl.
    rewrite IHn.
    rewrite <- kron_n_assoc; auto with wf_db.
Qed.

Definition nWire := fun n => nStack1 n Wire.

Global Opaque nWire.

Fixpoint Transpose {nIn nOut} (zx : ZX nIn nOut) : ZX nOut nIn :=
  match zx with
  | Empty => Empty
  | Z_Spider mIn mOut α => Z_Spider mOut mIn α
  | X_Spider mIn mOut α => X_Spider mOut mIn α
  | Compose zx1 zx2     => Compose (Transpose zx2) (Transpose zx1)
  | Stack zx1 zx2       => Stack (Transpose zx1) (Transpose zx2)
  | Cap                 => Cup
  | Cup                 => Cap
  end.

Lemma hadamard_self_transpose : hadamard ⊤ = hadamard.
Proof. solve_matrix. Qed.

Lemma ket0_transpose_bra0 : (ket 0) ⊤ = bra 0.
Proof. solve_matrix. Qed.

Lemma ket1_transpose_bra1 : (ket 1) ⊤ = bra 1.
Proof. solve_matrix. Qed.

Lemma bra0_transpose_ket0 : (bra 0) ⊤ = ket 0.
Proof. solve_matrix. Qed.

Lemma bra1_transpose_ket1 : (bra 1) ⊤ = ket 1.
Proof. solve_matrix. Qed.

Lemma bra1_adjoint_ket1 : (bra 1) † = ket 1.
Proof. solve_matrix. Qed.

Lemma ket1_adjoint_bra1 : (ket 1) † = bra 1.
Proof. solve_matrix. Qed.

Lemma bra0_adjoint_ket0 : (bra 0) † = ket 0.
Proof. solve_matrix. Qed.

Lemma ket0_adjoint_bra0 : (ket 0) † = bra 0.
Proof. solve_matrix. Qed.

Lemma kron_n_transpose : forall (m n o : nat) (A : Matrix m n),
  (o ⨂ A)⊤ = o ⨂ (A⊤). 
Proof. 
  induction o; intros.
  - apply id_transpose_eq.
  - simpl; rewrite <- IHo; rewrite <- kron_transpose; reflexivity. 
Qed.

Lemma adjoint_transpose_comm : forall m n (A : Matrix m n),
  A † ⊤ = A ⊤ †.
Proof. reflexivity. Qed.

Lemma Mmult_trans {n m o p} : forall (A : Matrix n m) (B : Matrix o p),
  m = o -> (A × B) ⊤ = B ⊤ × A ⊤.
Proof.
  intros.
  rewrite Mmult_transpose.
  rewrite H in *.
  reflexivity.
Qed.

Lemma ZX_semantics_Transpose_comm {nIn nOut} : forall (zx : ZX nIn nOut),
  ZX_semantics (Transpose zx) = (ZX_semantics zx)⊤.
Proof.
  assert (Mmult_trans_dep : forall n m o p (A : Matrix n m) (B : Matrix o p), m = o -> (A × B) ⊤ = B ⊤ × A ⊤).
    {
      intros; rewrite Mmult_transpose; rewrite H in *; reflexivity.      
    }
  induction zx.
  - Msimpl.
    reflexivity.
  - simpl.
    unfold_spider.
    rewrite Mplus_transpose.
    rewrite Mscale_trans.
    rewrite 2 Mmult_trans_dep; try (repeat rewrite Nat.pow_1_l; reflexivity).
    repeat rewrite kron_n_transpose.
    repeat rewrite Mmult_transpose.
    repeat rewrite adjoint_transpose_comm.
    repeat rewrite hadamard_self_transpose.
    repeat rewrite hadamard_sa.
    rewrite ket0_transpose_bra0.
    rewrite ket1_transpose_bra1.
    rewrite bra1_adjoint_ket1.
    rewrite ket1_adjoint_bra1.
    rewrite bra0_adjoint_ket0.
    rewrite ket0_adjoint_bra0.
    reflexivity.
  - simpl.
    unfold_spider.
    rewrite Mplus_transpose.
    rewrite Mscale_trans.
    rewrite 2 Mmult_trans_dep; try (repeat rewrite Nat.pow_1_l; reflexivity).
    repeat rewrite kron_n_transpose.
    repeat rewrite Mmult_transpose.
    rewrite ket0_transpose_bra0.
    rewrite ket1_transpose_bra1.
    rewrite bra1_transpose_ket1.
    rewrite bra0_transpose_ket0.
    reflexivity.
  - simpl; solve_matrix.
  - simpl; solve_matrix.
  - simpl. rewrite IHzx1. rewrite IHzx2. restore_dims. rewrite <- kron_transpose. reflexivity.
  - simpl. rewrite IHzx1. rewrite IHzx2. restore_dims. rewrite <- Mmult_transpose. reflexivity.
Qed.

Local Close Scope ZX_scope.
