Require Import Coq.Vectors.Fin.
Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.Proportional.
Require Import externals.QuantumLib.VectorStates.

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

Notation "⦰" := Empty. (* \revemptyset *)
Notation "⊂" := Cap. (* \subset *)
Notation "⊃" := Cup. (* \supset *)
Infix "⟷" := Compose (left associativity, at level 40). (* \longleftrightarrow *)
Infix "↕" := Stack (left associativity, at level 40). (* \updownarrow *)

(* TODO: Move into quantum lib *)
Hint Rewrite Mscale_kron_dist_l Mscale_kron_dist_r Mscale_mult_dist_l Mscale_mult_dist_r Mscale_assoc : scalar_move_db.

Definition Z_semantics (n m : nat) (α : R) : Matrix (2 ^ m) (2 ^ n) :=
  fun x y =>
  match x =? 0, y =? 0 with
  | true, true => match n =? 0, m =? 0 with
                  | true, true => C1 + Cexp α
                  | _, _  => C1
                  end
  | _, _  => match x =? (2 ^ m) - 1, y =? (2 ^ n) - 1 with
                  | true, true => Cexp α
                  | _, _  => C0
                  end
  end.

Lemma Z_semantics_transpose (n m : nat) (α : R) : (Z_semantics n m α) ⊤ = Z_semantics m n α.
Proof.
  unfold Z_semantics.
  unfold transpose.
  prep_matrix_equality.
  destruct (x =? 0);destruct (y =? 0); destruct (x =? 2 ^ n - 1); destruct (y =? 2 ^ m - 1); try reflexivity.
Qed.

Lemma Z_semantics_adj (n m : nat) (α : R) : (Z_semantics n m α) † = Z_semantics m n (- α).
Proof.
  unfold Z_semantics.
  unfold adjoint.
  prep_matrix_equality.
  destruct (x =? 0);destruct (y =? 0); destruct (x =? 2 ^ n - 1); destruct (y =? 2 ^ m - 1); 
    try lca;
    try (rewrite Cexp_conj_neg; reflexivity).
  rewrite Cconj_plus_distr.
  rewrite Cexp_conj_neg.
  lca.
Qed.

Lemma WF_Z_semantics {n m : nat} {α : R} : WF_Matrix (Z_semantics n m α).
Proof.
  unfold WF_Matrix.
  intros.
  assert ( GeqToEqb : forall (a b c : nat), b <= a  -> c < b -> a =? c = false ).
  {
    intros.
    apply Nat.eqb_neq.
    apply not_eq_sym.
    apply (Nat.lt_neq c a).
    apply (Nat.lt_le_trans c b a); assumption.
  }
  assert ( geq_symm : forall (a b : nat), a >= b -> b <= a).
  {
    induction a.
    - intros.
      inversion H0.
      reflexivity.
    - intros.
      inversion H0; try reflexivity.
      apply (Nat.le_le_succ_r _ _ H2).
  }
  assert ( expgt : forall a : nat, 2 ^ a - 1 < 2 ^ a).
  {
    intros.
    induction a.
    - constructor.
    - simpl.
      lia.
  }
  destruct H as [Hx | Hy].
  - unfold Z_semantics.
    rewrite (GeqToEqb x (2^m)%nat 0).
    + rewrite (GeqToEqb x (2^m)%nat (2^m-1)%nat).
      * reflexivity.
      * apply geq_symm; assumption.
      * apply expgt.
    + apply geq_symm.
      assumption.
    + apply pow_positive; easy.
  - unfold Z_semantics.
    destruct (x =? 0).
    + rewrite (GeqToEqb y (2^n)%nat 0).
      * destruct (x =? 2 ^ m - 1).
        -- rewrite (GeqToEqb y (2^n)%nat (2^n-1)%nat).
           ++ reflexivity.
           ++ apply geq_symm; assumption.
           ++ apply expgt.
        -- reflexivity.
      * apply geq_symm; assumption.
      * apply pow_positive; easy.
    + rewrite (GeqToEqb y (2^n)%nat (2^n - 1)%nat).
      * destruct (x =? 2 ^ m - 1); reflexivity.
      * apply geq_symm; assumption.
      * easy.
Qed.

Global Hint Resolve WF_Z_semantics : wf_db.

Definition X_semantics (n m : nat) (α : R) : Matrix (2 ^ m) (2 ^ n) :=
  (m ⨂ hadamard) × (Z_semantics n m α) × (n ⨂ hadamard).

Lemma X_semantics_transpose (n m : nat) (α : R) : (X_semantics n m α) ⊤ = X_semantics m n α.
Proof.
  unfold X_semantics.
  Msimpl.
  rewrite 2 Mmult_transpose.
  rewrite 2 kron_n_transpose.
  Msimpl.
  restore_dims.
  rewrite hadamard_st.
  rewrite <- Mmult_assoc.
  rewrite Z_semantics_transpose.
  reflexivity.
Qed.

Lemma X_semantics_adj (n m : nat) (α : R) : (X_semantics n m α)† = X_semantics m n (- α).
Proof.
  unfold X_semantics.
  rewrite 2 Mmult_adjoint.
  rewrite <- Mmult_assoc.
  rewrite Z_semantics_adj.
  rewrite 2 kron_n_adjoint; try auto with wf_db.
  rewrite hadamard_sa.
  reflexivity.
Qed.

Lemma WF_X_semantics {n m : nat} {α : R} : WF_Matrix (X_semantics n m α).
Proof.
  unfold X_semantics.
  auto with wf_db.
Qed.

Global Hint Resolve WF_X_semantics : wf_db.

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
  | ⦰ => I 1
  | X_Spider _ _ α => X_semantics nIn nOut α
  | Z_Spider _ _ α => Z_semantics nIn nOut α
  | ⊃ => list2D_to_matrix [[C1;C0;C0;C1]]
  | ⊂ => list2D_to_matrix [[C1];[C0];[C0];[C1]]  
  | zx0 ↕ zx1 => (ZX_semantics zx0) ⊗ (ZX_semantics zx1)
  | zx0 ⟷ zx1 => (ZX_semantics zx1) × (ZX_semantics zx0)
  end.

Ltac unfold_spider := unfold X_semantics, Z_semantics.

Ltac ZXunfold := simpl; Msimpl; unfold_spider; restore_dims.

Theorem WF_ZX : forall nIn nOut (zx : ZX nIn nOut), WF_Matrix (ZX_semantics zx).
Proof.
  intros.
  induction zx; try (simpl; auto 10 with wf_db);
  try (simpl; auto 10 with wf_db);
    apply WF_list2D_to_matrix;
    try easy; (* case list of length 4 *)
    try intros; simpl in H; repeat destruct H; try discriminate; try (subst; easy). (* Case of 4 lists length 1 *)
Qed.


Definition bra_ket_MN (bra: Matrix 1 2) (ket : Vector 2) {n m} : Matrix (2 ^ m) (2 ^ n) := 
  (m ⨂ ket) × (n ⨂ bra).
Transparent bra_ket_MN. 

Lemma WF_bra_ket_MN : forall n m bra ket, WF_Matrix bra -> WF_Matrix ket -> WF_Matrix (@bra_ket_MN bra ket n m).
Proof.
  intros.
  unfold bra_ket_MN.
  apply WF_mult; restore_dims; apply WF_kron_n; assumption.
Qed.

Definition Dirac_spider_semantics (bra0 bra1 : Matrix 1 2) (ket0 ket1 : Vector 2) (α : R) {n m : nat} : Matrix (2 ^ m) (2 ^ n) :=
  (bra_ket_MN bra0 ket0) .+ (Cexp α) .* (bra_ket_MN bra1 ket1). 
Local Transparent Dirac_spider_semantics.

Lemma WF_Dirac_Spider_semantics : forall n m bra0 bra1 ket0 ket1 α, 
                                WF_Matrix bra0 -> WF_Matrix bra1 -> WF_Matrix ket0 -> WF_Matrix ket1 -> 
                                WF_Matrix (@Dirac_spider_semantics bra0 bra1 ket0 ket1 α n m).
Proof.
  intros.
  unfold Dirac_spider_semantics.
  apply WF_plus; restore_dims; try apply WF_scale; apply WF_bra_ket_MN; assumption.
Qed.

Global Hint Resolve WF_Dirac_Spider_semantics WF_bra_ket_MN : wf_db.

Fixpoint ZX_Dirac_semantics {nIn nOut} (zx : ZX nIn nOut) : 
  Matrix (2 ^ nOut) (2 ^nIn) := 
  match zx with
  | ⦰ => I 1
  | X_Spider _ _ α => Dirac_spider_semantics (hadamard × (ket 0))† (hadamard × (ket 1))† (hadamard × (ket 0)) (hadamard × (ket 1)) α
  | Z_Spider _ _ α => Dirac_spider_semantics (bra 0) (bra 1) (ket 0) (ket 1) α
  | ⊃ => list2D_to_matrix [[C1;C0;C0;C1]]
  | ⊂ => list2D_to_matrix [[C1];[C0];[C0];[C1]]  
  | zx0 ↕ zx1 => (ZX_Dirac_semantics zx0) ⊗ (ZX_Dirac_semantics zx1)
  | zx0 ⟷ zx1 => (ZX_Dirac_semantics zx1) × (ZX_Dirac_semantics zx0)
  end.


Ltac unfold_dirac_spider := unfold Dirac_spider_semantics, bra_ket_MN; try (simpl; Msimpl).

Ltac ZXDiracunfold := simpl; Msimpl; unfold_spider; restore_dims.

Theorem WF_ZX_Dirac : forall nIn nOut (zx : ZX nIn nOut), WF_Matrix (ZX_Dirac_semantics zx).
Proof.
  intros.
  induction zx; try (simpl; auto 10 with wf_db);
  try (simpl; auto 10 with wf_db);
    apply WF_list2D_to_matrix;
    try easy; (* case list of length 4 *)
    try intros; simpl in H; repeat destruct H; try discriminate; try (subst; easy). (* Case of 4 lists length 1 *)
Qed.

Lemma ZX_Dirac_spider_X_H_Z : forall nIn nOut α, ZX_Dirac_semantics (X_Spider nIn nOut α) = nOut ⨂ hadamard × ZX_Dirac_semantics (Z_Spider nIn nOut α) × (nIn ⨂ hadamard).
Proof.
  intros.
  unfold_dirac_spider.
  unfold_dirac_spider.
  repeat rewrite <- kron_n_mult.
  rewrite Mmult_plus_distr_l.
  rewrite Mmult_plus_distr_r.
  apply Mplus_simplify.
  - repeat rewrite Mmult_assoc. 
    rewrite hadamard_sa.
    rewrite ket2bra.
    reflexivity.
  - autorewrite with scalar_move_db.
    apply Mscale_simplify; try reflexivity.
    rewrite hadamard_sa.
    rewrite ket2bra.
    repeat rewrite Mmult_assoc.
    reflexivity.
Qed.
  
Global Hint Resolve WF_ZX_Dirac : wf_db.

Lemma ZX_Z_semantics_equiv : forall nIn nOut α, ZX_semantics (Z_Spider nIn nOut α) = ZX_Dirac_semantics (Z_Spider nIn nOut α).
Proof.
  intros.
  unfold_dirac_spider.
  unfold Z_semantics.
  unfold Dirac_spider_semantics, bra_ket_MN.
  prep_matrix_equality.
Admitted. (* TODO *)

Theorem ZX_semantics_equiv : forall {nIn nOut} (zx : ZX nIn nOut), ZX_semantics zx = ZX_Dirac_semantics zx.
Proof.
  intros.
  induction zx; try (simpl; rewrite IHzx1, IHzx2); try reflexivity.
  - rewrite ZX_Dirac_spider_X_H_Z.
    unfold ZX_semantics, X_semantics.
    rewrite <- ZX_Z_semantics_equiv.
    simpl.
    reflexivity.
  - apply ZX_Z_semantics_equiv.
Qed.


Definition Wire : ZX 1 1 := Z_Spider _ _ 0.

Notation "—" := Wire. (* \emdash *)

Theorem wire_identity_semantics : ZX_semantics — = I 2.
Proof.
  simpl.
  unfold Z_semantics.
  unfold I.
  prep_matrix_equality.
  rewrite Cexp_0.
  simpl.
  destruct x; destruct y; try reflexivity.
  - simpl.
    destruct x; reflexivity.
  - simpl.
    destruct x; destruct y; try reflexivity.
    + simpl.
      unfold Nat.ltb.
      unfold Nat.leb.
      rewrite andb_false_r.
      reflexivity.
Qed.

Global Opaque Wire.

Global Hint Resolve wire_identity_semantics : zx_sem_db.

Reserved Notation "n ⇑ zx" (at level 40). (* \Uparrow - maybe change to ⇕ (\Updownarrow) *)
Fixpoint nStack {nIn nOut} n (zx : ZX nIn nOut) : ZX (n * nIn) (n * nOut) :=
  match n with
  | 0 => ⦰
  | S n' => zx ↕ (n' ⇑ zx)
  end
  where "n ⇑ zx" := (nStack n zx).

Reserved Notation "n ↑ zx" (at level 41).
Fixpoint nStack1 n (zx : ZX 1 1) : ZX n n :=
  match n with
  | 0 => ⦰
  | S n' => zx ↕ (n' ↑ zx)
  end
  where "n ↑ zx" := (nStack1 n zx).

Lemma nStack1_n_kron : forall n (zx : ZX 1 1), ZX_semantics (n ↑ zx) = n ⨂ ZX_semantics zx.
Proof.
  intros.
  induction n.
  - unfold nStack. reflexivity.
  - simpl.
    rewrite IHn.
    restore_dims.
    rewrite <- kron_n_assoc; auto with wf_db.
Qed.

Definition nWire := fun n => n ↑ Wire.

Global Opaque nWire.

(* Definitions for transposes of ZX diagrams and a proof that its what we expect *)
Reserved Notation "zx ⊺" (at level 10). (* \intercal *)
Fixpoint Transpose {nIn nOut} (zx : ZX nIn nOut) : ZX nOut nIn :=
  match zx with
  | ⦰ => ⦰
  | Z_Spider mIn mOut α => Z_Spider mOut mIn α
  | X_Spider mIn mOut α => X_Spider mOut mIn α
  | zx1 ⟷ zx2 => (zx2 ⊺) ⟷ (zx1 ⊺)
  | zx1 ↕ zx2 => (zx1 ⊺) ↕ (zx2 ⊺)
  | ⊂ => ⊃
  | ⊃ => ⊂
  end
  where "zx ⊺" := (Transpose zx).

Fixpoint Invert_angles {nIn nOut} (zx : ZX nIn nOut) : ZX nIn nOut :=
  match zx with
  | Z_Spider mIn mOut α => Z_Spider mIn mOut (-α)
  | X_Spider mIn mOut α => X_Spider mIn mOut (-α)
  | zx1 ⟷ zx2 => (Invert_angles zx1) ⟷ (Invert_angles zx2)
  | zx1 ↕ zx2 => (Invert_angles zx1) ↕ (Invert_angles zx2)
  | other => other
  end.

Definition Adjoint {nIn nOut} (zx : ZX nIn nOut) : ZX nOut nIn := Invert_angles (zx ⊺).
Notation "zx ‡" := (Adjoint zx) (at level 10). (* \ddagger *)


Lemma ZX_semantics_Transpose_comm {nIn nOut} : forall (zx : ZX nIn nOut),
  ZX_semantics (zx ⊺) = (ZX_semantics zx) ⊤.
Proof.
  assert (Mmult_trans_dep : forall n m o p (A : Matrix n m) (B : Matrix o p), m = o -> (A × B) ⊤ = B ⊤ × A ⊤).
    {
      intros; rewrite Mmult_transpose; rewrite H in *; reflexivity.      
    }
  induction zx.
  - Msimpl.
    reflexivity.
  - simpl.
    rewrite X_semantics_transpose.
    reflexivity.
  - simpl.
    rewrite Z_semantics_transpose.
    reflexivity.
  - simpl; solve_matrix.
  - simpl; solve_matrix.
  - simpl; rewrite IHzx1, IHzx2; rewrite <- kron_transpose; reflexivity.
  - simpl; rewrite IHzx1, IHzx2; rewrite <- Mmult_transpose; reflexivity.
Qed.

Lemma ZX_semantics_Adjoint_comm {nIn nOut} : forall (zx : ZX nIn nOut),
  ZX_semantics (zx ‡) = (ZX_semantics zx) †.
Proof.
  intros.
  induction zx.
  1, 4, 5: ZXunfold; solve_matrix. (* Cap, Cup *)
  3, 4: simpl; unfold Adjoint in IHzx1; unfold Adjoint in IHzx2; rewrite IHzx1, IHzx2;
        try rewrite <- kron_adjoint; try rewrite <- Mmult_adjoint;
        reflexivity. (* Compose, Stack *)
  - simpl.
    rewrite X_semantics_adj.
    reflexivity.
  - simpl.
    rewrite Z_semantics_adj.
    reflexivity.
Qed.

Reserved Notation "⊙ zx" (at level 10). (* \odot *) 
Fixpoint ColorSwap {nIn nOut} (zx : ZX nIn nOut) : ZX nIn nOut := 
  match zx with
  | X_Spider n m α  => Z_Spider n m α
  | Z_Spider n m α  => X_Spider n m α
  | zx1 ↕ zx2   => (⊙ zx1) ↕ (⊙ zx2)
  | zx1 ⟷ zx2 => (⊙ zx1) ⟷ (⊙ zx2)
  | otherwise => otherwise
  end
  where "⊙ zx" := (ColorSwap zx).

Local Open Scope C_scope.

Lemma ZX_semantics_Colorswap_comm {nIn nOut} : forall (zx : ZX nIn nOut),
  ZX_semantics (⊙ zx) = nOut ⨂ hadamard × (ZX_semantics zx) × nIn ⨂ hadamard.
Proof.
  induction zx.
  - ZXunfold; reflexivity.
  - simpl.
    unfold X_semantics.
    rewrite <- 2 Mmult_assoc.
    rewrite kron_n_mult.
    rewrite 2 Mmult_assoc.
    rewrite kron_n_mult.
    rewrite MmultHH.
    rewrite 2 kron_n_I.
    rewrite Mmult_1_r; try auto with wf_db.
    rewrite Mmult_1_l; try auto with wf_db.
  - reflexivity.
  - solve_matrix.
  - solve_matrix.
  - simpl.
    rewrite IHzx1, IHzx2.
    rewrite 2 kron_n_m_split; try auto with wf_db.
    repeat rewrite <- kron_mixed_product.
    restore_dims.
    reflexivity.
  - simpl.
    rewrite IHzx1, IHzx2.
    rewrite Mmult_assoc.
    rewrite <- 2 Mmult_assoc with (nMid ⨂ hadamard) _ _.
    rewrite kron_n_mult.
    rewrite MmultHH.
    rewrite kron_n_I.
    rewrite Mmult_1_l; try auto with wf_db.
    repeat rewrite Mmult_assoc.
    reflexivity.
Qed.

Local Close Scope ZX_scope.
