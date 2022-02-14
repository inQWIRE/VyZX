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
  match x, y with
  | 0, 0 => match n, m with
                  | 0, 0 => C1 + Cexp α
                  | _, _  => C1
                  end
  | _, _ => if ((x =? 2^m-1) && (y =? 2^n-1)) then Cexp α else C0
  end.
(* 
bdestruct, takes a boolean equality and destructs it, reflects into context

*)


Lemma Z_semantics_transpose (n m : nat) (α : R) : (Z_semantics n m α) ⊤ = Z_semantics m n α.
Proof.
  unfold Z_semantics.
  unfold transpose.
  prep_matrix_equality.
  destruct x, y.
  - destruct n, m; reflexivity.
  - destruct (S y =? 2^m - 1), (0 =? 2^n-1); reflexivity.
  - destruct (0 =? 2^m - 1), (S x =? 2^n-1); reflexivity.
  - destruct (S y =? 2^m-1), (S x =? 2^n-1); reflexivity.
Qed.

Lemma Z_semantics_adj (n m : nat) (α : R) : (Z_semantics n m α) † = Z_semantics m n (- α).
Proof.
  unfold Z_semantics.
  unfold adjoint.
  prep_matrix_equality.
  destruct x,y. 
  - destruct n,m; try lca.
    rewrite Cconj_plus_distr.
    rewrite Cexp_conj_neg.
    lca.
  - destruct (S y =? 2^m-1), (0=?2^n-1); try lca.
    apply Cexp_conj_neg.
  - destruct (0=?2^m-1),(S x=?2^n-1); try lca.
    apply Cexp_conj_neg.
  - destruct (S y=?2^m-1),(S x=?2^n-1); try lca.
    apply Cexp_conj_neg.
Qed.

Lemma WF_Z_semantics {n m : nat} {α : R} : WF_Matrix (Z_semantics n m α).
Proof.
  unfold WF_Matrix; unfold Z_semantics.
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
      inversion H.
      reflexivity.
    - intros.
      inversion H; try reflexivity.
      apply (Nat.le_le_succ_r _ _ H1).
  }
  assert ( expgt : forall a : nat, 2 ^ a - 1 < 2 ^ a).
  {
    intros.
    induction a.
    - constructor.
    - simpl.
      lia.
  }
  intros x y [Hx | Hy].
  - destruct x,y.
    + inversion Hx.
      apply Nat.pow_nonzero in H0; [destruct H0 | lia].
    + inversion Hx.
      apply Nat.pow_nonzero in H0; [destruct H0 | lia].
    + rewrite (GeqToEqb (S x) (2^m)%nat (2^m-1)%nat); easy.
    + rewrite (GeqToEqb (S x) (2^m)%nat (2^m-1)%nat); easy.
  - destruct x,y.
    + inversion Hy.
      apply Nat.pow_nonzero in H0; [destruct H0 | lia].
    + rewrite (GeqToEqb (S y) (2^n)%nat (2^n-1)%nat); [ rewrite andb_false_r; easy | easy | easy].
    + inversion Hy.
      apply Nat.pow_nonzero in H0; [destruct H0 | lia].
    + rewrite (GeqToEqb (S y) (2^n)%nat (2^n-1)%nat); [ rewrite andb_false_r; easy | easy | easy].
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

(*
Lemma WF_Spider_semantics : forall n m bra0 bra1 ket0 ket1 α, 
                                WF_Matrix bra0 -> WF_Matrix bra1 -> WF_Matrix ket0 -> WF_Matrix ket1 -> 
                                WF_Matrix (@Spider_semantics bra0 bra1 ket0 ket1 α n m).
Proof.
  intros.
  unfold Spider_semantics.
  apply WF_plus; restore_dims; try apply WF_scale; apply WF_bra_ket_MN; assumption.
Qed.

Global Hint Resolve WF_Spider_semantics WF_bra_ket_MN : wf_db.
 *)
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

Lemma ZX_X_is_X_semantics : forall nIn nOut α, (ZX_semantics (X_Spider nIn nOut α) = X_semantics nIn nOut α).
Proof. easy. Qed.

Lemma ZX_Z_is_Z_semantics : forall nIn nOut α, (ZX_semantics (Z_Spider nIn nOut α) = Z_semantics nIn nOut α).
Proof. easy. Qed.

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

Global Hint Resolve WF_ZX : wf_db.

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


Ltac unfold_dirac_spider := simpl; unfold Dirac_spider_semantics, bra_ket_MN; try (simpl; Msimpl).

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

Definition braket_0_intermediate (n m : nat) : Matrix (2^m) (2^n) :=
  fun x y => match x, y with
             | 0, 0 => C1
             | _, _ => C0
             end.

Definition braket_1_intermediate (n m : nat) : Matrix (2^m) (2^n) :=
  fun x y => if (x =? 2^m - 1) && (y =? 2^n - 1) then C1 else C0.

Lemma Z_semantics_split_plus : forall (n m : nat) (α : R), Z_semantics n m α = (braket_0_intermediate n m) .+ Cexp α .* (braket_1_intermediate n m).
Proof.
  assert (contra : forall a, (2^S a - 1 <> 0)%nat).
  { intros; simpl. 
    destruct (2^a)%nat eqn:Ea. 
    - apply Nat.pow_nonzero in Ea; [destruct Ea | easy].
    - simpl; rewrite <- plus_n_Sm; easy.
  } 
  intros.
  unfold braket_0_intermediate; unfold braket_1_intermediate.
  unfold Z_semantics.
  unfold Mplus, scale.
  prep_matrix_equality.
  destruct x, y; simpl.
  - destruct (2^n-1)%nat eqn:En, (2^m-1)%nat eqn:Em.
    + destruct n, m; [lca | destruct (contra m Em) | | ]; destruct (contra n En).
    + destruct n, m; [discriminate | | | ]; lca.
    + destruct n, m; [discriminate | | | ]; lca.
    + destruct n, m; [discriminate | discriminate | | ]; lca.
  - destruct (2^n-1)%nat eqn:En, (2^m-1)%nat eqn:Em.
    + destruct n,m; [lca | destruct (contra m Em) | | ]; destruct (contra n En).
    + destruct n, m; [discriminate | | | ]; lca.
    + destruct n, m; [discriminate | discriminate | |]; destruct (y =? n0); lca.
    + destruct n, m; [discriminate | | | lca]; destruct (y =? n0); lca.
  - destruct (2^n-1)%nat eqn:En, (2^m-1)%nat eqn:Em; [lca | | lca | ]; destruct (_ =? _); lca.
  - destruct (2^n-1)%nat eqn:En, (2^m-1)%nat eqn:Em; [lca | | lca | ]; repeat destruct (_ =? _); lca.
Qed.

Lemma big_bra_0_0_0 : forall n, (n ⨂ (bra 0)) 0 0 = C1.
Proof.
  intros.
  induction n; [reflexivity | ].
  rewrite kron_n_assoc; [ | auto with wf_db].
  unfold kron.
  rewrite 2 Nat.div_0_l; try apply Nat.pow_nonzero; try easy.
  rewrite 2 Nat.mod_0_l; try apply Nat.pow_nonzero; try easy.
  rewrite IHn.
  rewrite Cmult_1_r.
  unfold bra.
  unfold adjoint.
  simpl.
  lca.
Qed.

Lemma big_bra_S_r : forall n i j, ((S n) ⨂ bra 0) i (S j) = C0.
Proof.
  induction n.
  - simpl; rewrite kron_1_l; [ | auto with wf_db ].
    intros; unfold bra; simpl; unfold adjoint; unfold qubit0.
    destruct i,j; lca.
  - intros.
    rewrite kron_n_assoc; [| auto with wf_db].
    unfold kron.
    destruct (S j mod 2 ^S n) eqn:En.
    + destruct (Nat.mod_divides (S j) (2 ^ S n)); [apply Nat.pow_nonzero; auto |]. 
      destruct (H En).
      rewrite H1.
      replace (2 ^ S n * x / 2 ^ S n)%nat with x.
      * unfold bra; simpl.
        unfold adjoint.
        simpl.
        destruct x.
        -- rewrite mult_0_r in H1.
           discriminate H1.
        -- destruct (i / (1 ^ n + 0))%nat. 
           ++ simpl.
              destruct x; lca.
           ++ simpl.
              destruct x; lca.
      * rewrite mult_comm.
        rewrite Nat.divide_div_mul_exact.
        -- rewrite Nat.div_same; [lia | ].
           apply Nat.pow_nonzero; easy.
        -- apply Nat.pow_nonzero; easy.
        -- apply Nat.divide_refl.
    + rewrite IHn.
      lca.
Qed.

Lemma big_bra_S_l : forall n i j, (n ⨂ bra 0) (S i) j = C0.
Proof.
  intros.
  assert (WF : WF_Matrix (n ⨂ bra 0)).
  { auto with wf_db. }
  apply WF.
  left.
  rewrite Nat.pow_1_l.
  induction i; auto.
Qed.

Lemma big_ket_0_0_0 : forall n, (n ⨂ (ket 0)) 0 0 = C1.
Proof.
  intros.
  induction n; [reflexivity | ].
  rewrite kron_n_assoc; [ | auto with wf_db].
  unfold kron.
  rewrite 2 Nat.div_0_l; try apply Nat.pow_nonzero; try easy.
  rewrite 2 Nat.mod_0_l; try apply Nat.pow_nonzero; try easy.
  rewrite IHn.
  rewrite Cmult_1_r.
  reflexivity.
Qed.

Lemma big_ket_S_r : forall n i j, (n ⨂ ket 0) i (S j) = C0.
Proof.
  intros.
  assert (WF : WF_Matrix (n ⨂ ket 0)).
  { auto with wf_db. }
  apply WF.
  right.
  rewrite Nat.pow_1_l.
  induction j; auto.
Qed.

Lemma big_ket_S_l : forall n i j, (S n ⨂ ket 0) (S i) j = C0.
Proof.
  induction n.
  - intros. simpl.
    rewrite kron_1_l; [ | auto with wf_db ].
    unfold ket.
    unfold qubit0; simpl.
    destruct i, j;lca.
  - intros.
    rewrite kron_n_assoc; [ | auto with wf_db ].
    unfold kron.
    rewrite Nat.pow_1_l.
    rewrite Nat.mod_1_r.
    rewrite Nat.div_1_r.
    destruct (S i mod 2 ^ S n) eqn:En.
    + destruct (Nat.mod_divides (S i) (2^S n)); [apply Nat.pow_nonzero; auto |].
      destruct H; [assumption |].
      rewrite H.
      rewrite mult_comm.
      rewrite Nat.divide_div_mul_exact; [ | apply Nat.pow_nonzero; auto | apply Nat.divide_refl ].
      rewrite Nat.div_same; [ | apply Nat.pow_nonzero; auto].
      rewrite Nat.mul_1_r.
      destruct x; [rewrite mult_0_r in H; discriminate H |].
      unfold ket; simpl.
      destruct x, j; lca.
    + rewrite IHn.
      lca.
Qed.

Lemma braket_sem_0_intermediate : forall (n m : nat), (n ⨂ ket 0) × (m ⨂ bra 0) = braket_0_intermediate m n.
Proof.
  intros.
  destruct n,m; prep_matrix_equality.
  - destruct x,y; lca.
  - unfold Mmult; simpl.
    destruct x,y; replace (m ⨂ bra 0 ⊗ bra 0) with ((S m) ⨂ bra 0) by reflexivity.
    + rewrite big_bra_0_0_0.
      lca.
    + rewrite big_bra_S_r.
      lca.
    + rewrite big_bra_0_0_0.
      lca.
    + rewrite big_bra_S_r.
      lca.
  - unfold Mmult; rewrite Nat.pow_1_l; simpl.
    destruct x,y; replace (n ⨂ ket 0 ⊗ ket 0) with ((S n) ⨂ ket 0) by reflexivity.
    + rewrite big_ket_0_0_0.
      lca.
    + rewrite big_ket_0_0_0.
      lca.
    + rewrite big_ket_S_l.
      lca.
    + rewrite big_ket_S_l.
      lca.
  - unfold Mmult; rewrite Nat.pow_1_l; simpl; rewrite Cplus_0_l.
    replace (n ⨂ ket 0 ⊗ ket 0) with ((S n) ⨂ ket 0) by reflexivity;
    replace (m ⨂ bra 0 ⊗ bra 0) with ((S m) ⨂ bra 0) by reflexivity.
    destruct x,y.
    + rewrite big_ket_0_0_0; rewrite big_bra_0_0_0.
      lca.
    + rewrite big_bra_S_r.
      lca.
    + rewrite big_ket_S_l.
      lca.
    + rewrite big_ket_S_l.
      lca.
Qed.

Lemma big_ket_1_max_0 : forall n, (n ⨂ (ket 1)) (2 ^ n - 1)%nat 0 = C1.
Proof.
  induction n.
  - lca.
  - rewrite kron_n_assoc; [| auto with wf_db].
    unfold kron.
    simpl.
    rewrite <- Nat.add_sub_assoc.
    + replace (0 / 1 ^ n)%nat with 0%nat by (rewrite Nat.pow_1_l; rewrite Nat.div_1_r; reflexivity).
      replace (0 mod 1^n) with 0 by (rewrite Nat.pow_1_l; reflexivity).
      replace ((2 ^ n + (2 ^ n + 0 - 1)) / 2 ^ n)%nat with 1%nat.
      * replace ((2 ^ n + (2 ^ n + 0 - 1)) mod 2 ^ n)%nat with (2^n-1)%nat.
        -- rewrite IHn; lca.
        -- rewrite Nat.add_mod; [| apply Nat.pow_nonzero; auto].
           ++ rewrite plus_0_r.
              rewrite Nat.mod_same; [| apply Nat.pow_nonzero; auto].
              rewrite plus_0_l.
              rewrite Nat.mod_mod; [| apply Nat.pow_nonzero; auto].
              destruct n.
              ** reflexivity.
              ** rewrite Nat.mod_small; [reflexivity|].
                 destruct (2 ^ S n)%nat eqn:E.
                 --- destruct (Nat.pow_nonzero 2 (S n)); [auto |apply E].
                 --- simpl.
                     rewrite Nat.sub_0_r.
                     constructor.
      * rewrite plus_0_r.
        replace ((2 ^ n + (2 ^ n - 1)) / 2 ^ n)%nat with (((1 * 2 ^ n) + (2 ^ n - 1)) / 2 ^ n)%nat.
        -- rewrite Nat.div_add_l; [| apply Nat.pow_nonzero; auto].
           rewrite Nat.div_small; [reflexivity|].
           destruct (2^n)%nat eqn:E.
           ++ destruct (Nat.pow_nonzero 2 n); [auto | apply E].
           ++ simpl; rewrite Nat.sub_0_r.
              auto.
        -- rewrite mult_1_l.
           reflexivity.
    + rewrite plus_0_r.
      rewrite <- (Nat.pow_1_l n).
      replace (S (1 ^ n)) with 2.
      * apply Nat.pow_le_mono_l.
        auto.
      * rewrite Nat.pow_1_l; reflexivity.
Qed.

Lemma big_bra_1_0_max : forall n, (n ⨂ (bra 1)) 0 (2 ^ n - 1)%nat = C1.
Proof.
  induction n.
  - lca.
  - rewrite kron_n_assoc; [| auto with wf_db].
    unfold kron.
    simpl.
    rewrite <- Nat.add_sub_assoc.
    + replace (0 / 1 ^ n)%nat with 0%nat by (rewrite Nat.pow_1_l; rewrite Nat.div_1_r; reflexivity).
      replace (0 mod 1^n) with 0 by (rewrite Nat.pow_1_l; reflexivity).
      replace ((2 ^ n + (2 ^ n + 0 - 1)) / 2 ^ n)%nat with 1%nat.
      * replace ((2 ^ n + (2 ^ n + 0 - 1)) mod 2 ^ n)%nat with (2^n-1)%nat.
        -- rewrite IHn; lca.
        -- rewrite Nat.add_mod; [| apply Nat.pow_nonzero; auto].
           ++ rewrite plus_0_r.
              rewrite Nat.mod_same; [| apply Nat.pow_nonzero; auto].
              rewrite plus_0_l.
              rewrite Nat.mod_mod; [| apply Nat.pow_nonzero; auto].
              destruct n.
              ** reflexivity.
              ** rewrite Nat.mod_small; [reflexivity|].
                 destruct (2 ^ S n)%nat eqn:E.
                 --- destruct (Nat.pow_nonzero 2 (S n)); [auto |apply E].
                 --- simpl.
                     rewrite Nat.sub_0_r.
                     constructor.
      * rewrite plus_0_r.
        replace ((2 ^ n + (2 ^ n - 1)) / 2 ^ n)%nat with (((1 * 2 ^ n) + (2 ^ n - 1)) / 2 ^ n)%nat.
        -- rewrite Nat.div_add_l; [| apply Nat.pow_nonzero; auto].
           rewrite Nat.div_small; [reflexivity|].
           destruct (2^n)%nat eqn:E.
           ++ destruct (Nat.pow_nonzero 2 n); [auto | apply E].
           ++ simpl; rewrite Nat.sub_0_r.
              auto.
        -- rewrite mult_1_l.
           reflexivity.
    + rewrite plus_0_r.
      rewrite <- (Nat.pow_1_l n).
      replace (S (1 ^ n)) with 2.
      * apply Nat.pow_le_mono_l.
        auto.
      * rewrite Nat.pow_1_l; reflexivity.
Qed.

Lemma big_ket_1_n_S : forall n i j, (n ⨂ (ket 1)) i (S j) = C0.
Proof.
  induction n.
  - intros.
    simpl.
    destruct i.
    + lca.
    + unfold I.
      replace (S i <? 1) with false; [| reflexivity].
      rewrite andb_false_r.
      reflexivity.
  - intros.
    simpl.
    unfold kron.
    rewrite Nat.div_1_r.
    rewrite IHn.
    lca.
Qed.

Definition big_bra_sem (n : nat) : Matrix 1 (2 ^ n) :=
  fun x y => 
  if (y =? 2^n-1) && (x =? 0) then C1 else C0.

Lemma big_bra_to_sem : forall n, (n ⨂ (bra 1)) = big_bra_sem n.
Proof.
  induction n.
  - prep_matrix_equality.
    destruct x,y.
    + lca.
    + lca.
    + lca.
    + unfold big_bra_sem.
      rewrite andb_false_r.
      simpl.
      unfold I.
      rewrite andb_false_r.
      reflexivity.
  - prep_matrix_equality.
    simpl.
    rewrite IHn.
    unfold kron.
    destruct (y =? 2^(S n) - 1) eqn:Ex.
    + unfold big_bra_sem.
      rewrite Ex.
      apply Nat.eqb_eq in Ex.
      rewrite Ex.
      rewrite Nat.mod_1_r.
      rewrite Nat.div_1_r.
      destruct y.
      * destruct (2^n)%nat eqn:En.
        -- contradict En.
           apply Nat.pow_nonzero.
           easy.
        -- replace ((2 ^ S n - 1) / 2)%nat with (2^n - 1)%nat.
           ++ rewrite En.
              rewrite Nat.eqb_refl.
              replace ((2 ^ S n - 1) mod 2)%nat with 1%nat.
              ** destruct x; lca.
              ** replace (2 ^ S n)%nat with (2^n + 2^n)%nat.
                 --- destruct (2 ^ n)%nat eqn:E2n.
                     +++ contradict E2n.
                         apply Nat.pow_nonzero; easy.
                     +++ rewrite <- plus_n_Sm.
                         replace (S (S n1 + n1) - 1)%nat with (S (n1 + n1))%nat by reflexivity.
                         rewrite (double_mult n1).
                         rewrite <- (plus_0_l (2*n1)).
                         replace (S (0 + 2 * n1))%nat with (1 + 2 * n1)%nat by reflexivity.
                         rewrite Nat.add_mod; [| easy].
                         rewrite mult_comm.
                         rewrite Nat.mod_mul; [| easy].
                         reflexivity.
                 --- simpl.
                     rewrite plus_0_r.
                     lia.
           ++ replace (2 ^ S n)%nat with (2 * (2 ^ n))%nat.
              ** destruct (2^n)%nat.
                 --- reflexivity.
                 --- contradict Ex.
                     destruct (2^S n)%nat eqn:Esn.
                     +++ contradict Esn.
                         apply Nat.pow_nonzero; easy.
                     +++ destruct n2.
                         *** contradict Esn.
                             simpl.
                             destruct (2^n)%nat.
                             ---- easy.
                             ---- destruct n2.
                                  ++++ easy.
                                  ++++ simpl.
                                       easy.
                         *** easy.
              ** reflexivity.
      * Opaque Nat.div.
        Opaque Nat.modulo.
        replace ((2 ^ S n - 1) / 2)%nat with (2^n - 1)%nat.
        replace ((2 ^ S n - 1) mod 2)%nat with 1%nat.
        -- rewrite Nat.eqb_refl.
           destruct x; lca.
        -- simpl.
           rewrite plus_0_r.
           destruct (2 ^ n)%nat eqn:En.
           ++ contradict En.
              ** apply Nat.pow_nonzero; easy.
           ++ simpl.
              rewrite <- plus_n_Sm.
              rewrite Nat.sub_0_r.
              rewrite double_mult.
              replace (S (2 * n0))%nat with (1 + (2 * n0))%nat by reflexivity.
              rewrite mult_comm.
              rewrite Nat.add_mod; [| easy].
              rewrite Nat.mod_mul; [| easy].
              reflexivity.
        -- simpl.
           rewrite plus_0_r.
           destruct (2 ^ n)%nat.
           ++ reflexivity.
           ++ simpl.
              rewrite Nat.sub_0_r.
              rewrite Nat.sub_0_r.
              rewrite <- plus_n_Sm.
              rewrite double_mult.
              replace (S (2 * n0))%nat with ((1 + (2 * n0)))%nat by reflexivity.
              rewrite plus_comm.
              rewrite mult_comm.
              rewrite Nat.div_add_l; [| easy].
              rewrite plus_comm.
              reflexivity.
    + unfold big_bra_sem.
      rewrite Ex.
      simpl.
      rewrite Nat.mod_1_r.
      Transparent Nat.div.
      destruct (Nat.divmod y 1 0 1) eqn:Edm.
      assert (Hy : (y = 2 * (y / 2) + y mod 2)%nat).
      { apply Nat.div_mod_eq. }
      destruct (y/2 =? 2^n-1) eqn:Ey2.
      * destruct (y mod 2 =? 1) eqn:Eym.
        -- apply Nat.eqb_eq in Eym, Ey2.
           rewrite Ey2, Eym in Hy.
           replace (2 * (2 ^ n - 1) + 1)%nat with (2 ^ S n - 1)%nat in Hy.
           ++ rewrite Hy in Ex.
              rewrite Nat.eqb_refl in Ex.
              discriminate.
           ++ simpl.
              rewrite 2 plus_0_r.
              rewrite <- plus_assoc.
              rewrite <- plus_n_Sm.
              rewrite plus_0_r.
              destruct (2 ^ n)%nat eqn:En.
              ** contradict En.
                 apply Nat.pow_nonzero; easy.
              ** simpl. lia.
        -- destruct (y mod 2).
           ++ lca.
           ++ destruct n2.
              ** discriminate.
              ** lca.
      * lca.
Qed.

Definition big_ket_sem (n : nat) : Matrix (2 ^ n) 1 :=
  fun x y => 
  if (x =? 2^n-1) && (y =? 0) then C1 else C0.

Lemma big_ket_sem_big_bra_sem_transpose : forall n, big_ket_sem n = (big_bra_sem n) ⊤.
Proof.
  intros.
  solve_matrix.
Qed.

Lemma big_ket_to_sem : forall n, (n ⨂ (ket 1)) = big_ket_sem n.
Proof.
  intros.
  rewrite <- (transpose_involutive _ _ _).
  rewrite kron_n_transpose.
  replace ((ket 1)⊤) with (bra 1).
  - rewrite big_ket_sem_big_bra_sem_transpose.
    f_equal.
    + rewrite Nat.pow_1_l.
      easy.
    + apply big_bra_to_sem.
  - solve_matrix.
Qed.

Lemma braket_sem_1_intermediate : forall n m : nat, n ⨂ ket 1 × m ⨂ bra 1 = braket_1_intermediate m n.
Proof.
  intros.
  rewrite big_bra_to_sem.
  rewrite big_ket_to_sem.
  prep_matrix_equality.
  unfold braket_1_intermediate, big_ket_sem, big_bra_sem, Mmult.
  rewrite Nat.pow_1_l; simpl.
  rewrite Cplus_0_l.
  destruct (x =? 2^n-1), (y =? 2^m-1); lca.
Qed.

Lemma ZX_Z_semantics_equiv : forall nIn nOut α, ZX_semantics (Z_Spider nIn nOut α) = ZX_Dirac_semantics (Z_Spider nIn nOut α).
Proof.
  assert (contra : forall a, (0 =? 2 ^ S a - 1) = false).
  { intros.
    simpl.
    destruct (2^a)%nat eqn:Ea.
    - contradict Ea.
      apply Nat.pow_nonzero; easy.
    - rewrite plus_0_r.
      rewrite <- plus_n_Sm. easy.
  }
  intros.
  simpl.
  unfold_dirac_spider.
  rewrite (braket_sem_0_intermediate nOut nIn).
  rewrite (braket_sem_1_intermediate nOut nIn).
  apply Z_semantics_split_plus.
Qed.

Lemma ZX_X_semantics_equiv : forall nIn nOut α, ZX_semantics (X_Spider nIn nOut α) = ZX_Dirac_semantics (X_Spider nIn nOut α).
Proof.
  intros.
  simpl.
  unfold X_semantics.
  unfold_dirac_spider.
  repeat rewrite <- kron_n_mult.
  replace (nOut ⨂ hadamard × nOut ⨂  ket 1 × (nIn ⨂  (ket 1) † × nIn ⨂ (hadamard) †)) 
    with (nOut  ⨂ hadamard × ((nOut ⨂  ket 1) × (nIn ⨂ (ket 1) †)) × nIn ⨂ (hadamard) †).
  replace (nOut ⨂ hadamard × nOut ⨂ ∣ 0 ⟩ × (nIn ⨂ (∣ 0 ⟩) † × nIn ⨂ (hadamard) †)) 
    with (nOut ⨂ hadamard × ((nOut ⨂  ket 0) × (nIn ⨂ (ket 0) †)) × nIn ⨂ (hadamard) †).
    - rewrite <- Mscale_mult_dist_l.
      rewrite <- Mscale_mult_dist_r.
      rewrite <- Mmult_plus_distr_r.
      rewrite <- Mmult_plus_distr_l.
      assert (H : forall nIn nOut α, ZX_semantics (Z_Spider nIn nOut α) = ZX_Dirac_semantics (Z_Spider nIn nOut α)).
      { apply ZX_Z_semantics_equiv. } 
      simpl in H.
      unfold Dirac_spider_semantics in H.
      unfold bra_ket_MN in H.
      rewrite <- H.
      rewrite hadamard_sa.
      reflexivity.
    - repeat rewrite Mmult_assoc.
      reflexivity.
    - repeat rewrite Mmult_assoc.
      reflexivity.
Qed.

Transparent Nat.div.
Transparent Nat.modulo.

Theorem ZX_semantics_equiv (nIn nOut : nat) : forall (zx : ZX nIn nOut),
  ZX_semantics zx = ZX_Dirac_semantics zx.
Proof.
  intros.
  induction zx; try auto.
  - apply ZX_X_semantics_equiv.
  - apply ZX_Z_semantics_equiv.
  - simpl.
    rewrite IHzx1, IHzx2.
    reflexivity.
  - simpl.
    rewrite IHzx1, IHzx2.
    reflexivity.
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
    rewrite <- kron_n_assoc; auto.
    apply WF_ZX.
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
    rewrite Mmult_1_l; [| apply WF_ZX].
    repeat rewrite Mmult_assoc.
    reflexivity.
Qed.

Local Close Scope ZX_scope.
