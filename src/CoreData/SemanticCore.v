(* 
Contains the definitions for Z and X spider semantics, their equivalence, 
and well formedness 
*)

Require Export QuantumLib.Modulus.
Require Export QuantumLib.Quantum.
Require Import QuantumLib.Proportional.
Require Export QuantumLib.VectorStates.
Require Export QlibTemp.

(* Sparse Matrix Definition *)

Definition Z_semantics (n m : nat) (α : R) : Matrix (2 ^ m) (2 ^ n) :=
  fun x y =>
  match x, y with
  | 0, 0 => match n, m with
                  | 0, 0 => C1 + Cexp α
                  | _, _  => C1
                  end
  | _, _ => if ((x =? 2^m-1) && (y =? 2^n-1)) then Cexp α else C0
  end.

Lemma Z_semantics_0_0 (n m : nat) (α : R) : 
  Z_semantics (S n) (S m) α 0%nat 0%nat = 1.
Proof. reflexivity. Qed.

Lemma Z_semantics_max_max (n m : nat) (α : R) : 
  Z_semantics (S n) (S m) α (2^(S m) - 1)%nat (2^(S n) - 1)%nat = Cexp α.
Proof. 
  unfold Z_semantics.
  simpl.
  destruct (2^m)%nat eqn:Em.
  { contradict Em; apply Nat.pow_nonzero; easy. }
  destruct (2^n)%nat eqn:En.
  { contradict En; apply Nat.pow_nonzero; easy. }
  simpl.
  repeat rewrite Nat.sub_0_r;
  repeat rewrite Nat.add_0_r;
  repeat rewrite <- plus_n_Sm;
  repeat rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Definition X_semantics (n m : nat) (α : R) : Matrix (2 ^ m) (2 ^ n) :=
  (m ⨂ hadamard) × (Z_semantics n m α) × (n ⨂ hadamard).


(* Transpose and Adjoint lemmas *)

Lemma Z_semantics_transpose (n m : nat) (α : R) : 
  (Z_semantics n m α) ⊤ = Z_semantics m n α.
Proof.
  unfold Z_semantics.
  unfold transpose.
  prep_matrix_equality.
  destruct x, y.
  1: destruct n, m; reflexivity.
  all: rewrite andb_comm; reflexivity.
Qed.

Lemma Z_semantics_adj (n m : nat) (α : R) : 
  (Z_semantics n m α) † = Z_semantics m n (- α).
Proof.
  unfold adjoint.
  unfold Z_semantics.
  prep_matrix_equality.
  destruct x,y. 
  1: destruct n,m; try lca;
    rewrite Cconj_plus_distr;
    rewrite Cexp_conj_neg;
    lca.
  all: rewrite andb_comm;
       rewrite (if_dist _ _ _ (Cconj));
       rewrite Cexp_conj_neg;
       rewrite Cconj_0;
       reflexivity.
Qed.

Lemma X_semantics_transpose (n m : nat) (α : R) : 
  (X_semantics n m α) ⊤ = X_semantics m n α.
Proof.
  unfold X_semantics.
  rewrite 2 Mmult_transpose.
  rewrite 2 kron_n_transpose.
  rewrite hadamard_st.
  rewrite Mmult_assoc.
  rewrite Z_semantics_transpose.
  reflexivity.
Qed.

Lemma X_semantics_adj (n m : nat) (α : R) : 
  (X_semantics n m α)† = X_semantics m n (- α).
Proof.
  unfold X_semantics.
  distribute_adjoint.
  rewrite Z_semantics_adj.
  rewrite 2 kron_n_adjoint; try auto with wf_db.
  rewrite hadamard_hermitian_rw.
  rewrite Mmult_assoc.
  reflexivity.
Qed.


(* Dirac Notation *)

(* The core of dirac notation *)

Definition bra_ket_mn (bra: Matrix 1 2) (ket : Vector 2) {n m} : 
                                          Matrix (2 ^ m) (2 ^ n) := 
  (m ⨂ ket) × (n ⨂ bra).
Transparent bra_ket_mn. 

Arguments bra_ket_mn bra ket n m /.

Lemma WF_bra_ket_mn : forall n m bra ket, 
  WF_Matrix bra -> WF_Matrix ket -> WF_Matrix (@bra_ket_mn bra ket n m).
Proof.
  intros.
  unfold bra_ket_mn.
  apply WF_mult; restore_dims; apply WF_kron_n; assumption.
Qed.

Definition dirac_spider_semantics 
  (bra0 bra1 : Matrix 1 2) (ket0 ket1 : Vector 2) 
  (α : R) (n m : nat) : Matrix (2 ^ m) (2 ^ n) :=
    (bra_ket_mn bra0 ket0) .+ (Cexp α) .* (bra_ket_mn bra1 ket1). 

Arguments dirac_spider_semantics bra0 bra1 ket0 ket1 α n m /.

Lemma WF_dirac_spider_semantics : forall n m bra0 bra1 ket0 ket1 α, 
  WF_Matrix bra0 -> WF_Matrix bra1 -> WF_Matrix ket0 -> WF_Matrix ket1 -> 
  WF_Matrix (@dirac_spider_semantics bra0 bra1 ket0 ket1 α n m).
Proof.
  intros.
  unfold dirac_spider_semantics.
  apply WF_plus; restore_dims; try apply WF_scale; 
                                   apply WF_bra_ket_mn; 
                                   assumption.
Qed.

#[export] Hint Resolve WF_dirac_spider_semantics WF_bra_ket_mn : wf_db.

(* Dirac semantics for a given spider *)

Definition Z_dirac_semantics (n m : nat) (α : R) := 
  dirac_spider_semantics ⟨0∣ ⟨1∣ ∣0⟩ ∣1⟩ α n m.

Definition X_dirac_semantics (n m : nat) (α : R) :=
  dirac_spider_semantics ⟨+∣ ⟨-∣ ∣+⟩ ∣-⟩ α n m.

Arguments Z_dirac_semantics n m α /.
Arguments X_dirac_semantics n m α /.

(** Simplify by unfolding [dirac_spider_semantics] and [bra_ket_mn],
  then [simplf; Msimpl]. *)
Ltac unfold_dirac_spider := 
  simpl; unfold dirac_spider_semantics, bra_ket_mn; try (simpl; Msimpl).

(** Working towards equivalence of the two forms of semantics *)

Lemma dirac_spider_X_H_Z : forall n m α, 
  X_dirac_semantics n m α = 
  m ⨂ hadamard × (Z_dirac_semantics n m α) × (n ⨂ hadamard).
Proof.
  intros.
  simpl.
  restore_dims.
  rewrite Mmult_plus_distr_l.
  rewrite Mmult_plus_distr_r.
  apply Mplus_simplify.
  - repeat rewrite Mmult_assoc. 
    restore_dims.
    rewrite kron_n_mult.
    rewrite <- Mmult_assoc.
    rewrite kron_n_mult.
    replace (hadamard × ∣0⟩) with ∣+⟩ by lma.
    replace (⟨0∣ × hadamard) with ⟨+∣ by lma.
    reflexivity.
  - autorewrite with scalar_move_db.
    apply Mscale_simplify; [| lca].
    repeat rewrite Mmult_assoc.
    restore_dims.
    rewrite kron_n_mult.
    rewrite <- Mmult_assoc.
    rewrite kron_n_mult.
    replace (hadamard × ∣1⟩) with ∣-⟩ by lma.
    replace (⟨1∣ × hadamard) with ⟨-∣ by lma.
    reflexivity.
Qed.

Definition braket_0_intermediate (n m : nat) : Matrix (2^m) (2^n) :=
  fun x y => match x, y with
             | 0, 0 => C1
             | _, _ => C0
             end.

Definition braket_1_intermediate (n m : nat) : Matrix (2^m) (2^n) :=
  fun x y => if (x =? 2^m - 1) && (y =? 2^n - 1) then C1 else C0.

Lemma Z_semantics_split_plus : forall (n m : nat) (α : R), 
  Z_semantics n m α = 
  (braket_0_intermediate n m) .+ Cexp α .* (braket_1_intermediate n m).
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
    + destruct n, m; [lca | destruct (contra m Em) | | ]; 
                                  destruct (contra n En).
    + destruct n, m; [discriminate | | | ]; lca.
    + destruct n, m; [discriminate | | | ]; lca.
    + destruct n, m; [discriminate | discriminate | | ]; lca.
  - destruct (2^n-1)%nat eqn:En, (2^m-1)%nat eqn:Em.
    + destruct n,m; [lca | destruct (contra m Em) | | ]; destruct (contra n En).
    + destruct n, m; [discriminate | | | ]; lca.
    + destruct n, m; [discriminate | discriminate | |]; destruct (y =? n0); lca.
    + destruct n, m; [discriminate | | | lca]; destruct (y =? n0); lca.
  - destruct (2^n-1)%nat eqn:En, (2^m-1)%nat eqn:Em; [lca | | lca | ]; 
                                               destruct (_ =? _); lca.
  - destruct (2^n-1)%nat eqn:En, (2^m-1)%nat eqn:Em; [lca | | lca | ]; 
                                        repeat destruct (_ =? _); lca.
Qed.


Lemma big_bra_0_0_0 : forall n, (n ⨂ (bra 0)) 0%nat 0%nat = C1.
Proof.
  intros.
  induction n; [reflexivity | ].
  rewrite kron_n_assoc; [ | auto with wf_db].
  unfold kron.
  rewrite 2 Nat.Div0.div_0_l.
  rewrite 2 Nat.Div0.mod_0_l.
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
    + destruct (Nat.mod_divides (S j) (2 ^ S n) (pow2_nonzero _)).
      destruct (H En).
      rewrite H1.
      replace (2 ^ S n * x / 2 ^ S n)%nat with x.
      * unfold bra; simpl.
        unfold adjoint.
        simpl.
        destruct x;
        [now rewrite Nat.mul_0_r in H1|].
        destruct (i / (1 ^ n + 0))%nat;
        simpl; destruct x; lca.
      * rewrite Nat.mul_comm.
        rewrite Nat.div_mul by now apply Nat.pow_nonzero.
        easy.
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

Lemma big_ket_0_0_0 : forall n, (n ⨂ (ket 0)) 0%nat 0%nat = C1.
Proof.
  intros.
  induction n; [reflexivity | ].
  rewrite kron_n_assoc; [ | auto with wf_db].
  unfold kron.
  rewrite 2 Nat.Div0.div_0_l.
  rewrite 2 Nat.Div0.mod_0_l.
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
    + destruct (Nat.mod_divides (S i) (2^S n) (pow2_nonzero _)).
      destruct H; [assumption |].
      rewrite H.
      rewrite Nat.mul_comm.

      rewrite Nat.div_mul by now apply Nat.pow_nonzero.
      destruct x; [rewrite Nat.mul_0_r in H; discriminate H |].
      unfold ket; simpl.
      destruct x, j; lca.
    + rewrite IHn.
      lca.
Qed.

Lemma braket_sem_0_intermediate : forall (n m : nat), 
  (n ⨂ ket 0) × (m ⨂ bra 0) = braket_0_intermediate m n.
Proof.
  intros.
  destruct n,m; prep_matrix_equality.
  - destruct x,y; lca.
  - unfold Mmult; simpl.
    destruct x,y; 
    replace (m ⨂ bra 0 ⊗ bra 0) with ((S m) ⨂ bra 0) by reflexivity.
    + rewrite big_bra_0_0_0.
      lca.
    + rewrite big_bra_S_r.
      lca.
    + rewrite big_bra_0_0_0.
      lca.
    + rewrite big_bra_S_r.
      lca.
  - unfold Mmult; rewrite Nat.pow_1_l; simpl.
    destruct x,y; 
    replace (n ⨂ ket 0 ⊗ ket 0) with ((S n) ⨂ ket 0) by reflexivity.
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

Lemma big_ket_1_n_S : forall n i j, (n ⨂  ∣1⟩) i (S j) = C0.
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

Lemma big_bra_sem_to_e_i n : 
  big_bra_sem n = (e_i (2^n-1)) ⊤.
Proof.
  prep_matrix_equality.
  unfold transpose, big_bra_sem, e_i.
  pose proof (Modulus.pow2_nonzero n).
  Modulus.bdestructΩ'.
Qed.

Lemma big_bra_to_sem : forall n, (n ⨂ (bra 1)) = big_bra_sem n.
Proof.
  intros n.
  rewrite big_bra_sem_to_e_i.
  replace (bra 1) with ((@e_i 2 1) ⊤) by lma'.
  rewrite <- kron_n_transpose.
  rewrite Nat.pow_1_l.
  f_equal.
  induction n.
  - lma'.
  - cbn [kron_n].
    rewrite IHn.
    restore_dims.
    pose proof (Modulus.pow2_nonzero n).
    rewrite (Kronecker.kron_e_i_e_i 2 (2^n) 1 (2^n-1)) by lia.
    f_equal; cbn; lia.
Qed.

Definition big_ket_sem (n : nat) : Matrix (2 ^ n) 1 :=
  fun x y => 
  if (x =? 2^n-1) && (y =? 0) then C1 else C0.

Lemma big_ket_sem_big_bra_sem_transpose : forall n, 
  big_ket_sem n = (big_bra_sem n) ⊤.
Proof.
  intros.
  unfold big_ket_sem, big_bra_sem.
  unfold transpose.
  reflexivity.
Qed.

Lemma big_ket_to_sem : forall n, (n ⨂ (ket 1)) = big_ket_sem n.
Proof.
  intros.
  rewrite <- (transpose_involutive _ _ _).
  rewrite kron_n_transpose.
  rewrite ket1_transpose_bra1.
  rewrite big_ket_sem_big_bra_sem_transpose.
  rewrite big_bra_to_sem, Nat.pow_1_l.
  easy.
Qed.

Lemma big_ket_1_max_0 : forall n, (n ⨂  ∣1⟩) (2 ^ n - 1)%nat 0%nat = C1.
Proof.
  intros n.
  rewrite ket1_equiv.
  rewrite big_ket_to_sem.
  unfold big_ket_sem.
  now rewrite 2!Nat.eqb_refl.
Qed.

Lemma big_bra_1_0_max : forall n, (n ⨂ ⟨1∣) 0%nat (2 ^ n - 1)%nat = C1.
Proof.
  intros n.
  rewrite bra1_equiv.
  rewrite big_bra_to_sem.
  unfold big_bra_sem.
  now rewrite 2!Nat.eqb_refl.
Qed.

Lemma braket_sem_1_intermediate : forall n m : nat, 
  n ⨂ ket 1 × m ⨂ bra 1 = braket_1_intermediate m n.
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

Lemma Z_semantics_equiv : forall n m α, 
  Z_semantics n m α = Z_dirac_semantics n m α.
Proof.
  intros.
  simpl.
  replace (m ⨂ ∣0⟩ × n ⨂ ⟨0∣)
     with (braket_0_intermediate n m).
  replace (m ⨂ ∣1⟩ × n ⨂ ⟨1∣)
     with (braket_1_intermediate n m).
  apply Z_semantics_split_plus.
  rewrite braket_sem_1_intermediate; auto.
  rewrite braket_sem_0_intermediate; auto.
Qed.

Lemma X_semantics_equiv : forall n m α, 
  X_semantics n m α = X_dirac_semantics n m α.
Proof.
  intros.
  rewrite dirac_spider_X_H_Z.
  unfold X_semantics.
  Msimpl.
  restore_dims.
  rewrite Z_semantics_equiv.
  reflexivity.
Qed.

Lemma WF_Z_semantics : forall n m α, WF_Matrix (Z_semantics n m α).
Proof. 
  intros; rewrite Z_semantics_equiv; 
  apply WF_dirac_spider_semantics; auto with wf_db. 
Qed.

Lemma WF_X_semantics : forall n m α, WF_Matrix (X_semantics n m α).
Proof. 
  intros; rewrite X_semantics_equiv; 
  apply WF_dirac_spider_semantics; auto with wf_db. 
Qed.

#[export] Hint Resolve WF_Z_semantics WF_X_semantics : wf_db.


Lemma X_2_1_semantics α : X_semantics 2 1 α = 
  (/ √ 2 * / 2) .* @make_WF (2^1) (2^2) (list2D_to_matrix
    [[1 + Cexp α; 1 - Cexp α; 1 - Cexp α; 1 + Cexp α]; 
     [1 - Cexp α; 1 + Cexp α; 1 + Cexp α; 1 - Cexp α]]).
Proof.
  unfold X_semantics.
  cbn [kron_n].
  Msimpl.
  prep_matrix_equivalence.
  restore_dims.
  compute_matrix (hadamard × Z_semantics 2 1 α × (hadamard ⊗ hadamard)).
  group_radicals.
  replace (/ √ 2 * / C2 + / √ 2 * Cexp α * / C2) with 
    (/ √ 2 * / C2 * (C1 + Cexp α)) by lca.
  replace (/ √ 2 * / C2 + - (/ √ 2 * Cexp α * / C2)) with 
    (/ √ 2 * / C2 * (C1 - Cexp α)) by lca.
  rewrite 2!make_WF_equiv.
  by_cell; lca.
Qed.

Lemma X_2_1_0_semantics : X_semantics 2 1 0 = 
  @make_WF (2^1) (2^2) (list2D_to_matrix
    [[/ √ 2; C0; C0; / √ 2]; [C0; / √ 2; / √ 2; C0]]).
Proof.
  rewrite X_2_1_semantics.
  prep_matrix_equivalence.
  match goal with 
  |- ?A ≡ _ => compute_matrix A
  end.
  rewrite 2!make_WF_equiv.
  rewrite Cexp_0.
  rewrite <- Cdouble, Cmult_1_r, Cminus_diag by reflexivity.
  rewrite <- Cmult_assoc.
  now autorewrite with C_db.
Qed.

Lemma X_2_1_pi_semantics : X_semantics 2 1 PI = 
  @make_WF (2^1) (2^2) (list2D_to_matrix
    [[C0; / √ 2; / √ 2; C0]; [/ √ 2; C0; C0; / √ 2]]).
Proof.
  rewrite X_2_1_semantics.
  prep_matrix_equivalence.
  match goal with 
  |- ?A ≡ _ => compute_matrix A
  end.
  rewrite Cexp_PI.
  change (-1 : R) with (Ropp 1).
  rewrite RtoC_opp.
  autorewrite with C_db.
  rewrite <- Cmult_assoc.
  now autorewrite with C_db.
Qed.

(* Compatibility from earlier code *)
Opaque Nat.div.
Opaque Nat.modulo.

