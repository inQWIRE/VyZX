From QuantumLib Require Import Matrix.
From QuantumLib Require Import Quantum.

Lemma INR_PI_EXP : forall (r : nat),
	Cexp (INR r * PI) = 1 \/ Cexp (INR r * PI) = -1.
Proof.
	intros.
	dependent induction r.
	- simpl.
		rewrite Rmult_0_l.
		left.
		apply Cexp_0.
	-	rewrite S_O_plus_INR.
		rewrite Rmult_plus_distr_r.
		rewrite Rmult_1_l.
		rewrite Rplus_comm.
		rewrite Cexp_plus_PI.
		destruct IHr.
		+ rewrite H; right; lca.
		+ rewrite H; left; lca.
Qed.

Lemma transpose_matrices : forall {n m} (A B : Matrix n m),
	A ⊤ = B ⊤ -> A = B.
Proof.
	intros.
	rewrite <- transpose_involutive.
	rewrite <- H.
	rewrite transpose_involutive.
	easy.
Qed.

Lemma adjoint_matrices : forall {n m} (A B : Matrix n m),
	A † = B † -> A = B.
Proof.
	intros.
	rewrite <- adjoint_involutive.
	rewrite <- H.
	rewrite adjoint_involutive.
	easy.
Qed.


Lemma kron_id_dist_r : forall {n m o} p (A : Matrix n m) (B : Matrix m o),
WF_Matrix A -> WF_Matrix B -> (A × B) ⊗ (I p) = (A ⊗ (I p)) × (B ⊗ (I p)).
Proof.
	intros.
	rewrite <- (Mmult_1_l _ _ (I p)).
	rewrite kron_mixed_product.
	Msimpl.
	easy.
	auto with wf_db.
Qed.

Lemma kron_id_dist_l : forall {n m o} p (A : Matrix n m) (B : Matrix m o),
WF_Matrix A -> WF_Matrix B -> (I p) ⊗ (A × B) = ((I p) ⊗ A) × ((I p) ⊗ B).
Proof.
	intros.
	rewrite <- (Mmult_1_l _ _ (I p)).
	rewrite kron_mixed_product.
	Msimpl.
	easy.
	auto with wf_db.
Qed.

Lemma swap_transpose : swap ⊤%M = swap.
Proof. lma. Qed.

Lemma swap_spec' : swap = ((ket 0 × bra 0)  ⊗ (ket 0 × bra 0) .+ (ket 0 × bra 1)  ⊗ (ket 1 × bra 0)
  .+ (ket 1 × bra 0)  ⊗ (ket 0 × bra 1) .+ (ket 1 × bra 1)  ⊗ (ket 1 × bra 1)).
Proof.
  solve_matrix.
Qed.

Lemma xbasis_plus_spec : ∣+⟩ = / √ 2 .* (∣0⟩ .+ ∣1⟩).
Proof. solve_matrix. Qed.

Lemma xbasis_minus_spec : ∣-⟩ = / √ 2 .* (∣0⟩ .+  (- 1) .* (∣1⟩)).
Proof. solve_matrix. Qed.

Definition braminus :=  / √ 2 .* (⟨0∣ .+ (-1 .* ⟨1∣)).
Definition braplus  :=  / √ 2 .* (⟨0∣ .+ ⟨1∣).

Notation "⟨+∣" := braplus.
Notation "⟨-∣" := braminus.

Lemma WF_braplus : WF_Matrix (⟨+∣).
Proof. unfold braplus; auto with wf_db. Qed.

Lemma WF_braminus : WF_Matrix (⟨-∣).
Proof. unfold braminus; auto with wf_db. Qed.

Lemma braplus_transpose_ketplus :
  ⟨+∣⊤ = ∣+⟩.
Proof. unfold braplus; lma. Qed.

Lemma braminus_transpose_ketminus :
  ⟨-∣⊤ = ∣-⟩.
Proof. unfold braminus; lma. Qed.

#[export] Hint Resolve 
  WF_braplus
  WF_braminus : wf_db.

#[export] Hint Rewrite 
  Mscale_kron_dist_l 
  Mscale_kron_dist_r 
  Mscale_mult_dist_l 
  Mscale_mult_dist_r 
  Mscale_assoc : scalar_move_db.

#[export] Hint Rewrite <- Mscale_plus_distr_l : scalar_move_db.
#[export] Hint Rewrite <- Mscale_plus_distr_r : scalar_move_db.

