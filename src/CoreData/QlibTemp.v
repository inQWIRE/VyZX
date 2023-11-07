From QuantumLib Require Import Matrix.
From QuantumLib Require Import Quantum.

(* @nocheck name *)
Lemma Mscale_inv : forall {n m} (A B : Matrix n m) c, c <> C0 -> c .* A = B <-> A = (/ c) .* B.
Proof.
  intros.
  split; intro H0; [rewrite <- H0 | rewrite H0];
  rewrite Mscale_assoc.
  - rewrite Cinv_l; [ lma | assumption].  
  - rewrite Cinv_r; [ lma | assumption].  
Qed.

(* @nocheck name *)
Lemma Ropp_lt_0 : forall x : R, x < 0 -> 0 < -x.
Proof.
	intros.
	rewrite <- Ropp_0.
	apply Ropp_lt_contravar.
	easy.
Qed.

(* @nocheck name *)
Definition Rsqrt (x : R) :C := 
match Rcase_abs x with
| left a => Ci * Rsqrt {| nonneg := - x; cond_nonneg := Rlt_le 0 (-x)%R (Ropp_lt_0 x a) |}
| right a => C1 * Rsqrt {| nonneg := x; cond_nonneg := Rge_le x R0 a |}
end.

(* @nocheck name *)
(* *)
Lemma INR_pi_exp : forall (r : nat),
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

(* @nocheck name *)
(* PI is captialized in Coq R *)
Lemma Cexp_2_PI : forall a, Cexp (INR a * 2 * PI) = 1.
Proof.
	intros.
	induction a.
	- simpl.
		rewrite 2 Rmult_0_l.
		rewrite Cexp_0.
		easy.
	- rewrite S_INR.
		rewrite 2 Rmult_plus_distr_r.
		rewrite Rmult_1_l.
		rewrite double.
		rewrite <- Rplus_assoc.
		rewrite 2 Cexp_plus_PI.
		rewrite IHa.
		lca.
Qed.

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

(* @nocheck name *)
Definition Csqrt (z : C) : C :=
	match z with
	| (a, b) => sqrt ((Cmod z + a) / 2) + Ci * (b / Rabs b) * sqrt((Cmod z - a) / 2)
	end.

Notation "√ z" := (Csqrt z) : C_scope.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmultplus0 : 
	⟨+∣ × ∣0⟩ = / (√2)%R .* I 1.
Proof.
	unfold braplus.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult_plus_distr_r.
	rewrite Mmult00.
	rewrite Mmult10.
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmult0plus : 
	⟨0∣ × ∣+⟩ = / (√2)%R .* I 1.
Proof.
	unfold xbasis_plus.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult_plus_distr_l.
	rewrite Mmult00.
	rewrite Mmult01.
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmultplus1 : 
	⟨+∣ × ∣1⟩ = / (√2)%R .* I 1.
Proof.
	unfold braplus.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult_plus_distr_r.
	rewrite Mmult01.
	rewrite Mmult11.
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmult1plus : 
	⟨1∣ × ∣+⟩ = / (√2)%R .* I 1.
Proof.
	unfold xbasis_plus.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult_plus_distr_l.
	rewrite Mmult10.
	rewrite Mmult11.
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmultminus0 : 
	⟨-∣ × ∣0⟩ = / (√2)%R .* I 1.
Proof.
	unfold braminus.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult_plus_distr_r.
	rewrite Mmult00.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult10.
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmult0minus : 
	⟨0∣ × ∣-⟩ = / (√2)%R .* I 1.
Proof.
	unfold xbasis_minus.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult_plus_distr_l.
	rewrite Mmult00.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult01.
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmultminus1 : 
	⟨-∣ × ∣1⟩ = - / (√2)%R .* I 1.
Proof.
	unfold braminus.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult_plus_distr_r.
	rewrite Mmult01.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult11.
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmult1minus : 
	⟨1∣ × ∣-⟩ = - / (√2)%R .* I 1.
Proof.
	unfold xbasis_minus.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult_plus_distr_l.
	rewrite Mmult10.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult11.
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmultminusminus : 
	⟨-∣ × ∣-⟩ = I 1.
Proof.
	unfold braminus.
	unfold xbasis_minus.
	repeat rewrite Mscale_mult_dist_l.
	repeat rewrite Mscale_mult_dist_r.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	rewrite Mmult00.
	rewrite Mmult01.
	rewrite Mmult10.
	rewrite Mmult11.
	Msimpl.
	autorewrite with scalar_move_db.
	solve_matrix.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmultplusminus : 
	⟨+∣ × ∣-⟩ = Zero.
Proof.
	unfold xbasis_minus.
	unfold braplus.
	repeat rewrite Mscale_mult_dist_l.
	repeat rewrite Mscale_mult_dist_r.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	rewrite Mmult00.
	rewrite Mmult01.
	rewrite Mmult10.
	rewrite Mmult11.
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmultminusplus : 
	⟨-∣ × ∣+⟩ = Zero.
Proof.
	unfold xbasis_plus.
	unfold braminus.
	repeat rewrite Mscale_mult_dist_l.
	repeat rewrite Mscale_mult_dist_r.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	rewrite Mmult00.
	rewrite Mmult01.
	rewrite Mmult10.
	rewrite Mmult11.
	Msimpl.
	lma.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Mmultplusplus : 
	⟨+∣ × ∣+⟩ = I 1.
Proof.
	unfold xbasis_plus.
	unfold braplus.
	repeat rewrite Mscale_mult_dist_l.
	repeat rewrite Mscale_mult_dist_r.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	rewrite Mmult00.
	rewrite Mmult01.
	rewrite Mmult10.
	rewrite Mmult11.
	solve_matrix.
Qed.

#[export] Hint Rewrite 
	Mmult00 Mmult01 Mmult10 Mmult11 
	Mmultplus0 Mmultplus1 Mmultminus0 Mmultminus1
	Mmult0plus Mmult0minus Mmult1plus Mmult1minus
	Mmultplusplus Mmultplusminus Mmultminusplus Mmultminusminus
	: ketbra_mult_db.

Lemma bra0transpose :
	⟨0∣⊤ = ∣0⟩.
Proof. solve_matrix. Qed.

Lemma bra1transpose :
	⟨1∣⊤ = ∣1⟩.
Proof. solve_matrix. Qed.

Lemma ket0transpose :
	∣0⟩⊤ = ⟨0∣.
Proof. solve_matrix. Qed.

Lemma ket1transpose :
	∣1⟩⊤ = ⟨1∣.
Proof. solve_matrix. Qed.

(* @nocheck name *)
(* qlib standard *)
Lemma C2_neq_0 : C2 <> C0.
Proof.
	intros.
	replace C2 with (RtoC (R1 + R1)) by lca.
	apply RtoC_neq.
	lra.
Qed.
