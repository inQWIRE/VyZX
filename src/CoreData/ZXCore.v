Require Import QuantumLib.Quantum.
Require Import QuantumLib.Proportional.
Require Import QuantumLib.VectorStates.

Require Export SemanticCore.
Require Export QlibTemp.

(* 
Base constructions for the ZX calculus, lets us build every diagram inductively.
We have included some "unnecessary" objects because they are common and useful. 
*)

Declare Scope ZX_scope.
Delimit Scope ZX_scope with ZX.
Open Scope ZX_scope.

Inductive ZX : nat -> nat -> Type :=
  | Empty : ZX 0 0
  | Cup  : ZX 0 2
  | Cap  : ZX 2 0
  | Swap : ZX 2 2
  | Wire : ZX 1 1
  | Box  : ZX 1 1
  | X_Spider n m (α : R) : ZX n m
  | Z_Spider n m (α : R) : ZX n m
  | Stack {n_0 m_0 n_1 m_1} (zx0 : ZX n_0 m_0) (zx1 : ZX n_1 m_1) : 
          ZX (n_0 + n_1) (m_0 + m_1)
  | Compose {n m o} (zx0 : ZX n m) (zx1 : ZX m o) : ZX n o.

Definition cast (n m : nat) {n' m'} 
              (prfn : n = n') (prfm : m = m') (zx : ZX n' m') : ZX n m.
Proof.
  destruct prfn.
  destruct prfm.
  exact zx.
Defined.

(* Notations for the ZX diagrams *)
Notation "⦰" := Empty : ZX_scope. (* \revemptyset *)
Notation "⊂" := Cup : ZX_scope. (* \subset *)
Notation "⊃" := Cap : ZX_scope. (* \supset *)
Notation "⨉" := Swap : ZX_scope. (* \bigtimes *)
Notation "—" := Wire : ZX_scope. (* \emdash *)
Notation "□" := Box : ZX_scope. (* \square *)
Notation "A ⟷ B" := (Compose A B) 
  (left associativity, at level 40) : ZX_scope. (* \longleftrightarrow *)
Notation "A ↕ B" := (Stack A B) 
  (left associativity, at level 40) : ZX_scope. (* \updownarrow *)
Notation "'Z'" := Z_Spider (no associativity, at level 1) : ZX_scope.
Notation "'X'" := X_Spider (no associativity, at level 1) : ZX_scope.
Notation "$ n , m ::: A $" := (cast n m _ _ A) (at level 20) : ZX_scope.

(* 
We provide two separate options for semantic functions, one based on sparse 
matrices and one based on dirac notation. 
*)

(* @nocheck name *)
Reserved Notation "⟦ zx ⟧" (at level 0, zx at level 200). (* = is 70, need to be below *)
Fixpoint ZX_semantics {n m} (zx : ZX n m) : 
  Matrix (2 ^ m) (2 ^ n) := 
  match zx with
  | ⦰ => I 1
  | X _ _ α => X_semantics n m α
  | Z _ _ α => Z_semantics n m α
  | ⊃ => list2D_to_matrix [[C1;C0;C0;C1]]
  | ⊂ => list2D_to_matrix [[C1];[C0];[C0];[C1]]  
  | ⨉ => swap
  | — => I 2
  | □ => hadamard
  | zx0 ↕ zx1 => ⟦ zx0 ⟧ ⊗ ⟦ zx1 ⟧
  | Compose zx0 zx1 => ⟦ zx1 ⟧ × ⟦ zx0 ⟧
  end
  where "⟦ zx ⟧" := (ZX_semantics zx).

Lemma zx_compose_spec : forall n m o (zx0 : ZX n m) (zx1 : ZX m o),
	⟦ zx0 ⟷ zx1 ⟧ = ⟦ zx1 ⟧ × ⟦ zx0 ⟧.
Proof. easy. Qed.

Lemma zx_stack_spec : forall n m o p (zx0 : ZX n m) (zx1 : ZX o p),
	⟦ zx0 ↕ zx1 ⟧ = ⟦ zx0 ⟧ ⊗ ⟦ zx1 ⟧.
Proof. easy. Qed.

Lemma cast_semantics : forall {n m n' m'} {eqn eqm} (zx : ZX n m),
  ⟦ cast n' m' eqn eqm zx ⟧ = ⟦ zx ⟧.
Proof.
  intros.
  subst.
  easy.
Qed.

Definition cast_semantics_dim_eqn {n m n' m' : nat} (zx : ZX n m) : Matrix (2 ^ n') (2 ^ m') := ⟦ zx ⟧.

Lemma cast_semantics_dim : forall {n m n' m'} {eqn eqm} (zx : ZX n m),
  ⟦ (cast n' m' eqn eqm zx) ⟧ = cast_semantics_dim_eqn zx.
Proof.
  intros.
  unfold cast_semantics_dim_eqn.
  apply cast_semantics.
Qed.

(** Replace [⟦ cast n m prf1 prf2 zx ⟧] in the goal with [⟦ zx ⟧]. 
  NB this may make the goal no longer definitionally dimensionally 
  consistent, as the size of [⟦ zx ⟧] need not be trivially equal to
  the size of [⟦ cast n m prf1 prf2 zx ⟧]. In some cases, this may even
  escape the abilities of [restore_dims] and require manual intervention. *)
Ltac simpl_cast_semantics := 
  try repeat rewrite cast_semantics; 
  try repeat (rewrite cast_semantics_dim; unfold cast_semantics_dim_eqn).
(* @nocheck name *)

Fixpoint ZX_dirac_sem {n m} (zx : ZX n m) : 
  Matrix (2 ^ m) (2 ^ n) := 
  match zx with
  | ⦰ => I 1
  | X _ _ α => X_dirac_semantics n m α
  | Z _ _ α => Z_dirac_semantics n m α
  | ⊃ => list2D_to_matrix [[C1;C0;C0;C1]]
  | ⊂ => list2D_to_matrix [[C1];[C0];[C0];[C1]]  
  | ⨉ => swap
  | — => I 2
  | □ => hadamard
  | zx0 ↕ zx1 => (ZX_dirac_sem zx0) ⊗ (ZX_dirac_sem zx1)
  | zx0 ⟷ zx1 => (ZX_dirac_sem zx1) × (ZX_dirac_sem zx0)
(* @nocheck name *)
  end.

Lemma ZX_semantic_equiv : forall n m (zx : ZX n m),
  ⟦ zx ⟧ = ZX_dirac_sem zx.
Proof.
  intros.
  induction zx; try lma; simpl.
  rewrite X_semantics_equiv; reflexivity.
  rewrite Z_semantics_equiv; reflexivity.
(* @nocheck name *)
  1,2: subst; rewrite IHzx1, IHzx2; reflexivity.
Qed.

Theorem WF_ZX : forall nIn nOut (zx : ZX nIn nOut), WF_Matrix (⟦ zx ⟧).
Proof.
  intros.
  induction zx; try (simpl; auto 10 with wf_db).
  1,2: try (simpl; auto 10 with wf_db);
    apply WF_list2D_to_matrix;
    try easy; (* case list of length 4 *)
    try intros; simpl in H; repeat destruct H; 
          try discriminate; try (subst; easy). (* Case of 4 lists length 1 *)
Qed.

#[export] Hint Resolve WF_ZX : wf_db.

(* Parametrized diagrams *)

Reserved Notation "n ⇑ zx" (at level 35). 
Fixpoint n_stack {nIn nOut} n (zx : ZX nIn nOut) : ZX (n * nIn) (n * nOut) :=
  match n with
  | 0 => ⦰
  | S n' => zx ↕ (n' ⇑ zx)
  end
  where "n ⇑ zx" := (n_stack n zx).

Reserved Notation "n ↑ zx" (at level 35).
Fixpoint n_stack1 n (zx : ZX 1 1) : ZX n n :=
  match n with
  | 0 => ⦰
  | S n' => zx ↕ (n' ↑ zx)
  end
  where "n ↑ zx" := (n_stack1 n zx).

Lemma n_stack1_n_kron : forall n (zx : ZX 1 1), 
  ⟦ (n ↑ zx) ⟧ = n ⨂ ⟦ zx ⟧.
Proof.
  intros.
  induction n.
  - unfold n_stack. reflexivity.
  - simpl.
    rewrite IHn.
    restore_dims.
    rewrite <- kron_n_assoc; auto.
    apply WF_ZX.
Qed.

Definition n_wire := fun n => n ↑ Wire.
Definition n_box := fun n => n ↑ Box.

Lemma n_wire_semantics {n} : ⟦ n_wire n ⟧ = I (2^n).
Proof.
  induction n; auto.
  simpl.
  unfold n_wire in IHn.
  rewrite IHn.
  rewrite id_kron.
  reflexivity. 
Qed.

Lemma n_box_semantics {n} : ⟦ n_box n ⟧ = n ⨂ hadamard.
Proof.
  induction n; auto.
  simpl.
  unfold n_box in IHn.
  rewrite IHn.
  rewrite <- kron_n_assoc by auto with wf_db.
  reflexivity.
Qed.

#[export] Hint Rewrite @n_wire_semantics @n_box_semantics : zx_sem_db.

(** Global operations on ZX diagrams *)

(* Transpose of a diagram *)

Reserved Notation "zx ⊤" (at level 0). (* \top *)
Fixpoint transpose {nIn nOut} (zx : ZX nIn nOut) : ZX nOut nIn :=
  match zx with
  | ⦰ => ⦰
  | Z mIn mOut α => Z mOut mIn α
  | X mIn mOut α => X mOut mIn α
  | zx0 ⟷ zx1 => (zx1 ⊤) ⟷ (zx0 ⊤)
  | zx1 ↕ zx2 => (zx1 ⊤) ↕ (zx2 ⊤)
  | ⊂ => ⊃
  | ⊃ => ⊂
  | other => other
  end
  where "zx ⊤" := (transpose zx) : ZX_scope.

(* Negating the angles of a diagram, complex conjugate *)

Reserved Notation "zx ⊼" (at level 0). (* \barwedge *)
Fixpoint conjugate {n m} (zx : ZX n m) : ZX n m :=
  match zx with
  | Z n m α => Z n m (-α)
  | X n m α => X n m (-α)
  | zx0 ⟷ zx1 => (zx0⊼) ⟷ (zx1⊼)
  | zx1 ↕ zx2 => zx1⊼ ↕ zx2⊼
  | other => other
  end
  where "zx ⊼" := (conjugate zx) : ZX_scope.

Definition adjoint {n m} (zx : ZX n m) : ZX m n :=
  (zx⊼)⊤.
Notation "zx †" := (adjoint zx) (at level 0) : ZX_scope.

Lemma semantics_transpose_comm {nIn nOut} : forall (zx : ZX nIn nOut),
  ⟦ zx ⊤ ⟧ = ((⟦ zx ⟧) ⊤)%M.
Proof.
  induction zx.
  - Msimpl; reflexivity.
  - simpl; solve_matrix.
  - simpl; solve_matrix.
  - simpl; lma.
  - simpl; rewrite id_transpose_eq; reflexivity.
  - simpl; rewrite hadamard_st; reflexivity.
  - simpl; rewrite X_semantics_transpose; reflexivity.
  - simpl; rewrite Z_semantics_transpose; reflexivity.
  - simpl; rewrite IHzx1, IHzx2; rewrite <- kron_transpose; reflexivity.
  - simpl; rewrite IHzx1, IHzx2; restore_dims; rewrite Mmult_transpose; 
    reflexivity.
Qed.

Lemma semantics_adjoint_comm {nIn nOut} : forall (zx : ZX nIn nOut),
  ⟦ zx † ⟧ = (⟦ zx ⟧) †%M.
Proof.
  intros.
  induction zx.
  - simpl; Msimpl; reflexivity.
  - simpl; solve_matrix.
  - simpl; solve_matrix.
  - simpl; lma.
  - simpl; Msimpl; reflexivity.
  - simpl; lma.
  - simpl; rewrite X_semantics_adj; reflexivity.
  - simpl; rewrite Z_semantics_adj; reflexivity.
  - simpl; fold (zx1†); fold (zx2†); rewrite IHzx1, IHzx2; 
                     rewrite <- kron_adjoint; reflexivity.
  - simpl; fold (zx1†); fold(zx2†); rewrite IHzx1, IHzx2; 
        restore_dims; rewrite Mmult_adjoint; reflexivity.
Qed.

Lemma conjugate_decomp {n m} (zx : ZX n m) : 
  zx ⊼ = zx † ⊤.
Proof.
  induction zx; [reflexivity.. | |];
  unfold adjoint in *; cbn; congruence.
Qed.

Lemma semantics_conjugate_comm {nIn nOut} : forall (zx : ZX nIn nOut),
  ⟦ zx ⊼ ⟧ = (⟦ zx ⟧) †%M ⊤%M.
Proof.
  intros zx.
  rewrite conjugate_decomp.
  now rewrite semantics_transpose_comm, semantics_adjoint_comm.
Qed.

Opaque adjoint.

Reserved Notation "⊙ zx" (at level 0, zx at level 35). (* \odot *) 
Fixpoint color_swap {nIn nOut} (zx : ZX nIn nOut) : ZX nIn nOut := 
  match zx with
  | X n m α   => Z n m α
  | Z n m α   => X n m α
  | zx1 ↕ zx2 => (⊙ zx1) ↕ (⊙ zx2)
  | zx0 ⟷ zx1 => (⊙zx0) ⟷ (⊙zx1)
  | otherwise => otherwise
  end
  where "⊙ zx" := (color_swap zx) : ZX_scope.

Lemma semantics_colorswap_comm {nIn nOut} : forall (zx : ZX nIn nOut),
  ⟦ ⊙ zx ⟧ = nOut ⨂ hadamard × (⟦ zx ⟧) × nIn ⨂ hadamard.
Proof.
  induction zx.
  - simpl; Msimpl; reflexivity.
  - solve_matrix.
  - solve_matrix.
  - simpl.
    Msimpl.
    solve_matrix.
  - simpl; Msimpl; restore_dims; rewrite MmultHH; reflexivity.
  - simpl; Msimpl; restore_dims; rewrite MmultHH; Msimpl; reflexivity.
  - simpl. unfold X_semantics.
    rewrite <- 2 Mmult_assoc.
    rewrite kron_n_mult.
    rewrite 2 Mmult_assoc.
    rewrite kron_n_mult.
    rewrite MmultHH.
    rewrite 2 kron_n_I.
    Msimpl; reflexivity.
  - reflexivity.
  - simpl.
    rewrite IHzx1, IHzx2.
    rewrite 2 kron_n_m_split; try auto with wf_db.
    repeat rewrite <- kron_mixed_product.
    restore_dims.
    reflexivity.
  - simpl.
    rewrite IHzx1, IHzx2.
    rewrite Mmult_assoc.
    restore_dims.
    subst.
    rewrite <- 2 Mmult_assoc with (m ⨂ hadamard) _ _.
    rewrite kron_n_mult.
    rewrite MmultHH.
    rewrite kron_n_I.
    Msimpl.
    repeat rewrite Mmult_assoc.
    reflexivity.
Qed.

Lemma Z_spider_1_1_fusion_eq : forall {nIn nOut} α β, 
  ⟦ (Z_Spider nIn 1 α) ⟷ (Z_Spider 1 nOut β) ⟧ =
  ⟦ Z_Spider nIn nOut (α + β) ⟧.
Proof.
  assert (expnonzero : forall a, exists b, (2 ^ a + (2 ^ a + 0) - 1)%nat = S b).
  { 
    intros.
    destruct (2^a)%nat eqn:E.
      - contradict E.
        apply Nat.pow_nonzero; easy.
      - simpl.
        rewrite <- plus_n_Sm.
        exists (n + n)%nat.
        lia.
  }
  intros.
  prep_matrix_equality.
  simpl.
  unfold Mmult.
  simpl.
  rewrite Cplus_0_l.
  destruct nIn, nOut.
  - simpl.
    destruct x,y; [simpl; autorewrite with Cexp_db | | | ]; lca.
  - destruct x,y; simpl; destruct (expnonzero nOut); 
                       rewrite H; [ lca | lca | | ].
    + destruct (x =? x0)%nat.
      * simpl.
        autorewrite with Cexp_db.
        lca.
      * simpl.
        lca.
    + destruct (x =? x0)%nat; lca.
  - destruct x,y; simpl; destruct (expnonzero nIn); 
                    rewrite H; [lca | | lca | lca].
    + destruct (y =? x)%nat; [autorewrite with Cexp_db | ]; lca.
  - destruct x,y; simpl; destruct (expnonzero nIn), (expnonzero nOut); 
                                       rewrite H,H0; [lca | lca | | ].
    + destruct (x =? x1)%nat; lca.
    + destruct (x =? x1)%nat, (y =? x0)%nat; [| lca | lca | lca].
      autorewrite with Cexp_db.
      lca.
Qed.

Lemma z_1_1_pi_σz :
	⟦ Z 1 1 PI ⟧ = σz.
Proof. solve_matrix. autorewrite with Cexp_db. lca. Qed.

Lemma x_1_1_pi_σx :
	⟦ X 1 1 PI ⟧ = σx.
Proof. 
	simpl. 
	unfold X_semantics. simpl; Msimpl. solve_matrix; autorewrite with Cexp_db. 
	all: C_field_simplify; [lca | C_field].
Qed.

Definition zx_triangle : ZX 1 1 :=
	(X 1 1 (PI/2) ⟷ Z 1 1 (PI/4)) ⟷ ((Z 0 1 (PI/4) ↕ —) ⟷ X 2 1 0) ⟷ (Z 1 2 0 ⟷ (— ↕ (X 1 2 0 ⟷ (Z 1 0 (-PI/4) ↕ Z 1 0 (-PI/4))))).

Definition zx_triangle_left : ZX 1 1 :=
	(zx_triangle ⊤)%ZX.

Notation "▷" := zx_triangle : ZX_scope. (* \triangleright *)
Notation "◁" := zx_triangle_left : ZX_scope. (* \triangleleft *)

Lemma triangle_step_1 :
	⟦ X 1 1 (PI/2) ⟷ Z 1 1 (PI/4) ⟧ = 
	/ (√ 2)%R .* (∣0⟩ × ⟨+∣) .+ 
	Cexp (PI / 2) * /(√2)%R .* (∣0⟩ × ⟨-∣) .+ 
	Cexp (PI / 4) * /(√2)%R .* (∣1⟩ × ⟨+∣) .+ 
	Cexp (PI / 2) * Cexp (PI / 4) * - /(√2)%R .* (∣1⟩ × ⟨-∣).
Proof.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.
	rewrite <- 2 (Mmult_assoc (⟨0∣)).
	rewrite <- 2 (Mmult_assoc (⟨1∣)).
	restore_dims.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	lma.
Qed.
	
Lemma triangle_step_2 : 
	⟦ Z 0 1 (PI/4) ↕ — ⟷ X 2 1 0 ⟧ = 
	1/(√2)%R .* ∣0⟩⟨0∣ .+ 
	Cexp (PI/4)/(√2)%R .* ∣0⟩⟨1∣ .+ 
	Cexp (PI/4)/(√2)%R .* ∣1⟩⟨0∣ .+ 
	1/(√2)%R .* ∣1⟩⟨1∣.
		(* (((1 + Cexp (PI/4)) / (√2)%R) .* ∣+⟩ × ⟨+∣ .+ 
		 ((1 - Cexp (PI/4)) / (√2)%R) .* ∣-⟩ × ⟨-∣). *)
Proof.
	rewrite ZX_semantic_equiv.
	unfold_dirac_spider.
	Msimpl.
	rewrite kron_plus_distr_r.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	rewrite Mmult_assoc.
	rewrite (kron_mixed_product (⟨+∣) (⟨+∣)).
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.
	repeat rewrite (kron_mixed_product (⟨+∣) (⟨+∣)).
	repeat rewrite (kron_mixed_product (⟨-∣) (⟨-∣)).
	autorewrite with ketbra_mult_db.
	repeat rewrite Mscale_kron_dist_l.
	Msimpl.
	autorewrite with scalar_move_db.
	unfold braplus, braminus.
	unfold xbasis_plus, xbasis_minus.
	autorewrite with scalar_move_db.
	rewrite Cexp_0.
	Msimpl.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	rewrite Cmult_1_l.
	replace ((/ (√ 2)%R + Cexp (PI / 4) * / (√ 2)%R) * / (√ 2)%R *
/ (√ 2)%R) with ((1 + Cexp (PI / 4)) * / ((√2)%R * 2)) by C_field.
	replace ((/ (√ 2)%R + Cexp (PI / 4) * - / (√ 2)%R) * / (√ 2)%R * / (√ 2)%R) with ((1 - Cexp (PI/4)) / ((√2)%R * 2)) by C_field.
	remember ((1 + Cexp (PI/4)) * / ((√2)%R * 2)) as v1.
	remember ((C1 - Cexp (PI / 4)) / ((√ 2)%R * C2)) as v2.
	repeat rewrite Mscale_plus_distr_r.
	repeat rewrite Mscale_assoc.
	replace (v2 * -1 * -1) with v2 by lca.
	replace (v2 * -1) with (- v2) by lca.
	replace (v1 .* ∣0⟩⟨0∣ .+ v1 .* ∣1⟩⟨0∣ .+ (v1 .* ∣0⟩⟨1∣ .+ v1 .* ∣1⟩⟨1∣) .+ (v2 .* ∣0⟩⟨0∣ .+ - v2 .* ∣1⟩⟨0∣ .+ (- v2 .* ∣0⟩⟨1∣ .+ v2 .* ∣1⟩⟨1∣))) with ((v1 + v2) .* ∣0⟩⟨0∣ .+ (v1 - v2) .* ∣0⟩⟨1∣ .+ (v1 - v2) .* ∣1⟩⟨0∣ .+ (v1 + v2) .* ∣1⟩⟨1∣) by lma.
	assert (Hv0 : v1 + v2 = C1 / (√2)%R).
	{ subst; C_field_simplify. lca. C_field. }
	assert (Hv1 : v1 - v2 = Cexp (PI/4) / (√2)%R).
	{ subst; C_field_simplify. lca. C_field. }
	rewrite Hv0, Hv1.
	easy.
Qed.

Lemma triangle_step_3 :
 ⟦ Z 1 2 0 ⟷ (— ↕ (X 1 2 0 ⟷ (Z 1 0 (-PI/4) ↕ Z 1 0 (-PI/4)))) ⟧ = (1 + Cexp (-PI/4)^2) / (√2)%R .* ∣0⟩⟨0∣ .+ 
 (√2)%R * Cexp (-PI/4) .* ∣1⟩⟨1∣.
Proof.
	assert (H : ⟦ (X 1 2 0 ⟷ (Z 1 0 (-PI/4) ↕ Z 1 0 (-PI/4))) ⟧ = (1 + Cexp (-PI/4))^2 / 2 .* ⟨+∣ .+ 
	(1 - Cexp (-PI/4))^2 / 2 .* ⟨-∣).
	{ 
		rewrite ZX_semantic_equiv.
		unfold_dirac_spider.
		rewrite Cexp_0.
		Msimpl.
		rewrite Mmult_plus_distr_l.
		rewrite <- 2 Mmult_assoc.
		rewrite 2 kron_mixed_product.
		rewrite 2 Mmult_plus_distr_r.
		autorewrite with scalar_move_db.
		autorewrite with ketbra_mult_db.
		autorewrite with scalar_move_db.
		rewrite kron_1_l by auto with wf_db.
		rewrite 2 Mmult_1_l by auto with wf_db.
		apply Mplus_simplify.
		- apply Mscale_simplify; try auto.
			C_field.
		- apply Mscale_simplify; try auto.
			C_field.
	}
	rewrite zx_compose_spec.
	rewrite (zx_stack_spec _ _ _ _ —).
	rewrite H.
	clear H.
	rewrite 2 ZX_semantic_equiv.
	unfold_dirac_spider.
	rewrite Cexp_0.
	Msimpl.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite Mmult_plus_distr_l.
	rewrite <- 2 Mmult_assoc.
	rewrite 2 kron_mixed_product.
	Msimpl.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	autorewrite with ketbra_mult_db.
	autorewrite with scalar_move_db.
	Msimpl.
	apply Mplus_simplify.
	- apply Mscale_simplify; try auto.
		lca.
	- apply Mscale_simplify; try auto.
		C_field_simplify.
		rewrite Rplus_0_l.
		repeat rewrite Rmult_0_l.
		repeat rewrite Rmult_0_r.
		lca.
		C_field.
Qed.

Lemma zx_triangle_semantics : 
	⟦ ▷ ⟧ = ∣0⟩⟨0∣ .+ ∣1⟩⟨0∣ .+ ∣1⟩⟨1∣.
Proof.
	unfold zx_triangle.
	remember (X 1 1 (PI / 2) ⟷ Z 1 1 (PI / 4)) as t_1.
	remember (Z 0 1 (PI / 4) ↕ — ⟷ X 2 1 0) as t_2.
	remember (Z 1 2 0 ⟷ (— ↕ (X 1 2 0 ⟷ (Z 1 0 (- PI / 4) ↕ Z 1 0 (- PI / 4))))) as t_3.
	simpl.
	rewrite Heqt_1.
	rewrite triangle_step_1.
	rewrite Heqt_2.
	rewrite zx_compose_spec.
	rewrite <- zx_compose_spec.
	rewrite triangle_step_2.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_plus_distr_r.
	repeat rewrite <- (Mmult_plus_distr_l _ _ _ (⟦ t_3 ⟧)).
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.
	repeat rewrite <- (Mmult_assoc _ (∣0⟩)).
	repeat rewrite <- (Mmult_assoc _ (∣1⟩)).
	autorewrite with ketbra_mult_db.
	Msimpl.
	repeat rewrite Mscale_plus_distr_l.
	repeat rewrite Mscale_plus_distr_r.
	repeat rewrite Mscale_assoc.
	replace (/(√2)%R * (C1/(√2)%R)) with (/2) by C_field.
	replace (/ (√ 2)%R * (Cexp (PI / 4) / (√ 2)%R)) with (Cexp (PI/4)/2) by C_field.
	replace (Cexp (PI / 2) * / (√ 2)%R * (C1 / (√ 2)%R)) with (Cexp (PI/2)/2) by C_field.
	replace (Cexp (PI / 2) * / (√ 2)%R * (Cexp (PI / 4) / (√ 2)%R)) with (Cexp ((3 * PI) / 4)/2) by (autorewrite with Cexp_db; C_field_simplify; [lca | C_field ]).
	replace (Cexp (PI / 4) * / (√ 2)%R * (Cexp (PI / 4) / (√ 2)%R)) with (Cexp (PI/2) / 2) by (autorewrite with Cexp_db; C_field_simplify; [lca | C_field ]).
	replace (Cexp (PI / 4) * / (√ 2)%R * (C1 / (√ 2)%R)) with (Cexp (PI/4)/2) by C_field.
	replace (Cexp (PI / 2) * Cexp (PI / 4) * - / (√ 2)%R *
(Cexp (PI / 4) / (√ 2)%R)) with (/ 2) by (autorewrite with Cexp_db; C_field_simplify; [lca | C_field ]).
	replace (Cexp (PI / 2) * Cexp (PI / 4) * - / (√ 2)%R * (C1 / (√ 2)%R)) with (-(Cexp ((3 * PI)/4)/2)) by (autorewrite with Cexp_db; C_field_simplify; [lca | C_field ]).
	remember (/ 2) as v1.
	remember (Cexp (PI/4)/2) as v2.
	remember (Cexp(PI/2)/2) as v3.
	remember (Cexp (3 * PI/4)/2) as v4.
	replace (v1 .* (∣0⟩ × ⟨+∣) .+ v2 .* (∣1⟩ × ⟨+∣) .+ (v3 .* (∣0⟩ × ⟨-∣) .+ v4 .* (∣1⟩ × ⟨-∣)) .+ (v3 .* (∣0⟩ × ⟨+∣) .+ v2 .* (∣1⟩ × ⟨+∣)) .+ (v1 .* (∣0⟩ × ⟨-∣) .+ - v4 .* (∣1⟩ × ⟨-∣))) with ((v1 + v3) .* (∣0⟩ × ⟨+∣) .+ 2 * v2 .* (∣1⟩ × ⟨+∣) .+ ((v1 + v3) .* (∣0⟩ × ⟨-∣))) by lma.
	rewrite Heqt_3.
	rewrite triangle_step_3.
	repeat rewrite Mmult_plus_distr_l.
	repeat rewrite Mmult_plus_distr_r.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_assoc.
	repeat rewrite <- (Mmult_assoc _ (∣0⟩)).
	repeat rewrite <- (Mmult_assoc _ (∣1⟩)).
	autorewrite with ketbra_mult_db.
	Msimpl.
	repeat rewrite Mscale_assoc.
	rewrite Heqv2.
	replace (C2 * (Cexp (PI / 4) / C2) * ((√ 2)%R * Cexp (- PI / 4))) with (1 * (√2)%R) by (autorewrite with Cexp_db; C_field_simplify; [lca | C_field]).
	rewrite Cmult_1_l.
	replace ((v1 + v3) * ((1 + Cexp (-PI/4)^2)/(√2)%R)) with (/(√2)%R) by (rewrite Heqv1, Heqv3; autorewrite with Cexp_db; C_field_simplify; [ | C_field]; simpl; C_field_simplify; [lca | C_field]).
	unfold braplus, braminus.
	autorewrite with scalar_move_db.
	repeat rewrite Mmult_plus_distr_l.
	autorewrite with scalar_move_db.
	repeat rewrite Mscale_plus_distr_r.
	rewrite Mscale_assoc.
	replace (/ (√2)%R * / (√2)%R) with (/2) by C_field.
	replace ((√2)%R * / (√2)%R) with (C1) by C_field.
	lma.
Qed.
	
Global Opaque zx_triangle.

Lemma zx_triangle_left_semantics :
	⟦ ◁ ⟧ = ∣0⟩⟨0∣ .+ ∣0⟩⟨1∣ .+ ∣1⟩⟨1∣.
Proof.
	unfold zx_triangle_left.
	rewrite semantics_transpose_comm.
	rewrite zx_triangle_semantics.
	repeat rewrite Mplus_transpose.
	repeat rewrite Mmult_transpose.
	rewrite bra0transpose, bra1transpose, ket0transpose, ket1transpose.
	easy.
Qed.

Global Opaque zx_triangle_left.

Local Close Scope ZX_scope.
