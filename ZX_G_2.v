Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.VectorStates.
Require Export ZX.
Require Export ZX_G.
Require Export Gates.
Require Export GateRules.
Require Export Rules.
Require Export VyZX.Proportional.
Require Import Setoid.

Local Declare Scope G2_ZX_scope.
Local Open Scope G2_ZX_scope.

Local Open Scope R_scope.
Inductive G2_ZX : nat -> nat -> Type :=
  | G2_Empty : G2_ZX 0 0
  | G2_Z_Spider_In0 (α : R) : G2_ZX 1 0
  | G2_Z_Spider_Out0 (α : R) : G2_ZX 0 1
  | G2_Z_Spider_1 (α : R) : G2_ZX 1 1 (* Required to build wire construct *)
  | G2_Z_Spider_In2 (α : R) : G2_ZX 1 2
  | G2_Z_Spider_Out2 (α : R) : G2_ZX 2 1
  | G2_Cap : G2_ZX 0 2
  | G2_Cup : G2_ZX 2 0
  | G2_Stack {nIn0 nIn1 nOut0 nOut1} (zx0 : G2_ZX nIn0 nOut0) (zx1 : G2_ZX nIn1 nOut1) :
        G2_ZX (nIn0 + nIn1) (nOut0 + nOut1)
  | G2_Compose {nIn nMid nOut} (zx0 : G2_ZX nIn nMid) (zx1 : G2_ZX nMid nOut) : G2_ZX nIn nOut.
Local Close Scope R_scope.

Notation "⦰G2" := G2_Empty. (* \revemptyset *)
Notation "⊂G2" := G2_Cap. (* \subset *)
Notation "⊃G2" := G2_Cup. (* \supset *)
Infix "⟷G2" := G2_Compose (left associativity, at level 40). (* \longleftrightarrow *)
Infix "↕G2" := G2_Stack (left associativity, at level 40). (* \updownarrow *)

Fixpoint G2_ZX_semantics {nIn nOut} (zx : G2_ZX nIn nOut) : 
  Matrix (2 ^ nOut) (2 ^nIn) := 
  match zx with
  | ⦰G2 => G_ZX_semantics ⦰G
  | G2_Z_Spider_In0 α => G_ZX_semantics (G_Z_Spider_In 0 α)
  | G2_Z_Spider_Out0 α => G_ZX_semantics (G_Z_Spider_Out 0 α)
  | G2_Z_Spider_1 α => G_ZX_semantics (G_Z_Spider_In 1 α)
  | G2_Z_Spider_In2 α => G_ZX_semantics (G_Z_Spider_In 2 α)
  | G2_Z_Spider_Out2 α => G_ZX_semantics (G_Z_Spider_Out 2 α)
  | G2_Cap => G_ZX_semantics (G_Cap)
  | G2_Cup => G_ZX_semantics (G_Cup)
  | zx0 ↕G2 zx1 => (G2_ZX_semantics zx0) ⊗ (G2_ZX_semantics zx1)
  | @G2_Compose _ nMid _ zx0 zx1 => (G2_ZX_semantics zx1) × (nMid ⨂ hadamard) × (G2_ZX_semantics zx0)
  end.

Fixpoint G2_ZX_to_G_ZX {nIn nOut} (zx : G2_ZX nIn nOut) : G_ZX nIn nOut :=
  match zx with
  | ⦰G2 => ⦰G
  | G2_Z_Spider_In0 α => G_Z_Spider_In 0 α
  | G2_Z_Spider_Out0 α => G_Z_Spider_Out 0 α
  | G2_Z_Spider_1 α => G_Z_Spider_In 1 α
  | G2_Z_Spider_In2 α => G_Z_Spider_In 2 α
  | G2_Z_Spider_Out2 α => G_Z_Spider_Out 2 α
  | G2_Cap => G_Cap
  | G2_Cup => G_Cup
  | zx0 ↕G2 zx1 => (G2_ZX_to_G_ZX zx0) ↕G (G2_ZX_to_G_ZX zx1)
  | zx0 ⟷G2 zx1 => (G2_ZX_to_G_ZX zx0) ⟷G (G2_ZX_to_G_ZX zx1)
  end.

Local Opaque ZX_semantics.
Lemma WF_G2_ZX : forall nIn nOut (zx : G2_ZX nIn nOut), WF_Matrix (G2_ZX_semantics zx).
Proof.
  intros.
  induction zx; simpl; try restore_dims; try auto with wf_db.
Qed.
Local Transparent ZX_semantics.

Global Hint Resolve WF_G2_ZX : wf_db.

Definition G2_proportional {nIn nOut} (zx0 : G2_ZX nIn nOut) (zx1 : G2_ZX nIn nOut) :=
  proportional_general G2_ZX_semantics zx0 zx1.

Infix "∝G2" := G2_proportional (at level 70).

Lemma G2_proportional_refl : forall {nIn nOut} (zx : G2_ZX nIn nOut), zx ∝G2 zx.
Proof.
  intros.
  apply proportional_general_refl.
Qed.

Lemma G2_proportional_symm : forall {nIn nOut} (zx0 zx1 : G2_ZX nIn nOut),
  zx0 ∝G2 zx1 -> zx1 ∝G2 zx0.
Proof.
  intros.
  apply proportional_general_symm; assumption.
Qed.

Lemma G2_proportional_trans : forall {nIn nOut} (zx0 zx1 zx2 : G2_ZX nIn nOut),
  zx0 ∝G2 zx1 -> zx1 ∝G2 zx2 -> zx0 ∝G2 zx2.
Proof.
  intros.
  apply (proportional_general_trans _ _ _ G2_ZX_semantics zx0 zx1 zx2); assumption.
Qed.

Add Parametric Relation (nIn nOut : nat) : (G2_ZX nIn nOut) (@G2_proportional nIn nOut)
  reflexivity proved by G2_proportional_refl
  symmetry proved by G2_proportional_symm
  transitivity proved by G2_proportional_trans
  as zx_g_prop_equiv_rel.

Lemma G2_stack_compat :
  forall nIn0 nOut0 nIn1 nOut1,
    forall zx0 zx1 : G2_ZX nIn0 nOut0, zx0 ∝G2 zx1 ->
    forall zx2 zx3 : G2_ZX nIn1 nOut1, zx2 ∝G2 zx3 ->
    zx0 ↕G2 zx2 ∝G2 zx1 ↕G2 zx3.
Proof.
  intros.
  destruct H; destruct H; destruct H0; destruct H0.
  exists (x * x0).
  split.
  - simpl; rewrite H; rewrite H0.
    lma.
  - apply Cmult_neq_0; try assumption.
Qed.

Add Parametric Morphism (nIn0 nOut0 nIn1 nOut1 : nat) : (@G2_Stack nIn0 nIn1 nOut0 nOut1)
  with signature (@G2_proportional nIn0 nOut0) ==> (@G2_proportional nIn1 nOut1) ==> 
                 (@G2_proportional (nIn0 + nIn1) (nOut0 + nOut1)) as G2_stack_mor.
Proof. apply G2_stack_compat; assumption. Qed.

Local Open Scope C_scope.

Theorem G2_ZX_to_G_ZX_consistent : forall nIn nOut (zx : G2_ZX nIn nOut),
  G2_ZX_semantics zx = (G_ZX_semantics (G2_ZX_to_G_ZX zx)).
Proof.
  intros.
  induction zx; try auto;
  (* Composition cases *)
  simpl; rewrite IHzx1, IHzx2; reflexivity.
Qed.

Definition G2_Wire := G2_Z_Spider_1 0.

Local Opaque G_ZX_semantics.
Local Transparent G_Wire.
Lemma G2_wire_identity_semantics : G2_ZX_semantics G2_Wire = I 2.
Proof.
  simpl.
  rewrite <- G_wire_identity_semantics.
  unfold G_Wire.
  reflexivity.
Qed.
Local Transparent G_ZX_semantics.
Local Opaque G_Wire.
Global Opaque G2_Wire.

Definition StackWire {nIn nOut} (zx : G2_ZX nIn nOut) : G2_ZX (S nIn) (S nOut) := G2_Wire ↕G2 zx.

Fixpoint G_Spider_In_to_G2_Spiders nOut α: G2_ZX 1 nOut :=
  match nOut with
  | 0%nat => G2_Z_Spider_In0 α
  | S nOut' => G2_Z_Spider_In2 α ⟷G2 (StackWire G2_Wire) ⟷G2 StackWire (G_Spider_In_to_G2_Spiders nOut' 0%R)
  end.

Local Opaque G_ZX_semantics.
Lemma G_Spider_In_to_G2_Spiders_consistent : forall nOut α, G_ZX_semantics (G_Z_Spider_In nOut α) = G2_ZX_semantics (G_Spider_In_to_G2_Spiders nOut α).
Proof.
  intro nOut.
  induction nOut; intros.
  - simpl.
    reflexivity.
  - simpl.
    repeat rewrite G2_wire_identity_semantics.
    rewrite id_kron.
    repeat rewrite Mmult_1_l; try auto with wf_db.
    repeat rewrite kron_1_l; try auto with wf_db.
    repeat rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc (hadamard ⊗ hadamard) (hadamard ⊗ hadamard) _).
    replace ((hadamard ⊗ hadamard × (hadamard ⊗ hadamard))) with (I 4) by solve_matrix.
    Msimpl; restore_dims; try auto with wf_db.
    specialize (IHnOut 0%R).
    rewrite <- IHnOut.
Local Transparent G_ZX_semantics.    
    simpl.
    unfold_spider.
    assert (contra : forall a, (2^S a - 1 <> 0)%nat).
    { intros; simpl. 
      destruct (2^a)%nat eqn:Ea. 
      - apply Nat.pow_nonzero in Ea; [destruct Ea | easy].
      - simpl; rewrite <- plus_n_Sm; easy.
    }
    unfold Mmult.
    prep_matrix_equality.
    destruct x eqn:Hx,y eqn:Hy; rewrite Nat.pow_1_r; simpl.
    2, 3, 4 :  rewrite Nat.add_0_r;
    rewrite double_pow;
    rewrite Nat.add_1_r; 
    destruct (2 ^ (S nOut) - 1)%nat eqn:He; [ contradict He; apply contra | destruct He ];
    unfold kron;
    repeat rewrite Nat.div_0_l; try apply Nat.pow_nonzero; auto;
    repeat rewrite Nat.mod_0_l; try apply Nat.pow_nonzero; auto;
    simpl.
    + repeat rewrite Cmult_0_r.
      unfold kron.
      rewrite Nat.mod_0_l; [ | apply Nat.pow_nonzero; auto ].
      rewrite Nat.div_0_l; [ | apply Nat.pow_nonzero; auto ].
      rewrite Nat.mod_0_l; [| auto ].
      rewrite Nat.div_0_l; [| auto ].
      unfold I.
      simpl.
      lca.
    + repeat rewrite Cmult_0_r.
      unfold I.
      simpl.
      lca.
    + repeat rewrite andb_false_r.
      repeat rewrite Cmult_0_r.
      unfold I.
      destruct (S n / 2 ^ nOut =? 0) eqn:HSn2nOut; [ rewrite Nat.eqb_eq in HSn2nOut; rewrite HSn2nOut; simpl | simpl; rewrite Cmult_0_l; lca].
      destruct (S n mod 2 ^ nOut) eqn:Hsnmod; [ | lca].
      assert (S n = 0).
      {
        Search ( _ mod _ = 0).
        rewrite <- Nat.div_exact in Hsnmod; [ | apply Nat.pow_nonzero; auto].
        rewrite HSn2nOut in Hsnmod.
        rewrite Hsnmod.
        lia.
      }
      discriminate H.
    + destruct n0; simpl; [ destruct (n =? n1) eqn:Hnn1 | rewrite andb_false_r ]; simpl; repeat rewrite Cmult_0_r; [ | | lca]; admit.
      * unfold I.
        destruct ((S n / 2 ^ nOut =? 1)) eqn:Hsn; [ rewrite Nat.eqb_eq in Hsn | rewrite Cmult_0_l]; simpl.
        -- rewrite Hsn.
           simpl.
           destruct (S n mod 2 ^ nOut) eqn:HSnmod.
           destruct nOut.
           ++ rewrite Nat.pow_0_r.
              simpl.
              rewrite Cexp_0.
              lca.
           ++ destruct (0 =? 2 ^ S nOut - 1) eqn:HSnOut; [ rewrite Nat.eqb_eq in HSnOut; symmetry in HSnOut; contradict HSnOut; apply contra | ].
              simpl.
              admit.
           ++ destruct (S n0 =? 2 ^ nOut - 1) eqn:Hsn02nOut; [ simpl |].
              ** autorewrite with Cexp_db.
                 lca.
              ** simpl. 
                 rewrite <- HSnmod in Hsn02nOut.
                 subst.
                 Search (_ mod _ = _).
                 contradict Hsn02nOut.
                 apply not_false_iff_true.
                 rewrite Nat.eqb_eq.
                 assert ((S n / 2 ^ nOut)%nat = 1 /\ S n mod 2 ^ nOut = (2 ^ nOut - 1)%nat -> S n mod 2 ^ nOut = (2 ^ nOut - 1)%nat).
                 {
                   intros. destruct H. assumption.
                 }
                 apply H.
                 apply divmod_decomp.
                 --- admit.
                 --- admit.
                 --- rewrite Nat.mul_1_l.
                     Search (_ - 1)%nat.
                     admit.
Abort.
(* Other start
    solve_matrix.
    + simpl.
      rewrite Nat.div_0_l; [simpl | apply Nat.pow_nonzero; auto].
      rewrite Nat.mod_0_l; [lca | apply Nat.pow_nonzero; auto].
    + rewrite Nat.add_0_r.
      rewrite double_pow.
      rewrite Nat.add_1_r.
      destruct (2 ^ S nOut - 1)%nat eqn:He; [contradict He; apply contra | destruct He].
      simpl.
      rewrite Nat.div_0_l; [simpl; lca | apply Nat.pow_nonzero; auto].
    + destruct (S x / 2 ^ nOut =? 0) eqn:HSx2nOut; simpl; [rewrite Nat.eqb_eq in HSx2nOut; rewrite HSx2nOut | lca].
      simpl.
      Search (_ mod _ = _)%nat.
    + rewrite Nat.add_0_r.
      rewrite double_pow.
      rewrite Nat.add_1_r.
      destruct (2 ^ S nOut - 1)%nat eqn:He; [contradict He; apply contra | destruct He].
      destruct (x =? n) eqn:Hxn, (y =? 0) eqn:Hy0; simpl; [| lca | | lca]; rewrite andb_true_r;
      destruct (S x / 2 ^ nOut =? 1) eqn:HSx2nOut;
      simpl.
      * rewrite Nat.eqb_eq in HSx2nOut.
        rewrite HSx2nOut.
        simpl.
        destruct (S x mod 2 ^ nOut)%nat eqn:HSxMod2nOut; simpl;
        destruct (2 ^ nOut - 1)%nat eqn:H2nOut1l;
        [ autorewrite with Cexp_db; lca | | | ].
        --  Search "divmod_spec".
            Search (_ mod _ = 0).
            
Abort. *)

Fixpoint G_Spider_Out_to_G2_Spiders nIn α: G2_ZX nIn 1 :=
  match nIn with
  | 0%nat => G2_Z_Spider_Out0 α
  | S nIn' => (StackWire (G_Spider_Out_to_G2_Spiders nIn' R0)) ⟷G2 (StackWire G2_Wire) ⟷G2 G2_Z_Spider_Out2 R0
  end.

Lemma G_Spider_Out_to_G2_Spiders_consistent : forall nIn α, G_ZX_semantics (G_Z_Spider_Out nIn α) = G2_ZX_semantics (G_Spider_Out_to_G2_Spiders nIn α).
Admitted.


Fixpoint G_ZX_to_G2_ZX {nIn nOut} (zx : G_ZX nIn nOut) : G2_ZX nIn nOut :=
  match zx with
  | G_Empty => G2_Empty
  | G_Z_Spider_In nOut α => G_Spider_In_to_G2_Spiders nOut α
  | G_Z_Spider_Out nIn α => G_Spider_Out_to_G2_Spiders nIn α
  | G_Cap => G2_Cap
  | G_Cup => G2_Cup
  | zx0 ↕G zx1 => (G_ZX_to_G2_ZX zx0) ↕G2 (G_ZX_to_G2_ZX zx1)
  | zx0 ⟷G zx1 => (G_ZX_to_G2_ZX zx0) ⟷G2 (G_ZX_to_G2_ZX zx1)
  end.

Theorem G_ZX_to_G2_ZX_consistent : forall nIn nOut (zx : G_ZX nIn nOut),
  G_ZX_semantics zx = (G2_ZX_semantics (G_ZX_to_G2_ZX zx)).
Proof.
  intros.
  induction zx; try auto;
  (* Composition *)
  try (simpl;
  rewrite IHzx1, IHzx2;
  reflexivity). 
  (* Interesting case: Spider fusion *)
  apply G_Spider_In_to_G2_Spiders_consistent.
  apply G_Spider_Out_to_G2_Spiders_consistent.
Qed.

Definition ZX_to_G2_ZX {nIn nOut} (zx : ZX nIn nOut) := G_ZX_to_G2_ZX (ZX_to_G_ZX zx).
Definition G2_ZX_to_ZX {nIn nOut} (zx : G2_ZX nIn nOut) := G_ZX_to_ZX (G2_ZX_to_G_ZX zx).

Theorem G2_ZX_to_ZX_consistent : forall nIn nOut (zx : G2_ZX nIn nOut),
  exists (θ : R), G2_ZX_semantics zx = (Cexp θ) .* (ZX_semantics (G2_ZX_to_ZX zx)).
Proof.
  intros.
  rewrite G2_ZX_to_G_ZX_consistent.
  apply G_ZX_to_ZX_consistent.
Qed.

Theorem ZX_to_ZX_G_consistent : forall nIn nOut (zx : ZX nIn nOut),
  exists (θ : R), ZX_semantics zx = (Cexp θ) .* (G2_ZX_semantics (ZX_to_G2_ZX zx)).
Proof.
  intros.
  simpl.
  unfold ZX_to_G2_ZX.
  rewrite <- G_ZX_to_G2_ZX_consistent.
  apply ZX_to_ZX_G_consistent.
Qed.

Lemma ZX_G2_ZX_H_involutive : forall nIn nOut (zx : G_ZX nIn nOut), G2_ZX_to_G_ZX (G_ZX_to_G2_ZX zx) ∝G zx.
Proof.
  intros.
  prop_exist_non_zero 1%R.
  Msimpl.
  simpl.
  rewrite <- G2_ZX_to_G_ZX_consistent.
  rewrite <- G_ZX_to_G2_ZX_consistent.
  reflexivity.
Qed.

Lemma ZX_G_ZX_G_involutive : forall nIn nOut (zx : G2_ZX nIn nOut), G_ZX_to_G2_ZX (G2_ZX_to_G_ZX zx) ∝G2 zx.
Proof.
  intros.
  prop_exist_non_zero 1%R.
  Msimpl.
  simpl.
  rewrite <- G_ZX_to_G2_ZX_consistent.
  rewrite <- G2_ZX_to_G_ZX_consistent.
  reflexivity.
Qed.

Lemma G_ZX_to_G2_ZX_compat : forall nIn nOut (zx0 zx1 : G_ZX nIn nOut), 
  zx0 ∝G zx1 -> (G_ZX_to_G2_ZX zx0) ∝G2 (G_ZX_to_G2_ZX zx1).
Proof.
  intros.
  destruct H.
  destruct H.
  unfold H_proportional.
  unfold proportional_general.
  exists x.
  repeat rewrite <- G_ZX_to_G2_ZX_consistent.
  split; assumption.
Qed.

Lemma G2_ZX_to_G_ZX_compat : forall nIn nOut (zx0 zx1 : G2_ZX nIn nOut), 
  zx0 ∝G2 zx1 -> (G2_ZX_to_G_ZX zx0) ∝G (G2_ZX_to_G_ZX zx1).
Proof.
  intros.
  destruct H.
  destruct H.
  unfold H_proportional.
  unfold proportional_general.
  exists x.
  repeat rewrite <- G2_ZX_to_G_ZX_consistent.
  split; assumption.
Qed.

Lemma ZX_to_G2_ZX_compat : forall nIn nOut (zx0 zx1 : ZX nIn nOut), 
  zx0 ∝ zx1 -> (ZX_to_G2_ZX zx0) ∝G2 (ZX_to_G2_ZX zx1).
Proof.
  intros.
  apply G_ZX_to_G2_ZX_compat.
  apply ZX_to_G_ZX_compat.
  assumption.
Qed.

Lemma G2_ZX_to_ZX_compat : forall nIn nOut (zx0 zx1 : G2_ZX nIn nOut), 
  zx0 ∝G2 zx1 -> (G2_ZX_to_ZX zx0) ∝ (G2_ZX_to_ZX zx1).
Proof.
  intros.
  apply G_ZX_to_ZX_compat.
  apply G2_ZX_to_G_ZX_compat.
  assumption.
Qed.

Add Parametric Morphism (nIn nOut : nat) : (@ZX_to_G2_ZX nIn nOut)
  with signature (@proportional nIn nOut) ==> (@G2_proportional nIn nOut) as ZX_to_G2_ZX_mor.
Proof. apply ZX_to_G2_ZX_compat. Qed.

Add Parametric Morphism (nIn nOut : nat) : (@G2_ZX_to_ZX nIn nOut)
  with signature (@G2_proportional nIn nOut) ==> (@proportional nIn nOut) as G2_ZX_to_ZX_mor.
Proof. apply G2_ZX_to_ZX_compat. Qed. 

Add Parametric Morphism (nIn nOut : nat) : (@G_ZX_to_G2_ZX nIn nOut)
  with signature (@G_proportional nIn nOut) ==> (@G2_proportional nIn nOut) as G_ZX_to_G2_ZX_mor.
Proof. apply G_ZX_to_G2_ZX_compat. Qed.

Add Parametric Morphism (nIn nOut : nat) : (@G2_ZX_to_G_ZX nIn nOut)
  with signature (@G2_proportional nIn nOut) ==> (@G_proportional nIn nOut) as G2_ZX_to_G_ZX_mor.
Proof. apply G2_ZX_to_G_ZX_compat. Qed. 

Lemma G2_ZX_ZX_involutive : forall nIn nOut (zx : ZX nIn nOut), G2_ZX_to_ZX (ZX_to_G2_ZX zx) ∝ zx.
Proof.
  intros.
  Msimpl.
  simpl.
  unfold ZX_to_G2_ZX.
  unfold G2_ZX_to_ZX.
  rewrite ZX_G2_ZX_H_involutive.
  apply G_ZX_ZX_involutive.
Qed.

Lemma ZX_G2_ZX_involutive : forall nIn nOut (zx : G2_ZX nIn nOut), ZX_to_G2_ZX (G2_ZX_to_ZX zx) ∝G2 zx.
Proof.
  intros.
  Msimpl.
  simpl.
  unfold ZX_to_G2_ZX.
  unfold G2_ZX_to_ZX.
  rewrite ZX_G_ZX_involutive.
  apply ZX_G_ZX_G_involutive.
Qed.

