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
  | G2_Z_Spider_1_0 (α : R) : G2_ZX 1 0
  | G2_Z_Spider_0_1 (α : R) : G2_ZX 0 1
  | G2_Z_Spider_1_1 (α : R) : G2_ZX 1 1 (* Required to build wire construct *)
  | G2_Z_Spider_1_2 (α : R) : G2_ZX 1 2
  | G2_Z_Spider_2_1 (α : R) : G2_ZX 2 1
  | G2_Cap : G2_ZX 0 2
  | G2_Cup : G2_ZX 2 0
  | G2_Swap : G2_ZX 2 2
  | G2_Stack {nIn0 nIn1 nOut0 nOut1} (zx0 : G2_ZX nIn0 nOut0) (zx1 : G2_ZX nIn1 nOut1) :
        G2_ZX (nIn0 + nIn1) (nOut0 + nOut1)
  | G2_Compose {nIn nMid nOut} (zx0 : G2_ZX nIn nMid) (zx1 : G2_ZX nMid nOut) : G2_ZX nIn nOut.
Local Close Scope R_scope.

Notation "⦰G2" := G2_Empty. (* \revemptyset *)
Notation "⊂G2" := G2_Cap. (* \subset *)
Notation "⊃G2" := G2_Cup. (* \supset *)
Notation "⨉G2" := G2_Swap. (* \bigtimes *)
Infix "⟷G2" := G2_Compose (left associativity, at level 40). (* \longleftrightarrow *)
Infix "↕G2" := G2_Stack (left associativity, at level 40). (* \updownarrow *)

Fixpoint G2_ZX_semantics {nIn nOut} (zx : G2_ZX nIn nOut) : 
  Matrix (2 ^ nOut) (2 ^nIn) := 
  match zx with
  | ⦰G2 => G_ZX_semantics ⦰G
  | G2_Z_Spider_1_0 α => G_ZX_semantics (G_Z_Spider_1_nOut 0 α)
  | G2_Z_Spider_0_1 α => G_ZX_semantics (G_Z_Spider_nIn_1 0 α)
  | G2_Z_Spider_1_1 α => G_ZX_semantics (G_Z_Spider_1_nOut 1 α)
  | G2_Z_Spider_1_2 α => G_ZX_semantics (G_Z_Spider_1_nOut 2 α)
  | G2_Z_Spider_2_1 α => G_ZX_semantics (G_Z_Spider_nIn_1 2 α)
  | G2_Cap => G_ZX_semantics (G_Cap)
  | G2_Cup => G_ZX_semantics (G_Cup)
  | G2_Swap => G_ZX_semantics (G_Swap)
  | zx0 ↕G2 zx1 => (G2_ZX_semantics zx0) ⊗ (G2_ZX_semantics zx1)
  | @G2_Compose _ nMid _ zx0 zx1 => (G2_ZX_semantics zx1) × (nMid ⨂ hadamard) × (G2_ZX_semantics zx0)
  end.

Fixpoint G2_ZX_to_G_ZX {nIn nOut} (zx : G2_ZX nIn nOut) : G_ZX nIn nOut :=
  match zx with
  | ⦰G2 => ⦰G
  | G2_Z_Spider_1_0 α => G_Z_Spider_1_nOut 0 α
  | G2_Z_Spider_0_1 α => G_Z_Spider_nIn_1 0 α
  | G2_Z_Spider_1_1 α => G_Z_Spider_1_nOut 1 α
  | G2_Z_Spider_1_2 α => G_Z_Spider_1_nOut 2 α
  | G2_Z_Spider_2_1 α => G_Z_Spider_nIn_1 2 α
  | G2_Cap => G_Cap
  | G2_Cup => G_Cup
  | G2_Swap => G_Swap
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

Definition G2_Wire := G2_Z_Spider_1_1 0.

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
  | 0%nat => G2_Z_Spider_1_0 α
  | S nOut' => G2_Z_Spider_1_2 α ⟷G2 (StackWire G2_Wire) ⟷G2 StackWire (G_Spider_In_to_G2_Spiders nOut' 0%R)
  end.

Local Opaque G_ZX_semantics.
Lemma G_Spider_In_to_G2_Spiders_consistent : forall nOut α, G_ZX_semantics (G_Z_Spider_1_nOut nOut α) = G2_ZX_semantics (G_Spider_In_to_G2_Spiders nOut α).
Proof.
  intro nOut.
  Transparent G_ZX_semantics.
  induction nOut.
  - (* Base Case *)
    reflexivity.
  - (* Inductive Case  ∀ α : R, G_ZX_semantics (G_Z_Spider_1_nOut nOut α) = G2_ZX_semantics (G_Spider_In_to_G2_Spiders (S nOut) α *)
    (* Extract the inductive hypothesis from the statement, and remove the hadamards. *)
    simpl in IHnOut. simpl.
    rewrite kron_1_l; [| auto with wf_db].
    rewrite G2_wire_identity_semantics.
    rewrite id_kron.
    replace (2*2)%nat with (4)%nat by reflexivity.
    rewrite Mmult_1_l; [| auto with wf_db].
    intros.
    rewrite Mmult_assoc.
    restore_dims.
    rewrite <- (Mmult_assoc (hadamard ⊗ hadamard)).
    rewrite kron_mixed_product.
    rewrite MmultHH.
    rewrite id_kron.
    restore_dims.
    rewrite Mmult_1_l; [| auto with wf_db].
    rewrite <- IHnOut.
    (* Prepare for matrix equality by putting x,y in front of every matrix (except for those with ⊗). *)
    prep_matrix_equality.
    unfold Mmult.
    Opaque Z_semantics.
    simpl.
    rewrite Cplus_0_l.
    Transparent Z_semantics.
    (* C_field_simplify eliminates 0%R * cases, but will not always be well behaved. It is for this one, but the next proof it is not. *)
    destruct x,y; simpl; C_field_simplify.
    + (* x = 0, y = 0 *)
      unfold kron; simpl.
      rewrite Nat.mod_0_l;[| apply Nat.pow_nonzero; easy].
      rewrite Nat.div_0_l;[| apply Nat.pow_nonzero; easy].
      lca.
    + (* x = 0, y = S y' *)
      bdestruct (y =? 0). (* This y is y', shows up in both booleans, so we bdestruct it *)
      * unfold kron. (* We have booleans in the lhs of =, but no way to see how they relate to rhs of = *)
        destruct (2 ^ nOut)%nat eqn:E2nOut.
        -- apply (Nat.pow_nonzero) in E2nOut; [destruct E2nOut | easy].
        -- simpl.
           rewrite <- plus_n_Sm.
           simpl.
           lca.
      * rewrite andb_false_r.
        lca.
    + rewrite andb_false_r.
      unfold kron.
      simpl.
      unfold Z_semantics.
      rewrite andb_false_r.
      destruct ((S x) mod 2^nOut) eqn:ExMod.
      * apply Nat.mod_divides in ExMod; [| apply Nat.pow_nonzero; easy].
        destruct ExMod.
        rewrite H.
        rewrite Nat.mul_comm.
        rewrite Nat.div_mul; [| apply Nat.pow_nonzero; easy].
        destruct x0.
        -- rewrite Nat.mul_0_r in H.
           discriminate H.
        -- lca.
      * lca.
    + bdestruct (y =? 0).
      * rewrite andb_true_r.
        unfold kron.
        simpl.
        destruct (2 ^ nOut)%nat eqn:E2nOut.
        -- simpl.
           lca.
        -- replace (S n + (S n + 0) - 1)%nat with (S (n + n))%nat by lia.
           bdestruct (x =? n + n).
           ++ rewrite H0.
              rewrite plus_n_Sm.
              rewrite Nat.add_mod; [| easy].
              rewrite Nat.mod_same; [| easy].
              rewrite plus_0_r.
              rewrite Nat.mod_mod; [| easy].
              rewrite Nat.mod_small; [| constructor; constructor].
              replace ((n + S n) / S n)%nat
                 with (1)%nat.
                 ** unfold Z_semantics.
                     assert ((2 ^ nOut - 1) = n)%nat.
                     { rewrite E2nOut. lia. }
                     rewrite H1.
                     rewrite Nat.eqb_refl.
                     autorewrite with Cexp_db.
                     destruct n; lca.
                 ** rewrite Nat.add_comm.
                     replace ((S n) + n)%nat with ((1 * (S n)) + n)%nat by lia.
                     rewrite Nat.div_add_l; [| easy].
                     rewrite Nat.div_small; [| auto].
                     reflexivity.
           ++ unfold Z_semantics.
              rewrite E2nOut.
              unfold I.
              bdestruct (S x / S n =? 1).
                 ** assert (Hx : (S x) = ((S n) * ((S x) / (S n)) + (S x) mod (S n))%nat); [apply Nat.div_mod; lia |].
                    rewrite H1 in Hx.
                    rewrite Nat.mul_1_r in Hx.
                    bdestruct (S x mod S n =? S n - 1).
                    --- rewrite H2 in Hx.
                        simpl in Hx.
                        rewrite Nat.sub_0_r in Hx.
                        inversion Hx.
                        contradiction.
                    --- destruct (S x mod S n); lca.
                 ** lca.
      * rewrite andb_false_r.
        lca.
Qed.

Fixpoint G_Spider_Out_to_G2_Spiders nIn α: G2_ZX nIn 1 :=
  match nIn with
  | 0%nat => G2_Z_Spider_0_1 α
  | S nIn' => (StackWire (G_Spider_Out_to_G2_Spiders nIn' 0%R)) ⟷G2 (StackWire G2_Wire) ⟷G2 G2_Z_Spider_2_1 α
  end.

Lemma G_Spider_Out_to_G2_Spiders_consistent : forall nIn α, G_ZX_semantics (G_Z_Spider_nIn_1 nIn α) = G2_ZX_semantics (G_Spider_Out_to_G2_Spiders nIn α).
Proof.
  intro nIn.
  Transparent G_ZX_semantics.
  induction nIn.
  - reflexivity.
  - simpl.
    rewrite kron_1_l; [| auto with wf_db].
    rewrite G2_wire_identity_semantics.
    rewrite id_kron.
    replace (2*2)%nat with (4)%nat by reflexivity.
    rewrite Mmult_1_l; [| auto with wf_db].
    intros.
    rewrite Mmult_assoc.
    restore_dims.
    rewrite <- (Mmult_assoc (hadamard ⊗ hadamard)).
    rewrite kron_mixed_product.
    rewrite MmultHH.
    rewrite id_kron.
    restore_dims.
    rewrite Mmult_1_l; [| auto with wf_db].
    rewrite <- IHnIn.
    prep_matrix_equality.
    unfold Mmult.
    Opaque Z_semantics.
    simpl.
    rewrite Cplus_0_l.
    Transparent Z_semantics.
    destruct x, y; simpl; try (rewrite andb_false_r; simpl).
    + (* x = 0, y = 0 *)
      C_field_simplify.
      unfold kron; simpl.
      rewrite Nat.mod_0_l;[| apply Nat.pow_nonzero; easy].
      rewrite Nat.div_0_l;[| apply Nat.pow_nonzero; easy].
      destruct nIn; lca.
    + (* x = 0, y = S n *)
      repeat rewrite Cmult_0_l.
      repeat rewrite Cplus_0_r.
      rewrite Cmult_1_l.
      unfold kron.
      rewrite Nat.mod_0_l; [| easy].
      rewrite Nat.div_0_l; [| easy].
      simpl.
      destruct (S y mod 2 ^ nIn) eqn:ESnmod2NIn.
      * rewrite Nat.mod_divides in ESnmod2NIn; [| apply Nat.pow_nonzero; easy].
        destruct ESnmod2NIn as [c Hc].
        destruct c.
        -- rewrite Nat.mul_0_r in Hc.
           discriminate.
        -- rewrite Hc.
           rewrite Nat.mul_comm.
           rewrite Nat.div_mul; [| apply Nat.pow_nonzero; easy].
           lca.
      * lca.
    + (* x = S n, y = 0 *)
      C_field_simplify.
      destruct (2^nIn)%nat eqn:Epow.
      * contradict Epow.
        apply Nat.pow_nonzero.
        easy.
      * simpl.
        rewrite <- plus_n_Sm.
        simpl.
        rewrite andb_false_r.
        lca.
    + (* x = S n, y = S m *)
      C_field_simplify.
      destruct (2^nIn)%nat eqn:Epow.
      { contradict Epow; apply Nat.pow_nonzero; easy. }
      simpl.
      rewrite <- plus_n_Sm.
      simpl.
      rewrite andb_true_r.
      rewrite plus_0_r.
      unfold kron.
      replace (3/2)%nat with 1%nat by reflexivity.
      replace (3 mod 2)%nat with 1%nat by reflexivity.
      unfold Z_semantics.
      replace (1 =? 2 ^ 1 - 1) with true by reflexivity.
      rewrite andb_true_l.
      bdestruct (y =? n + n).
      * rewrite H.
        rewrite Epow.
        replace (S (n + n) / S n)% nat with 1%nat.
        -- rewrite <- plus_Sn_m.
           rewrite Nat.add_mod; [| easy].
           rewrite Nat.mod_same; [| easy].
           rewrite Nat.add_0_l.
           rewrite Nat.mod_mod; [| easy].
           rewrite Nat.mod_small; [| auto].
           simpl.
           rewrite Nat.sub_0_r.
           rewrite Nat.eqb_refl.
           rewrite Cexp_0.
           destruct x; lca.
        -- rewrite <- plus_Sn_m.
           replace ((S n + n) / S n)%nat
           with ( 1 + (n / S n))%nat.
           { rewrite Nat.div_small; auto. }
           rewrite <- Nat.div_add_l; [| auto].
           rewrite Nat.mul_1_l.
           reflexivity.
      * rewrite andb_false_r.
        rewrite Epow.
        bdestruct (S y / S n =? 1)%nat.
        -- assert (Hx : (S y) = ((S n) * ((S y) / (S n)) + (S y) mod (S n))%nat); [apply Nat.div_mod; lia |].
           rewrite H0 in Hx.
           rewrite Nat.mul_1_r in Hx.
           bdestruct (S y mod S n =? S n - 1)%nat.
           ++ rewrite H1 in Hx.
              simpl in Hx.
              rewrite Nat.sub_0_r in Hx.
              inversion Hx.
              contradiction.
           ++ lca.
        -- destruct (S y / S n)%nat.
           ++ lca.
           ++ destruct n0.
              ** contradiction.
              ** unfold I. 
                 simpl.
                 rewrite Cmult_0_l.
                 lca.
Qed.

Fixpoint G_ZX_to_G2_ZX {nIn nOut} (zx : G_ZX nIn nOut) : G2_ZX nIn nOut :=
  match zx with
  | G_Empty => G2_Empty
  | G_Z_Spider_1_nOut nOut α => G_Spider_In_to_G2_Spiders nOut α
  | G_Z_Spider_nIn_1 nIn α => G_Spider_Out_to_G2_Spiders nIn α
  | G_Cap => G2_Cap
  | G_Cup => G2_Cup
  | G_Swap => G2_Swap
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

