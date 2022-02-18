Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.VectorStates.
Require Export ZX.
Require Export ZX_G_2.
Require Export Gates.
Require Export GateRules.
Require Export Rules.
Require Export VyZX.Proportional.
Require Import Setoid.

Local Open Scope R_scope.
Inductive A_G2_ZX : nat (* #inputs *) -> nat (* #outputs *) -> nat (* node id *) -> Type :=
  | A_G2_Empty n : A_G2_ZX 0 0 n
  | A_G2_Z_Spider_1_0 n (α : R) : A_G2_ZX 1 0 n
  | A_G2_Z_Spider_0_1 n (α : R) : A_G2_ZX 0 1 n
  | A_G2_Z_Spider_1_1 n (α : R) : A_G2_ZX 1 1 n (* Required to build wire construct *)
  | A_G2_Z_Spider_1_2 n (α : R) : A_G2_ZX 1 2 n
  | A_G2_Z_Spider_2_1 n (α : R) : A_G2_ZX 2 1 n
  | A_G2_Cap n : A_G2_ZX 0 2 n
  | A_G2_Cup n : A_G2_ZX 2 0 n
  | A_G2_Stack {nIn0 nIn1 nOut0 nOut1 n0 n1} (zx0 : A_G2_ZX nIn0 nOut0 n0) (zx1 : A_G2_ZX nIn1 nOut1 n1) n :
         A_G2_ZX (nIn0 + nIn1) (nOut0 + nOut1) n
  | A_G2_Compose {nIn nMid nOut n0 n1} (zx0 : A_G2_ZX nIn nMid n0) (zx1 : A_G2_ZX nMid nOut n1) n : A_G2_ZX nIn nOut n.
Local Close Scope R_scope.

Notation "⦰AG2" := A_G2_Empty. (* \revemptyset *)
Notation "⊂AG2" := A_G2_Cap. (* \subset *)
Notation "⊃AG2" := A_G2_Cup. (* \supset *)

Fixpoint A_G2_ZX_semantics {nIn nOut n} (zx : A_G2_ZX nIn nOut n) : 
  Matrix (2 ^ nOut) (2 ^nIn) := 
  match zx with
  | ⦰AG2 _ => G2_ZX_semantics ⦰G2
  | A_G2_Z_Spider_1_0 _ α => G2_ZX_semantics (G2_Z_Spider_1_0 α)
  | A_G2_Z_Spider_0_1 _ α => G2_ZX_semantics (G2_Z_Spider_0_1 α)
  | A_G2_Z_Spider_1_1 _ α => G2_ZX_semantics (G2_Z_Spider_1_1 α)
  | A_G2_Z_Spider_1_2 _ α => G2_ZX_semantics (G2_Z_Spider_1_2 α)
  | A_G2_Z_Spider_2_1 _ α => G2_ZX_semantics (G2_Z_Spider_2_1 α)
  | A_G2_Cap _ => G2_ZX_semantics (G2_Cap)
  | A_G2_Cup _ => G2_ZX_semantics (G2_Cup)
  | A_G2_Stack zx0 zx1  _=> (A_G2_ZX_semantics zx0) ⊗ (A_G2_ZX_semantics zx1)
  | @A_G2_Compose _ nMid _ _ _ zx0 zx1 _ => (A_G2_ZX_semantics zx1) × (nMid ⨂ hadamard) × (A_G2_ZX_semantics zx0)
  end.

Fixpoint A_G2_ZX_to_G2_ZX {nIn nOut n} (zx : A_G2_ZX nIn nOut n) : G2_ZX nIn nOut :=
  match zx with
  | ⦰AG2 _ => ⦰G2
  | A_G2_Z_Spider_1_0 _ α => G2_Z_Spider_1_0 α
  | A_G2_Z_Spider_0_1 _ α => G2_Z_Spider_0_1 α
  | A_G2_Z_Spider_1_1 _ α => G2_Z_Spider_1_1 α
  | A_G2_Z_Spider_1_2 _ α => G2_Z_Spider_1_2 α
  | A_G2_Z_Spider_2_1 _ α => G2_Z_Spider_2_1 α
  | A_G2_Cap _ => G2_Cap
  | A_G2_Cup _ => G2_Cup
  | A_G2_Stack zx0 zx1 _ => (A_G2_ZX_to_G2_ZX zx0) ↕G2 (A_G2_ZX_to_G2_ZX zx1)
  | A_G2_Compose zx0 zx1 _ => (A_G2_ZX_to_G2_ZX zx0) ⟷G2 (A_G2_ZX_to_G2_ZX zx1)
  end.

Fixpoint G2_ZX_to_A_G2_ZX_helper base {nIn nOut} (zx : G2_ZX nIn nOut) : (A_G2_ZX nIn nOut base) * nat :=
  match zx with
  | ⦰G2 => (⦰AG2 base, S base)
  | G2_Z_Spider_1_0 α => (A_G2_Z_Spider_1_0 base α, S base)
  | G2_Z_Spider_0_1 α => (A_G2_Z_Spider_0_1 base α, S base)
  | G2_Z_Spider_1_1 α => (A_G2_Z_Spider_1_1 base α, S base)
  | G2_Z_Spider_1_2 α => (A_G2_Z_Spider_1_2 base α, S base)
  | G2_Z_Spider_2_1 α => (A_G2_Z_Spider_2_1 base α, S base)
  | G2_Cap => (A_G2_Cap base, S base)
  | G2_Cup => (A_G2_Cup base, S base)
  | G2_Stack zx0 zx1 => (A_G2_Stack 
                            (fst (G2_ZX_to_A_G2_ZX_helper (S base) zx0)) 
                            (fst (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper (S base) zx0)) zx1)) base,
                            S (snd (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper (S base) zx0)) zx1)))
  | G2_Compose zx0 zx1 => (A_G2_Compose
                            (fst (G2_ZX_to_A_G2_ZX_helper (S base) zx0)) 
                            (fst (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper (S base) zx0)) zx1)) base,
                            S (snd (G2_ZX_to_A_G2_ZX_helper (snd (G2_ZX_to_A_G2_ZX_helper (S base) zx0)) zx1)))
  end.

Definition G2_ZX_to_A_G2_ZX {nIn nOut} (zx : G2_ZX nIn nOut) := fst (G2_ZX_to_A_G2_ZX_helper 0 zx).

(* Todo: 
   - State/Prove no collisions
   - Add maps from node id -> [node id] * [node id] (i.e. map to connected spider/cap/cup) 
*)

Fixpoint collect_ids {nIn nOut n} (zx : A_G2_ZX nIn nOut n) : list nat :=
  match zx with
  | ⦰AG2 n => [n]
  | A_G2_Z_Spider_1_0 n _ => [n]
  | A_G2_Z_Spider_0_1 n _ => [n]
  | A_G2_Z_Spider_1_1 n _ => [n]
  | A_G2_Z_Spider_1_2 n _ => [n]
  | A_G2_Z_Spider_2_1 n _ => [n]
  | A_G2_Cap n => [n]
  | A_G2_Cup n => [n]
  | A_G2_Stack zx0 zx1 n => n :: (collect_ids zx0 ++ collect_ids zx1)
  | A_G2_Compose zx0 zx1 n => n :: (collect_ids zx0 ++ collect_ids zx1)
  end.

Definition WF_A_G2_ZX {nIn nOut n} (zx : A_G2_ZX nIn nOut n) := NoDup (collect_ids zx).

Lemma G2_ZX_to_A_G2_ZX_helper_ret_geq_base : forall base {nIn nOut} (zx : G2_ZX nIn nOut), base <= snd (G2_ZX_to_A_G2_ZX_helper base zx).
Proof.
  intros.
  generalize dependent base.
  induction zx; intros; simpl; try auto (* Non composite *).
  all: 
  simpl;
  apply (Nat.le_trans _ (snd (G2_ZX_to_A_G2_ZX_helper (S base) zx1)) _);
  [ apply (Nat.le_trans _ (S base) _); [auto | apply IHzx1] | constructor; apply IHzx2].
Qed.

Lemma G2_ZX_to_A_G2_ZX_helper_assigns_geq_base : forall base {nIn nOut} (zx : G2_ZX nIn nOut), forallb (fun n => base <=? n) (collect_ids (fst (G2_ZX_to_A_G2_ZX_helper base zx))) = true.
Proof.
  intros.
  generalize dependent base.
  assert (forall x base, (S base <=? x = true) -> (base <=? x = true)).
    {
      intros.
      rewrite leb_correct; [ reflexivity | ].
      apply leb_complete in H.
      eapply Nat.le_trans.
      2: apply H.
      auto.
    }
  assert (andb_simpl : forall a b, a = true /\ b = true -> a && b = true) by (intros a b H'; destruct H'; subst; reflexivity).
  induction zx; intros; simpl; try (rewrite Nat.leb_refl; easy).
  - simpl.
    rewrite Nat.leb_refl.
    rewrite andb_true_l.
    rewrite forallb_app.
    apply andb_simpl.
    split. 
    + specialize (IHzx1 (S base)).
      rewrite forallb_forall in *.
      intros; apply H; apply IHzx1; assumption.
    + specialize (IHzx2 (snd (G2_ZX_to_A_G2_ZX_helper (S base) zx1))).
      rewrite forallb_forall in *.
      intros.
      assert ((snd (G2_ZX_to_A_G2_ZX_helper (S base) zx1) <=? x) = true -> base <=? x = true).
      {
       intros.
       rewrite leb_correct; [ reflexivity | ].
       apply leb_complete in H1.
       apply (Nat.le_trans _ (S base) _); [ auto | ].
       eapply Nat.le_trans.
       apply G2_ZX_to_A_G2_ZX_helper_ret_geq_base.
       apply H1.
      }
      apply H1.
      apply IHzx2.
      apply H0.
  - simpl.
    rewrite Nat.leb_refl.
    rewrite andb_true_l.
    rewrite forallb_app.
    apply andb_simpl.
    split. 
    + specialize (IHzx1 (S base)).
      rewrite forallb_forall in *.
      intros; apply H; apply IHzx1; assumption.
    + specialize (IHzx2 (snd (G2_ZX_to_A_G2_ZX_helper (S base) zx1))).
      rewrite forallb_forall in *.
      intros.
      assert ((snd (G2_ZX_to_A_G2_ZX_helper (S base) zx1) <=? x) = true -> base <=? x = true).
      {
        intros.
        rewrite leb_correct; [ reflexivity | ].
        apply leb_complete in H1.
        apply (Nat.le_trans _ (S base) _); [ auto | ].
        eapply Nat.le_trans.
        apply G2_ZX_to_A_G2_ZX_helper_ret_geq_base.
        apply H1.
      }
      apply H1.
      apply IHzx2.
      apply H0.
Qed.

Lemma WF_G2_ZX_to_A_G2_ZX : forall {nIn nOut} (zx : G2_ZX nIn nOut), WF_A_G2_ZX (G2_ZX_to_A_G2_ZX zx).
Proof.
  intros.
  unfold G2_ZX_to_A_G2_ZX.
  unfold WF_A_G2_ZX.
  induction zx; try (simpl; constructor; try auto; constructor) (* All non compositional cases *).
  - simpl.
    constructor.
    + rewrite in_app_iff.
      unfold not.
      intros.
      destruct H.
      assert (Hcontra : forallb (fun n => 1 <=? n) (collect_ids (fst (G2_ZX_to_A_G2_ZX_helper 1 zx1))) = true) by apply G2_ZX_to_A_G2_ZX_helper_assigns_geq_base.
      rewrite forallb_forall in Hcontra.
      * apply Hcontra in H.
        discriminate H.
      * admit.
    + Search (NoDup (_ ++ _)). 
Abort.