Require Import QuantumLib.Quantum.
Require Export ZX.

Local Open Scope ZX_scope.

Fixpoint Spider_Angle_Prop (prop : C -> Prop) {nIn nOut} (zx : ZX nIn nOut) : Prop :=  
  match zx with
  | X_Spider _ _ α => prop α
  | Z_Spider _ _ α => prop α
  | zx0 ↕ zx1 => (Spider_Angle_Prop prop zx0) /\ (Spider_Angle_Prop prop zx1)
  | zx0 ⟷ zx1 => (Spider_Angle_Prop prop zx0) /\ (Spider_Angle_Prop prop zx1)
  | _ => True (* Non-composititonal non-spiders have no impact *)
  end.

Definition Proper_Clifford_Prop (α : C) : Prop := exists n : nat, α = PI / C2 + (INR n) * PI.

Definition Proper_Clifford_ZX {nIn nOut} (zx : ZX nIn nOut) := Spider_Angle_Prop Proper_Clifford_Prop zx.

Definition Pauli_Prop (α : C) : Prop := exists n : nat, α = ((INR n) * PI)%C.

Definition Pauli_ZX {nIn nOut} (zx : ZX nIn nOut) := Spider_Angle_Prop Pauli_Prop zx.

Definition Clifford_Prop (α : C) : Prop := exists n : nat, α = (INR n) * PI / C2.

Definition Clifford_ZX {nIn nOut} (zx : ZX nIn nOut) := Spider_Angle_Prop Clifford_Prop zx.

Lemma Spider_Angle_Prop_Weaking : forall (prop0 prop1 : C -> Prop) {nIn nOut} (zx : ZX nIn nOut),
  (forall c, prop0 c -> prop1 c) -> (Spider_Angle_Prop prop0 zx -> Spider_Angle_Prop prop1 zx).
Proof.
  intros.
  induction zx; try (unfold Spider_Angle_Prop in *; try apply H; assumption);
                try (simpl in H0; destruct H0; split; try apply IHzx1; try apply IHzx2; assumption).
Qed.

Definition Pauli_Proper_Clifford_Prop_Is_Clifford_Prop : forall c, Pauli_Prop c \/ Proper_Clifford_Prop c -> Clifford_Prop c.
Proof.
  intros.
  unfold Pauli_Prop, Proper_Clifford_Prop, Clifford_Prop in *.
  destruct H;
  destruct H.
  - exists (2 * x)%nat.
    rewrite mult_INR.
    rewrite H.
    lca.
  - exists (2 * x + 1)%nat.
    rewrite H.
    rewrite plus_INR.
    rewrite mult_INR.
    lca.
Qed. 

Definition Clifford_Prop_Is_Pauli_Proper_Clifford_Prop : forall c, Clifford_Prop c -> Pauli_Prop c \/ Proper_Clifford_Prop c.
Proof.
  intros.
  unfold Pauli_Prop, Proper_Clifford_Prop, Clifford_Prop in *.
  destruct H.
  assert (exists p : nat, x = (2 * p)%nat \/ x = S (2 * p)) by apply even_odd_cor.
  destruct H0;
  destruct H0;
  subst.
  - left.
    exists x0.  
    rewrite mult_INR.
    lca.
  - right.
    rewrite S_INR.
    rewrite mult_INR.
    exists x0.
    lca.
Qed. 

Lemma Clifford_is_Proper_Clifford_And_Pauli : forall {nIn nOut} (zx : ZX nIn nOut), (Pauli_ZX zx) \/ (Proper_Clifford_ZX zx) -> Clifford_ZX zx.
Proof.
  intros.
  induction zx; intros; simpl; try easy; auto
  ; try 
    (destruct H;
     unfold Pauli_ZX, Pauli_Prop in *;
      unfold Clifford_ZX, Clifford_Prop in *;
      unfold Proper_Clifford_ZX, Proper_Clifford_Prop in *;
      simpl in *).
  - destruct H.
    exists (2 * x)%nat.
    rewrite H.
    rewrite mult_INR.
    lca.
  - destruct H.
    exists (2 * x + 1)%nat.
    rewrite H.
    rewrite plus_INR.
    rewrite mult_INR.
    lca.
  - destruct H.
    exists (2 * x)%nat.
    rewrite H.
    rewrite mult_INR.
    lca.
  - destruct H.
    exists (2 * x + 1)%nat.
    rewrite H.
    rewrite plus_INR.
    rewrite mult_INR.
    lca.
  - destruct H.
    split.
    apply IHzx1.
    left.
    assumption.
    apply IHzx2.
    left.
    assumption.
  - destruct H.
    split.
    apply IHzx1.
    right.
    assumption.
    apply IHzx2.
    right.
    assumption.
  - destruct H.
    split.
    apply IHzx1.
    left.
    assumption.
    apply IHzx2.
    left.
    assumption.
  - destruct H.
    split.
    apply IHzx1.
    right.
    assumption.
    apply IHzx2.
    right.
    assumption.  
Qed.  