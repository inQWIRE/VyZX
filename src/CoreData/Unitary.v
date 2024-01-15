
Require Import ZXCore.
Require Import Proportional.

Definition unitary {n} (zx : ZX n n) := ((⟦ zx ⟧) † × (⟦ zx ⟧) = I _)%M.
Definition weak_unitary_l {n} (zx : ZX n n) := zx ⟷ zx† ∝ n_wire _.
Definition weak_unitary_r {n} (zx : ZX n n) := zx† ⟷ zx ∝ n_wire _.

Lemma unitary_lift : forall {n} (zx : ZX n n), unitary zx <-> WF_Unitary (⟦ zx ⟧).
Proof.
  intros; split; intros.
  - unfold WF_Unitary; split; auto with wf_db.
  - unfold WF_Unitary in H; unfold unitary; destruct H; easy.
Qed.

Lemma unitary_is_weak_unitary_l : forall {n} (zx : ZX n n), unitary zx -> weak_unitary_l zx.
Proof.
  unfold unitary, weak_unitary_l.
  intros.
  prop_exists_nonzero 1.
  Msimpl; rewrite n_wire_semantics; simpl.
  rewrite semantics_adjoint_comm.
  easy.
Qed.  

Lemma unitary_is_weak_unitary_r : forall {n} (zx : ZX n n), unitary zx -> weak_unitary_r zx.
Proof.
  intros.
  prop_exists_nonzero 1.
  Msimpl; rewrite n_wire_semantics; simpl.
  rewrite semantics_adjoint_comm.
  apply unitary_lift in H.
  apply WF_unitary_rev in H.
  easy.
Qed.

Lemma n_wire_unitary : forall n, unitary (n_wire n).
Proof. 
  intros.
  unfold unitary.
  rewrite n_wire_semantics.
  rewrite id_sa.
  rewrite Mmult_1_l; auto with wf_db.
Qed.

Lemma weak_unitary_l_prop : forall {n} (zx0 zx1 : ZX n n), zx0 ∝ zx1 -> weak_unitary_l zx0 -> weak_unitary_l zx1.
Proof.
  intros.
  unfold weak_unitary_l in *.
  rewrite H in H0.
  easy.
Qed.

Lemma weak_unitary_r_prop : forall {n} (zx0 zx1 : ZX n n), zx0 ∝ zx1 -> weak_unitary_r zx0 -> weak_unitary_r zx1.
  Proof.
    intros.
    unfold weak_unitary_r in *.
    rewrite H in H0.
    easy.
Qed.