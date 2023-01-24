From VyZX Require Import CoreData.ZXCore.
From VyZX Require Import CoreData.SemanticCore.
From VyZX Require Import CoreData.Proportional.

From VyZX Require Import CoreRules.StackRules.

Local Open Scope ZX_scope.

Lemma Z_0_is_wire : Z 1 1 0 ∝ —.
Proof.
  intros.
  prop_exists_nonzero 1.
  simpl.
  unfold Z_semantics.
  autorewrite with Cexp_db.
  solve_matrix.
  assert (forall x y, (x =? 0) && (y =? 0) = (x =? y) && (x <=? 0))%nat.
  {
    intros.
    bdestruct (x0 <=? 0).
    - apply Nat.le_0_r in H; subst.
      rewrite Nat.eqb_refl, andb_true_r, andb_true_l.
      destruct y0; easy.
    - rewrite andb_false_r.
      destruct x0; easy.
  }
  rewrite H.
  easy.
Qed.

Lemma Z_2_0_0_is_cap : Z 2 0 0 ∝ ⊃.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
  apply Cexp_0.
Qed.

Lemma Z_0_2_0_is_cup : Z 0 2 0 ∝ ⊂.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
  apply Cexp_0.
Qed.

Lemma yank_r : 
  (⊂ ↕ —) ⟷ (— ↕ ⊃) ∝ —.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
Qed.

Lemma yank_l : 
  (— ↕ ⊂) ⟷ (⊃ ↕ —) ∝ —.
Proof.
  prop_exists_nonzero 1.
  simpl.
  solve_matrix.
Qed.

Lemma X_0_is_wire : X 1 1 0 ∝ —.
Proof. 
    Admitted.

Lemma stack_nwire_distribute_r : forall {n m o p} (zx0 : ZX n m) (zx1 : ZX m o),
(zx0 ⟷ zx1) ↕ nWire p ∝ (zx0 ↕ nWire p) ⟷ (zx1 ↕ nWire p).
Proof.
intros.
induction p.
- repeat rewrite ZX_Stack_Empty_r.
	eapply (cast_diagrams n o).
	repeat rewrite cast_contract.
	rewrite cast_id.
	rewrite cast_compose_distribute.
	simpl_casts.
	erewrite (cast_compose_mid m _ ($ n, m + 0 ::: zx0 $)).
	simpl_casts.
	easy.
	Unshelve.
	all: lia.
- rewrite nStack1_r.
	repeat rewrite cast_stack_r.
	eapply (cast_diagrams (n + (p + 1)) (o + (p + 1))).
	rewrite cast_contract.
	rewrite cast_id.
	rewrite cast_compose_distribute.
	simpl_casts.
	erewrite (cast_compose_mid (m + (p + 1)) _ 
                ($ n + (p + 1), m + (S p) ::: zx0 ↕ (nWire p ↕ —)$)).
	simpl_casts.
	rewrite 3 ZX_Stack_assoc_back.
	eapply (cast_diagrams (n + p + 1) (o + p + 1)).
	rewrite cast_contract.
	rewrite cast_id.
	rewrite cast_compose_distribute.
	rewrite 2 cast_contract.
	erewrite (cast_compose_mid (m + p + 1) _ 
                ($ n + p + 1, m + (p + 1) ::: zx0 ↕ nWire p ↕ — $)).
	simpl_casts.
	rewrite <- stack_wire_distribute_r.
	rewrite <- IHp.
	easy.
	Unshelve.
	all: lia.
Qed.

Lemma wire_to_nWire : 
  — ∝ nWire 1.
Proof.
  simpl.
  rewrite ZX_Stack_Empty_r.
  simpl_casts.
  easy.
Qed.
