Require Export CoreData.CoreData.
Require Import castRules.
Require Import SpiderInduction.

Local Open Scope ZX_scope.

Lemma stack_assoc : 
forall {n0 n1 n2 m0 m1 m2}
	(zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2),
	(zx0 ↕ zx1) ↕ zx2 ∝ 
		cast ((n0 + n1) + n2) ((m0 + m1) + m2) 
				 (eq_sym(Nat.add_assoc _ _ _)) (eq_sym(Nat.add_assoc _ _ _)) 
											(zx0 ↕ (zx1 ↕ zx2)).
Proof.                                                      
	intros.
	prop_exists_nonzero 1.  
	simpl.
	Msimpl.
	rewrite (@cast_semantics (n0 + (n1 + n2)) _ ((n0 + n1) + n2)%nat).
	rewrite kron_assoc; auto with wf_db.
Qed.

Lemma stack_assoc_back : 
forall {n0 n1 n2 m0 m1 m2}
	(zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2),
	zx0 ↕ (zx1 ↕ zx2) ∝ 
		cast (n0 + (n1 + n2)) (m0 + (m1 + m2)) 
				 (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _) 
											((zx0 ↕ zx1) ↕ zx2).
Proof.                                                      
	intros.
	prop_exists_nonzero 1.  
	simpl.
	Msimpl.
	rewrite (@cast_semantics ((n0 + n1) + n2) _ (n0 + (n1 + n2))%nat).
	simpl; restore_dims.
	rewrite kron_assoc; auto with wf_db.
Qed.

Lemma stack_empty_l : forall {nIn nOut} (zx : ZX nIn nOut),
	⦰ ↕ zx ∝ zx.
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl.
	rewrite kron_1_l; try auto with wf_db.
	lma.
Qed.

Lemma stack_empty_r : forall {n m : nat} (zx : ZX n m),
	zx ↕ ⦰ ∝ 
		cast (n + 0) (m + 0) (Nat.add_0_r _) (Nat.add_0_r _) zx.
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl.
	Msimpl.
	rewrite (@cast_semantics n m (n + 0) (m + 0)).
	reflexivity.
Qed.

Lemma stack_empty_r_rev : forall {n m : nat} (zx : ZX n m),
	zx ∝ 
		cast _ _ (eq_sym (Nat.add_0_r _)) (eq_sym (Nat.add_0_r _)) (zx ↕ ⦰).
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl.
	Msimpl.
	simpl_cast_semantics.
	simpl.
	Msimpl.
	reflexivity.
Qed.

Lemma stack_simplify : forall {n1 m1 n2 m2}
  (zx1 zx3 : ZX n1 m1) (zx2 zx4 : ZX n2 m2),
  zx1 ∝ zx3 -> zx2 ∝ zx4 -> zx1 ↕ zx2 ∝ zx3 ↕ zx4.
Proof.
  intros.
  rewrite H, H0.
  easy.
Qed.

Lemma stack_transpose : forall {n1 m1 n2 m2} (zx1 : ZX n1 m1) (zx2 : ZX n2 m2), (zx1 ↕ zx2) ⊤ ∝ (zx1⊤ ↕ zx2⊤).
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl.
	lma.
Qed.

Lemma n_stack1_transpose : forall n (zx : ZX 1 1), (n ↑ zx)⊤ ∝ (n ↑ zx⊤).
Proof.
	intros.
	induction n.
	- easy.
	- simpl.
		rewrite IHn.
		easy.
Qed.

Lemma n_stack1_colorswap : forall n (zx : ZX 1 1), ⊙(n ↑ zx) ∝ (n ↑ (⊙ zx)).
Proof.
	intros.
	induction n.
	- easy.
	- simpl.
		rewrite IHn.
		easy.
Qed.

Lemma n_stack_transpose : forall n (zx : ZX 1 1), (n ⇑ zx)⊤ ∝ (n ⇑ zx⊤).
Proof.
	intros.
	induction n.
	- easy.
	- simpl.
		rewrite IHn.
		easy.
Qed.

Lemma n_stack_colorswap : forall n {n' m'} (zx : ZX n' m'), ⊙(n ⇑ zx) ∝ (n ⇑ (⊙ zx)).
Proof.
	intros.
	induction n.
	- easy.
	- simpl.
		rewrite IHn.
		easy.
Qed.

Lemma n_stack1_l : forall n (zx : ZX 1 1),
	(S n) ↑ zx ∝ zx ↕ (n ↑ zx).
Proof. easy. Qed.

Lemma n_stack1_r : forall n (zx : ZX 1 1), 
	(S n) ↑ zx ∝ 
	cast (S n) (S n) (eq_sym (Nat.add_1_r _)) (eq_sym (Nat.add_1_r _)) ((n ↑ zx) ↕ zx).
Proof.
induction n.
- intros.
	simpl.
	simpl_casts.
	rewrite stack_empty_l, stack_empty_r.
	simpl_casts.
	easy.
- intros.
	rewrite n_stack1_l.
	rewrite IHn at 1.
	rewrite cast_stack_r.
	simpl.
	simpl_casts.
	rewrite stack_assoc_back.
	simpl_casts.
	easy.
Qed.

Lemma stack_wire_distribute_l : forall {n m o} (zx0 : ZX n m) (zx1 : ZX m o),
	— ↕ (zx0 ⟷ zx1) ∝ (— ↕ zx0) ⟷ (— ↕ zx1).
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl; Msimpl; easy.
Qed.

Lemma stack_wire_distribute_r : forall {n m o} (zx0 : ZX n m) (zx1 : ZX m o),
	(zx0 ⟷ zx1) ↕ —  ∝ (zx0 ↕ —) ⟷ (zx1 ↕ —).
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl; Msimpl; easy.
Qed.

Lemma stack_nwire_distribute_l : forall {n m o p} (zx0 : ZX n m) (zx1 : ZX m o),
	n_wire p ↕ (zx0 ⟷ zx1) ∝ (n_wire p ↕ zx0) ⟷ (n_wire p ↕ zx1).
Proof.
	intros.
	induction p.
	- repeat rewrite stack_empty_l. easy.
	- rewrite n_stack1_l.
		rewrite (stack_assoc — (n_wire p) zx0).
		rewrite (stack_assoc — (n_wire p) zx1).
		simpl_casts.
		rewrite <- (stack_wire_distribute_l (n_wire p ↕ zx0) (n_wire p ↕ zx1)).
		rewrite <- IHp.
		rewrite stack_assoc_back.
		simpl_casts.
		easy.
Qed.

(* Lemma n_wire_collapse_r : forall {n0 n1 m1} (zx0 : ZX n0 0) (zx1 : ZX n1 m1),
 (zx0 ↕ n_wire n1) ⟷ zx1 ∝ zx0 ↕ zx1. *)

Lemma nstack1_split : forall n m (zx : ZX 1 1),
	(n + m) ↑ zx ∝ 
	(n ↑ zx) ↕ (m ↑ zx).
Proof.
	intros.
	induction n.
	- simpl. rewrite stack_empty_l. easy.
	- simpl.
		rewrite IHn.
		rewrite (stack_assoc zx).
		simpl_casts.
		reflexivity.
Qed.

Lemma nstack_split : forall n m {nIn mOut} (zx : ZX nIn mOut),
	(n + m) ⇑ zx ∝ 
	cast _ _ (Nat.mul_add_distr_r _ _ _) (Nat.mul_add_distr_r _ _ _) 
		((n ⇑ zx) ↕ (m ⇑ zx)).
Proof.
	intros.
	dependent induction n.
	- simpl. simpl_casts.
		rewrite stack_empty_l. easy.
	- simpl.
		rewrite IHn.
		simpl.
		simpl_casts.
		rewrite stack_assoc.
		simpl_casts.
		reflexivity.
Qed.
