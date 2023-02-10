Require Export CoreData.CoreData.
Require Import CastRules.
Require Import SpiderInduction.

Local Open Scope ZX_scope.

Lemma ZX_Stack_assoc : 
forall {n0 n1 n2 m0 m1 m2}
	(zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2),
	(zx0 ↕ zx1) ↕ zx2 ∝ 
		Cast ((n0 + n1) + n2) ((m0 + m1) + m2) 
				 (eq_sym(Nat.add_assoc _ _ _)) (eq_sym(Nat.add_assoc _ _ _)) 
											(zx0 ↕ (zx1 ↕ zx2)).
Proof.                                                      
	intros.
	prop_exists_nonzero 1.  
	simpl.
	Msimpl.
	rewrite (@Cast_semantics (n0 + (n1 + n2)) _ ((n0 + n1) + n2)%nat).
	rewrite kron_assoc; auto with wf_db.
Qed.

Lemma ZX_Stack_assoc_back : 
forall {n0 n1 n2 m0 m1 m2}
	(zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2),
	zx0 ↕ (zx1 ↕ zx2) ∝ 
		Cast (n0 + (n1 + n2)) (m0 + (m1 + m2)) 
				 (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _) 
											((zx0 ↕ zx1) ↕ zx2).
Proof.                                                      
	intros.
	prop_exists_nonzero 1.  
	simpl.
	Msimpl.
	rewrite (@Cast_semantics ((n0 + n1) + n2) _ (n0 + (n1 + n2))%nat).
	simpl; restore_dims.
	rewrite kron_assoc; auto with wf_db.
Qed.

Lemma ZX_Stack_Empty_l : forall {nIn nOut} (zx : ZX nIn nOut),
	⦰ ↕ zx ∝ zx.
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl.
	rewrite kron_1_l; try auto with wf_db.
	lma.
Qed.

Lemma ZX_Stack_Empty_r : forall {n m : nat} (zx : ZX n m),
	zx ↕ ⦰ ∝ 
		Cast (n + 0) (m + 0) (Nat.add_0_r _) (Nat.add_0_r _) zx.
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl.
	Msimpl.
	rewrite (@Cast_semantics n m (n + 0) (m + 0)).
	reflexivity.
Qed.

Lemma ZX_Stack_simplify : forall {n1 m1 n2 m2}
  (zx1 zx3 : ZX n1 m1) (zx2 zx4 : ZX n2 m2),
  zx1 ∝ zx3 -> zx2 ∝ zx4 -> zx1 ↕ zx2 ∝ zx3 ↕ zx4.
Proof.
  intros.
  rewrite H, H0.
  easy.
Qed.

Lemma ZX_Stack_transpose : forall {n1 m1 n2 m2} (zx1 : ZX n1 m1) (zx2 : ZX n2 m2), (zx1 ↕ zx2) ⊤ ∝ (zx1⊤ ↕ zx2⊤).
Proof.
	intros.
	prop_exists_nonzero 1.
	simpl.
	lma.
Qed.

Lemma nStack1_transpose : forall n (zx : ZX 1 1), (n ↑ zx)⊤ ∝ (n ↑ zx⊤).
Proof.
	intros.
	induction n.
	- easy.
	- simpl.
		rewrite IHn.
		easy.
Qed.

Lemma nStack1_colorswap : forall n (zx : ZX 1 1), ⊙(n ↑ zx) ∝ (n ↑ (⊙ zx)).
Proof.
	intros.
	induction n.
	- easy.
	- simpl.
		rewrite IHn.
		easy.
Qed.

Lemma nStack1_l : forall n (zx : ZX 1 1),
	(S n) ↑ zx ∝ zx ↕ (n ↑ zx).
Proof. easy. Qed.

Lemma nStack1_r : forall n (zx : ZX 1 1), 
	(S n) ↑ zx ∝ 
	Cast (S n) (S n) (eq_sym (Nat.add_1_r _)) (eq_sym (Nat.add_1_r _)) ((n ↑ zx) ↕ zx).
Proof.
induction n.
- intros.
	simpl.
	simpl_casts.
	rewrite ZX_Stack_Empty_l, ZX_Stack_Empty_r.
	simpl_casts.
	easy.
- intros.
	rewrite nStack1_l.
	rewrite IHn at 1.
	rewrite cast_stack_r.
	simpl.
	simpl_casts.
	rewrite ZX_Stack_assoc_back.
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
	nWire p ↕ (zx0 ⟷ zx1) ∝ (nWire p ↕ zx0) ⟷ (nWire p ↕ zx1).
Proof.
	intros.
	induction p.
	- repeat rewrite ZX_Stack_Empty_l. easy.
	- rewrite nStack1_l.
		rewrite (ZX_Stack_assoc — (nWire p) zx0).
		rewrite (ZX_Stack_assoc — (nWire p) zx1).
		simpl_casts.
		rewrite <- (stack_wire_distribute_l (nWire p ↕ zx0) (nWire p ↕ zx1)).
		rewrite <- IHp.
		rewrite ZX_Stack_assoc_back.
		simpl_casts.
		easy.
Qed.

(* Lemma nWire_collapse_r : forall {n0 n1 m1} (zx0 : ZX n0 0) (zx1 : ZX n1 m1),
 (zx0 ↕ nWire n1) ⟷ zx1 ∝ zx0 ↕ zx1. *)

Lemma nstack1_split : forall n m (zx : ZX 1 1),
	(n + m) ↑ zx ∝ 
	(n ↑ zx) ↕ (m ↑ zx).
Proof.
	intros.
	induction n.
	- simpl. rewrite ZX_Stack_Empty_l. easy.
	- simpl.
		rewrite IHn.
		rewrite (ZX_Stack_assoc zx).
		simpl_casts.
		reflexivity.
Qed.

Lemma nstack_split : forall n m {nIn mOut} (zx : ZX nIn mOut),
	(n + m) ⇑ zx ∝ 
	Cast _ _ (Nat.mul_add_distr_r _ _ _) (Nat.mul_add_distr_r _ _ _) 
		((n ⇑ zx) ↕ (m ⇑ zx)).
Proof.
	intros.
	dependent induction n.
	- simpl. simpl_casts.
		rewrite ZX_Stack_Empty_l. easy.
	- simpl.
		rewrite IHn.
		simpl.
		simpl_casts.
		rewrite ZX_Stack_assoc.
		simpl_casts.
		reflexivity.
Qed.
