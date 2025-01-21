Require Export CoreData.CoreData.
Require Import CastRules.
Require Import SpiderInduction.

Local Open Scope ZX_scope.

Lemma stack_assoc : 
forall {n0 n1 n2 m0 m1 m2} 
	(zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2) prfn prfm,
	(zx0 ↕ zx1) ↕ zx2 ∝= 
		cast _ _ prfn prfm (zx0 ↕ (zx1 ↕ zx2)).
Proof.
	intros.
	unfold proportional_by_1.
	simpl_cast_semantics.
	cbn.
	restore_dims.
	now rewrite kron_assoc by auto_wf.
Qed.

Lemma stack_assoc_back : 
forall {n0 n1 n2 m0 m1 m2}
	(zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2) prfn prfm,
	zx0 ↕ (zx1 ↕ zx2) ∝=
		cast (n0 + (n1 + n2)) (m0 + (m1 + m2)) prfn prfm
				((zx0 ↕ zx1) ↕ zx2).
Proof.
	intros.
	unfold proportional_by_1.
	simpl_cast_semantics.
	cbn.
	restore_dims.
	now rewrite kron_assoc by auto_wf.
Qed.

Lemma stack_empty_l : forall {nIn nOut} (zx : ZX nIn nOut),
	⦰ ↕ zx ∝= zx.
Proof.
	intros.
	unfold proportional_by_1.
	cbn.
	restore_dims.
	now rewrite kron_1_l by auto_wf.
Qed.

Lemma stack_empty_r : forall {n m : nat} (zx : ZX n m) prfn prfm,
	zx ↕ ⦰ ∝= 
		cast (n + 0) (m + 0) prfn prfm zx.
Proof.
	intros.
	unfold proportional_by_1.
	simpl_cast_semantics.
	cbn.
	restore_dims.
	now rewrite kron_1_r by auto_wf.
Qed.

Lemma stack_empty_r_back : forall {n m : nat} (zx : ZX n m) prfn prfm,
	zx ∝= 
		cast _ _ prfn prfm (zx ↕ ⦰).
Proof.
	intros.
	unfold proportional_by_1.
	simpl_cast_semantics.
	cbn.
	restore_dims.
	now rewrite kron_1_r by auto_wf.
Qed.

Lemma stack_simplify_eq : forall {n1 m1 n2 m2}
  (zx1 zx3 : ZX n1 m1) (zx2 zx4 : ZX n2 m2),
  zx1 ∝= zx3 -> zx2 ∝= zx4 -> zx1 ↕ zx2 ∝= zx3 ↕ zx4.
Proof.
  now intros * -> ->.
Qed.

Lemma stack_simplify : forall {n1 m1 n2 m2}
  (zx1 zx3 : ZX n1 m1) (zx2 zx4 : ZX n2 m2),
  zx1 ∝ zx3 -> zx2 ∝ zx4 -> zx1 ↕ zx2 ∝ zx3 ↕ zx4.
Proof.
  now intros * -> ->.
Qed.

Lemma stack_transpose : forall {n1 m1 n2 m2} (zx1 : ZX n1 m1) (zx2 : ZX n2 m2), 
	(zx1 ↕ zx2) ⊤ = (zx1⊤ ↕ zx2⊤).
Proof.
	reflexivity.
Qed.

Lemma nstack1_colorswap : forall n (zx : ZX 1 1), ⊙(n ↑ zx) = (n ↑ (⊙ zx)).
Proof.
	intros.
	induction n.
	- easy.
	- simpl.
		rewrite IHn.
		easy.
Qed.

Lemma nstack_transpose : forall k {n m} (zx : ZX n m), (k ⇑ zx)⊤ = (k ⇑ zx⊤).
Proof.
	intros.
	induction k.
	- easy.
	- simpl.
		rewrite IHk.
		easy.
Qed.

Lemma nstack_colorswap : forall n {n' m'} (zx : ZX n' m'), ⊙(n ⇑ zx) = (n ⇑ (⊙ zx)).
Proof.
	intros.
	induction n.
	- easy.
	- simpl.
		rewrite IHn.
		easy.
Qed.

Lemma n_stack1_succ_l : forall n (zx : ZX 1 1),
	(S n) ↑ zx = zx ↕ (n ↑ zx).
Proof. easy. Qed.

Lemma n_stack1_succ_r : forall n (zx : ZX 1 1) prfn prfm, 
	(S n) ↑ zx ∝=
	cast (S n) (S n) prfn prfm ((n ↑ zx) ↕ zx).
Proof.
	intros.
	induction n.	
	- cbn. 
		now rewrite stack_empty_r, 2!cast_id_eq, stack_empty_l.
	- rewrite n_stack1_succ_l.
		rewrite IHn at 1.
		rewrite cast_stack_r.
		simpl.
		simpl_casts.
		rewrite stack_assoc_back.
		simpl_casts.
		easy.
Unshelve.
all: lia.
Qed.

Lemma stack_wire_distribute_l : forall {n m o} (zx0 : ZX n m) (zx1 : ZX m o),
	— ↕ (zx0 ⟷ zx1) ∝= (— ↕ zx0) ⟷ (— ↕ zx1).
Proof.
	intros.
	unfold proportional_by_1.
	simpl; Msimpl; easy.
Qed.

Lemma stack_wire_distribute_r : forall {n m o} (zx0 : ZX n m) (zx1 : ZX m o),
	(zx0 ⟷ zx1) ↕ — ∝= (zx0 ↕ —) ⟷ (zx1 ↕ —).
Proof.
	intros.
	unfold proportional_by_1.
	simpl; Msimpl; easy.
Qed.

Lemma stack_nwire_distribute_l : forall {n m o p} (zx0 : ZX n m) (zx1 : ZX m o),
	n_wire p ↕ (zx0 ⟷ zx1) ∝= (n_wire p ↕ zx0) ⟷ (n_wire p ↕ zx1).
Proof.
	intros.
	unfold proportional_by_1.
	cbn; rewrite n_wire_semantics; Msimpl; reflexivity.
Qed.

Lemma stack_nwire_distribute_r : forall {n m o p} (zx0 : ZX n m) (zx1 : ZX m o),
	(zx0 ⟷ zx1) ↕ n_wire p ∝= (zx0 ↕ n_wire p) ⟷ (zx1 ↕ n_wire p).
Proof.
	intros.
	unfold proportional_by_1.
	cbn; rewrite n_wire_semantics; Msimpl; reflexivity.
Qed.

(* Lemma n_wire_collapse_r : forall {n0 n1 m1} (zx0 : ZX n0 0) (zx1 : ZX n1 m1),
 (zx0 ↕ n_wire n1) ⟷ zx1 ∝ zx0 ↕ zx1. *)

Lemma nstack1_split : forall n m (zx : ZX 1 1),
	(n + m) ↑ zx ∝= 
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
Unshelve.
all: lia.
Qed.

Lemma nstack_split : forall n m {nIn mOut} (zx : ZX nIn mOut) prfn prfm,
	(n + m) ⇑ zx ∝= 
	cast _ _ prfn prfm ((n ⇑ zx) ↕ (m ⇑ zx)).
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
Unshelve.
all: lia.
Qed.

Lemma nstack1_1 : forall zx, 1 ↑ zx ∝= zx.
Proof.
	intros.
	simpl.
	rewrite stack_empty_r.
	simpl_casts.
	easy.
Unshelve.
all: lia.
Qed.

Lemma nstack1_0 : forall zx, 0 ↑ zx = ⦰.
Proof. easy. Qed.