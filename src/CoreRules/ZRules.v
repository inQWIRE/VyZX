From VyZX Require Import CoreData.
From VyZX Require Import CoreAutomation.
From VyZX Require Import CastRules.
From VyZX Require Import StackComposeRules.
From VyZX Require Import WireRules.

Lemma Grow_Z_Left : forall (nIn nOut : nat) α,
	Z (S (S nIn)) nOut α ∝  
	(Z 2 1 0) ↕ (nWire nIn) ⟷ (Z (S nIn) nOut α).
Proof.
	intros.
	replace α%R with (0 + α)%R at 1 by lra.
	simpl.
	rewrite <- Z_spider_1_1_fusion.
	simpl.
	rewrite Grow_Z_Left_2_1.
	rewrite ZX_Compose_assoc.
	rewrite Z_spider_1_1_fusion.
	replace (0+α)%R with α%R by lra.
	reflexivity.
Qed.

Lemma Grow_Z_Right : forall (nIn nOut : nat) α,
	Z nIn (S (S nOut)) α ∝ 
	(Z nIn (S nOut) α) ⟷ ((Z_Spider 1 2 0) ↕ (nWire nOut)).
Proof.
	intros.
	replace α%R with (0 + α)%R at 1 by lra.
	rewrite <- Z_spider_1_1_fusion.
	simpl.
	rewrite Grow_Z_Right_1_2.
	rewrite <- ZX_Compose_assoc.
	rewrite Z_spider_1_1_fusion.
	replace (0+α)%R with α%R by lra.
	reflexivity.
Qed.


Lemma Z_rot_l : forall n m α β,
	Z (S n) m (α + β) ∝ Z 1 1 α ↕ nWire n ⟷ Z (S n) m β.
Proof.
	assert (Z_rot_passthrough : forall α β, 
		(Z 1 1 α ↕ — ⟷ Z 2 1 β) ∝ Z 2 1 β ⟷ Z 1 1 α).
		{ solve_prop 1. }
	induction n; intros.
	- cleanup_zx.
		simpl_casts.
		rewrite Z_spider_1_1_fusion.
		easy.
	- simpl.
		rewrite (Grow_Z_Left n m β).
		rewrite <- ZX_Compose_assoc.
		rewrite (ZX_Stack_assoc_back (Z 1 1 α) —).
		simpl_casts.
		rewrite <- (ZX_Stack_Compose_distr (Z 1 1 α ↕ —) (Z 2 1 0) (nWire n)).
		cleanup_zx.
		rewrite Z_rot_passthrough.
		rewrite stack_nwire_distribute_r.
		rewrite ZX_Compose_assoc.
		rewrite <- IHn.
		rewrite <- (Grow_Z_Left n).
		easy.
Qed.

Lemma Z_rot_r : forall n m α β,
	Z n (S m) (α + β) ∝  Z n (S m) α ⟷ Z 1 1 β ↕ nWire m.
Proof.
	intros.
	rewrite Rplus_comm.
	apply transpose_diagrams.
	simpl.
	rewrite nstack1_transpose.
	rewrite transpose_wire.
	apply Z_rot_l.
Qed.

Lemma Z_appendix_rot_l : forall n m α β,
	Z n m (α + β) ∝ (Z 0 1 α ↕ nWire n) ⟷ Z (S n) m β.
Proof.
	assert (Z_appendix_base : forall α β,
		(Z 0 1 α ↕ — ⟷ Z 2 1 β) ∝ Z 1 1 (α + β)).
		{ solve_prop 1. }
	induction n; intros.
	- cleanup_zx.
		simpl_casts.
		rewrite Z_spider_1_1_fusion.
		easy.
	- rewrite Grow_Z_Left.
		simpl.
		rewrite (ZX_Stack_assoc_back (Z 0 1 α) —).
		simpl_casts.
		rewrite <- ZX_Compose_assoc.
		rewrite <- (@stack_nwire_distribute_r _ _ _ n (Z 0 1 α ↕ —) (Z 2 1 0)).
		rewrite Z_appendix_base.
		rewrite <- Z_rot_l.
		rewrite Rplus_0_r.
		easy.
Qed.

Lemma Z_appendix_rot_r : forall n m α β,
	Z n m (β + α) ∝ Z n (S m) α ⟷ (Z 1 0 β ↕ nWire m).
Proof. 
	intros.
	apply transpose_diagrams.
	simpl.
	rewrite nstack1_transpose.
	rewrite transpose_wire.
	apply Z_appendix_rot_l.
Qed.

Lemma WrapOver_L : forall n m α,
	Z (S n) m α ∝ (Wire ↕ Z n (S m) α) ⟷  (Cup ↕ nWire m).
Proof.
	induction m.
	- intros.
		rewrite <- WrapOver_Right_Top_0.
		cleanup_zx.
		simpl_casts.
		reflexivity.
	- intros.
		destruct m.
		+ rewrite <- WrapOver_Right_Top_Base.
			rewrite wire_to_nWire at 2.
			reflexivity.
		+ rewrite Grow_Z_Right.
			rewrite IHm.
			rewrite <- (ZX_Stack_Empty_l (Z 1 2 0 ↕ (m ↑ —))).
			fold (nWire m).
			replace ⦰ with (nWire 0) by auto.
			specialize (nwire_stack_compose_botleft ⊃ (Z 1 2 0 ↕ nWire m)); intros.
			simpl in H.
			rewrite ZX_Compose_assoc.
			rewrite H.
			clear H.
			specialize (nwire_stack_compose_topleft (Z 1 2 0 ↕ nWire m) ⊃); intros.
			rewrite <- H.
			clear H.
			rewrite <- ZX_Compose_assoc.
			rewrite Grow_Z_Right.
			rewrite ZX_Compose_assoc.
			replace (nWire 2) with (— ↕ (— ↕ ⦰)) by auto.
			cleanup_zx.
			simpl_casts.
			rewrite (ZX_Stack_assoc — — _).
			simpl_casts.
			rewrite <- ZX_Compose_assoc.
			rewrite <- (stack_wire_distribute_l 
				((Z) n (S m) α ⟷ ((Z) 1 2 0 ↕ (m ↑ —))) 
				(— ↕ ((Z) 1 2 0 ↕ nWire m))).
			rewrite ZX_Compose_assoc.
			fold (nWire m).
			rewrite ZX_Stack_assoc_back.
			simpl_casts.
			rewrite <- (ZX_Stack_Compose_distr (Z 1 2 0) (— ↕ Z 1 2 0) (nWire m) (nWire m)).
			rewrite <- Grow_Z_Right_Bot_1_2_Base.
			rewrite Grow_Z_Right.
			rewrite ZX_Stack_Compose_distr.
			rewrite <- ZX_Compose_assoc.
			rewrite <- Grow_Z_Right.
			rewrite (ZX_Stack_assoc (Z 1 2 0) (1 ↑ —) (m ↑ —)).
			simpl_casts.
			rewrite <- nstack1_split.
			rewrite <- (Grow_Z_Right n (S m)).
			easy.
Qed.

Lemma WrapOver_R : forall n m α,
	Z n (S m) α ∝ (Cap ↕ nWire n) ⟷ (Wire ↕ Z (S n) m α).
Proof. 
	intros. apply transpose_diagrams. simpl. 
	rewrite nstack1_transpose. rewrite transpose_wire.
	apply WrapOver_L.
Qed.

Lemma Z_add_r : forall {n} m o {α β γ},
	Z n (m + o) (α + β + γ) ∝ Z n 2 β ⟷ (Z 1 m α ↕ Z 1 o γ).
Proof.
	intros.
	induction m.
	- simpl.
		rewrite <- nwire_stack_compose_botleft.
		rewrite <- ZX_Compose_assoc.
		cleanup_zx.
		rewrite <- Z_appendix_rot_r.
		rewrite Z_spider_1_1_fusion.
		easy.
	- destruct m.
		+ simpl.
			cleanup_zx.
			rewrite <- (nwire_removal_l (Z 1 o γ)).
			rewrite <- (nwire_removal_r (Z 1 1 α)).
			rewrite ZX_Stack_Compose_distr.
			rewrite <- ZX_Compose_assoc.
			rewrite <- Z_rot_r.
			rewrite (WrapOver_R n 1).
			simpl.
			cleanup_zx.
			simpl_casts.
			rewrite ZX_Compose_assoc.
			rewrite <- stack_wire_distribute_l.
			rewrite Z_spider_1_1_fusion.
			rewrite <- (WrapOver_R n o).
			rewrite (Rplus_comm β α).
			easy.
		+ simpl.
			rewrite (Grow_Z_Right 1 m).
			rewrite <- (nwire_removal_r (Z 1 o _)).
			rewrite ZX_Stack_Compose_distr.
			rewrite <- ZX_Compose_assoc.
			rewrite <- IHm.
			rewrite (ZX_Stack_assoc (Z 1 2 0) (nWire m) (nWire o)).
			simpl_casts.
			rewrite <- nstack1_split.
			rewrite <- (Grow_Z_Right n (m + o)).
			easy.
Qed.

Lemma Z_add_l : forall n m {o α β γ},
	Z (n + m) o (α + β + γ) ∝ (Z n 1 α ↕ Z m 1 γ) ⟷ Z 2 o β.
Proof. intros. transpose_of (@Z_add_r o n m). Qed.
