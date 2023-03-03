Require Import CoreData.CoreData.
Require Import CoreAutomation.
Require Import castRules.
Require Import StackComposeRules.
Require Import WireRules.
Require Import SpiderInduction.

Lemma grow_Z_top_left : forall (nIn nOut : nat) α,
	Z (S (S nIn)) nOut α ∝  
	(Z 2 1 0) ↕ (nWire nIn) ⟷ (Z (S nIn) nOut α).
Proof.
	intros.
	replace α%R with (0 + α)%R at 1 by lra.
	simpl.
	rewrite <- Z_spider_1_1_fusion.
	simpl.
	rewrite grow_Z_left_2_1.
	rewrite ZX_Compose_assoc.
	rewrite Z_spider_1_1_fusion.
	replace (0+α)%R with α%R by lra.
	reflexivity.
Qed.

Lemma grow_Z_top_right : forall (nIn nOut : nat) α,
	Z nIn (S (S nOut)) α ∝ 
	(Z nIn (S nOut) α) ⟷ ((Z_Spider 1 2 0) ↕ (nWire nOut)).
Proof.
	intros.
	replace α%R with (0 + α)%R at 1 by lra.
	rewrite <- Z_spider_1_1_fusion.
	simpl.
	rewrite grow_Z_right_1_2.
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
		rewrite (grow_Z_top_left n m β).
		rewrite <- ZX_Compose_assoc.
		rewrite (ZX_Stack_assoc_back (Z 1 1 α) —).
		simpl_casts.
		rewrite <- (ZX_Stack_Compose_distr (Z 1 1 α ↕ —) (Z 2 1 0) (nWire n)).
		cleanup_zx.
		rewrite Z_rot_passthrough.
		rewrite stack_nwire_distribute_r.
		rewrite ZX_Compose_assoc.
		rewrite <- IHn.
		rewrite <- (grow_Z_top_left n).
		easy.
Qed.

Lemma Z_rot_r : forall n m α β,
	Z n (S m) (α + β) ∝  Z n (S m) α ⟷ (Z 1 1 β ↕ nWire m).
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
	- rewrite grow_Z_top_left.
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

Lemma Z_WrapOver_Top_Left : forall n m α,
	Z (S n) m α ∝ (Wire ↕ Z n (S m) α) ⟷  (Cup ↕ nWire m).
Proof.
	induction m.
	- intros.
		rewrite <- Z_WrapOver_Top_Rightight_Top_0.
		cleanup_zx.
		simpl_casts.
		reflexivity.
	- intros.
		destruct m.
		+ rewrite <- Z_WrapOver_Top_Rightight_Top_Base.
			rewrite wire_to_nWire at 2.
			reflexivity.
		+ rewrite grow_Z_top_right.
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
			rewrite grow_Z_top_right.
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
			rewrite <- (ZX_Stack_Compose_distr (Z 1 2 0) (— ↕ Z 1 2 0) 
																					(nWire m) (nWire m)).
			rewrite <- grow_Z_right_bot_1_2_base.
			rewrite grow_Z_top_right.
			rewrite ZX_Stack_Compose_distr.
			rewrite <- ZX_Compose_assoc.
			rewrite <- grow_Z_top_right.
			rewrite (ZX_Stack_assoc (Z 1 2 0) (1 ↑ —) (m ↑ —)).
			simpl_casts.
			rewrite <- nstack1_split.
			rewrite <- (grow_Z_top_right n (S m)).
			easy.
Qed.

Lemma Z_WrapOver_Top_Right : forall n m α,
	Z n (S m) α ∝ (Cap ↕ nWire n) ⟷ (Wire ↕ Z (S n) m α).
Proof. 
	intros. apply transpose_diagrams. simpl. 
	rewrite nstack1_transpose. rewrite transpose_wire.
	apply Z_WrapOver_Top_Left.
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
			rewrite (Z_WrapOver_Top_Right n 1).
			simpl.
			cleanup_zx.
			simpl_casts.
			rewrite ZX_Compose_assoc.
			rewrite <- stack_wire_distribute_l.
			rewrite Z_spider_1_1_fusion.
			rewrite <- (Z_WrapOver_Top_Right n o).
			rewrite (Rplus_comm β α).
			easy.
		+ simpl.
			rewrite (grow_Z_top_right 1 m).
			rewrite <- (nwire_removal_r (Z 1 o _)).
			rewrite ZX_Stack_Compose_distr.
			rewrite <- ZX_Compose_assoc.
			rewrite <- IHm.
			rewrite (ZX_Stack_assoc (Z 1 2 0) (nWire m) (nWire o)).
			simpl_casts.
			rewrite <- nstack1_split.
			rewrite <- (grow_Z_top_right n (m + o)).
			easy.
Qed.

Lemma Z_add_l : forall n m {o α β γ},
	Z (n + m) o (α + β + γ) ∝ (Z n 1 α ↕ Z m 1 γ) ⟷ Z 2 o β.
Proof. intros. transpose_of (@Z_add_r o n m). Qed.

Lemma Z_add_r_base_rot : forall {n} m o {α}, Z n (m + o) α ∝ Z n 2 α ⟷ (Z 1 m 0 ↕ Z 1 o 0).
Proof. 
	intros.
	rewrite <- (@Z_add_r n m o 0 α 0).
	rewrite Rplus_0_l, Rplus_0_r.
	easy.
Qed.

Lemma Z_add_l_base_rot : forall {n} m o {α}, Z (n + m) o α ∝ (Z n 1 0 ↕ Z m 1 0) ⟷ Z 2 o α.
Proof. intros. transpose_of (@Z_add_r_base_rot o n m). Qed.

Lemma Z_1_2_1_fusion : forall α β,
	(Z 1 2 α ⟷ Z 2 1 β) ∝ (Z 1 1 (α + β)).
Proof. solve_prop 1. Qed.

Lemma Z_Absolute_Fusion : forall {n m o} α β,
	(Z n (S m) α ⟷ Z (S m) o β) ∝
	Z n o (α + β).
Proof.
	intros.
	induction m.
	- apply Z_spider_1_1_fusion.
	- rewrite grow_Z_top_right, grow_Z_top_left.
		rewrite ZX_Compose_assoc.
		rewrite <- (ZX_Compose_assoc ((Z 1 2 0) ↕ (m ↑ —))
																 ((Z 2 1 0) ↕ (m ↑ —))
																	(Z (S m) o β)) .
		rewrite <- ZX_Stack_Compose_distr.
		rewrite Z_1_2_1_fusion.
		rewrite Rplus_0_l.
		rewrite Z_0_is_wire.
		cleanup_zx.
		apply IHm.
Qed.

Lemma dominated_Z_spider_fusion_top_right : forall n m0 m1 o α β,
	(Z n (S m0) α ↕ nWire m1 ⟷ Z (S m0 + m1) o β) ∝
	Z (n + m1) o (α + β).
Proof.
	intros.
	replace β%R with (0 + β + 0)%R at 1 by lra.
	rewrite Z_add_l.
	rewrite <- ZX_Compose_assoc.
	rewrite <- ZX_Stack_Compose_distr.
	rewrite Z_Absolute_Fusion.
	cleanup_zx.
	rewrite <- Z_add_l.
	replace (α + 0 + β + 0)%R with (α + β)%R by lra.
	easy.
Qed.


Lemma dominated_Z_spider_fusion_bot_right : forall n m0 m1 o α β,
	((nWire m1 ↕ (Z n (S m0) α)) ⟷ Z (m1 + (S m0)) o β) ∝
	Z (m1 + n) o (α + β).
Proof.
	intros.
	replace β%R with (0 + β + 0)%R at 1 by lra.
	rewrite Z_add_l.
	rewrite <- ZX_Compose_assoc.
	rewrite <- ZX_Stack_Compose_distr.
	rewrite Z_Absolute_Fusion.
	cleanup_zx.
	rewrite <- Z_add_l.
	replace (0 + β + (α + 0))%R with (α + β)%R by lra.
	easy.
Qed.

Lemma dominated_Z_spider_fusion_top_left : forall m n0 n1 i α β,
	Z i (S n0 + n1) β ⟷ (Z (S n0) m α ↕ nWire n1) ∝
	Z i (m + n1) (α + β).
Proof. intros. transpose_of dominated_Z_spider_fusion_top_right. Qed.

Lemma dominated_Z_spider_fusion_bot_left : forall m n0 n1 i α β,
	Z i (n1 + S n0) β ⟷ (nWire n1 ↕ Z (S n0) m α) ∝
	Z i (n1 + m) (α + β).
Proof. intros. transpose_of dominated_Z_spider_fusion_bot_right. Qed.

Lemma Z_SpiderFusion_TopLeft_BotRight : forall top mid bot input output α β,
	Z input (top + S mid) α ↕ nWire bot ⟷
	cast (top + (S mid) + bot) (top + output) (eq_sym (Nat.add_assoc _ _ _)) eq_refl 
		(nWire top ↕ Z (S mid + bot) output β) ∝
	Z (input + bot) (top + output) (α + β).
Proof.
	intros.
	replace α%R with (0 + α + 0)%R at 1 by lra.
	rewrite Z_add_r.
	rewrite stack_nwire_distribute_r.
	rewrite ZX_Compose_assoc.
	rewrite (ZX_Stack_assoc (Z 1 top 0)).
	rewrite cast_compose_r.
	simpl_casts.
	rewrite <- (ZX_Stack_Compose_distr (Z 1 top 0) (nWire top) (Z 1 (S mid) 0 ↕ nWire bot)).
	cleanup_zx.
	rewrite dominated_Z_spider_fusion_top_right.
	rewrite <- (Rplus_0_r (0 + β)).
	rewrite Z_add_l.
	simpl.
	cleanup_zx.
	rewrite Z_WrapOver_Top_Right.
	rewrite stack_nwire_distribute_r.
	rewrite (ZX_Stack_assoc — (Z (S input) 1 α) (nWire bot)).
	simpl_casts.
	rewrite ZX_Compose_assoc.
	rewrite <- (ZX_Stack_Compose_distr — (Z 1 top 0) (Z (S input) 1 α ↕ nWire bot)).
	cleanup_zx.
	rewrite wire_to_nWire at 4.
	rewrite <- ZX_Compose_assoc.
	rewrite (nwire_stack_compose_botleft (Z (S input) 1 α)).
	rewrite <- Z_add_l.
	rewrite <- (wire_removal_l (Z 1 top 0)).
	rewrite <- (nwire_removal_r (Z (S input + bot) _ _)).
	rewrite ZX_Stack_Compose_distr.
	rewrite <- ZX_Compose_assoc.
	rewrite (ZX_Stack_assoc ⊂ (nWire input)).
	simpl_casts.
	rewrite <- nstack1_split.
	rewrite <- (Z_WrapOver_Top_Right (input + bot)).
	rewrite (Z_add_r 1%nat output).
	rewrite ZX_Compose_assoc.
	rewrite <- (ZX_Stack_Compose_distr (Z 1 1 α)).
	rewrite Z_Absolute_Fusion.
	cleanup_zx.
	rewrite <- Z_add_r.
	replace (α + 0 + β + 0)%R with (α + β)%R by lra.
	easy.
Qed.

Lemma Z_SpiderFusion_BotLeft_TopRight : forall top mid bot input output α β,
	((nWire top ↕ Z input (S mid + bot) α) ⟷
	cast (top + ((S mid) + bot)) _ ((Nat.add_assoc _ _ _)) eq_refl 
		(Z (top + (S mid)) output β ↕ nWire bot)) ∝
	Z (top + input) (output + bot) (β + α).
Proof.
	intros.
	apply transpose_diagrams.
	simpl.
	rewrite <- (Z_SpiderFusion_TopLeft_BotRight top mid bot).
	autorewrite with transpose_db.
Opaque cast.
	simpl.
Transparent cast.
	rewrite cast_compose_l.
	simpl_casts.
	autorewrite with transpose_db.
	easy.
Qed.

Lemma Z_SelfCapAbsorbtion_base : forall {n} α, Z n 2%nat α ⟷ ⊃ ∝ Z n 0%nat α.
Proof.
	intros.
	prop_exists_nonzero 1.
	Msimpl.
	simpl.
	solve_matrix.
	replace ((2 ^ n + (2 ^ n + 0) - 1)%nat) with (2 ^ (S n) - 1)%nat by (simpl; lia).
	assert (exists n', 2 ^ S n = (S (S n')))%nat.
	{
		intros.
		induction n.
		- exists 0%nat.
			easy.
		-	destruct IHn.
			rewrite Nat.pow_succ_r'.
			rewrite H.
			exists ((2 * x + 2))%nat.
			lia.
	}
	destruct H.
	rewrite H.
	simpl.
	lca.
Qed.

Lemma Z_SelfCapAbsorbtion_Top : forall {n m α}, (Z) n (S (S m)) α ⟷ (⊃ ↕ nWire m) ∝ Z n m α.
Proof.
	intros.
	rewrite (Z_add_r_base_rot 2 m).
	rewrite ZX_Compose_assoc.
	rewrite <- (ZX_Stack_Compose_distr (Z 1 2 _) ⊃ (Z 1 m _) (nWire m)).
	rewrite Z_SelfCapAbsorbtion_base.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_SelfCupAbsorbtion_Top : forall {n m α}, ((⊂ ↕ nWire n) ⟷ Z (S (S n)) m α) ∝ (Z n m α).
Proof. intros. transpose_of (@Z_SelfCapAbsorbtion_Top m n). Qed.

Lemma Z_SelfCapAbsorbtion : forall {n m m' α}, Z n (m + (S (S m'))) α ⟷ (nWire m ↕ (⊃ ↕ nWire m')) ∝ (Z n (m + m') α).
Proof.
	intros.
	rewrite Z_add_r_base_rot.
	rewrite ZX_Compose_assoc.
	rewrite <- (ZX_Stack_Compose_distr (Z 1 m _) (nWire m) (Z 1 (S (S m')) _) (⊃ ↕ nWire m')).
	rewrite Z_SelfCapAbsorbtion_Top.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_SelfCupAbsorbtion : forall {n n' m α}, ((nWire n ↕ (⊂ ↕ nWire n')) ⟷ Z (n + (S (S n'))) m α) ∝ (Z (n + n') m α).
Proof. intros. transpose_of (@Z_SelfCapAbsorbtion m n n'). Qed.

Lemma Z_SelfLoopRemoval_Top : forall {n m α}, Z n m α ∝ (⊂ ↕ nWire n) ⟷ (— ↕ Z (S n) (S m) α) ⟷ (⊃ ↕ nWire m).
Proof.
	intros.
	rewrite <- Z_WrapOver_Top_Right.
	rewrite Z_SelfCapAbsorbtion_Top.
	easy.
Qed.

Lemma Z_SelfSwapAbsorbtion_Right_Base : forall {n α}, Z n 2 α ⟷ ⨉ ∝ Z n 2 α.
Proof. intros. solve_prop 1. Qed.

Lemma Z_SelfSwapAbsorbtion_Right_Top : forall {n m α}, Z n (S (S m)) α ⟷ (⨉ ↕ nWire m) ∝ Z n (S (S m)) α.
Proof.
	intros.
	rewrite (Z_add_r_base_rot 2 m) at 1.
	rewrite ZX_Compose_assoc.
	rewrite <- (ZX_Stack_Compose_distr (Z 1 2 0) (⨉) (Z 1 m 0) (nWire m)).
	rewrite Z_SelfSwapAbsorbtion_Right_Base.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_SelfSwapAbsorbtion_Right : forall {n m m' α}, Z n (m' + S (S m)) α ⟷ (nWire m' ↕ (⨉ ↕ nWire m)) ∝ Z n (m' + S (S m)) α.
Proof.
	intros.
	rewrite Z_add_r_base_rot at 1.
	rewrite ZX_Compose_assoc.
	rewrite <- (ZX_Stack_Compose_distr (Z 1 m' 0) (nWire _) (Z 1 (S (S m)) 0) (⨉ ↕ nWire _)).
	rewrite Z_SelfSwapAbsorbtion_Right_Top.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_SelfSwapAbsorbtion_Left_Base : forall {m α}, (⨉ ⟷ Z 2 m α) ∝ Z 2 m α.
Proof. intros. transpose_of (@Z_SelfSwapAbsorbtion_Right_Base m α). Qed.

Lemma Z_SelfSwapAbsorbtion_Left_Top : forall {n m α}, ((⨉ ↕ nWire n) ⟷ Z (S (S n)) m α) ∝ Z (S (S n)) m α.
Proof. intros. transpose_of (@Z_SelfSwapAbsorbtion_Right_Top m n α). Qed.

Lemma Z_SelfSwapAbsorbtion_Left : forall {n n' m α}, ((nWire n' ↕ (⨉ ↕ nWire n)) ⟷ Z (n' + S (S n)) m α) ∝ Z (n' + S (S n)) m α.
Proof. intros. transpose_of (@Z_SelfSwapAbsorbtion_Right m n n' α). Qed.