Require Import CoreData.CoreData.
Require Import CoreAutomation.
Require Import CastRules.
Require Import StackComposeRules.
Require Import WireRules.
Require Import SpiderInduction.

Lemma grow_Z_top_left : forall (nIn nOut : nat) α,
	𝒵 (S (S nIn)) nOut α ∝  
	(𝒵 2 1 0) ↕ (n_wire nIn) ⟷ (𝒵 (S nIn) nOut α).
Proof.
	intros.
	replace α%R with (0 + α)%R at 1 by lra.
	simpl.
	rewrite <- Z_spider_1_1_fusion.
	simpl.
	rewrite grow_Z_left_2_1.
	rewrite compose_assoc.
	rewrite Z_spider_1_1_fusion.
	replace (0+α)%R with α%R by lra.
	reflexivity.
Qed.

Lemma grow_Z_top_right : forall (nIn nOut : nat) α,
	𝒵 nIn (S (S nOut)) α ∝ 
	(𝒵 nIn (S nOut) α) ⟷ ((𝒵 1 2 0) ↕ (n_wire nOut)).
Proof.
	intros.
	replace α%R with (0 + α)%R at 1 by lra.
	rewrite <- Z_spider_1_1_fusion.
	simpl.
	rewrite grow_Z_right_1_2.
	rewrite <- compose_assoc.
	rewrite Z_spider_1_1_fusion.
	replace (0+α)%R with α%R by lra.
	reflexivity.
Qed.

Lemma Z_rot_l : forall n m α β,
	𝒵 (S n) m (α + β) ∝ 𝒵 1 1 α ↕ n_wire n ⟷ 𝒵 (S n) m β.
Proof.
	assert (Z_rot_passthrough : forall α β, 
		(𝒵 1 1 α ↕ — ⟷ 𝒵 2 1 β) ∝ 𝒵 2 1 β ⟷ 𝒵 1 1 α).
		{ solve_prop 1. }
	induction n; intros.
	- cleanup_zx.
		simpl_casts.
		rewrite Z_spider_1_1_fusion.
		easy.
	- simpl.
		rewrite (grow_Z_top_left n m β).
		rewrite <- compose_assoc.
		rewrite (stack_assoc_back (𝒵 1 1 α) —).
		simpl_casts.
		rewrite <- (stack_compose_distr (𝒵 1 1 α ↕ —) (𝒵 2 1 0) (n_wire n)).
		cleanup_zx.
		rewrite Z_rot_passthrough.
		rewrite stack_nwire_distribute_r.
		rewrite compose_assoc.
		rewrite <- IHn.
		rewrite <- (grow_Z_top_left n).
		easy.
Qed.

Lemma Z_rot_r : forall n m α β,
	𝒵 n (S m) (α + β) ∝  𝒵 n (S m) α ⟷ (𝒵 1 1 β ↕ n_wire m).
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
	𝒵 n m (α + β) ∝ (𝒵 0 1 α ↕ n_wire n) ⟷ 𝒵 (S n) m β.
Proof.
	assert (Z_appendix_base : forall α β,
		(𝒵 0 1 α ↕ — ⟷ 𝒵 2 1 β) ∝ 𝒵 1 1 (α + β)).
		{ solve_prop 1. }
	induction n; intros.
	- cleanup_zx.
		simpl_casts.
		rewrite Z_spider_1_1_fusion.
		easy.
	- rewrite grow_Z_top_left.
		simpl.
		rewrite (stack_assoc_back (𝒵 0 1 α) —).
		simpl_casts.
		rewrite <- compose_assoc.
		rewrite <- (@stack_nwire_distribute_r _ _ _ n (𝒵 0 1 α ↕ —) (𝒵 2 1 0)).
		rewrite Z_appendix_base.
		rewrite <- Z_rot_l.
		rewrite Rplus_0_r.
		easy.
Qed.

Lemma Z_appendix_rot_r : forall n m α β,
	𝒵 n m (β + α) ∝ 𝒵 n (S m) α ⟷ (𝒵 1 0 β ↕ n_wire m).
Proof. 
	intros.
	apply transpose_diagrams.
	simpl.
	rewrite nstack1_transpose.
	rewrite transpose_wire.
	apply Z_appendix_rot_l.
Qed.

Lemma Z_wrap_over_top_left : forall n m α,
	𝒵 (S n) m α ∝ (Wire ↕ 𝒵 n (S m) α) ⟷  (Cup ↕ n_wire m).
Proof.
	induction m.
	- intros.
		rewrite <- Z_wrap_over_top_right_0.
		cleanup_zx.
		simpl_casts.
		reflexivity.
	- intros.
		destruct m.
		+ rewrite <- Z_wrap_over_top_right_base.
			rewrite wire_to_n_wire at 2.
			reflexivity.
		+ rewrite grow_Z_top_right.
			rewrite IHm.
			rewrite <- (stack_empty_l (𝒵 1 2 0 ↕ (m ↑ —))).
			fold (n_wire m).
			replace ⦰ with (n_wire 0) by auto.
			specialize (nwire_stack_compose_botleft ⊃ (𝒵 1 2 0 ↕ n_wire m)); intros.
			simpl in H.
			rewrite compose_assoc.
			rewrite H.
			clear H.
			specialize (nwire_stack_compose_topleft (𝒵 1 2 0 ↕ n_wire m) ⊃); intros.
			rewrite <- H.
			clear H.
			rewrite <- compose_assoc.
			rewrite grow_Z_top_right.
			rewrite compose_assoc.
			replace (n_wire 2) with (— ↕ (— ↕ ⦰)) by auto.
			cleanup_zx.
			simpl_casts.
			rewrite (stack_assoc — — _).
			simpl_casts.
			rewrite <- compose_assoc.
			rewrite <- (stack_wire_distribute_l 
				((𝒵) n (S m) α ⟷ ((𝒵) 1 2 0 ↕ (m ↑ —))) 
				(— ↕ ((𝒵) 1 2 0 ↕ n_wire m))).
			rewrite compose_assoc.
			fold (n_wire m).
			rewrite stack_assoc_back.
			simpl_casts.
			rewrite <- (stack_compose_distr (𝒵 1 2 0) (— ↕ 𝒵 1 2 0) 
																					(n_wire m) (n_wire m)).
			rewrite <- grow_Z_right_bot_1_2_base.
			rewrite grow_Z_top_right.
			rewrite stack_compose_distr.
			rewrite <- compose_assoc.
			rewrite <- grow_Z_top_right.
			rewrite (stack_assoc (𝒵 1 2 0) (1 ↑ —) (m ↑ —)).
			simpl_casts.
			rewrite <- nstack1_split.
			rewrite <- (grow_Z_top_right n (S m)).
			easy.
Qed.

Lemma Z_wrap_over_top_right : forall n m α,
	𝒵 n (S m) α ∝ (Cap ↕ n_wire n) ⟷ (Wire ↕ 𝒵 (S n) m α).
Proof. 
	intros. apply transpose_diagrams. simpl. 
	rewrite nstack1_transpose. rewrite transpose_wire.
	apply Z_wrap_over_top_left.
Qed.

Lemma Z_add_r : forall {n} m o {α β γ},
	𝒵 n (m + o) (α + β + γ) ∝ 𝒵 n 2 β ⟷ (𝒵 1 m α ↕ 𝒵 1 o γ).
Proof.
	intros.
	induction m.
	- simpl.
		rewrite <- nwire_stack_compose_botleft.
		rewrite <- compose_assoc.
		cleanup_zx.
		rewrite <- Z_appendix_rot_r.
		rewrite Z_spider_1_1_fusion.
		easy.
	- destruct m.
		+ simpl.
			cleanup_zx.
			rewrite <- (nwire_removal_l (𝒵 1 o γ)).
			rewrite <- (nwire_removal_r (𝒵 1 1 α)).
			rewrite stack_compose_distr.
			rewrite <- compose_assoc.
			rewrite <- Z_rot_r.
			rewrite (Z_wrap_over_top_right n 1).
			simpl.
			cleanup_zx.
			simpl_casts.
			rewrite compose_assoc.
			rewrite <- stack_wire_distribute_l.
			rewrite Z_spider_1_1_fusion.
			rewrite <- (Z_wrap_over_top_right n o).
			rewrite (Rplus_comm β α).
			easy.
		+ simpl.
			rewrite (grow_Z_top_right 1 m).
			rewrite <- (nwire_removal_r (𝒵 1 o _)).
			rewrite stack_compose_distr.
			rewrite <- compose_assoc.
			rewrite <- IHm.
			rewrite (stack_assoc (𝒵 1 2 0) (n_wire m) (n_wire o)).
			simpl_casts.
			rewrite <- nstack1_split.
			rewrite <- (grow_Z_top_right n (m + o)).
			easy.
Qed.

Lemma Z_add_l : forall n m {o α β γ},
	𝒵 (n + m) o (α + β + γ) ∝ (𝒵 n 1 α ↕ 𝒵 m 1 γ) ⟷ 𝒵 2 o β.
Proof. intros. transpose_of (@Z_add_r o n m). Qed.

Lemma Z_add_r_base_rot : forall {n} m o {α}, 𝒵 n (m + o) α ∝ 𝒵 n 2 α ⟷ (𝒵 1 m 0 ↕ 𝒵 1 o 0).
Proof. 
	intros.
	rewrite <- (@Z_add_r n m o 0 α 0).
	rewrite Rplus_0_l, Rplus_0_r.
	easy.
Qed.

Lemma Z_add_l_base_rot : forall {n} m o {α}, 𝒵 (n + m) o α ∝ (𝒵 n 1 0 ↕ 𝒵 m 1 0) ⟷ 𝒵 2 o α.
Proof. intros. transpose_of (@Z_add_r_base_rot o n m). Qed.

Lemma Z_1_2_1_fusion : forall α β,
	(𝒵 1 2 α ⟷ 𝒵 2 1 β) ∝ (𝒵 1 1 (α + β)).
Proof. solve_prop 1. Qed.

Lemma Z_absolute_fusion : forall {n m o} α β,
	(𝒵 n (S m) α ⟷ 𝒵 (S m) o β) ∝
	𝒵 n o (α + β).
Proof.
	intros.
	induction m.
	- apply Z_spider_1_1_fusion.
	- rewrite grow_Z_top_right, grow_Z_top_left.
		rewrite compose_assoc.
		rewrite <- (compose_assoc ((𝒵 1 2 0) ↕ (m ↑ —))
																 ((𝒵 2 1 0) ↕ (m ↑ —))
																	(𝒵 (S m) o β)) .
		rewrite <- stack_compose_distr.
		rewrite Z_1_2_1_fusion.
		rewrite Rplus_0_l.
		rewrite Z_0_is_wire.
		cleanup_zx.
		apply IHm.
Qed.

Lemma dominated_Z_spider_fusion_top_right : forall n m0 m1 o α β,
	(𝒵 n (S m0) α ↕ n_wire m1 ⟷ 𝒵 (S m0 + m1) o β) ∝
	𝒵 (n + m1) o (α + β).
Proof.
	intros.
	replace β%R with (0 + β + 0)%R at 1 by lra.
	rewrite Z_add_l.
	rewrite <- compose_assoc.
	rewrite <- stack_compose_distr.
	rewrite Z_absolute_fusion.
	cleanup_zx.
	rewrite <- Z_add_l.
	replace (α + 0 + β + 0)%R with (α + β)%R by lra.
	easy.
Qed.


Lemma dominated_Z_spider_fusion_bot_right : forall n m0 m1 o α β,
	((n_wire m1 ↕ (𝒵 n (S m0) α)) ⟷ 𝒵 (m1 + (S m0)) o β) ∝
	𝒵 (m1 + n) o (α + β).
Proof.
	intros.
	replace β%R with (0 + β + 0)%R at 1 by lra.
	rewrite Z_add_l.
	rewrite <- compose_assoc.
	rewrite <- stack_compose_distr.
	rewrite Z_absolute_fusion.
	cleanup_zx.
	rewrite <- Z_add_l.
	replace (0 + β + (α + 0))%R with (α + β)%R by lra.
	easy.
Qed.

Lemma dominated_Z_spider_fusion_top_left : forall m n0 n1 i α β,
	𝒵 i (S n0 + n1) β ⟷ (𝒵 (S n0) m α ↕ n_wire n1) ∝
	𝒵 i (m + n1) (α + β).
Proof. intros. transpose_of dominated_Z_spider_fusion_top_right. Qed.

Lemma dominated_Z_spider_fusion_bot_left : forall m n0 n1 i α β,
	𝒵 i (n1 + S n0) β ⟷ (n_wire n1 ↕ 𝒵 (S n0) m α) ∝
	𝒵 i (n1 + m) (α + β).
Proof. intros. transpose_of dominated_Z_spider_fusion_bot_right. Qed.

Lemma Z_spider_fusion_top_left_bot_right : forall top mid bot input output α β,
	𝒵 input (top + S mid) α ↕ n_wire bot ⟷
	cast (top + (S mid) + bot) (top + output) (eq_sym (Nat.add_assoc _ _ _)) eq_refl 
		(n_wire top ↕ 𝒵 (S mid + bot) output β) ∝
	𝒵 (input + bot) (top + output) (α + β).
Proof.
	intros.
	replace α%R with (0 + α + 0)%R at 1 by lra.
	rewrite Z_add_r.
	rewrite stack_nwire_distribute_r.
	rewrite compose_assoc.
	rewrite (stack_assoc (𝒵 1 top 0)).
	rewrite cast_compose_r.
	simpl_casts.
	rewrite <- (stack_compose_distr (𝒵 1 top 0) (n_wire top) (𝒵 1 (S mid) 0 ↕ n_wire bot)).
	cleanup_zx.
	rewrite dominated_Z_spider_fusion_top_right.
	rewrite <- (Rplus_0_r (0 + β)).
	rewrite Z_add_l.
	simpl.
	cleanup_zx.
	rewrite Z_wrap_over_top_right.
	rewrite stack_nwire_distribute_r.
	rewrite (stack_assoc — (𝒵 (S input) 1 α) (n_wire bot)).
	simpl_casts.
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr — (𝒵 1 top 0) (𝒵 (S input) 1 α ↕ n_wire bot)).
	cleanup_zx.
	rewrite wire_to_n_wire at 4.
	rewrite <- compose_assoc.
	rewrite (nwire_stack_compose_botleft (𝒵 (S input) 1 α)).
	rewrite <- Z_add_l.
	rewrite <- (wire_removal_l (𝒵 1 top 0)).
	rewrite <- (nwire_removal_r (𝒵 (S input + bot) _ _)).
	rewrite stack_compose_distr.
	rewrite <- compose_assoc.
	rewrite (stack_assoc ⊂ (n_wire input)).
	simpl_casts.
	rewrite <- nstack1_split.
	rewrite <- (Z_wrap_over_top_right (input + bot)).
	rewrite (Z_add_r 1%nat output).
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (𝒵 1 1 α)).
	rewrite Z_absolute_fusion.
	cleanup_zx.
	rewrite <- Z_add_r.
	replace (α + 0 + β + 0)%R with (α + β)%R by lra.
	easy.
Qed.

Lemma Z_spider_fusion_bot_left_top_right : forall top mid bot input output α β,
	((n_wire top ↕ 𝒵 input (S mid + bot) α) ⟷
	cast (top + ((S mid) + bot)) _ ((Nat.add_assoc _ _ _)) eq_refl 
		(𝒵 (top + (S mid)) output β ↕ n_wire bot)) ∝
	𝒵 (top + input) (output + bot) (β + α).
Proof.
	intros.
	apply transpose_diagrams.
	simpl.
	rewrite <- (Z_spider_fusion_top_left_bot_right top mid bot).
	autorewrite with transpose_db.
Opaque cast.
	simpl.
Transparent cast.
	rewrite cast_compose_l.
	simpl_casts.
	autorewrite with transpose_db.
	easy.
Qed.

Lemma Z_self_cap_absorbtion_base : forall {n} α, 𝒵 n 2%nat α ⟷ ⊃ ∝ 𝒵 n 0%nat α.
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

Lemma Z_self_cap_absorbtion_top : forall {n m α}, 𝒵 n (S (S m)) α ⟷ (⊃ ↕ n_wire m) ∝ 𝒵 n m α.
Proof.
	intros.
	rewrite (Z_add_r_base_rot 2 m).
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (𝒵 1 2 _) ⊃ (𝒵 1 m _) (n_wire m)).
	rewrite Z_self_cap_absorbtion_base.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_self_cup_absorbtion_top : forall {n m α}, ((⊂ ↕ n_wire n) ⟷ 𝒵 (S (S n)) m α) ∝ (𝒵 n m α).
Proof. intros. transpose_of (@Z_self_cap_absorbtion_top m n). Qed.

Lemma Z_self_cap_absorbtion : forall {n m m' α}, 𝒵 n (m + (S (S m'))) α ⟷ (n_wire m ↕ (⊃ ↕ n_wire m')) ∝ (𝒵 n (m + m') α).
Proof.
	intros.
	rewrite Z_add_r_base_rot.
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (𝒵 1 m _) (n_wire m) (𝒵 1 (S (S m')) _) (⊃ ↕ n_wire m')).
	rewrite Z_self_cap_absorbtion_top.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_self_cup_absorbtion : forall {n n' m α}, ((n_wire n ↕ (⊂ ↕ n_wire n')) ⟷ 𝒵 (n + (S (S n'))) m α) ∝ (𝒵 (n + n') m α).
Proof. intros. transpose_of (@Z_self_cap_absorbtion m n n'). Qed.

Lemma Z_self_loop_removal_top : forall {n m α}, 𝒵 n m α ∝ (⊂ ↕ n_wire n) ⟷ (— ↕ 𝒵 (S n) (S m) α) ⟷ (⊃ ↕ n_wire m).
Proof.
	intros.
	rewrite <- Z_wrap_over_top_right.
	rewrite Z_self_cap_absorbtion_top.
	easy.
Qed.

Lemma Z_self_swap_absorbtion_right_base : forall {n α}, 𝒵 n 2 α ⟷ ⨉ ∝ 𝒵 n 2 α.
Proof. intros. solve_prop 1. Qed.

Lemma Z_self_swap_absorbtion_right_top : forall {n m α}, 𝒵 n (S (S m)) α ⟷ (⨉ ↕ n_wire m) ∝ 𝒵 n (S (S m)) α.
Proof.
	intros.
	rewrite (Z_add_r_base_rot 2 m) at 1.
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (𝒵 1 2 0) (⨉) (𝒵 1 m 0) (n_wire m)).
	rewrite Z_self_swap_absorbtion_right_base.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_self_swap_absorbtion_right : forall {n m m' α}, 𝒵 n (m' + S (S m)) α ⟷ (n_wire m' ↕ (⨉ ↕ n_wire m)) ∝ 𝒵 n (m' + S (S m)) α.
Proof.
	intros.
	rewrite Z_add_r_base_rot at 1.
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (𝒵 1 m' 0) (n_wire _) (𝒵 1 (S (S m)) 0) (⨉ ↕ n_wire _)).
	rewrite Z_self_swap_absorbtion_right_top.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_self_swap_absorbtion_left_base : forall {m α}, (⨉ ⟷ 𝒵 2 m α) ∝ 𝒵 2 m α.
Proof. intros. transpose_of (@Z_self_swap_absorbtion_right_base m α). Qed.

Lemma Z_self_swap_absorbtion_left_top : forall {n m α}, ((⨉ ↕ n_wire n) ⟷ 𝒵 (S (S n)) m α) ∝ 𝒵 (S (S n)) m α.
Proof. intros. transpose_of (@Z_self_swap_absorbtion_right_top m n α). Qed.

Lemma Z_self_swap_absorbtion_left : forall {n n' m α}, ((n_wire n' ↕ (⨉ ↕ n_wire n)) ⟷ 𝒵 (n' + S (S n)) m α) ∝ 𝒵 (n' + S (S n)) m α.
Proof. intros. transpose_of (@Z_self_swap_absorbtion_right m n n' α). Qed.

(* @nocheck Z_X *)
Lemma wrap_under_dimension : forall n, (n + 1 + 1 = n + 2)%nat.
Proof. lia. Qed.

Lemma Z_wrap_under_bot_left : forall n m α,
	𝒵 n (m + 1) α ∝ 
	(cast n (n + 1 + 1) 
		(eq_sym (Nat.add_0_r _)) (wrap_under_dimension _)
		(n_wire n ↕ ⊂)) ⟷
			(𝒵 (n + 1) m α ↕ Wire).
Proof.
	intros.
	rewrite (Z_add_l_base_rot).
	rewrite stack_wire_distribute_r.
	rewrite Z_0_is_wire.
	rewrite stack_assoc.
	rewrite <- compose_assoc.
	simpl.
	eapply (cast_diagrams (n + 0) (m + 1)).
	repeat rewrite cast_compose_distribute.
	simpl_casts.
	erewrite (@cast_compose_mid (n + 0) (n + 1 + 1) 3 (n + 2) _ ($ n + 0, n + 1 + 1 ::: n_wire n ↕ ⊂ $)).
	simpl_casts.
	rewrite <- Z_0_2_0_is_cup.
	rewrite wire_to_n_wire at 2.
	rewrite wire_to_n_wire at 3.
	rewrite n_wire_stack.
	rewrite <- (stack_compose_distr
		(n_wire n) (𝒵 n 1 0)
		(𝒵 0 2 0)  (n_wire 2)).
	cleanup_zx.
	rewrite <- (nwire_removal_r (𝒵 n 1 0)).
	rewrite <- (nwire_removal_l (𝒵 0 2 0)).
	rewrite stack_compose_distr.
	rewrite compose_assoc.
	rewrite wire_to_n_wire at 3.
	specialize (Z_spider_fusion_bot_left_top_right 
		1 0 1 0 m 0 α); intros.
	rewrite cast_id in H.
	rewrite H.
	clear H.
	cleanup_zx.
	simpl_casts.
	rewrite Z_absolute_fusion.
	rewrite Rplus_0_r.
	rewrite Rplus_0_l.
	easy.
	Unshelve.
	all: lia.
Qed.

Lemma Z_wrap_under_bot_right : forall n m α,
	𝒵 (n + 1) m α ∝ 
		(𝒵 n (m + 1) α ↕ —) ⟷ 
	(cast (m + 1 + 1) m
		(wrap_under_dimension _)
		(eq_sym (Nat.add_0_r _))
		(n_wire m ↕ ⊃)).
Proof. transpose_of Z_wrap_under_bot_left. Qed.