Require Import CoreData.CoreData.
Require Import CoreAutomation.
Require Import CapCupRules.
Require Import CastRules.
Require Import StackComposeRules.
Require Import SwapRules.
Require Import WireRules.
Require Import SpiderInduction.
Require Import ZXpermFacts.

Lemma grow_Z_top_left : forall (nIn nOut : nat) α,
	Z (S (S nIn)) nOut α ∝=
	(Z 2 1 0) ↕ (n_wire nIn) ⟷ (Z (S nIn) nOut α).
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
	Z nIn (S (S nOut)) α ∝=
	(Z nIn (S nOut) α) ⟷ ((Z_Spider 1 2 0) ↕ (n_wire nOut)).
Proof.
	intros.
	apply transpose_diagrams_eq.
	simpl.
	rewrite n_wire_transpose.
	apply grow_Z_top_left.
Qed.

Lemma grow_Z_bot_left : forall n {m o α},
	Z (n + m) o α ∝=
	(n_wire n ↕ Z m 1 0) ⟷ Z (n + 1) o α.
Proof.
	intros n m o α.
	hnf.
	cbn.
	rewrite !Z_semantics_equiv, n_wire_semantics.
	simpl.
	rewrite Cexp_0.
	Msimpl.
	restore_dims.
	distribute_plus.
	distribute_scale.
	rewrite 2!(kron_n_m_split n 1), !kron_n_1 by auto_wf.
	rewrite !Mmult_assoc.
	restore_dims.
	rewrite !kron_mixed_product, !Mmult_1_r by auto_wf.
	restore_dims.
	rewrite <- !Mmult_assoc.
	rewrite Mmult00, Mmult01, Mmult10, Mmult11.
	Msimpl.
	restore_dims.
	Msimpl.
	now rewrite <- !kron_n_m_split by auto_wf.
Qed.

Lemma grow_Z_bot_right : forall {n m} o {α},
	Z n (m + o) α ∝=
	Z n (m + 1) α ⟷ (n_wire m ↕ Z 1 o 0).
Proof.
	intros.
	apply transpose_diagrams_eq.
	simpl.
	rewrite n_wire_transpose.
	apply grow_Z_bot_left.
Qed.

Lemma Z_rot_passthrough : forall α β, 
	(Z 1 1 α ↕ — ⟷ Z 2 1 β) ∝= Z 2 1 β ⟷ Z 1 1 α.
Proof. intros ? ?; lma'. Qed.

Lemma Z_rot_l : forall n m α β,
	Z (S n) m (α + β) ∝= Z 1 1 α ↕ n_wire n ⟷ Z (S n) m β.
Proof.
	induction n; intros.
	- cleanup_zx.
		simpl_casts.
		rewrite Z_spider_1_1_fusion.
		easy.
	- cbn.
		rewrite (grow_Z_top_left n m β).
		rewrite <- compose_assoc.
		auto_cast_eqn (rewrite (stack_assoc_back (Z 1 1 α) —)).
		simpl_casts.
		rewrite <- (stack_compose_distr (Z 1 1 α ↕ —) (Z 2 1 0) (n_wire n)).
		cleanup_zx.
		rewrite Z_rot_passthrough.
		rewrite stack_nwire_distribute_r.
		rewrite compose_assoc.
		rewrite <- IHn.
		rewrite <- (grow_Z_top_left n).
		easy.
Qed.

Lemma Z_rot_r : forall n m α β,
	Z n (S m) (α + β) ∝= Z n (S m) α ⟷ (Z 1 1 β ↕ n_wire m).
Proof.
	intros.
	rewrite Rplus_comm.
	apply transpose_diagrams_eq.
	simpl.
	rewrite n_wire_transpose.
	apply Z_rot_l.
Qed.

Lemma Z_appendix_base : forall α β,
	(Z 0 1 α ↕ — ⟷ Z 2 1 β) ∝= Z 1 1 (α + β).
Proof. 
	intros. 
	hnf.
	Msimpl.
	prep_matrix_equivalence. 
	cbn; unfold Z_semantics.
	rewrite Cexp_add.
	by_cell; lca. 
Qed.

Lemma Z_appendix_rot_l : forall n m α β,
	Z n m (α + β) ∝= (Z 0 1 α ↕ n_wire n) ⟷ Z (S n) m β.
Proof.
	induction n; intros.
	- cleanup_zx.
		simpl_casts.
		rewrite Z_spider_1_1_fusion.
		easy.
	- rewrite grow_Z_top_left.
		cbn.
		rewrite (stack_assoc_back (Z 0 1 α) —).
		simpl_casts.
		rewrite <- compose_assoc.
		rewrite <- (@stack_nwire_distribute_r _ _ _ n (Z 0 1 α ↕ —) (Z 2 1 0)).
		rewrite Z_appendix_base.
		rewrite <- Z_rot_l.
		rewrite Rplus_0_r.
		easy.
Unshelve.
all: lia.
Qed.

Lemma Z_appendix_rot_r : forall n m α β,
	Z n m (β + α) ∝= Z n (S m) α ⟷ (Z 1 0 β ↕ n_wire m).
Proof. 
	intros.
	apply transpose_diagrams_eq.
	simpl.
	rewrite n_wire_transpose.
	apply Z_appendix_rot_l.
Qed.

Lemma Z_wrap_over_top_left : forall n m α,
	Z (S n) m α ∝= (Wire ↕ Z n (S m) α) ⟷  (Cap ↕ n_wire m).
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
			rewrite <- (stack_empty_l (Z 1 2 0 ↕ (m ↑ —))).
			fold (n_wire m).
			replace ⦰ with (n_wire 0) by auto.
			specialize (nwire_stack_compose_botleft ⊃ (Z 1 2 0 ↕ n_wire m)); intros.
			simpl in H.
			rewrite compose_assoc.
			rewrite H.
			clear H.
			specialize (nwire_stack_compose_topleft (Z 1 2 0 ↕ n_wire m) ⊃); intros.
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
				((Z) n (S m) α ⟷ ((Z) 1 2 0 ↕ (m ↑ —))) 
				(— ↕ ((Z) 1 2 0 ↕ n_wire m))).
			rewrite compose_assoc.
			fold (n_wire m).
			rewrite stack_assoc_back.
			simpl_casts.
			rewrite <- (stack_compose_distr (Z 1 2 0) (— ↕ Z 1 2 0) 
																					(n_wire m) (n_wire m)).
			rewrite <- grow_Z_right_bot_1_2_base.
			rewrite grow_Z_top_right.
			rewrite stack_compose_distr.
			rewrite <- compose_assoc.
			rewrite <- grow_Z_top_right.
			rewrite (stack_assoc (Z 1 2 0) (1 ↑ —) (m ↑ —)).
			simpl_casts.
			rewrite <- nstack1_split.
			rewrite <- (grow_Z_top_right n (S m)).
			easy.
Unshelve.
all: lia.
Qed.

Lemma Z_wrap_over_top_right : forall n m α,
	Z n (S m) α ∝= (Cup ↕ n_wire n) ⟷ (Wire ↕ Z (S n) m α).
Proof. 
	intros. apply transpose_diagrams_eq. simpl. 
	rewrite n_wire_transpose.
	apply Z_wrap_over_top_left.
Qed.

Lemma Z_add_r : forall {n} m o {α β γ},
	Z n (m + o) (α + β + γ) ∝= Z n 2 β ⟷ (Z 1 m α ↕ Z 1 o γ).
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
			rewrite <- (nwire_removal_l (Z 1 o γ)).
			rewrite <- (nwire_removal_r (Z 1 1 α)).
			rewrite stack_compose_distr.
			rewrite <- compose_assoc.
			rewrite <- Z_rot_r.
			rewrite (Z_wrap_over_top_right n 1).
			simpl.
			bundle_wires.
			rewrite compose_assoc.
			change (1 + 0)%nat with 1%nat.
			bundle_wires.
			rewrite <- stack_wire_distribute_l.
			rewrite Z_spider_1_1_fusion.
			rewrite <- (Z_wrap_over_top_right n o).
			rewrite (Rplus_comm β α).
			easy.
		+ simpl.
			rewrite (grow_Z_top_right 1 m).
			rewrite <- (nwire_removal_r (Z 1 o _)).
			rewrite stack_compose_distr.
			rewrite <- compose_assoc.
			rewrite <- IHm.
			rewrite (stack_assoc (Z 1 2 0) (n_wire m) (n_wire o)).
			simpl_casts.
			rewrite n_wire_stack.
			rewrite <- (grow_Z_top_right n (m + o)).
			easy.
Unshelve.
all: lia.
Qed.

Lemma Z_add_l : forall n m {o α β γ},
	Z (n + m) o (α + β + γ) ∝= (Z n 1 α ↕ Z m 1 γ) ⟷ Z 2 o β.
Proof. intros. transpose_of (@Z_add_r o n m). Qed.

Lemma Z_add_r_base_rot : forall {n} m o {α}, Z n (m + o) α ∝= 
	Z n 2 α ⟷ (Z 1 m 0 ↕ Z 1 o 0).
Proof. 
	intros.
	rewrite <- (@Z_add_r n m o 0 α 0).
	rewrite Rplus_0_l, Rplus_0_r.
	easy.
Qed.

Lemma Z_add_l_base_rot : forall {n} m o {α}, Z (n + m) o α ∝= 
	(Z n 1 0 ↕ Z m 1 0) ⟷ Z 2 o α.
Proof. intros. transpose_of (@Z_add_r_base_rot o n m). Qed.

Lemma Z_1_2_1_fusion : forall α β,
	(Z 1 2 α ⟷ Z 2 1 β) ∝= (Z 1 1 (α + β)).
Proof. intros. lma'. rewrite Cexp_add; lca. Qed.

Lemma Z_absolute_fusion : forall {n m o} α β,
	(Z n (S m) α ⟷ Z (S m) o β) ∝=
	Z n o (α + β).
Proof.
	intros.
	induction m.
	- apply Z_spider_1_1_fusion.
	- rewrite grow_Z_top_right, grow_Z_top_left.
		rewrite compose_assoc.
		rewrite <- (compose_assoc ((Z 1 2 0) ↕ (m ↑ —))
																 ((Z 2 1 0) ↕ (m ↑ —))
																	(Z (S m) o β)).
		rewrite <- stack_compose_distr.
		rewrite Z_1_2_1_fusion.
		rewrite Rplus_0_l.
		cleanup_zx.
		apply IHm.
Qed.

Lemma Z_split_left : forall n m α,
	Z n m α ∝= Z n 1 α ⟷ Z 1 m 0.
Proof.
	intros n m α.
	rewrite Z_absolute_fusion.
	now rewrite Rplus_0_r.
Qed.

Lemma Z_split_right : forall n m α,
	Z n m α ∝= Z n 1 0 ⟷ Z 1 m α.
Proof.
	intros n m α.
	rewrite Z_absolute_fusion.
	now rewrite Rplus_0_l.
Qed.

Lemma dominated_Z_spider_fusion_top_right : forall n m0 m1 o α β,
	(Z n (S m0) α ↕ n_wire m1 ⟷ Z (S m0 + m1) o β) ∝=
	Z (n + m1) o (α + β).
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
	((n_wire m1 ↕ (Z n (S m0) α)) ⟷ Z (m1 + (S m0)) o β) ∝=
	Z (m1 + n) o (α + β).
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
	Z i (S n0 + n1) β ⟷ (Z (S n0) m α ↕ n_wire n1) ∝=
	Z i (m + n1) (α + β).
Proof. intros. transpose_of dominated_Z_spider_fusion_top_right. Qed.

Lemma dominated_Z_spider_fusion_bot_left : forall m n0 n1 i α β,
	Z i (n1 + S n0) β ⟷ (n_wire n1 ↕ Z (S n0) m α) ∝=
	Z i (n1 + m) (α + β).
Proof. intros. transpose_of dominated_Z_spider_fusion_bot_right. Qed.

Lemma Z_spider_fusion_top_left_bot_right : forall top mid bot input output α β prfn prfm,
	Z input (top + S mid) α ↕ n_wire bot ⟷
	cast (top + (S mid) + bot) (top + output) prfn prfm 
		(n_wire top ↕ Z (S mid + bot) output β) ∝=
	Z (input + bot) (top + output) (α + β).
Proof.
	intros.
	replace α%R with (0 + α + 0)%R at 1 by lra.
	rewrite Z_add_r.
	rewrite stack_nwire_distribute_r.
	rewrite compose_assoc.
	rewrite (stack_assoc (Z 1 top 0)).
	rewrite cast_compose_r.
	simpl_casts.
	rewrite <- (stack_compose_distr (Z 1 top 0) (n_wire top) (Z 1 (S mid) 0 ↕ n_wire bot)).
	cleanup_zx.
	rewrite dominated_Z_spider_fusion_top_right.
	rewrite <- (Rplus_0_r (0 + β)).
	rewrite Z_add_l.
	simpl.
	cleanup_zx.
	rewrite Z_wrap_over_top_right.
	rewrite stack_nwire_distribute_r.
	rewrite (stack_assoc — (Z (S input) 1 α) (n_wire bot)).
	simpl_casts.
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr — (Z 1 top 0) (Z (S input) 1 α ↕ n_wire bot)).
	cleanup_zx.
	rewrite wire_to_n_wire.
	rewrite <- compose_assoc.
	rewrite (nwire_stack_compose_botleft (Z (S input) 1 α)).
	rewrite <- Z_add_l.
	rewrite <- (wire_removal_l (Z 1 top 0)).
	rewrite <- (nwire_removal_r (Z (S input + bot) _ _)).
	rewrite stack_compose_distr.
	rewrite <- compose_assoc.
	rewrite (stack_assoc ⊂ (n_wire input)).
	simpl_casts.
	rewrite n_wire_stack.
	rewrite <- (Z_wrap_over_top_right (input + bot)).
	rewrite (Z_add_r 1%nat output).
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (Z 1 1 α)).
	rewrite Z_absolute_fusion.
	cleanup_zx.
	rewrite <- Z_add_r.
	replace (α + 0 + β + 0)%R with (α + β)%R by lra.
	easy.
Unshelve.
all: lia.
Qed.

Lemma Z_spider_fusion_bot_left_top_right : forall top mid bot input output α β prfn prfm,
	((n_wire top ↕ Z input (S mid + bot) α) ⟷
	cast (top + ((S mid) + bot)) _ prfn prfm 
		(Z (top + (S mid)) output β ↕ n_wire bot)) ∝=
	Z (top + input) (output + bot) (β + α).
Proof.
	intros.
	apply transpose_diagrams_eq.
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

Lemma Z_self_cap_absorbtion_base : forall {n} α, Z n 2%nat α ⟷ ⊃ ∝= 
	Z n 0%nat α.
Proof.
	intros n α.
	rewrite <- (Rplus_0_l α).
	rewrite <- 2!(@Z_absolute_fusion _ 0).
	rewrite compose_assoc.
	apply compose_simplify_eq; [reflexivity|].
	lma'.
Qed.

Lemma Z_self_cap_absorbtion_top : forall {n m α}, 
	Z n (S (S m)) α ⟷ (⊃ ↕ n_wire m) ∝= Z n m α.
Proof.
	intros.
	rewrite (Z_add_r_base_rot 2 m).
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (Z 1 2 _) ⊃ (Z 1 m _) (n_wire m)).
	rewrite Z_self_cap_absorbtion_base.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_self_cup_absorbtion_top : forall {n m α}, 
	((⊂ ↕ n_wire n) ⟷ Z (S (S n)) m α) ∝= (Z n m α).
Proof. intros. transpose_of (@Z_self_cap_absorbtion_top m n). Qed.

Lemma Z_self_cap_absorbtion : forall {n m m' α}, 
	Z n (m + (S (S m'))) α ⟷ (n_wire m ↕ (⊃ ↕ n_wire m')) ∝= (Z n (m + m') α).
Proof.
	intros.
	rewrite Z_add_r_base_rot.
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (Z 1 m _) (n_wire m) (Z 1 (S (S m')) _) (⊃ ↕ n_wire m')).
	rewrite Z_self_cap_absorbtion_top.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_self_cup_absorbtion : forall {n n' m α}, 
	((n_wire n ↕ (⊂ ↕ n_wire n')) ⟷ Z (n + (S (S n'))) m α) ∝= (Z (n + n') m α).
Proof. intros. transpose_of (@Z_self_cap_absorbtion m n n'). Qed.

Lemma Z_self_loop_removal_top : forall {n m α}, 
	Z n m α ∝= (⊂ ↕ n_wire n) ⟷ (— ↕ Z (S n) (S m) α) ⟷ (⊃ ↕ n_wire m).
Proof.
	intros.
	rewrite <- Z_wrap_over_top_right.
	rewrite Z_self_cap_absorbtion_top.
	easy.
Qed.

Lemma Z_self_swap_absorbtion_right_base : forall {n α}, Z n 2 α ⟷ ⨉ ∝= Z n 2 α.
Proof. 
	intros n α.
	rewrite <- (Rplus_0_l α).
	rewrite <- (@Z_absolute_fusion _ 0).
	rewrite compose_assoc.
	apply compose_simplify_eq; [reflexivity|].
	lma'.
Qed.

Lemma Z_self_swap_absorbtion_right_top : forall {n m α}, 
	Z n (S (S m)) α ⟷ (⨉ ↕ n_wire m) ∝= Z n (S (S m)) α.
Proof.
	intros.
	rewrite (Z_add_r_base_rot 2 m) at 1.
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (Z 1 2 0) (⨉) (Z 1 m 0) (n_wire m)).
	rewrite Z_self_swap_absorbtion_right_base.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_self_swap_absorbtion_right : forall {n m m' α}, 
	Z n (m' + S (S m)) α ⟷ (n_wire m' ↕ (⨉ ↕ n_wire m)) ∝= Z n (m' + S (S m)) α.
Proof.
	intros.
	rewrite Z_add_r_base_rot at 1.
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (Z 1 m' 0) (n_wire _) (Z 1 (S (S m)) 0) (⨉ ↕ n_wire _)).
	rewrite Z_self_swap_absorbtion_right_top.
	cleanup_zx.
	rewrite <- Z_add_r_base_rot.
	easy.
Qed.

Lemma Z_self_swap_absorbtion_left_base : forall {m α}, (⨉ ⟷ Z 2 m α) ∝= Z 2 m α.
Proof. intros. transpose_of (@Z_self_swap_absorbtion_right_base m α). Qed.

Lemma Z_self_swap_absorbtion_left_top : forall {n m α}, ((⨉ ↕ n_wire n) ⟷ Z (S (S n)) m α) ∝= Z (S (S n)) m α.
Proof. intros. transpose_of (@Z_self_swap_absorbtion_right_top m n α). Qed.

Lemma Z_self_swap_absorbtion_left : forall {n n' m α}, ((n_wire n' ↕ (⨉ ↕ n_wire n)) ⟷ Z (n' + S (S n)) m α) ∝= Z (n' + S (S n)) m α.
Proof. intros. transpose_of (@Z_self_swap_absorbtion_right m n n' α). Qed.


Lemma Z_wrap_under_bot_left : forall n m α prfn prfm,
	Z n (m + 1) α ∝=
	(cast n (n + 1 + 1) 
		prfn prfm
		(n_wire n ↕ ⊂)) ⟷
			(Z (n + 1) m α ↕ Wire).
Proof.
	intros.
	rewrite (Z_add_l_base_rot).
	rewrite stack_wire_distribute_r.
	rewrite Z_0_is_wire.
	rewrite stack_assoc.
	rewrite <- compose_assoc.
	simpl.
	eapply (cast_diagrams_eq (n + 0) (m + 1)).
	repeat rewrite cast_compose_distribute.
	simpl_casts.
	erewrite (@cast_compose_mid (n + 0) (n + 1 + 1) 3 (n + 2) _ _ ($ n + 0, n + 1 + 1 ::: n_wire n ↕ ⊂ $)).
	rewrite !cast_contract, !cast_id.
	rewrite <- Z_0_2_0_is_cup.
	bundle_wires.
	rewrite <- (stack_compose_distr
		(n_wire n) (Z n 1 0)
		(Z 0 2 0)  (n_wire 2)).
	cleanup_zx.
	rewrite <- (nwire_removal_r (Z n 1 0)).
	rewrite <- (nwire_removal_l (Z 0 2 0)).
	rewrite stack_compose_distr.
	rewrite compose_assoc.
	rewrite wire_to_n_wire.
	specialize (Z_spider_fusion_bot_left_top_right 
		1 0 1 0 m 0 α); intros.
	specialize (H eq_refl eq_refl).
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

Lemma Z_wrap_under_bot_right : forall n m α prfn prfm,
	Z (n + 1) m α ∝=
		(Z n (m + 1) α ↕ —) ⟷ 
	(cast (m + 1 + 1) m
		prfn
		prfm
		(n_wire m ↕ ⊃)).
Proof. transpose_of Z_wrap_under_bot_left. Qed.

Lemma Z_self_top_to_bottom_absorbtion_right_base : forall n m α, 
	Z n m α ⟷ top_to_bottom m ∝= Z n m α.
Proof.
	intros.
	destruct m; [ simpl; cleanup_zx; easy | ].
	destruct m; [ simpl; cleanup_zx; easy | ].
	generalize dependent n.
	generalize dependent α.
	induction m; intros.
	- simpl.
		cleanup_zx.
		rewrite cast_id.
		rewrite wire_to_n_wire, n_wire_stack, nwire_removal_r.
		apply Z_self_swap_absorbtion_right_base.
	- rewrite top_to_bottom_grow_r.
		erewrite <- (@cast_Z n _  ((S (S m)) + 1)).
		rewrite Z_add_r_base_rot.
		erewrite (cast_compose_mid ((S (S m)) + 1)).
		rewrite cast_contract.
		rewrite cast_id.
		rewrite compose_assoc.
		rewrite cast_compose_l.
		rewrite !cast_contract, cast_id.
		rewrite <- (compose_assoc (Z 1 (S (S m)) 0 ↕ Z 1 1 0)).
		rewrite <- stack_compose_distr.
		rewrite IHm.
		rewrite wire_removal_r.
		rewrite <- compose_assoc.
		rewrite <- Z_add_r.
		rewrite cast_Z.
		rewrite cast_compose_r.
		rewrite cast_Z.
		rewrite (stack_empty_r_back ⨉).
		replace ⦰ with (n_wire 0) by easy.
		rewrite cast_id.
		rewrite Z_self_swap_absorbtion_right.
		rewrite cast_Z.
		reflexivity.
Unshelve.
	all: lia.
Qed.

Lemma Z_self_bottom_to_top_absorbtion_right_base : forall n m α, 
	Z n m α ⟷ bottom_to_top m ∝= Z n m α.
Proof.
	intros.
	destruct m; [ simpl; cleanup_zx; easy | ].
	destruct m; [ simpl; cleanup_zx; easy | ].
	generalize dependent n.
	generalize dependent α.
	induction m; intros.
	- simpl.
		unfold bottom_to_top, top_to_bottom.
		simpl.
		cleanup_zx.
		rewrite cast_id, wire_to_n_wire, n_wire_stack, nwire_removal_l.
		apply Z_self_swap_absorbtion_right_base.
	- rewrite bottom_to_top_grow_r.
		erewrite <- (@cast_Z n _  (1 + (S (S m)))).
		rewrite Z_add_r_base_rot.
		erewrite (cast_compose_mid (1 + (S (S m)))).
		rewrite cast_contract.
		simpl_casts.
		rewrite compose_assoc.
		rewrite <- (compose_assoc (Z 1 1 0 ↕ Z 1 (S (S m)) 0)).
		rewrite <- stack_compose_distr.
		rewrite IHm.
		rewrite wire_removal_r.
		rewrite <- compose_assoc.
		rewrite <- Z_add_r.
		rewrite <- (stack_empty_l ⨉).
		replace ⦰ with (n_wire 0) by easy.
		erewrite <- (@cast_Z n _ (0 + (S (S (S m))))).
		rewrite cast_compose_l.
		rewrite (stack_assoc (n_wire 0) ⨉ (n_wire _)).
		simpl_casts.
		rewrite Z_self_swap_absorbtion_right.
		easy.
Unshelve.
	all: lia.
Qed.

Lemma Z_a_swap_absorbtion_right_base : forall n m α, 
	Z n m α ⟷ a_swap m ∝= Z n m α.
Proof.
	intros.
	destruct m; [ simpl; cleanup_zx; easy | ].
	destruct m; [ simpl; cleanup_zx; easy | ].
	Local Opaque top_to_bottom.
	simpl.
	rewrite <- compose_assoc.
	rewrite (Z_self_bottom_to_top_absorbtion_right_base n (S (S m)) α).
	rewrite <- (@cast_Z n _ (1 + (S m))) at 1.  
	rewrite Z_add_r_base_rot at 1.
	simpl_casts.
	rewrite compose_assoc.
	rewrite <- (stack_compose_distr (Z 1 1 0) —).
	rewrite Z_self_top_to_bottom_absorbtion_right_base.
	rewrite wire_removal_r.
	rewrite <- (Z_add_r_base_rot 1 (S m)).
	easy.
Unshelve.
  all: lia.
Qed.

Lemma Z_stacked_a_swap_absorbtion_right n m0 m1 m2 α : 
	Z n (m0 + m1 + m2) α ⟷ (n_wire m0 ↕ a_swap m1 ↕ n_wire m2) ∝=
	Z n (m0 + m1 + m2) α.
Proof.
	rewrite 2!Z_add_r_base_rot, compose_assoc.
	rewrite <- (nwire_removal_l (Z 1 m2 0)).
	rewrite stack_compose_distr, compose_assoc.
	rewrite <- stack_compose_distr.
	rewrite <- (stack_compose_distr (Z 1 m0 0)).
	rewrite 2!nwire_removal_r.
	now rewrite Z_a_swap_absorbtion_right_base.
Qed.

Lemma Z_zx_to_bot_absorbtion_right n m α a : 
	Z n m α ⟷ zx_to_bot a m ∝=
	Z n m α.
Proof.
	unfold zx_to_bot.
	rewrite cast_Z_contract_r.
	rewrite grow_Z_bot_right, compose_assoc, <- stack_compose_distr.
	rewrite Z_a_swap_absorbtion_right_base, nwire_removal_l.
	rewrite <- grow_Z_bot_right.
	now simpl_casts.
Qed.

Lemma Z_zx_of_swap_list_absorbtion_right n α l : 
	Z n (length l) α ⟷ zx_of_swap_list l ∝=
	Z n (length l) α.
Proof.
	revert n α;
	induction l; intros n α.
	- simpl.
		now cleanup_zx.
	- simpl.
		rewrite <- compose_assoc.
		rewrite Z_zx_to_bot_absorbtion_right.
		rewrite cast_Z_contract_r.
		rewrite Z_add_r_base_rot, compose_assoc.
		rewrite <- (stack_compose_distr (Z 1 (length l) 0)).
		rewrite wire_removal_r, IHl.
		rewrite <- Z_add_r_base_rot.
		now simpl_casts.
Qed.

Lemma Z_zx_of_perm_absorbtion_right n m α f : 
	Z n m α ⟷ zx_of_perm m f ∝=
	Z n m α.
Proof.
	unfold zx_of_perm.
	rewrite cast_Z_contract_r.
	unfold zx_of_perm_uncast.
	rewrite Z_zx_of_swap_list_absorbtion_right.
	now simpl_casts.
Qed.

Lemma Z_zx_of_perm_cast_absorbtion_right n m o α f H : 
	Z n m α ⟷ zx_of_perm_cast m o f H ∝=
	Z n o α.
Proof.
	subst.
	apply Z_zx_of_perm_absorbtion_right.
Qed.

Lemma Z_zxperm_absorbtion_right n m o α 
	(zx : ZX m o) (Hzx : ZXperm zx) :
	Z n m α ⟷ zx ∝= 
	Z n o α.
Proof.
	rewrite (zxperm_to_zx_of_perm_cast zx Hzx).
	apply Z_zx_of_perm_cast_absorbtion_right.
Qed.

Lemma Z_zxperm_absorbtion_left n m o α 
	(zx : ZX n m) (Hzx : ZXperm zx) : 
	zx ⟷ Z m o α ∝=
	Z n o α.
Proof.
	transpose_of (Z_zxperm_absorbtion_right o m n α 
		(zx⊤) (transpose_zxperm Hzx)).
Qed.

Lemma Z_zx_comm_absorbtion_right n p q α : 
	Z n (p + q) α ⟷ zx_comm p q ∝=
	Z n (q + p) α.
Proof.
	apply Z_zxperm_absorbtion_right; auto_zxperm.
Qed.

Lemma Z_zx_comm_absorbtion_left p q m α :
	zx_comm p q ⟷ Z (q + p) m α ∝=
	Z (p + q) m α.
Proof. transpose_of (Z_zx_comm_absorbtion_right m q p α). Qed.

Lemma Z_zx_gap_comm_absorbtion_right n p m q α : 
	Z n (p + m + q) α ⟷ zx_gap_comm p m q ∝=
	Z n (q + m + p) α.
Proof.
	apply Z_zxperm_absorbtion_right; auto_zxperm.
Qed.

Lemma Z_zx_gap_comm_absorbtion_left p n q m α : 
	zx_gap_comm p n q ⟷ Z (q + n + p) m α ∝=
	Z (p + n + q) m α.
Proof. transpose_of (Z_zx_gap_comm_absorbtion_right m q n p α). Qed.

Lemma Z_swap_pullthrough_top_right : forall n α prfn prfm, 
	((Z (S n) 1 α) ↕ —) ⟷ ⨉ ∝= 
	cast _ _ prfn prfm (n_swap _ ⟷ (— ↕ (Z (S n) 1 α))).
Proof.
  intros.
  rewrite swap_commutes_r.
  auto_cast_eqn erewrite (cast_compose_mid_contract _ (1 + (1 + n))%nat).
	rewrite n_swap_grow_l.
  auto_cast_eqn erewrite (cast_compose_mid_contract _ (1 + (1 + n))%nat).
	rewrite cast_id.
  (* rewrite cast_fn_eq_dim. *)
  change (S n) with (1 + n)%nat.
	change 2%nat with (1 + 1)%nat.
	auto_cast_eqn rewrite cast_stack_distribute.
	rewrite 2!cast_id.
	rewrite compose_assoc.
	rewrite <- stack_wire_distribute_l.
	rewrite Z_zxperm_absorbtion_left by auto with zxperm_db.
	apply compose_simplify_eq; [|easy].
	unfold zx_comm, zx_of_perm_cast.
	simpl_casts.
	by_perm_eq_nosimpl.
	rewrite perm_of_bottom_to_top_eq.
	change (S (1 + n)) with (1 + (1 + n))%nat.
	rewrite (Nat.add_comm 1 (1 + n)).
	rewrite perm_of_zx_of_perm_eq, 
		bottom_to_top_perm_eq_rotl by auto_perm.
	now rewrite rotl_add_r.
Qed.

Lemma Z_n_swap_absorbtion_right_base : forall n m α, Z n m α ⟷ n_swap m ∝= Z n m α.
Proof.
	intros.
	apply Z_zxperm_absorbtion_right; auto_zxperm.
Qed.

Lemma Z_n_swap_absorbtion_left_base : forall n m α, n_swap n ⟷ Z n m α ∝= Z n m α.
Proof.
	transpose_of Z_n_swap_absorbtion_right_base.
Qed.

Lemma Z_n_wrap_under_r_base_unswapped : forall n m α, Z (n + m) 0 α ∝= (Z n m α ↕ n_wire m) ⟷ n_cup_unswapped m.
Proof.
	intros n m α.
	rewrite (Z_split_left n m), stack_nwire_distribute_r.
	rewrite compose_assoc, n_cup_unswapped_pullthrough_top.
	cbn [ZXCore.transpose].
	rewrite Z_zxperm_absorbtion_left, Z_zxperm_absorbtion_right by auto_zxperm.
	rewrite <- compose_assoc, <- stack_compose_distr.
	rewrite nwire_removal_l, nwire_removal_r.
	unfold n_cup_unswapped.
	rewrite cup_Z.
	rewrite Z_zxperm_absorbtion_left by auto_zxperm.
	rewrite <- Z_add_l.
	now rewrite 2!Rplus_0_r.
Qed.
	
Lemma Z_n_wrap_under_r_base : forall n m α, 
	Z (n + m) 0 α ∝= (Z n m α ↕ n_wire m) ⟷ n_cup m.
Proof.
	intros.
	unfold n_cup.
	rewrite <- compose_assoc.
	rewrite <- stack_nwire_distribute_r.
	rewrite Z_n_swap_absorbtion_right_base.
	rewrite Z_n_wrap_under_r_base_unswapped.
	easy.
Qed.

Lemma Z_n_wrap_over_r_base_unswapped : forall n m α, 
	Z (m + n) 0 α ∝= (n_wire m ↕ Z n m α) ⟷ n_cup_unswapped m.
Proof.
	intros n m α.
	rewrite Z_n_wrap_under_r_base_unswapped.
	rewrite n_cup_unswapped_pullthrough_top.
	cbn [ZXCore.transpose].
	now rewrite Z_zxperm_absorbtion_left, 
		Z_zxperm_absorbtion_right by auto_zxperm.
Qed.

Lemma Z_n_wrap_over_r_base : forall n m α, 
	Z (m + n) 0 α ∝= (n_wire m ↕ Z n m α) ⟷ n_cup m.
Proof.
	intros.
	unfold n_cup.
	rewrite <- compose_assoc.
	rewrite <- stack_compose_distr.
	cleanup_zx.
	rewrite <- (nwire_removal_l (Z n m α)).
	rewrite <- (nwire_removal_r (n_swap m)).
	rewrite stack_compose_distr.
	rewrite compose_assoc.
	rewrite <- Z_n_wrap_over_r_base_unswapped.
	rewrite Z_add_l_base_rot.
	rewrite <- compose_assoc.
	rewrite <- stack_compose_distr.
	cleanup_zx.
	rewrite Z_n_swap_absorbtion_left_base.
	rewrite <- Z_add_l_base_rot.
	easy.
Qed.

Lemma Z_n_wrap_over_l_base_unswapped : forall n m α, 
	Z 0 (n + m) α ∝= n_cap_unswapped n ⟷ (n_wire n ↕ Z n m α).
Proof. transpose_of Z_n_wrap_over_r_base_unswapped. Qed.

Lemma Z_n_wrap_over_l_base : forall n m α, 
	Z 0 (n + m) α ∝= n_cap n ⟷ (n_wire n ↕ Z n m α).
Proof. transpose_of Z_n_wrap_over_r_base. Qed.

Lemma Z_n_wrap_under_l_base_unswapped : forall n m α, 
	Z 0 (m + n) α ∝= n_cap_unswapped n ⟷ (Z n m α ↕ n_wire n).
Proof. transpose_of Z_n_wrap_under_r_base_unswapped. Qed.

Lemma Z_n_wrap_under_l_base : forall n m α, 
	Z 0 (m + n) α ∝= n_cap n ⟷ (Z n m α ↕ n_wire n).
Proof. transpose_of Z_n_wrap_under_r_base. Qed.

(* @nocheck name *)
(* PI is captialized in Coq R *)
Lemma Z_2_PI : forall n m a, 
	Z n m (INR a * 2 * PI) ∝= Z n m 0.
Proof.
	intros.
	prep_matrix_equivalence.
	simpl.
	unfold Z_semantics. 
	rewrite Cexp_2_PI.
	rewrite Cexp_0.
	easy.
Qed.
