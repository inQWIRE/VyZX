Require Import CoreData.CoreData.
Require Import WireRules.
Require Import CoreAutomation.
Require Import ZRules.

Lemma grow_X_top_left : forall (nIn nOut : nat) α,
	X (S (S nIn)) nOut α ∝  
	(X 2 1 0) ↕ (n_wire nIn) ⟷ (X (S nIn) nOut α).
Proof. intros. colorswap_of grow_Z_top_left. Qed.

Lemma grow_X_top_right : forall (nIn nOut : nat) α,
	X nIn (S (S nOut)) α ∝ 
	(X nIn (S nOut) α) ⟷ ((X_Spider 1 2 0) ↕ (n_wire nOut)).
Proof. intros. colorswap_of grow_Z_top_right. Qed.

Lemma X_rot_l : forall n m α β,
	X (S n) m (α + β) ∝ X 1 1 α ↕ n_wire n ⟷ X (S n) m β.
Proof. intros. colorswap_of Z_rot_l. Qed.

Lemma X_rot_r : forall n m α β,
	X n (S m) (α + β) ∝ X n (S m) α ⟷ (X 1 1 β ↕ n_wire m).
Proof. intros. colorswap_of Z_rot_r. Qed.

Lemma X_add_r_base_rot : forall {n} m o {α}, X n (m + o) α ∝ X n 2 α ⟷ (X 1 m 0 ↕ X 1 o 0).
Proof. intros. colorswap_of (@Z_add_r_base_rot n). Qed.

Lemma X_add_l_base_rot : forall {n} m o {α}, X (n + m) o α ∝ (X n 1 0 ↕ X m 1 0) ⟷ X 2 o α.
Proof. intros. colorswap_of (@Z_add_l_base_rot n). Qed.

Lemma X_appendix_rot_l : forall n m α β,
	X n m (α + β) ∝ (X 0 1 α ↕ n_wire n) ⟷ X (S n) m β.
Proof. intros. colorswap_of Z_appendix_rot_l. Qed.

Lemma X_appendix_rot_r : forall n m α β,
	X n m (β + α) ∝ X n (S m) α ⟷ (X 1 0 β ↕ n_wire m).
Proof. intros. colorswap_of Z_appendix_rot_r. Qed.

Lemma X_wrap_over_top_left : forall n m α,
	X (S n) m α ∝ (Wire ↕ X n (S m) α) ⟷  (Cup ↕ n_wire m).
Proof. intros. colorswap_of Z_wrap_over_top_left. Qed.

Lemma X_wrap_over_top_right : forall n m α,
	X n (S m) α ∝ (Cap ↕ n_wire n) ⟷ (Wire ↕ X (S n) m α).
Proof. intros. colorswap_of Z_wrap_over_top_right. Qed.

Lemma X_add_r : forall {n} m o {α β γ},
	X n (m + o) (α + β + γ) ∝ X n 2 β ⟷ (X 1 m α ↕ X 1 o γ).
Proof. intros. colorswap_of (@Z_add_r n). Qed.

Lemma X_add_l : forall n m {o α β γ},
	X (n + m) o (α + β + γ) ∝ (X n 1 α ↕ X m 1 γ) ⟷ X 2 o β.
Proof. intros. colorswap_of (@Z_add_l n m o). Qed.

Lemma X_1_2_1_fusion : forall α β,
	(X 1 2 α ⟷ X 2 1 β) ∝ (X 1 1 (α + β)).
Proof. intros. colorswap_of (Z_1_2_1_fusion). Qed.

Lemma X_absolute_fusion : forall {n m o} α β,
	(X n (S m) α ⟷ X (S m) o β) ∝
	X n o (α + β).
Proof. intros. colorswap_of (@Z_absolute_fusion n m o). Qed.

Lemma dominated_X_spider_fusion_top_right : forall n m0 m1 o α β,
	(X n (S m0) α ↕ n_wire m1 ⟷ X (S m0 + m1) o β) ∝
	X (n + m1) o (α + β).
Proof. intros. colorswap_of dominated_Z_spider_fusion_top_right. Qed.

Lemma dominated_X_spider_fusion_top_left : forall m n0 n1 i α β,
	X i (S n0 + n1) β ⟷ (X (S n0) m α ↕ n_wire n1) ∝
	X i (m + n1) (α + β).
Proof. intros. colorswap_of dominated_Z_spider_fusion_top_left. Qed.

Lemma dominated_X_spider_fusion_bot_right : forall n m0 m1 o α β,
	((n_wire m1 ↕ (X n (S m0) α)) ⟷ X (m1 + (S m0)) o β) ∝
	X (m1 + n) o (α + β).
Proof. intros. colorswap_of dominated_Z_spider_fusion_bot_right. Qed.

Lemma dominated_X_spider_fusion_bot_left : forall m n0 n1 i α β,
	X i (n1 + S n0) β ⟷ (n_wire n1 ↕ X (S n0) m α) ∝
	X i (n1 + m) (α + β).
Proof. intros. colorswap_of dominated_Z_spider_fusion_bot_left. Qed.

Lemma X_spider_fusion_top_left_bot_right : forall top mid bot input output α β,
	X input (top + S mid) α ↕ n_wire bot ⟷
	cast (top + (S mid) + bot) (top + output) (eq_sym (Nat.add_assoc _ _ _)) eq_refl 
		(n_wire top ↕ X (S mid + bot) output β) ∝
	X (input + bot) (top + output) (α + β).
Proof. intros. colorswap_of Z_spider_fusion_top_left_bot_right. Qed.

Lemma X_spider_fusion_bot_left_top_right : forall top mid bot input output α β,
	((n_wire top ↕ X input (S mid + bot) α) ⟷
	cast (top + ((S mid) + bot)) _ ((Nat.add_assoc _ _ _)) eq_refl 
		(X (top + (S mid)) output β ↕ n_wire bot)) ∝
	X (top + input) (output + bot) (β + α).
Proof. intros. colorswap_of Z_spider_fusion_bot_left_top_right. Qed.

Lemma X_self_cap_absorbtion_base : forall {n} α, X n 2%nat α ⟷ ⊃ ∝ X n 0%nat α.
Proof. intros. colorswap_of (@Z_self_cap_absorbtion_base n). Qed.

Lemma X_self_cap_absorbtion_top : forall {n m α}, (X) n (S (S m)) α ⟷ (⊃ ↕ n_wire m) ∝ X n m α.
Proof. intros. colorswap_of (@Z_self_cap_absorbtion_top n m). Qed.

Lemma X_self_cup_absorbtion_top : forall {n m α}, ((⊂ ↕ n_wire n) ⟷ X (S (S n)) m α) ∝ (X n m α).
Proof. intros. colorswap_of (@Z_self_cup_absorbtion_top n m). Qed.

Lemma X_self_cap_absorbtion : forall {n m m' α}, X n (m + (S (S m'))) α ⟷ (n_wire m ↕ (⊃ ↕ n_wire m')) ∝ (X n (m + m') α).
Proof. intros. colorswap_of (@Z_self_cap_absorbtion n m m'). Qed.

Lemma X_self_cup_absorbtion : forall {n n' m α}, ((n_wire n ↕ (⊂ ↕ n_wire n')) ⟷ X (n + (S (S n'))) m α) ∝ (X (n + n') m α).
Proof. intros. colorswap_of (@Z_self_cup_absorbtion n n' m). Qed.

Lemma X_self_loop_removal_top : forall {n m α}, X n m α ∝ (⊂ ↕ n_wire n) ⟷ (— ↕ X (S n) (S m) α) ⟷ (⊃ ↕ n_wire m).
Proof. intros. colorswap_of (@Z_self_loop_removal_top n m). Qed.

Lemma X_self_swap_absorbtion_right_base : forall {n α}, X n 2 α ⟷ ⨉ ∝ X n 2 α.
Proof. intros. colorswap_of (@Z_self_swap_absorbtion_right_base n α). Qed.

Lemma X_self_swap_absorbtion_right_top : forall {n m α}, X n (S (S m)) α ⟷ (⨉ ↕ n_wire m) ∝ X n (S (S m)) α.
Proof. intros. colorswap_of (@Z_self_swap_absorbtion_right_top n m α). Qed.

Lemma X_self_swap_absorbtion_right : forall {n m m' α}, X n (m' + S (S m)) α ⟷ (n_wire m' ↕ (⨉ ↕ n_wire m)) ∝ X n (m' + S (S m)) α.
Proof. intros. colorswap_of (@Z_self_swap_absorbtion_right n m m' α). Qed.

Lemma X_self_swap_absorbtion_left_base : forall {m α}, (⨉ ⟷ X 2 m α) ∝ X 2 m α.
Proof. intros. colorswap_of (@Z_self_swap_absorbtion_left_base m α). Qed.

Lemma X_self_swap_absorbtion_left_top : forall {n m α}, ((⨉ ↕ n_wire n) ⟷ X (S (S n)) m α) ∝ X (S (S n)) m α.
Proof. intros. colorswap_of (@Z_self_swap_absorbtion_left_top n m α). Qed.

Lemma X_self_swap_absorbtion_left : forall {n n' m α}, ((n_wire n' ↕ (⨉ ↕ n_wire n)) ⟷ X (n' + S (S n)) m α) ∝ X (n' + S (S n)) m α.
Proof. intros. colorswap_of (@Z_self_swap_absorbtion_left n n' m α). Qed.

Lemma X_wrap_under_bot_left : forall n m α,
	X n (m + 1) α ∝ 
	(cast n (n + 1 + 1) 
		(eq_sym (Nat.add_0_r _)) (wrap_under_dimension _)
		(n_wire n ↕ ⊂)) ⟷
			(X (n + 1) m α ↕ Wire).
Proof. colorswap_of Z_wrap_under_bot_left. Qed.

Lemma X_wrap_under_bot_right : forall n m α,
	X (n + 1) m α ∝ 
		(X n (m + 1) α ↕ —) ⟷ 
	(cast (m + 1 + 1) m
		(wrap_under_dimension _)
		(eq_sym (Nat.add_0_r _))
		(n_wire m ↕ ⊃)).
Proof. colorswap_of Z_wrap_under_bot_right. Qed.