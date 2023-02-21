Require Import CoreData.CoreData.
Require Import WireRules.
Require Import CoreAutomation.
Require Import ZRules.

Lemma Grow_X_Top_Left : forall (nIn nOut : nat) α,
	X (S (S nIn)) nOut α ∝  
	(X 2 1 0) ↕ (nWire nIn) ⟷ (X (S nIn) nOut α).
Proof. intros. colorswap_of Grow_Z_Top_Left. Qed.

Lemma Grow_X_Top_Right : forall (nIn nOut : nat) α,
	X nIn (S (S nOut)) α ∝ 
	(X nIn (S nOut) α) ⟷ ((X_Spider 1 2 0) ↕ (nWire nOut)).
Proof. intros. colorswap_of Grow_Z_Top_Right. Qed.

Lemma X_rot_l : forall n m α β,
	X (S n) m (α + β) ∝ X 1 1 α ↕ nWire n ⟷ X (S n) m β.
Proof. intros. colorswap_of Z_rot_l. Qed.

Lemma X_rot_r : forall n m α β,
	X n (S m) (α + β) ∝  X n (S m) α ⟷ X 1 1 β ↕ nWire m.
Proof. intros. colorswap_of Z_rot_r. Qed.

Lemma X_appendix_rot_l : forall n m α β,
	X n m (α + β) ∝ (X 0 1 α ↕ nWire n) ⟷ X (S n) m β.
Proof. intros. colorswap_of Z_appendix_rot_l. Qed.

Lemma Z_appendix_rot_r : forall n m α β,
	X n m (β + α) ∝ X n (S m) α ⟷ (X 1 0 β ↕ nWire m).
Proof. intros. colorswap_of Z_appendix_rot_r. Qed.

Lemma X_WrapOver_Top_Left : forall n m α,
	X (S n) m α ∝ (Wire ↕ X n (S m) α) ⟷  (Cup ↕ nWire m).
Proof. intros. colorswap_of Z_WrapOver_Top_Left. Qed.

Lemma X_WrapOver_Top_Right : forall n m α,
	X n (S m) α ∝ (Cap ↕ nWire n) ⟷ (Wire ↕ X (S n) m α).
Proof. intros. colorswap_of Z_WrapOver_Top_Right. Qed.

Lemma X_add_r : forall {n} m o {α β γ},
	X n (m + o) (α + β + γ) ∝ X n 2 β ⟷ (X 1 m α ↕ X 1 o γ).
Proof. intros. colorswap_of (@Z_add_r n). Qed.

Lemma X_add_l : forall n m {o α β γ},
	X (n + m) o (α + β + γ) ∝ (X n 1 α ↕ X m 1 γ) ⟷ X 2 o β.
Proof. intros. colorswap_of (@Z_add_l n m o). Qed.

Lemma X_1_2_1_fusion : forall α β,
	(X 1 2 α ⟷ X 2 1 β) ∝ (X 1 1 (α + β)).
Proof. intros. colorswap_of (Z_1_2_1_fusion). Qed.

Lemma X_Absolute_Fusion : forall {n m o} α β,
	(X n (S m) α ⟷ X (S m) o β) ∝
	X n o (α + β).
Proof. intros. colorswap_of (@Z_Absolute_Fusion n m o). Qed.

Lemma dominated_X_spider_fusion_top_right : forall n m0 m1 o α β,
	(X n (S m0) α ↕ nWire m1 ⟷ X (S m0 + m1) o β) ∝
	X (n + m1) o (α + β).
Proof. intros. colorswap_of dominated_Z_spider_fusion_top_right. Qed.

Lemma dominated_X_spider_fusion_top_left : forall m n0 n1 i α β,
	X i (S n0 + n1) β ⟷ (X (S n0) m α ↕ nWire n1) ∝
	X i (m + n1) (α + β).
Proof. intros. colorswap_of dominated_Z_spider_fusion_top_left. Qed.

Lemma dominated_X_spider_fusion_bot_right : forall n m0 m1 o α β,
	((nWire m1 ↕ (X n (S m0) α)) ⟷ X (m1 + (S m0)) o β) ∝
	X (m1 + n) o (α + β).
Proof. intros. colorswap_of dominated_Z_spider_fusion_bot_right. Qed.

Lemma dominated_X_spider_fusion_bot_left : forall m n0 n1 i α β,
	X i (n1 + S n0) β ⟷ (nWire n1 ↕ X (S n0) m α) ∝
	X i (n1 + m) (α + β).
Proof. intros. colorswap_of dominated_Z_spider_fusion_bot_left. Qed.

Lemma X_SpiderFusion_TopLeft_BotRight : forall top mid bot input output α β,
	X input (top + S mid) α ↕ nWire bot ⟷
	Cast (top + (S mid) + bot) (top + output) (eq_sym (Nat.add_assoc _ _ _)) eq_refl 
		(nWire top ↕ X (S mid + bot) output β) ∝
	X (input + bot) (top + output) (α + β).
Proof. intros. colorswap_of Z_SpiderFusion_TopLeft_BotRight. Qed.

Lemma Z_SpiderFusion_BotLeft_TopRight : forall top mid bot input output α β,
	((nWire top ↕ X input (S mid + bot) α) ⟷
	Cast (top + ((S mid) + bot)) _ ((Nat.add_assoc _ _ _)) eq_refl 
		(X (top + (S mid)) output β ↕ nWire bot)) ∝
	X (top + input) (output + bot) (β + α).
Proof. intros. colorswap_of Z_SpiderFusion_BotLeft_TopRight. Qed.