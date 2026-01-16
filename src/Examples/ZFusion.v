Require Import ZRules.
Require Import CoreData.CoreData.
Require Import CoreAutomation.
Require Import CapCupRules.
Require Import CastRules.
Require Import StackComposeRules.
Require Import SwapRules.
Require Import WireRules.
Require Import SpiderInduction.
Require Import ZXpermFacts.
Require Import ChoiJamiolchosky.


Lemma Z_absolute_fusion_ex : forall {n m o} α β,
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