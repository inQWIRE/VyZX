Require Import CoreData.
Require Import CoreRules.

Definition bell_state_prep :=
  (((X 0 1 0) ↕ (X 0 1 0)) ⟷ (□ ↕ —) ⟷ 
  ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 0))).

Lemma bell_state_prep_correct : bell_state_prep ∝= ⊂.
Proof.
  unfold bell_state_prep.
  rewrite <- stack_compose_distr.
  assert (X 0 1 0 ⟷ □ ∝= Z 0 1 0) as H.
  {
    replace (X 0 1 0) with (⊙ (Z 0 1 0)) at 1 by easy.
    rewrite colorswap_is_bihadamard; simpl; cleanup_zx; simpl_casts.
    rewrite compose_assoc; cleanup_zx; easy.
  }
  rewrite H; cleanup_zx.
  rewrite <- compose_assoc.
  rewrite <- (stack_compose_distr (Z 0 1 0) (Z 1 2 0) (X 0 1 0) —); cleanup_zx.
  rewrite Z_spider_1_1_fusion.
  rewrite <- nwire_stack_compose_botleft.
  rewrite compose_assoc.
  rewrite <- (n_wire_stack 1 1); rewrite wire_to_n_wire.
  rewrite (stack_assoc (n_wire 1) (n_wire 1)); simpl_casts.
  rewrite <- (stack_compose_distr (n_wire 1) (n_wire 1) (n_wire 1 ↕ X 0 1 0)).
  rewrite (dominated_X_spider_fusion_bot_right 0 0 1).
  cleanup_zx; simpl_casts.
  rewrite Rplus_0_r; rewrite X_0_is_wire.
  bundle_wires; cleanup_zx.
  rewrite <- cap_Z.
  easy.
Unshelve.
all: reflexivity.
Qed.

Definition teleportation (a b : nat) :=
  (⊂ ↕ Z 1 2 0) ⟷ ((X 1 1 (INR b * PI) ⟷ Z 1 1 (INR a * PI)) ↕ (((X 2 1 0) ↕ (Z 1 0 (INR a * PI)) ⟷ (□ ⟷ Z 1 0 (INR b * PI))))).

Lemma teleportation_correct : forall a b, teleportation a b ∝= —.
Proof.
  intros; unfold teleportation.
  assert (□ ⟷ Z 1 0 (INR b * PI) ∝= (X 1 0 (INR b * PI))).
  {
    replace (X 1 0 (INR b * PI)) with (⊙ (Z 1 0 (INR b * PI))) by easy.
    rewrite colorswap_is_bihadamard.
    simpl; cleanup_zx; simpl_casts.
    easy.
  }
  rewrite H.
  rewrite (stack_empty_r_back (X 1 0 _)).
  simpl_casts.
  rewrite <- (stack_compose_distr (X 2 1 0) (X 1 0 _) (Z 1 0 _) ⦰).
  rewrite X_spider_1_1_fusion.
  cleanup_zx.
  rewrite (stack_assoc_back (X 1 1 _ ⟷ Z 1 1 _) (X 2 0 _) (Z 1 0 _)).
  simpl_casts.
  rewrite <- (nwire_removal_l (X 2 0 _)).
  cbn; rewrite stack_empty_r; simpl_casts.
  rewrite stack_compose_distr.
  rewrite (stack_assoc_back (X 1 1 _) — —).
  simpl_casts.
  rewrite <- (compose_empty_r (Z 1 0 _)).
  rewrite stack_compose_distr.
  rewrite <- compose_assoc.
  rewrite (stack_assoc (X 1 1 _ ↕ —) — (Z 1 0 _)).
  simpl_casts.
  rewrite <- (stack_compose_distr ⊂ (X 1 1 _ ↕ —) (Z 1 2 0) (— ↕ Z 1 0 _)).
  rewrite cap_X.
  rewrite wire_to_n_wire at 1 2.
  rewrite (dominated_X_spider_fusion_top_left 1 0).
  rewrite (dominated_Z_spider_fusion_bot_left 0 0 1).
  rewrite <- (nwire_removal_l (Z 1 1 _)).
  rewrite <- (nwire_removal_r (X 2 0 _)).
  rewrite stack_compose_distr.
  replace (0 + INR b * PI)%R with ((INR b * PI) + 0 +0)%R by lra.
  rewrite (X_add_l 1 1).
  rewrite stack_nwire_distribute_l.
  rewrite (stack_assoc_back (n_wire 1) (X 1 1 _)).
  rewrite stack_empty_r.
  simpl_casts.
  rewrite compose_assoc.
  rewrite <- (compose_assoc (X 0 (1 + 1) _ ↕ Z 1 (1 + 0) _)).
  rewrite <- (stack_compose_distr (X 0 (1 + 1) _) (n_wire 1 ↕ X 1 1 _) (Z 1 (1 + 0) _) (X 1 1 _)).
  rewrite (dominated_X_spider_fusion_bot_left 1 0).
  replace ((INR b * PI + (INR b * PI + 0)))%R with (INR b * 2 * PI)%R by lra.
  rewrite X_2_PI.
  rewrite X_0_is_wire.
  rewrite <- (nwire_removal_l (X 0 _ _)).
  rewrite <- cap_X, <- cup_X.
  rewrite stack_compose_distr.
  rewrite <- wire_to_n_wire.
  repeat rewrite <- compose_assoc.
  rewrite (compose_assoc (n_wire 0 ↕ Z 1 (1 + 0) (INR a * PI + 0))).
  rewrite yank_r.
  cleanup_zx; simpl_casts.
  rewrite Z_spider_1_1_fusion.
  replace (INR a * PI + 0 + INR a * PI)%R with ((INR a * 2 * PI))%R by lra.
  rewrite Z_2_PI.
  rewrite Z_0_is_wire.
  easy.
Unshelve.
all: lia.
Qed.