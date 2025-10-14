From VyZX Require Import GateDefinitions ZXCore CoreRules Bell.

Definition bell_state_prep :=
  (((X 0 1 0) ↕ (X 0 1 0)) ⟷ (□ ↕ —) ⟷ 
  ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 0))).

Definition bell_measurement (a b : nat) :=
  (_CNOT_ ⟷ (((Z 1 0 ((INR a) * PI))) ↕ (X 1 0 ((INR b) * PI)))).

Lemma bell_measurement_eq : forall a b,
  bell_measurement a b ∝= (Z 1 1 (INR a * PI) ⟷ X 1 1 (INR b * PI)) ↕ — ⟷ ⊃.
Proof.
  intros; unfold bell_measurement.
  unfold bell_measurement.
  rewrite compose_assoc.
  rewrite <- (stack_compose_distr Wire (Z 1 0 _) (X 2 1 0)).
  rewrite X_spider_1_1_fusion.
  rewrite wire_removal_l.
  rewrite Rplus_0_l.
  assert (H : ((Z 1 0 (INR a * PI) ↕ X 2 0 (INR b * PI))) ∝=
  (((Z 1 0 (INR a * PI) ↕ — ↕ —) ⟷ (X 2 0 (INR b * PI))))).
  { rewrite stack_assoc.      
    simpl_casts.
    rewrite <- (stack_empty_l (X 2 0 _)) at 2.
    rewrite <- (stack_compose_distr (Z 1 0 _) ⦰ (— ↕ —) (X 2 0 _)).
    bundle_wires.
    cleanup_zx.
    reflexivity. }
  rewrite H.
  rewrite <- compose_assoc.
  rewrite <- stack_compose_distr.
  assert (H0 : — ∝= n_wire 1).
  {
    bundle_wires.
    reflexivity.
  }
  rewrite H0.
  rewrite (dominated_Z_spider_fusion_top_left 0 0).
  simpl.
  cleanup_zx.
  replace (INR b * PI)%R with (INR b * PI + 0)%R by lra.
  rewrite <- (dominated_X_spider_fusion_top_right 1 0 1 0).
  rewrite <- cup_X.
  rewrite 2 Rplus_0_r.
  rewrite <- compose_assoc.
  simpl_casts.
  bundle_wires.
  rewrite <- (stack_compose_distr (Z 1 1 _) (X 1 1 _) (—) (—)).
  cleanup_zx.
  reflexivity.
  Unshelve.
  all:lia. Qed.

Definition teleportation_2 
  (a b : nat) :=
  (— ↕ bell_state_prep) ⟷ ((bell_measurement a b) ↕ 
                          (X 1 1 (INR b * PI) ⟷ (Z 1 1 (INR a * PI)))).

Lemma yank_l_gen {n m} : forall (zx0 : ZX n 1) (zx1 : ZX 1 m),
  (zx0 ↕ ⊂) ⟷ (⊃ ↕ zx1) ∝= cast (n + 0) (0 + m) (Nat.add_0_r n) (eq_refl) (zx0 ⟷ zx1).
Proof.
  intros.
  rewrite <- (compose_empty_l ⊂).
  rewrite <- (wire_removal_r zx0).
  rewrite stack_compose_distr.
  rewrite <- (compose_empty_r ⊃).
  rewrite <- (wire_removal_l zx1).
  rewrite stack_compose_distr.
  repeat rewrite compose_assoc.
  rewrite <- (compose_assoc (— ↕ ⊂)).
  rewrite yank_l.
  cleanup_zx.
  rewrite cast_compose_l.
  simpl_casts.
  reflexivity. Qed.

Lemma teleportation_2_correct : forall (a b : bool), teleportation_2 a b ∝= —.
Proof.
  intros; unfold teleportation_2.
  rewrite bell_measurement_eq.
  rewrite bell_state_prep_correct.
  rewrite <- (wire_removal_l (X 1 1 _ ⟷ Z 1 1 _)).
  rewrite stack_compose_distr.
  rewrite stack_assoc.
  simpl_casts.
  rewrite <- compose_assoc.
  rewrite <- (stack_compose_distr — (Z 1 1 _ ⟷ X 1 1 _) ⊂ (— ↕ —)).
  rewrite wire_removal_l.
  bundle_wires.
  cleanup_zx.
  rewrite yank_l_gen.
  simpl_casts.
  repeat rewrite compose_assoc.
  rewrite <- (compose_assoc (X 1 1 _) (X 1 1 _) (Z 1 1 _)).
  rewrite X_spider_1_1_fusion.
  replace (INR b * PI + INR b * PI)%R with (INR b * 2 * PI)%R by lra.
  rewrite X_2_PI.
  cleanup_zx.
  rewrite Z_spider_1_1_fusion.
  simpl.
  replace (INR a * PI + INR a * PI)%R with (INR a * 2 * PI)%R by lra.
  rewrite Z_2_PI.
  cleanup_zx.
  reflexivity. 
  Unshelve.
  all: lia.
  Qed.