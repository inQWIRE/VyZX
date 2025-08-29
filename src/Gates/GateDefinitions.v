Require Import ZXCore.
Require Import CoreRules.
Require Import GateRules.
Require Setoid.
From VyZX Require Import Proportional.

Local Open Scope ZX_scope.

(** Gate Definitions in the ZX Calculus *)

Notation "'_Z_'" := (Z 1 1 PI) (at level 40).
Notation "'_X_'" := (X 1 1 PI) (at level 40).
Definition _Rz_ α : ZX 1 1 := Z 1 1 α.

Notation "'_H_'" := 
    ((Z 1 1 (PI/2)) ⟷ (X 1 1 (PI/2)) ⟷ (Z 1 1 (PI/2)))
    (at level 40).

Notation "'_CNOT_'" :=
  ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 0)).

Notation "'_CNOT_inv_'" := ((2 ↑ □) ⟷ _CNOT_ ⟷ (2 ↑ □)).

Notation "'_CNOT_R'" :=
  ((— ↕ X 1 2 0) ⟷ (Z 2 1 0 ↕ —)).

Notation "'_NOTC_'" :=
  ((— ↕ Z 1 2 0 ) ⟷ (X 2 1 0 ↕ —)).

Notation "'_NOTC_R'" :=
  ((X 1 2 0 ↕ —) ⟷ (— ↕ Z 2 1 0 )).

Notation "'_3_CNOT_SWAP_'" :=
  (_CNOT_ ⟷ _NOTC_ ⟷ _CNOT_).

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
  rewrite <- (stack_compose_distr (Z 1 1 _) (X 1 1 _) (n_wire 1) (n_wire 1)).
  cleanup_zx.
  reflexivity.
  Unshelve.
  all:lia. Qed.

Definition teleportation_2 
  (a b : nat) :=
  (— ↕ bell_state_prep) ⟷ ((bell_measurement a b) ↕ 
                          (X 1 1 (INR b * PI) ⟷ (Z 1 1 (INR a * PI)))).

Lemma teleportation_2_correct : forall a b, teleportation_2 a b ∝= —.
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
  rewrite <- (wire_removal_r (Z 1 1 _ ⟷ X 1 1 _)).
  rewrite <- compose_empty_l.
  rewrite stack_compose_distr.
  rewrite <- (wire_removal_l (X 1 1 _ ⟷ Z 1 1 _)).
  rewrite <- (compose_empty_r ⊃).
  rewrite stack_compose_distr.
  repeat rewrite compose_assoc.
  rewrite <- (compose_assoc (— ↕ ⊂)).
  rewrite yank_l.
  cleanup_zx.
  simpl_casts.
  repeat rewrite compose_assoc.
  rewrite <- (compose_assoc (X 1 1 _) (X 1 1 _) (Z 1 1 _)).
  rewrite X_spider_1_1_fusion.
  replace (INR b * PI + INR b * PI)%R with (INR b * 2 * PI)%R by lra.
  rewrite X_2_PI.
  cleanup_zx.
  rewrite Z_spider_1_1_fusion.
  replace (INR a * PI + INR a * PI)%R with (INR a * 2 * PI)%R by lra.
  rewrite Z_2_PI.
  cleanup_zx.
  reflexivity. 
  Unshelve.
  all: lia.
  Qed.
