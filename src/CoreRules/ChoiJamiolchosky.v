Require Export CoreData CoreAutomation 
  CastRules StackComposeRules CapCupRules.

(** Results about the Choi-Jamiolshosky isomorphism, i.e. 
  process/state duality. *)

Lemma proc_to_state_to_proc {n m} (zx : ZX n m) : 
  state_to_proc (proc_to_state zx) ∝= zx.
Proof.
  unfold state_to_proc, proc_to_state.
  rewrite n_cap_pullthrough_bot.
  rewrite stack_nwire_distribute_l.
  rewrite cast_compose_distribute, compose_assoc.
  rewrite stack_assoc_back, cast_contract.

  rewrite (cast_compose_l _ _ _ (_ ↕ _)), cast_id. 
  rewrite <- stack_nwire_distribute_r.
  rewrite n_cup_pullthrough_bot, transpose_involutive_eq.
  rewrite stack_nwire_distribute_r.
  rewrite cast_compose_distribute, stack_assoc, cast_contract.
  rewrite <- compose_assoc.
  rewrite cast_compose_eq_mid_join.
  rewrite <- stack_compose_distr, nwire_removal_l.
  rewrite push_out_bot, cast_compose_distribute, cast_contract.
  rewrite compose_assoc, (cast_compose_l _ _ (_ ↕ _)), cast_contract.
  rewrite n_wire_stack, nwire_removal_r.
  rewrite big_yank_r.
  rewrite cast_compose_l.
  rewrite 2 cast_contract.
  rewrite 2 cast_id, nwire_removal_r.
  reflexivity.
  Unshelve. all: lia.
Qed.


Lemma state_to_proc_to_state {n m} (zx : ZX 0 (n + m)) : 
  proc_to_state (state_to_proc zx) ∝= zx.
Proof.
  unfold state_to_proc, proc_to_state.
  rewrite stack_nwire_distribute_l.
  rewrite cast_stack_r, stack_assoc_back, cast_contract.
  rewrite <- compose_assoc, n_wire_stack.
  rewrite cast_compose_r, push_out_bot, <- compose_assoc, 
    cast_compose_eq_mid_join, nwire_removal_r.
  rewrite <- (push_out_bot zx (n_cap n)).
  rewrite <- nwire_stack_compose_topleft, cast_compose_distribute, 
  compose_assoc.
  rewrite <- n_wire_stack, stack_assoc_back, cast_contract.
  rewrite cast_id.
  rewrite (cast_compose_l _ _ (_ ↕ n_wire m)), cast_id.
  rewrite (stack_assoc_back (n_wire n) (n_cup n) (n_wire m)), cast_contract.
  rewrite cast_stack_distribute, cast_id.
  rewrite <- stack_nwire_distribute_r, big_yank_l.
  rewrite stack_empty_l, n_wire_stack, nwire_removal_r.
  reflexivity.
  Unshelve. all: lia.
Qed.

Lemma colorswap_proc_to_state {n m} (zx : ZX n m) : 
  ⊙ (proc_to_state zx) ∝= proc_to_state (⊙ zx).
Proof.
  unfold proc_to_state; cbn [color_swap]; 
  autorewrite with colorswap_db.
  reflexivity.
Qed.

Lemma colorswap_state_to_proc {n m} (zx : ZX 0 (n + m)) : 
  ⊙ (state_to_proc zx) ∝= state_to_proc (⊙ zx).
Proof.
  unfold state_to_proc; cbn [color_swap]; 
  autorewrite with colorswap_db.
  cbn [color_swap].
  autorewrite with colorswap_db.
  reflexivity.
Qed.

#[export] Hint Rewrite 
  @colorswap_proc_to_state @colorswap_state_to_proc : colorswap_db.





Lemma proc_to_state_state {n} (zx : ZX 0 n) : 
  proc_to_state zx ∝= zx.
Proof.
  unfold proc_to_state.
  rewrite n_cap_0_empty.
  cleanup_zx.
  reflexivity.
Qed.


Lemma state_to_proc_diagrams {n m} (zx zx' : ZX 0 (n + m)) : 
  state_to_proc zx ∝= state_to_proc zx' ->
  zx ∝= zx'.
Proof.
  intros H%proc_to_state_mor.
  now rewrite 2 state_to_proc_to_state in H.
Qed.

Lemma proc_to_state_diagrams {n m} (zx zx' : ZX n m) : 
  proc_to_state zx ∝= proc_to_state zx' ->
  zx ∝= zx'.
Proof.
  intros H%state_to_proc_mor.
  now rewrite 2 proc_to_state_to_proc in H.
Qed.

Lemma state_to_proc_diagrams_iff {n m} (zx zx' : ZX 0 (n + m)) : 
  state_to_proc zx ∝= state_to_proc zx' <->
  zx ∝= zx'.
Proof.
  split; [apply state_to_proc_diagrams | now intros ->].
Qed.

Lemma proc_to_state_diagrams_iff {n m} (zx zx' : ZX n m) : 
  proc_to_state zx ∝= proc_to_state zx' <->
  zx ∝= zx'.
Proof.
  split; [apply proc_to_state_diagrams | now intros ->].
Qed.

Lemma state_to_proc_eq_l {n m} (zx : ZX 0 (n + m)) zx' : 
  state_to_proc zx ∝= zx' <-> zx ∝= proc_to_state zx'.
Proof.
  rewrite <- (proc_to_state_to_proc zx') at 1.
  apply state_to_proc_diagrams_iff.
Qed.

Lemma state_to_proc_eq_r {n m} zx (zx' : ZX 0 (n + m)) : 
  zx ∝= state_to_proc zx' <-> proc_to_state zx ∝= zx'.
Proof.
  rewrite <- (proc_to_state_to_proc zx) at 1.
  apply state_to_proc_diagrams_iff.
Qed.

Lemma proc_to_state_eq_l {n m} zx (zx' : ZX 0 (n + m)) : 
  proc_to_state zx ∝= zx' <-> zx ∝= state_to_proc zx'.
Proof.
  rewrite <- (state_to_proc_to_state zx') at 1.
  apply proc_to_state_diagrams_iff.
Qed.

Lemma proc_to_state_eq_r {n m} (zx : ZX 0 (n + m)) zx' : 
  zx ∝= proc_to_state zx' <-> state_to_proc zx ∝= zx'.
Proof.
  rewrite <- (state_to_proc_to_state zx) at 1.
  apply proc_to_state_diagrams_iff.
Qed.

Lemma proc_to_state_n_wire n : proc_to_state (n_wire n) ∝= n_cap n.
Proof.
  unfold proc_to_state.
  rewrite n_wire_stack, nwire_removal_r.
  reflexivity.
Qed.

Lemma state_to_proc_n_cap n : state_to_proc (n_cap n) ∝= n_wire n.
Proof.
  rewrite state_to_proc_eq_l, proc_to_state_n_wire.
  reflexivity.
Qed.

Lemma proc_to_state_alt {n m} (zx : ZX n m) : 
  proc_to_state zx ∝= n_cap m ⟷ ((zx ⊤) ↕ n_wire m).
Proof.
  unfold proc_to_state.
  apply n_cap_pullthrough_bot.
Qed.

Lemma proc_to_state_effect {n} (zx : ZX n 0) : 
  proc_to_state zx ∝= zx⊤ ↕ ⦰.
Proof.
  unfold proc_to_state.
  rewrite n_cap_pullthrough_bot, n_cap_0_empty, compose_empty_l.
  reflexivity.
Qed.

Lemma state_to_proc_n_cup n : proc_to_state (n_cup n) ∝= n_cap n ↕ ⦰.
Proof.
  apply proc_to_state_effect.
Qed.



Lemma wrap_over_left {n m} (zx zx' : ZX n m) : 
	n_cap n ⟷ (n_wire n ↕ zx) ∝= n_cap n ⟷ (n_wire n ↕ zx') ->
	zx ∝= zx'.
Proof.
	intros Heq.
	apply proc_to_state_diagrams.
	apply Heq.
Qed.

Lemma wrap_over_right {n m} (zx zx' : ZX n m) : 
	n_wire m ↕ zx ⟷ n_cup m ∝= n_wire m ↕ zx' ⟷ n_cup m ->
	zx ∝= zx'.
Proof.
	intros Heq.
	apply transpose_prop_by_1_proper in Heq.
	cbn -[n_cup] in Heq.
	autorewrite with transpose_db in Heq.
	apply transpose_diagrams_eq.
	now apply wrap_over_left.
Qed.

Lemma wrap_under_left {n m} (zx zx' : ZX n m) : 
	n_cap n ⟷ (zx ↕ n_wire n) ∝= n_cap n ⟷ (zx' ↕ n_wire n) ->
	zx ∝= zx'.
Proof.
	intros Heq.
  apply transpose_diagrams_eq.
	apply proc_to_state_diagrams.
  rewrite 2 proc_to_state_alt.
  now rewrite 2 transpose_involutive_eq.
Qed.

Lemma wrap_under_right {n m} (zx zx' : ZX n m) : 
	(zx ↕ n_wire m) ⟷ n_cup m ∝= (zx' ↕ n_wire m) ⟷ n_cup m ->
	zx ∝= zx'.
Proof.
	intros Heq.
	apply transpose_prop_by_1_proper in Heq.
	cbn -[n_cup] in Heq.
	autorewrite with transpose_db in Heq.
	apply transpose_diagrams_eq.
	now apply wrap_under_left.
Qed.