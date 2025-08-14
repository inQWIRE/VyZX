Require Import CoreRules Soundness.
Import Setoid.

Definition zx_scale {n m} (c : C) (zx : ZX n m) : ZX n m :=
  zx_of_const c ↕ zx.

Notation "c '.*' zx" := (zx_scale c zx) 
  (at level 40, left associativity) : ZX_scope.

Lemma zx_scale_defn {n m} c (zx : ZX n m) : c .* zx = zx_of_const c ↕ zx.
Proof. reflexivity. Qed.

Lemma zx_scale_fun_defn : @zx_scale = fun n m c zx => zx_of_const c ↕ zx.
Proof. reflexivity. Qed.

(* We really don't want zx_scale to reduce, as that'll be messy
  (especially with dimensions!) *)
#[global] Opaque zx_scale.

Add Parametric Morphism {n m} c : (@zx_scale n m c) with signature 
  proportional_by_1 ==> proportional_by_1 as zx_scale_prop_by_1_mor.
Proof.
  rewrite zx_scale_fun_defn.
  intros zx0 zx1 ->.
  reflexivity.
Qed.

Add Parametric Morphism {n m} c : (@zx_scale n m c) with signature 
  proportional ==> proportional as zx_scale_mor.
Proof.
  rewrite zx_scale_fun_defn.
  intros zx0 zx1 ->.
  reflexivity.
Qed.

Lemma zx_scale_semantics {n m} c (zx : ZX n m) : ⟦ c .* zx ⟧ = scale c ⟦ zx ⟧.
Proof.
  rewrite zx_scale_defn.
  etransitivity; [apply zx_stack_spec|].
  rewrite zx_of_const_semantics.
  rewrite Mscale_kron_dist_l, kron_1_l by auto_wf.
  reflexivity.
Qed.

Lemma zx_scale_assoc {n m} c d (zx : ZX n m) : c .* (d .* zx) ∝= (c * d) .* zx.
Proof.
  hnf.
  rewrite 3 zx_scale_semantics.
  apply Mscale_assoc.
Qed.

Lemma zx_scale_1_l {n m} (zx : ZX n m) : 1 .* zx ∝= zx.
Proof.
  hnf.
  rewrite zx_scale_semantics.
  apply Mscale_1_l.
Qed.

Lemma zx_scale_compose_distr_l {n m o} (c : C) (zx0 : ZX n m) (zx1 : ZX m o) : 
  (c .* zx0) ⟷ zx1 ∝= c .* (zx0 ⟷ zx1).
Proof.
  hnf.
  simpl; rewrite 2 zx_scale_semantics.
  apply Mscale_mult_dist_r.
Qed.

Lemma zx_scale_compose_distr_r {n m o} (c : C) (zx0 : ZX n m) (zx1 : ZX m o) : 
  zx0 ⟷ (c .* zx1) ∝= c .* (zx0 ⟷ zx1).
Proof.
  hnf.
  simpl; rewrite 2 zx_scale_semantics.
  apply Mscale_mult_dist_l.
Qed.

Lemma zx_scale_stack_distr_l {n m o p} (c : C) (zx0 : ZX n m) (zx1 : ZX o p) : 
  (c .* zx0) ↕ zx1 ∝= c .* (zx0 ↕ zx1).
Proof.
  hnf.
  simpl; rewrite 2 zx_scale_semantics.
  apply Mscale_kron_dist_l.
Qed.

Lemma zx_scale_stack_distr_r {n m o p} (c : C) (zx0 : ZX n m) (zx1 : ZX o p) : 
  zx0 ↕ (c .* zx1) ∝= c .* (zx0 ↕ zx1).
Proof.
  hnf.
  simpl; rewrite 2 zx_scale_semantics.
  apply Mscale_kron_dist_r.
Qed.

Lemma zx_scale_transpose {n m} c (zx : ZX n m) : 
  (c .* zx) ⊤ ∝= c .* zx ⊤.
Proof.
  hnf.
  rewrite semantics_transpose_comm, 2 zx_scale_semantics, 
    semantics_transpose_comm. 
  apply Mscale_trans.
Qed.

Lemma zx_scale_adjoint {n m} c (zx : ZX n m) : 
  (c .* zx) † ∝= c ^* .* zx †.
Proof.
  hnf.
  rewrite semantics_adjoint_comm, 2 zx_scale_semantics, 
    semantics_adjoint_comm. 
  apply Mscale_adj.
Qed.

Lemma zx_scale_conjugate {n m} c (zx : ZX n m) : 
  (c .* zx) ⊼ ∝= c ^* .* zx ⊼.
Proof.
  rewrite 2 conjugate_decomp.
  rewrite zx_scale_adjoint, zx_scale_transpose.
  reflexivity.
Qed.

Lemma zx_scale_colorswap {n m} c (zx : ZX n m) : 
  ⊙ (c .* zx) ∝= c .* ⊙ zx.
Proof.
  hnf.
  rewrite semantics_colorswap_comm, 2 zx_scale_semantics, 
    semantics_colorswap_comm.
  now rewrite Mscale_mult_dist_r, Mscale_mult_dist_l.
Qed.

Lemma zx_scale_n_stack {n m} k c (zx : ZX n m) : 
  k ⇑ (c .* zx) ∝= c ^ k .* k ⇑ zx.
Proof.
  induction k.
  - simpl.
    now rewrite zx_scale_1_l.
  - simpl.
    rewrite IHk.
    rewrite zx_scale_stack_distr_l, zx_scale_stack_distr_r, zx_scale_assoc.
    reflexivity.
Qed.

Lemma zx_scale_n_stack1 k c (zx : ZX 1 1) : 
  k ↑ (c .* zx) ∝= c ^ k .* k ↑ zx.
Proof.
  induction k.
  - simpl.
    now rewrite zx_scale_1_l.
  - simpl.
    rewrite IHk.
    rewrite zx_scale_stack_distr_l, zx_scale_stack_distr_r, zx_scale_assoc.
    reflexivity.
Qed.

Lemma zx_scale_cast {n m n' m'} c (zx : ZX n' m') H H' : 
  cast n m H H' (c .* zx) = c .* cast n m H H' zx.
Proof.
  now subst.
Qed.

(* NB: This is entirely unnecessary, as rewrite databases are completely
  separate from standard hint databases, but it's probably good practice
  (and hopefully someday that'll change). *)
Create HintDb zxscale_db discriminated.
#[export] Hint Rewrite 
  @zx_scale_1_l
  @zx_scale_assoc
  @zx_scale_compose_distr_l   @zx_scale_compose_distr_r
  @zx_scale_stack_distr_l     @zx_scale_stack_distr_r
  @zx_scale_transpose   @zx_scale_adjoint   @zx_scale_conjugate
  @zx_scale_colorswap
  @zx_scale_n_stack     @zx_scale_n_stack1
  @zx_scale_cast : zxscale_db.

#[export] Hint Rewrite @zx_scale_colorswap : colorswap_db.
#[export] Hint Rewrite @zx_scale_transpose : transpose_db.
#[export] Hint Rewrite @zx_scale_adjoint : adjoint_db.

Ltac distribute_zxscale := rewrite_strat (bottomup (hints zxscale_db)).
Tactic Notation "distribute_zxscale" "in" hyp(H) :=
  rewrite_strat (bottomup (hints zxscale_db)) in H.

Lemma zx_scale_simplify_eq {n m} (c c' : C) (zx zx' : ZX n m) : 
  c = c' -> zx ∝= zx' -> c .* zx ∝= c' .* zx'.
Proof.
  intros -> ->.
  reflexivity.
Qed.

Lemma zx_scale_simplify_eq_l {n m} (c c' : C) (zx : ZX n m) : 
  c = c' -> c .* zx ∝= c' .* zx.
Proof.
  intros ->.
  reflexivity.
Qed.

Lemma zx_scale_simplify_eq_r {n m} (c : C) (zx zx' : ZX n m) : 
  zx ∝= zx' -> c .* zx ∝= c .* zx'.
Proof.
  intros ->.
  reflexivity.
Qed.

Lemma prop_by_iff_zx_scale {n m} c (zx zx' : ZX n m) : 
  zx ∝[c] zx' <-> zx ∝= c .* zx' /\ c <> 0.
Proof.
  unfold proportional_by.
  unfold proportional_by_1.
  now rewrite zx_scale_semantics.
Qed.

Lemma prop_iff_zx_scale {n m} (zx zx' : ZX n m) : 
  zx ∝ zx' <-> exists c, zx ∝= c .* zx' /\ c <> 0.
Proof.
  unfold proportional.
  now setoid_rewrite prop_by_iff_zx_scale.
Qed.

Lemma zx_scale_eq_l {n m} c (zx zx' : ZX n m) : c <> C0 ->
  c .* zx ∝= zx' <-> zx ∝= /c .* zx'.
Proof.
  intros Hc.
  split; [intros <- | intros ->]; distribute_zxscale; 
  rewrite 1?Cinv_l, 1?Cinv_r by auto;
  now rewrite zx_scale_1_l.
Qed.

Lemma zx_scale_eq_r {n m} c (zx zx' : ZX n m) : c <> C0 ->
  zx ∝= c .* zx' <-> / c .* zx ∝= zx'.
Proof.
  intros Hc.
  split; [intros -> | intros <-]; distribute_zxscale; 
  rewrite 1?Cinv_l, 1?Cinv_r by auto;
  now rewrite zx_scale_1_l.
Qed.

Lemma zx_scale_prop_by_l {n m} c d (zx zx' : ZX n m) : c <> C0 -> 
  c .* zx ∝[d] zx' <-> zx ∝[d/c] zx'.
Proof.
  intros Hc.
  rewrite 2 prop_by_iff_zx_scale.
  rewrite zx_scale_eq_l by auto.
  distribute_zxscale.
  rewrite Cmult_comm.
  apply Modulus.and_iff_distr_l.
  intros _. 
  unfold Cdiv.
  rewrite Cmult_integral_iff, Cinv_eq_0_iff.
  intuition idtac.
Qed.

Lemma zx_scale_prop_by_r {n m} c d (zx zx' : ZX n m) : c <> C0 -> 
  zx ∝[d] c .* zx' <-> zx ∝[d * c] zx'.
Proof.
  intros Hc.
  rewrite 2 prop_by_iff_zx_scale.
  distribute_zxscale.
  apply Modulus.and_iff_distr_l.
  intros _.
  rewrite Cmult_integral_iff.
  intuition fail.
Qed.

Lemma zx_scale_prop_l {n m} c (zx zx' : ZX n m) : c <> C0 ->
  c .* zx ∝ zx' <-> zx ∝ zx'.
Proof.
  intros Hc.
  rewrite 2 prop_iff_zx_scale.
  split.
  - intros (d & Heq & Hd).
    rewrite zx_scale_eq_l in Heq by auto.
    exists (/c * d).
    split.
    + distribute_zxscale in Heq.
      apply Heq.
    + rewrite Cmult_integral_iff, Cinv_eq_0_iff.
      intuition fail.
  - intros (d & Heq & Hd).
    exists (d * c).
    rewrite zx_scale_eq_l by auto.
    split.
    + distribute_zxscale.
      rewrite Heq.
      apply zx_scale_simplify_eq_l.
      C_field.
    + rewrite Cmult_integral_iff.
      intuition fail.
Qed.

Lemma zx_scale_prop_r {n m} c (zx zx' : ZX n m) : c <> C0 ->
  zx ∝ c .* zx' <-> zx ∝ zx'.
Proof.
  intros Hc.
  split.
  - intros ->.
    now apply zx_scale_prop_l.
  - intros ->.
    symmetry.
    now apply zx_scale_prop_l.
Qed.




(* FIXME: Move... somewhere *)
Lemma box_decomposition_Z_X_Z : □ ∝= 
  (C1 - Ci) / √ 2 .*
  (Z 1 1 (PI/2) ⟷ X 1 1 (PI/2) ⟷ Z 1 1 (PI/2)).
Proof.
  prep_matrix_equivalence.
  rewrite zx_scale_semantics.
  rewrite 2 zx_compose_spec.
  compute_matrix (⟦ Z 1 1 (PI / 2) ⟧).
  compute_matrix (⟦ X 1 1 (PI / 2) ⟧).
  rewrite kron_1_l by auto_wf.
  unfold hadamard.
  unfold Cdiv; Csimpl.
  rewrite 2 make_WF_equiv.
  rewrite Cexp_PI2 (* , Cexp_PI4 *).
  group_radicals.
  by_cell; autounfold with U_db; unfold list2D_to_matrix; cbn;
  lca.
Qed.

Lemma box_decomposition_X_Z_X : □ ∝= 
  (C1 - Ci) / √ 2 .*
  (X 1 1 (PI/2) ⟷ Z 1 1 (PI/2) ⟷ X 1 1 (PI/2)).
Proof.
  colorswap_of box_decomposition_Z_X_Z.
Qed.


Lemma prop_by_to_zx_scale {n m} (zx0 zx1 : ZX n m) c : 
  zx0 ∝[c] zx1 -> zx0 ∝= c .* zx1.
Proof.
  rewrite prop_by_iff_zx_scale.
  easy.
Qed.

(* Automation for gadgets *)

(* Automatically convert an explicit proportionality lemma
  (i.e. ending in [_ ∝[_] _]) to the corresponding semantic
  equality statement. *)
Ltac zxlem_to_scale h :=
  lazymatch type of h with 
  | ?zx0 ∝[?c] ?zx1 => open_constr:(prop_by_to_zx_scale zx0 zx1 c h)
  | forall x : ?T, _ => 
    let x := fresh x in 
    constr:(fun x : T => 
      ltac:(
        let happ := eval cbn beta in (h x) in 
        let res := zxlem_to_scale happ
        in exact res))
  | ?T => fail 0 "Couldn't see lemma of type '" T
    "' as a lemma of shape '_ ∝[_] _'"
  end.

(* Use an explicit proportionality [∝[c]] lemma in a semantic 
  equality [∝=] context by converting to a gadget statement. 
  For example, [rewrite (to_scale bi_algebra_rule_Z_X)]. Note
  that the lemma cannot have any implicit arguments, which is 
  usually most easily rectified by writing [to_scale @lem] 
  instead of [to_scale lem]. (Specifically, [lem] can be any
  term without holes, potentially with evars, so it can be 
  partially applied to arguments)*)
Notation "'to_scale' h" := 
  (ltac:(
    let res := zxlem_to_scale open_constr:(h) in 
    exact res))
  (at level 0, h at level 100, only parsing) : ZX_scope.

