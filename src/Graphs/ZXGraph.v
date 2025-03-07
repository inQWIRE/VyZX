Require Export ZXCore.
Require Export ZXpermFacts.
Require Import BipermAux.
Require Import BigPerm.
Import Kronecker.
Import Setoid.
Require Export CoreRules.
Require Import Bipermutations BipermutationMatrices NFBiperm ZXbiperm.
Require Import ZXpermcomp.
Require Import ZXGraphTheory.


Lemma n_cap_mid_prf2 {n m o p} : n + m + (o + p) = n + (m + o) + p.
Proof. lia. Qed.

Definition n_cap_mid n m o : ZX (n + o) ((n + m) + (m + o)) :=
  cast _ _ (Nat.add_assoc n 0 o) n_cap_mid_prf2 
  (n_wire n ↕ n_cap m ↕ n_wire o).

Definition ZXvert n m := ZX (n + m) 0.

Definition ZXvert_prop n m (zx0 zx1 : ZXvert n m) :=
  @proportional (n + m) 0 zx0 zx1.

Definition wrap_n_cap_under {n o} m (zx : ZX (n + m) o) : ZX n (o + m) :=
  cast _ _ (eq_sym (Nat.add_0_r n)) (eq_sym (Nat.add_assoc _ _ _))
    (n_wire n ↕ n_cap m) ⟷ (zx ↕ n_wire m).

Definition ZX_of_ZXvert {n m} (zxv : ZXvert n m) : ZX n m :=
  wrap_n_cap_under m zxv.

Definition stack_ZX_vert {n0 m0 n1 m1} (zx0 : ZXvert n0 m0)
  (zx1 : ZXvert n1 m1) : ZXvert (n0 + n1) (m0 + m1) :=
  zx_mid_comm n0 n1 m0 m1 ⟷ (zx0 ↕ zx1).

Definition compose_ZX_vert {n m o} (zx0 : ZXvert n m) (zx1 : ZXvert m o) :
  ZXvert n o :=
  n_cap_mid n m o ⟷ (zx0 ↕ zx1).

Module ZXvertNotation.

Declare Custom Entry zxvert.

Notation "'[vert' e ']'" := e 
  (e custom zxvert at level 200, at level 0) : ZX_scope.

Notation "zx0 ∝ zx1" := (ZXvert_prop zx0 zx1)
  (in custom zxvert at level 70).

Notation "zx0 ⟷ zx1" := (compose_ZX_vert zx0 zx1)
  (in custom zxvert at level 50).

Notation "zx0 ↕ zx1" := (stack_ZX_vert zx0 zx1)
  (in custom zxvert at level 40).



End ZXvertNotation.


Lemma compose_ZX_vert_alt {n m o} (zx0 : ZXvert n m) (zx1 : ZXvert m o) :
  compose_ZX_vert zx0 zx1 ∝ n_cap_mid n m o ⟷ stack_ZX_vert zx0 zx1.
Proof.
Admitted.

(* Section on theory specific to the graphs *)



Definition perm_indep_wrt_upto_swaps m n ns f g :=
  (* m * 2 = big_sum ns n *)
  let f' := Nsum_index n ns ∘ f in 
  let g' := Nsum_index n ns ∘ g in
  forall k, k < m -> 
  (f' (k * 2) = g' (k * 2) /\ f' (k * 2 + 1) = g' (k * 2 + 1)) \/
  (f' (k * 2) = g' (k * 2 + 1) /\ f' (k * 2 + 1) = g' (k * 2)).

Definition perm_indep_wrt_upto_swaps_bool m n ns f g :=
  (* m * 2 = big_sum ns n *)
  let f' := Nsum_index n ns ∘ f in 
  let g' := Nsum_index n ns ∘ g in
  forallb (fun k =>  
  ((f' (k * 2) =? g' (k * 2)) && (f' (k * 2 + 1) =? g' (k * 2 + 1))) ||
  ((f' (k * 2) =? g' (k * 2 + 1)) && (f' (k * 2 + 1) =? g' (k * 2))))
  (seq 0 m).

Lemma perm_indep_wrt_upto_swaps_bool_true_iff m n ns f g : 
  perm_indep_wrt_upto_swaps_bool m n ns f g = true <->
  perm_indep_wrt_upto_swaps m n ns f g.
Proof.
  unfold perm_indep_wrt_upto_swaps_bool.
  rewrite forallb_seq0.
  apply forall_lt_iff.
  intros k Hk.
  rewrite orb_true_iff, 2!andb_true_iff, 4!Nat.eqb_eq.
  reflexivity.
Qed.

Lemma perm_indep_wrt_upto_swaps_sym m n ns f g : 
  perm_indep_wrt_upto_swaps m n ns g f -> 
  perm_indep_wrt_upto_swaps m n ns f g.
Proof.
  intros H k Hk.
  pose proof (H k Hk).
  intuition auto.
Qed.





Definition pair_biperm (n : nat) : Type := nat -> nat.

Definition WF_pair_biperm {n} (f : pair_biperm n) :=
  permutation (n * 2) f.

Definition biperm_of_pair_biperm {n} (f : pair_biperm n) : nat -> nat :=
  compose_perm_biperm (n * 2) (n_m_cup_cap n 0) f.

Lemma biperm_of_pair_biperm_bipermutation {n} (f : pair_biperm n) 
  (Hf : WF_pair_biperm f) :
  bipermutation (n * 2) (biperm_of_pair_biperm f).
Proof.
  apply compose_perm_bipermutation; [|apply Hf].
  auto_biperm.
Qed.

#[export] Hint Resolve biperm_of_pair_biperm_bipermutation : biperm_db.

Definition pair_biperm_of_biperm n (f : nat -> nat) : pair_biperm n :=
  lperm' (NF_of_biperm (n * 2) 0 f).

Lemma WF_pair_biperm_of_biperm n f (Hf : bipermutation (n * 2) f) : 
  WF_pair_biperm (pair_biperm_of_biperm n f).
Proof.
  apply NF_of_biperm_WF.
  rewrite Nat.add_0_r.
  assumption.
Qed.

Lemma pair_biperm_of_biperm_correct n f (Hf : bipermutation (n * 2) f) :
  perm_eq (n * 2) (biperm_of_pair_biperm (pair_biperm_of_biperm n f))
  f.
Proof.
  unfold pair_biperm_of_biperm.
  pose proof (NF_of_biperm_spec (n * 2) 0 f ltac:(now rewrite Nat.add_0_r))
    as (HWF & Hin & Hout & Heq).
  pose proof HWF as (Hin' & Hout' & Hlperm & Hrperm).
  rewrite Nat.add_0_r in Heq.
  rewrite Hin, Hout in *.
  etransitivity; [|apply Heq].
  rewrite realize_NF_biperm_spec by auto.
  rewrite Hin, Hout.
  assert (Hcup : ncup' (NF_of_biperm (n * 2) 0 f) = n) by lia.
  assert (Hcap : ncap' (NF_of_biperm (n * 2) 0 f) = 0) by lia.
  assert (Hid : nid' (NF_of_biperm (n * 2) 0 f) = 0) by lia.
  rewrite Hcup, Hcap, Hid.
  rewrite 2!stack_perms_0_r.
  rewrite stack_biperms_0_out, stack_perms_0_r.
  unfold biperm_of_pair_biperm.
  rewrite compose_perm_biperm_defn.
  assert (bipermutation (n + n) (n_m_cup_cap n 0)) by auto_biperm.
  replace (n + n) with (n * 2) in * by lia.
  now rewrite 3!make_WF_Perm_perm_eq.
Qed.

Lemma ZX_of_pair_biperm_prf {n} : n * 2 = n + n. 
Proof. lia. Qed.

Definition ZX_of_pair_biperm {n} (f : pair_biperm n) : ZX (n * 2) 0 :=
  zx_of_perm_cast (n * 2) (n + n) f ZX_of_pair_biperm_prf
  ⟷ n_stacked_caps n.

Lemma biperm_of_pair_biperm_WF {n} (f : pair_biperm n) : 
  WF_Perm (n * 2) (biperm_of_pair_biperm f).
Proof.
  apply compose_perm_biperm_WF.
Qed.

#[export] Hint Resolve biperm_of_pair_biperm_WF : WF_Perm_db.




Lemma biperm_of_pair_biperm_alt {n} (f : pair_biperm n) : 
  biperm_of_pair_biperm f = 
  biperm_compose_perm_l (n * 2) 0 (n_m_cup_cap n 0) f.
Proof.
  now rewrite biperm_compose_perm_l_0_r by auto_biperm.
Qed.

Lemma ZX_of_pair_biperm_correct {n} (f : pair_biperm n) (Hf : WF_pair_biperm f) : 
  matrix_of_biperm (n * 2) 0 (biperm_of_pair_biperm f) 
  = ⟦ ZX_of_pair_biperm f ⟧.
Proof.
  rewrite biperm_of_pair_biperm_alt.
  rewrite matrix_of_biperm_compose_perm_l_eq by auto_biperm.
  unfold ZX_of_pair_biperm.
  rewrite zx_compose_spec.
  unfold zx_of_perm_cast.
  simpl_cast_semantics.
  rewrite zx_of_perm_semantics by auto.
  replace (n * 2) with (n + n) by lia.
  rewrite matrix_of_biperm_n_m_cup_cap_0_r.
  now rewrite n_stacked_caps_semantics.
Qed.

Local Obligation Tactic := idtac.





Lemma pair_biperm_of_biperm_WF n f (Hf : bipermutation (n * 2) f) : 
  WF_pair_biperm (pair_biperm_of_biperm n f).
Proof.
  unfold WF_pair_biperm, pair_biperm_of_biperm.
  apply NF_of_biperm_WF.
  now rewrite Nat.add_0_r.
Qed.

Lemma pair_biperm_of_biperm_WF_alt n f (Hf : bipermutation n f) : 
  WF_pair_biperm (pair_biperm_of_biperm (n / 2) f).
Proof.
  pose proof (bipermutation_dim_even n f Hf) as Hev.
  rewrite <- div_2_mul_2_exact_iff_even in Hev.
  apply pair_biperm_of_biperm_WF.
  now rewrite Hev.
Qed.

Lemma pair_biperm_of_biperm_of_zx {n} (zx : ZX n 0) (Hzx : ZXbiperm zx) : 
  zx ∝
  cast _ _ (eq_sym (proj2 (div_2_mul_2_exact_iff_even n) 
    (eq_trans (f_equal Nat.even (eq_sym (Nat.add_0_r n)))
      (zxbiperm_dims_even zx Hzx)))) eq_refl
  (ZX_of_pair_biperm 
    (pair_biperm_of_biperm (n / 2) 
        (biperm_of_zx zx))).
Proof.
  apply ZX_prop_by_mat_prop.
  rewrite (NF_of_zx_correct zx Hzx).
  simpl_cast_semantics. 
  pose proof (zxbiperm_dims_even zx Hzx) as Hev.
  rewrite Nat.add_0_r in Hev.
  assert (n / 2 * 2 = n) as Hex by (now apply div_2_mul_2_exact_iff_even).
  assert (bipermutation (n / 2 * 2) (biperm_of_zx zx)) by 
    (rewrite Hex, <- (Nat.add_0_r n) at 1; 
    now apply biperm_of_zx_bipermutation).
  rewrite <- ZX_of_pair_biperm_correct by 
    (apply pair_biperm_of_biperm_WF; assumption).
  erewrite matrix_of_biperm_eq_of_perm_eq;
  [|rewrite Nat.add_0_r;
  now apply pair_biperm_of_biperm_correct].
  now rewrite Hex.
Qed.




Lemma zx_of_pair_biperm_succ n (f : pair_biperm (S n)) 
  (Hf : WF_pair_biperm f) prf : 
  zx_of_perm (S n + S n) f ⟷ n_stacked_caps (S n) ∝
  zx_arb_cap (f 0) (f 1) (S n + S n) ⟷
    zx_of_perm_cast _ _ (contract_biperm 0 1 f) prf ⟷ n_stacked_caps n.
Proof.
  rewrite n_stacked_caps_succ.
  rewrite stack_split_diag.
  rewrite cast_compose_distribute.
  rewrite <- compose_assoc.
  rewrite cap_stack_n_wire_r_to_arb_cap, cast_contract_eq.
  rewrite cast_zx_arb_cap_natural_l.
  rewrite (cast_compose_r_eq_mid (zx_of_perm _ f)).
  rewrite zx_arb_cap_compose_zx_of_perm_l by 
    ((eapply permutation_change_dims; [|apply Hf]; lia) + lia).
  rewrite stack_empty_l, cast_id.
  apply compose_simplify_l.
  rewrite cast_compose_distribute_r_eq_mid.
  apply compose_simplify_r.
  cast_irrelevance.
Qed.

(* Section on graph specifics *)


Definition WF_ZXdecomp {n m} (zx : ZXdecomp n m) : Prop :=
  ZXstack (zx.(spiders)) /\ ZXbiperm (zx.(iobiperm)).

Create HintDb wf_zx_db discriminated.
#[export] Hint Extern 100 (ZXbiperm _) => 
  solve [auto with zxbiperm_db | auto with zxbiperm_db zxperm_db] 
  : wf_zx_db.
Hint Constructors ZXstack : wf_zx_db.
Hint Resolve ZXstack_cast : wf_zx_db.
Hint Extern 100 (WF_ZXdecomp _) => split : wf_zx_db.
Hint Extern 0 (ZXstack (?zx0 ↕ ?zx1)) =>
  apply (ZXstack_stack zx0 zx1) : wf_zx_db.

Lemma WF_ZXdecomp_ZXstack {n m} (zx : ZXdecomp n m) : 
  WF_ZXdecomp zx -> ZXstack (zx.(spiders)).
Proof. now unfold WF_ZXdecomp. Qed.

Lemma WF_ZXdecomp_ZXbiperm {n m} (zx : ZXdecomp n m) : 
  WF_ZXdecomp zx -> ZXbiperm (zx.(iobiperm)).
Proof. now unfold WF_ZXdecomp. Qed.

#[export] Hint Resolve WF_ZXdecomp_ZXstack WF_ZXdecomp_ZXbiperm : wf_zx_db. 

Lemma WF_ZXdecomp_biperm {n m} (zx : ZX n m) (Hzx : ZXbiperm zx) :  
  WF_ZXdecomp (ZXdecomp_biperm zx).
Proof.
  auto with wf_zx_db.
Qed.

#[export] Hint Resolve WF_ZXdecomp_biperm : wf_zx_db.

Lemma WF_ZXdecomp_stack {n0 m0 n1 m1} (zx0 : ZXdecomp n0 m0)
  (zx1 : ZXdecomp n1 m1) : WF_ZXdecomp zx0 -> WF_ZXdecomp zx1 ->
  WF_ZXdecomp (ZXdecomp_stack zx0 zx1).
Proof.
  intros Hzx0 Hzx1.
  split; cbn; [auto with wf_zx_db|].
  auto with wf_zx_db zxbiperm_db.
Qed.

#[export] Hint Resolve WF_ZXdecomp_stack : wf_zx_db.

Lemma WF_ZXdecomp_compose {n m o} (zx0 : ZXdecomp n m)
  (zx1 : ZXdecomp m o) : WF_ZXdecomp zx0 -> WF_ZXdecomp zx1 ->
  WF_ZXdecomp (ZXdecomp_compose zx0 zx1).
Proof.
  intros Hzx0 Hzx1.
  split; cbn; [auto with wf_zx_db|].
  auto with wf_zx_db zxbiperm_db.
Qed.

#[export] Hint Resolve WF_ZXdecomp_compose : wf_zx_db.

Lemma WF_ZXdecomp_Z n m α : WF_ZXdecomp (ZXdecomp_Z n m α).
Proof. split; cbn; auto with wf_zx_db. Qed.

Lemma WF_ZXdecomp_X n m α : WF_ZXdecomp (ZXdecomp_X n m α).
Proof. split; cbn; auto with wf_zx_db. Qed.

Lemma WF_ZXdecomp_box : WF_ZXdecomp (ZXdecomp_box).
Proof. split; cbn; auto with wf_zx_db. Qed.

#[export] Hint Resolve WF_ZXdecomp_Z WF_ZXdecomp_X 
  WF_ZXdecomp_box : wf_zx_db.

Lemma WF_ZXdecomp_of_ZX {n m} (zx : ZX n m) : WF_ZXdecomp (ZXdecomp_of_ZX zx).
Proof. induction zx; cbn [ZXdecomp_of_ZX]; auto with wf_zx_db. Qed.

Lemma WF_ZXdecomp_of_ZX_alt {n m} (zx : ZX n m) : 
  WF_ZXdecomp (ZXdecomp_of_ZX_alt zx).
Proof. 
  induction zx;
  [apply WF_ZXdecomp_biperm; constructor.. | | | | |];
  [cbn; auto with wf_zx_db.. | |];
  cbn [ZXdecomp_of_ZX_alt].
  - destruct (is_ZXbiperm (zx1 ↕ zx2)) eqn:e;
    auto using is_ZXbiperm_ZXbiperm with wf_zx_db.
  - destruct (is_ZXbiperm (zx1 ⟷ zx2)) eqn:e;
    auto using is_ZXbiperm_ZXbiperm with wf_zx_db.
Qed.

#[export] Hint Resolve WF_ZXdecomp_of_ZX WF_ZXdecomp_of_ZX_alt : wf_zx_db.






Record ZXbd {n m : nat} : Set := {
  bd_size : nat;
  bd_spiders : ZX 0 bd_size;
  bd_iobiperm : ZX (bd_size + n + m) 0;
}.

Arguments ZXbd (_ _)%nat_scope : clear implicits.



Definition ZX_of_bd {n m} (zxd : ZXbd n m) : ZX n m :=
  cast _ _ (eq_sym (Nat.add_0_r _)) eq_refl 
    (zxd.(bd_spiders) ↕ n_wire n ↕ n_cap m ⟷ 
  cast _ _ (Nat.add_assoc _ _ _) eq_refl
  (zxd.(bd_iobiperm) ↕ n_wire m)).

Arguments ZX_of_bd _ /.

Coercion ZX_of_bd : ZXbd >-> ZX.

Definition ZXbd_of_decomp {n m} (zxd : ZXdecomp n m) : ZXbd n m :=
  {|
    bd_size := zxd.(mid_size);
    bd_spiders := zxd.(spiders);
    bd_iobiperm := zxd.(iobiperm) ↕ n_wire m ⟷ n_cup m;
  |}.

Lemma ZXbd_of_decomp_correct {n m} (zxd : ZXdecomp n m) : 
  zxd ∝ ZXbd_of_decomp zxd.
Proof.
  cbn -[n_cup].
  rewrite (stack_split_diag _ (n_cap m)).
  rewrite compose_assoc, cast_compose_distribute.
  unshelve (eapply compose_simplify_casted); [lia|..];
  rewrite cast_contract_eq.
  - clean_eqns rewrite stack_empty_r, cast_contract_eq.
    now rewrite cast_id.
  - rewrite cast_backwards_rev.
    rewrite stack_nwire_distribute_r.
    clean_eqns rewrite stack_assoc.
    rewrite cast_compose_l, cast_contract_eq.
    rewrite cast_compose_distribute.
    rewrite cast_id.
    rewrite <- compose_assoc, <- stack_compose_distr.
    rewrite n_wire_stack, nwire_removal_l, nwire_removal_r.
    rewrite stack_split_diag.
    clean_eqns rewrite stack_empty_r, compose_assoc, cast_compose_l.
    apply cast_simplify.
    rewrite cast_contract_eq.
    rewrite big_yank_r.
    rewrite cast_contract_eq, cast_id.
    now rewrite nwire_removal_r.
Qed.



(* Represent a ZX diagram with a stack of spiders, 
  a permutation, and edges. *)
Record ZX_pe_graph {n m : nat} : Set := {
  pe_edges : nat;
  pe_numspi : nat;
  pe_deg : nat -> nat;
  pe_color : nat -> bool;
  pe_phase : nat -> R;
  pe_ioperm : nat -> nat;
  pe_size_pf : big_sum pe_deg pe_numspi + n + m = pe_edges * 2;
}.

Arguments ZX_pe_graph (_ _)%nat : clear implicits.

Definition ZXbd_of_pe_graph {n m} (zxg : ZX_pe_graph n m) : ZXbd n m := {|
    (* bd_size  *)
    bd_spiders := 
      cast _ _ (Nsum_constant_0' _) eq_refl 
        (big_stack (fun _ => 0) zxg.(pe_deg)
        (fun k => b2ZX (zxg.(pe_color) k) _ _ (zxg.(pe_phase) k))
        zxg.(pe_numspi));
    bd_iobiperm :=
      zx_of_perm_cast _ _ 
        zxg.(pe_ioperm) zxg.(pe_size_pf)
      ⟷ 
      cast _ _ eq_refl (eq_sym (Nat.mul_0_r _))
      (zxg.(pe_edges) ⇑ ⊃)
|}.

Coercion ZXbd_of_pe_graph : ZX_pe_graph >-> ZXbd.

Lemma ZXbd_alt_form {n m} (zxb : ZXbd n m) : 
  zxb ∝ 
  cast n m (eq_sym (Nat.add_0_r _ )) eq_refl
  (n_wire n ↕ n_cap m ⟷
    cast (n + (m + m)) m ( (Nat.add_assoc _ _ _)) eq_refl
    ((zxb.(bd_spiders) ↕ n_wire n ↕ n_wire m ⟷ 
    zxb.(bd_iobiperm)) ↕ n_wire m)).
Proof.
  cbn - [n_cup].
  symmetry.
  rewrite stack_nwire_distribute_r.
  rewrite (cast_compose_distribute _ (_ + (_ + _))).
  rewrite <- compose_assoc.
  clean_eqns rewrite stack_assoc, cast_contract_eq.
  rewrite (cast_compose_r _ _ (_ ↕ _)).
  rewrite cast_id.
  rewrite <- stack_compose_distr.
  rewrite n_wire_stack, nwire_removal_l, nwire_removal_r.
  rewrite cast_compose_l, cast_contract_eq.
  apply cast_simplify, compose_simplify; [reflexivity|].
  rewrite cast_contract_eq.
  cast_irrelevance.
Qed.

Lemma ZXbd_to_flat {n m} (zxb : ZXbd n m) : 
  zxb ↕ n_wire m ⟷ n_cup m ∝
  zxb.(bd_spiders) ↕ n_wire n ↕ n_wire m ⟷ zxb.(bd_iobiperm).
Proof.
  rewrite ZXbd_alt_form.
  clean_eqns rewrite cast_stack_l, stack_nwire_distribute_r, 
    cast_stack_l, cast_compose_l.
  clean_eqns rewrite (stack_assoc 
    (_ ⟷ bd_iobiperm zxb) (n_wire m) (n_wire m)).
  rewrite cast_contract_eq, compose_assoc.
  rewrite cast_compose_eq_mid_join.
  rewrite <- (stack_empty_l (n_cup m)).
  rewrite <- (stack_compose_distr (_ ⟷ bd_iobiperm zxb) ⦰ _ (n_cup m)).
  rewrite compose_empty_r, n_wire_stack, nwire_removal_l.
  rewrite (stack_split_antidiag _ (n_cup m)).
  rewrite cast_compose_r, <- compose_assoc.
  rewrite cast_contract_eq.
  clean_eqns rewrite stack_empty_r, cast_compose_r, cast_contract_eq.
  rewrite cast_compose_distribute, cast_id.
  etransitivity; [|apply nwire_removal_l].
  apply compose_simplify; [|reflexivity].
  clean_eqns rewrite <- n_wire_stack, 2!stack_assoc.
  rewrite 2!cast_contract_eq.
  rewrite cast_compose_distribute, 2!cast_contract_eq.
  clean_eqns rewrite cast_compose_l, cast_contract_eq, 
    cast_stack_distribute_fwd_l.
  rewrite <- stack_compose_distr.
  rewrite nwire_removal_l, cast_id.
  clean_eqns rewrite cast_stack_distribute_fwd_l.
  apply stack_simplify; [now rewrite cast_id|].
  rewrite cast_id.
  apply big_yank_l.
Qed.

(* FIXME: Move *)
Lemma ZXbd_equiv_iff_raw {n m} (zxb zxb' : ZXbd n m) : 
  zxb ∝ zxb' <-> 
  zxb.(bd_spiders) ↕ n_wire n ↕ n_wire m ⟷ zxb.(bd_iobiperm) ∝
  zxb'.(bd_spiders) ↕ n_wire n ↕ n_wire m ⟷ zxb'.(bd_iobiperm).
Proof.
  split.
  - intros Hequiv.
    assert (zxb ↕ n_wire m ⟷ n_cup m ∝ zxb' ↕ n_wire m ⟷ n_cup m)
      as Heq' by now rewrite Hequiv.
    revert Heq'.
    now rewrite 2!ZXbd_to_flat.
  - intros Hequiv.
    rewrite 2!ZXbd_alt_form.
    now rewrite Hequiv.
Qed.




Lemma ZX_pe_graph_equiv_iff_raw {n m} (zxg zxg' : ZX_pe_graph n m) : 
  zxg ∝ zxg' <-> 
  cast _ _ (f_equal (fun k => k + n + m) (Nsum_constant_0' _)) 
    (eq_sym (Nat.mul_0_r _))
  (big_stack (fun _ => 0) zxg.(pe_deg)
    (fun k => b2ZX (zxg.(pe_color) k) _ _ (zxg.(pe_phase) k))
    zxg.(pe_numspi) ↕ n_wire n ↕ n_wire m ⟷
  zx_of_perm_cast _ _ zxg.(pe_ioperm) zxg.(pe_size_pf)
  ⟷ (zxg.(pe_edges) ⇑ ⊃)) ∝
  cast _ _ (f_equal (fun k => k + n + m) (Nsum_constant_0' _)) 
    (eq_sym (Nat.mul_0_r _))
  (big_stack (fun _ => 0) zxg'.(pe_deg)
    (fun k => b2ZX (zxg'.(pe_color) k) _ _ (zxg'.(pe_phase) k))
    zxg'.(pe_numspi) ↕ n_wire n ↕ n_wire m ⟷
  zx_of_perm_cast _ _ zxg'.(pe_ioperm) zxg'.(pe_size_pf)
  ⟷ (zxg'.(pe_edges) ⇑ ⊃)).
Proof.
  rewrite ZXbd_equiv_iff_raw.
  cbn [bd_spiders bd_iobiperm ZXbd_of_pe_graph].
  rewrite 4!cast_stack_l_fwd.
  do 2 rewrite cast_compose_l, cast_id.
  do 4 rewrite cast_compose_r, cast_id.
  rewrite 2!cast_contract_eq, 2!compose_assoc.
  apply prop_iff_simplify; cast_irrelevance.
Qed.

Open Scope prg.

Definition set_pe_graph_ioperm {n m} (zxp : ZX_pe_graph n m) f
  : ZX_pe_graph n m :=
  {|
  pe_edges := zxp.(pe_edges); 
  pe_numspi := zxp.(pe_numspi); 
  pe_deg := zxp.(pe_deg); 
  pe_color := zxp.(pe_color); 
  pe_phase := zxp.(pe_phase); 
  pe_ioperm := f; 
  pe_size_pf := zxp.(pe_size_pf);
|}.

Definition compose_perm_pe_l {n m} (zxp : ZX_pe_graph n m) f 
  : ZX_pe_graph n m := set_pe_graph_ioperm zxp (f ∘ zxp.(pe_ioperm)).

Definition compose_perm_pe_r {n m} (zxp : ZX_pe_graph n m) f 
  : ZX_pe_graph n m := set_pe_graph_ioperm zxp (zxp.(pe_ioperm) ∘ f).







Lemma ZX_pe_graph_absorb_conditional_swap_r {n m} 
  (zxp : ZX_pe_graph n m) (cond : nat -> bool) 
  (Hzxp : permutation (zxp.(pe_edges) * 2) zxp.(pe_ioperm)) :
  compose_perm_pe_r zxp (big_stack_perms zxp.(pe_edges) 
    (fun _ => 2) (fun k => if cond k then swap_2_perm else idn)) ∝ zxp.
Proof.
  rewrite ZX_pe_graph_equiv_iff_raw;
  cbn.
  apply cast_simplify.
  rewrite 2!compose_assoc.
  apply compose_simplify; [reflexivity|].
  rewrite n_stack_to_big_stack.
  unfold zx_of_perm_cast.
  rewrite 2!(cast_zx_of_perm_natural_r (_ +_)).
  rewrite <- compose_zx_of_perm by auto_perm.
  rewrite cast_compose_distribute.
  rewrite compose_assoc.
  apply compose_simplify; [cast_irrelevance|].
  rewrite cast_compose_r, cast_contract_eq.
  rewrite cast_zx_of_perm_natural_r.
  rewrite cast_compose_l, cast_id, cast_contract_eq.
  apply cast_simplify.
  rewrite zx_of_big_stack_perms by auto_perm.
  rewrite big_stack_compose.
  apply big_stack_simplify.
  intros k Hk.
  destruct (cond k).
  - rewrite zx_of_swap_2_perm.
    now rewrite cap_swap_absorbtion.
  - now rewrite zx_of_perm_idn, nwire_removal_l.
Qed.




Definition pe_full_sizes {n m} (zxp : ZX_pe_graph n m) : nat -> nat :=
  fun k => if k <? zxp.(pe_numspi) then zxp.(pe_deg) k else 1.

Lemma pe_full_sizes_sum {n m} (zxp : ZX_pe_graph n m) : 
  big_sum (pe_full_sizes zxp) (zxp.(pe_numspi) + n + m) = 
  zxp.(pe_edges) * 2.
Proof.
  rewrite <- pe_size_pf.
  rewrite <- 2 Nat.add_assoc.
  unfold pe_full_sizes.
  rewrite (Nsum_if_lt _ _ _ (fun _ => _)).
  rewrite Nsum_1.
  reflexivity.
Qed.



Lemma set_pe_graph_ioperm_perm_equiv_wrt_simplify 
  {n m} (zxp : ZX_pe_graph n m) f 
  (Hf : permutation (zxp.(pe_edges) * 2) f)
  (Hzxp : permutation (zxp.(pe_edges) * 2) zxp.(pe_ioperm))
  (Hfeq : f ~[/ (zxp.(pe_numspi) + n + m) (pe_full_sizes zxp)] 
    zxp.(pe_ioperm)) :
  set_pe_graph_ioperm zxp f ∝
  zxp.
Proof.
  rewrite <- pe_full_sizes_sum in *.
  pose proof (perm_indep_wrt_diff_idn _ _ _ _ Hf Hzxp Hfeq) as Hidn.
  pose proof ((fun H => perm_indep_wrt_idn_all_shifts_perms 
    _ _ _ H Hidn) ltac:(auto_perm)) as Hperm.
  rewrite ZX_pe_graph_equiv_iff_raw.
  cbn.
  apply cast_simplify.
  apply compose_simplify; [|reflexivity].
  apply (cast_diagrams _ _ eq_refl (pe_full_sizes_sum zxp)).
  rewrite 2!cast_compose_distribute, cast_id.
  unfold zx_of_perm_cast.
  rewrite 2!cast_contract_eq.
  rewrite 2!(cast_zx_of_perm_natural_r (_ + _)).
  rewrite (perm_indep_wrt_diff_rw Hfeq) by auto.
  rewrite <- compose_zx_of_perm by auto_perm.
  rewrite cast_compose_distribute.
  rewrite cast_zx_of_perm_natural_l, cast_id.
  rewrite cast_compose_l, cast_compose_distribute, cast_contract_eq, cast_id.
  rewrite <- compose_assoc.
  apply compose_simplify; [|cast_irrelevance].
  rewrite <- ((fun H => cast_zx_of_perm _ _ _ H H) (pe_size_pf _)).
  rewrite <- ((fun H => cast_zx_of_perm _ _ _ H H) 
    (eq_sym (pe_full_sizes_sum zxp))).
  rewrite zx_of_big_stack_perms by auto.
  clean_eqns rewrite stack_assoc, cast_compose_l.
  rewrite n_wire_stack.
  rewrite n_stack1_to_big_stack, cast_stack_r_fwd.
  rewrite big_stack_join_add.
  rewrite (big_stack_rebound (Nat.add_assoc _ _ _)).
  rewrite 5!cast_contract_eq.
  rewrite cast_compose_eq_mid_join.
  rewrite big_stack_compose.
  rewrite cast_contract_eq.
  apply cast_simplify.
  apply big_stack_simplify.
  intros k Hk.
  unfold pe_full_sizes.
  bdestruct (k <? pe_numspi zxp).
  - apply b2ZX_zxperm_absorbtion_right; auto_zxperm.
  - rewrite wire_removal_l.
    apply zx_of_perm_1.
Qed.

(* FIXME: Move *)
Lemma ZXbd_simplify {n m} (zxb zxb' : ZXbd n m) : 
  zxb.(bd_size) = zxb'.(bd_size) ->
  (forall H, zxb.(bd_spiders) ∝ cast _ _ eq_refl H zxb'.(bd_spiders)) ->
  (forall H, zxb.(bd_iobiperm) ∝ cast _ _ H eq_refl zxb'.(bd_iobiperm)) ->
  zxb ∝ zxb'.
Proof.
  destruct zxb as [k spi bip],
    zxb' as [k' spi' bip'];
  cbn [bd_size bd_spiders bd_iobiperm].
  intros <- Hspi Hbip.
  specialize (Hspi eq_refl).
  specialize (Hbip eq_refl).
  cbn in *.
  apply cast_simplify.
  apply compose_simplify;
  [|now rewrite Hbip].
  now rewrite Hspi.
Qed.


Lemma ZX_pe_graph_simplify {n m} (zxp zxp' : ZX_pe_graph n m) :
  zxp.(pe_edges) = zxp'.(pe_edges) -> 
  zxp.(pe_numspi) = zxp'.(pe_numspi) ->
  perm_eq (zxp.(pe_numspi)) zxp.(pe_deg) zxp'.(pe_deg) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_color) k = zxp'.(pe_color) k) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_phase) k = zxp'.(pe_phase) k) -> 
  perm_eq (zxp.(pe_edges) * 2) zxp.(pe_ioperm) zxp'.(pe_ioperm) ->
  zxp ∝ zxp'.
Proof.
  destruct zxp as [R k deg col phase f HkR],
    zxp' as [R' k' deg' col' phase' f' HkR'];
  cbn [pe_edges pe_numspi pe_deg pe_color pe_phase pe_ioperm].
  intros <- <- Hdeg Hcol Hphase Hf.
  apply ZXbd_simplify;
  cbn [pe_edges pe_numspi pe_deg pe_color pe_phase pe_ioperm
    bd_size bd_spiders bd_iobiperm ZXbd_of_pe_graph].
  - now apply big_sum_eq_bounded.
  - intros H.
    rewrite cast_contract_eq.
    apply big_stack_simplify_casted_casted_abs;
    [easy..|].
    intros l ? ? Hl.
    rewrite cast_b2ZX.
    apply b2ZX_simplify; auto.
  - intros H.
    rewrite cast_compose_distribute, cast_id.
    apply compose_simplify; [|reflexivity].
    unfold zx_of_perm_cast.
    rewrite cast_zx_of_perm_natural_r, cast_backwards_fwd,
      2!cast_contract_eq, cast_zx_of_perm.
    now rewrite Hf.
Qed.

Lemma ZX_pe_graph_simplify_indep_wrt {n m} (zxp zxp' : ZX_pe_graph n m)
  (Hzxp : permutation (zxp.(pe_edges) * 2) zxp.(pe_ioperm))
  (Hzxp' : permutation (zxp'.(pe_edges) * 2) zxp'.(pe_ioperm))
  (Heq : zxp'.(pe_ioperm) 
    ~[/ (zxp.(pe_numspi) + n + m) (pe_full_sizes zxp)] 
    zxp.(pe_ioperm)) :
  zxp.(pe_edges) = zxp'.(pe_edges) -> 
  zxp.(pe_numspi) = zxp'.(pe_numspi) ->
  perm_eq (zxp.(pe_numspi)) zxp.(pe_deg) zxp'.(pe_deg) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_color) k = zxp'.(pe_color) k) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_phase) k = zxp'.(pe_phase) k)  -> 
  zxp ∝ zxp'.
Proof.
  intros Hedge Hnumspi Hdeg Hcol Hphase.
  rewrite <- Hedge in Hzxp'.
  rewrite <- (set_pe_graph_ioperm_perm_equiv_wrt_simplify
    zxp _ Hzxp' Hzxp Heq).
  apply ZX_pe_graph_simplify;
  cbn [pe_edges pe_numspi pe_deg pe_color pe_phase pe_ioperm
    set_pe_graph_ioperm]; 
  auto_perm.
Qed.





Lemma ZX_pe_graph_simplify_input_swaps_prop {n m} (zxp zxp' : ZX_pe_graph n m)
  (Hzxp : permutation (zxp.(pe_edges) * 2) zxp.(pe_ioperm))
  (Hzxp' : permutation (zxp'.(pe_edges) * 2) zxp'.(pe_ioperm))
  (Heq : forall k, k < zxp.(pe_edges) -> 
    (zxp.(pe_ioperm) (k * 2) = zxp'.(pe_ioperm) (k * 2)
    /\ zxp.(pe_ioperm) (k * 2 + 1) = zxp'.(pe_ioperm) (k * 2 + 1)) \/
    (zxp.(pe_ioperm) (k * 2) = zxp'.(pe_ioperm) (k * 2 + 1)
    /\ zxp.(pe_ioperm) (k * 2 + 1) = zxp'.(pe_ioperm) (k * 2))) :
  zxp.(pe_edges) = zxp'.(pe_edges) -> 
  zxp.(pe_numspi) = zxp'.(pe_numspi) ->
  perm_eq (zxp.(pe_numspi)) zxp.(pe_deg) zxp'.(pe_deg) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_color) k = zxp'.(pe_color) k) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_phase) k = zxp'.(pe_phase) k)  -> 
  zxp ∝ zxp'.
Proof.
  intros Hedge Hnumspi Hdeg Hcol Hphase.
  transitivity 
  (compose_perm_pe_r zxp
  (big_stack_perms (pe_edges zxp) (fun _ => 2)
	 (fun k => if 
   (zxp.(pe_ioperm) (k * 2) =? zxp'.(pe_ioperm) (k * 2 + 1))
    then swap_2_perm else idn))).
  - symmetry.
    now apply ZX_pe_graph_absorb_conditional_swap_r.
  - apply ZX_pe_graph_simplify;
    [assumption..|].
    cbn.
    rewrite big_stack_perms_constant_alt.
    rewrite perm_eq_split_times_2_iff.
    intros k Hk.
    unfold compose.
    rewrite Nat.div_mul, Nat.div_add_l, Nat.Div0.mod_mul, 
      mod_add_l, Nat.mod_small, Nat.div_small, Nat.add_0_r by lia.
    specialize (Heq k Hk).
    bdestruct_one.
    + cbn. rewrite Nat.add_0_r. lia.
    + cbn. rewrite Nat.add_0_r. lia.
Qed.

Lemma ZX_pe_graph_simplify_full_prop {n m} (zxp zxp' : ZX_pe_graph n m)
  (Hzxp : permutation (zxp.(pe_edges) * 2) zxp.(pe_ioperm))
  (Hzxp' : permutation (zxp'.(pe_edges) * 2) zxp'.(pe_ioperm))
  (Heq : 
    perm_indep_wrt_upto_swaps zxp.(pe_edges) 
      (zxp.(pe_numspi) + n + m) (pe_full_sizes zxp)
      zxp.(pe_ioperm) zxp'.(pe_ioperm)) :
  zxp.(pe_edges) = zxp'.(pe_edges) -> 
  zxp.(pe_numspi) = zxp'.(pe_numspi) ->
  perm_eq (zxp.(pe_numspi)) zxp.(pe_deg) zxp'.(pe_deg) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_color) k = zxp'.(pe_color) k) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_phase) k = zxp'.(pe_phase) k)  -> 
  zxp ∝ zxp'.
Proof.
  intros Hedge Hnumspi Hdeg Hcol Hphase.
  let N' := constr:(Nsum_index (zxp.(pe_numspi) + n + m) 
    (pe_full_sizes zxp)) in 
  transitivity 
  (compose_perm_pe_r zxp
  (big_stack_perms (pe_edges zxp) (fun _ => 2)
	 (fun k => if 
   ((N' ∘ zxp.(pe_ioperm)) (k * 2) =? (N' ∘ zxp'.(pe_ioperm)) (k * 2 + 1)) 
    then swap_2_perm else idn))).
  - symmetry.
    now apply ZX_pe_graph_absorb_conditional_swap_r.
  - apply ZX_pe_graph_simplify_indep_wrt;
    [|assumption | | assumption..].
    + cbn.
      auto_perm.
    + cbn.
      change (pe_full_sizes ?zx') with (pe_full_sizes zxp).
      unfold perm_indep_wrt.
      unfold perm_indep_wrt_upto_swaps in Heq.
      rewrite <- Combinators.compose_assoc.
      rewrite pe_full_sizes_sum.
      rewrite big_stack_perms_constant_alt.
      rewrite perm_eq_split_times_2_iff.
      intros k Hk.
      change ((?f ∘ ?g ∘ ?h) ?x) with ((f ∘ g) (h x)).
      cbn beta.
      rewrite Nat.div_mul, Nat.div_add_l, Nat.Div0.mod_mul, 
        mod_add_l, Nat.mod_small, Nat.div_small, Nat.add_0_r by lia.
      specialize (Heq k Hk).
      bdestruct_one.
      * cbn. rewrite Nat.add_0_r. lia.
      * cbn. rewrite Nat.add_0_r. lia.
Qed.

Lemma ZX_pe_graph_simplify_full_bool {n m} (zxp zxp' : ZX_pe_graph n m)
  (Hzxp : permutation (zxp.(pe_edges) * 2) zxp.(pe_ioperm))
  (Hzxp' : permutation (zxp'.(pe_edges) * 2) zxp'.(pe_ioperm))
  (Heq : 
    perm_indep_wrt_upto_swaps_bool zxp.(pe_edges) 
      (zxp.(pe_numspi) + n + m) (pe_full_sizes zxp)
      zxp.(pe_ioperm) zxp'.(pe_ioperm) = true) :
  zxp.(pe_edges) = zxp'.(pe_edges) -> 
  zxp.(pe_numspi) = zxp'.(pe_numspi) ->
  perm_eq (zxp.(pe_numspi)) zxp.(pe_deg) zxp'.(pe_deg) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_color) k = zxp'.(pe_color) k) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_phase) k = zxp'.(pe_phase) k)  -> 
  zxp ∝ zxp'.
Proof.
  rewrite perm_indep_wrt_upto_swaps_bool_true_iff in Heq.
  now apply ZX_pe_graph_simplify_full_prop.
Qed.





Lemma ZX_pe_graph_absorb_edge_perm_r {n m} 
  (zxp : ZX_pe_graph n m) f (Hf : permutation (zxp.(pe_edges)) f) 
  (Hzxp : permutation (pe_edges zxp * 2) (pe_ioperm zxp)) :
  compose_perm_pe_r zxp
  (enlarge_permutation zxp.(pe_edges) f (fun _ => 2)) ∝ zxp.
Proof.
  rewrite ZX_pe_graph_equiv_iff_raw; cbn.
  apply cast_simplify.
  rewrite enlarge_permutation_constant.
  rewrite zx_of_perm_cast_compose_r by auto_perm.
  rewrite 3!compose_assoc.
  apply compose_simplify; [reflexivity|].
  apply compose_simplify; [cast_irrelevance|].
  (* apply ZX_prop_by_mat_prop. *)
  (* cbn. *)
  rewrite <- enlarge_permutation_constant.
  rewrite <- ((fun H => cast_zx_of_perm _ _ _ H H) 
    (eq_sym (Nsum_constant _ _))).
  rewrite (zx_of_enlarge_to_big_zx_of_permutation_l _ _ _ Hf).
  rewrite n_stack_to_big_stack.
  rewrite cast_contract_eq.
  rewrite cast_compose_eq_mid_join.
  apply cast_simplify.
  etransitivity;
  [apply big_zx_of_permutation_l_natural|].
  etransitivity; 
  [|apply nwire_removal_r].
  apply compose_simplify; [reflexivity|].
  by_perm_eq_nosimpl.
  unfold compose.
  rewrite <- Nsum_constant_0' at 1.
  easy.
Qed.





(* Represent a ZX diagram with a stack of spiders, a number of edges,
   and a function saying to which spider each edge-endpoint goes. *)
Record ZX_ve_graph {n m : nat} : Set := {
  ve_edges : nat;
  ve_numspi : nat;
  ve_deg : nat -> nat;
  ve_color : nat -> bool;
  ve_phase : nat -> R;
  ve_iofunc : nat -> nat;
  ve_size_pf : big_sum ve_deg ve_numspi + n + m = ve_edges * 2;
}.

Arguments ZX_ve_graph (_ _) : clear implicits.

Definition ZX_pe_of_ve_graph {n m} (zxv : ZX_ve_graph n m) : 
  ZX_pe_graph n m := {|
  pe_edges := zxv.(ve_edges);
  pe_numspi := zxv.(ve_numspi);
  pe_deg := zxv.(ve_deg);
  pe_color := zxv.(ve_color);
  pe_phase := zxv.(ve_phase);
  pe_ioperm := perm_of_input_func (zxv.(ve_edges) * 2) zxv.(ve_iofunc);
  pe_size_pf := zxv.(ve_size_pf);
|}.

Coercion ZX_pe_of_ve_graph : ZX_ve_graph >-> ZX_pe_graph.

Definition ZX_ve_of_pe_graph {n m} (zxp : ZX_pe_graph n m) :
  ZX_ve_graph n m := {|
  ve_edges := zxp.(pe_edges);
  ve_numspi := zxp.(pe_numspi);
  ve_deg := zxp.(pe_deg);
  ve_color := zxp.(pe_color);
  ve_phase := zxp.(pe_phase);
  ve_iofunc := Nsum_index (zxp.(pe_numspi) + n + m) 
    (pe_full_sizes zxp) ∘ zxp.(pe_ioperm);
  ve_size_pf := zxp.(pe_size_pf);
|}.

Lemma ZX_ve_of_pe_graph_correct {n m} (zxp : ZX_pe_graph n m) 
  (Hzxp : permutation (zxp.(pe_edges) * 2) zxp.(pe_ioperm)) : 
  ZX_ve_of_pe_graph zxp ∝ zxp.
Proof.
  apply ZX_pe_graph_simplify_indep_wrt;
  cbn [pe_edges pe_numspi pe_deg pe_color pe_phase pe_ioperm
    ve_edges ve_numspi ve_deg ve_color ve_phase ve_iofunc
    ZX_ve_of_pe_graph ZX_pe_of_ve_graph];
  [auto_perm | auto_perm|
  | reflexivity..].
  rewrite <- pe_full_sizes_sum in *.
  apply perm_indep_wrt_perm_of_input_func, Hzxp.
Qed.

Lemma ZX_ve_graph_simplify {n m} (zxv zxv' : ZX_ve_graph n m) :
  zxv.(ve_edges) = zxv'.(ve_edges) -> 
  zxv.(ve_numspi) = zxv'.(ve_numspi) ->
  perm_eq (zxv.(ve_numspi)) zxv.(ve_deg) zxv'.(ve_deg) -> 
  (forall k, k < zxv.(ve_numspi) -> 
    zxv.(ve_color) k = zxv'.(ve_color) k) -> 
  (forall k, k < zxv.(ve_numspi) -> 
    zxv.(ve_phase) k = zxv'.(ve_phase) k) -> 
  perm_eq (zxv.(ve_edges) * 2) zxv.(ve_iofunc) zxv'.(ve_iofunc) ->
  zxv ∝ zxv'.
Proof.
  intros Hedge Hspi Hdeg Hcol Hphase Hio.
  apply ZX_pe_graph_simplify; [assumption..|].
  cbn [pe_ioperm ZX_pe_of_ve_graph].
  now rewrite Hio, <- Hedge.
Qed.

Definition WF_ZX_ve_graph {n m} (zxv : ZX_ve_graph n m) : Prop :=
  perm_eq (zxv.(ve_numspi) + n + m)
    (count_func_vals (zxv.(ve_edges) * 2) zxv.(ve_iofunc)) 
    (pe_full_sizes zxv).



Lemma WF_ZX_ve_graph_defn {n m} (zxv : ZX_ve_graph n m) :
  WF_ZX_ve_graph zxv <-> 
  perm_eq zxv.(ve_numspi) 
    (count_func_vals (zxv.(ve_edges) * 2) zxv.(ve_iofunc))
    zxv.(ve_deg) /\
  (forall k, k < n + m -> 
    count_func_vals (zxv.(ve_edges) * 2) zxv.(ve_iofunc) 
    (zxv.(ve_numspi) + k) = 1).
Proof.
  unfold WF_ZX_ve_graph.
  rewrite <- Nat.add_assoc.
  unfold perm_eq at 1.
  rewrite forall_nat_lt_add.
  apply ZifyClasses.and_morph.
  - apply forall_lt_iff.
    intros k Hk.
    unfold pe_full_sizes.
    cbn.
    now simplify_bools_lia_one_kernel.
  - apply forall_lt_iff.
    intros k Hk.
    unfold pe_full_sizes.
    cbn.
    now simplify_bools_lia_one_kernel.
Qed.










Lemma WF_ZX_ve_graph_defn_alt {n m} (zxv : ZX_ve_graph n m) :
  WF_ZX_ve_graph zxv <-> 
  perm_eq zxv.(ve_numspi) 
    (count_func_vals (zxv.(ve_edges) * 2) zxv.(ve_iofunc))
    zxv.(ve_deg) /\
  (forall k, k < n + m -> 
    exists l, l < zxv.(ve_edges) * 2 /\ 
    zxv.(ve_iofunc) l = zxv.(ve_numspi) + k /\
      forall i, i < zxv.(ve_edges) * 2 -> 
      zxv.(ve_iofunc) i = zxv.(ve_numspi) + k -> i = l).
Proof.
  rewrite WF_ZX_ve_graph_defn.
  apply and_iff_distr_l; intros _.
  setoid_rewrite count_func_vals_1_defn_alt.
  reflexivity.
Qed.

Lemma WF_ZX_ve_of_pe_graph {n m} (zxp : ZX_pe_graph n m) 
  (Hzxp : permutation (zxp.(pe_edges) * 2) zxp.(pe_ioperm)) : 
  WF_ZX_ve_graph (ZX_ve_of_pe_graph zxp).
Proof.
  unfold WF_ZX_ve_graph.
  cbn [pe_edges pe_numspi pe_deg pe_color pe_phase pe_ioperm
    ve_edges ve_numspi ve_deg ve_color ve_phase ve_iofunc
    ZX_ve_of_pe_graph ZX_pe_of_ve_graph].
  rewrite count_func_vals_reorder by auto.
  rewrite <- pe_full_sizes_sum.
  now rewrite count_func_vals_Nsum_index.
Qed.

















Lemma ZXbd_stack_prf0 {a b c d e f} : 
(a + b + c) + (d + e + f) = a + (b + c) + (d + (e + f)).
Proof. lia. Qed.


(* FIXME: Move *)
Definition ZXbd_stack {n0 m0 n1 m1} 
  (zxb0 : ZXbd n0 m0) (zxb1 : ZXbd n1 m1) : 
  ZXbd (n0 + n1) (m0 + m1) := {|
  bd_size := zxb0.(bd_size) + zxb1.(bd_size);
  bd_spiders := zxb0.(bd_spiders) ↕ zxb1.(bd_spiders);
  bd_iobiperm := 
  (cast _ _ (eq_sym (Nat.add_assoc _ _ _)) (eq_sym (Nat.add_assoc _ _ _))
  (n_wire _ ↕ zx_mid_comm n0 n1 m0 m1)) ⟷ 
  (cast _ _ (eq_sym (Nat.add_assoc _ _ _)) ZXbd_stack_prf0
  (zx_mid_comm _ _ (n0 + m0) (n1 + m1))) ⟷
  (zxb0.(bd_iobiperm) ↕ zxb1.(bd_iobiperm))
|}.



(* Lemma stack_stack_from_0_0_top_comm {n2 n3 m0 m1 m2 m3} 
  (zx0 : ZX 0 m0) (zx1 : ZX 0 m1) (zx2 : ZX n2 m2) (zx3 : ZX n3 m3) : 
  zx0 ↕ zx1 ↕ (zx2 ↕ zx3) ∝
  zx0 ↕ zx2 ↕ (zx1 ↕ zx3) ⟷ zx_mid_comm _ _ _ _.
Proof.
  rewrite zx_mid_comm_commutes_r.
  now rewrite zx_mid_comm_0_third, cast_id, nwire_removal_l.
Qed. *)



Lemma ZXbd_stack_correct {n0 m0 n1 m1} 
  (zxb0 : ZXbd n0 m0) (zxb1 : ZXbd n1 m1) :
  ZXbd_stack zxb0 zxb1 ∝ zxb0 ↕ zxb1.
Proof.
  rewrite ZXbd_alt_form.
  cbn [ZXbd_stack bd_spiders bd_iobiperm].
  rewrite (stack_assoc_fwd (zxb0.(bd_spiders) ↕ zxb1.(bd_spiders))
    (n_wire (n0 + n1))).
  rewrite n_wire_stack.
  rewrite <- 2!compose_assoc.
  rewrite cast_compose_eq_mid_join.
  rewrite <- stack_split_diag, (stack_split_antidiag (_ ↕ _)).
  rewrite (cast_compose_distribute (0 + 0 + _ + _)).
  rewrite stack_empty_l, cast_id.
  do 2 change (0 + ?x) with x.
  rewrite (compose_assoc (zx_mid_comm _ _ _ _)).
  rewrite cast_compose_eq_mid_join.
  rewrite <- (n_wire_stack (n0 + m0)).
  rewrite (zx_mid_comm_commutes_r zxb0.(bd_spiders) zxb1.(bd_spiders)
    (n_wire (n0 + m0)) (n_wire (n1 + m1))).
  rewrite zx_mid_comm_0_second, cast_id, nwire_removal_l.
  rewrite <- (n_wire_stack n0 m0).
  rewrite <- (n_wire_stack n1 m1).
  rewrite (stack_assoc_back_fwd _ (n_wire n0)).
  rewrite (stack_assoc_back_fwd _ (n_wire n1)).
  rewrite cast_stack_l_r, cast_contract_eq, cast_id.
  rewrite compose_assoc.
  rewrite <- (stack_compose_distr _ zxb0.(bd_iobiperm) _ zxb1.(bd_iobiperm)).
  rewrite <- (ZXbd_to_flat zxb0), <- (ZXbd_to_flat zxb1).
  rewrite stack_compose_distr, <- compose_assoc.
  rewrite <- zx_mid_comm_commutes_r, compose_assoc.
  rewrite <- n_cup_split_add.
  rewrite cast_backwards_fwd.
  rewrite stack_nwire_distribute_r, cast_compose_distribute.
  rewrite stack_assoc_fwd, cast_contract_eq.
  rewrite <- compose_assoc.
  rewrite (cast_compose_r _ _ (_ ↕ _)), cast_id.
  rewrite 2!n_wire_stack.
  rewrite <- stack_split_antidiag, stack_split_diag.
  rewrite cast_compose_distribute, compose_assoc, cast_id.
  rewrite cast_compose_l, cast_contract_eq.
  rewrite big_yank_r, cast_contract_eq.
  rewrite cast_compose_r, nwire_removal_r, stack_empty_r_fwd.
  rewrite 2!cast_contract_eq.
  cast_irrelevance.
Qed.


Program Definition ZX_pe_graph_of_bd {n m} (zxb : ZXbd n m) 
  (Hzxbs : ZXstack zxb.(bd_spiders))
  (Hzxbp : ZXbiperm zxb.(bd_iobiperm)) : ZX_pe_graph n m :=
  {|
    pe_edges := (zxb.(bd_size) + n + m) / 2;
    pe_numspi := ZXstack_size zxb.(bd_spiders);
    pe_deg := ZXstack_out_dims zxb.(bd_spiders);
    pe_color := ZXstack_colors zxb.(bd_spiders);
    pe_phase := ZXstack_phases zxb.(bd_spiders);
    pe_ioperm := 
      pair_biperm_of_biperm ((zxb.(bd_size) + n + m) / 2) 
        (biperm_of_zx zxb.(bd_iobiperm));
    pe_size_pf := _
|}.
Next Obligation.
  intros n m zxb Hstack Hbip.
  rewrite <- ZXstack_out_dims_spec by auto.
  symmetry. 
  apply div_2_mul_2_exact_iff_even.
  apply zxbiperm_dims_even in Hbip.
  now rewrite Nat.add_0_r in Hbip.
Qed.

Lemma ZX_pe_graph_of_bd_correct {n m} (zxb : ZXbd n m) 
  (Hzxbs : ZXstack zxb.(bd_spiders))
  (Hzxbp : ZXbiperm zxb.(bd_iobiperm)) : 
  zxb ∝ ZX_pe_graph_of_bd zxb Hzxbs Hzxbp.
Proof.
  apply ZXbd_simplify; [|intros H..].
  - cbn.
    now rewrite <- ZXstack_out_dims_spec by auto.
  - cbn -[cast].
    rewrite cast_contract_eq.
    rewrite (ZXstack_to_big_stack _ Hzxbs) at 1.
    apply big_stack_simplify_casted_casted_abs.
    + refine (proj1 (Nsum_0_iff _ _) _).
      now rewrite <- ZXstack_in_dims_spec.
    + reflexivity.
    + intros k ? ? Hk.
      now rewrite cast_b2ZX.
  - rewrite (pair_biperm_of_biperm_of_zx _ Hzxbp).
    cbn [bd_iobiperm ZX_pe_graph_of_bd ZXbd_of_pe_graph
      pe_deg pe_numspi pe_edges pe_ioperm].
    unfold ZX_of_pair_biperm.
    rewrite 2!cast_compose_distribute, cast_contract_eq, 
      2!cast_zx_of_perm_cast.
    apply compose_simplify_casted_abs; [|intros ?..].
    + lia.
    + rewrite cast_zx_of_perm_cast.
      ereflexivity.
      now apply zx_of_perm_cast_perm_eq_to_eq_proper.
    + unfold n_stacked_caps.
      rewrite 2!cast_contract_eq.
      cast_irrelevance.
Qed.

Lemma ZXbd_of_decomp_stack {n m} (zx : ZX n m) : 
  ZXstack (ZXbd_of_decomp (ZXdecomp_of_ZX zx)).(bd_spiders).
Proof.
  apply WF_ZXdecomp_of_ZX.
Qed.

Lemma ZXbd_of_decomp_biperm {n m} (zx : ZX n m) : 
  ZXbiperm (ZXbd_of_decomp (ZXdecomp_of_ZX zx)).(bd_iobiperm).
Proof.
  cbn.
  pose proof (WF_ZXdecomp_of_ZX zx) as [? ?].
  auto with zxbiperm_db zxperm_db.
Qed.

Definition ZX_pe_graph_of_ZX {n m} (zx : ZX n m) : ZX_pe_graph n m :=
  ZX_pe_graph_of_bd (ZXbd_of_decomp (ZXdecomp_of_ZX zx))
    (ZXbd_of_decomp_stack zx) (ZXbd_of_decomp_biperm zx).

Lemma ZX_pe_graph_of_ZX_correct {n m} (zx : ZX n m) : 
  ZX_pe_graph_of_ZX zx ∝ zx.
Proof.
  unfold ZX_pe_graph_of_ZX.
  rewrite <- ZX_pe_graph_of_bd_correct.
  rewrite <- ZXbd_of_decomp_correct.
  apply ZXdecomp_of_ZX_correct.
Qed.


Lemma ZXbd_of_decomp_alt_stack {n m} (zx : ZX n m) : 
  ZXstack (ZXbd_of_decomp (ZXdecomp_of_ZX_alt zx)).(bd_spiders).
Proof.
  apply WF_ZXdecomp_of_ZX_alt.
Qed.

Lemma ZXbd_of_decomp_alt_biperm {n m} (zx : ZX n m) : 
  ZXbiperm (ZXbd_of_decomp (ZXdecomp_of_ZX_alt zx)).(bd_iobiperm).
Proof.
  cbn.
  pose proof (WF_ZXdecomp_of_ZX_alt zx) as [? ?].
  auto with zxbiperm_db zxperm_db.
Qed.

Definition ZX_pe_graph_of_ZX_alt {n m} (zx : ZX n m) : ZX_pe_graph n m :=
  ZX_pe_graph_of_bd (ZXbd_of_decomp (ZXdecomp_of_ZX_alt zx))
    (ZXbd_of_decomp_alt_stack zx) (ZXbd_of_decomp_alt_biperm zx).

Lemma ZX_pe_graph_of_ZX_alt_correct {n m} (zx : ZX n m) : 
  ZX_pe_graph_of_ZX_alt zx ∝ zx.
Proof.
  unfold ZX_pe_graph_of_ZX_alt.
  rewrite <- ZX_pe_graph_of_bd_correct.
  rewrite <- ZXbd_of_decomp_correct.
  apply ZXdecomp_of_ZX_alt_correct.
Qed.

Lemma ZX_pe_graph_of_ZX_permutation {n m} (zx : ZX n m) : 
  permutation (pe_edges (ZX_pe_graph_of_ZX zx) * 2)
    (pe_ioperm (ZX_pe_graph_of_ZX zx)).
Proof.
  apply pair_biperm_of_biperm_WF.
  eapply bipermutation_change_dims;
  [|apply biperm_of_zx_bipermutation].
  - rewrite <- pe_size_pf.
    cbn.  
    rewrite <- ZXstack_out_dims_spec by (apply ZXbd_of_decomp_stack).
    lia.
  - apply ZXbd_of_decomp_biperm.
Qed.

Lemma ZX_pe_graph_of_ZX_alt_permutation {n m} (zx : ZX n m) : 
  permutation (pe_edges (ZX_pe_graph_of_ZX_alt zx) * 2)
    (pe_ioperm (ZX_pe_graph_of_ZX_alt zx)).
Proof.
  apply pair_biperm_of_biperm_WF.
  eapply bipermutation_change_dims;
  [|apply biperm_of_zx_bipermutation].
  - rewrite <- pe_size_pf.
    cbn.  
    rewrite <- ZXstack_out_dims_spec by (apply ZXbd_of_decomp_alt_stack).
    lia.
  - apply ZXbd_of_decomp_alt_biperm.
Qed.

(* Lemma test : 
  ⊂ ↕ — ⟷ (— ↕ Z 2 1 1) ∝ Z 1 2 1.
Proof.
  (* prop_exists_nonzero 1%R.
  rewrite Mscale_1_l.
  prep_matrix_equivalence. 
  cbn.
  compute_matrix (Z_semantics 2 1 1).
  rewrite make_WF_equiv, Kronecker.kron_I_l, Kronecker.kron_I_r.
  by_cell; cbv; lca. *)

  etransitivity;
  [|etransitivity];
  [symmetry|..];
  [apply ZXdecomp_of_ZX_correct | | apply ZXdecomp_of_ZX_correct ].
  cbn.
  unfold zx_comm.
  rewrite 2!zx_of_perm_cast_id.
  unfold n_cup.
  cbn.
  rewrite !cast_id.
  unfold zx_of_perm.
  cbn.
  unfold zx_to_bot.
  cbn.
  rewrite !cast_id.
  rewrite !stack_empty_l, !stack_empty_r_fwd, !cast_id.
  rewrite !wire_removal_l.
  rewrite (ltac:(by_perm_eq_nosimpl; by_perm_cell; reflexivity) : 
    — ↕ — ∝ n_wire 2).
  rewrite !nwire_removal_l, !nwire_removal_r.
  apply compose_simplify; [reflexivity|].
  apply ZXbiperm_prop_by_biperm_eq;
  [auto 100 with zxbiperm_db zxperm_db..|].
  by_perm_cell; cbv. 
*)

Definition ZXbd_of_decomp_comp {n m} (zxd : ZXdecomp n m) : ZXbd n m :=
  {|
  bd_size := mid_size zxd;
  bd_spiders := spiders zxd;
  bd_iobiperm := iobiperm zxd ↕ n_wire m ⟷ n_cup_comp m
|}.

Lemma ZXbd_of_decomp_comp_eq {n m} (zxd : ZXdecomp n m) : 
  ZXbd_of_decomp_comp zxd = ZXbd_of_decomp zxd.
Proof.
  unfold ZXbd_of_decomp_comp.
  now rewrite n_cup_comp_eq.
Qed.


Lemma ZX_ve_graph_equiv_iff_raw {n m} (zxg zxg' : ZX_ve_graph n m) : 
  zxg ∝ zxg' <-> 
  cast _ _ (f_equal (fun k => k + n + m) (Nsum_constant_0' _)) 
    (eq_sym (Nat.mul_0_r _))
  (big_stack (fun _ => 0) zxg.(ve_deg)
    (fun k => b2ZX (zxg.(ve_color) k) _ _ (zxg.(ve_phase) k))
    zxg.(ve_numspi) ↕ n_wire n ↕ n_wire m ⟷
  zx_of_perm_cast _ _ 
      (perm_of_input_func (ve_edges zxg * 2) (ve_iofunc zxg)) zxg.(ve_size_pf)
    ⟷ (zxg.(ve_edges) ⇑ ⊃)) ∝
  cast _ _ (f_equal (fun k => k + n + m) (Nsum_constant_0' _)) 
    (eq_sym (Nat.mul_0_r _))
  (big_stack (fun _ => 0) zxg'.(ve_deg)
    (fun k => b2ZX (zxg'.(ve_color) k) _ _ (zxg'.(ve_phase) k))
    zxg'.(ve_numspi) ↕ n_wire n ↕ n_wire m ⟷
  zx_of_perm_cast _ _ 
    (perm_of_input_func (ve_edges zxg' * 2) (ve_iofunc zxg')) zxg'.(ve_size_pf)
  ⟷ (zxg'.(ve_edges) ⇑ ⊃)).
Proof.
  etransitivity; [apply ZX_pe_graph_equiv_iff_raw|].
  apply prop_iff_simplify; cast_irrelevance.
Qed.



Definition ZX_of_pe_graph_func n m edges numspi 
  deg color phase ioperm size_pf : ZX n m :=
  {|
    pe_edges := edges;
    pe_numspi := numspi;
    pe_deg := deg;
    pe_color := color;
    pe_phase := phase;
    pe_ioperm := ioperm;
    pe_size_pf := size_pf
  |}.

Definition pe_full_sizes_func numspi deg :=
  fun k => if k <? numspi then deg k else 1.


Lemma pe_full_sizes_func_sum n m numspi deg edges
  (size_pf : big_sum deg numspi + n + m = edges * 2) :
  big_sum (pe_full_sizes_func numspi deg) (numspi + n + m) = edges * 2.
Proof.
  apply (pe_full_sizes_sum
  (Build_ZX_pe_graph n m edges numspi deg (fun _ => false)
  (fun _ => R0) idn size_pf)).
Qed.

Lemma pe_full_sizes_func_eq_of_perm_eq numspi deg deg' : 
  perm_eq numspi deg deg' ->
  pe_full_sizes_func numspi deg = pe_full_sizes_func numspi deg'.
Proof.
  intros Hdeg.
  apply functional_extensionality.
  intros k.
  unfold pe_full_sizes_func.
  bdestruct_one;
  auto.
Qed.

Lemma ZX_of_pe_graph_func_indep_wrt
  n m edges numspi deg color phase ioperm ioperm' size_pf 
  (Hio : permutation (edges * 2) ioperm) 
  (Hio' : permutation (edges * 2) ioperm')
  (Hios : ioperm ~[/ (numspi + n + m) (pe_full_sizes_func numspi deg)] ioperm') :
  ZX_of_pe_graph_func n m edges numspi deg color phase ioperm size_pf ∝
  ZX_of_pe_graph_func n m edges numspi deg color phase ioperm' size_pf.
Proof.
  now apply ZX_pe_graph_simplify_indep_wrt.
Qed.

Add Parametric Morphism n m edges numspi deg color phase : 
  (ZX_of_pe_graph_func n m edges numspi deg color phase) with signature
  perm_eq (edges * 2) ==> eq ==> proportional as 
  ZX_of_pe_graph_func_ioperm_proper.
Proof.
  intros f g Hfg H.
  now apply ZX_pe_graph_simplify.
Qed.

Lemma ZX_of_pe_graph_func_absorb_conditional_swaps_r
  n m edges numspi deg color phase ioperm size_pf (cond : nat -> bool)
  (Hio : permutation (edges * 2) ioperm) :
  ZX_of_pe_graph_func n m edges numspi deg color phase 
    (ioperm ∘ big_stack_perms edges (fun _ => 2) 
      (fun k => if cond k then swap_2_perm else idn)) 
    size_pf ∝
  ZX_of_pe_graph_func n m edges numspi deg color phase ioperm size_pf.
Proof.
  apply (ZX_pe_graph_absorb_conditional_swap_r 
  (Build_ZX_pe_graph n m edges numspi deg color phase ioperm size_pf)
  cond), Hio.
Qed.

Lemma ZX_of_pe_graph_func_absorb_tensor_perms_r
  n m edges numspi deg color phase ioperm size_pf g
  (Hg : permutation edges g)
  (Hio : permutation (edges * 2) ioperm) :
  ZX_of_pe_graph_func n m edges numspi deg color phase 
    (ioperm ∘ tensor_perms edges 2 g idn) 
    size_pf ∝
  ZX_of_pe_graph_func n m edges numspi deg color phase ioperm size_pf.
Proof.
  rewrite <- (perm_inv'_perm_inv' _ g Hg).
  rewrite <- enlarge_permutation_constant.
  apply (ZX_pe_graph_absorb_edge_perm_r
  (Build_ZX_pe_graph n m edges numspi deg color phase ioperm size_pf));
  cbn; auto_perm.
Qed.

Lemma ZX_pe_to_pe_graph_func {n m} (zxp : ZX_pe_graph n m) : 
  @eq (ZX n m) zxp (ZX_of_pe_graph_func n m zxp.(pe_edges) zxp.(pe_numspi)
  zxp.(pe_deg) zxp.(pe_color) zxp.(pe_phase) zxp.(pe_ioperm) zxp.(pe_size_pf)).
Proof.
  reflexivity.
Qed.

Lemma ZX_pe_constructor_to_pe_graph_func n m edges numspi 
  deg color phase ioperm size_pf : 
  @eq (ZX n m) {|
    pe_edges := edges;
    pe_numspi := numspi;
    pe_deg := deg;
    pe_color := color;
    pe_phase := phase;
    pe_ioperm := ioperm;
    pe_size_pf := size_pf
  |} (ZX_of_pe_graph_func n m edges numspi deg color phase ioperm size_pf).
Proof.
  reflexivity.
Qed.


Lemma perm_of_input_func_compose_perm_r_zxp n m numspi deg edges f g
  (size_pf : big_sum deg numspi + n + m = edges * 2)
  (Hg : permutation (edges * 2) g) 
  (Hf : WF_input_func (edges * 2) (numspi + n + m) f) 
  (HWF : perm_eq (numspi + n + m)
    (count_func_vals (edges * 2) f)
    (pe_full_sizes_func numspi deg)) : 
  perm_of_input_func (edges * 2) (f ∘ g) 
  ~[/ (numspi + n + m) (pe_full_sizes_func numspi deg)]
  perm_of_input_func (edges * 2) f ∘ g.
Proof.
  erewrite perm_indep_wrt_dim_change_eq;
  [apply perm_of_input_func_compose_perm_r|];
  easy + auto with relations.
Qed.

Lemma ZX_ve_graph_simplify_degs {n m : nat} (zxv zxv' : ZX_ve_graph n m) :
  zxv.(ve_edges) = zxv'.(ve_edges) -> 
  zxv.(ve_numspi) = zxv'.(ve_numspi) ->
  perm_eq (zxv.(ve_numspi)) zxv.(ve_deg) zxv'.(ve_deg) -> 
  (forall k, k < zxv.(ve_numspi) -> 
    zxv.(ve_color) k = zxv'.(ve_color) k) -> 
  (forall k, k < zxv.(ve_numspi) -> 
    zxv.(ve_phase) k = zxv'.(ve_phase) k) -> 
  WF_input_func (zxv.(ve_edges) * 2) 
    (zxv.(ve_numspi) + n + m) zxv.(ve_iofunc) ->
  WF_input_func (zxv'.(ve_edges) * 2) 
    (zxv'.(ve_numspi) + n + m) zxv'.(ve_iofunc) ->
  perm_eq (ve_numspi zxv + n + m)
    (count_func_vals (ve_edges zxv * 2) (ve_iofunc zxv)) 
    (pe_full_sizes zxv) ->
  perm_deg_eq (zxv.(ve_numspi) + n + m)
    (deg_of_edgefunc (zxv.(ve_edges)) (edgefunc_of_infunc zxv.(ve_iofunc))) 
    (deg_of_edgefunc (zxv'.(ve_edges)) (edgefunc_of_infunc zxv'.(ve_iofunc))) ->
  zxv ∝ zxv'.
Proof.
  destruct zxv as [edges numspi deg color phase iofunc Hsize];
  destruct zxv' as [edges' numspi' deg' color' phase' iofunc' Hsize'];
  cbn [ve_edges ve_numspi ve_deg ve_color ve_phase ve_iofunc].
  change (pe_full_sizes _) with (pe_full_sizes_func numspi deg).
  intros <- <- Hdeg Hcol Hphase HWF HWF' HWFsize Hiodeg.
  rewrite (pe_full_sizes_func_eq_of_perm_eq _ _ _ Hdeg) in HWFsize.
  apply deg_of_edgefunc_eq_permutation_witness in Hiodeg;
  [|now apply edgefunc_of_infunc_WF..].
  destruct Hiodeg as (h & Hh & HhWF & Heq).
  symmetry in Heq.
  apply infunc_of_edgefunc_perm_edge_eq in Heq.
  rewrite infunc_of_edgefunc_compose_r in Heq.
  rewrite 2!infunc_of_edgefunc_of_infunc in Heq.
  cbv [ZX_pe_of_ve_graph 
    ve_edges ve_numspi ve_deg ve_color ve_phase ve_iofunc
    ve_size_pf].
  rewrite 2!ZX_pe_constructor_to_pe_graph_func.
  rewrite Heq.
  rewrite Combinators.compose_assoc.
  symmetry.
  erewrite ZX_of_pe_graph_func_indep_wrt;
  [..|apply perm_of_input_func_compose_perm_r_zxp];
  [|now auto_perm..].
  rewrite <- Combinators.compose_assoc.
  rewrite ZX_of_pe_graph_func_absorb_conditional_swaps_r by auto_perm.
  rewrite ZX_of_pe_graph_func_absorb_tensor_perms_r by auto_perm.
  symmetry.
  now apply ZX_pe_graph_simplify.
Qed.



Lemma ZX_pe_graph_simplify_degs {n m} (zxp zxp' : ZX_pe_graph n m) 
  (Hzxp : permutation (zxp.(pe_edges) * 2) zxp.(pe_ioperm))
  (Hzxp' : permutation (zxp'.(pe_edges) * 2) zxp'.(pe_ioperm)) :
  zxp.(pe_edges) = zxp'.(pe_edges) -> 
  zxp.(pe_numspi) = zxp'.(pe_numspi) ->
  perm_eq (zxp.(pe_numspi)) zxp.(pe_deg) zxp'.(pe_deg) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_color) k = zxp'.(pe_color) k) -> 
  (forall k, k < zxp.(pe_numspi) -> 
    zxp.(pe_phase) k = zxp'.(pe_phase) k) -> 
  perm_deg_eq (pe_numspi zxp + n + m)
  (deg_of_edgefunc (pe_edges zxp)
     (edgefunc_of_infunc
        (Nsum_index (pe_numspi zxp + n + m)
           (pe_full_sizes zxp)
         ∘ pe_ioperm zxp)))
  (deg_of_edgefunc (pe_edges zxp)
     (edgefunc_of_infunc
        (Nsum_index
           (pe_numspi zxp + n + m)
           (pe_full_sizes zxp)
         ∘ pe_ioperm zxp'))) ->
  zxp ∝ zxp'.
Proof.
  intros Hedge Hspi Hdeg Hcol Hphase Hiodeg.
  rewrite <- ZX_ve_of_pe_graph_correct, <- (ZX_ve_of_pe_graph_correct zxp')
    by auto.
  apply ZX_ve_graph_simplify_degs; try easy;
  cbn [ve_numspi ZX_ve_of_pe_graph ve_iofunc ve_edges].
  - rewrite <- pe_full_sizes_sum.
    apply compose_Nsum_index_l_WF_input_func.
  - rewrite <- pe_full_sizes_sum.
    apply compose_Nsum_index_l_WF_input_func.
  - now apply WF_ZX_ve_of_pe_graph.
  - change (pe_full_sizes zxp') with 
      (pe_full_sizes_func zxp'.(pe_numspi) zxp'.(pe_deg)).
    rewrite <- Hedge, <- Hspi.
    erewrite <- (pe_full_sizes_func_eq_of_perm_eq _ _ _ Hdeg).
    exact Hiodeg.
Qed.






Definition ZX_of_edge_list edges (f : nat -> nat * nat) : 
  ZX (edges * 2) 0 :=
  

Definition ZX_of_edge_list n m numspi 

Record ZX_el_graph := {
  el_numspi ZX_ve_graph
}.























Ltac reflexivity_no_check :=
  match goal with
  |- ?A = ?B => 
    exact_no_check (@eq_refl _ A)
  end.

Lemma test : 
  ⊂ ⟷ (— ↕ Z 1 1 1) ∝ Z 0 2 1.
Proof.
  etransitivity;
  [|etransitivity];
  [symmetry|..];
  [apply ZX_pe_graph_of_ZX_alt_correct | 
  | apply ZX_pe_graph_of_ZX_alt_correct ].
  apply ZX_pe_graph_simplify_degs;
  [apply ZX_pe_graph_of_ZX_alt_permutation|
  apply ZX_pe_graph_of_ZX_alt_permutation|..];
  change (pe_numspi (ZX_pe_graph_of_ZX_alt (⊂ ⟷ (— ↕ Z 1 1 1))))
    with 1;
  change (pe_edges (ZX_pe_graph_of_ZX_alt (⊂ ⟷ (— ↕ Z 1 1 1)))) with 2.
  reflexivity.
  reflexivity.
  by_perm_cell; reflexivity.
  by_perm_cell; reflexivity.
  by_perm_cell; reflexivity.

  unfold ZX_pe_graph_of_ZX_alt.
  cbn [pe_ioperm ZX_pe_graph_of_bd].
  (* cbn [Nat.add Nat.div Nat.divmod fst]. *)
  generalize (ZXbd_of_decomp_alt_stack (⊂ ⟷ (— ↕ Z 1 1 1))).
  generalize (ZXbd_of_decomp_alt_biperm (⊂ ⟷ (— ↕ Z 1 1 1))).
  pattern (ZXdecomp_of_ZX_alt (⊂ ⟷ (— ↕ Z 1 1 1))).
  rewrite <- ZXdecomp_of_ZX_alt_comp_eq.
  rewrite <- ZXbd_of_decomp_comp_eq.
  intros ? ?.
  change (1 + 0 + (1 + 1)) with 3.
  change ((_ + _) / _) with 2.
  rewrite <- ZXbd_of_decomp_comp_eq, <- ZXdecomp_of_ZX_alt_comp_eq.
  apply perm_deg_eqb_eq.
  (* reflexivity_no_check. *)
  reflexivity.
Qed.


Lemma test2 : 
  ⊂ ↕ — ⟷ (— ↕ Z 2 1 1) ∝ Z 1 2 1.
Proof.
  etransitivity;
  [|etransitivity];
  [symmetry|..];
  [apply ZX_pe_graph_of_ZX_alt_correct | 
  | apply ZX_pe_graph_of_ZX_alt_correct ].
  apply ZX_pe_graph_simplify_degs;
  [apply ZX_pe_graph_of_ZX_alt_permutation|
  apply ZX_pe_graph_of_ZX_alt_permutation|..];
  change (pe_numspi (ZX_pe_graph_of_ZX_alt (⊂ ↕ — ⟷ (— ↕ Z 2 1 1))))
    with 1;
  change (pe_edges (ZX_pe_graph_of_ZX_alt (⊂ ↕ — ⟷ (— ↕ Z 2 1 1)))) with 3.
  reflexivity.
  reflexivity.
  by_perm_cell; reflexivity.
  by_perm_cell; reflexivity.
  by_perm_cell; reflexivity.

  unfold ZX_pe_graph_of_ZX_alt.
  cbn [pe_ioperm ZX_pe_graph_of_bd].
  (* cbn [Nat.add Nat.div Nat.divmod fst]. *)
  generalize (ZXbd_of_decomp_alt_stack (⊂ ↕ — ⟷ (— ↕ Z 2 1 1))).
  generalize (ZXbd_of_decomp_alt_biperm (⊂ ↕ — ⟷ (— ↕ Z 2 1 1))).
  pattern (ZXdecomp_of_ZX_alt (⊂ ↕ — ⟷ (— ↕ Z 2 1 1))).
  rewrite <- ZXdecomp_of_ZX_alt_comp_eq.
  rewrite <- ZXbd_of_decomp_comp_eq.
  intros ? ?.
  rewrite <- ZXbd_of_decomp_comp_eq, <- ZXdecomp_of_ZX_alt_comp_eq.
  apply perm_deg_eqb_eq.
  reflexivity.
Qed.










Record ZX_vd_graph {n m : nat} : Set := {
  vd_numspi : nat;
  vd_deg : nat * nat -> nat;
  vd_color : nat -> bool;
  vd_phase : nat -> R;
  vd_deg_symm : deg_symm (vd_numspi + n + m) vd_deg;
  vd_WF : forall k, k < n + m ->
    big_sum (fun l => vd_deg (l, vd_numspi + k)) vd_numspi = 1
}.

Arguments ZX_vd_graph (_ _) : clear implicits.

Local Obligation Tactic := idtac.

Program Definition ZX_ve_of_vd_graph {n m} (zxd : ZX_vd_graph n m) : 
  ZX_ve_graph n m := 
  let knm := zxd.(vd_numspi) + n + m in 
  {|
  ve_edges := big_sum (zxd.(vd_deg) ∘ sidx_to_edge knm) ((knm + 1) * knm / 2);
  ve_numspi := zxd.(vd_numspi);
  ve_deg := fun k => big_sum (fun l => zxd.(vd_deg) (k, l)) knm 
    + zxd.(vd_deg) (k, k);
  ve_color := zxd.(vd_color);
  ve_phase := zxd.(vd_phase);
  ve_iofunc := 
    infunc_of_edgefunc (edgefunc_of_deg knm zxd.(vd_deg));
|}.
Next Obligation.
  intros n m zxd.
  set (knm := zxd.(vd_numspi) + n + m).
  cbn zeta.
  rewrite Nsum_plus.
  rewrite <- triangle_number'.
  rewrite big_sum_Nsum.
  Abort.




(* Lemma biperm_of_pair_biperm_succ_arb_cap n (f : pair_biperm (S n)) : 
  perm_eq (S n + S n) (biperm_of_pair_biperm f)
  () *)
  
  
  











Definition stack_pair_biperms {n m} (f : pair_biperm n) (g : pair_biperm m) : 
  pair_biperm (n + m) := stack_perms (n * 2) (m * 2) f g.

Lemma stack_pair_biperms_WF {n m} (f : pair_biperm n) (g : pair_biperm m)
  (Hf : WF_pair_biperm f) (Hg : WF_pair_biperm g) : 
  WF_pair_biperm (stack_pair_biperms f g).
Proof.
  unfold WF_pair_biperm, stack_pair_biperms.
  auto_perm.
Qed.

(* Lemma ZX_of_stack_pair_biperms {n m} (f : pair_biperm n) (g : pair_biperm m)
  (Hf : WF_pair_biperm f) (Hg : WF_pair_biperm g) : 
  ZX_of_pair_biperm (stack_pair_biperms f g) ∝ *)




  









Definition sort_ioperm_micro edges f : nat -> nat :=
  f ∘ big_stack_perms edges (fun _ => 2) 
    (fun k => if f (2 * k + 1) <? f (2 * k) then swap_2_perm else idn).

(* Lemma micro_sorted_decomp edges f (Hf : permutation (edges * 2))

Definition sort_ioperm_macro edges f : nat -> nat := 
  f ∘ tensor_perm edges 2 
  () idn *)













(* The subset of ZX diagrams forming the CCC structure
  (or, ZX-Cap/Cup) *)
  Inductive ZXCC : forall n m : nat, Set :=
  | CCEmpty : ZXCC 0 0
  | CCWire : ZXCC 1 1 
  | CCSwap : ZXCC 2 2
  | CCCap : ZXCC 2 0
  | CCCup : ZXCC 0 2
  | CCCompose {n m o} (zxc0 : ZXCC n m) (zxc1 : ZXCC m o) : ZXCC n o
  | CCStack {n0 m0 n1 m1} 
    (zxc0 : ZXCC n0 m0) (zxc1 : ZXCC n1 m1) : ZXCC (n0 + n1) (m0 + m1).

Fixpoint ZXCC_to_ZX {n m} (zxc : ZXCC n m) : ZX n m :=
  match zxc with
  | CCEmpty => Empty
  | CCWire => Wire
  | CCSwap => Swap
  | CCCap => Cap
  | CCCup => Cup
  | CCCompose zxc0 zxc1 => ZXCC_to_ZX zxc0 ⟷ ZXCC_to_ZX zxc1
  | CCStack zxc0 zxc1 => ZXCC_to_ZX zxc0 ↕ ZXCC_to_ZX zxc1
  end.

Coercion ZXCC_to_ZX : ZXCC >-> ZX.

Lemma ZXCC_biperm {n m} (zxc : ZXCC n m) : ZXbiperm zxc.
Proof.
  induction zxc; cbn; auto with zxbiperm_db.
Defined.
Opaque ZXCC_biperm.

Lemma ZXCC_biperm_t {n m} (zxc : ZXCC n m) : ZXbiperm_t zxc.
Proof.
  induction zxc; cbn; now constructor. 
Defined.

Fixpoint ZXCC_of_ZXbiperm_t {n m} (zx : ZX n m) (Hzx : ZXbiperm_t zx) 
  : ZXCC n m := 
  match Hzx with
  | BipermEmpty_t => CCEmpty
  | BipermWire_t => CCWire
  | BipermSwap_t => CCSwap
  | BipermCap_t => CCCap
  | BipermCup_t => CCCup
  | BipermStack_t zx0 zx1 Hzx0 Hzx1 => CCStack
    (ZXCC_of_ZXbiperm_t zx0 Hzx0) (ZXCC_of_ZXbiperm_t zx1 Hzx1)
  | BipermComp_t zx0 zx1 Hzx0 Hzx1 => CCCompose
    (ZXCC_of_ZXbiperm_t zx0 Hzx0) (ZXCC_of_ZXbiperm_t zx1 Hzx1)
  end.


Definition ZXCC_of_ZXbiperm {n m} (zx : ZX n m) (Hzx : ZXbiperm zx) 
  : ZXCC n m := ZXCC_of_ZXbiperm_t zx (ZXbiperm_t_of_ZXbiperm zx Hzx).

Lemma ZX_of_ZXCC_of_ZXbiperm {n m} (zx : ZX n m) (Hzx : ZXbiperm zx) :
  zx = ZXCC_of_ZXbiperm zx Hzx.
Proof.
  unfold ZXCC_of_ZXbiperm.
  generalize (ZXbiperm_t_of_ZXbiperm zx Hzx).
  clear Hzx.
  intros Hzx.
  induction Hzx; cbn; now f_equal.
Qed.

Lemma ZXCC_of_ZXbiperm_t_of_ZXCC {n m} (zxc : ZXCC n m) : 
  zxc = ZXCC_of_ZXbiperm_t zxc (ZXCC_biperm_t zxc).
Proof.
  induction zxc; cbn; now f_equal.
Qed.


(* Spider stack diagrams *)
Inductive ZXSS : forall (n : nat), Set :=
  | SSX_Spider n (α : R) : ZXSS n
  | SSZ_Spider n (α : R) : ZXSS n
  | SSStack {n m} (zxs0 : ZXSS n) (zxs1 : ZXSS m) : ZXSS (n + m).

Fixpoint ZXSS_to_ZX {n} (zxs : ZXSS n) : ZX 0 n :=
  match zxs with 
  | SSX_Spider n α => X 0 n α
  | SSZ_Spider n α => Z 0 n α
  | SSStack zxs0 zxs1 => ZXSS_to_ZX zxs0 ↕ ZXSS_to_ZX zxs1
  end.

Coercion ZXSS_to_ZX : ZXSS >-> ZX.



Inductive ZXSSCC : forall (n m : nat), Set :=
  | ZX_SS_CC {n m k} (zxs : ZXSS k) (zxc : ZXCC (k + n) m) : ZXSSCC n m.

Definition ZX_of_ZXSSCC {n m} (zxsc : ZXSSCC n m) : ZX n m :=
  match zxsc in ZXSSCC n' m' return ZX n' m' with
  | @ZX_SS_CC n m k zxs zxc =>
    zxs ↕ n_wire n ⟷ zxc
  end.

Coercion ZX_of_ZXSSCC : ZXSSCC >-> ZX.

(* Definition ZXSSCC_Compose {n m o} 
  (zxsc0 : ZXSSCC n m) (zxsc1 : ZXSSCC m o) : ZXSSCC n o.
Proof.
  destruct zxsc0 as [n m k zxs0 zxc0].
  destruct zxsc1 as [m o l zxs1 zxc1].
  apply (ZX_SS_CC (SSStack zxs0 zxs1)). *)




