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


(* Lemma compose_ZX_vert_alt {n m o} (zx0 : ZXvert n m) (zx1 : ZXvert m o) :
  compose_ZX_vert zx0 zx1 ∝ n_cap_mid n m o ⟷ stack_ZX_vert zx0 zx1. *)

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




Lemma ZX_of_perm_func_pf {n m numspi} : 
  n + m = big_sum (fun _ => 0) numspi + n + m.
Proof. rewrite <- Nsum_constant_0'. reflexivity. Qed.

Definition ZX_of_infunc edges (f : nat -> nat) : 
  ZX (edges * 2) 0 :=
  cast _ _ eq_refl (eq_sym (Nat.mul_0_r edges)) 
  (zx_of_perm _ f ⟷ n_stack edges ⊃).

Definition ZX_of_stack_uncast n m numspi (deg : nat -> nat)
  (phase : nat -> R) (color : nat -> bool) : 
  ZX (n + m) (big_sum deg numspi + n + m) := 
  cast (n + m) _ ZX_of_perm_func_pf eq_refl (
    big_stack (fun _ => 0) deg 
      (fun k => b2ZX (color k) 0 (deg k) (phase k)) numspi
      ↕ n_wire n ↕ n_wire m).

Definition ZX_of_stack n m numspi (deg : nat -> nat)
  (phase : nat -> R) (color : nat -> bool) edges 
  (size_pf : big_sum deg numspi + n + m = edges * 2) : 
  ZX (n + m) (edges * 2) := 
  cast (n + m) _ ZX_of_perm_func_pf (eq_sym size_pf) (
    big_stack (fun _ => 0) deg 
      (fun k => b2ZX (color k) 0 (deg k) (phase k)) numspi
      ↕ n_wire n ↕ n_wire m).

Lemma ZX_of_stack_eq_cast_uncast n m numspi deg phase color edges size_pf : 
  ZX_of_stack n m numspi deg phase color edges size_pf = 
  cast _ _ eq_refl (eq_sym size_pf) 
    (ZX_of_stack_uncast n m numspi deg phase color).
Proof.
  unfold ZX_of_stack_uncast.
  rewrite cast_contract_eq.
  apply cast_simplify_eq.
  reflexivity.
Qed.

Definition ZX_of_infunc_data n m numspi (deg : nat -> nat)
  (phase : nat -> R) (color : nat -> bool) edges 
  (size_pf : big_sum deg numspi + n + m = edges * 2)
  (f : nat -> nat) : 
  ZX (n + m) 0 :=
   ZX_of_stack n m numspi deg phase color edges size_pf 
   ⟷ ZX_of_infunc edges f.

Definition ZX_of_edgeperm edges (f : nat -> nat * nat) : ZX (edges * 2) 0 :=
  ZX_of_infunc edges (infunc_of_edgefunc f).

Definition ZX_of_edgeperm_data n m numspi (deg : nat -> nat)
  (phase : nat -> R) (color : nat -> bool) edges 
  (size_pf : big_sum deg numspi + n + m = edges * 2)
  (f : nat -> nat * nat) : 
  ZX (n + m) 0 :=
  ZX_of_infunc_data n m numspi deg phase color 
    edges size_pf (infunc_of_edgefunc f).


Definition infunc_equiv_upto_ZX n m numspi (deg : nat -> nat) 
  (f g : nat -> nat) : Prop :=
  forall edges phase color (Hedges : big_sum deg numspi + n + m = edges * 2),
  ZX_of_infunc_data n m numspi deg phase color edges Hedges f ∝
  ZX_of_infunc_data n m numspi deg phase color edges Hedges g.

Definition edgeperm_equiv_upto_ZX n m numspi (deg : nat -> nat) 
  (f g : nat -> nat * nat) : Prop :=
  forall edges phase color (Hedges : big_sum deg numspi + n + m = edges * 2),
  ZX_of_edgeperm_data n m numspi deg phase color edges Hedges f ∝
  ZX_of_edgeperm_data n m numspi deg phase color edges Hedges g.



Lemma zx_arb_cup_transpose k l n : 
  (zx_arb_cup k l n) ⊤ ∝
  zx_arb_cap k l n.
Proof.
  apply Proportional.transpose_involutive.
Qed.

Lemma contract_biperm_perm_eq_of_perm_eq n f g k l 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) (Hfg : perm_eq n f g) :
  perm_eq (n - 2) (contract_biperm k l f) (contract_biperm k l g).
Proof.
  unfold contract_biperm.
  replace (n - 2) with (n - 1 - 1) by (clear; lia). 
  bdestruct (k <? l).
  - erewrite contract_perm_perm_eq_of_perm_eq by
      (lia||apply (contract_perm_perm_eq_of_perm_eq n f g); auto_perm).
    reflexivity.
  - erewrite contract_perm_perm_eq_of_perm_eq by
      (lia||apply (contract_perm_perm_eq_of_perm_eq n f g); auto_perm).
    reflexivity.
Qed.

Local Add Parametric Morphism k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) :
  (contract_biperm k l) with signature perm_eq n ==> perm_eq (n - 2)
  as contract_biperm_proper.
Proof.
  intros; apply contract_biperm_perm_eq_of_perm_eq; auto.
Qed.

Lemma zx_arb_cup_compose_zx_of_perm_r
  (n : nat) (f : nat -> nat) (k l : nat)
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) 
  (Hf : permutation n f) : 
  zx_arb_cup k l n ⟷ zx_of_perm n f ∝ 
  zx_of_perm (n - 2) (contract_biperm (perm_inv n f k) (perm_inv n f l) f) 
  ⟷ zx_arb_cup (perm_inv n f k) (perm_inv n f l) n.
Proof.
  apply transpose_diagrams.
  cbn [ZXCore.transpose].
  rewrite zx_of_perm_transpose by auto.
  rewrite 2!zx_arb_cup_transpose.
  rewrite zx_arb_cap_compose_zx_of_perm_l by auto_perm.
  assert (perm_inv n f k <> perm_inv n f l) by 
    (apply (@permutation_neq n); auto_perm).
  rewrite zx_of_perm_transpose by auto_perm.
  rewrite (zx_of_perm_eq_of_perm_eq _ _ _ (perm_inv'_eq _ _)).
  rewrite contract_biperm_inv by 
    (try apply (@permutation_neq n); auto_perm).
  rewrite 2!perm_inv_is_rinv_of_permutation by auto_perm.
  rewrite 2!perm_inv'_eq by auto.
  erewrite zx_of_perm_eq_of_perm_eq;
  [|erewrite contract_biperm_perm_eq_of_perm_eq; [..|apply perm_inv'_eq];
    [reflexivity|auto..]].
  reflexivity.
Qed.


(* compose_zx_arb_cap_n_stacked_cups *)

Lemma zx_arb_cap_transpose k l n : 
  (zx_arb_cap k l n) ⊤ ∝
  zx_arb_cup k l n.
Proof. reflexivity. Qed.

Lemma mul_0_r_eq {n m} : n * 0 = m * 0.
Proof. lia. Qed.

Lemma comp_zx_cap_n_stack_prf {n} : n * 2 - 2 - 2 = (n - 2) * 2.
Proof. lia. Qed.

Lemma compose_zx_arb_cap_n_stack_cups n k l 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) : 
  n ⇑ ⊂ ⟷ zx_arb_cap k l (n * 2) ∝
  if k / 2 =? l / 2 then 
    cast _ _ mul_0_r_eq 
      (eq_sym (Nat.mul_sub_distr_r n 1 2)) ((n - 1) ⇑ ⊂)
  else
    cast _ _ mul_0_r_eq comp_zx_cap_n_stack_prf ((n - 2) ⇑ ⊂) ⟷  
    zx_arb_cup (2 * (min k l / 2)) 
      (2 * (max k l / 2) - 1) _.
Proof.
  pose proof 
    (compose_zx_arb_cap_n_stacked_cups k l n 
    ltac:(lia) ltac:(lia) Hkl) as Hequiv.
  revert Hequiv.
  unfold n_stacked_cups.
  rewrite cast_compose_l, cast_zx_arb_cap_natural_l.
  rewrite cast_compose_r_eq_mid, cast_contract_eq.
  rewrite cast_backwards_fwd.
  intros ->.
  bdestruct_one.
  - rewrite 2!cast_contract_eq.
    apply cast_simplify; reflexivity.
  - rewrite cast_contract_eq. 
    rewrite cast_compose_distribute.
    apply compose_simplify_casted_abs; 
      [lia| |].
    + intros ?.
      rewrite 2!cast_contract_eq.
      cast_irrelevance.
    + intros ?.
      apply transpose_diagrams.
      rewrite 2!cast_transpose.
      rewrite 2!zx_arb_cup_transpose.
      rewrite cast_zx_arb_cap_natural_l.
      cast_irrelevance.
Qed.


Lemma compose_arb_cup_n_stack_caps n k l 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) : 
  zx_arb_cup k l (n * 2) ⟷ n ⇑ ⊃ ∝
  if k / 2 =? l / 2 then 
    cast _ _ (eq_sym (Nat.mul_sub_distr_r n 1 2)) 
      mul_0_r_eq ((n - 1) ⇑ ⊃)
  else
    zx_arb_cap (2 * (min k l / 2)) 
      (2 * (max k l / 2) - 1) _
    ⟷ cast _ _ comp_zx_cap_n_stack_prf mul_0_r_eq ((n - 2) ⇑ ⊃).
Proof.
  apply transpose_diagrams.
  cbn [ZXCore.transpose].
  rewrite n_stack_transpose, zx_arb_cup_transpose.
  rewrite compose_zx_arb_cap_n_stack_cups by auto.
  bdestruct_one.
  - rewrite cast_transpose, n_stack_transpose.
    cast_irrelevance.
  - cbn [ZXCore.transpose].
    rewrite zx_arb_cap_transpose, cast_transpose, n_stack_transpose.
    apply compose_simplify; [cast_irrelevance|reflexivity].
Qed.

Lemma min_div n m k : min n m / k = min (n / k) (m / k). 
Proof.
  assert (Hor : n <= m \/ m <= n) by lia.
  by_symmetry Hor 
    by (intros ? ?; rewrite Nat.min_comm; intros ->; apply Nat.min_comm).
  rewrite Nat.min_l by auto.
  symmetry.
  apply Nat.min_l.
  apply Nat.Div0.div_le_mono; auto.
Qed.

Lemma max_div n m k : max n m / k = max (n / k) (m / k). 
Proof.
  assert (Hor : n <= m \/ m <= n) by lia.
  by_symmetry Hor 
    by (intros ? ?; rewrite Nat.max_comm; intros ->; apply Nat.max_comm).
  rewrite Nat.max_r by auto.
  symmetry.
  apply Nat.max_r.
  apply Nat.Div0.div_le_mono; auto.
Qed.

Lemma ZX_of_infunc_absorb_subswaps_r n f (g : nat -> (nat -> nat)) 
  (Hf : permutation (n * 2) f) 
  (Hg : forall k, k < n -> permutation 2 (g k)) :
  ZX_of_infunc n (f ∘ big_stack_perms n (fun _ => 2) g) ∝
  ZX_of_infunc n f.
Proof.
  unfold ZX_of_infunc.
  rewrite <- compose_zx_of_perm by auto_perm.
  rewrite cast_backwards_fwd, cast_contract_eq, cast_id.
  rewrite compose_assoc.
  apply compose_simplify_r.
  rewrite n_stack_to_big_stack, cast_compose_r.
  rewrite cast_zx_of_perm_natural_r, cast_compose_l_eq_mid, cast_contract_eq.
  rewrite zx_of_big_stack_perms by auto_perm.
  rewrite big_stack_compose.
  apply cast_simplify.
  apply big_stack_simplify.
  intros k Hk.
  specialize (Hg k Hk).
  apply permutation_2_case in Hg.
  destruct Hg as [Hg | Hg]; rewrite Hg.
  - rewrite zx_of_perm_idn, nwire_removal_l.
    reflexivity.
  - rewrite zx_of_swap_2_perm, cap_swap_absorbtion.
    reflexivity.
Qed.


Lemma ZX_of_infunc_absorb_conditional_swaps_r n f (g : nat -> bool) 
  (Hf : permutation (n * 2) f) :
  ZX_of_infunc n (f ∘ big_stack_perms n (fun _ => 2) 
  (fun i => if g i then swap_2_perm else idn)) ∝
  ZX_of_infunc n f.
Proof.
  apply ZX_of_infunc_absorb_subswaps_r; auto_perm.
Qed.

Lemma ZX_of_infunc_simplify n f g (Hfg : perm_eq (n * 2) f g) : 
  ZX_of_infunc n f ∝ ZX_of_infunc n g.
Proof.
  unfold ZX_of_infunc.
  rewrite Hfg.
  reflexivity.
Qed.

Lemma ZX_of_infunc_edgeperm_eq_simplify n f g (Hf : permutation (n * 2) f) 
  (Hfg : forall k, k < n -> 
    edge_eq (f (2 * k), f (2 * k + 1)) (g (2 * k), g (2 * k + 1))) : 
  ZX_of_infunc n f ∝ ZX_of_infunc n g.
Proof.
  transitivity
    (ZX_of_infunc n (f ∘
    big_stack_perms n (fun _ => 2) (fun k => 
      if f (2 * k) =? g (2 * k) then idn else swap_2_perm))).
  - rewrite ZX_of_infunc_absorb_subswaps_r by auto_perm.
    reflexivity.
  - apply ZX_of_infunc_simplify.
    rewrite big_stack_perms_constant_alt.
    intros k Hk.
    unfold compose.
    rewrite dist_if.
    specialize (Hfg (k / 2) ltac:(dmlia)).
    cbv delta [edge_eq fst snd] beta match in Hfg.
    assert (k mod 2 < 2) as Hk2 by (clear; dmlia).
    bdestruct_one.
    + bdestruct (k mod 2 =? 0).
      * replace -> (k mod 2).
        rewrite Nat.add_0_r, Nat.mul_comm.
        replace -> (f (2 * (k / 2))).
        f_equal.
        pose proof (Nat.div_mod_eq k 2).
        lia.
      * assert (k mod 2 = 1) by lia.
        replace -> (k mod 2).
        rewrite Nat.mul_comm.
        assert (f (2 * (k / 2) + 1) = g (2 * (k / 2) + 1)) as Hrw by lia.
        rewrite Hrw.
        f_equal.
        pose proof (Nat.div_mod_eq k 2).
        lia.
    + bdestruct (k mod 2 =? 0).
      * replace -> (k mod 2).
        cbn -[Nat.divmod Nat.div].
        rewrite Nat.mul_comm.
        enough (g (2 * (k / 2)) = g k) by lia.
        f_equal.
        pose proof (Nat.div_mod_eq k 2).
        lia.
      * assert (k mod 2 = 1) by lia.
        replace -> (k mod 2).
        cbn -[Nat.divmod Nat.div].
        rewrite Nat.mul_comm, Nat.add_0_r.
        enough (g (2 * (k / 2) + 1) = g k) by lia.
        f_equal.
        pose proof (Nat.div_mod_eq k 2).
        lia.
Qed.

Lemma ZX_of_infunc_edgeperm_eq_simplify' n f g (Hf : permutation (n * 2) f) 
  (Hfg : perm_edge_eq n (edgefunc_of_infunc f) (edgefunc_of_infunc g)) : 
  ZX_of_infunc n f ∝ ZX_of_infunc n g.
Proof.
  apply ZX_of_infunc_edgeperm_eq_simplify.
  - auto.
  - intros k.
    rewrite (Nat.mul_comm 2).
    apply Hfg.
Qed.


Definition parswap n :=
  2 * (n / 2) + (1 - (n mod 2)).

Lemma parswap_defn n : 
  parswap n = if Nat.even n then n + 1 else n - 1.
Proof.
  unfold parswap.
  rewrite even_eqb.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)).
  pose proof (Nat.div_mod_eq n 2).
  bdestruct_one;
  lia.
Qed.

Lemma parswap_defn' n : 
  parswap n = if Nat.even n then S n else n - 1.
Proof.
  rewrite parswap_defn; bdestruct_one; lia.
Qed.

Lemma parswap_lt_double_iff a n : 
  parswap a < n + n <-> a < n + n.
Proof.
  rewrite parswap_defn', even_eqb.
  bdestruct_one; split; try lia.
  - apply succ_even_lt_even; [|apply even_add_same].
    rewrite even_eqb, Nat.eqb_eq; auto.
  - assert (a <> 0) by (intros ->; easy).
    replace a with (S (a - 1)) at 2 by lia.
    apply succ_even_lt_even; [|apply even_add_same].
    rewrite Nat.even_sub by lia.
    simpl.
    rewrite even_eqb.
    bdestruct_one; easy.
Qed.

Lemma parswap_lt_twice_iff a n : 
  parswap a < n * 2 <-> a < n * 2.
Proof.
  replace (n * 2) with (n + n) by lia.
  apply parswap_lt_double_iff.
Qed.

Lemma parswap_neq n : parswap n <> n.
Proof.
  rewrite parswap_defn, even_eqb.
  bdestruct_one; [lia|].
  assert (n <> 0) by (intros ->; easy).
  lia.
Qed.

Lemma even_parswap n : Nat.even (parswap n) = ¬ Nat.even n.
Proof.
  rewrite parswap_defn, (even_eqb n).
  bdestruct_one.
  - rewrite Nat.even_add, even_eqb.
    bdestruct_one; easy.
  - assert (n <> 0) by (intros ->; easy).
    rewrite Nat.even_sub, even_eqb by lia.
    bdestruct_one; easy.
Qed.

Lemma odd_parswap n : Nat.odd (parswap n) = ¬ Nat.odd n.
Proof.
  rewrite <- Nat.negb_even, even_parswap, Nat.negb_even.
  reflexivity.
Qed.

Lemma parswap_involutive n : parswap (parswap n) = n.
Proof.
  rewrite parswap_defn.
  rewrite even_parswap, negb_if.
  rewrite parswap_defn, even_eqb.
  bdestruct_one; [lia|].
  assert (n <> 0) by (intros ->; easy).
  lia.
Qed.

#[export]
Hint Resolve <- parswap_lt_twice_iff : perm_bounded_db.

Definition infunc_partner n f k :=
  f (parswap (perm_inv (n * 2) f k)).

Lemma infunc_partner_biperm n f (Hf : permutation (n * 2) f) :
  bipermutation (n * 2 + 0) (infunc_partner n f).
Proof.
  apply bipermutation_defn; repeat split.
  - rewrite Nat.add_0_r. 
    intros k Hk.
    unfold infunc_partner.
    auto_perm.
  - intros k Hk.
    unfold infunc_partner.
    symmetry.
    rewrite <- (perm_inv_eq_iff Hf) by auto_perm.
    symmetry.
    apply parswap_neq.
  - intros k Hk.
    simpl.
    unfold compose, infunc_partner.
    rewrite perm_inv_is_linv_of_permutation by auto_perm.
    rewrite parswap_involutive.
    auto_perm.
Qed.

#[export]
Hint Resolve infunc_partner_biperm : biperm_db.

Definition permute_infunc n (f : nat -> nat) g :=
  f ∘ tensor_perms n 2 g idn.

Lemma permute_infunc_permutation n f g 
  (Hf : permutation (n * 2) f) (Hg : permutation n g) : 
  permutation (n * 2) (permute_infunc n f g).
Proof.
  unfold permute_infunc.
  auto_perm.
Qed.

#[export] Hint Resolve permute_infunc_permutation : perm_db.

Lemma infunc_partner_permute n f g 
  (Hf : permutation (n * 2) f) (Hg : permutation n g) : 
  perm_eq (n * 2) 
    (infunc_partner n (permute_infunc n f g)) 
    (infunc_partner n f).
Proof.
  unfold infunc_partner, permute_infunc.
  intros k Hk.
  rewrite <- perm_inv'_eq by auto_perm.
  (* rewrite perm_inv_compose by auto_perm. *)
  rewrite perm_inv'_compose, tensor_perms_inv' by auto_perm.
  Abort.


Definition infunc_idx n f k :=
  perm_inv (n * 2) f k / 2.

(* Lemma infunc_idx_correct_edgefunc n f k 
  (Hf : permutation (n * 2) f) (Hk : k < n * 2) :  *)
  


Lemma swap_from_0_1_perm_0_1 n : 
  perm_eq n (swap_from_0_1_perm 0 1 n) idn.
Proof.
  rewrite swap_from_0_1_perm_defn.
  intros k Hk.
  simpl.
  bdestructΩ'.
Qed.

Lemma zx_arb_cap_0_1 {n} (Hn : 2 <= n) : 
  zx_arb_cap 0 1 n ∝ 
  cast _ _ (zx_padded_cap_prf Hn) eq_refl
  (⊃ ↕ n_wire (n - 2)).
Proof.
  unfold zx_arb_cap.
  rewrite swap_from_0_1_perm_0_1, zx_of_perm_idn, nwire_removal_l.
  unfold zx_padded_cap.
  rewrite (le_lt_dec_le Hn).
  reflexivity.
Qed.

Lemma zx_arb_cap_0_1_alt {n} : 
  zx_arb_cap 0 1 n ∝ 
  zx_padded_cap n.
Proof.
  unfold zx_arb_cap.
  rewrite swap_from_0_1_perm_0_1, zx_of_perm_idn, nwire_removal_l.
  reflexivity.
Qed.

(* FIXME: Move to Modulus *)
Lemma ltb_1 n : n <? 1 = (n =? 0).
Proof. now destruct n. Qed.

(* TODO: Compare with lemma that says what biperm of compose arb_cup does *)

(* FIXME: Move these; to StackRules??? *)
Lemma n_stack_succ {n m} k (zx : ZX n m) : 
  n_stack (S k) zx = zx ↕ n_stack k zx.
Proof. reflexivity. Qed.

Lemma n_stack_assoc {n m} k l (zx : ZX n m) : 
  n_stack (k + l) zx ∝ 
  cast _ _ (Nat.mul_add_distr_r _ _ _) (Nat.mul_add_distr_r _ _ _) (
  n_stack k zx ↕ n_stack l zx).
Proof.
  apply ZX_prop_by_mat_prop.
  simpl_cast_semantics.
  rewrite stack_semantics, 3!n_stack_semantics.
  rewrite kron_n_m_split by auto_wf.
  rewrite <- 4!Nat.pow_mul_r.
  ereflexivity. 
  do 2 f_equal; lia.
Qed.



Lemma compose_arb_cup_ZX_of_infunc_base edges f
  (Hedges : 1 < edges) (Hf : permutation (edges * 2) f) 
  (Hf0 : f 1 = 0) (Hf1 : f 2 = 1) : 
  zx_arb_cup 0 1 (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1)
  (fun k => if k =? 0 then f k - 2 else f (k + 2) - 2)).
Proof.
  assert (Hf'0 : perm_inv (edges * 2) f 0 = 1) by
    (rewrite <- Hf0 at 2; auto_perm).
  assert (Hf'1 : perm_inv (edges * 2) f 1 = 2) by
    (rewrite <- Hf1 at 2; auto_perm).
  
  cbv delta [ZX_of_infunc] beta.
  rewrite cast_compose_r_eq_mid.
  rewrite <- compose_assoc.
  rewrite zx_arb_cup_compose_zx_of_perm_r by auto_perm.
  rewrite Hf'0, Hf'1.
  rewrite compose_assoc.
  rewrite compose_arb_cup_n_stack_caps by lia.
    (* (try apply (@permutation_neq (edges * 2)); auto_perm). *)
  change (1 / 2 =? 2 / 2) with false.
  cbn match.
  change (zx_arb_cap _ _) with (zx_arb_cap 0 1).
  rewrite zx_arb_cap_0_1, cast_compose_l_eq_mid.
  rewrite <- pull_out_top, cast_stack_r_fwd, 2!cast_contract_eq.
  rewrite cast_backwards_fwd, cast_contract_eq.
  rewrite cast_compose_distribute.
  apply compose_simplify_casted_abs; 
  [|intros ?Heq..].
  {lia. }
  - rewrite cast_contract_eq, cast_zx_of_perm.
    ereflexivity.
    apply zx_of_perm_eq_of_perm_eq.
    intros k Hk.
    rewrite contract_biperm_to_min_max.
    simpl.
    unfold contract_perm.
    rewrite Hf0, Hf1.
    simpl.
    rewrite !ltb_1.
    rewrite !(Nat.eqb_sym (f _)).
    rewrite <- !(perm_inv_eqb_iff Hf) by lia.
    rewrite Hf'0.
    rewrite !(Nat.eqb_sym 1).
    replace_bool_lia (k + 1 =? 1) (k =? 0).
    replace_bool_lia (k + 1 + 1 =? 1) false.
    replace_bool_lia (k + 1 =? 1) (k =? 0).
    replace_bool_lia (k + 1 <? 2) (k =? 0).
    bdestruct (k =? 0).
    + subst.
      simpl.
      lia.
    + rewrite <- Nat.add_assoc.
      simpl.
      lia.
  - rewrite cast_backwards_fwd, 2!cast_contract_eq.
    apply ZX_prop_by_mat_prop.
    simpl_cast_semantics.
    rewrite stack_semantics, 2!n_stack_semantics.
    replace (edges - 1) with (S (edges - 2)) by lia.
    rewrite kron_n_assoc by auto_wf.
    ereflexivity.
    f_equal;
    rewrite <- Nat.pow_mul_r;
    f_equal; lia.
  Unshelve.
    lia.
Qed.

Lemma ZX_of_infunc_compose_perm_of_zx_l edges f g 
  (Hf : permutation (edges * 2) f) (Hg : permutation (edges * 2) g) :
  zx_of_perm (edges * 2) g ⟷ ZX_of_infunc edges f ∝
  ZX_of_infunc edges (g ∘ f).
Proof.
  unfold ZX_of_infunc.
  rewrite cast_compose_r_eq_mid.
  rewrite <- compose_assoc.
  rewrite compose_zx_of_perm by auto.
  reflexivity.
Qed.



Lemma infunc_of_edgefunc_twice f k : 
  infunc_of_edgefunc f (2 * k) = 
  fst (f k).
Proof.
  unfold infunc_of_edgefunc.
  rewrite Nat.mul_comm, Nat.div_mul, Nat.Div0.mod_mul by easy.
  reflexivity.
Qed.

Lemma infunc_of_edgefunc_twice_plus f k : 
  infunc_of_edgefunc f (2 * k + 1) = 
  snd (f k).
Proof.
  unfold infunc_of_edgefunc.
  rewrite Nat.mul_comm, Nat.div_add_l, mod_add_l by easy.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma infunc_of_edgefunc_twice' f k : 
  infunc_of_edgefunc f (k * 2) = 
  fst (f k).
Proof.
  now rewrite Nat.mul_comm, infunc_of_edgefunc_twice.
Qed.

Lemma infunc_of_edgefunc_twice_plus' f k : 
  infunc_of_edgefunc f (k * 2 + 1) = 
  snd (f k).
Proof.
  now rewrite Nat.mul_comm, infunc_of_edgefunc_twice_plus.
Qed.

Lemma infunc_of_edgefunc_compose_l n f g
  (Hg : perm_edge_eq n (g ∘ f) f) : 
  perm_eq (n * 2) (infunc_of_edgefunc (g ∘ f))
    (infunc_of_edgefunc f ∘
    big_stack_perms n (fun _ => 2) (fun i => 
      if fst (g (f i)) =? snd (f i) then swap_2_perm else idn)).
Proof.
  rewrite perm_eq_split_times_2_iff.
  unfold infunc_of_edgefunc.
  intros k Hk.
  rewrite Nat.div_mul, mod_add_l, 
    Nat.div_add_l, Nat.Div0.mod_mul by easy.
  change (1 / 2) with 0.
  change (1 mod 2) with 1.
  rewrite Nat.add_0_r.
  change ((?f ∘ ?g) ?x) with ((f ∘ (fun y => y)) (g x)).
  rewrite 2!big_stack_perms_constant_alt by nia.
  rewrite Nat.div_mul, mod_add_l, 
    Nat.div_add_l, Nat.Div0.mod_mul by easy.
  change (1 / 2) with 0.
  change (1 mod 2) with 1.
  rewrite Nat.add_0_r.
  unfold compose.
  rewrite 2!mod_add_l, 2!Nat.div_add_l by easy.
  rewrite 2!Nat.div_small, 2!Nat.mod_small by (bdestruct_one; cbn; lia).
  rewrite Nat.add_0_r.
  specialize (Hg k Hk).
  hnf in Hg.
  unfold compose in Hg.
  bdestruct_one; cbn -[Nat.divmod Nat.modulo Nat.div];
  lia.
Qed.


(* FIXME: Move to PermutationFacts *)
Lemma permutation_compose_r_iff n f g 
  (Hg : permutation n g) : 
  permutation n (f ∘ g) <-> permutation n f.
Proof.
  split; [|auto_perm].
  intros Hfg.
  rewrite <- compose_idn_r.
  rewrite <- (perm_inv_rinv_of_permutation n g Hg).
  rewrite <- Combinators.compose_assoc.
  auto_perm.
Qed.



Definition edgepermutation n f :=
  permutation (n * 2) (infunc_of_edgefunc f).

Lemma edgepermutation_WF n f 
  (Hf : edgepermutation n f) : 
  WF_edgefunc n (n * 2) f.
Proof.
  intros k Hk.
  rewrite <- infunc_of_edgefunc_twice, <- infunc_of_edgefunc_twice_plus.
  split; 
  apply (permutation_is_bounded _ _ Hf);
  show_moddy_lt.
Qed.

Lemma edgepermutation_compose_r_iff n f g 
  (Hg : permutation n g) : 
  edgepermutation n (f ∘ g) <-> edgepermutation n f.
Proof.
  unfold edgepermutation.
  rewrite infunc_of_edgefunc_compose_r.
  apply permutation_compose_r_iff.
  auto_perm.
Qed.

Add Parametric Morphism n : (edgepermutation n) 
  with signature perm_edge_eq n ==> iff as 
  edgepermutation_perm_edge_eq_iff.
Proof.
  intros f g Hfg.
  unfold edgepermutation.
  rewrite (infunc_of_edgefunc_perm_edge_eq _ _ _ Hfg).
  apply permutation_compose_r_iff.
  auto_perm.
Qed.


(* FIXME: Move *)
Add Parametric Morphism n : (ZX_of_infunc n) with signature
  perm_eq (n * 2) ==> eq as ZX_of_infunc_eq_of_perm_eq.
Proof.
  intros f g Hfg.
  unfold ZX_of_infunc.
  apply cast_simplify_eq.
  f_equal.
  apply zx_of_perm_eq_of_perm_eq.
  exact Hfg.
Qed.

(* FIXME: Move to ZXPermFacts *)
Lemma zx_of_perm_empty_eq_n_wire n f 
  (Hn : n = 0) : zx_of_perm n f = n_wire n.
Proof.
  subst.
  cbv.
  rewrite (UIP_nat _ _ _ eq_refl).
  reflexivity.
Qed.

Lemma ZX_of_infunc_absorb_tensor_perms_r n f g
  (Hf : permutation (n * 2) f) (Hg : permutation n g) : 
  ZX_of_infunc n (f ∘ tensor_perms n 2 g idn) ∝ ZX_of_infunc n f.
Proof.
  unfold ZX_of_infunc.
  rewrite <- compose_zx_of_perm by auto_perm.
  rewrite compose_assoc, <- nstack_zx_of_perm_passthrough by auto.
  rewrite (zx_of_perm_empty_eq_n_wire (n * 0)) by lia.
  rewrite nwire_removal_r.
  reflexivity.
Qed.


Lemma ZX_of_edgeperm_absorb_perm_r n f g 
  (Hf : edgepermutation n f) (Hg : permutation n g) :
  ZX_of_edgeperm n (f ∘ g) ∝
  ZX_of_edgeperm n f.
Proof.
  unfold ZX_of_edgeperm.
  rewrite infunc_of_edgefunc_compose_r.
  rewrite ZX_of_infunc_absorb_tensor_perms_r by assumption.
  reflexivity.
Qed.



Lemma ZX_of_edgeperm_perm_edge_eq_simplify n f g 
  (Hf : edgepermutation n f) (Hg : perm_edge_eq n f g) :
  ZX_of_edgeperm n f ∝
  ZX_of_edgeperm n g.
Proof.
  unfold ZX_of_edgeperm.
  apply ZX_of_infunc_edgeperm_eq_simplify; [assumption|].
  intros k Hk.
  rewrite 2!infunc_of_edgefunc_twice, 2!infunc_of_edgefunc_twice_plus.
  exact (Hg k Hk).
Qed.

Lemma ZX_of_edgeperm_absorb_swaps n f g 
  (Hf : edgepermutation n f) (Hg : perm_edge_eq n (g ∘ f) f) :
  ZX_of_edgeperm n (g ∘ f) ∝
  ZX_of_edgeperm n f.
Proof.
  symmetry.
  apply ZX_of_edgeperm_perm_edge_eq_simplify; [assumption|].
  symmetry.
  assumption.
Qed.



Lemma ZX_of_edgeperm_perm_edge_eq_rw {n f g}
  (Hfg : perm_edge_eq n f g) (Hf : edgepermutation n f) : 
  ZX_of_edgeperm n f ∝ ZX_of_edgeperm n g.
Proof.
  now apply ZX_of_edgeperm_perm_edge_eq_simplify.
Qed.

Lemma ZX_of_edgeperm_perm_edge_eq_rw' {n f g}
  (Hfg : perm_edge_eq n f g) (Hf : edgepermutation n g) : 
  ZX_of_edgeperm n f ∝ ZX_of_edgeperm n g.
Proof.
  rewrite <- Hfg in Hf.
  now apply ZX_of_edgeperm_perm_edge_eq_simplify.
Qed.

Lemma ZX_of_edgeperm_eq_of_deg_eq n f g 
  (Hf : edgepermutation n f) (Hg : edgepermutation n g) 
  (Hfg : 
    perm_deg_eq (n * 2) 
      (deg_of_edgefunc n f)
      (deg_of_edgefunc n g) ) :
  ZX_of_edgeperm n f ∝ ZX_of_edgeperm n g.
Proof.
  apply deg_of_edgefunc_eq_permutation_witness in Hfg;
  [|now apply edgepermutation_WF..].
  destruct Hfg as (h & Hh & HhWF & Heq).
  rewrite <- (ZX_of_edgeperm_perm_edge_eq_rw' Heq) by auto.
  rewrite ZX_of_edgeperm_absorb_perm_r by auto.
  reflexivity.
Qed.

(* FIXME: Move to Modulus *)
Lemma and_of_or_of_iff {P Q} : 
  P \/ Q -> (P <-> Q) -> P /\ Q.
Proof.
  tauto.
Qed.

Lemma ZX_of_edgeperm_eq_of_deg_eq_gen_WF n f g 
  (HfWF : WF_edgefunc n (n * 2) f)
  (HgWF : WF_edgefunc n (n * 2) g)
  (Hforg : edgepermutation n f \/ edgepermutation n g) 
  (Hfg : 
    perm_deg_eq (n * 2) 
      (deg_of_edgefunc n f)
      (deg_of_edgefunc n g) ) :
  ZX_of_edgeperm n f ∝ ZX_of_edgeperm n g.
Proof.
  refine ((fun P => ZX_of_edgeperm_eq_of_deg_eq _ _ _ 
    (proj1 P) (proj2 P) Hfg) _).
  apply (and_of_or_of_iff Hforg).
  (* TODO: Make a tactic (by_symmetry') to use symmetry on HHforg here *)
  apply deg_of_edgefunc_eq_permutation_witness in Hfg; [|auto..].
  destruct Hfg as (h & Hh & HhWF & Hfg).
  rewrite <- Hfg.
  symmetry.
  apply edgepermutation_compose_r_iff.
  exact Hh.
Qed.


(* FIXME: Move this to by edge_eq theory *)
Definition edge_mem k ij :=
  (k =? fst ij) || (k =? snd ij).

Add Parametric Morphism k : (edge_mem k) with signature
  edge_eq ==> eq as edge_mem_eq_of_edge_eq.
Proof.
  intros ij ij' [Heq | Hswap]%edge_eq_defn_l.
  - now rewrite Heq.
  - rewrite Hswap; apply orb_comm.
Qed.

Definition edge_partner k ij :=
  if k =? fst ij then 
    snd ij
  else 
    (if k =? snd ij then fst ij else k).

Add Parametric Morphism k : (edge_partner k) with signature
  edge_eq ==> eq as edge_partner_eq_of_edge_eq.
Proof.
  intros ij ij' [Heq | Hswap]%edge_eq_defn_l.
  - now rewrite Heq.
  - rewrite Hswap.
    unfold edge_partner.
    simpl.
    bdestructΩ'.
Qed.

Definition pairmap {A B} (f : A -> B) : A * A -> B * B :=
  fun xy => (f (fst xy), f (snd xy)).

Arguments pairmap _ !_ /.









Lemma big_sum_twice_of_edgefunc_test_perm_edge_eq (n x c d : nat) f g 
  (Hfg : perm_edge_eq n f g) :
  big_sum (fun i => if infunc_of_edgefunc f i =? x then c else d) (n * 2) =
  big_sum (fun i => if infunc_of_edgefunc g i =? x then c else d) (n * 2).
Proof.
  rewrite Nat.mul_comm, 2!big_sum_product_div_mod_split.
  apply big_sum_eq_bounded.
  intros k Hk.
  simpl.
  replace (S (k * 2)) with (k * 2 + 1) by lia.
  rewrite 2!infunc_of_edgefunc_twice',
    2!infunc_of_edgefunc_twice_plus'.
  specialize (Hfg k Hk).
  hnf in Hfg.
  repeat (bdestruct_one; try subst); lia.
Qed.
  
Lemma count_func_vals_twice_of_edgefunc_of_perm_edge_eq n f g 
  (Hfg : perm_edge_eq n f g) x : 
  count_func_vals (n * 2) (infunc_of_edgefunc f) x = 
  count_func_vals (n * 2) (infunc_of_edgefunc g) x.
Proof.
  unfold count_func_vals.
  apply big_sum_twice_of_edgefunc_test_perm_edge_eq, Hfg.
Qed.

Lemma count_func_vals_twice_of_edgefunc_of_perm_edge_eq_ext n f g 
  (Hfg : perm_edge_eq n f g) : 
  count_func_vals (n * 2) (infunc_of_edgefunc f) = 
  count_func_vals (n * 2) (infunc_of_edgefunc g).
Proof.
  apply functional_extensionality, 
    (count_func_vals_twice_of_edgefunc_of_perm_edge_eq n f g Hfg).
Qed.

(* FIXME: Move *)
Lemma big_sum_1 {G} {HG : Monoid G} (f : nat -> G) : 
  big_sum f 1 = f 0.
Proof.
  simpl.
  apply HG.
Qed.

Lemma perm_of_input_func_preserves_perm_edge_eq n f g 
  (Hfg : perm_edge_eq n f g) : 
  perm_edge_eq n
  (edgefunc_of_infunc (perm_of_input_func (n * 2) (infunc_of_edgefunc f)))
  (edgefunc_of_infunc (perm_of_input_func (n * 2) (infunc_of_edgefunc g))).
Proof.
  intros k Hk.
  unfold edgefunc_of_infunc.
  unfold perm_of_input_func.
  do 2 if_false_lia.
  rewrite 2!infunc_of_edgefunc_twice', 2!infunc_of_edgefunc_twice_plus'.
  rewrite (count_func_vals_twice_of_edgefunc_of_perm_edge_eq_ext _ _ _ Hfg).
  rewrite 2!big_sum_sum.
  rewrite 2!(big_sum_twice_of_edgefunc_test_perm_edge_eq k _ _ _ f g) 
    by (intros ? ?; apply Hfg; lia).
  rewrite 2!big_sum_1, Nat.add_0_r.
  rewrite 2!infunc_of_edgefunc_twice'.
  specialize (Hfg k Hk) as Heq.
  bdestruct_one.
  - hnf in Heq.
    assert (Hg1 : fst (g k) = fst (f k)) by lia. 
    assert (Hg2 : snd (g k) = fst (f k)) by lia.
    assert (Hf2 : snd (f k) = fst (f k)) by easy.
    rewrite Hg1, Hg2, Hf2.
    rewrite Nat.eqb_refl.
    reflexivity.
  - destruct Heq as [[Hf1 Hf2] | [Hf1 Hf2]].
    + rewrite Hf1, Hf2 in *.
      if_false_lia.
      reflexivity.
    + rewrite Hf1, Hf2, edge_eq_swap in *.
      if_false_lia.
      rewrite 2!Nat.add_0_r.
      reflexivity.
Qed.


Definition ZX_of_input_func n f :=
  ZX_of_infunc n (perm_of_input_func (n * 2) f).

Definition ZX_of_edgefunc n f :=
  ZX_of_input_func n (infunc_of_edgefunc f).


Add Parametric Morphism n : (ZX_of_input_func n)
  with signature perm_eq (n * 2) ==> eq as
  ZX_of_input_func_eq_of_perm_eq.
Proof.
  intros f g Hfg.
  unfold ZX_of_input_func.
  now rewrite Hfg.
Qed.

Add Parametric Morphism n : (ZX_of_edgefunc n) with signature
  perm_edge_eq n ==> proportional as
  ZX_of_edgefunc_prop_of_perm_edge_eq.
Proof.
  intros f g Hfg.
  unfold ZX_of_edgefunc, ZX_of_input_func.
  apply ZX_of_infunc_edgeperm_eq_simplify; [auto_perm|].
  intros k.
  rewrite (Nat.mul_comm 2).
  revert k.
  apply perm_of_input_func_preserves_perm_edge_eq, Hfg.
Qed.

(* Definition normalizer_rperm n k l (f : nat -> nat) : nat -> nat :=
  if perm_inv (n * 2) f k / 2 =? perm_inv (n * 2) f l / 2 then
    tensor_perms n 2 (swap_perm 0 (perm_inv (n * 2) f k / 2) n) idn
  else 
    tensor_perms n 2 (
      swap_to_0_1_perm (perm_inv (n * 2) f k / 2) 
        (perm_inv (n * 2) f l / 2) n)
      idn.

Lemma normalizer_rperm_permutation n k l f 
  (Hf : permutation (n * 2) f) (Hk : k < n * 2) (Hl : l < n * 2) :
  permutation (n * 2) (normalizer_rperm n k l f).
Proof.
  unfold normalizer_rperm.
  bdestruct_one.
  - apply tensor_perms_permutation; [|auto_perm].
    rewrite Nat.mul_comm.
    apply swap_perm_permutation; [lia|].
    apply Nat.Div0.div_lt_upper_bound.
    auto_perm.
  - apply tensor_perms_permutation; [|auto_perm].
    apply swap_to_0_1_perm_permutation; [| |easy];
    apply Nat.Div0.div_lt_upper_bound;
    rewrite Nat.mul_comm;
    auto_perm.
Qed. *)

Definition edgeperm_idx n (f : nat -> nat * nat) k :=
  perm_inv (n * 2) (infunc_of_edgefunc f) k / 2.

Definition edgeperm_offset n (f : nat -> nat * nat) k :=
  (perm_inv (n * 2) (infunc_of_edgefunc f) k) mod 2.

Lemma edgeperm_idx_bounded n f k (Hk : k < n * 2) : 
  edgeperm_idx n f k < n.
Proof.
  apply Nat.Div0.div_lt_upper_bound.
  rewrite (Nat.mul_comm 2).
  auto_perm.
Qed.

#[export] Hint Resolve edgeperm_idx_bounded : perm_bounded_db.

Lemma edgeperm_offset_bounded n f k : 
  edgeperm_offset n f k < 2.
Proof.
  apply Nat.mod_upper_bound.
  lia.
Qed.

#[export] Hint Resolve edgeperm_offset_bounded : perm_bounded_db.

Lemma edgeperm_offset_not_zero n f k : 
  edgeperm_offset n f k <> 0 <-> edgeperm_offset n f k = 1.
Proof.
  split; [|intros ->; easy].
  unfold edgeperm_offset.
  pose proof (Nat.mod_upper_bound 
    (perm_inv (n * 2) (infunc_of_edgefunc f) k) 2 ltac:(easy)) as H.
  lia.
Qed.

(* FIXME: Move to by edge_eq *)
Lemma edge_eq_of_parts (a b : nat * nat) :
  fst a = fst b -> snd a = snd b ->
  edge_eq a b.
Proof.
  intros H1 H2; left.
  easy.
Qed.

(* FIXME: Move to QuantumLib.Prelim *)
Ltac bdestruct_as b H :=
  let e := fresh "e" in
  evar ( e : Prop ); assert (H : reflect e b); subst e;
   [ eauto with bdestruct | destruct H as [H| H];
	  [  | try (first [ apply not_lt in H | apply not_le in H ]) ] ].

Tactic Notation "bdestruct" constr(b) :=
  bdestruct b.

Tactic Notation "bdestruct" constr(b) "as" ident(H) :=
  bdestruct_as b H.

(* Tactic Notation "bdestruct_one" :=
  bdestruct_one.

Tactic Notation "bdestruct_one" "as" ident(H) :=
  bdestruct_as b H. *)





Definition edgeperm_partner n f k := 
  edge_partner k (f (edgeperm_idx n f k)).

Lemma edgeperm_idx_rinv n f k (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edge_to_func (f (edgeperm_idx n f k)) (edgeperm_offset n f k) = k.
Proof.
  unfold edge_to_func.
  bdestruct (edgeperm_offset n f k =? 0) as Heq.
  - simpl.
    rewrite <- infunc_of_edgefunc_twice'.
    unfold edgeperm_idx.
    unfold edgeperm_offset in *.
    rewrite div_mul_not_exact, Heq, Nat.sub_0_r by easy.
    apply perm_inv_is_rinv_of_permutation; assumption.
  - rewrite edgeperm_offset_not_zero in Heq.
    if_true_lia.
    rewrite <- infunc_of_edgefunc_twice_plus'.
    unfold edgeperm_idx.
    unfold edgeperm_offset in *.
    rewrite div_mul_not_exact, Heq by easy.
    rewrite Nat.sub_add.
    + apply perm_inv_is_rinv_of_permutation; assumption.
    + enough (perm_inv (n * 2) (infunc_of_edgefunc f) k <> 0) by lia.
      intros H.
      now rewrite H in Heq.
Qed.

Lemma edgeperm_idx_rinv_fst n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edgeperm_offset n f k = 0 ->
  fst (f (edgeperm_idx n f k)) = k.
Proof.
  pose proof (edgeperm_idx_rinv n f k Hf Hk) as Heq.
  intros Hrw.
  rewrite Hrw in Heq.
  exact Heq.
Qed.

Lemma edgeperm_idx_rinv_snd n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edgeperm_offset n f k = 1 ->
  snd (f (edgeperm_idx n f k)) = k.
Proof.
  pose proof (edgeperm_idx_rinv n f k Hf Hk) as Heq.
  intros Hrw.
  rewrite Hrw in Heq.
  exact Heq.
Qed.

Lemma edgeperm_idx_rinv_snd' n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edgeperm_offset n f k <> 0 ->
  snd (f (edgeperm_idx n f k)) = k.
Proof.
  rewrite edgeperm_offset_not_zero.
  apply edgeperm_idx_rinv_snd; auto.
Qed.

Lemma edgepermutation_fst_neq_snd n f k 
  (Hf : edgepermutation n f) (Hk : k < n) :
  fst (f k) <> snd (f k).
Proof.
  rewrite <- infunc_of_edgefunc_twice, <- infunc_of_edgefunc_twice_plus.
  apply (permutation_neq Hf);
  [show_moddy_lt..|nia].
Qed.

Lemma edgeperm_idx_rinv_fst_iff n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edgeperm_offset n f k = 0 <->
  fst (f (edgeperm_idx n f k)) = k.
Proof.
  split; [apply edgeperm_idx_rinv_fst; auto|].
  bdestruct (edgeperm_offset n f k =? 0) as Heq; [easy|].
  apply edgeperm_idx_rinv_snd' in Heq; [|auto..].
  pose proof (edgepermutation_fst_neq_snd n f (edgeperm_idx n f k) Hf
    ltac:(auto_perm)).
  congruence.
Qed.

Lemma edgeperm_idx_rinv_snd_iff n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edgeperm_offset n f k = 1 <->
  snd (f (edgeperm_idx n f k)) = k.
Proof.
  split; [apply edgeperm_idx_rinv_snd; auto|].
  rewrite <- edgeperm_offset_not_zero.
  bdestruct (edgeperm_offset n f k =? 0) as Heq; [|easy].
  apply edgeperm_idx_rinv_fst in Heq; [|auto..].
  pose proof (edgepermutation_fst_neq_snd n f (edgeperm_idx n f k) Hf
    ltac:(auto_perm)).
  congruence.
Qed.

Lemma edgeperm_idx_rinv_snd_iff' n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edgeperm_offset n f k <> 0 <->
  snd (f (edgeperm_idx n f k)) = k.
Proof.
  rewrite edgeperm_offset_not_zero.
  apply edgeperm_idx_rinv_snd_iff; auto.
Qed.

Lemma edgeperm_idx_rinv_edge_eq n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edge_eq (f (edgeperm_idx n f k))
    (k, edgeperm_partner n f k).
Proof.
  bdestruct (edgeperm_offset n f k =? 0) as Heq.
  - apply edge_eq_of_parts.
    + simpl.
      apply edgeperm_idx_rinv_fst; auto.
    + simpl.
      unfold edgeperm_partner.
      unfold edge_partner.
      rewrite edgeperm_idx_rinv_fst by auto.
      rewrite Nat.eqb_refl.
      reflexivity.
  - rewrite edge_eq_swap.
    apply edge_eq_of_parts.
    + simpl.
      unfold edgeperm_partner.
      unfold edge_partner.
      rewrite edgeperm_idx_rinv_snd' by auto.
      rewrite Nat.eqb_refl.
      bdestructΩ'.
    + simpl.
      apply edgeperm_idx_rinv_snd'; auto.
Qed.

Lemma edgeperm_partner_neq n f k (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edgeperm_partner n f k <> k.
Proof.
  unfold edgeperm_partner.
  unfold edge_partner.
  bdestruct (edgeperm_offset n f k =? 0) as Heq.
  - pose proof (edgeperm_idx_rinv_fst n f k Hf Hk Heq).
    pose proof (edgepermutation_fst_neq_snd n f 
      (edgeperm_idx n f k) Hf ltac:(auto_perm)).
    bdestructΩ'.
  - pose proof (edgeperm_idx_rinv_snd' n f k Hf Hk Heq).
    pose proof (edgepermutation_fst_neq_snd n f 
      (edgeperm_idx n f k) Hf ltac:(auto_perm)).
    bdestructΩ'.
Qed.

Lemma edgeperm_idx_rinv_part_fst_iff n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edgeperm_offset n f k = 1 <->
  fst (f (edgeperm_idx n f k)) = edgeperm_partner n f k.
Proof.
  pose proof (edgeperm_idx_rinv_edge_eq n f k Hf Hk) as Heq.
  unfold edge_eq in Heq.
  cbn [fst snd] in Heq.
  rewrite edgeperm_idx_rinv_snd_iff by auto_perm.
  lia.
Qed.

Lemma edgeperm_idx_rinv_part_fst_iff' n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edgeperm_offset n f k <> 0 <->
  fst (f (edgeperm_idx n f k)) = edgeperm_partner n f k.
Proof.
  rewrite edgeperm_offset_not_zero.
  apply edgeperm_idx_rinv_part_fst_iff; auto.
Qed.

Lemma edgeperm_idx_rinv_part_snd_iff n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) :
  edgeperm_offset n f k = 0 <->
  snd (f (edgeperm_idx n f k)) = edgeperm_partner n f k.
Proof.
  pose proof (edgeperm_idx_rinv_edge_eq n f k Hf Hk) as Heq.
  unfold edge_eq in Heq.
  cbn [fst snd] in Heq.
  rewrite edgeperm_idx_rinv_fst_iff by auto_perm.
  lia.
Qed.

Lemma edgeperm_partner_defn n f (Hf : edgepermutation n f) : 
  perm_eq (n * 2) (edgeperm_partner n f)
  (fun k => infunc_of_edgefunc f (edgeperm_idx n f k * 2 
    + (1 - edgeperm_offset n f k))).
Proof.
  intros k Hk.
  unfold edgeperm_partner.
  unfold edge_partner.
  bdestruct (edgeperm_offset n f k =? 0) as Heq.
  - rewrite edgeperm_idx_rinv_fst by auto.
    rewrite Nat.eqb_refl, Heq.
    rewrite infunc_of_edgefunc_twice_plus'.
    reflexivity.
  - rewrite edgeperm_offset_not_zero in Heq.
    rewrite Heq, Nat.add_0_r.
    rewrite infunc_of_edgefunc_twice'.
    rewrite edgeperm_idx_rinv_snd_iff in Heq by auto.
    pose proof (edgeperm_idx_rinv_fst_iff n f k Hf Hk).
    bdestructΩ'.
Qed.

Lemma edgeperm_partner_bounded n f (Hf : edgepermutation n f) : 
  perm_bounded (n * 2) (edgeperm_partner n f).
Proof.
  unfold edgeperm_partner.
  intros k Hk.
  unfold edge_partner.
  bdestructΩ'.
  - rewrite <- infunc_of_edgefunc_twice_plus.
    apply (permutation_is_bounded _ _ Hf).
    pose proof (edgeperm_idx_bounded n f k Hk).
    show_moddy_lt.
  - rewrite <- infunc_of_edgefunc_twice.
    apply (permutation_is_bounded _ _ Hf).
    pose proof (edgeperm_idx_bounded n f k Hk).
    show_moddy_lt.
Qed.

#[export] Hint Resolve edgeperm_partner_bounded : perm_bounded_db.

Lemma edgeperm_idx_offset_eq n f k
  (Hf : edgepermutation n f) (Hk : k < n * 2) : 
  edgeperm_idx n f k * 2 + edgeperm_offset n f k = 
  perm_inv (n * 2) (infunc_of_edgefunc f) k.
Proof.
  rewrite Nat.mul_comm.
  symmetry.
  apply Nat.div_mod_eq.
Qed.

Lemma edgeperm_offset_eq_sub_idx n f k
  (Hf : edgepermutation n f) (Hk : k < n * 2) : 
  edgeperm_offset n f k = 
  perm_inv (n * 2) (infunc_of_edgefunc f) k - edgeperm_idx n f k * 2.
Proof.
  pose proof (edgeperm_idx_offset_eq n f k Hf Hk).
  lia.
Qed.

Lemma edgeperm_idx_eq_sub_offset n f k
  (Hf : edgepermutation n f) (Hk : k < n * 2) : 
  edgeperm_idx n f k * 2 = 
  perm_inv (n * 2) (infunc_of_edgefunc f) k - edgeperm_offset n f k.
Proof.
  pose proof (edgeperm_idx_offset_eq n f k Hf Hk).
  lia.
Qed.

Lemma edgeperm_idx_edgeperm_partner n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) : 
  edgeperm_idx n f (edgeperm_partner n f k) = 
  edgeperm_idx n f k.
Proof.
  unfold edgeperm_idx at 1.
  rewrite edgeperm_partner_defn by auto_perm.
  pose proof (edgeperm_idx_bounded n f k Hk).
  rewrite perm_inv_is_linv_of_permutation by (auto_perm + show_moddy_lt).
  rewrite Nat.div_add_l, Nat.div_small by lia.
  apply Nat.add_0_r.
Qed.

Lemma edgeperm_offset_edgeperm_partner n f k 
  (Hf : edgepermutation n f) (Hk : k < n * 2) : 
  edgeperm_offset n f (edgeperm_partner n f k) = 
  1 - edgeperm_offset n f k.
Proof.
  unfold edgeperm_offset at 1.
  rewrite edgeperm_partner_defn by auto_perm.
  pose proof (edgeperm_idx_bounded n f k Hk).
  rewrite perm_inv_is_linv_of_permutation by (auto_perm + show_moddy_lt).
  rewrite mod_add_l, Nat.mod_small by lia.
  reflexivity.
Qed.

Lemma edgeperm_partner_bipermutation n f (Hf : edgepermutation n f) : 
  bipermutation (n * 2) (edgeperm_partner n f).
Proof.
  apply bipermutation_defn; repeat split.
  - auto_perm. 
  - intros k Hk.
    now apply edgeperm_partner_neq.
  - (* rewrite 2!edgeperm_partner_defn at 1 by auto. *)
    (* intros k Hk. *)
    rewrite edgeperm_partner_defn at 1 by auto.
    intros k Hk.
    unfold compose.
    rewrite edgeperm_idx_edgeperm_partner, 
      edgeperm_offset_edgeperm_partner by auto.
    replace (1 - (1 - edgeperm_offset n f k)) with (edgeperm_offset n f k) 
      by (pose proof edgeperm_offset_bounded n f k; lia).
    rewrite edgeperm_idx_offset_eq by auto.
    apply perm_inv_is_rinv_of_permutation; auto_perm.
Qed.

#[export] Hint Resolve edgeperm_partner_bipermutation : biperm_db.







(* Lemma compose_zx_of_perm_ZX_of_edgeperm  *)

Lemma compose_arb_cup_ZX_of_edgeperm_defn_raw n k l f 
  (Hf : edgepermutation n f) (Hn : 1 <= n)
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) :
  zx_arb_cup k l (n * 2) ⟷ ZX_of_edgeperm n f ∝
  cast _ _ eq_refl (zx_padded_cap_prf (Nat.mul_le_mono_r 1 n 2 Hn)) 
    (⊂ ↕ n_wire ((n * 2 - 2))) ⟷
  ZX_of_infunc n (swap_to_0_1_perm k l (n * 2) ∘ infunc_of_edgefunc f).
Proof.
  unfold zx_arb_cup, zx_arb_cap.
  cbn [ZXCore.transpose].
  rewrite zx_of_perm_transpose by auto_perm.
  rewrite swap_from_0_1_perm_inv' by auto_perm.
  rewrite compose_assoc.
  unfold ZX_of_edgeperm.
  rewrite ZX_of_infunc_compose_perm_of_zx_l by auto_perm.
  apply compose_simplify_l.
  unfold zx_padded_cap.
  destruct (le_lt_dec 2 (n * 2)); [|lia].
  rewrite cast_transpose.
  cbn [ZXCore.transpose].
  rewrite n_wire_transpose.
  now apply cast_simplify.
Qed.

Lemma compose_arb_cup_ZX_of_edgeperm_defn n k l f 
  (Hf : edgepermutation n f)
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) :
  zx_arb_cup k l (n * 2) ⟷ ZX_of_edgeperm n f ∝
  zx_arb_cup 0 1 (n * 2) ⟷
  ZX_of_infunc n (swap_to_0_1_perm k l (n * 2) ∘ infunc_of_edgefunc f).
Proof.
  rewrite compose_arb_cup_ZX_of_edgeperm_defn_raw by auto.
  apply compose_simplify_l.
  unfold zx_arb_cup.
  rewrite zx_arb_cap_0_1.
  rewrite cast_transpose.
  cbn [ZXCore.transpose].
  rewrite n_wire_transpose.
  now apply cast_simplify.
  Unshelve.
  all: lia.
Qed.

Lemma compose_arb_cup_ZX_of_infunc_defn n k l f 
  (Hf : permutation (n * 2) f)
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) :
  zx_arb_cup k l (n * 2) ⟷ ZX_of_infunc n f ∝
  zx_arb_cup 0 1 (n * 2) ⟷
  ZX_of_infunc n (swap_to_0_1_perm k l (n * 2) ∘ f).
Proof.
  unfold zx_arb_cup, zx_arb_cap.
  cbn [ZXCore.transpose].
  rewrite zx_of_perm_transpose by auto_perm.
  rewrite swap_from_0_1_perm_inv' by auto_perm.
  rewrite compose_assoc.
  rewrite ZX_of_infunc_compose_perm_of_zx_l by auto_perm.
  apply compose_simplify_l.
  unfold zx_padded_cap.
  destruct (le_lt_dec 2 (n * 2)); [|lia].
  rewrite cast_transpose.
  cbn [ZXCore.transpose].
  rewrite n_wire_transpose.
  rewrite swap_from_0_1_perm_0_1, zx_of_perm_idn, n_wire_transpose, nwire_removal_r.
  now apply cast_simplify.
Qed.


Lemma ZX_of_infunc_0 f : 
  ZX_of_infunc 0 f ∝ ⦰.
Proof.
  unfold ZX_of_infunc.
  cbn -[cast].
  rewrite zx_of_perm_0.
  now rewrite cast_id, compose_empty_l.
Qed.

(* FIXME: Move *)
Lemma zx_arb_cup_0_1 {n} (Hn : 2 <= n) : 
  zx_arb_cup 0 1 n ∝ 
  cast _ _ eq_refl (zx_padded_cap_prf Hn)
  (⊂ ↕ n_wire (n - 2)).
Proof.
  unfold zx_arb_cup.
  rewrite (zx_arb_cap_0_1 Hn).
  rewrite cast_transpose.
  apply cast_simplify.
  simpl.
  now rewrite n_wire_transpose.
Qed.

(* FIXME: Move *)
Lemma perm_inv_eq_of_eq {n f k l} (Hfk : f k = l) (Hf : permutation n f) 
  (Hk : k < n) (Hl : l < n) : perm_inv n f l = k.
Proof.
  now rewrite perm_inv_eq_iff.
Qed.

Lemma n_stack_renumber {n m k k'} (Hk : k = k') (zx : ZX n m) : 
  k ⇑ zx = cast _ _ (f_equal (fun l=>l*n) Hk) (f_equal (fun l=>l*m) Hk) 
    (k' ⇑ zx).
Proof.
  now subst.
Qed.

Lemma n_stack_1 {n m} (zx : ZX n m) : 
  1 ⇑ zx ∝ cast _ _ (Nat.add_0_r _) (Nat.add_0_r _) zx.
Proof.
  apply stack_empty_r_fwd.
Qed.



(* FIXME: Move to Modulus *)
Lemma div_eqb_0_iff n k : 
  k <> 0 ->
  (n / k =? 0) = (n <? k).
Proof.
  intros Hk.
  rewrite div_eqb_iff by easy.
  bdestructΩ'.
Qed.

Lemma swap_2_perm_WF : WF_Perm 2 swap_2_perm.
Proof.
  apply swap_perm_WF.
Qed.

Lemma conditional_swaps_if_eqb_eq n a : 
  perm_eq (n * 2) (big_stack_perms n (fun _ => 2) 
  (fun i => if i =? a then swap_2_perm else idn))
  (swap_perm (2 * a) (2 * a + 1) (n * 2)).
Proof.
  intros k Hk.
  rewrite big_stack_perms_constant_alt by easy.
  rewrite div_eqb_iff by lia.
  rewrite andb_if.
  bdestruct (2 * a <=? k); [bdestruct (k <? 2 * S a)|].
  - assert (Hkdiv : k / 2 = a) by (rewrite div_eq_iff; lia).
    pose proof (Nat.mod_upper_bound k 2 ltac:(lia)) as Hkmod.
    rewrite (Nat.div_mod_eq k 2) at 3.
    rewrite Hkdiv.
    bdestruct (k mod 2 =? 0).
    + replace -> (k mod 2).
      rewrite Nat.add_0_r, swap_perm_left by lia.
      now rewrite Nat.mul_comm.
    + replace (k mod 2) with 1 by lia.
      rewrite Nat.add_0_r, swap_perm_right by lia.
      now rewrite Nat.mul_comm.
  - rewrite swap_perm_neither by lia.
    pose proof (Nat.div_mod_eq k 2); lia.
  - rewrite swap_perm_neither by lia.
    pose proof (Nat.div_mod_eq k 2); lia.
Qed.

Lemma conditional_swaps_0_eq n : 
  perm_eq (n * 2) (big_stack_perms n (fun _ => 2) 
  (fun i => if i =? 0 then swap_2_perm else idn))
  swap_2_perm.
Proof.
  intros k Hk.
  rewrite big_stack_perms_constant_alt by easy.
  rewrite div_eqb_0_iff by lia.
  bdestruct (k <? 2).
  - rewrite Nat.div_small, Nat.mod_small by lia.
    reflexivity.
  - rewrite Nat.mul_comm, <- Nat.div_mod_eq.
    now rewrite swap_2_perm_WF.
Qed.


Lemma swap_to_0_1_perm_small k l n a : 
  k < n -> l < n ->
  a = k \/ a = l -> 
  swap_to_0_1_perm k l n a < 2.
Proof.
  intros Hk Hl [-> | ->].
  - bdestruct (k <=? l).
    + rewrite swap_to_0_1_perm_left_min; lia.
    + rewrite swap_to_0_1_perm_comm, swap_to_0_1_perm_right_max; lia.
  - bdestruct (k <? l).
    + rewrite swap_to_0_1_perm_right_max; lia.
    + rewrite swap_to_0_1_perm_comm, swap_to_0_1_perm_left_min; lia.
Qed.





(* FIXME: Move to by edgepermutation stuff *)
Lemma fst_edgepermutation_bounded n f k 
  (Hf : edgepermutation n f) (Hk : k < n) : 
  fst (f k) < n * 2.
Proof.
  pose proof (permutation_is_bounded _ _ Hf (k * 2) ltac:(lia)) as Hlt.
  now rewrite infunc_of_edgefunc_twice' in Hlt.
Qed.

Lemma snd_edgepermutation_bounded n f k 
  (Hf : edgepermutation n f) (Hk : k < n) : 
  snd (f k) < n * 2.
Proof.
  pose proof (permutation_is_bounded _ _ Hf (k * 2 + 1) ltac:(show_moddy_lt)) as Hlt.
  now rewrite infunc_of_edgefunc_twice_plus' in Hlt.
Qed.

#[export]
Hint Resolve fst_edgepermutation_bounded 
  snd_edgepermutation_bounded : perm_bounded_db.

Lemma edgeperm_idx_linv_fst n f k
  (Hf : edgepermutation n f) (Hk : k < n) :
  edgeperm_idx n f (fst (f k)) = k.
Proof.
  unfold edgeperm_idx.
  enough (Hinv : perm_inv (n * 2) (infunc_of_edgefunc f) (fst (f k)) = k * 2).
  - rewrite Hinv.
    now rewrite Nat.div_mul.
  - rewrite perm_inv_eq_iff by auto_perm.
    now rewrite infunc_of_edgefunc_twice'.
Qed.

Lemma edgeperm_idx_linv_snd n f k
  (Hf : edgepermutation n f) (Hk : k < n) :
  edgeperm_idx n f (snd (f k)) = k.
Proof.
  unfold edgeperm_idx.
  enough (Hinv : perm_inv (n * 2) (infunc_of_edgefunc f) (snd (f k)) = k * 2 + 1).
  - rewrite Hinv.
    rewrite Nat.div_add_l; simpl; lia.
  - rewrite perm_inv_eq_iff by auto_perm.
    now rewrite infunc_of_edgefunc_twice_plus'.
Qed.


Lemma edgeperm_offset_linv_fst n f k
  (Hf : edgepermutation n f) (Hk : k < n) :
  edgeperm_offset n f (fst (f k)) = 0.
Proof.
  unfold edgeperm_offset.
  enough (Hinv : perm_inv (n * 2) (infunc_of_edgefunc f) (fst (f k)) = k * 2).
  - rewrite Hinv.
    now rewrite Nat.Div0.mod_mul.
  - rewrite perm_inv_eq_iff by auto_perm.
    now rewrite infunc_of_edgefunc_twice'.
Qed.

Lemma edgeperm_offset_linv_snd n f k
  (Hf : edgepermutation n f) (Hk : k < n) :
  edgeperm_offset n f (snd (f k)) = 1.
Proof.
  unfold edgeperm_offset.
  enough (Hinv : perm_inv (n * 2) (infunc_of_edgefunc f) (snd (f k)) = k * 2 + 1).
  - rewrite Hinv.
    rewrite mod_add_l; simpl; lia.
  - rewrite perm_inv_eq_iff by auto_perm.
    now rewrite infunc_of_edgefunc_twice_plus'.
Qed.

(* TODO: FIXME: Make a theory of edge_mem and edge_memb and restate this that way *)
Lemma edgeperm_idx_eq_iff_fst_or_snd n f k l 
  (Hf : edgepermutation n f) (Hk : k < n * 2) (Hl : l < n) :
  edgeperm_idx n f k = l <-> k = fst (f l) \/ k = snd (f l).
Proof.
  split.
  - intros Heq%(f_equal f).
    pose proof (edgeperm_idx_rinv_edge_eq n f k Hf Hk) as Hee.
    hnf in Hee; simpl in Hee.
    rewrite Heq in Hee.
    lia.
  - intros [-> | ->].
    + now apply edgeperm_idx_linv_fst.
    + now apply edgeperm_idx_linv_snd.
Qed.

Lemma edgeperm_idx_eq_edge_mem n f k l 
  (Hf : edgepermutation n f) (Hk : k < n * 2) (Hl : l < n) :
  edgeperm_idx n f k = l -> edge_mem k (f l) = true.
Proof.
  rewrite edgeperm_idx_eq_iff_fst_or_snd by auto.
  intros [-> | ->]; unfold edge_mem; bdestructΩ'.
Qed.

Lemma edge_mem_iff_edgeperm_idx_eqb n f k l 
  (Hf : edgepermutation n f) (Hk : k < n * 2) (Hl : l < n) :
  edge_mem k (f l) = (edgeperm_idx n f k =? l).
Proof.
  apply eq_true_iff_eq.
  unfold edge_mem.
  rewrite orb_true_iff, 3!Nat.eqb_eq.
  now rewrite edgeperm_idx_eq_iff_fst_or_snd.
Qed.

Lemma infunc_of_edgefunc_compose_pairmap_l (f : nat -> nat * nat) g k : 
  infunc_of_edgefunc (pairmap g ∘ f) k = 
  (g ∘ infunc_of_edgefunc f) k.
Proof.
  unfold compose, infunc_of_edgefunc, pairmap.
  pose proof (Nat.mod_upper_bound k 2 ltac:(lia)) as Hkmod2.
  destruct (ltac:(lia) : k mod 2 = 0 \/ k mod 2 = 1) as [-> | ->];
  reflexivity.
Qed.

Lemma infunc_of_edgefunc_compose_pairmap_l_perm_eq (f : nat -> nat * nat) g n : 
  perm_eq n (infunc_of_edgefunc (pairmap g ∘ f)) 
    (g ∘ infunc_of_edgefunc f).
Proof.
  hnf; auto using infunc_of_edgefunc_compose_pairmap_l.
Qed.

Lemma edgeperm_partner_eq_iff_edgeperm_idx_eq n f k l 
  (Hf : edgepermutation n f) (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) : 
  edgeperm_idx n f k = edgeperm_idx n f l <-> edgeperm_partner n f k = l.
Proof.
  split.
  - intros Hidx_eq.
    rewrite edgeperm_partner_defn by auto.
    assert (Hoff : 1 - edgeperm_offset n f k = edgeperm_offset n f l). 1: {
      pose proof (edgeperm_offset_bounded n f k).
      pose proof (edgeperm_offset_bounded n f l).
      enough (edgeperm_offset n f k <> edgeperm_offset n f l) by lia.
      intros Hoffeq.
      apply Hkl.
      apply (permutation_is_injective (n * 2) (edgeperm_partner n f));
      [auto_biperm..|].
      rewrite 2!edgeperm_partner_defn by auto.
      congruence.
    }
    rewrite Hoff, Hidx_eq.
    rewrite edgeperm_idx_offset_eq by auto.
    apply perm_inv_is_rinv_of_permutation; auto_biperm.
  - intros <-.
    now rewrite edgeperm_idx_edgeperm_partner.
Qed.

Lemma edgeperm_idx_compose_r n f g 
  (Hf : edgepermutation n f) (Hg : permutation n g) :
  perm_eq (n * 2) (edgeperm_idx n (f ∘ g)) 
  (perm_inv n g ∘ edgeperm_idx n f).
Proof.
  change (edgeperm_idx n (f ∘ g)) with ((fun a => a / 2) ∘ perm_inv (n * 2) (infunc_of_edgefunc (f ∘ g))).
  rewrite (infunc_of_edgefunc_compose_r n f g).
  rewrite perm_inv_compose by auto_perm.
  rewrite tensor_perms_inv, idn_inv by auto_perm.
  intros a Ha.
  unfold compose.
  unfold edgeperm_idx.
  rewrite tensor_perms_defn by auto_perm.
  rewrite Nat.div_add_l, mod_div by easy.
  lia.
Qed.

Lemma edgepermutation_compose_r n f g : 
  edgepermutation n f -> permutation n g ->
  edgepermutation n (f ∘ g).
Proof.
  pose proof (edgepermutation_compose_r_iff n f g).
  tauto.
Qed.

#[export] Hint Resolve edgepermutation_compose_r : perm_db.

Lemma edgeperm_offset_compose_r n f g 
  (Hf : edgepermutation n f) (Hg : permutation n g) :
  perm_eq (n * 2) (edgeperm_offset n (f ∘ g)) 
  (edgeperm_offset n f).
Proof.
  change (edgeperm_offset n (f ∘ g)) with ((fun a => a mod 2) ∘ perm_inv (n * 2) (infunc_of_edgefunc (f ∘ g))).
  rewrite (infunc_of_edgefunc_compose_r n f g).
  rewrite perm_inv_compose by auto_perm.
  rewrite tensor_perms_inv, idn_inv by auto_perm.
  intros a Ha.
  unfold compose.
  unfold edgeperm_offset.
  rewrite tensor_perms_defn by auto_perm.
  now rewrite mod_add_l, Nat.Div0.mod_mod by easy.
Qed.

Lemma edgeperm_partner_compose_r n f g 
  (Hf : edgepermutation n f) (Hg : permutation n g) :
  perm_eq (n * 2) (edgeperm_partner n (f ∘ g)) 
    (edgeperm_partner n f).
Proof.
  intros a Ha.
  unfold edgeperm_partner.
  rewrite edgeperm_idx_compose_r by easy.
  unfold compose.
  now rewrite perm_inv_is_rinv_of_permutation by auto_perm.
Qed.








Lemma ZX_of_edgeperm_compose_pairmap_l n (f : nat -> nat * nat) g : 
  ZX_of_edgeperm n (pairmap g ∘ f) = 
  ZX_of_infunc n (g ∘ infunc_of_edgefunc f).
Proof.
  unfold ZX_of_edgeperm.
  apply ZX_of_infunc_eq_of_perm_eq.
  intros k Hk.
  apply infunc_of_edgefunc_compose_pairmap_l.
Qed.

Add Parametric Morphism f : (pairmap f) with signature
  edge_eq ==> edge_eq as pairmap_edge_eq_mor.
Proof.
  intros ij ij'.
  unfold edge_eq.
  simpl.
  intros [[-> ->] | [-> ->]]; auto.
Qed.





Definition rshift (i : nat) (k : nat) : nat := k + i.

Definition lshift (i : nat) (k : nat) : nat := k - i.

Lemma rshift_defn : rshift = fun k l => Nat.add l k.
Proof. reflexivity. Qed.

Lemma lshift_defn : lshift = fun k l => Nat.sub l k.
Proof. reflexivity. Qed.

Lemma rshift_defn_perm n i : perm_eq n (rshift i) (fun k => k + i).
Proof. reflexivity. Qed.

Lemma rshift_defn_perm' n i : perm_eq n (rshift i) (fun k => i + k).
Proof. intros k _; apply Nat.add_comm. Qed.

Lemma lshift_defn_perm n i : perm_eq n (lshift i) (fun k => k - i).
Proof. reflexivity. Qed.


Lemma lshift_rshift_permutation n f m (Hf : permutation n f) 
  (Hfm : perm_bounded m f) : 
  permutation (n - m) (lshift m ∘ f ∘ rshift m).
Proof.
  bdestruct (m <=? n).
  - rewrite rshift_defn_perm'.
    now apply perm_shift_upper_permutation_of_lower_bounded.
  - replace (n - m) with 0 by lia.
    apply permutation_0.
Qed.

Definition swap_to_0_perm (k n : nat) :=
  fun a => if a <? k then a + 1 else if a =? k then 0 else a.

Definition swap_from_0_perm (k n : nat) :=
  fun a => if a =? 0 then k else if a <? k + 1 then a - 1 else a.

Lemma swap_to_0_perm_defn k n : 
  swap_to_0_perm k n = 
  fun a => if a <? k then a + 1 else if a =? k then 0 else a.
Proof.
  reflexivity.
Qed.

Lemma swap_from_0_perm_defn k n : 
  swap_from_0_perm k n = 
  fun a => if a =? 0 then k else if a <? k + 1 then a - 1 else a.
Proof.
  reflexivity.
Qed.

Lemma swap_to_0_perm_defn' k n (Hk : k < n) : 
  perm_eq n 
    (swap_to_0_perm k n)
    (stack_perms (k + 1) (n - (k + 1)) (big_swap_perm k 1) idn).
Proof.
  intros a Ha.
  unfold swap_to_0_perm.
  bdestruct (a <? k + 1).
  - rewrite stack_perms_left by lia.
    bdestruct (a <? k).
    + rewrite big_swap_perm_left; lia.
    + if_true_lia. 
      rewrite big_swap_perm_right; lia.
  - rewrite stack_perms_right by lia.
    if_false_lia.
    if_false_lia.
    lia.
Qed.

Lemma swap_from_0_perm_defn' k n (Hk : k < n) : 
  perm_eq n 
    (swap_from_0_perm k n)
    (stack_perms (k + 1) (n - (k + 1)) (big_swap_perm 1 k) idn).
Proof.
  intros a Ha.
  unfold swap_from_0_perm.
  bdestruct (a <? k + 1).
  - rewrite stack_perms_left by lia.
    bdestruct (a =? 0).
    + rewrite big_swap_perm_left; lia.
    + rewrite big_swap_perm_right; lia.
  - rewrite stack_perms_right by lia.
    if_false_lia.
    lia.
Qed.


Lemma swap_to_0_perm_permutation k n (Hk : k < n) :
  permutation n (swap_to_0_perm k n).
Proof.
  rewrite swap_to_0_perm_defn' by easy.
  auto_perm.
Qed.

Lemma swap_from_0_perm_permutation k n (Hk : k < n) :
  permutation n (swap_from_0_perm k n).
Proof.
  rewrite swap_from_0_perm_defn' by easy.
  auto_perm.
Qed.

#[export] Hint Resolve swap_to_0_perm_permutation 
  swap_from_0_perm_permutation : perm_db.

Lemma swap_to_0_perm_WF k n (Hk : k < n) : 
  WF_Perm n (swap_to_0_perm k n).
Proof.
  rewrite swap_to_0_perm_defn.
  intros a Ha; bdestructΩ'.
Qed.

Lemma swap_from_0_perm_WF k n (Hk : k < n) : 
  WF_Perm n (swap_from_0_perm k n).
Proof.
  rewrite swap_from_0_perm_defn.
  intros a Ha; bdestructΩ'.
Qed.

#[export] Hint Resolve swap_to_0_perm_WF 
  swap_from_0_perm_WF : WF_Perm_db.


Lemma swap_to_0_perm_inv' k n (Hk : k < n) : 
  perm_inv' n (swap_to_0_perm k n) = swap_from_0_perm k n.
Proof.
  eq_by_WF_perm_eq n.
  rewrite swap_to_0_perm_defn', swap_from_0_perm_defn' by easy.
  set (s := n - (k + 1)).
  replace n with (k + 1 + (n - (k + 1))) by lia.
  cleanup_perm_inv.
Qed.

Lemma swap_from_0_perm_inv' k n (Hk : k < n) : 
  perm_inv' n (swap_from_0_perm k n) = swap_to_0_perm k n.
Proof.
  eq_by_WF_perm_eq n.
  rewrite swap_to_0_perm_defn', swap_from_0_perm_defn' by easy.
  set (s := n - (k + 1)).
  replace n with (k + 1 + (n - (k + 1))) by lia.
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite swap_to_0_perm_inv' swap_from_0_perm_inv' 
  using lia : perm_inv_db.

Lemma swap_to_0_perm_inv k n (Hk : k < n) : 
  perm_eq n (perm_inv n (swap_to_0_perm k n)) (swap_from_0_perm k n).
Proof.
  rewrite <- perm_inv'_eq.
  cleanup_perm_inv.
Qed.

Lemma swap_from_0_perm_inv k n (Hk : k < n) : 
  perm_eq n (perm_inv n (swap_from_0_perm k n)) (swap_to_0_perm k n).
Proof.
  rewrite <- perm_inv'_eq.
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite swap_to_0_perm_inv swap_from_0_perm_inv
  using lia : perm_inv_db.





Lemma contract_perm_definition n f a (Hf : perm_inj n f) (Ha : a < n): 
  perm_eq (n - 1) (contract_perm f a)
  (lshift 1 ∘ (swap_to_0_perm (f a) n ∘ f ∘ swap_from_0_perm a n) ∘ rshift 1).
Proof.
  intros k Hk.
  pose proof (Hf k a).
  pose proof (Hf (k + 1) a).
  unfold contract_perm.
  unfold compose.
  rewrite rshift_defn, swap_from_0_perm_defn, swap_to_0_perm_defn, lshift_defn.
  replace_bool_lia (k + 1 =? 0) false.
  rewrite Nat.add_sub.
  bdestructΩ'.
Qed.


Lemma swap_to_0_perm_small k n a : a < k -> 
  swap_to_0_perm k n a = a + 1.
Proof.
  intros Ha.
  rewrite swap_to_0_perm_defn.
  now if_true_lia.
Qed.

Lemma swap_to_0_perm_same k n : 
  swap_to_0_perm k n k = 0.
Proof.
  rewrite swap_to_0_perm_defn.
  bdestructΩ'.
Qed.

Lemma swap_to_0_perm_diag k n a : a = k ->
  swap_to_0_perm k n a = 0.
Proof.
  intros ->.
  apply swap_to_0_perm_same.
Qed.

Lemma swap_to_0_perm_large k n a : k < a -> 
  swap_to_0_perm k n a = a.
Proof.
  intros Ha.
  rewrite swap_to_0_perm_defn.
  bdestructΩ'.
Qed.

Lemma swap_from_0_perm_0 k n : 
  swap_from_0_perm k n 0 = k.
Proof.
  rewrite swap_from_0_perm_defn.
  bdestructΩ'.
Qed.

Lemma swap_to_0_perm_of_eq_0 k n a : a = 0 ->
  swap_from_0_perm k n a = k.
Proof.
  intros ->.
  apply swap_from_0_perm_0.
Qed.

Lemma swap_from_0_perm_small k n a : 0 < a -> a < k + 1 -> 
  swap_from_0_perm k n a = a - 1.
Proof.
  intros Hapos Ha.
  rewrite swap_from_0_perm_defn.
  bdestructΩ'.
Qed.

Lemma swap_from_0_perm_large k n a : k < a -> 
  swap_from_0_perm k n a = a.
Proof.
  intros Ha.
  rewrite swap_from_0_perm_defn.
  bdestructΩ'.
Qed.

Lemma swap_from_to_0_perm k n : 
  swap_to_0_perm k n ∘ swap_from_0_perm k n = idn.
Proof.
  apply functional_extensionality.
  intros a.
  unfold compose.
  rewrite swap_to_0_perm_defn, swap_from_0_perm_defn.
  bdestructΩ'.
Qed.

Lemma swap_to_from_0_perm k n : 
  swap_from_0_perm k n ∘ swap_to_0_perm k n = idn.
Proof.
  apply functional_extensionality.
  intros a.
  unfold compose.
  rewrite swap_to_0_perm_defn, swap_from_0_perm_defn.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite swap_to_from_0_perm swap_from_to_0_perm : perm_inv_db.

Lemma swap_from_to_0_perm_eq k n : 
  perm_eq n (swap_to_0_perm k n ∘ swap_from_0_perm k n) idn.
Proof.
  cleanup_perm_inv.
Qed.

Lemma swap_to_from_0_perm_eq k n : 
  perm_eq n (swap_from_0_perm k n ∘ swap_to_0_perm k n) idn.
Proof.
  cleanup_perm_inv.
Qed.




Lemma swap_to_0_1_perm_defn_alt k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_eq n (swap_to_0_1_perm k l n)
  (stack_perms 1 (n - 1) idn (swap_to_0_perm (max k l - 1) (n - 1)) ∘
    swap_to_0_perm (min k l) n).
Proof.
  rewrite swap_to_0_1_perm_defn.
  intros a Ha.
  unfold compose.
  bdestruct (a =? min k l); 
  [|bdestruct (a =? max k l); 
  [|bdestruct (a <? min k l); 
  [|bdestruct (a <? max k l)]]].
  - subst a.
    rewrite swap_to_0_perm_same.
    rewrite stack_perms_left; lia.
  - subst a. 
    rewrite swap_to_0_perm_large by lia.
    rewrite stack_perms_right by lia.
    rewrite swap_to_0_perm_same; lia.
  - rewrite swap_to_0_perm_small by lia.
    rewrite stack_perms_right by lia.
    rewrite swap_to_0_perm_small by lia.
    lia.
  - rewrite swap_to_0_perm_large by lia.
    rewrite stack_perms_right by lia.
    rewrite swap_to_0_perm_small by lia.
    lia.
  - rewrite swap_to_0_perm_large by lia.
    rewrite stack_perms_right by lia.
    rewrite swap_to_0_perm_large by lia.
    lia.
Qed.


Lemma swap_to_0_1_perm_defn_alt' k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_eq n (swap_to_0_1_perm k l n)
  (stack_perms 2 (n - 2) swap_2_perm idn ∘ 
    stack_perms 1 (n - 1) idn (swap_to_0_perm (min k l) (n - 1)) ∘
    swap_to_0_perm (max k l) n).
Proof.
  rewrite stack_perms_WF_idn by auto_perm.
  rewrite swap_to_0_1_perm_defn.
  intros a Ha.
  unfold compose.
  bdestruct (a =? min k l); 
  [|bdestruct (a =? max k l); 
  [|bdestruct (a <? min k l); 
  [|bdestruct (a <? max k l)]]].
  - rewrite swap_to_0_perm_small by lia.
    rewrite stack_perms_right by lia.
    rewrite swap_to_0_perm_diag by lia.
    reflexivity.
  - subst a.
    rewrite swap_to_0_perm_same.
    rewrite stack_perms_left by lia; reflexivity.
  - rewrite swap_to_0_perm_small by lia.
    rewrite stack_perms_right by lia.
    rewrite swap_to_0_perm_small by lia.
    rewrite swap_2_perm_WF; lia.
  - rewrite swap_to_0_perm_small by lia.
    rewrite stack_perms_right by lia.
    rewrite swap_to_0_perm_large by lia.
    rewrite swap_2_perm_WF; lia.
  - rewrite swap_to_0_perm_large by lia.
    rewrite stack_perms_right by lia.
    rewrite swap_to_0_perm_large by lia.
    rewrite swap_2_perm_WF; lia.
Qed.

Lemma lshift_stack_perms_to_idn n m f g (Hf : perm_bounded n f) : 
  perm_eq (n + m) (lshift n ∘ stack_perms n m f g) 
    (lshift n ∘ stack_perms n m idn g).
Proof.
  intros a Ha.
  unfold compose, lshift.
  bdestruct (a <? n).
  - rewrite 2!stack_perms_left by lia.
    specialize (Hf a).
    lia.
  - rewrite 2!stack_perms_right by lia; lia.
Qed.

Lemma lshift_absorb_perm k f (Hf : perm_bounded k f) (HWFf : WF_Perm k f) : 
  lshift k ∘ f = lshift k.
Proof.
  apply functional_extensionality.
  intros a.
  unfold compose.
  bdestruct (a <? k).
  - specialize (Hf a).
    unfold lshift.
    lia.
  - now rewrite HWFf by lia.
Qed.

Lemma swap_to_0_1_perm_defn_alt'' k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_eq n (lshift 2 ∘ swap_to_0_1_perm k l n)
  (lshift 2 ∘
    stack_perms 1 (n - 1) idn 
      (swap_to_0_perm (if k <? l then l - 1 else l) (n - 1)) ∘
    swap_to_0_perm (k) n).
Proof.
  bdestruct (k <? l).
  - pose proof (swap_to_0_1_perm_defn_alt l k n Hl Hk ltac:(lia)) as Hrw.
    rewrite Nat.max_l, Nat.min_r in Hrw by lia.
    rewrite swap_to_0_1_perm_comm.
    now rewrite Hrw.
  - pose proof (swap_to_0_1_perm_defn_alt' k l n Hk Hl ltac:(lia)) as Hrw.
    rewrite Nat.max_l, Nat.min_r in Hrw by lia.
    rewrite Hrw.
    rewrite Combinators.compose_assoc.
    rewrite (stack_perms_WF_idn 2) by auto_perm.
    rewrite ###comp_r -> lshift_absorb_perm by auto_perm.
    reflexivity.
Qed.


Lemma swap_from_0_1_perm_defn_alt k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_eq n (swap_from_0_1_perm k l n)
  (swap_from_0_perm (min k l) n ∘ 
    stack_perms 1 (n - 1) idn (swap_from_0_perm (max k l - 1) (n - 1))).
Proof.
  perm_eq_by_inv_inj (swap_to_0_1_perm k l n) n.
  - rewrite <- swap_from_0_1_perm_inv' by auto.
    cleanup_perm_inv.
  - rewrite swap_to_0_1_perm_defn_alt by auto.
    rewrite !Combinators.compose_assoc.
    rewrite ###comp_r -> @stack_perms_compose by auto_perm.
    cleanup_perm_inv.
Qed.

Lemma swap_from_0_1_perm_defn_alt' k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_eq n (swap_from_0_1_perm k l n)
  (swap_from_0_perm (max k l) n ∘
    stack_perms 1 (n - 1) idn (swap_from_0_perm (min k l) (n - 1)) ∘
    stack_perms 2 (n - 2) swap_2_perm idn).
Proof.
  perm_eq_by_inv_inj (swap_to_0_1_perm k l n) n.
  - rewrite <- swap_from_0_1_perm_inv' by auto.
    cleanup_perm_inv.
  - rewrite swap_to_0_1_perm_defn_alt' by auto.
    rewrite !Combinators.compose_assoc.
    rewrite (stack_perms_WF_idn 2) by auto_perm.
    unfold swap_2_perm.
    rewrite ###comp_r -> swap_perm_invol by lia.
    rewrite ###comp_r -> @stack_perms_compose by auto_perm.
    cleanup_perm_inv.
Qed.


Lemma lshift_lshift k l n : 
  perm_eq n (lshift k ∘ lshift l) (lshift (k + l)).
Proof.
  intros a _.
  unfold compose, lshift.
  lia.
Qed.

Lemma lshift_lshift_eq k l : 
  lshift k ∘ lshift l = lshift (k + l).
Proof.
  apply functional_extensionality; intros a.
  unfold compose, lshift.
  lia.
Qed.

Lemma rshift_rshift k l n : 
  perm_eq n (rshift k ∘ rshift l) (rshift (k + l)).
Proof.
  intros a _.
  unfold compose, rshift.
  lia.
Qed.

Lemma rshift_rshift_eq k l : 
  rshift k ∘ rshift l = rshift (k + l).
Proof.
  apply functional_extensionality; intros a.
  unfold compose, rshift.
  lia.
Qed.

Lemma lshift_rshift_diag k n : 
  perm_eq n (lshift k ∘ rshift k) (idn).
Proof.
  intros a _.
  unfold compose, rshift, lshift.
  lia.
Qed.

Lemma lshift_rshift_ge k l n : l <= k ->
  perm_eq n (lshift k ∘ rshift l) (lshift (k - l)).
Proof.
  intros Hkl a _.
  unfold compose, rshift, lshift.
  lia.
Qed.

Lemma lshift_rshift_le k l n : k <= l ->
  perm_eq n (lshift k ∘ rshift l) (rshift (l - k)).
Proof.
  intros Hkl a _.
  unfold compose, rshift, lshift.
  lia.
Qed.

Lemma rshift_lshift_diag k n : 
  perm_eq n (rshift k ∘ lshift k) (max k).
Proof.
  intros a _.
  unfold compose, rshift, lshift.
  lia.
Qed.

Lemma rshift_lshift_ge k l n : l <= k ->
  perm_eq n (rshift k ∘ lshift l) (rshift (k - l) ∘ max l).
Proof.
  intros Hkl a _.
  unfold compose, rshift, lshift.
  lia.
Qed.

Lemma rshift_lshift_le k l n : k <= l ->
  perm_eq n (rshift k ∘ lshift l) (max k ∘ lshift (l - k)).
Proof.
  intros Hkl a _.
  unfold compose, rshift, lshift.
  lia.
Qed.

Lemma perm_eq_rshift_simplify_r k n f g : 
  perm_eq n f g -> 
  perm_eq (n - k) (f ∘ rshift k) (g ∘ rshift k).
Proof.
  intros Hfg.
  intros a Ha.
  unfold compose, rshift.
  apply Hfg; lia.
Qed.

Lemma stack_perms_rshift n m f g : 
  perm_eq m (stack_perms n m f g ∘ rshift n) (rshift n ∘ g).
Proof.
  intros a Ha.
  unfold compose, rshift.
  rewrite stack_perms_right by lia.
  now rewrite Nat.add_sub.
Qed.

Lemma compose_rshift_l n m f : 
  perm_eq m (rshift n ∘ f) (stack_perms n m idn f ∘ rshift n).
Proof.
  now rewrite stack_perms_rshift.
Qed.

(* TODO: FIXME: This is ad-hoc. I'd love a better mechanism for size-changing permutations. *)
Add Parametric Morphism k n : (fun f => f ∘ rshift k) with signature
  perm_eq n ==> perm_eq (n - k) as compose_rshift_r_proper.
Proof.
  intros f g Hfg.
  intros a Ha.
  apply Hfg.
  unfold rshift.
  lia.
Qed.

(* FIXME: Move *)
Lemma swap_from_0_perm_not_0 k n a (Ha : a <> 0) : 
  swap_from_0_perm k n a = if a <? k + 1 then a - 1 else a.
Proof.
  bdestruct (a <? k + 1).
  - now rewrite swap_from_0_perm_small by lia.
  - now rewrite swap_from_0_perm_large by lia.
Qed.

(* Lemma swap_from_0_perm_rshift_double_comm k l n 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_eq (n - 1 - 1) 
    (swap_from_0_perm (k - 1) n ∘ rshift 1 ∘ swap_from_0_perm l (n - 1) ∘ rshift 1)
    (swap_from_0_perm (l - 1) n ∘ rshift 1 ∘ swap_from_0_perm k (n - 1) ∘ rshift 1).

    swap_from_0_perm (Init.Nat.max k l) n
   ∘ stack_perms 1 (n - 1) idn
       (swap_from_0_perm (Init.Nat.min k l) (n - 1))
   (swap_from_0_perm (Init.Nat.min k l) n
      ∘ stack_perms 1 (n - 1) idn
          (swap_from_0_perm (Init.Nat.max k l - 1) (n - 1))))
Proof.
  intros a Ha.
  unfold compose.
  unfold rshift.
  rewrite !swap_from_0_perm_not_0 by lia.
  bdestructΩ'. *)

Lemma lshift_bounded k n : perm_bounded n (lshift k).
Proof.
  intros a Ha.
  unfold lshift.
  lia.
Qed.

#[export] Hint Resolve lshift_bounded : perm_bounded_db.

Lemma contract_biperm_definition n f k l (Hf : permutation n f) 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_eq (n - 2) (contract_biperm k l f)
  (lshift 2 ∘ (swap_to_0_1_perm (f k) (f l) n ∘ f ∘ swap_from_0_1_perm k l n) ∘ rshift 2).
Proof.
  rewrite contract_biperm_to_min_max.

  symmetry.
  rewrite <- !Combinators.compose_assoc.
  erewrite compose_rshift_r_proper; [|
  now rewrite swap_from_0_1_perm_defn_alt' by auto_perm].
  rewrite <- !Combinators.compose_assoc.
  rewrite ###perm_l -> stack_perms_rshift, compose_idn_r.
  symmetry.

  replace (n - 2) with (n - 1 - 1) by lia.
  rewrite contract_perm_definition by auto_perm.

  change (rshift 2) with (rshift (1 + 1)).
  rewrite <- rshift_rshift.
  rewrite <- !Combinators.compose_assoc.
  erewrite compose_rshift_r_proper; [|
  now rewrite contract_perm_definition by auto_perm].
  rewrite <- !Combinators.compose_assoc.

  apply perm_eq_rshift_simplify_r.
  rewrite !Combinators.compose_assoc.
  rewrite compose_rshift_l.
  rewrite <- !Combinators.compose_assoc.
  apply perm_eq_rshift_simplify_r.
  rewrite 2!(Combinators.compose_assoc _ f).
  rewrite 2!(Combinators.compose_assoc _ (f ∘ _)).
  apply compose_perm_eq_proper_l; 
  [|unfold on_predicate_relation_l; split; auto_perm].
  assert (Hor : k < l \/ l < k) by lia.
  by_symmetry Hor. 2:{
    intros a b H.
    rewrite Nat.max_comm, Nat.min_comm, swap_to_0_1_perm_comm.
    intros; now apply H.
  }
  rewrite Nat.max_r, Nat.min_l by lia.
  rewrite swap_to_0_1_perm_comm.
  assert (Hfkl : f k <> f l) by now apply (permutation_neq Hf); lia.
  rewrite swap_to_0_1_perm_defn_alt'' by auto_perm.
  apply compose_perm_eq_proper_l; [| split; auto_perm].
  unfold contract_perm.
  if_true_lia.
  intros a Ha.
  unfold compose.
  rewrite stack_perms_defn by lia.
  unfold lshift, swap_to_0_perm.
  bdestruct (f k <? f l);
  [replace_bool_lia (f l <? f k) false | replace_bool_lia (f l <? f k) true];
  bdestructΩ'.
Qed.









Lemma compose_arb_cup_ZX_of_infunc_eq_base edges f
  (Hf : permutation (edges * 2) f) 
  (Hf0 : f 0 = 0) (Hf1 : f 1 = 1) : 
  zx_arb_cup 0 1 (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1) (lshift 2 ∘ f ∘ rshift 2)).
Proof.
  unfold compose, lshift, rshift.
  bdestruct (edges =? 0). 1:{
    (* Trivial case *)
    subst.
    simpl.
    rewrite 2!ZX_of_infunc_0, compose_empty_r, cast_id.
    unfold zx_arb_cup.
    simpl.
    rewrite zx_of_perm_0.
    unfold zx_padded_cap.
    simpl.
    rewrite compose_empty_r.
    rewrite <- Z_0_0_is_empty.
    reflexivity.
  }
  unfold ZX_of_infunc.
  rewrite <- cast_compose_r_eq_mid, <- compose_assoc.
  rewrite zx_arb_cup_compose_zx_of_perm_r by auto_perm.
  rewrite (perm_inv_eq_of_eq Hf0 Hf), (perm_inv_eq_of_eq Hf1 Hf) by lia.
  rewrite compose_assoc.
  rewrite cast_contract_eq, cast_compose_distribute.
  apply compose_simplify_casted_abs; [lia | intros ?..].
  - rewrite cast_contract_eq.
    rewrite cast_zx_of_perm.
    ereflexivity.
    apply zx_of_perm_eq_of_perm_eq.
    unfold contract_biperm.
    if_true_lia.
    intros k Hk.
    unfold contract_perm at 1.
    if_false_lia.
    unfold contract_perm at 2.
    rewrite Hf0, Hf1.
    simpl.
    unfold contract_perm.
    if_false_lia.
    rewrite Hf1.
    rewrite ltb_1.
    rewrite <- Nat.add_assoc; simpl.
    rewrite Nat.eqb_sym.
    rewrite <- (perm_inv_eqb_iff Hf) by lia.
    rewrite (perm_inv_eq_of_eq Hf0 Hf) by lia.
    if_false_lia.
    lia.
  - rewrite zx_arb_cup_0_1.
    rewrite cast_compose_r.
    rewrite 2!cast_contract_eq.
    rewrite (n_stack_renumber (ltac:(lia) : edges = 1 + (edges - 1))).
    rewrite nstack_split, n_stack_1.
    rewrite cast_contract_eq, cast_id_eq.
    apply ZX_prop_by_mat_prop.
    simpl_cast_semantics.
    cbn [ZX_semantics].
    simpl_cast_semantics.
    rewrite 2!stack_semantics.
    restore_dims.
    rewrite kron_mixed_product' by restore_dims_tac.
    rewrite <- compose_semantics.
    rewrite cup_cap.
    rewrite n_wire_semantics.
    restore_dims.
    rewrite Mmult_1_r by auto_wf.
    now rewrite kron_1_l by auto_wf.
  Unshelve.
  all: lia.
Qed.

(* FIXME: I think there's something like this elsewhere? *)
Lemma perm_eq_dim_pos_intro n f g : 
  (n <> 0 -> perm_eq n f g) ->
  perm_eq n f g.
Proof.
  intros H.
  bdestruct (n =? 0).
  - subst n.
    apply perm_eq_0.
  - auto.
Qed.

(* FIXME: Move *)

Lemma swap_to_0_1_perm_0_1 n : 
  perm_eq n (swap_to_0_1_perm 0 1 n) idn.
Proof.
  rewrite swap_to_0_1_perm_defn.
  intros a Ha.
  simpl.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_0_1_eq n : 
  swap_to_0_1_perm 0 1 n = idn.
Proof.
  eq_by_WF_perm_eq n.
  apply swap_to_0_1_perm_0_1.
Qed.

Lemma swap_from_0_1_perm_0_1_eq n : 
  swap_from_0_1_perm 0 1 n = idn.
Proof.
  eq_by_WF_perm_eq n.
  apply swap_from_0_1_perm_0_1.
Qed.

Lemma helper_compose_arb_cup_ZX_of_infunc_eq_base edges f
  (Hf : permutation (edges * 2) f) 
  (Hf0 : f 0 = 0) (Hf1 : f 1 = 1) : 
  perm_eq (edges * 2 - 2) (lshift 2 ∘ f ∘ rshift 2)
    (contract_biperm 0 1 f).
Proof.
  apply perm_eq_dim_pos_intro; intros Hedges.
  rewrite contract_biperm_definition by auto_perm.
  rewrite Hf0, Hf1.
  rewrite swap_to_0_1_perm_0_1_eq, swap_from_0_1_perm_0_1_eq.
  reflexivity.
Qed.


Lemma compose_arb_cup_ZX_of_infunc_eq_base_gen edges f
  (Hf : permutation (edges * 2) f) 
  (Hf0 : f 0 < 2) (Hf1 : f 1 < 2) : 
  zx_arb_cup 0 1 (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1) (lshift 2 ∘ f ∘ rshift 2)).
Proof.
  unfold lshift, rshift, compose.
  bdestruct (edges =? 0). 1:{
    (* Trivial case *)
    subst.
    simpl.
    rewrite 2!ZX_of_infunc_0, compose_empty_r, cast_id.
    unfold zx_arb_cup.
    simpl.
    rewrite zx_of_perm_0.
    unfold zx_padded_cap.
    simpl.
    rewrite compose_empty_r.
    rewrite <- Z_0_0_is_empty.
    reflexivity.
  }
  assert (Hf01 : f 0 = 0 /\ f 1 = 1 \/ f 0 = 1 /\ f 1 = 0). 1: {
    enough (f 0 <> f 1) by lia.
    apply (permutation_neq Hf); lia.
  }
  destruct Hf01 as [Hfeq | Hfswap];
  [now apply compose_arb_cup_ZX_of_infunc_eq_base|].
  rewrite <- (ZX_of_infunc_absorb_conditional_swaps_r edges f 
    (fun k => k =? 0) Hf).
  rewrite compose_arb_cup_ZX_of_infunc_eq_base.
  - apply cast_simplify.
    ereflexivity.
    apply ZX_of_infunc_eq_of_perm_eq.
    intros k Hk.
    unfold compose, lshift, rshift.
    rewrite conditional_swaps_0_eq by lia.
    now rewrite swap_2_perm_WF by lia.
  - auto_perm.
  - unfold compose.
    rewrite conditional_swaps_0_eq by lia.
    apply Hfswap.
  - unfold compose.
    rewrite conditional_swaps_0_eq by lia.
    apply Hfswap.
Qed.

Lemma helper_compose_arb_cup_ZX_of_infunc_eq_base_gen edges f
  (Hf : permutation (edges * 2) f) 
  (Hf0 : f 0 < 2) (Hf1 : f 1 < 2) : 
  perm_eq (edges * 2 - 2) (lshift 2 ∘ f ∘ rshift 2)
    (contract_biperm 0 1 f).
Proof.
  apply perm_eq_dim_pos_intro; intros Hedges.
  assert (Hf01 : f 0 = 0 /\ f 1 = 1 \/ f 0 = 1 /\ f 1 = 0). 1: {
    enough (f 0 <> f 1) by lia.
    apply (permutation_neq Hf); lia.
  }
  destruct Hf01 as [Hfeq | [Hf0' Hf1']];
  [now apply helper_compose_arb_cup_ZX_of_infunc_eq_base|].

  rewrite contract_biperm_definition by auto_perm.
  rewrite Hf0', Hf1'.
  rewrite swap_to_0_1_perm_comm, swap_to_0_1_perm_0_1_eq, 
    swap_from_0_1_perm_0_1_eq.
  reflexivity.
Qed.

Lemma helper_compose_arb_cup_ZX_of_infunc_eq_base_gen' edges f
  (Hf : permutation (edges * 2) f) 
  (Hf0 : f 0 < 2) (Hf1 : f 1 < 2) : 
  perm_eq ((edges - 1) * 2) (lshift 2 ∘ f ∘ rshift 2)
    (contract_biperm 0 1 f).
Proof. 
  rewrite Nat.mul_sub_distr_r. 
  now apply helper_compose_arb_cup_ZX_of_infunc_eq_base_gen.
Qed.


Lemma compose_arb_cup_ZX_of_infunc_eq_base_gen' edges f
  (Hf : permutation (edges * 2) f) 
  (Hf0 : f 0 < 2) (Hf1 : f 1 < 2) : 
  zx_arb_cup 0 1 (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1) (contract_biperm 0 1 f)).
Proof.
  rewrite <- helper_compose_arb_cup_ZX_of_infunc_eq_base_gen' by easy.
  now apply compose_arb_cup_ZX_of_infunc_eq_base_gen.
Qed.


Lemma subresult_compose_arb_cup_ZX_of_infunc_eq_gen edges f
  (Hf : permutation (edges * 2) f) k l
  (Hk : k < edges * 2) (Hl : l < edges * 2)
  (Hf01 : edge_eq (f 0, f 1) (k, l)) : 
  perm_eq (edges * 2 - 2) 
    (lshift 2 ∘ (fun k' => (if k' <? Init.Nat.min k l then k' + 2
    else if k' <? Init.Nat.max k l then k' + 1 else k')) ∘ f ∘ rshift 2)
    (lshift 2 ∘ swap_to_0_1_perm k l (edges * 2) ∘ f ∘ rshift 2).
Proof.
  assert (Hf01neq : f 0 <> f 1) by (apply (permutation_neq Hf); lia).
  assert (Hkl : k <> l). 1: {
    hnf in Hf01.
    simpl in Hf01.
    lia.
  }
  symmetry;
  erewrite compose_rshift_r_proper;
  [|now rewrite swap_to_0_1_perm_defn];
  symmetry.
  rewrite !Combinators.compose_assoc.
  apply compose_perm_eq_proper_r.
  intros i Hi.
  unfold compose, rshift.
  pose proof (permutation_is_injective _ f Hf (i + 2) 0 ltac:(lia) ltac:(lia)).
  pose proof (permutation_is_injective _ f Hf (i + 2) 1 ltac:(lia) ltac:(lia)).
  symmetry.
  hnf in Hf01; simpl in Hf01.
  if_false_lia.
  if_false_lia.
  reflexivity.
Qed.

Lemma compose_arb_cup_ZX_of_infunc_eq_gen edges f
  (Hf : permutation (edges * 2) f) k l
  (Hk : k < edges * 2) (Hl : l < edges * 2)
  (Hf01 : edge_eq (f 0, f 1) (k, l)) : 
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1) 
  (lshift 2 ∘ (fun k' => (if k' <? Init.Nat.min k l then k' + 2
  else if k' <? Init.Nat.max k l then k' + 1 else k')) ∘ f ∘ rshift 2)).
Proof.
  assert (Hf01neq : f 0 <> f 1) by (apply (permutation_neq Hf); lia).
  assert (Hkl : k <> l). 1: {
    hnf in Hf01.
    simpl in Hf01.
    lia.
  }
  rewrite compose_arb_cup_ZX_of_infunc_defn by auto_perm.
  rewrite compose_arb_cup_ZX_of_infunc_eq_base_gen.
  - apply cast_simplify.
    ereflexivity.
    apply ZX_of_infunc_eq_of_perm_eq.
    rewrite Nat.mul_sub_distr_r.
    now rewrite subresult_compose_arb_cup_ZX_of_infunc_eq_gen.
  - auto_perm.
  - unfold compose.
    apply swap_to_0_1_perm_small; [easy..|].
    hnf in Hf01; simpl in Hf01.
    lia.
  - unfold compose.
    apply swap_to_0_1_perm_small; [easy..|].
    hnf in Hf01; simpl in Hf01.
    lia.
Qed.

(* FIXME: Move *)
Lemma contract_biperm_edge_eq_rw {ij kl} (Heq : edge_eq ij kl) f : 
  contract_biperm (fst ij) (snd ij) f = contract_biperm (fst kl) (snd kl) f.
Proof.
  pose proof Heq as [-> | ->]%edge_eq_defn_l.
  - reflexivity.
  - apply contract_biperm_comm.
Qed.

Lemma swap_to_0_1_perm_edge_eq_rw {ij kl} (Heq : edge_eq ij kl) n : 
  swap_to_0_1_perm (fst ij) (snd ij) n = swap_to_0_1_perm (fst kl) (snd kl) n.
Proof.
  pose proof Heq as [-> | ->]%edge_eq_defn_l.
  - reflexivity.
  - apply swap_to_0_1_perm_comm.
Qed.

Lemma swap_from_0_1_perm_edge_eq_rw {ij kl} (Heq : edge_eq ij kl) n : 
  swap_from_0_1_perm (fst ij) (snd ij) n = swap_from_0_1_perm (fst kl) (snd kl) n.
Proof.
  pose proof Heq as [-> | ->]%edge_eq_defn_l.
  - reflexivity.
  - apply swap_from_0_1_perm_comm.
Qed.

Lemma helper_compose_arb_cup_ZX_of_infunc_eq_gen edges f
  (Hf : permutation (edges * 2) f) k l
  (Hk : k < edges * 2) (Hl : l < edges * 2)
  (Hf01 : edge_eq (f 0, f 1) (k, l)) : 
  perm_eq (edges * 2 - 2) 
    (lshift 2 ∘ (fun k' => (if k' <? Init.Nat.min k l then k' + 2
    else if k' <? Init.Nat.max k l then k' + 1 else k')) ∘ f ∘ rshift 2)
    (contract_biperm 0 1 f).
Proof.
  rewrite subresult_compose_arb_cup_ZX_of_infunc_eq_gen by easy.
  rewrite contract_biperm_definition by auto_perm.
  rewrite (swap_to_0_1_perm_edge_eq_rw Hf01).
  rewrite swap_from_0_1_perm_0_1_eq.
  reflexivity.
Qed.

Lemma helper_compose_arb_cup_ZX_of_infunc_eq_gen' edges f
  (Hf : permutation (edges * 2) f) k l
  (Hk : k < edges * 2) (Hl : l < edges * 2)
  (Hf01 : edge_eq (f 0, f 1) (k, l)) : 
  perm_eq ((edges - 1) * 2) 
    (lshift 2 ∘ (fun k' => (if k' <? Init.Nat.min k l then k' + 2
    else if k' <? Init.Nat.max k l then k' + 1 else k')) ∘ f ∘ rshift 2)
    (contract_biperm 0 1 f).
Proof. 
  rewrite Nat.mul_sub_distr_r.
  now apply helper_compose_arb_cup_ZX_of_infunc_eq_gen.
Qed.

Lemma compose_arb_cup_ZX_of_infunc_eq_gen' edges f
  (Hf : permutation (edges * 2) f) k l
  (Hk : k < edges * 2) (Hl : l < edges * 2)
  (Hf01 : edge_eq (f 0, f 1) (k, l)) : 
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1) (contract_biperm 0 1 f)).
Proof.
  rewrite compose_arb_cup_ZX_of_infunc_eq_gen by easy.
  now rewrite helper_compose_arb_cup_ZX_of_infunc_eq_gen'.
Qed.

Lemma infunc_of_edgefunc_plus_twice k f n : 
  infunc_of_edgefunc f (n + 2 * k) = infunc_of_edgefunc (f ∘ rshift k) n.
Proof.
  unfold infunc_of_edgefunc.
  unfold compose, rshift.
  f_equal.
  - f_equal.
    rewrite Nat.mul_comm.
    rewrite Nat.div_add; lia.
  - rewrite Nat.mul_comm.
    rewrite Nat.Div0.mod_add; lia.
Qed.

Lemma compose_arb_cup_ZX_of_edgeperm_eq_base_gen n k l f 
  (Hf : edgepermutation n f)
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l)
  (Hf0 : edge_eq (f 0) (k, l)) : 
  zx_arb_cup k l (n * 2) ⟷ ZX_of_edgeperm n f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r n 1 2)) eq_refl (
  ZX_of_edgeperm (n - 1) 
  (pairmap (lshift 2 ∘ fun k' => (if k' <? Init.Nat.min k l then k' + 2
  else if k' <? Init.Nat.max k l then k' + 1 else k')) ∘ 
  (fun a => f (a + 1)))).
Proof.
  unfold ZX_of_edgeperm at 1.
  rewrite compose_arb_cup_ZX_of_infunc_eq_gen by auto_perm + assumption.
  apply cast_simplify.
  rewrite ZX_of_edgeperm_compose_pairmap_l.
  ereflexivity.
  apply ZX_of_infunc_eq_of_perm_eq.
  rewrite Combinators.compose_assoc.
  apply compose_perm_eq_proper_r.
  intros i Hi.
  unfold compose, rshift.
  now rewrite (infunc_of_edgefunc_plus_twice 1).
Qed.

Definition stack_funcs n m (f g : nat -> nat) : nat -> nat :=
  fun k =>
  if n + m <=? k then k else
  if k <? n then f k else g k.

Lemma stack_funcs_WF n m f g : WF_Perm (n + m) (stack_funcs n m f g).
Proof. apply make_WF_Perm_WF. Qed.

#[export] Hint Resolve stack_funcs_WF : WF_Perm_db.

#[export] Hint Extern 3 (WF_Perm ?nm (stack_funcs ?n ?m ?f ?g)) => 
  apply (WF_Perm_change_dims nm (n + m) (stack_funcs n m f g) ltac:(lia)); 
  apply stack_funcs_WF : WF_Perm_db.

Lemma stack_funcs_defn n m f g : 
  perm_eq (n + m) 
    (stack_funcs n m f g) 
    (fun k => if k <? n then f k else g k).
Proof. apply make_WF_Perm_perm_eq. Qed.

Lemma stack_funcs_defn' nm n m f g : nm = n + m ->
  perm_eq nm 
    (stack_funcs n m f g) 
    (fun k => if k <? n then f k else g k).
Proof. intros ->. apply make_WF_Perm_perm_eq. Qed.


Add Parametric Morphism n m : (stack_funcs n m) with signature 
  perm_eq n ==> perm_eq (n + m) ==> eq as stack_funcs_perm_eq_proper.
Proof.
  intros f f' Hf g g' Hg.
  eq_by_WF_perm_eq _.
  rewrite 2!stack_funcs_defn.
  intros k Hk.
  bdestruct_one.
  - now apply Hf.
  - now apply Hg.
Qed.


(* FIXME: Move *)
#[export] Instance pointwise_eq_perm_eq_subrelation n : 
  subrelation (Morphisms.pointwise_relation nat eq) (perm_eq n).
Proof.
  easy.
Qed.

Lemma stack_funcs_left n m f g k (Hk : k < n) : 
  stack_funcs n m f g k = f k.
Proof.
  unfold stack_funcs; bdestructΩ'.
Qed.

Lemma stack_funcs_right n m f g k : n <= k -> k < n + m ->
  stack_funcs n m f g k = g k.
Proof.
  intros; unfold stack_funcs; bdestructΩ'.
Qed.

Lemma stack_perms_shift_defn n m f g : 
  stack_perms n m f g = 
  stack_funcs n m f (rshift n ∘ g ∘ lshift n).
Proof.
  eq_by_WF_perm_eq (n + m).
  rewrite stack_perms_defn, stack_funcs_defn.
  reflexivity.
Qed.

Lemma stack_funcs_rshift n m f g : 
  perm_eq m (stack_funcs n m f g ∘ rshift n)
    (g ∘ rshift n).
Proof.
  intros k Hk.
  unfold compose, rshift.
  now rewrite stack_funcs_right by lia.
Qed.

Lemma stack_funcs_lshift n m f g : n <> 0 ->
  perm_eq (n + m) (stack_funcs n m f g ∘ lshift m)
    (f ∘ lshift m).
Proof.
  intros Hn k Hk.
  unfold compose, lshift.
  now rewrite stack_funcs_left by lia.
Qed.

(* FIXME: Move this, and move its lemma from way above to this section *)
Lemma helper_base_compose_arb_cup_ZX_of_infunc_base edges f : 
  perm_eq (edges * 2 - 2) (fun a => if a =? 0 then f a - 2 else f (a + 2) - 2) 
  (lshift 2 ∘ f ∘ stack_funcs 1 (edges * 2 - 3) idn (rshift 2)).
Proof.
  apply perm_eq_dim_pos_intro; intros Hedges.
  unfold compose, lshift, rshift, stack_funcs.
  intros a Ha.
  symmetry.
  if_false_lia.
  bdestructΩ'.
Qed.

Lemma stack_funcs_idn_r n m f : 
  stack_funcs n m f idn = make_WF_Perm n f.
Proof.
  eq_by_WF_perm_eq (n + m).
  - apply WF_Perm_monotone with n; lia + auto_perm.
  - rewrite stack_funcs_defn.
    intros k Hk.
    bdestruct_one.
    + now rewrite make_WF_Perm_perm_eq by lia.
    + now rewrite make_WF_Perm_WF by lia.
Qed.

Lemma swap_from_0_1_perm_succ_r k n (Hk : S k < n) : 
  swap_from_0_1_perm k (S k) n =
  stack_funcs 2 (n - 2) (rshift k) 
    (stack_funcs (k + 2) (n - 2 - k) (lshift 2) idn).
Proof.
  eq_by_WF_perm_eq n.
  rewrite swap_from_0_1_perm_defn.
  intros a Ha.
  bdestruct (a <? 2).
  - rewrite stack_funcs_left by lia.
    unfold rshift.
    bdestructΩ'.
  - if_false_lia; if_false_lia.
    rewrite stack_funcs_right by lia.
    rewrite stack_funcs_idn_r.
    unfold compose, make_WF_Perm, lshift.
    bdestructΩ'.
Qed.

Lemma stack_funcs_rshift_gen n m f g k (Hk : k <= n) : 
  perm_eq (n - k + m) (stack_funcs n m f g ∘ rshift k)
    (stack_funcs (n - k) m (f ∘ rshift k) (g ∘ rshift k)).
Proof.
  intros a Ha.
  unfold compose, rshift, stack_funcs.
  if_false_lia.
  symmetry.
  if_false_lia.
  bdestructΩ'.
Qed.

Lemma swap_from_0_1_perm_succ_r_rshift k n (Hk : S k < n) : 
  perm_eq (n - 2) 
    (swap_from_0_1_perm k (S k) n ∘ rshift 2)
    (stack_funcs k (n - (k + 2)) idn (rshift 2)).
Proof.
  rewrite stack_funcs_defn' by lia.
  rewrite swap_from_0_1_perm_succ_r by lia.
  replace (n - 2 - k) with (n - (k + 2)) by lia.
  rewrite stack_funcs_rshift.
  replace (n - 2) with (k + 2 - 2 + (n - (k + 2))) at 1 by lia.
  rewrite stack_funcs_rshift_gen by lia.
  rewrite stack_funcs_defn.
  intros a Ha.
  unfold compose, rshift, lshift.
  now rewrite 2!Nat.add_sub.
Qed.



Lemma helper_compose_arb_cup_ZX_of_infunc_base edges f 
  (Hedges : 1 < edges) 
  (Hf : permutation (edges * 2) f) 
  (Hf1 : f 1 = 0) (Hf2 : f 2 = 1) : 
  perm_eq (edges * 2 - 2) (fun a => if a =? 0 then f a - 2 else f (a + 2) - 2) 
  (contract_biperm 1 2 f).
Proof.
  rewrite helper_base_compose_arb_cup_ZX_of_infunc_base.
  rewrite contract_biperm_definition by auto_perm.
  rewrite Hf1, Hf2.
  rewrite swap_to_0_1_perm_0_1_eq, compose_idn_l.
  rewrite !Combinators.compose_assoc.
  rewrite swap_from_0_1_perm_succ_r_rshift by lia.
  reflexivity.
Qed.

(* FIXME: Move *)
Lemma rshift_lshift_cancel_fully_general n k f 
  (Hf : forall a, a < n -> k <= f a) : 
  perm_eq n (rshift k ∘ lshift k ∘ f) f.
Proof.
  intros a Ha.
  unfold rshift, lshift, compose.
  specialize (Hf a).
  lia.
Qed.

Lemma rshift_lshift_cancel_compose_rshift_gen n k f 
  (Hf : forall a, k <= a -> a < n -> k <= f a) : 
  perm_eq (n - k) (rshift k ∘ lshift k ∘ f ∘ rshift k) (f ∘ rshift k).
Proof.
  rewrite (Combinators.compose_assoc (rshift k)).
  apply rshift_lshift_cancel_fully_general.
  unfold compose, rshift.
  intros a Ha.
  apply Hf; lia.
Qed.

Lemma rshift_lshift_cancel_compose_rshift_perm n k f
  (Hf : permutation n f) (Hfk : perm_bounded k f) (Hk : k <= n) : 
  perm_eq (n - k) (rshift k ∘ lshift k ∘ f ∘ rshift k) (f ∘ rshift k).
Proof.
  apply rshift_lshift_cancel_compose_rshift_gen.
  intros a Hak Han.
  replace a with (k + (a - k)) by lia.
  apply (perm_shift_upper_bounded_below_of_lower_bounded n); auto_perm.
Qed.

Lemma rshift_lshift_2_cancel_compose_rshift_of_idn n f
  (Hf : permutation n f) (Hn : 2 <= n) (Hf0 : f 0 < 2) (Hf1 : f 1 < 2) : 
  perm_eq (n - 2) (rshift 2 ∘ lshift 2 ∘ f ∘ rshift 2) (f ∘ rshift 2).
Proof.
  apply rshift_lshift_cancel_compose_rshift_perm; [auto_perm | | auto_perm].
  now by_perm_cell.
Qed.

Lemma swap_from_0_1_perm_0 n k l (Hn : n <> 0) :
  swap_from_0_1_perm k l n 0 = min k l.
Proof.
  unfold swap_from_0_1_perm.
  if_false_lia.
  reflexivity.
Qed.

Lemma swap_from_0_1_perm_1 n k l (Hn : 1 < n) :
  swap_from_0_1_perm k l n 1 = max k l.
Proof.
  unfold swap_from_0_1_perm.
  if_false_lia.
  reflexivity.
Qed.

Lemma swap_to_0_1_perm_left n k l (Hk : k < n) (Hkl : k <> l) :
  swap_to_0_1_perm k l n k = if k <? l then 0 else 1.
Proof.
  unfold swap_to_0_1_perm.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_right n k l (Hl : l < n) (Hkl : k <> l) :
  swap_to_0_1_perm k l n l = if k <? l then 1 else 0.
Proof.
  unfold swap_to_0_1_perm.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_max n k l (Hk : k < n) (Hl : l < n) (Hkl : k <> l) :
  swap_to_0_1_perm k l n (max k l) = 1.
Proof.
  unfold swap_to_0_1_perm.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_min n k l (Hk : k < n) :
  swap_to_0_1_perm k l n (min k l) = 0.
Proof.
  unfold swap_to_0_1_perm.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_min' n k l (Hl : l < n) :
  swap_to_0_1_perm k l n (min k l) = 0.
Proof.
  unfold swap_to_0_1_perm.
  bdestructΩ'.
Qed.

(* FIXME: Move *)
Lemma contract_biperm_compose n f g k l 
  (Hf : permutation n f) (Hg : permutation n g)
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) :
  perm_eq (n - 2) (contract_biperm k l (f ∘ g))
    (contract_biperm (g k) (g l) f ∘ contract_biperm k l g).
Proof.
  assert (Hor : k < l \/ l < k) by lia.
  by_symmetry Hor. 2:{ 
    intros a b IH Hb Ha Hba.
    rewrite 2!(contract_biperm_comm _ b).
    rewrite (contract_biperm_comm _ (g b)).
    now apply IH.
  }

  assert (Hgkl : g k <> g l) by now apply (permutation_neq Hg).

  rewrite contract_biperm_definition by auto_perm.
  rewrite (contract_biperm_definition n f) by auto_perm.
  rewrite (contract_biperm_definition n g) by auto_perm.
  symmetry.
  (* set (sg := (swap_to_0_1_perm (g k) (g l) n ∘ g ∘ swap_from_0_1_perm k l n)). *)
  rewrite Combinators.compose_assoc.
  rewrite <- 2!(Combinators.compose_assoc _ _ (rshift 2)).
  (* rewrite <- !Combinators.compose_assoc. *)
  (* subst sg. *)
  rewrite rshift_lshift_2_cancel_compose_rshift_of_idn; 
    [| auto_perm | lia | |].
  - rewrite !Combinators.compose_assoc.
    rewrite ###comp_r -> swap_from_to_0_1_perm_inverse by auto_perm.
    reflexivity.
  - unfold compose.
    rewrite swap_from_0_1_perm_0 by lia.
    rewrite Nat.min_l by lia.
    rewrite swap_to_0_1_perm_left by auto_perm.
    bdestructΩ'.
  - unfold compose.
    rewrite swap_from_0_1_perm_1 by lia.
    rewrite Nat.max_r by lia.
    rewrite swap_to_0_1_perm_right by auto_perm.
    bdestructΩ'.
Qed.

Lemma contract_biperm_compose_change_dims n f g k l 
  (Hf : permutation n f) (Hg : permutation n g)
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) m : m = n - 2 ->
  perm_eq m (contract_biperm k l (f ∘ g))
    (contract_biperm (g k) (g l) f ∘ contract_biperm k l g).
Proof.
  intros ->.
  now apply contract_biperm_compose.
Qed.

(* FIXME: Move *)
Lemma swap_perm_defn_eq a b n (Ha : a < n) (Hb : b < n) : 
  swap_perm a b n = (fun k => if k =? a then b else if k =? b then a else k).
Proof.
  eq_by_WF_perm_eq n; [intros k Hk; bdestructΩ'|].
  intros k Hk.
  now apply swap_perm_defn.
Qed.

Lemma contract_biperm_swap_perm_r n f k l 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  contract_biperm k l (f ∘ swap_perm k l n) = 
  contract_biperm k l f.
Proof.
  assert (Hor : k < l \/ l < k) by lia.
  by_symmetry Hor. 2:{ 
    intros a b IH Hb Ha Hba.
    rewrite 2!(contract_biperm_comm _ b).
    rewrite swap_perm_comm.
    now apply IH.
  }

  apply functional_extensionality.
  intros a.
  rewrite 2!contract_biperm_to_min_max.
  rewrite Nat.min_l, Nat.max_r by lia.
  unfold contract_perm, compose.
  replace_bool_lia (k <? l) true.
  rewrite swap_perm_left, swap_perm_right by lia.
  bdestruct (a <? k); [| bdestruct (a + 1 <? l)].
  - replace_bool_lia (a <? l) true.
    rewrite swap_perm_neither by lia.
    bdestruct (f k =? f l); [now replace -> (f k)|].
    bdestruct (f k <? f l); 
    [replace_bool_lia (f l <? f k) false | replace_bool_lia (f l <? f k) true];
    bdestructΩ'.
  - rewrite swap_perm_neither by lia.
    bdestruct (f k =? f l); [now replace -> (f k)|].
    bdestruct (f k <? f l); 
    [replace_bool_lia (f l <? f k) false | replace_bool_lia (f l <? f k) true];
    bdestructΩ'.
  - rewrite swap_perm_neither by lia.
    bdestruct (f k =? f l); [now replace -> (f k)|].
    bdestruct (f k <? f l); 
    [replace_bool_lia (f l <? f k) false | replace_bool_lia (f l <? f k) true];
    bdestructΩ'.
Qed.

Lemma contract_biperm_idn k l : 
  contract_biperm k l idn = idn.
Proof.
  rewrite contract_biperm_to_min_max.
  now rewrite 2!contract_perm_idn.
Qed.

Lemma contract_biperm_swap_perm n k l 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) :
  contract_biperm k l (swap_perm k l n) = idn.
Proof.
  rewrite <- (compose_idn_l (swap_perm _ _ _)).
  rewrite contract_biperm_swap_perm_r by lia.
  apply contract_biperm_idn.
Qed.

(* FIXME: Move *)
Lemma edge_eq_min_max k l : 
  edge_eq (min k l, max k l) (k, l).
Proof.
  hnf; simpl; lia.
Qed.

Lemma edge_eq_max_min k l : 
  edge_eq (max k l, min k l) (k, l).
Proof.
  hnf; simpl; lia.
Qed.

(* FIXME: Move *)
Lemma f_edge_equal_pairmap f p q : 
  edge_eq p q ->
  edge_eq (pairmap f p) (pairmap f q).
Proof.
  intros [-> | ->]%edge_eq_defn_l;
  [reflexivity | apply edge_eq_swap].
Qed.

Lemma edge_eq_pair_defn i j k l :
  edge_eq (i, j) (k, l) <-> 
  (i = k /\ j = l) \/ (i = l /\ j = k).
Proof. reflexivity. Qed.

Lemma edge_eq_pair_defn' i j k l :
  edge_eq (i, j) (k, l) -> 
  (i = k /\ j = l) \/ (i = l /\ j = k).
Proof. easy. Qed.

Lemma f_edge_equal f i j k l : 
  edge_eq (i, j) (k, l) ->
  edge_eq (f i, f j) (f k, f l).
Proof.
  intros [[-> ->] | [-> ->]]%edge_eq_pair_defn;
  [reflexivity | apply edge_eq_swap].
Qed.

Lemma compose_arb_cup_ZX_of_infunc_eq_full edges f k l 
  (Hf : permutation (edges * 2) f)
  (Hk : k < edges * 2) (Hl : l < edges * 2) (Hkl : k <> l)
  (Hfeq : perm_inv (edges * 2) f k / 2 = perm_inv (edges * 2) f l / 2) :
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1) (contract_biperm 0 1 (
    f ∘ tensor_perms edges 2 
        (swap_from_0_perm (perm_inv (edges * 2) f k / 2) edges) idn))
  ).
Proof.
  assert (perm_inv (edges * 2) f k / 2 < edges) by (
    apply Nat.Div0.div_lt_upper_bound; rewrite Nat.mul_comm;
    auto_perm). 
  
  rewrite <- (ZX_of_infunc_absorb_tensor_perms_r edges f
    (swap_from_0_perm (perm_inv (edges * 2) f k / 2) edges)) by auto_perm.
  rewrite compose_arb_cup_ZX_of_infunc_eq_gen';
  [reflexivity | auto_perm..|].
  unfold compose.
  rewrite 2!tensor_perms_defn by lia.
  rewrite 2!swap_from_0_perm_0.
  change (0 mod 2) with 0.
  change (1 mod 2) with 1.
  replace (k, l) 
    with (f (perm_inv (edges * 2) f k), f (perm_inv (edges * 2) f l))
    by cleanup_perm_inv.
  apply f_edge_equal.
  rewrite (Nat.div_mod_eq (perm_inv (edges * 2) f l) 2).
  rewrite (Nat.div_mod_eq (perm_inv (edges * 2) f k) 2) at 3.
  rewrite 2!(Nat.mul_comm 2).
  rewrite <- Hfeq.
  apply f_edge_equal.
  rewrite edge_eq_pair_defn.
  pose proof (Nat.mod_upper_bound (perm_inv (edges * 2) f k) 2 ltac:(lia)).
  pose proof (Nat.mod_upper_bound (perm_inv (edges * 2) f l) 2 ltac:(lia)).

  enough (perm_inv (edges * 2) f k mod 2 
    <> perm_inv (edges * 2) f l mod 2) by lia.
  assert (Hneq: perm_inv (edges * 2) f k <> perm_inv (edges * 2) f l) 
    by (apply (permutation_neq (n:=edges * 2)); auto_perm).
  pose proof (Nat.div_mod_eq (perm_inv (edges * 2) f l) 2).
  pose proof (Nat.div_mod_eq (perm_inv (edges * 2) f k) 2).
  congruence.
Qed. 




Lemma compose_arb_cup_ZX_of_infunc_neq_base edges f k l
  (Hk : k < edges * 2) (Hl : l < edges * 2) (Hkl : k < l)
  (Hedges : 1 < edges) 
  (Hf : permutation (edges * 2) f) 
  (Hf1 : f 1 = k) (Hf2 : f 2 = l) : 
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1) (fun a => 
    let k' := if a =? 0 then a else a + 2 in 
    (if f k' <? Init.Nat.min k l then f k' + 2
      else if f k' <? Init.Nat.max k l then f k' + 1 else f k') - 2)).
Proof.
  assert (Hf'k : perm_inv (edges * 2) f k = 1) by
    (rewrite <- Hf1; auto_perm).
  assert (Hf'l : perm_inv (edges * 2) f l = 2) by
    (rewrite <- Hf2; auto_perm).
  assert (k <> l) by lia.
  cbv delta [zx_arb_cup zx_arb_cap] beta.
  cbn delta [ZXCore.transpose] iota.
  rewrite zx_of_perm_transpose by auto_perm.
  rewrite swap_from_0_1_perm_inv', compose_assoc, 
    ZX_of_infunc_compose_perm_of_zx_l by auto_perm.
  rewrite <- zx_arb_cap_0_1_alt, zx_arb_cap_transpose.
  rewrite compose_arb_cup_ZX_of_infunc_base; [|now auto_perm..| |].
  - apply cast_simplify.
    apply ZX_of_infunc_simplify.
    intros a Ha.
    bdestruct_one.
    + subst a.
      unfold compose.
      rewrite swap_to_0_1_perm_neither; [reflexivity|auto_perm|..|auto];
      subst; apply (permutation_neq Hf); lia.
    + unfold compose.
      rewrite swap_to_0_1_perm_neither; [reflexivity|auto_perm|..|auto];
      subst; apply (permutation_neq Hf); lia.
  - unfold compose.
    rewrite Hf1.
    rewrite swap_to_0_1_perm_left_min; lia.
  - unfold compose.
    rewrite Hf2.
    rewrite swap_to_0_1_perm_right_max; lia.
Qed.


Lemma helper_base_compose_arb_cup_ZX_of_infunc_neq_base edges f k l
  (Hedges : 1 < edges) 
  (Hf : permutation (edges * 2) f) 
  (Hf1 : f 1 = k) (Hf2 : f 2 = l) : 
  perm_eq (edges * 2 - 2) 
    (fun a => 
    let k' := if a =? 0 then a else a + 2 in 
    (if f k' <? Init.Nat.min k l then f k' + 2
      else if f k' <? Init.Nat.max k l then f k' + 1 else f k') - 2)
    ((lshift 2 ∘ swap_to_0_1_perm k l (edges * 2) ∘ f 
      ∘ stack_funcs 1 (edges * 2 - 3) idn (rshift 2))).
Proof.
  assert (k <> l) by (subst k l; apply (permutation_neq Hf); lia).
  rewrite (Combinators.compose_assoc f).
  rewrite stack_funcs_defn' by lia.
  intros a Ha.
  unfold compose.
  rewrite ltb_1.
  unfold lshift.
  f_equal.
  unfold rshift.
  rewrite swap_to_0_1_perm_defn by (bdestruct_one; auto_perm).
  bdestruct (k <? l).
  - rewrite Nat.min_l, Nat.max_r by lia.
    subst k l.
    rewrite !(permutation_eqb_iff _ _ Hf) by (try bdestruct_one; lia).
    symmetry.
    bdestruct (a =? 0); [subst; reflexivity|].
    if_false_lia.
    if_false_lia.
    reflexivity.
  - rewrite Nat.min_r, Nat.max_l by lia.
    subst k l.
    rewrite !(permutation_eqb_iff _ _ Hf) by (try bdestruct_one; lia).
    symmetry.
    bdestruct (a =? 0); [subst; reflexivity|].
    if_false_lia.
    if_false_lia.
    reflexivity.
Qed.

Lemma helper_compose_arb_cup_ZX_of_infunc_neq_base edges f k l
  (Hedges : 1 < edges) 
  (Hf : permutation (edges * 2) f) 
  (Hf1 : f 1 = k) (Hf2 : f 2 = l) : 
  perm_eq (edges * 2 - 2) 
    (fun a => 
    let k' := if a =? 0 then a else a + 2 in 
    (if f k' <? Init.Nat.min k l then f k' + 2
      else if f k' <? Init.Nat.max k l then f k' + 1 else f k') - 2)
    (contract_biperm 1 2 f).
Proof.
  rewrite helper_base_compose_arb_cup_ZX_of_infunc_neq_base by easy.
  rewrite contract_biperm_definition by auto_perm.
  rewrite !Combinators.compose_assoc.
  rewrite swap_from_0_1_perm_succ_r_rshift by lia.
  now rewrite Hf1, Hf2.
Qed.

Lemma compose_arb_cup_ZX_of_infunc_neq_base_gen edges f k l
  (Hk : k < edges * 2) (Hl : l < edges * 2) (Hkl : k <> l)
  (Hedges : 1 < edges) 
  (Hf : permutation (edges * 2) f) 
  (Hf1 : f 1 = k) (Hf2 : f 2 = l) : 
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1) (fun a => 
    let k' := 
      if a =? 0 then if k <? l then 0 else 3 else
      if a =? 1 then if k <? l then 3 else 0 else a + 2 in 
    (if f k' <? Init.Nat.min k l then f k' + 2
      else if f k' <? Init.Nat.max k l then f k' + 1 else f k') - 2)).
Proof.
  bdestruct (k <? l).
  1: {
    rewrite compose_arb_cup_ZX_of_infunc_neq_base by easy.
    apply cast_simplify.
    ereflexivity.
    apply ZX_of_infunc_eq_of_perm_eq.
    intros a Ha.
    destruct a; [|destruct a]; reflexivity.
  }
  rewrite zx_arb_cup_comm.
  pose proof (permutation_of_le_permutation_WF swap_2_perm 2 edges
    ltac:(lia) ltac:(auto_perm) ltac:(auto_perm)) as Hpadswap.
  rewrite <- (ZX_of_infunc_absorb_conditional_swaps_r edges f 
    (fun i => i <? 2) Hf).
  rewrite <- (ZX_of_infunc_absorb_tensor_perms_r edges _ 
    (swap_2_perm)) by auto_perm.
  rewrite compose_arb_cup_ZX_of_infunc_neq_base;
    [|lia + auto_perm.. | | ];
    [| unfold compose; destruct edges; [lia|destruct edges; [lia|]]; cbn;
      rewrite big_stack_perms_constant_alt by lia; cbn; assumption..].
  apply cast_simplify.
  ereflexivity.
  apply ZX_of_infunc_eq_of_perm_eq.
  intros i Hi.
  bdestruct (i =? 0); [|bdestruct (i =? 1)].
  - cbn zeta.
    subst i.
    unfold compose.
    destruct edges; [lia|destruct edges; [lia|]]; cbn;
    rewrite big_stack_perms_constant_alt by lia; cbn.
    rewrite Nat.min_comm, Nat.max_comm.
    reflexivity.
  - subst i.
    cbn delta -[Nat.ltb] beta match iota zeta.
    unfold compose.
    destruct edges; [lia|destruct edges; [lia|]]; cbn;
    rewrite big_stack_perms_constant_alt by lia; cbn.
    rewrite Nat.min_comm, Nat.max_comm.
    reflexivity.
  - cbn zeta.
    replace ((f ∘ big_stack_perms edges (fun _ : nat => 2)
        (fun i0 => if i0 <? 2 then swap_2_perm else idn)
        ∘ tensor_perms edges 2 swap_2_perm idn) (i + 2))
      with (f (i + 2)). 2:{ 
      unfold compose.
      f_equal.
      rewrite tensor_perms_defn by lia.
      replace (i + 2) with (1 * 2 + i) by lia.
      rewrite mod_add_l, Nat.div_add_l by lia.
      assert (i / 2 <> 0) by (rewrite Nat.div_small_iff; lia).
      rewrite swap_2_perm_WF by lia.
      replace ((1 + i / 2) * 2 + i mod 2) with (1 * 2 + i) by 
        (pose proof (Nat.div_mod_eq i 2); lia).
      rewrite big_stack_perms_constant_alt by lia.
      rewrite mod_add_l, Nat.div_add_l by lia.
      if_false_lia.
      pose proof (Nat.div_mod_eq i 2); lia.
    }
    rewrite Nat.min_comm, Nat.max_comm.
    reflexivity.
Qed.

(* FIXME: Move *)
Lemma swap_perm_eqb_left_iff a b n k : a < n -> b < n -> 
  (swap_perm a b n k =? a) = (k =? b).
Proof.
  intros Ha Hb.
  bdestruct (k <? n).
  - rewrite <- (swap_perm_right a b n Hb) at 2.
    apply (permutation_eqb_iff (n := n)); auto_perm.
  - rewrite swap_perm_WF by lia.
    bdestructΩ'.
Qed.

Lemma swap_perm_eqb_right_iff a b n k : a < n -> b < n -> 
  (swap_perm a b n k =? b) = (k =? a).
Proof.
  intros Ha Hb.
  bdestruct (k <? n).
  - rewrite <- (swap_perm_left a b n Ha) at 2.
    apply (permutation_eqb_iff (n := n)); auto_perm.
  - rewrite swap_perm_WF by lia.
    bdestructΩ'.
Qed.

Lemma swap_perm_of_big a b n k : a < k -> b < k -> 
  swap_perm a b n k = k.
Proof.
  intros Ha Hb.
  unfold swap_perm.
  bdestructΩ'.
Qed.



Lemma helper_base_compose_arb_cup_ZX_of_infunc_neq_base_gen edges f k l
  (Hedges : 1 < edges) 
  (Hf : permutation (edges * 2) f) 
  (Hf1 : f 1 = k) (Hf2 : f 2 = l) : 
  perm_eq (edges * 2 - 2) (fun a => 
    let k' := 
      if a =? 0 then if k <? l then 0 else 3 else
      if a =? 1 then if k <? l then 3 else 0 else a + 2 in 
    (if f k' <? Init.Nat.min k l then f k' + 2
      else if f k' <? Init.Nat.max k l then f k' + 1 else f k') - 2)
    (lshift 2 ∘ swap_to_0_1_perm k l (edges * 2) ∘ f
      ∘ stack_funcs 1 (edges * 2 - 3) idn (rshift 2)
      ∘ (if k <? l then idn else (swap_perm 0 1 (edges * 2 - 2)))).
Proof.
  assert (Hk : k < edges * 2) by (subst k; auto_perm).
  assert (Hl : l < edges * 2) by (subst l; auto_perm).
  assert (Hkl : k <> l) by (subst k l; apply (permutation_neq Hf); lia).
  bdestruct (k <? l).
  - rewrite compose_idn_r.
    rewrite <- helper_base_compose_arb_cup_ZX_of_infunc_neq_base by easy.
    intros a Ha.
    bdestruct (a =? 0); [subst; easy|].
    now replace (if a =? 1 then 3 else a + 2) with (a + 2) by bdestructΩ'.
  - rewrite (Combinators.compose_assoc f).
    rewrite stack_funcs_defn' by lia.
    intros a Ha.
    unfold compose.
    rewrite ltb_1.
    unfold lshift.
    f_equal.
    unfold rshift.
    rewrite swap_perm_eqb_left_iff by lia.
    replace (if a =? 1
      then swap_perm 0 1 (edges * 2 - 2) a
      else swap_perm 0 1 (edges * 2 - 2) a + 2) with 
      (if a =? 0 then 3 else if a =? 1 then 0 else a + 2). 2:{
      bdestruct (a <? 2).
      + bdestruct (a =? 0).
        * subst a.
          simpl.
          rewrite swap_perm_left by lia.
          reflexivity.
        * replace a with 1 by lia.
          if_true_lia.
          now rewrite swap_perm_right by lia.
      + do 2 if_false_lia.
        now rewrite swap_perm_of_big by lia.
    }
    rewrite swap_to_0_1_perm_defn by (bdestructΩ'; auto_perm).
    rewrite Nat.min_r, Nat.max_l by lia.
    subst k l.
    rewrite !(permutation_eqb_iff _ _ Hf) by (bdestructΩ'; lia).
    symmetry.
    bdestruct (a =? 0); [subst; reflexivity|].
    bdestruct (a =? 1); [subst; reflexivity|].
    if_false_lia.
    if_false_lia.
    reflexivity.
Qed.

Lemma helper_compose_arb_cup_ZX_of_infunc_neq_base_gen edges f k l  
  (Hedges : 1 < edges) 
  (Hf : permutation (edges * 2) f) 
  (Hf1 : f 1 = k) (Hf2 : f 2 = l) : 
  perm_eq ((edges - 1) * 2) (fun a => 
    let k' := 
      if a =? 0 then if k <? l then 0 else 3 else
      if a =? 1 then if k <? l then 3 else 0 else a + 2 in 
    (if f k' <? Init.Nat.min k l then f k' + 2
      else if f k' <? Init.Nat.max k l then f k' + 1 else f k') - 2)
    (contract_biperm 1 2 f
      ∘ (if k <? l then idn else (swap_perm 0 1 ((edges - 1) * 2)))).
Proof.
  rewrite Nat.mul_sub_distr_r.
  assert (Hk : k < edges * 2) by (subst k; auto_perm).
  assert (Hl : l < edges * 2) by (subst l; auto_perm).
  assert (Hkl : k <> l) by (subst k l; apply (permutation_neq Hf); lia).
  rewrite helper_base_compose_arb_cup_ZX_of_infunc_neq_base_gen by easy.
  rewrite contract_biperm_definition by auto_perm.
  apply compose_perm_eq_proper_l; [| split; auto_perm].
  rewrite !Combinators.compose_assoc.
  rewrite swap_from_0_1_perm_succ_r_rshift by lia.
  subst k l.
  reflexivity.
Qed.

(* FIXME: Move *)

Lemma ZX_of_infunc_absorb_swap_r n f k l (Hf : permutation (n * 2) f) 
  (Hkl : k / 2 = l / 2) : 
  ZX_of_infunc n (f ∘ swap_perm k l (n * 2)) ∝
  ZX_of_infunc n f.
Proof.
  bdestruct (k =? l); [subst; now rewrite swap_perm_same|].
  assert (Hklsmall : k < n * 2 <-> l < n * 2). 1:{
    enough (n * 2 <= k <-> n * 2 <= l) by lia. 
    split.
    - intros Hk.
      assert (Hkdiv : n * 2 / 2 <= k / 2) by (apply Nat.Div0.div_le_mono; lia).
      rewrite Nat.div_mul in Hkdiv by lia.
      rewrite (Nat.div_mod_eq l 2).
      lia.
    - intros Hl.
      assert (Hldiv : n * 2 / 2 <= l / 2) by (apply Nat.Div0.div_le_mono; lia).
      rewrite Nat.div_mul in Hldiv by lia.
      rewrite (Nat.div_mod_eq k 2).
      lia.
  }
  bdestruct (k <? n * 2); [|now rewrite swap_perm_big by lia].
  assert (Hl : l < n * 2) by lia.
  clear Hklsmall.
  assert (Hor : k < l \/ l < k) by lia.
  by_symmetry Hor by (intros a b IH **; rewrite swap_perm_comm; now apply IH).
  assert (k mod 2 = 0 /\ l mod 2 = 1) as [Hkmod Hlmod]. 1:{
    pose proof (Nat.mod_upper_bound k 2).
    pose proof (Nat.mod_upper_bound l 2).
    pose proof (Nat.div_mod_eq k 2).
    pose proof (Nat.div_mod_eq l 2).
    lia.
  }
  rewrite (Nat.div_mod_eq k 2), (Nat.div_mod_eq l 2).
  rewrite Hkl, Hkmod, Hlmod, Nat.add_0_r.
  rewrite <- conditional_swaps_if_eqb_eq.
  now apply ZX_of_infunc_absorb_conditional_swaps_r.
Qed.

Lemma ZX_of_infunc_absorb_conditional_swap_r n f k l 
  (Hf : permutation (n * 2) f) 
  (Hkl : k / 2 = l / 2) (b : bool) : 
  ZX_of_infunc n (f ∘ if b then swap_perm k l (n * 2) else idn) ∝
  ZX_of_infunc n f.
Proof.
  destruct b; [|easy].
  now apply ZX_of_infunc_absorb_swap_r.
Qed.

Lemma ZX_of_infunc_absorb_conditional_swap_r' n f k l b
  (Hf : permutation (n * 2) f) 
  (Hkl : b = true -> k / 2 = l / 2) : 
  ZX_of_infunc n (f ∘ if b then swap_perm k l (n * 2) else idn) ∝
  ZX_of_infunc n f.
Proof.
  destruct b; [|easy].
  now apply ZX_of_infunc_absorb_swap_r; auto.
Qed.


Lemma compose_arb_cup_ZX_of_infunc_neq_base_gen' edges f k l
  (Hedges : 1 < edges) 
  (Hf : permutation (edges * 2) f) 
  (Hf1 : f 1 = k) (Hf2 : f 2 = l) : 
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1) (contract_biperm 1 2 f)).
Proof.
  assert (Hk : k < edges * 2) by (subst k; auto_perm). 
  assert (Hl : l < edges * 2) by (subst l; auto_perm).
  assert (Hkl : k <> l) by (subst k l; apply (permutation_neq Hf); auto_perm).
  rewrite compose_arb_cup_ZX_of_infunc_neq_base_gen by easy.
  rewrite helper_compose_arb_cup_ZX_of_infunc_neq_base_gen by easy. 
  bdestruct (k <? l); [reflexivity|].
  rewrite ZX_of_infunc_absorb_swap_r; [reflexivity| |reflexivity].
  rewrite Nat.mul_sub_distr_r; auto_perm.
Qed.


Lemma compose_arb_cup_ZX_of_infunc_neq_base_gen_gen edges f k l
  (Hk : k < edges * 2) (Hl : l < edges * 2) (Hkl : k <> l)
  (Hedges : 1 < edges) 
  (Hf : permutation (edges * 2) f) 
  (Hf12 : edge_eq (f 1, f 2) (k, l)) :
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1) (contract_biperm 1 2 f)).
Proof.
  pose proof Hf12 as [[Hf1 Hf2] | [Hf1 Hf2]]%edge_eq_pair_defn'.
  - now apply compose_arb_cup_ZX_of_infunc_neq_base_gen'.
  - rewrite zx_arb_cup_comm.
    now apply compose_arb_cup_ZX_of_infunc_neq_base_gen'.
Qed.

(* FIXME: Move *)
Lemma swap_perm_min a b n (Ha : a < n) : 
  swap_perm a b n (min a b) = max a b.
Proof.
  unfold swap_perm.
  bdestructΩ'.
Qed.

Lemma swap_perm_min' a b n (Hb : b < n) : 
  swap_perm a b n (min a b) = max a b.
Proof.
  unfold swap_perm.
  bdestructΩ'.
Qed.

Lemma swap_perm_max a b n (Ha : a < n) (Hb : b < n) : 
  swap_perm a b n (max a b) = min a b.
Proof.
  unfold swap_perm.
  bdestructΩ'.
Qed.



Lemma contract_perm_swap_perm_min 
  a b n (Ha : a < n) (Hb : b < n) (Hab : a <> b) :
  perm_eq (n - 1) (contract_perm (swap_perm a b n) (min a b))
    (stack_perms (min a b) (n - 1 - min a b) idn 
      (stack_perms (max a b - min a b) (n - 1 - max a b) 
        (big_swap_perm (max a b - min a b - 1) 1) idn)).
Proof.
  intros k Hk.
  unfold contract_perm.
  rewrite swap_perm_min by lia.
  bdestruct (k <? min a b); [|bdestruct (k + 1 =? max a b); 
    [|bdestruct (k <? max a b)]].
  - rewrite swap_perm_neither by lia.
    if_true_lia.
    now rewrite stack_perms_left by lia.
  - replace -> (k + 1).
    rewrite swap_perm_max by lia.
    if_true_lia.
    rewrite stack_perms_right by lia.
    rewrite stack_perms_left by lia.
    rewrite big_swap_perm_right by lia.
    lia.
  - rewrite stack_perms_right by lia.
    rewrite swap_perm_neither by lia.
    if_true_lia.
    rewrite stack_perms_left by lia.
    rewrite big_swap_perm_left by lia.
    lia.
  - rewrite swap_perm_neither by lia.
    if_false_lia.
    rewrite 2!stack_perms_right by lia.
    lia.
Qed.

Lemma contract_perm_swap_perm_max
  a b n (Ha : a < n) (Hb : b < n) (Hab : a <> b) :
  perm_eq (n - 1) (contract_perm (swap_perm a b n) (max a b))
    (stack_perms (min a b) (n - 1 - min a b) idn 
      (stack_perms (max a b - min a b) (n - 1 - max a b) 
        (big_swap_perm 1 (max a b - min a b - 1)) idn)).
Proof.
  intros k Hk.
  unfold contract_perm.
  rewrite swap_perm_max by lia.
  bdestruct (k <? min a b); [|bdestruct (k =? min a b); 
    [|bdestruct (k <? max a b)]].
  - rewrite swap_perm_neither by lia.
    do 2 if_true_lia.
    now rewrite stack_perms_left by lia.
  - replace -> (k).
    rewrite swap_perm_min by lia.
    if_true_lia.
    if_false_lia.
    rewrite stack_perms_right by lia.
    rewrite stack_perms_left by lia.
    rewrite big_swap_perm_left by lia.
    lia.
  - rewrite stack_perms_right by lia.
    rewrite swap_perm_neither by lia.
    if_false_lia.
    rewrite stack_perms_left by lia.
    rewrite big_swap_perm_right by lia.
    lia.
  - rewrite swap_perm_neither by lia.
    if_false_lia.
    rewrite 2!stack_perms_right by lia.
    lia.
Qed.

Lemma contract_perm_swap_perm_above
  a b n (Ha : a < n) (Hb : b < n) (Hab : a <> b) c (Hc : max a b < c) :
  perm_eq (n - 1) (contract_perm (swap_perm a b n) c)
    (swap_perm a b (n - 1)).
Proof.
  intros k Hk.
  unfold contract_perm.
  rewrite (swap_perm_neither a b n c) by lia.
  unfold swap_perm.
  replace_bool_lia (n <=? k) false.
  replace_bool_lia (n <=? k + 1) false.
  bdestructΩ'.
Qed.

Lemma contract_perm_swap_perm_between
  a b n (Ha : a < n) (Hb : b < n) (Hab : a <> b) c 
    (Hcmin : min a b < c) (Hcmax : c < max a b) :
  perm_eq (n - 1) (contract_perm (swap_perm a b n) c)
    (swap_perm (min a b) (max a b - 1) (n - 1)).
Proof.
  intros k Hk.
  unfold contract_perm.
  rewrite (swap_perm_neither a b n c) by lia.
  unfold swap_perm.
  replace_bool_lia (n <=? k) false.
  replace_bool_lia (n <=? k + 1) false.
  bdestructΩ'.
Qed.

Lemma contract_perm_swap_perm_below
  a b n (Ha : a < n) (Hb : b < n) (Hab : a <> b) c 
    (Hc : c < min a b) :
  perm_eq (n - 1) (contract_perm (swap_perm a b n) c)
    (swap_perm (a - 1) (b - 1) (n - 1)).
Proof.
  intros k Hk.
  unfold contract_perm.
  rewrite (swap_perm_neither a b n c) by lia.
  unfold swap_perm.
  replace_bool_lia (n <=? k) false.
  replace_bool_lia (n <=? k + 1) false.
  bdestructΩ'.
Qed.


Lemma contract_biperm_1_2_swap_perm_0_1 n : 
  perm_eq ((n - 1) * 2) (contract_biperm 1 2 (swap_perm 0 1 (n * 2))) idn.
Proof.
  bdestruct (n <=? 1); [replace ((n - 1) * 2) with 0 by lia; apply perm_eq_0|].
  rewrite contract_biperm_to_min_max.
  replace ((n - 1) * 2) with (n * 2 - 1 - 1) by lia.
  rewrite contract_perm_swap_perm_above by lia.
  simpl.
  rewrite contract_perm_swap_perm_max by lia.
  simpl.
  rewrite big_swap_perm_0_r.
  now rewrite !stack_perms_idn_idn.
Qed.





Lemma compose_arb_cup_ZX_of_infunc_neq_base_gen_gen_alt edges f k l
  (Hk : k < edges * 2) (Hl : l < edges * 2) (Hkl : k <> l)
  (Hedges : 1 < edges) 
  (Hf : permutation (edges * 2) f) 
  (Hf12 : edge_eq (f 0, f 2) (k, l)) :
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1) (contract_biperm 0 2 f)).
Proof.
  rewrite <- (ZX_of_infunc_absorb_swap_r edges f 0 1) by auto_perm.
  rewrite compose_arb_cup_ZX_of_infunc_neq_base_gen_gen; [|auto_perm..|].
  - rewrite (contract_biperm_compose_change_dims (edges * 2)) by lia + auto_perm.
    rewrite contract_biperm_1_2_swap_perm_0_1.
    rewrite swap_perm_right, swap_perm_neither by lia.
    reflexivity.
  - unfold compose.
    rewrite swap_perm_right, swap_perm_neither by lia.
    easy.
Qed.

Lemma compose_arb_cup_ZX_of_infunc_neq_full_aux edges f k l
  (Hk : k < edges * 2) (Hl : l < edges * 2) (Hkl : k <> l)
  (Hf : permutation (edges * 2) f) 
  (Hfkl : perm_inv (edges * 2) f k / 2 <> perm_inv (edges * 2) f l / 2) :
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
    ZX_of_infunc (edges - 1) (contract_biperm 0 2 (f
    ∘ (swap_perm (perm_inv (edges * 2) f k / 2 * 2) 
        (perm_inv (edges * 2) f k) (edges * 2))
    ∘ (swap_perm (perm_inv (edges * 2) f l / 2 * 2) 
        (perm_inv (edges * 2) f l) (edges * 2))
    ∘ tensor_perms edges 2 
    (swap_from_0_1_perm 
      (perm_inv (edges * 2) f k / 2) 
      (perm_inv (edges * 2) f l / 2) 
      edges) idn
  ))).
Proof.
  set (f'k := perm_inv (edges * 2) f k) in *.
  set (f'l := perm_inv (edges * 2) f l) in *.
  assert (Hf'k : f'k < edges * 2) by (subst f'k; auto_perm).
  assert (Hf'l : f'l < edges * 2) by (subst f'l; auto_perm).
  assert (Hf'k2 : f'k / 2 < edges) by (subst f'k; dmlia).
  assert (Hf'l2 : f'l / 2 < edges) by (subst f'l; dmlia).
  assert (Hedges : 1 < edges). 1: {
    enough (2 < edges * 2) by lia.
    now apply (diff_divs_lower_bound _ _ _ _ Hf'k Hf'l).
  }
  rewrite <- (compose_arb_cup_ZX_of_infunc_neq_base_gen_gen_alt 
    edges _ k l Hk Hl Hkl Hedges).
  - rewrite ZX_of_infunc_absorb_tensor_perms_r by (auto_perm).
    rewrite 2!ZX_of_infunc_absorb_swap_r by (rewrite 1? Nat.div_mul; auto_perm).
    reflexivity.
  - auto_perm.
  - unfold compose.
    rewrite 2!tensor_perms_defn by lia.
    rewrite swap_from_0_1_perm_0, swap_from_0_1_perm_1 by lia.
    rewrite 2!Nat.add_0_r.
    replace (k, l) with (f f'k, f f'l) by (subst f'k f'l; cleanup_perm_inv).
    apply f_edge_equal.
    erewrite f_edge_equal; [|refine (f_edge_equal _ _ _ _ _
      (f_edge_equal (fun k => k * 2) _ _ _ _ (edge_eq_min_max _ _)))].
    rewrite (swap_perm_neither _ _ _ (_ * 2)) by 
      (intros Heq%(f_equal (fun k => k / 2)); rewrite 2?Nat.div_mul in Heq; lia).
    rewrite swap_perm_left by lia.
    rewrite swap_perm_left by lia.
    rewrite swap_perm_neither by 
      (intros Heq%(f_equal (fun k => k / 2)); rewrite 2?Nat.div_mul in Heq; lia).
    reflexivity.
Qed.

Lemma compose_arb_cup_ZX_of_infunc n k l f (Hf : permutation (n * 2) f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) : 
  zx_arb_cup k l (n * 2) ⟷ ZX_of_infunc n f ∝
  cast _ _ (eq_sym (Nat.mul_sub_distr_r n 1 2)) eq_refl (
    ZX_of_infunc (n - 1) (
    if perm_inv (n * 2) f k / 2 =? perm_inv (n * 2) f l / 2 then 
      (contract_biperm 0 1 (f ∘ tensor_perms n 2
         (swap_from_0_perm (perm_inv (n * 2) f k / 2) n) idn))
    else 
      contract_biperm 0 2 (f
      ∘ (swap_perm (perm_inv (n * 2) f k / 2 * 2) 
          (perm_inv (n * 2) f k) (n * 2))
      ∘ (swap_perm (perm_inv (n * 2) f l / 2 * 2) 
          (perm_inv (n * 2) f l) (n * 2))
      ∘ tensor_perms n 2 
        (swap_from_0_1_perm 
          (perm_inv (n * 2) f k / 2) 
          (perm_inv (n * 2) f l / 2) n) 
        idn)
  )).
Proof.
  bdestruct_one.
  - now apply compose_arb_cup_ZX_of_infunc_eq_full.
  - now apply compose_arb_cup_ZX_of_infunc_neq_full_aux.
Qed.

Lemma tensor_perms_2_swap_from_0_perm_swap_from_0_1_perm n k (Hk : k < n) :
  tensor_perms n 2 (swap_from_0_perm k n) idn =
  swap_from_0_1_perm (2 * k) (2 * k + 1) (n * 2).
Proof.
  eq_by_WF_perm_eq (n * 2).
  rewrite tensor_perms_defn, swap_from_0_1_perm_defn.
  intros a Ha.
  rewrite swap_from_0_perm_defn by dmlia.
  rewrite div_eqb_0_iff by lia.
  rewrite Nat.min_l, Nat.max_r by lia.
  bdestruct (a <? 2); [|bdestruct (a / 2 <? k + 1)].
  - bdestruct (a =? 0).
    + subst; simpl; lia.
    + if_true_lia.
      replace a with 1; simpl; lia.
  - do 2 if_false_lia.
    pose proof (Nat.div_mod_eq a 2) as Ha2.
    pose proof (Nat.mod_upper_bound a 2 ltac:(lia)) as Hamod2.
    assert (a < 2 * k + 2)
      by (rewrite Ha2; clear Ha; show_moddy_lt).
    if_true_lia.
    lia.
  - do 2 if_false_lia.
    pose proof (Nat.div_mod_eq a 2) as Ha2.
    pose proof (Nat.mod_upper_bound a 2 ltac:(lia)) as Hamod2.
    do 2 if_false_lia.  
    lia.
Qed.

(* FIXME: Move *)
Lemma swap_to_0_1_perm_edge_eq_pair_rw {i j k l}
  (Hrw : edge_eq (i, j) (k, l)) n : 
  swap_to_0_1_perm i j n =
  swap_to_0_1_perm k l n.
Proof.
  apply (swap_to_0_1_perm_edge_eq_rw Hrw).
Qed.

Lemma swap_from_0_1_perm_edge_eq_pair_rw {i j k l}
  (Hrw : edge_eq (i, j) (k, l)) n : 
  swap_from_0_1_perm i j n =
  swap_from_0_1_perm k l n.
Proof.
  apply (swap_from_0_1_perm_edge_eq_rw Hrw).
Qed.

Lemma contract_biperm_edge_eq_pair_rw {i j k l}
  (Hrw : edge_eq (i, j) (k, l)) f : 
  contract_biperm i j f =
  contract_biperm k l f.
Proof. 
  apply (contract_biperm_edge_eq_rw Hrw).
Qed.

Lemma edge_eq_parities_of_div2_eq_neq k l 
  (Hkl : k <> l) (Hkl2 : k / 2 = l / 2) :
  edge_eq (2 * (k / 2), 2 * (k / 2) + 1) (k, l).
Proof.
  rewrite (Nat.div_mod_eq l 2).
  rewrite <- Hkl2.
  assert (l mod 2 <> k mod 2) by 
    (pose (Nat.div_mod_eq l 2); pose (Nat.div_mod_eq k 2); congruence).
  pose proof (Nat.div_mod_eq k 2).
  pose proof (Nat.mod_upper_bound k 2 ltac:(lia)).
  pose proof (Nat.mod_upper_bound l 2 ltac:(lia)).
  rewrite edge_eq_pair_defn.
  lia.
Qed.


Lemma helper_compose_arb_cup_ZX_of_infunc_case_1 
  n k l f (Hf : permutation (n * 2) f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) 
  (Hfkl : perm_inv (n * 2) f k / 2 = perm_inv (n * 2) f l / 2) :
  perm_eq (n * 2 - 2) 
    ((contract_biperm 0 1 (f ∘ tensor_perms n 2
      (swap_from_0_perm (perm_inv (n * 2) f k / 2) n) idn)))
    (contract_biperm (perm_inv (n * 2) f k) (perm_inv (n * 2) f l) f).
Proof.
  set (f' := perm_inv (n * 2) f) in *.
  assert (Hf'k : f' k < n * 2) by (subst f'; auto_perm).
  assert (Hf'l : f' l < n * 2) by (subst f'; auto_perm).
  assert (Hf'kl : f' k <> f' l) by 
    (apply (permutation_neq (n:=n*2)); subst f'; auto_perm).
  rewrite 2!contract_biperm_definition by auto_perm.
  rewrite swap_from_0_1_perm_0_1_eq.
  rewrite compose_idn_r.
  rewrite tensor_perms_2_swap_from_0_perm_swap_from_0_1_perm by dmlia.
  change ((?f ∘ ?g) ?x) with (f (g x)).
  rewrite swap_from_0_1_perm_0, swap_from_0_1_perm_1, 
    Nat.min_l, Nat.max_r by lia.
  rewrite <- (Combinators.compose_assoc _ f).
  apply compose_rshift_r_proper.
  apply compose_perm_eq_proper_r.
  assert (Hf'k21 : 2 * (f' k / 2) + 1 < n * 2) by show_moddy_lt.
  assert (Hf'k2 : 2 * (f' k / 2) < n * 2) by lia.
  assert (2 * (f' k / 2) <> 2 * (f' k / 2) + 1) by lia.
  apply compose_perm_eq_proper_l; [|split; [auto_perm|]].
  - apply compose_perm_eq_proper_l; [|split; auto_perm].
    ereflexivity.
    apply swap_to_0_1_perm_edge_eq_pair_rw.
    apply f_edge_equal.
    now apply edge_eq_parities_of_div2_eq_neq.
  - ereflexivity.
    apply swap_from_0_1_perm_edge_eq_pair_rw.
    now apply edge_eq_parities_of_div2_eq_neq.
Qed.

Lemma swap_from_0_1_perm_0_2 n (Hn : 2 < n) : 
  swap_from_0_1_perm 0 2 n = 
  swap_perm 1 2 n.
Proof.
  eq_by_WF_perm_eq n.
  rewrite swap_from_0_1_perm_defn, swap_perm_defn by lia.
  intros k Hk.
  simpl.
  bdestructΩ'.
Qed.

(* FIXME: Move *)
Lemma swap_to_0_1_perm_below k l n a : 
  a < k -> a < l -> a < n ->
  swap_to_0_1_perm k l n a = a + 2.
Proof.
  unfold swap_to_0_1_perm.
  intros; bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_between k l n a : 
  min k l < a -> a < max k l -> a < n ->
  swap_to_0_1_perm k l n a = a + 1.
Proof.
  unfold swap_to_0_1_perm.
  intros; bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_above k l n a : 
  max k l < a ->
  swap_to_0_1_perm k l n a = a.
Proof.
  unfold swap_to_0_1_perm.
  intros; bdestructΩ'.
Qed.

Lemma swap_from_0_1_perm_below k l n a : 
  1 < a -> a < k + 2 -> a < l + 2 -> a < n ->
  swap_from_0_1_perm k l n a = a - 2.
Proof.
  unfold swap_from_0_1_perm.
  intros; bdestructΩ'.
Qed.

Lemma swap_from_0_1_perm_between k l n a : 
  1 < a -> min k l + 2 <= a -> a < max k l + 1 -> a < n ->
  swap_from_0_1_perm k l n a = a - 1.
Proof.
  unfold swap_from_0_1_perm.
  intros; bdestructΩ'.
Qed.

Lemma swap_from_0_1_perm_above k l n a : 
  max k l + 1 < a ->
  swap_from_0_1_perm k l n a = a.
Proof.
  unfold swap_from_0_1_perm.
  intros; bdestructΩ'.
Qed.

Lemma swap_from_0_1_perm_above' k l n a : 
  1 < a -> k <> l -> max k l + 1 <= a ->
  swap_from_0_1_perm k l n a = a.
Proof.
  unfold swap_from_0_1_perm.
  intros; bdestructΩ'.
Qed.



Lemma contract_biperm_0_2_tensor_perms_swap_from_0_1 
  n k l
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k / 2 <> l / 2) :
  perm_eq (n * 2 - 2) 
    (contract_biperm 0 2
      (tensor_perms n 2 
        (swap_from_0_1_perm (k / 2) (l / 2) n) idn))
    (swap_from_0_1_perm (2 * (min k l / 2)) 
      (2 * (max k l / 2) - 1) (n * 2 - 2)). 
Proof.
  assert (Hn : 1 < n). 1: {
    enough (2 < n * 2) by lia.
    now apply (diff_divs_lower_bound _ _ _ _ Hk Hl).
  }
  assert (Htens0 : tensor_perms n 2 
    (swap_from_0_1_perm (k / 2) (l / 2) n) idn 0 
    = (2 * (min (k / 2) (l / 2)))). 1:{
    rewrite tensor_perms_defn by lia.
    rewrite swap_from_0_1_perm_0 by lia.
    rewrite Nat.add_0_r.
    lia.
  }
  assert (Htens2 : tensor_perms n 2 
    (swap_from_0_1_perm (k / 2) (l / 2) n) idn 2
    = (2 * (max (k / 2) (l / 2)))). 1:{
    rewrite tensor_perms_defn by lia.
    rewrite swap_from_0_1_perm_1 by lia.
    rewrite Nat.add_0_r.
    lia.
  }
  rewrite contract_biperm_definition by auto_perm.
  rewrite Htens0, Htens2.
  rewrite (swap_to_0_1_perm_edge_eq_pair_rw
    (f_edge_equal (Nat.mul 2) _ _ _ _ 
      (edge_eq_min_max _ _))).
  rewrite swap_from_0_1_perm_0_2 by lia.
  intros a Ha.
  unfold compose.
  rewrite (swap_from_0_1_perm_defn (2 * (min k l / 2))) by lia.
  unfold rshift.
  rewrite Nat.min_l, (Nat.max_r (2 * (_ / 2))) by (rewrite ?max_div, ?min_div; lia).
  rewrite Nat.sub_add by (rewrite max_div; lia).
  bdestruct (a =? 0); [|bdestruct (a =? 1);
    [|bdestruct (a <? 2 * (min k l / 2) + 2); 
    [|bdestruct (a <? 2 * (max k l / 2))]]].
  - subst a.
    rewrite swap_perm_right by lia.
    rewrite tensor_perms_defn, swap_from_0_1_perm_0 by lia.
    change (1 mod 2) with 1.
    assert (min k l / 2 < n) by (dmlia).
    rewrite swap_to_0_1_perm_between by (nia || rewrite <- 1?min_div; nia).
    unfold lshift.
    rewrite <- min_div.
    lia.
  - subst a.
    rewrite swap_perm_neither by lia.
    rewrite tensor_perms_defn, swap_from_0_1_perm_1 by lia.
    change ((1 + 2) mod 2) with 1.
    assert (min k l / 2 < n) by (dmlia).
    rewrite swap_to_0_1_perm_above by (nia || rewrite <- 1?min_div; nia).
    unfold lshift.
    rewrite <- max_div.
    lia.
  - rewrite swap_perm_neither by lia.
    rewrite tensor_perms_defn by lia.
    rewrite mod_add_n_r.
    rewrite min_div in *.
    rewrite swap_from_0_1_perm_below by dmlia.
    rewrite div_add_n_r by lia.
    assert (1 <= a / 2) by dmlia.
    replace ((a / 2 + 1 - 2) * 2 + a mod 2) with (a - 2) by 
      (pose (Nat.div_mod_eq a 2); lia).
    rewrite swap_to_0_1_perm_below by lia.
    unfold lshift.
    lia.
  - rewrite swap_perm_neither by lia.
    rewrite tensor_perms_defn by lia.
    rewrite mod_add_n_r.
    rewrite min_div, max_div in *.
    rewrite swap_from_0_1_perm_between by dmlia.
    rewrite div_add_n_r by lia.
    assert (1 <= a / 2) by dmlia.
    replace ((a / 2 + 1 - 1) * 2 + a mod 2) with (a) by 
      (pose (Nat.div_mod_eq a 2); lia).
    rewrite swap_to_0_1_perm_between by lia.
    unfold lshift.
    lia.
  - rewrite swap_perm_neither by lia.
    rewrite tensor_perms_defn by lia.
    rewrite mod_add_n_r.
    rewrite min_div, max_div in *.
    rewrite swap_from_0_1_perm_above' by dmlia.
    rewrite div_add_n_r by lia.
    replace ((a / 2 + 1) * 2 + a mod 2) with (a + 2) by 
      (pose (Nat.div_mod_eq a 2); lia).
    rewrite swap_to_0_1_perm_above by lia.
    unfold lshift.
    lia.
Qed.

Lemma swap_perm_commutes a b c d n : 
  a <> c -> a <> d -> b <> c -> b <> d ->
  swap_perm a b n ∘ swap_perm c d n =
  swap_perm c d n ∘ swap_perm a b n.
Proof.
  intros.
  eq_by_WF_perm_eq n.
  intros k Hk.
  unfold compose, swap_perm.
  bdestructΩ'.
Qed.


Lemma contract_biperm_bounded k l n f (Hf : perm_bounded n f) 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_bounded (n - 2) (contract_biperm k l f).
Proof.
  rewrite contract_biperm_to_min_max.
  replace (n - 2) with (n - 1 - 1) by lia.
  auto_perm.
Qed.

#[export] Hint Resolve contract_biperm_bounded : perm_bounded_db.

Lemma contract_perm_swap_perm_neither a b n 
  (Ha : a < n) (Hb : b < n) c 
  (Hac : a <> c) (Hbc : b <> c) : 
  perm_eq (n - 1) (contract_perm (swap_perm a b n) c)
  (swap_perm (if c <? a then a - 1 else a) 
    (if c <? b then b - 1 else b) (n - 1)).
Proof.
  bdestruct (a =? b); [subst; now rewrite 2!swap_perm_same, contract_perm_idn|].
  assert (Hor : c < min a b \/ (min a b < c < max a b) \/ max a b < c) by lia.
  destruct Hor as [Hlow | [Hmid | Hhigh]].
  - rewrite contract_perm_swap_perm_below by lia.
    now do 2 if_true_lia.
  - rewrite contract_perm_swap_perm_between by lia.
    rewrite min_ltb, max_ltb.
    bdestructΩ'; now rewrite swap_perm_comm.
  - rewrite contract_perm_swap_perm_above by lia.
    now do 2 if_false_lia.
Qed.

Lemma contract_biperm_swap_perm_single_min_lt a b c n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hac : a < c) (Hcb : c < b) : 
  perm_eq (n - 2) 
    (contract_biperm a b (swap_perm a c n))
    (stack_perms a (n - 2 - a) idn
     (stack_perms (c - a) (n - 2 - c) (big_swap_perm (c - a - 1) 1) idn)).
Proof.
  unfold contract_biperm. 
  replace (n - 2) with (n - 1 - 1) by lia.
  if_true_lia.
  rewrite contract_perm_swap_perm_neither by lia.
  do 2 if_false_lia.
  replace a with (min a c) at 2
      by bdestructΩ'.
  rewrite contract_perm_swap_perm_min by bdestructΩ'.
  rewrite min_l, max_r by bdestructΩ'.
  reflexivity.
Qed.

Lemma contract_biperm_swap_perm_single_min_gt a b c n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hac : c < a) (Hcb : c < b) 
  (Hab : a < b) : 
  perm_eq (n - 2) 
    (contract_biperm a b (swap_perm a c n))
    (stack_perms c (n - 2 - c) idn
     (stack_perms (a - c) (n - 2 - a) (big_swap_perm 1 (a - c - 1)) idn)).
Proof.
  unfold contract_biperm. 
  replace (n - 2) with (n - 1 - 1) by lia.
  if_true_lia.
  rewrite contract_perm_swap_perm_neither by lia.
  do 2 if_false_lia.
  replace a with (max a c) at 2
      by lia.
  rewrite contract_perm_swap_perm_max by lia.
  rewrite min_r, max_l by lia.
  reflexivity.
Qed.

Lemma contract_biperm_swap_perm_single_min a b c n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hcb : c < b)
  (Hab : a < b) : 
  perm_eq (n - 2) 
    (contract_biperm a b (swap_perm a c n))
    (stack_perms (min a c) (n - 2 - min a c) idn
     (stack_perms (max a c - min a c) (n - 2 - max a c) 
      (big_swap_perm (if a <=? c then c - a - 1 else 1)
        (if c <=? a then a - c - 1 else 1)) idn)).
Proof.
  bdestruct (a =? c); [|bdestruct (a <? c)].
  - subst a.
    rewrite swap_perm_same, Nat.max_id, Nat.min_id, Nat.sub_diag.
    if_true_lia.
    rewrite big_swap_perm_0_l.
    now rewrite contract_biperm_idn, 2!stack_perms_idn_idn.
  - rewrite contract_biperm_swap_perm_single_min_lt by lia.
    if_true_lia; if_false_lia.
    now rewrite min_l, max_r by lia.
  - rewrite contract_biperm_swap_perm_single_min_gt by lia.
    if_false_lia; if_true_lia.
    now rewrite min_r, max_l by lia.
Qed.

Lemma contract_biperm_small_swap_perm_l a b c n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hab : a <> b)
  (Hac : max a c - min a c <= 1) : 
  perm_eq (n - 2) 
    (contract_biperm a b (swap_perm a c n))
    idn.
Proof.
  bdestruct (a =? c); [subst; now rewrite swap_perm_same, contract_biperm_idn|].
  unfold contract_biperm.
  replace (n - 2) with (n - 1 - 1) by lia.
  bdestruct (a <? b); [bdestruct (b =? c)|].
  - subst.
    replace c with (max a c) at 2 by lia.
    rewrite contract_perm_swap_perm_max by lia.
    rewrite min_l, max_r by lia.
    replace (c - a - 1) with 0 by lia.
    now rewrite big_swap_perm_0_r, !stack_perms_idn_idn, contract_perm_idn.
  - rewrite contract_perm_swap_perm_neither by lia.
    if_false_lia.
    if_false_lia.
    bdestruct (a <? c).
    + replace a with (min a c) at 2 by lia.
      rewrite contract_perm_swap_perm_min by lia.
      rewrite min_l, max_r by lia.
      replace (c - a - 1) with 0 by lia.
      now rewrite big_swap_perm_0_l, !stack_perms_idn_idn.
    + replace a with (max a c) at 2 by lia.
      rewrite contract_perm_swap_perm_max by lia.
      rewrite min_r, max_l by lia.
      replace (a - c - 1) with 0 by lia.
      now rewrite big_swap_perm_0_r, !stack_perms_idn_idn.
  - bdestruct (a <? c).
    + replace a with (min a c) at 2 by lia.
      rewrite contract_perm_swap_perm_min by lia.
      rewrite min_l, max_r by lia.
      replace (c - a - 1) with 0 by lia.
      now rewrite big_swap_perm_0_l, !stack_perms_idn_idn, contract_perm_idn.
    + replace a with (max a c) at 2 by lia.
      rewrite (contract_perm_swap_perm_max a c n) by lia.
      rewrite min_r, max_l by lia.
      replace (a - c - 1) with 0 by lia.
      now rewrite big_swap_perm_0_r, !stack_perms_idn_idn, contract_perm_idn.
Qed.






Lemma contract_biperm_0_2_swap_swap_tensor
  n k l
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) 
  (Hkl2 : k / 2 <> l / 2):
  perm_eq (n * 2 - 2) 
    (contract_biperm 0 2
      (swap_perm ((k / 2) * 2) k (n * 2)
        ∘ swap_perm ((l / 2) * 2) l (n * 2)
        ∘ tensor_perms n 2 (swap_from_0_1_perm (k / 2) (l / 2) n) idn))
    (swap_from_0_1_perm (2 * (Init.Nat.min k l / 2))
     (2 * (Init.Nat.max k l / 2) - 1) (n * 2 - 2)). 
Proof.
  assert (Hn : 1 < n). 1: {
    enough (2 < n * 2) by lia.
    now apply (diff_divs_lower_bound _ _ _ _ Hk Hl).
  }
  assert (Htens0 : tensor_perms n 2 
    (swap_from_0_1_perm (k / 2) (l / 2) n) idn 0 
    = (2 * (min (k / 2) (l / 2)))). 1:{
    rewrite tensor_perms_defn by lia.
    rewrite swap_from_0_1_perm_0 by lia.
    rewrite Nat.add_0_r.
    lia.
  }
  assert (Htens2 : tensor_perms n 2 
    (swap_from_0_1_perm (k / 2) (l / 2) n) idn 2
    = (2 * (max (k / 2) (l / 2)))). 1:{
    rewrite tensor_perms_defn by lia.
    rewrite swap_from_0_1_perm_1 by lia.
    rewrite Nat.add_0_r.
    lia.
  }
  rewrite contract_biperm_compose by auto_perm.
  rewrite Htens0, Htens2.
  rewrite (contract_biperm_edge_eq_pair_rw
    (f_edge_equal (Nat.mul 2) _ _ _ _ (edge_eq_min_max _ _))).
  assert (Hk2 : k / 2 < n) by dmlia.
  assert (Hl2 : l / 2 < n) by dmlia.
  assert (0 < n * 2) by lia.
  assert (2 < n * 2) by lia.
  assert (perm_bounded (n * 2) (tensor_perms n 2 (swap_from_0_1_perm (k / 2) (l / 2) n) idn)) by auto_perm.
  erewrite compose_perm_eq_proper_l;
  [|apply contract_biperm_compose; try apply swap_perm_permutation; nia|
  split; [auto_perm|reflexivity]].
  rewrite swap_perm_neither by
    (intros Heq%(f_equal (fun k => k / 2)); 
      rewrite ?Nat.div_mul, ?div_mul_l in Heq; lia).
  rewrite (Nat.mul_comm 2 (l/2)), swap_perm_left by lia.
  rewrite (contract_biperm_comm _ _ (_ * 2)).
  rewrite Combinators.compose_assoc.
  erewrite compose_perm_eq_proper_r;
  [| now rewrite (contract_biperm_small_swap_perm_l) by 
    (lia + pose (Nat.div_mod_eq l 2); pose (Nat.mod_upper_bound l 2); lia)].
  rewrite compose_idn_l.
  rewrite (Nat.mul_comm 2 (k/2)), (contract_biperm_small_swap_perm_l) by 
    first [
      intros Heq%(f_equal (fun k => k / 2)); 
      rewrite ?Nat.div_mul, ?div_mul_l in Heq; lia |
      lia |   
      pose (Nat.div_mod_eq k 2); pose (Nat.mod_upper_bound k 2); lia].
  rewrite compose_idn_l.
  now rewrite contract_biperm_0_2_tensor_perms_swap_from_0_1.
Qed. 


Lemma helper_compose_arb_cup_ZX_of_infunc_case_2
  n k l f (Hf : permutation (n * 2) f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) 
  (Hfkl : perm_inv (n * 2) f k / 2 <> perm_inv (n * 2) f l / 2) :
  perm_eq (n * 2 - 2) 
    (contract_biperm 0 2 (f
    ∘ (swap_perm (perm_inv (n * 2) f k / 2 * 2) 
        (perm_inv (n * 2) f k) (n * 2))
    ∘ (swap_perm (perm_inv (n * 2) f l / 2 * 2) 
        (perm_inv (n * 2) f l) (n * 2))
    ∘ tensor_perms n 2 
      (swap_from_0_1_perm 
        (perm_inv (n * 2) f k / 2) 
        (perm_inv (n * 2) f l / 2) n) 
      idn))
    (contract_biperm (perm_inv (n * 2) f k) (perm_inv (n * 2) f l) f
    ∘ swap_from_0_1_perm 
      (2 * (Init.Nat.min (perm_inv (n * 2) f k) (perm_inv (n * 2) f l) / 2))
      (2 * (Init.Nat.max (perm_inv (n * 2) f k) (perm_inv (n * 2) f l) / 2) - 1) 
        (n * 2 - 2)).
Proof.
  set (f' := perm_inv (n * 2) f) in *.
  assert (Hf'kl : f' k <> f' l) by congruence. 
  assert (Hf'k : f' k < n * 2) by (subst f'; auto_perm).
  assert (Hf'l : f' l < n * 2) by (subst f'; auto_perm).
  assert (Hn : 1 < n). 1: {
    enough (2 < n * 2) by lia.
    now apply (diff_divs_lower_bound _ _ _ _ Hf'k Hf'l).
  }
  rewrite !(Combinators.compose_assoc _ _ f), contract_biperm_compose by auto_perm.
  assert (Htens0 : tensor_perms n 2 
    (swap_from_0_1_perm (f' k / 2) (f' l / 2) n) idn 0 
    = (2 * (min (f' k / 2) (f' l / 2)))). 1:{
    rewrite tensor_perms_defn by lia.
    rewrite swap_from_0_1_perm_0 by lia.
    rewrite Nat.add_0_r.
    lia.
  }
  assert (Htens2 : tensor_perms n 2 
    (swap_from_0_1_perm (f' k / 2) (f' l / 2) n) idn 2
    = (2 * (max (f' k / 2) (f' l / 2)))). 1:{
    rewrite tensor_perms_defn by lia.
    rewrite swap_from_0_1_perm_1 by lia.
    rewrite Nat.add_0_r.
    lia.
  }
  rewrite contract_biperm_0_2_swap_swap_tensor by lia.
  repeat (change ((?f ∘ ?g) ?x) with (f (g x))).
  rewrite Htens0, Htens2.
  erewrite contract_biperm_edge_eq_pair_rw by
    (do 3 apply f_edge_equal; apply edge_eq_min_max).
  rewrite 2!(Nat.mul_comm 2).
  rewrite (swap_perm_neither _ _ _ (_ * 2)) by
    (intros Heq%(f_equal (fun k => k / 2)); 
      rewrite ?Nat.div_mul, ?div_mul_l in Heq; lia).
  rewrite swap_perm_left by show_moddy_lt.
  rewrite swap_perm_left by show_moddy_lt.
  rewrite swap_perm_neither by
    (intros Heq%(f_equal (fun k => k / 2)); 
      rewrite ?Nat.div_mul, ?div_mul_l in Heq; lia).
  reflexivity.
Qed.

Definition pairswap {A B} (ab : A * B) := (snd ab, fst ab).

Add Parametric Morphism : pairswap with signature
  edge_eq ==> edge_eq as pairswap_edge_eq_proper.
Proof.
  unfold edge_eq.
  simpl.
  tauto.
Qed.

Lemma edge_eq_pairswap ij : 
  edge_eq (pairswap ij) ij.
Proof. apply edge_eq_swap. Qed.

Lemma lt_twice_iff_of_half_eq {k l} (Hkl : k / 2 = l / 2) n : 
  k < n * 2 <-> l < n * 2.
Proof.
  split.
  - intros Hk.
    rewrite (Nat.div_mod_eq l 2).
    rewrite <- Hkl.
    show_moddy_lt.
  - intros Hk.
    rewrite (Nat.div_mod_eq k 2).
    rewrite Hkl.
    show_moddy_lt.
Qed.

Lemma lt_twice_of_half_eq {k l n} (Hk : k < n * 2) (Hkl : k / 2 = l / 2) : l < n * 2.
Proof.
  now apply (lt_twice_iff_of_half_eq Hkl).
Qed.

(* FIXME: Move, and fix the swap_perm_commutes proof with them *)
Lemma compose_swap_perm_r n f a b (Ha : a < n) (Hb : b < n) 
  (Hf : permutation n f) :
  perm_eq n (f ∘ swap_perm a b n) 
    (swap_perm (f a) (f b) n ∘ f).
Proof.
  rewrite 2!swap_perm_defn by auto_perm.
  intros k Hk.
  unfold compose.
  rewrite 2!(permutation_eqb_iff k _ Hf) by auto_perm.
  bdestructΩ'.
Qed.

Lemma compose_swap_perm_l n f a b (Ha : a < n) (Hb : b < n) 
  (Hf : permutation n f) :
  perm_eq n (swap_perm a b n ∘ f) 
    (f ∘ swap_perm (perm_inv n f a) (perm_inv n f b) n).
Proof.
  apply perm_inv_inj; [auto_perm..|].
  now rewrite 2!perm_inv_compose, 2!swap_perm_inv, 
    compose_swap_perm_r by auto_perm.
Qed.

(* FIXME: Move *)
Lemma edgepermutation_defn n f : edgepermutation n f <-> 
  permutation (n * 2) (infunc_of_edgefunc f).
Proof. reflexivity. Qed.

Hint Resolve -> edgepermutation_defn : perm_db.

Lemma if_if_dist {A} (b c d : bool) (u v : A) : 
  (if (if b then c else d) then u else v) =
  if b then if c then u else v else if d then u else v.
Proof. 
  now destruct b.
Qed.

Lemma edgepermutation_fst_neqb_snd n f k (Hf : edgepermutation n f) 
  (Hk : k < n) :
  (fst (f k) =? snd (f k)) = false.
Proof.
  rewrite Nat.eqb_neq.
  now apply (edgepermutation_fst_neq_snd n f k).
Qed.

Lemma edgepermutation_fst_neq_snd' n f k l (Hf : edgepermutation n f) 
  (Hk : k < n) (Hl : l < n) : 
  fst (f k) <> snd (f l).
Proof.
  pose proof (permutation_is_injective _ _ Hf (k * 2) (l * 2 + 1)
    ltac:(show_moddy_lt) ltac:(show_moddy_lt)) as Heq.
  rewrite infunc_of_edgefunc_twice', infunc_of_edgefunc_twice_plus' in Heq.
  lia.
Qed.

Lemma edgepermutation_fst_neqb_snd' n f k l (Hf : edgepermutation n f) 
  (Hk : k < n) (Hl : l < n) : 
  (fst (f k) =? snd (f l)) = false.
Proof.
  rewrite Nat.eqb_neq.
  now apply (edgepermutation_fst_neq_snd' n f).
Qed.

Lemma edgepermutation_fst_inj 
  n f k l (Hf : edgepermutation n f) (Hk : k < n) (Hl : l < n) :
  fst (f k) = fst (f l) ->
  k = l.
Proof.
  intros.
  pose proof (permutation_is_injective _ _ Hf (k * 2) (l * 2)
    ltac:(show_moddy_lt) ltac:(show_moddy_lt)) as Heq.
  rewrite 2!infunc_of_edgefunc_twice' in Heq.
  lia.
Qed.

Lemma edgepermutation_snd_inj 
  n f k l (Hf : edgepermutation n f) (Hk : k < n) (Hl : l < n) :
  snd (f k) = snd (f l) ->
  k = l.
Proof.
  intros.
  pose proof (permutation_is_injective _ _ Hf (k * 2 + 1) (l * 2 + 1)
    ltac:(show_moddy_lt) ltac:(show_moddy_lt)) as Heq.
  rewrite 2!infunc_of_edgefunc_twice_plus' in Heq.
  lia.
Qed.


Lemma edgepermutation_fst_edgemem_iff 
  n f k l (Hf : edgepermutation n f) (Hk : k < n) (Hl : l < n) :
  edge_mem (fst (f k)) (f l) =
  (k =? l).
Proof.
  unfold edge_mem.
  apply eq_true_iff_eq.
  rewrite (edgepermutation_fst_neqb_snd' n f k l Hf Hk Hl).
  rewrite orb_false_r.
  rewrite 2!Nat.eqb_eq.
  split; [|congruence].
  apply (edgepermutation_fst_inj n); auto_perm.
Qed.

(* FIXME: Move *)
Lemma swap_perm_edge_eq_rw {ij kl} (Hrw : edge_eq ij kl) n : 
  swap_perm (fst ij) (snd ij) n = 
  swap_perm (fst kl) (snd kl) n.
Proof.
  pose proof Hrw as [-> | ->]%edge_eq_defn_l.
  - reflexivity.
  - apply swap_perm_comm.
Qed.

Lemma swap_perm_edge_eq_pair_rw {i j k l} (Hrw : edge_eq (i, j) (k, l)) n : 
  swap_perm i j n = 
  swap_perm k l n.
Proof.
  apply (swap_perm_edge_eq_rw Hrw).
Qed.
  

Lemma infunc_of_edgefunc_compose_pair_swap_r n f k l (Hf : edgepermutation n f) 
  (Hkl : k / 2 = l / 2) (Hk : k < n * 2) : 
  perm_eq (n * 2) (infunc_of_edgefunc f ∘ swap_perm k l (n * 2))
    (infunc_of_edgefunc
      ((fun ij => if edge_mem (fst (f (k / 2))) ij then 
        if k =? l then ij else pairswap ij 
        else ij) ∘ f)).
Proof.
  bdestruct (k =? l). 1:{
    subst k. 
    rewrite swap_perm_same.
    intros a Ha.
    unfold compose.
    unfold infunc_of_edgefunc.
    now rewrite Tauto.if_same.
  }
  apply (lt_twice_of_half_eq Hk) in Hkl as Hl.
  rewrite infunc_of_edgefunc_compose_l.
  - apply compose_perm_eq_proper_r.
    erewrite (big_stack_perms_simplify n n _ (fun _ => 2) _ 
      (fun a => if a =? k / 2 then swap_2_perm else idn)); [|reflexivity..|].
    2: {
      intros a Ha.
      rewrite (if_dist _ _ _ fst).
      cbn -[Nat.div].
      rewrite (if_dist _ _ _ (fun k => k =? snd (f a))).
      rewrite if_if_dist.
      rewrite Nat.eqb_refl, (edgepermutation_fst_neqb_snd n f a) by auto_perm.
      rewrite (edgepermutation_fst_edgemem_iff n) by auto_perm.
      now rewrite Nat.eqb_sym.
    }
    rewrite conditional_swaps_if_eqb_eq.
    ereflexivity.
    apply swap_perm_edge_eq_pair_rw.
    rewrite (Nat.div_mod_eq l 2).
    rewrite <- Hkl.
    pose proof (Nat.div_mod_eq k 2).
    pose proof (Nat.div_mod_eq l 2).
    pose proof (Nat.mod_upper_bound k 2 ltac:(lia)).
    pose proof (Nat.mod_upper_bound l 2 ltac:(lia)).
    rewrite edge_eq_pair_defn.
    lia.
  - intros a Ha.
    unfold compose.
    bdestruct_one; easy + apply edge_eq_pairswap.
Qed.

Lemma edgefunc_of_infunc_of_edgefunc_absorb_pair_swap_r n f 
  k l (Hf : edgepermutation n f) (Hkl : k / 2 = l / 2) (Hk : k < n * 2) : 
  perm_edge_eq n
    (edgefunc_of_infunc (infunc_of_edgefunc f ∘ swap_perm k l (n * 2)))
    f.
Proof.
  rewrite infunc_of_edgefunc_compose_pair_swap_r by auto_perm.
  rewrite edgefunc_of_infunc_of_edgefunc.
  intros a Ha.
  unfold compose.
  bdestructΩ'.
  apply edge_eq_pairswap.
Qed.

Lemma infunc_of_edgefunc_bounded_inj n f g : 
  (perm_eq (n * 2) (infunc_of_edgefunc f) (infunc_of_edgefunc g)) <->
  perm_edgefunc_eq n f g.
Proof.
  split.
  - intros Heq k Hk.
    rewrite (surjective_pairing (f k)), (surjective_pairing (g k)).
    f_equal.
    + rewrite <- 2!infunc_of_edgefunc_twice.
      apply Heq.
      lia.
    + rewrite <- 2!infunc_of_edgefunc_twice_plus.
      apply Heq.
      show_moddy_lt.
  - intros Heq.
    intros k Hk.
    unfold infunc_of_edgefunc.
    now rewrite Heq by dmlia.
Qed.

(* FIXME: Move *)
#[export] Instance perm_edgefunc_eq_perm_edge_eq_subrelation n : 
  subrelation (perm_edgefunc_eq n) (perm_edge_eq n).
Proof. 
  intros f g Hfg a Ha.
  ereflexivity.
  now apply Hfg.
Qed.



Lemma edgefunc_of_infunc_compose_tensor_perms_r n f g :
  perm_edgefunc_eq n (edgefunc_of_infunc (f ∘ tensor_perms n 2 g idn))
    (edgefunc_of_infunc f ∘ g).
Proof.
  apply infunc_of_edgefunc_bounded_inj.
  rewrite infunc_of_edgefunc_of_infunc.
  rewrite infunc_of_edgefunc_compose_r.
  rewrite infunc_of_edgefunc_of_infunc.
  reflexivity.
Qed. 

(* FIXME: Move *)
Lemma contract_biperm_definition_change_dims n f k l (Hf : permutation n f) 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) m : m = n - 2 ->
  perm_eq m (contract_biperm k l f)
  (lshift 2 ∘ (swap_to_0_1_perm (f k) (f l) n ∘ f ∘ swap_from_0_1_perm k l n) ∘ rshift 2).
Proof.
  intros ->.
  now apply contract_biperm_definition.
Qed.

Lemma contract_biperm_definition' n f k l (Hf : permutation (n * 2) f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) :
  perm_eq ((n - 1) * 2) (contract_biperm k l f)
  (lshift 2 ∘ (swap_to_0_1_perm (f k) (f l) (n * 2) ∘ 
    f ∘ swap_from_0_1_perm k l (n * 2)) ∘ rshift 2).
Proof.
  apply contract_biperm_definition_change_dims; lia + auto_perm.
Qed.

#[export] Hint Resolve -> Nat.mul_lt_mono_pos_r : perm_db. 
Lemma div_lt_upper_bound_r a b c : a < c * b -> a / b < c.
Proof.
  intros ?; apply Nat.Div0.div_lt_upper_bound; lia.
Qed.

#[export] Hint Resolve div_lt_upper_bound_r : perm_db.

(* Lemma swap_from_0_1_perm_defn_alt_div2_neq n k l 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k / 2 <> l <> 2) : 
  perm_eq (n * 2) 
    (swap_from_0_1_perm k l n)
*)

Lemma perm_edge_eq_iff_infunc_edge_eq n f g : 
  perm_edge_eq n f g <->
  forall k, k < n -> 
  edge_eq (infunc_of_edgefunc f (k * 2), infunc_of_edgefunc f (k * 2 + 1))
    (infunc_of_edgefunc g (k * 2), infunc_of_edgefunc g (k * 2 + 1)).
Proof.
  apply forall_iff; intros a.
  apply forall_iff; intros H.
  rewrite 2!infunc_of_edgefunc_twice', 2!infunc_of_edgefunc_twice_plus'.
  reflexivity.
Qed.

(* Lemma helper_compose_arb_cup_ZX_of_edgeperm_case_2_init n k l f 
  (Hf : permutation (n * 2) f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) 
  (Hfkl : edgeperm_idx n f k <> edgeperm_idx n f l) K : 
  perm_edge_eq (n - 1)
    (edgefunc_of_infunc (
      contract_biperm 0 2 (f
      ∘ (swap_perm (perm_inv (n * 2) f k / 2 * 2) 
          (perm_inv (n * 2) f k) (n * 2))
      ∘ (swap_perm (perm_inv (n * 2) f l / 2 * 2) 
          (perm_inv (n * 2) f l) (n * 2))
      ∘ tensor_perms n 2 
        (swap_from_0_1_perm 
          (perm_inv (n * 2) f k / 2) 
          (perm_inv (n * 2) f l / 2) n) 
        idn)
    ))
    (edgefunc_of_infunc 
      (fun a => if a =? 0 then 
      ()
         

    )). *)


(* TODO : Achieve this goal! *)
Lemma helper_compose_arb_cup_ZX_of_edgeperm_case_2 n k l f 
  (Hf : edgepermutation n f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) 
  (Hfkl : edgeperm_idx n f k <> edgeperm_idx n f l) : 
  perm_edge_eq (n - 1)
    (edgefunc_of_infunc (
      contract_biperm 0 2 (infunc_of_edgefunc f
      ∘ (swap_perm (perm_inv (n * 2) (infunc_of_edgefunc f) k / 2 * 2) 
          (perm_inv (n * 2) (infunc_of_edgefunc f) k) (n * 2))
      ∘ (swap_perm (perm_inv (n * 2) (infunc_of_edgefunc f) l / 2 * 2) 
          (perm_inv (n * 2) (infunc_of_edgefunc f) l) (n * 2))
      ∘ tensor_perms n 2 
        (swap_from_0_1_perm 
          (perm_inv (n * 2) (infunc_of_edgefunc f) k / 2) 
          (perm_inv (n * 2) (infunc_of_edgefunc f) l / 2) n) 
        idn)
    ))
    (fun a => if a =? 0 then 
        (edgeperm_partner n f k, edgeperm_partner n f l)
      else 
        f (swap_from_0_1_perm (edgeperm_idx n f k) (edgeperm_idx n f l) n a) 
    ).
Proof.
  assert (Hn : 1 < n). 1: {
    enough (2 < n * 2) by lia.
    refine (diff_divs_lower_bound _ _ _ _ _ _ Hfkl); auto_perm.
  }
  rewrite contract_biperm_definition' by 
    (repeat apply permutation_compose; auto_perm).
  Admitted.

(* FIXME: Really, don't do this... *)
Add Parametric Morphism n : (ZX_of_infunc (n - 1)) with signature
  perm_eq (n * 2 - 2) ==> eq as ZX_of_infunc_sub_1_eq_of_perm_eq.
Proof.
  intros f g Hfg.
  apply ZX_of_infunc_eq_of_perm_eq.
  rewrite Nat.mul_sub_distr_r.
  apply Hfg.
Qed.

(* FIXME: Move *)
Lemma edgeperm_partner_eq_of_edgeperm_idx_eq {n f k l}
  (Hidx : edgeperm_idx n f k = edgeperm_idx n f l) (Hf : edgepermutation n f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) : 
  edgeperm_partner n f k = l.
Proof.
  now apply edgeperm_partner_eq_iff_edgeperm_idx_eq.
Qed.

Lemma infunc_of_edgefunc_compose_rshift_r f k : 
  infunc_of_edgefunc (f ∘ rshift k) =
  infunc_of_edgefunc f ∘ rshift (k * 2).
Proof.
  apply functional_extensionality.
  intros a.
  rewrite <- infunc_of_edgefunc_plus_twice.
  now rewrite Nat.mul_comm.
Qed.

Lemma ZX_of_infunc_to_ZX_of_edgeperm n f :
  ZX_of_infunc n f = 
  ZX_of_edgeperm n (edgefunc_of_infunc f).
Proof.
  unfold ZX_of_edgeperm.
  now rewrite infunc_of_edgefunc_of_infunc.
Qed.

(* FIXME: Move *)
Lemma edgepermutation_edgefunc_of_infunc n f : 
  permutation (n * 2) f -> edgepermutation n (edgefunc_of_infunc f).
Proof.
  intros Hf.
  unfold edgepermutation.
  now rewrite infunc_of_edgefunc_of_infunc.
Qed.

#[export] Hint Resolve edgepermutation_edgefunc_of_infunc : perm_db.


Lemma edgepermutation_sub_1_edgefunc_of_infunc n f : 
  permutation (n * 2 - 2) f -> edgepermutation (n - 1) (edgefunc_of_infunc f).
Proof.
  rewrite <- (Nat.mul_sub_distr_r n 1 2 : _ = n * 2 - 2).
  auto_perm.
Qed.

#[export] Hint Resolve edgepermutation_sub_1_edgefunc_of_infunc : perm_db.



Lemma compose_arb_cup_ZX_of_edgeperm n k l f (Hf : edgepermutation n f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) : 
  zx_arb_cup k l (n * 2) ⟷ ZX_of_edgeperm n f ∝
  cast _ _ (eq_sym (Nat.mul_sub_distr_r n 1 2)) eq_refl (
    ZX_of_edgeperm (n - 1) (
    if edgeperm_idx n f k =? edgeperm_idx n f l then 
      pairmap (lshift 2 ∘ swap_to_0_1_perm k l (n * 2)) ∘ f 
      ∘ swap_from_0_perm (edgeperm_idx n f k) n
      ∘ rshift 1
    else
    (fun a => if a =? 0 then 
        (edgeperm_partner n f k, edgeperm_partner n f l)
      else 
        f (swap_from_0_1_perm (edgeperm_idx n f k) (edgeperm_idx n f l) n a) 
    )
  )).
Proof.
  unfold ZX_of_edgeperm at 1.
  rewrite compose_arb_cup_ZX_of_infunc by auto_perm.
  fold (edgeperm_idx n f k).
  fold (edgeperm_idx n f l).
  apply cast_simplify.
  bdestruct_one.
  - pose proof (infunc_of_edgefunc_compose_r n f
      (swap_from_0_perm (edgeperm_idx n f k) n)) as 
        Hrw%(contract_biperm_perm_eq_of_perm_eq _ _ _ 0 1);
      [|lia..].
    rewrite <- Hrw.
    rewrite contract_biperm_definition' by auto_perm.
    rewrite (infunc_of_edgefunc_twice _ 0).
    rewrite (infunc_of_edgefunc_twice_plus _ 0).
    change ((?f ∘ ?g) 0) with (f (g 0)).
    rewrite swap_from_0_perm_0.
    rewrite (swap_to_0_1_perm_edge_eq_rw 
      (edgeperm_idx_rinv_edge_eq n f k Hf Hk)).
    cbn [fst snd].
    rewrite (edgeperm_partner_eq_of_edgeperm_idx_eq ltac:(eassumption)) 
      by auto_perm.
    rewrite swap_from_0_1_perm_0_1_eq, compose_idn_r.
    rewrite 2!Combinators.compose_assoc.
    rewrite <- (infunc_of_edgefunc_compose_rshift_r _ 1).
    rewrite <- Combinators.compose_assoc.
    rewrite <- infunc_of_edgefunc_compose_pairmap_l_perm_eq.
    reflexivity.
  - rewrite ZX_of_infunc_to_ZX_of_edgeperm.
    refine (ZX_of_edgeperm_perm_edge_eq_rw
      (helper_compose_arb_cup_ZX_of_edgeperm_case_2 _ _ _ _ 
      Hf Hk Hl Hkl ltac:(auto)) _).
    assert (Hneq : edgeperm_idx n f k <> edgeperm_idx n f l) by assumption.
    unfold edgeperm_idx in Hneq.
    apply (diff_divs_lower_bound _ _ _ (n * 2)) in Hneq as Hlt; [|auto_perm..].
    apply edgepermutation_sub_1_edgefunc_of_infunc.
    apply contract_biperm_permutation;
    repeat apply permutation_compose; auto_perm.
Qed.


Record ZX_el_graph {n m : nat} : Set := {
  el_edges : nat;
  el_numspi : nat;
  el_color : nat -> bool;
  el_phase : nat -> R;
  (* A 'list' of edges, wherein indices should be less than 
    [numspi] + [n] + [m]*)
  el_edgefunc : nat -> nat * nat;
  el_io_deg_1 : 
    perm_eq (n + m) (edgefunc_deg el_edges el_edgefunc ∘ rshift el_numspi)
      (fun _ => 1);
  el_edgefunc_WF : WF_edgefunc el_edges (el_numspi + n + m) el_edgefunc;
  el_deg := edgefunc_deg el_edges el_edgefunc;
}.

#[global] Arguments ZX_el_graph _ _ : clear implicits.

Lemma edgefunc_deg_to_count_func_vals n f k : 
  edgefunc_deg n f k = 
  count_func_vals (n * 2) (infunc_of_edgefunc f) k.
Proof.
  unfold edgefunc_deg.
  unfold count_func_vals.
  unfold infunc_of_edgefunc.
  rewrite Nat.mul_comm.
  rewrite <- (big_sum_double_sum
    (fun idiv imod => if edge_to_func (f idiv) imod =? k then 1 else 0)).
  apply big_sum_eq_bounded.
  intros a Ha.
  simpl.
  unfold edge_to_func.
  simpl.
  bdestructΩ'.
Qed.

Lemma WF_edgefunc_iff_WF_input_func n m f : 
  WF_edgefunc n m f <-> WF_input_func (n * 2) m (infunc_of_edgefunc f).
Proof.
  split.
  - intros Hf.
    unfold WF_input_func.
    intros i Hi.
    unfold infunc_of_edgefunc.
    unfold edge_to_func.
    pose proof (Nat.mod_upper_bound i 2 ltac:(lia)).
    bdestructΩ'; apply Hf; dmlia.
  - intros Hf.
    intros k Hk.
    split.
    + specialize (Hf (k * 2) ltac:(lia)).
      now rewrite infunc_of_edgefunc_twice' in Hf.
    + specialize (Hf (k * 2 + 1) ltac:(show_moddy_lt)).
      now rewrite infunc_of_edgefunc_twice_plus' in Hf.
Qed.

Lemma el_data_size_pf n m edges numspi edgefunc 
  (io_deg_1 : perm_eq (n + m) (edgefunc_deg edges edgefunc ∘ rshift numspi) 
    (fun _ => 1))
  (edgefunc_WF : WF_edgefunc edges (numspi + n + m) edgefunc) 
  (deg := edgefunc_deg edges edgefunc) : 
  big_sum deg numspi + n + m = edges * 2.
Proof.
  rewrite <- (sum_count_func_vals _ _ _
    ((proj1 (WF_edgefunc_iff_WF_input_func _ _ _)) edgefunc_WF)).
  rewrite <- 2!Nat.add_assoc, big_sum_sum.
  simpl.
  f_equal.
  - apply big_sum_eq_bounded.
    intros k Hk.
    apply edgefunc_deg_to_count_func_vals.
  - symmetry. 
    rewrite <- (Nat.mul_1_r (n + m)) at 2.
    rewrite <- (Nsum_constant 1).
    apply big_sum_eq_bounded.
    intros k Hk.
    pose proof (io_deg_1 k Hk) as Hrw.
    unfold compose in Hrw.
    rewrite edgefunc_deg_to_count_func_vals in Hrw.
    rewrite Nat.add_comm.
    apply Hrw.
Qed.

Lemma el_size_pf {n m} (G : ZX_el_graph n m) : 
  big_sum G.(el_deg) G.(el_numspi) + n + m = G.(el_edges) * 2.
Proof.
  now apply el_data_size_pf; apply G.
Qed.



Definition ZXvert_of_el_data n m edges numspi color phase edgefunc io_deg_1
  edgefunc_WF :
  ZXvert n m :=
  ZX_of_stack n m numspi (edgefunc_deg edges edgefunc) phase color edges 
    (el_data_size_pf n m edges numspi edgefunc io_deg_1 edgefunc_WF)
    ⟷
    ZX_of_edgefunc edges edgefunc.

Definition ZXvert_of_el_graph {n m} (G : ZX_el_graph n m) :
  ZXvert n m :=
  ZXvert_of_el_data n m G.(el_edges) G.(el_numspi) G.(el_color) 
    G.(el_phase) G.(el_edgefunc) G.(el_io_deg_1) G.(el_edgefunc_WF).



(* Fixpoint find_nat (P : nat -> bool) (n : nat) : option nat :=
  match n with 
  | 0 => None
  | S n' => if P n' then Some n' else find_nat P n'
  end. 
*)



Require Import stdpp.fin_maps stdpp.natmap stdpp.fin_map_dom stdpp.gmultiset.





Definition minverses {A B M M'} 
  `{Lookup A B M} `{Lookup B A M'}
  (f : M) (g : M') :=
  ∀ i j, f !! i = Some j <-> g !! j = Some i.

Lemma minverses_symm {A B M M'} 
  `{Lookup A B M} `{Lookup B A M'}
  (f : M) (g : M') : minverses f g -> minverses g f.
Proof.
  intros Hfg i j; symmetry; apply Hfg.
Qed.

Lemma minverses_map_img_eq_dom {A B SA SB MA MB} 
  `{FinMapDom A MA SA} `{FinMapDom B MB SB}
  (f : MA B) (g : MB A) (Hfg : minverses f g) :
  map_img f ≡@{SB} dom g.
Proof.
  intros x.
  rewrite elem_of_map_img, elem_of_dom.
  setoid_rewrite (fun i => Hfg i x).
  destruct (g !! x) eqn:e; eauto.
Qed.

Lemma minverses_map_img_eq_dom_L {A B SA SB MA MB} 
  `{FinMapDom A MA SA} `{FinMapDom B MB SB} `{!LeibnizEquiv SB}
  (f : MA B) (g : MB A) (Hfg : minverses f g) :
  map_img f =@{SB} dom g.
Proof.
  apply set_eq.
  apply minverses_map_img_eq_dom, Hfg.
Qed.


Lemma minverses_rinv_dom {A B SA SB MA MB} 
  `{FinMapDom A MA SA} `{FinMapDom B MB SB}
  (f : MA B) (g : MB A) (Hfg : minverses f g) :
  ∀ i, i ∈ dom f -> (f !! i) ≫= (g !!.) = Some i.
Proof.
  intros i (j & Hj)%elem_of_dom.
  rewrite Hj.
  simpl.
  apply Hfg, Hj.
Qed.


Lemma minverses_linv_dom {A B SA SB MA MB} 
  `{FinMapDom A MA SA} `{FinMapDom B MB SB}
  (f : MA B) (g : MB A) (Hfg : minverses f g) :
  ∀ i, i ∈ dom g -> (g !! i) ≫= (f !!.) = Some i.
Proof.
  apply minverses_rinv_dom, minverses_symm, Hfg.
Qed.

(* Check fun G => 
 (list_to_set_disj G.(mg_edges) : gmultiset (nat * nat)). *)

(* Check fun G => 
 (fst <$> dom (G.(mg_edges)) : gset). *)



Require Import stdpp.sorting.

Definition natset_to_list (A : natset) : list nat := 
  merge_sort (≤) (elements A).

Lemma not_elem_HdRel_le_HdRel_lt (l : list nat) k : 
  k ∉ l -> HdRel (≤) k l -> HdRel (<) k l.
Proof.
  intros Hin Hhd.
  induction l; [easy|].
  constructor.
  enough (k <= a ∧ k ≠ a) by lia.
  split.
  - apply (HdRel_inv Hhd).
  - rewrite not_elem_of_cons in Hin.
    apply Hin.
Qed.

Lemma NoDup_le_Sorted_lt_Sorted (l : list nat) : 
  NoDup l -> Sorted (≤) l -> Sorted (<) l.
Proof.
  intros Hdup Hsort.
  induction Hsort as [|x l Hsort IH Hhd].
  - constructor.
  - rewrite NoDup_cons in Hdup.
    apply Sorted_cons.
    + apply IH, Hdup.
    + now apply (not_elem_HdRel_le_HdRel_lt _ _).
Qed.

Lemma StronglySorted_natset_to_list A : 
  StronglySorted (<) (natset_to_list A).
Proof.
  apply Sorted_StronglySorted; [typeclasses eauto|].
  apply NoDup_le_Sorted_lt_Sorted.
  - unfold natset_to_list.
    rewrite merge_sort_Permutation.
    apply NoDup_elements.
  - apply Sorted_merge_sort, _.
Qed.

Lemma elem_of_natset_to_list A x : 
  x ∈ natset_to_list A <-> x ∈ A.
Proof.
  unfold natset_to_list.
  rewrite merge_sort_Permutation.
  apply elem_of_elements.
Qed.

Definition list_idx_to_map {A} (l : list A) : natmap A :=
  list_to_map (zip (seq 0 (length l)) l).

Lemma dom_list_idx_to_map {A} (l : list A) : 
  dom (list_idx_to_map l) = list_to_set (seq 0 (length l)).
Proof.
  apply set_eq => x.
  unfold list_idx_to_map.
  rewrite dom_list_to_map.
  rewrite fst_zip by (rewrite length_seq; lia).
  reflexivity.
Qed.

Lemma lookup_list_idx_to_map {A} (l : list A) x : 
  list_idx_to_map l !! x = l !! x.
Proof.
  apply option_eq => v.
  unfold list_idx_to_map.
  rewrite <- elem_of_list_to_map by 
    (rewrite fst_zip by (rewrite length_seq; lia); apply NoDup_seq).
  rewrite elem_of_lookup_zip_with.
  split.
  - intros (i & x' & y' & (<- & <-)%pair_eq & Hgetseq & Hgetl).
    apply lookup_seq in Hgetseq as (-> & Hi).
    apply Hgetl.
  - intros Hgetx.
    exists x, x, v.
    split; [easy|].
    split; [|easy].
    rewrite lookup_seq.
    split; [easy|].
    apply (lookup_lt_Some _ _ _ Hgetx).
Qed.

Lemma lookup_total_list_idx_to_map {A} `{Inhabited A} 
  (l : list A) x : 
  list_idx_to_map l !!! x = l !!! x.
Proof.
  rewrite lookup_total_alt, list_lookup_total_alt,
     lookup_list_idx_to_map.
  reflexivity.
Qed.

Definition natmap_justify {A} (f : natmap A) : natmap A :=
  f ∘ₘ list_idx_to_map (natset_to_list $ dom f).

Lemma dom_omap_natmap_nat {A} 
  (f : nat -> option A) (g : natmap nat) : 
  dom (omap f g) = filter (is_Some ∘ (fun i => f (g !!! i))) (dom g).
Proof.
  apply set_eq => x.
  rewrite elem_of_dom.
  rewrite elem_of_filter, elem_of_dom.
  rewrite lookup_omap.
  destruct (g !! x) as [gx|] eqn:e.
  - simpl.
    rewrite (lookup_total_correct _ _ _ e).
    symmetry.
    rewrite 2!is_Some_alt.
    exact (and_True_r _).
  - simpl.
    symmetry.
    rewrite 3!is_Some_alt.
    easy.
Qed.

Lemma dom_natmap_compose {A} (f : natmap A) (g : natmap nat) : 
  dom (f ∘ₘ g) = filter (is_Some ∘ (f !!.) ∘ (g !!!.)) $ dom g.
Proof.
  apply dom_omap_natmap_nat.
Qed.

Lemma length_natset_to_list (A : natset) : 
  length (natset_to_list A) = size A.
Proof.
  unfold natset_to_list.
  rewrite merge_sort_Permutation.
  reflexivity.
Qed.

Lemma dom_natmap_justify {A} (f : natmap A) : 
  dom (natmap_justify f) = list_to_set (seq 0 (size f)).
Proof.
  unfold natmap_justify.
  rewrite dom_natmap_compose.
  rewrite dom_list_idx_to_map.
  rewrite length_natset_to_list, size_dom.
  apply set_eq => x.
  rewrite elem_of_filter.
  split; [now intros []|].
  rewrite elem_of_list_to_set, elem_of_seq.
  intros Hx.
    split; [|easy].
  simpl.
  rewrite <- elem_of_dom.
  rewrite lookup_total_list_idx_to_map.
  rewrite <- elem_of_natset_to_list.
  apply elem_of_list_lookup_2 with x.
  rewrite list_lookup_alt.
  rewrite length_natset_to_list, size_dom.
  easy.
Qed.



Lemma dom_omap {A SA M B D} `{FinMapDom A M SA}
  `{!Elements A SA} `{!FinSet A SA}
  (f : B -> option D) (g : M B) : 
  dom (omap f g) ≡@{SA} 
  filter (is_Some ∘ (fun i => (g !! i) ≫= f)) (dom g).
Proof.
  intros x.
  rewrite elem_of_dom.
  rewrite elem_of_filter, elem_of_dom.
  rewrite lookup_omap.
  destruct (g !! x) as [gx|] eqn:e.
  - simpl.
    rewrite e.
    symmetry.
    rewrite 3!is_Some_alt.
    exact (and_True_r _).
  - simpl.
    symmetry.
    rewrite 3!is_Some_alt.
    easy.
Qed.


Lemma dom_omap_L {A SA M B D} `{FinMapDom A M SA}
  `{!Elements A SA} `{!FinSet A SA} `{!LeibnizEquiv SA}
  (f : B -> option D) (g : M B) : 
  dom (omap f g) =@{SA} 
  filter (is_Some ∘ (fun i => (g !! i) ≫= f)) (dom g).
Proof.
  apply set_eq.
  apply dom_omap.
Qed.

Lemma dom_map_compose {A SA B SB D SD M M'} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{FinMapDom B M' SB} `{Elements B SB} `{!FinSet B SB}
  `{SemiSet D SD} 
  (f : M B) (g : M' D) : 
  dom (g ∘ₘ f) ≡@{SA} filter (is_Some ∘ (fun i => (f !! i) ≫= (g !!.))) $ dom f.
Proof.
  apply dom_omap.
Qed.

Lemma dom_map_compose_L {A SA B SB D SD M M'} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{FinMapDom B M' SB} `{Elements B SB} `{!FinSet B SB}
  `{SemiSet D SD} `{!LeibnizEquiv SA}
  (f : M B) (g : M' D) : 
  dom (g ∘ₘ f) =@{SA} filter (is_Some ∘ (fun i => (f !! i) ≫= (g !!.))) $ dom f.
Proof.
  apply dom_omap_L.
Qed.



Lemma map_compose_img {A SA B SB D SD M M'} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{FinMapDom B M' SB} `{Elements B SB} `{!FinSet B SB}
  `{SemiSet D SD} 
  (f : M B) (g : M' D) :
  map_img (g ∘ₘ f) ≡@{SD} 
    (set_omap (g !!.) (map_img f :> SB)).
Proof.
  intros d.
  rewrite elem_of_set_omap.
  setoid_rewrite elem_of_map_img.
  setoid_rewrite map_lookup_compose.
  split.
  - intros (i & Hi).
    destruct (f !! i) as [fi|] eqn:Hf. 
    2: {
      discriminate Hi.
    }
    exists fi.
    split; [|apply Hi].
    eauto.
  - intros (fi & (i & Hf) & Hg).
    exists i.
    rewrite Hf.
    apply Hg.
Qed.

Lemma map_compose_img_L {A SA B SB D SD M M'} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{FinMapDom B M' SB} `{Elements B SB} `{!FinSet B SB}
  `{SemiSet D SD} `{!LeibnizEquiv SD}
  (f : M B) (g : M' D) :
  map_img (g ∘ₘ f) =@{SD} 
    (set_omap (g !!.) (map_img f :> SB)).
Proof.
  apply (_ : LeibnizEquiv SD).
  apply map_compose_img.
Qed.


Lemma natmap_compose_img {A} `{EqDecision A} `{Countable A} 
  (f : natmap nat) (g : natmap A) :
  map_img (g ∘ₘ f) = (set_omap (g !!.) (map_img f :> natset)) :> gmap.gset A.
Proof.
  apply map_compose_img_L.
Qed.



Lemma set_omap_lookup_subseteq {A SA B SB M} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{SemiSet B SB} (f : M B) (d : SA) :
  set_omap (f !!.) d ⊆@{SB} map_img f.
Proof.
  intros x.
  rewrite elem_of_set_omap, elem_of_map_img.
  intros (i & _ & Hf).
  eauto.
Qed.

Lemma map_img_to_set_omap_dom {A SA B SB M} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{SemiSet B SB} (f : M B) : 
  map_img f ≡@{SB} set_omap (f !!.) (dom f).
Proof.
  intros a.
  rewrite elem_of_map_img, elem_of_set_omap.
  split.
  - intros (i & Hi).
    exists i.
    split; [|easy].
    rewrite elem_of_dom, Hi.
    easy.
  - intros (i & _ & Hi).
    eauto.
Qed.

Lemma map_img_to_set_omap_dom_L {A SA B SB M} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{SemiSet B SB} `{!LeibnizEquiv SB} (f : M B) : 
  map_img f =@{SB} set_omap (f !!.) (dom f).
Proof.
  apply (_ : LeibnizEquiv SB).
  apply map_img_to_set_omap_dom.
Qed.

Lemma map_img_to_set_map_dom {A SA B SB M} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{SemiSet B SB} `{Inhabited B}
  (f : M B) :
  map_img f ≡@{SB} set_map (f !!!.) (dom f).
Proof.
  intros a.
  rewrite elem_of_map_img, elem_of_map.
  split.
  - intros (i & Hi).
    exists i.
    rewrite lookup_total_alt, Hi.
    split; [easy|].
    rewrite elem_of_dom, Hi.
    easy.
  - intros (i & Ha & Hi).
    exists i.
    rewrite Ha.
    now apply lookup_lookup_total_dom.
Qed.

Lemma map_img_to_set_map_dom_L {A SA B SB M} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{SemiSet B SB} `{Inhabited B} `{!LeibnizEquiv SB}
  (f : M B) :
  map_img f = set_map (f !!!.) (dom f) :> SB.
Proof.
  apply (_ : LeibnizEquiv SB).
  apply map_img_to_set_map_dom.
Qed.



Lemma set_omap_lookup_full {A SA B SB M} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{SemiSet B SB} (f : M B) (d' : SA) :
  dom f ⊆ d' -> set_omap (f !!.) d' ≡@{SB} map_img f.
Proof.
  intros HB b.
  apply set_subseteq_antisymm.
  - apply set_omap_lookup_subseteq.
  - rewrite map_img_to_set_omap_dom.
    apply set_omap_mono; easy.
Qed.

Lemma set_omap_lookup_full_L {A SA B SB M} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{SemiSet B SB} `{!LeibnizEquiv SB} (f : M B) (d' : SA) :
  dom f ⊆ d' -> set_omap (f !!.) d' =@{SB} map_img f.
Proof.
  intros Hd.
  apply set_eq, set_omap_lookup_full, Hd.
Qed.



Lemma map_img_list_idx_to_map {A SA} `{FinSet A SA} l : 
  map_img (list_idx_to_map l) ≡@{SA} list_to_set l.
Proof.
  intros x.
  rewrite elem_of_list_to_set.
  rewrite elem_of_map_img.
  setoid_rewrite lookup_list_idx_to_map.
  rewrite elem_of_list_lookup.
  reflexivity.
Qed.

Lemma map_img_list_idx_to_map_L {A SA} `{FinSet A SA} `{!LeibnizEquiv SA} l : 
  map_img (list_idx_to_map l) =@{SA} list_to_set l.
Proof.
  apply set_eq.
  apply map_img_list_idx_to_map.
Qed.

Lemma list_to_set_natset_to_list (A : natset) :
  list_to_set (natset_to_list A) = A.
Proof.
  apply set_eq.
  intros x.
  now rewrite elem_of_list_to_set, elem_of_natset_to_list.
Qed.

Lemma map_img_natmap_justify {A} `{EqDecision A} `{Countable A} 
  (f : natmap A) : 
  map_img (natmap_justify f) = map_img f :> gmap.gset A.
Proof.
  unfold natmap_justify.
  rewrite natmap_compose_img.
  apply set_omap_lookup_full_L.
  rewrite map_img_list_idx_to_map.
  rewrite list_to_set_natset_to_list.
  reflexivity.
Qed.



Definition sum_elim {A B C} (f : A -> C) (g : B -> C) : A + B -> C :=
  fun x => match x with | inl a => f a | inr b => g b end.

Global Arguments sum_elim {_ _ _} _ _ !_.


Definition sum_to_l {A B} : A + B -> option A :=
  sum_elim Some (λ _, None). 

Definition sum_to_r {A B} : A + B -> option B :=
  sum_elim (λ _, None) Some.



Definition natset_ofold
  (f : nat -> nat -> nat) (A : natset) : option nat :=
  set_fold (λ a oacc, Some (from_option (f a) a oacc)) None A.

Definition natset_omin (A : natset) : option nat :=
  natset_ofold min A.

Definition natmap_inv (f : natmap nat) : natmap nat :=
  map_fold (λ k v m, <[v := k]> m) ∅ f.

Definition fun_to_natmap {A} (f : nat -> A) (d : natset) : natmap A :=
  set_to_map (λ n, (n, f n)) d.

Lemma exists_eq_l_iff {A} (P : A -> Prop) (b : A) : 
  (∃ a, a = b ∧ P a) ↔ P b.
Proof.
  split; [|eauto].
  now intros (? & -> & ?).
Qed.

Lemma exists_eq_l_iff' {A} (P : A -> Prop) (b : A) : 
  (∃ a, b = a ∧ P a) ↔ P b.
Proof.
  setoid_rewrite (eq_comm b).
  apply exists_eq_l_iff.
Qed.

Lemma exists_eq_r_iff {A} (P : A -> Prop) (b : A) : 
  (∃ a, P a ∧ a = b) ↔ P b.
Proof.
  setoid_rewrite (and_comm (P _)).
  apply exists_eq_l_iff.
Qed.

Lemma exists_eq_r_iff' {A} (P : A -> Prop) (b : A) : 
  (∃ a, P a ∧ b = a) ↔ P b.
Proof.
  setoid_rewrite (and_comm (P _)).
  apply exists_eq_l_iff'.
Qed.

Lemma lookup_fun_to_natmap {A} (f : nat -> A) d n : 
  (fun_to_natmap f d) !! n = if decide (n ∈ d) then Some (f n) else None.
Proof.
  apply option_eq => a.
  unfold fun_to_natmap.
  rewrite lookup_set_to_map by easy.
  setoid_rewrite pair_eq.
  setoid_rewrite (and_comm (_ ∈ _)).
  setoid_rewrite <- (and_assoc _).
  rewrite exists_eq_l_iff.
  destruct (decide (n ∈ d)); [|easy].
  naive_solver.
Qed.


Lemma lookup_total_fun_to_natmap {A} `{Inhabited A} (f : nat -> A) d n : 
  (fun_to_natmap f d) !!! n = if decide (n ∈ d) then f n else inhabitant.
Proof.
  rewrite lookup_total_alt, lookup_fun_to_natmap.
  now destruct (decide (n ∈ d)).
Qed.


Lemma dom_fun_to_natmap {A} (f : nat -> A) d : 
  dom (fun_to_natmap f d) = d.
Proof.
  apply set_eq => n.
  rewrite elem_of_dom, lookup_fun_to_natmap.
  rewrite is_Some_alt.
  destruct (decide (n ∈ d)); easy.
Qed.

(* Definition natset_to_gset (d : natset) : gmap.gset nat :=
  set_map (λ x, x) d.

Lemma map_img_fun_to_natmap {A} `{EqDecision A} `{Countable A} 
  (f : nat -> A) d : 
  map_img (fun_to_natmap f d) = set_map f $ natset_to_gset d :> gmap.gset A.
Proof.
  rewrite map_img_to_set_omap_dom.
  apply set_eq => n.

  rewrite elem_of_dom, lookup_fun_to_natmap.
  rewrite is_Some_alt.
  destruct (decide (n ∈ d)); easy.
Qed. *)




(* Search gmap.gset gmultiset. *)

Definition gset_to_multiset {A} `{Countable A} (B : gmap.gset A) : gmultiset A :=
  GMultiSet $ (set_to_map (fun a => (a, 1%positive)) B).

Lemma multiplicity_gset_to_multiset  `{Countable A} (B : gmap.gset A) b : 
  multiplicity b (gset_to_multiset B) = if decide (b ∈ B) then 1 else 0.
Proof.
  unfold multiplicity. 
  simpl.
  destruct (set_to_map (λ a, (a, 1%positive)) B !! b) as [aval | ] eqn:e.
  - rewrite lookup_set_to_map in e by easy.
    destruct e as (y & Ha & (-> & <-)%pair_eq).
    now rewrite decide_True by easy.
  - rewrite decide_False; [easy|].
    intros Hin.
    enough (None = Some 1%positive) by easy.
    rewrite <- e.
    rewrite lookup_set_to_map by easy.
    now exists b.
Qed.
(* 
Definition natset_to_multiset (A : natset) : gmultiset nat :=
  gset_to_multiset (A:=nat) A.

Lemma multiplicity_natset_to_multiset (A : natset) a : 
  multiplicity a (natset_to_multiset A) = if decide (a ∈ A) then 1 else 0.
Proof.
  unfold multiplicity. 
  simpl.
  destruct (set_to_map (λ a, (a, 1%positive)) A !! a) as [aval | ] eqn:e.
  - rewrite lookup_set_to_map in e by easy.
    destruct e as (y & Ha & (-> & <-)%pair_eq).
    now rewrite decide_True by easy.
  - rewrite decide_False; [easy|].
    intros Hin.
    enough (None = Some 1%positive) by easy.
    rewrite <- e.
    rewrite lookup_set_to_map by easy.
    now exists a.
Qed. *)

Definition natmap_inj (f : natmap nat) : Prop :=
  Inj (=) (fun (x y : option nat) => 
    is_Some x ∧ is_Some y ∧ x = y) (f !!.).

Lemma natmap_inj_empty : natmap_inj ∅.
Proof.
  hnf.
  setoid_rewrite is_Some_alt.
  easy.
Qed.

Lemma natmap_inj_insert 
  (f : natmap nat) (k v : nat) (Hk : f !! k = None) : 
  natmap_inj (<[k:=v]> f) <->
  v ∉ (map_img f :> natset) ∧ natmap_inj f.
Proof.
  split.
  - intros Hinj.
    split.
    + intros Hv.
      rewrite elem_of_map_img in Hv.
      destruct Hv as (i & Hi).
      assert (Hki : k <> i) by (intros ->; congruence).
      generalize (Hinj k i).
      rewrite lookup_insert.
      rewrite lookup_insert_ne by easy.
      rewrite Hi.
      intros Heq.
      apply Hki, Heq.
      done.
    + intros x y Hxy.
      apply Hinj.
      assert (Hkx : k ≠ x) by (intros ->; now rewrite !is_Some_alt, Hk in Hxy).
      assert (Hky : k ≠ y) by (intros ->; now rewrite !is_Some_alt, Hk in Hxy).
      rewrite 2!lookup_insert_ne by easy.
      easy.
  - intros (Hv & Hinj).
    rewrite not_elem_of_map_img in Hv.
    intros x y (Hx & Hy & Heq).
    revert Heq.
    destruct (decide (x = k)) as [Hxk | Hxk];
    destruct (decide (y = k)) as [Hyk | Hyk].
    + congruence.
    + subst x.
      rewrite lookup_insert, (eq_comm _).
      rewrite lookup_insert_ne by easy.
      now intros ?%Hv.
    + subst y.
      rewrite lookup_insert.
      rewrite lookup_insert_ne by easy.
      now intros ?%Hv.
    + rewrite 2!lookup_insert_ne in * by easy.
      intros Heq.
      now apply Hinj.
Qed.

Lemma natmap_inv_minverses (f : natmap nat) 
  (Hf : natmap_inj f) : 
  minverses f (natmap_inv f).
Proof.
  intros i j.
  unfold natmap_inv.
  induction f as [ | k v f IH Hk] using map_first_key_ind.
  - easy.
  - rewrite lookup_insert_Some.
    rewrite map_fold_insert_first_key by easy.
    rewrite lookup_insert_Some.
    rewrite natmap_inj_insert in Hf by easy.
    destruct Hf as [Hfv Hf].
    rewrite <- IHf by easy.
    rewrite (and_comm _ (k = i)).
    apply or_iff_compat_l.
    rewrite not_elem_of_map_img in Hfv.
    apply and_iff_distr_r.
    intros Hij.
    apply ZifyClasses.not_morph.
    split.
    + intros <-.
      congruence.
    + intros <-.
      now apply Hfv in Hij.
Qed.

Lemma natmap_inj_alt (f : natmap nat) : 
  natmap_inj f <-> 
  forall x y, x ∈ dom f -> y ∈ dom f 
    -> f !! x = f !! y -> x = y.
Proof.
  unfold natmap_inj, Inj.
  apply forall_iff => x; apply forall_iff => y.
  rewrite 2!elem_of_dom.
  tauto.
Qed.

Lemma natmap_inj_alt' (f : natmap nat) : 
  natmap_inj f <-> 
  forall x y z, f !! x = Some z -> f !! y = Some z -> x = y.
Proof.
  rewrite natmap_inj_alt.
  split.
  - intros Hinj x y z Hx Hy.
    apply Hinj; rewrite 1?elem_of_dom, 1?Hx, 1?Hy; easy.
  - intros Hinj x y.
    rewrite 2!elem_of_dom.
    intros (z & Hx) (z' & Hy) Heq.
    replace z' with z in * by congruence.
    now apply Hinj with z.
Qed.


Lemma elem_of_seq_0 k n : k ∈ seq 0 n <-> k < n.
Proof.
  rewrite elem_of_seq; lia.
Qed.

Lemma natmap_inj_list_idx_to_map l : 
  natmap_inj (list_idx_to_map l) <-> NoDup l.
Proof.
  rewrite NoDup_alt.
  rewrite natmap_inj_alt'.
  setoid_rewrite lookup_list_idx_to_map.
  reflexivity.
Qed.

Lemma natmap_inj_list_to_map l : 
  NoDup l.*1 -> 
  natmap_inj (list_to_map l) <-> NoDup l.*2.
Proof.
  intros Hl1.
  rewrite natmap_inj_alt'.
  setoid_rewrite <- elem_of_list_to_map; [|easy..].
  rewrite NoDup_alt.
  split.
  - intros Hinj i j x Hi Hj.
    rewrite NoDup_alt in Hl1.
    assert (Hil : i < length l) by 
      (rewrite <- (length_fmap snd); now apply lookup_lt_Some with x).
    assert (Hjl : j < length l) by 
      (rewrite <- (length_fmap snd); now apply lookup_lt_Some with x).
    assert (Hl1i : l.*1 !! i = Some (l.*1 !!! i)). {
      apply list_lookup_lookup_total.
      rewrite lookup_lt_is_Some.
      rewrite length_fmap.
      easy.
    }
    assert (Hl1j : l.*1 !! j = Some (l.*1 !!! j)). {
      apply list_lookup_lookup_total.
      rewrite lookup_lt_is_Some.
      rewrite length_fmap.
      easy.
    }
    apply Hl1 with (l.*1 !!! i).
    + apply Hl1i.
    + enough (l.*1 !!! i = l.*1 !!! j) by congruence.
      apply Hinj with x.
      * rewrite elem_of_list_lookup_total.
        exists i.
        split; [easy|].
        rewrite (surjective_pairing (l !!! i)).
        apply pair_eq.
        erewrite list_lookup_total_fmap by easy.
        split; [easy|].
        erewrite <- list_lookup_total_fmap by easy.
        now apply list_lookup_total_correct.
      * rewrite elem_of_list_lookup_total.
        exists j.
        split; [easy|].
        rewrite (surjective_pairing (l !!! j)).
        apply pair_eq.
        erewrite list_lookup_total_fmap by easy.
        split; [easy|].
        erewrite <- list_lookup_total_fmap by easy.
        now apply list_lookup_total_correct.
  - intros Hinj x y z.
    rewrite 2!elem_of_list_lookup.
    intros (i & Hi) (j & Hj).
    enough (i = j) by congruence. 
    apply Hinj with z;
    erewrite list_lookup_fmap.
    + now rewrite Hi.
    + now rewrite Hj.
Qed.


Lemma natmap_inj_list_to_map_2 l : 
  NoDup l.*2 ->
  natmap_inj (list_to_map l).
Proof.
  rewrite natmap_inj_alt'.
  rewrite NoDup_alt.
  intros Hinj x y z Hx%elem_of_list_to_map_2 Hy%elem_of_list_to_map_2.
  rewrite elem_of_list_lookup in *.
  revert Hx Hy.
  intros (i & Hi) (j & Hj).
  enough (i = j) by congruence. 
  apply Hinj with z;
  erewrite list_lookup_fmap.
  + now rewrite Hi.
  + now rewrite Hj.
Qed.

Lemma NoDup_map_to_list_fst {A} (f : natmap A) : 
  NoDup (map_to_list f).*1.
Proof.
  unfold map_to_list.
  induction f as [|k v f Hfi Hmap IHf] using fin_maps.map_fold_ind.
  - constructor.
  - rewrite Hmap.
    rewrite fmap_cons.
    apply NoDup_cons.
    split; [|easy].
    fold (map_to_list f).
    rewrite (elem_of_list_fmap fst).
    intros ([y a] & Hy & Hya).
    rewrite elem_of_map_to_list in Hya.
    simpl in Hy.
    congruence.
Qed.


Lemma natmap_inj_alt'' (f : natmap nat) : 
  natmap_inj f <-> NoDup (map_to_list f).*2.
Proof.
  rewrite <- (list_to_map_to_list f) at 1.
  apply natmap_inj_list_to_map.
  apply NoDup_map_to_list_fst.
Qed. 


Lemma lookup_insert_alt {A} (f : natmap A) k v l :
  (<[k:=v]> f) !! l = if decide (k = l) then Some v else f !! l.
Proof.
  destruct (decide (k = l)) as [Heq | Hneq].
  - subst.
    apply lookup_insert.
  - by apply lookup_insert_ne.
Qed.

Lemma insert_to_insert_delete {A} (f : natmap A) k v : 
  <[k:=v]> f = <[k:=v]> (delete k f).
Proof.
  apply map_eq => i.
  rewrite 2!lookup_insert_alt.
  destruct (decide (k = i)) as [?|Hneq]; [easy|].
  rewrite lookup_delete_ne by easy.
  reflexivity.
Qed.



Lemma natmap_inv_insert_first_key f k v 
  (Hk : f !! k = None) (Hf : map_first_key (<[k:=v]> f) k) : 
  natmap_inv (<[k:=v]> f) = <[v:=k]> (natmap_inv f).
Proof.
  unfold natmap_inv.
  rewrite map_fold_insert_first_key by easy.
  easy.
Qed.


Definition natset_nth (A : natset) : natmap nat :=
  list_idx_to_map (natset_to_list A).

Definition natset_idx (A : natset) : natmap nat :=
  natmap_inv (natset_nth A).

Lemma natmap_inv_alt (f : natmap nat) : 
  natmap_inv f = list_to_map (prod_swap <$> map_to_list f).
Proof.
  induction f using map_first_key_ind;
  [reflexivity|].
  rewrite natmap_inv_insert_first_key by easy.
  rewrite map_to_list_insert_first_key by easy.
  rewrite IHf.
  reflexivity.
Qed.

Lemma map_lookup_Some_to_map_to_list {A} (f : natmap A) k v : 
  f !! k = Some v <-> (k, v) ∈ map_to_list f.
Proof.
  by rewrite elem_of_map_to_list.
Qed.


Lemma map_fst_prod_swap {A B} (l : list (A * B)) : 
  (prod_swap <$> l).*1 = l.*2.
Proof.
  rewrite <- list_fmap_compose.
  now apply map_ext.
Qed.

Lemma map_snd_prod_swap {A B} (l : list (A * B)) : 
  (prod_swap <$> l).*2 = l.*1.
Proof.
  rewrite <- list_fmap_compose.
  now apply map_ext.
Qed.

Lemma map_to_list_natmap_inv (f : natmap nat) (Hf : natmap_inj f) : 
  map_to_list (natmap_inv f) ≡ₚ prod_swap <$> map_to_list f.
Proof.
  rewrite natmap_inv_alt.
  apply map_to_list_to_map.
  rewrite map_fst_prod_swap.
  now rewrite <- natmap_inj_alt''.
Qed. 




Lemma natmap_inv_list_to_map l (Hl1 : NoDup l.*1) (Hl2 : NoDup l.*2): 
  natmap_inv (list_to_map l) =
  list_to_map (prod_swap <$> l).
Proof.
  apply map_to_list_inj.
  rewrite map_to_list_natmap_inv by now rewrite natmap_inj_list_to_map.
  rewrite 2!map_to_list_to_map by now rewrite 1?map_fst_prod_swap.
  reflexivity.
Qed.

Lemma zip_nil_r {A B} (l : list A) : 
  zip l (@nil B) = [].
Proof.
  induction l; simpl; easy.
Qed.

Lemma fmap_prod_swap_zip {A B} (l : list A) (l' : list B) : 
  prod_swap <$> zip l l' = zip l' l.
Proof.
  revert l';
  induction l; intros l'.
  - simpl.
    now rewrite zip_nil_r.
  - destruct l'; [reflexivity|].
    simpl.
    f_equal.
    apply IHl.
Qed.


Lemma lookup_natmap_inv_Some (f : natmap nat) k v : natmap_inj f ->
  natmap_inv f !! v = Some k  <->
  f !! k = Some v.
Proof.
  intros Hf.
  rewrite <- 2!elem_of_map_to_list.
  rewrite map_to_list_natmap_inv by easy.
  rewrite elem_of_list_fmap.
  split.
  - intros ((v' & k') & (? & ?)%pair_eq & Hy).
    simpl in *.
    now subst.
  - now exists (k, v).
Qed.

Lemma lookup_total_insert_alt {A} `{Inhabited A} (f : natmap A) k v l : 
  <[k:=v]> f !!! l = if decide (k = l) then v else f !!! l.
Proof.
  rewrite 2!lookup_total_alt, lookup_insert_alt.
  now destruct (decide (k = l)).
Qed.

Lemma fmap_snd_map_to_list_equiv_range (f : natmap nat) : 
  (map_to_list f).*2 ≡ₚ 
  ((f !!!.) <$> elements (dom f)).
Proof.
  induction f as [|k v f Hfk Hfirst IHf] using map_first_key_ind; 
  [easy|].
  rewrite dom_insert, elements_union_singleton by now rewrite not_elem_of_dom.
  rewrite fmap_cons.
  rewrite lookup_total_insert.
  rewrite map_to_list_insert_first_key by easy.
  rewrite fmap_cons.
  rewrite IHf.
  apply perm_skip.
  ereflexivity.
  apply list_fmap_ext.
  intros i x Hx.
  rewrite lookup_total_insert_alt.
  rewrite decide_False; [easy|].
  intros <-.
  enough (H : k ∈ dom f) by (now apply not_elem_of_dom in H).
  rewrite <- elem_of_elements.
  rewrite elem_of_list_lookup.
  eauto.
Qed.


Lemma fmap_snd_map_to_list_equiv_omap_range (f : natmap nat) : 
  (map_to_list f).*2 ≡ₚ 
  (omap (f !!.) $ elements (dom f)).
Proof.
  rewrite fmap_snd_map_to_list_equiv_range.
  rewrite list_fmap_alt.
  ereflexivity.
  apply list_omap_ext.
  rewrite Forall2_lookup.
  intros i.
  destruct (elements (dom f) !! i) eqn:e; [|constructor].
  constructor.
  rewrite lookup_lookup_total_dom; [easy|].
  rewrite <- elem_of_elements.
  rewrite elem_of_list_lookup.
  eauto.
Qed.

Lemma dom_natmap_inv (f : natmap nat) : 
  dom (natmap_inv f) = map_img f.
Proof.
  induction f as [|k v f Hfk Hfirst IHf] using map_first_key_ind;
  [now apply set_eq|].
  apply set_eq => x.
  rewrite natmap_inv_insert_first_key by easy.
  rewrite map_img_insert_notin_L by easy.
  rewrite dom_insert.
  now rewrite IHf.
Qed.

Lemma lookup_natmap_inv_Some_inv (f : natmap nat) k v : 
  natmap_inv f !! k = Some v ->
  f !! v = Some k.
Proof.
  induction f as [|v' k' f Hfk Hfirst IHf] using map_first_key_ind;
  [easy|].
  rewrite natmap_inv_insert_first_key by easy.
  rewrite 2!lookup_insert_alt.
  destruct (decide (k' = k)) as [-> | Hk].
  - intros [=->].
    rewrite decide_True by easy.
    easy.
  - intros Hfv%IHf.
    rewrite decide_False by congruence. 
    easy. 
Qed. 

Lemma natmap_inj_natmap_inv (f : natmap nat) :
  natmap_inj (natmap_inv f).
Proof.
  rewrite natmap_inj_alt'.
  intros ? ? ? ?%lookup_natmap_inv_Some_inv ?%lookup_natmap_inv_Some_inv.
  congruence.
Qed.

Lemma natmap_inv_natmap_inv (f : natmap nat) (Hf : natmap_inj f) : 
  natmap_inv (natmap_inv f) = f.
Proof.
  apply map_eq => k.
  apply option_eq => v.
  rewrite lookup_natmap_inv_Some by apply natmap_inj_natmap_inv.
  now apply lookup_natmap_inv_Some.
Qed.

Lemma natmap_inj_natset_nth A : 
  natmap_inj (natset_nth A).
Proof.
  rewrite natmap_inj_alt''.
  unfold natset_nth, list_idx_to_map.
  rewrite map_to_list_to_map.
  - rewrite snd_zip by now rewrite length_seq.
    unfold natset_to_list.
    rewrite merge_sort_Permutation.
    apply NoDup_elements.
  - rewrite fst_zip by now rewrite length_seq.
    apply NoDup_seq.
Qed.

Lemma natset_nth_to_natmap_inv A : 
  natset_nth A = natmap_inv (natset_idx A).
Proof.
  unfold natset_idx.
  rewrite natmap_inv_natmap_inv; [easy|].
  apply natmap_inj_natset_nth.
Qed.

Lemma natset_nth_idx_minverses A : 
  minverses (natset_nth A) (natset_idx A).
Proof.
  apply natmap_inv_minverses.
  apply natmap_inj_natset_nth.
Qed.








(* FIXME: Move *)
Definition edgeset_dom {A SA SAA}
  `{Elements (A * A) SAA}
  `{Empty SA} `{Union SA} `{Singleton A SA}
  (d : SAA) : SA :=
  set_bind (fun '(i, j) => {[i; j]}) d.

Lemma elem_of_edgeset_dom {A SA SAA}
  `{SemiSet A SA} `{FinSet (A * A) SAA}
  (d : SAA) (k : A) : 
  k ∈ (edgeset_dom d :> SA) <-> ∃ ij, ij ∈ d ∧ (k = ij.1 \/ k = ij.2).
Proof.
  unfold edgeset_dom.
  rewrite (elem_of_set_bind _ d k).
  apply exists_iff.
  intros (i, j).
  by rewrite elem_of_union, 2!elem_of_singleton.
Qed.



(* FIXME: Move *) 
Lemma dom_gset_to_multiset {A} `{Countable A} 
  (B : gmap.gset A) : 
  dom (gset_to_multiset B) = B.
Proof.
  apply set_eq => k.
  rewrite gmultiset_elem_of_dom, elem_of_multiplicity, 
    multiplicity_gset_to_multiset.
  destruct (decide (k ∈ B)); intuition lia.
Qed.

(* FIXME: Move *)
Section seq_set.

Context `{FinSet nat A}.

Definition seq_set start len : A := list_to_set $ seq start len.

Lemma elem_of_seq_set start len k : k ∈ seq_set start len <-> start <= k < start + len.
Proof.
  unfold seq_set.
  rewrite elem_of_list_to_set.
  apply elem_of_seq.
Qed.


Lemma elem_of_seq_set_0 len k : 
  k ∈ seq_set 0 len <-> k < len.
Proof.
  rewrite elem_of_seq_set.
  lia.
Qed.

Lemma seq_set_split start len1 len2 : 
  seq_set start (len1 + len2) ≡@{A}
  seq_set start len1 ∪ seq_set (start + len1) len2.
Proof.
  intros x.
  rewrite elem_of_union, 3!elem_of_seq_set.
  lia.
Qed.

Lemma seq_set_split_L `{!LeibnizEquiv A} start len1 len2 : 
  seq_set start (len1 + len2) =@{A}
  seq_set start len1 ∪ seq_set (start + len1) len2.
Proof.
  apply (_ : LeibnizEquiv A).
  apply seq_set_split.
Qed.


End seq_set.

Lemma dom_set_to_map {B C D K A} `{Elements B C} `{FinMapDom K M D}
  `{Countable K} (f : B → K * A) (g : C) :
  dom (set_to_map f g :> M A) ≡@{D} set_map (fst ∘ f) g.
Proof.
  unfold set_to_map.
  rewrite dom_list_to_map.
  rewrite <- list_fmap_compose.
  reflexivity.
Qed.

Lemma dom_set_to_map_L {B C D K A} `{Elements B C} `{FinMapDom K M D}
  `{Countable K} {HD : LeibnizEquiv D} (f : B → K * A) (g : C) :
  dom (set_to_map f g :> M A) =@{D} set_map (fst ∘ f) g.
Proof.
  apply HD.
  apply dom_set_to_map.
Qed.

Lemma map_img_set_to_map {B C K A M SA} `{FinMap K M}
  `{Countable K} `{FinSet B C} 
  `{SemiSet A SA}
  (f : B → K * A) (g : C) 
  (Hf : ∀ y y', y ∈ g → y' ∈ g → (f y).1 = (f y').1 → y = y') :
  map_img (set_to_map f g :> M A) ≡@{SA} set_map (snd ∘ f) g.
Proof.
  unfold set_map, set_to_map.
  pose proof (NoDup_elements g) as Hg.
  setoid_rewrite <- elem_of_elements in Hf.
  induction (elements g) as [|b bs IHbs].
  - set_solver.
  - apply NoDup_cons in Hg as (Hb & Hbs).
    rewrite 2!fmap_cons. 
    rewrite (surjective_pairing (f b)), list_to_map_cons, list_to_set_cons.
    rewrite map_img_insert_notin.
    + rewrite <- IHbs; [reflexivity | | easy].
      intros y y' Hy Hy'.
      apply Hf; by apply elem_of_list_further.
    + apply not_elem_of_list_to_map.
      rewrite <- list_fmap_compose.
      intros Hfalse; apply Hb.
      apply elem_of_list_fmap in Hfalse as (b' & Hfb & Hb').
      enough (b = b') by congruence.
      apply Hf; try constructor; easy.
Qed.


Lemma map_img_set_to_map_L {B C K A M SA} `{FinMap K M}
  `{Countable K} `{FinSet B C} 
  `{SemiSet A SA} `{HSA : !LeibnizEquiv SA}
  (f : B → K * A) (g : C) 
  (Hf : ∀ y y', y ∈ g → y' ∈ g → (f y).1 = (f y').1 → y = y') :
  map_img (set_to_map f g :> M A) =@{SA} set_map (snd ∘ f) g.
Proof.
  apply HSA.
  now apply map_img_set_to_map.
Qed.

Lemma set_map_set_map {A B C D E F} 
  `{Elements A D} `{FinSet B E}
  `{SemiSet C F}
  (f : A -> B) (g : B -> C) (d : D) : 
  set_map g (set_map f d :> E) ≡@{F} set_map (g ∘ f) d.
Proof.
  unfold set_map.
  intros x.
  set_solver.
Qed.

Lemma set_map_set_map_L {A B C D E F} 
  `{Elements A D} `{FinSet B E}
  `{SemiSet C F} `{HF : !LeibnizEquiv F}
  (f : A -> B) (g : B -> C) (d : D) : 
  set_map g (set_map f d :> E) =@{F} set_map (g ∘ f) d.
Proof.
  apply HF.
  now apply set_map_set_map.
Qed.

Lemma set_map_to_omap_gen {A SA B SB} 
  `{FinSet A SA}
  `{SemiSet B SB}
  (f : A -> B) (g : A -> option B) (d : SA)
  (Hfg : forall a, a ∈ d -> g a = Some (f a)) :
  set_map f d ≡@{SB} set_omap g d.
Proof.
  intros a.
  rewrite elem_of_set_omap, elem_of_map.
  naive_solver.
Qed.

Lemma set_map_to_omap_gen_L {A SA B SB} 
  `{FinSet A SA} `{SemiSet B SB} `{!LeibnizEquiv SB}
  (f : A -> B) (g : A -> option B) (d : SA)
  (Hfg : forall a, a ∈ d -> g a = Some (f a)) :
  set_map f d =@{SB} set_omap g d.
Proof.
  apply (_ : LeibnizEquiv SB).
  by apply set_map_to_omap_gen.
Qed.

Lemma set_map_lookup_total_to_set_omap_lookup_gen {A SA B SB M} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{SemiSet B SB} `{Inhabited B}
  (f : M B) (d' : SA) : d' ⊆ dom f ->
  set_map (f !!!.) d' ≡@{SB} set_omap (f !!.) d'.
Proof.
  intros Hd'.
  apply set_map_to_omap_gen.
  intros a Ha.
  apply lookup_lookup_total_dom.
  by apply Hd', Ha.
Qed.

Lemma set_map_lookup_total_to_set_omap_lookup_gen_L {A SA B SB M} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{SemiSet B SB} `{Inhabited B} `{!LeibnizEquiv SB}
  (f : M B) (d' : SA) : d' ⊆ dom f ->
  set_map (f !!!.) d' =@{SB} set_omap (f !!.) d'.
Proof.
  intros Hd'.
  apply (_ : LeibnizEquiv SB).
  by apply set_map_lookup_total_to_set_omap_lookup_gen.
Qed.

Lemma set_map_lookup_total_eq_map_img {A SA B SB M} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{SemiSet B SB} `{Inhabited B} 
  (f : M B) (d' : SA) : d' ≡@{SA} dom f ->
  set_map (f !!!.) d' ≡@{SB} map_img f.
Proof.
  intros ->.
  rewrite set_map_lookup_total_to_set_omap_lookup_gen by reflexivity.
  apply set_omap_lookup_full; reflexivity.
Qed.

Lemma set_map_lookup_total_eq_map_img_L {A SA B SB M} 
  `{FinMapDom A M SA} `{Elements A SA} `{!FinSet A SA}
  `{SemiSet B SB} `{Inhabited B} `{!LeibnizEquiv SB}
  (f : M B) (d' : SA) : d' =@{SA} dom f ->
  set_map (f !!!.) d' =@{SB} map_img f.
Proof.
  intros ->.
  by apply set_eq, set_map_lookup_total_eq_map_img.
Qed.



Lemma map_img_natmap_inv_subseteq (f : natmap nat) : 
  map_img (natmap_inv f) ⊆ dom f.
Proof.
  intros n.
  rewrite elem_of_map_img.
  intros (i & Hi%lookup_natmap_inv_Some_inv).
  now rewrite elem_of_dom, Hi.
Qed.

Lemma map_img_natmap_inv (f : natmap nat) (Hf : natmap_inj f) : 
  map_img (natmap_inv f) = dom f.
Proof.
  apply set_eq => n.
  rewrite elem_of_map_img.
  setoid_rewrite lookup_natmap_inv_Some; [|easy].
  rewrite elem_of_dom.
  reflexivity.
Qed.

Lemma dom_natset_nth (A : natset) : 
  dom (natset_nth A) = seq_set 0 (size A) :> natset.
Proof.
  unfold natset_nth.
  rewrite dom_list_idx_to_map.
  rewrite length_natset_to_list.
  reflexivity.
Qed.

Lemma map_img_natset_nth (A : natset) : 
  map_img (natset_nth A) = A.
Proof.
  unfold natset_nth. 
  rewrite map_img_list_idx_to_map_L.
  apply list_to_set_natset_to_list.
Qed.

Lemma dom_natset_idx (A : natset) : 
  dom (natset_idx A) = A.
Proof.
  unfold natset_idx.
  rewrite dom_natmap_inv.
  apply map_img_natset_nth.
Qed.

(* Lemma dom_natset_idx_equiv `{FinSet nat SA} `{!LeibnizEquiv SA} (A : natset) : 
  dom (natset_idx A) =@{SA} set_map (λ x, x) A. *)

Definition set_cast {A SA SA'} `{Elements A SA}
  `{Singleton A SA'} `{Empty SA'} `{Union SA'} (d : SA) : SA' :=
  set_map Datatypes.id d.

Lemma elem_of_set_cast {A SA SA'} `{FinSet A SA} 
  `{SemiSet A SA'} (d : SA) a : 
  a ∈ (set_cast d :> SA') ↔ a ∈ d.
Proof.
  unfold set_cast.
  by rewrite elem_of_map, exists_eq_l_iff'.
Qed.


Lemma map_img_natmap_inv' `{FinSet nat A} 
  `{!LeibnizEquiv A} f (Hf : natmap_inj f) :
  map_img (natmap_inv f) =@{A} set_cast (dom f).
Proof.
  apply set_eq => x.
  rewrite <- map_img_natmap_inv by easy.
  rewrite elem_of_set_cast, 2!elem_of_map_img.
  reflexivity.
Qed.

Lemma map_img_natset_idx `{FinSet nat SA} `{!LeibnizEquiv SA} 
  (A : natset) : 
  map_img (natset_idx A) =@{SA} seq_set 0 (size A).
Proof.
  unfold natset_idx.
  apply set_eq => x.
  rewrite map_img_natmap_inv' by apply natmap_inj_natset_nth.
  rewrite dom_natset_nth, elem_of_set_cast, 2!elem_of_seq_set.
  reflexivity.
Qed.

Lemma natmap_inj_natset_idx (A : natset) :
  natmap_inj (natset_idx A).
Proof.
  apply natmap_inj_natmap_inv.
Qed.


Definition set_inl {A SA B SAB} `{Elements A SA}
  `{Singleton (A + B) SAB} `{Empty SAB} `{Union SAB} 
  (d : SA) : SAB :=
  set_map inl d.

Definition set_inr {A B SB SAB} `{Elements B SB}
  `{Singleton (A + B) SAB} `{Empty SAB} `{Union SAB} 
  (d : SB) : SAB :=
  set_map inr d.

Definition set_outl {A SA B SAB} `{Elements (A + B) SAB}
  `{Singleton A SA} `{Empty SA} `{Union SA} 
  (d : SAB) : SA :=
  set_omap sum_to_l d.

Definition set_outr {A B SB SAB} `{Elements (A + B) SAB}
  `{Singleton B SB} `{Empty SB} `{Union SB} 
  (d : SAB) : SB :=
  set_omap sum_to_r d.

Definition sum_set {A SA B SB SAB} `{Elements A SA} `{Elements B SB}
  `{Singleton (A + B) SAB} `{Empty SAB} `{Union SAB} 
  (d : SA) (d' : SB) : SAB :=
  set_inl d ∪ set_inr d'.


Lemma set_inl_eq {A SA B SAB} `{Elements A SA}
  `{Singleton (A + B) SAB} `{Empty SAB} `{Union SAB} 
  (d : SA) : 
  set_inl d = set_map inl d :> SAB.
Proof. by reflexivity. Qed.
Lemma set_inr_eq {A B SB SAB} `{Elements B SB}
  `{Singleton (A + B) SAB} `{Empty SAB} `{Union SAB} 
  (d : SB) : 
  set_inr d = set_map inr d :> SAB.
Proof. by reflexivity. Qed.
Lemma set_outl_eq {A SA B SAB} `{Elements (A + B) SAB}
  `{Singleton A SA} `{Empty SA} `{Union SA} 
  (d : SAB) : 
  set_outl d = set_omap sum_to_l d :> SA.
Proof. by reflexivity. Qed.
Lemma set_outr_eq {A B SB SAB} `{Elements (A + B) SAB}
  `{Singleton B SB} `{Empty SB} `{Union SB} 
  (d : SAB) : 
  set_outr d = set_omap sum_to_r d :> SB.
Proof. by reflexivity. Qed.
Lemma sum_set_eq {A SA B SB SAB} `{Elements A SA} `{Elements B SB}
  `{Singleton (A + B) SAB} `{Empty SAB} `{Union SAB} 
  (d : SA) (d' : SB) : 
  sum_set d d' = set_inl d ∪ set_inr d' :> SAB.
Proof. by reflexivity. Qed.

(* FIXME: Move *) 
Lemma sum_match_to_sum_elim {A B C} (P : A -> C) (Q : B -> C) (ab : A + B) : 
  match ab with 
  | inl a => P a
  | inr b => Q b
  end = sum_elim P Q ab.
Proof.
  by destruct ab.
Qed.

Lemma elem_of_set_inl_cases {A SA B SAB} `{FinSet A SA}
  `{SemiSet (A + B) SAB} (d : SA) (ab : A + B) :
  ab ∈@{SAB} set_inl d <->
  match ab with
  | inl a => a ∈ d
  | inr b => False
  end.
Proof.
  unfold set_inl.
  rewrite elem_of_map.
  destruct ab as [a | b]; [|split; try intros []; easy].
  naive_solver.
Qed.

Lemma elem_of_set_inr_cases {A B SB SAB} `{FinSet B SB}
  `{SemiSet (A + B) SAB} (d : SB) (ab : A + B) :
  ab ∈@{SAB} set_inr d <->
  match ab with
  | inl a => False
  | inr b => b ∈ d
  end.
Proof.
  unfold set_inr.
  rewrite elem_of_map.
  destruct ab as [a | b]; [split; try intros []; easy|].
  naive_solver.
Qed.

Lemma elem_of_sum_set_cases {A SA B SB SAB} 
  `{FinSet A SA} `{FinSet B SB} `{SemiSet (A + B) SAB} 
  (d : SA) (d' : SB) (ab : A + B) :
  ab ∈@{SAB} sum_set d d' <-> 
  match ab with
  | inl a => a ∈ d
  | inr b => b ∈ d'
  end.
Proof.
  unfold sum_set.
  rewrite elem_of_union, elem_of_set_inl_cases, elem_of_set_inr_cases.
  by destruct ab; naive_solver.
Qed.

Lemma elem_of_set_outl {A SA B SAB} `{SemiSet A SA}
  `{FinSet (A + B) SAB} (d : SAB) (a : A) :
  a ∈@{SA} set_outl d <-> inl a ∈@{SAB} d.
Proof.
  unfold set_outl.
  rewrite elem_of_set_omap.
  split; [|intros ?; by exists (inl a)].
  by intros ([] & ? & [= ->]).
Qed.

Lemma elem_of_set_outr {A B SB SAB} `{SemiSet B SB}
  `{FinSet (A + B) SAB} (d : SAB) (b : B) :
  b ∈@{SB} set_outr d <-> inr b ∈@{SAB} d.
Proof.
  unfold set_outr.
  rewrite elem_of_set_omap.
  split; [|intros ?; by exists (inr b)].
  by intros ([] & ? & [= ->]).
Qed.

Lemma set_outl_union {A SA B SAB} `{SemiSet A SA}
  `{FinSet (A + B) SAB} (d d' : SAB) :
  set_outl (d ∪ d') ≡@{SA} set_outl d ∪ set_outl d'.
Proof.
  apply set_omap_union.
Qed.

Lemma set_outr_union {A B SB SAB} `{SemiSet B SB}
  `{FinSet (A + B) SAB} (d d' : SAB) :
  set_outr (d ∪ d') ≡@{SB} set_outr d ∪ set_outr d'.
Proof.
  apply set_omap_union.
Qed.



Lemma set_outl_inl {A SA B SAB} `{FinSet A SA} `{FinSet (A + B) SAB}
  (d : SA) : 
  set_outl (set_inl d :> SAB) ≡@{SA} d.
Proof.
  intros x.
  by rewrite elem_of_set_outl, elem_of_set_inl_cases.
Qed.

Lemma set_outr_inr {A B SB SAB} `{FinSet B SB} `{FinSet (A + B) SAB}
  (d : SB) : 
  set_outr (set_inr d :> SAB) ≡@{SB} d.
Proof.
  intros x.
  by rewrite elem_of_set_outr, elem_of_set_inr_cases.
Qed.

Lemma set_outl_inl_L {A SA B SAB} `{FinSet A SA} `{FinSet (A + B) SAB}
  `{!LeibnizEquiv SA} (d : SA) : 
  set_outl (set_inl d :> SAB) =@{SA} d.
Proof.
  apply set_eq, set_outl_inl.
Qed.

Lemma set_outr_inr_L {A B SB SAB} `{FinSet B SB} `{FinSet (A + B) SAB}
  `{!LeibnizEquiv SB} (d : SB) : 
  set_outr (set_inr d :> SAB) =@{SB} d.
Proof.
  apply set_eq, set_outr_inr.
Qed.

(* TODO: Improve hypotheses of these four *)
Lemma set_outl_inr {A SA B SB SAB} 
  `{FinSet A SA} `{FinSet B SB} `{FinSet (A + B) SAB}
  (d : SB) : 
  set_outl (set_inr d :> SAB) ≡@{SA} ∅.
Proof.
  intros x.
  by rewrite elem_of_set_outl, elem_of_set_inr_cases, elem_of_empty.
Qed.

Lemma set_outr_inl {A SA B SB SAB} 
  `{FinSet A SA} `{FinSet B SB} `{FinSet (A + B) SAB}
  (d : SA) : 
  set_outr (set_inl d :> SAB) ≡@{SB} ∅.
Proof.
  intros x.
  by rewrite elem_of_set_outr, elem_of_set_inl_cases, elem_of_empty.
Qed.

Lemma set_outl_inr_L {A SA B SB SAB} 
  `{FinSet A SA} `{FinSet B SB} `{FinSet (A + B) SAB} `{!LeibnizEquiv SA}
  (d : SB) : 
  set_outl (set_inr d :> SAB) =@{SA} ∅.
Proof.
  apply set_eq, set_outl_inr.
Qed.

Lemma set_outr_inl_L {A SA B SB SAB} 
  `{FinSet A SA} `{FinSet B SB} `{FinSet (A + B) SAB} `{!LeibnizEquiv SB}
  (d : SA) : 
  set_outr (set_inl d :> SAB) =@{SB} ∅.
Proof.
  apply set_eq, set_outr_inl.
Qed.



(* TODO: Improve hypotheses of these: *)
Lemma set_outl_sum_set {A SA B SB SAB} 
  `{FinSet A SA} `{FinSet B SB} `{FinSet (A + B) SAB}
  (d : SA) (d' : SB) : 
  set_outl (sum_set d d' :> SAB) ≡@{SA} d.
Proof.
  unfold sum_set.
  rewrite set_outl_union.
  rewrite set_outl_inl, set_outl_inr, (union_empty_r _).
  reflexivity.
Qed.

Lemma set_outl_sum_set_L {A SA B SB SAB} 
  `{FinSet A SA} `{FinSet B SB} `{FinSet (A + B) SAB} `{!LeibnizEquiv SA}
  (d : SA) (d' : SB) : 
  set_outl (sum_set d d' :> SAB) =@{SA} d.
Proof.
  apply set_eq, set_outl_sum_set.
Qed.

Lemma set_outr_sum_set {A SA B SB SAB} 
  `{FinSet A SA} `{FinSet B SB} `{FinSet (A + B) SAB}
  (d : SA) (d' : SB) : 
  set_outr (sum_set d d' :> SAB) ≡@{SB} d'.
Proof.
  unfold sum_set.
  rewrite set_outr_union.
  rewrite set_outr_inl, set_outr_inr, (union_empty_l _).
  reflexivity.
Qed.

Lemma set_outr_sum_set_L {A SA B SB SAB} 
  `{FinSet A SA} `{FinSet B SB} `{FinSet (A + B) SAB} `{!LeibnizEquiv SB}
  (d : SA) (d' : SB) : 
  set_outr (sum_set d d' :> SAB) =@{SB} d'.
Proof.
  apply set_eq, set_outr_sum_set.
Qed.

Lemma set_sum_to_sum_set {A SA B SB SAB} 
  `{FinSet A SA} `{FinSet B SB} `{FinSet (A + B) SAB}
  (d : SAB) : 
  d ≡@{SAB} sum_set (set_outl d :> SA) (set_outr d :> SB).
Proof.
  intros x.
  rewrite elem_of_sum_set_cases.
  destruct x; 
  by rewrite 1?elem_of_set_outl, 1?elem_of_set_outr.
Qed.

Lemma set_sum_to_sum_set_L {A SA B SB SAB} 
  `{FinSet A SA} `{FinSet B SB} `{FinSet (A + B) SAB} `{!LeibnizEquiv SAB}
  (d : SAB) : 
  d =@{SAB} sum_set (set_outl d :> SA) (set_outr d :> SB).
Proof.
  apply set_eq, set_sum_to_sum_set.
Qed.


(* TODO: Use natset_nth / _idx to build the "shifted" (i.e. justified) 
  versions *)


Lemma size_set_map_le `{FinSet A SA} `{FinSet B SB} (f : A -> B) (s : SA) :
  size (set_map f s :> SB) <= size s.
Proof.
  revert s.
  apply set_ind.
  - by intros ? ? ->.
  - by rewrite set_map_empty, 2!size_empty.
  - intros a s Ha IH.
    rewrite size_union by set_solver.
    rewrite set_map_union, set_map_singleton, size_singleton.
    rewrite size_union_alt, size_singleton.
    enough (size (set_map f s ∖ {[f a]} :> SB) ≤ size (set_map f s :> SB)) by lia.
    apply subseteq_size.
    set_solver.
Qed.

Lemma size_set_map_eq_iff `{FinSet A SA} `{FinSet B SB} (f : A -> B) (s : SA) :
  size (set_map f s :> SB) = size s <->
  (∀ a b, a ∈ s -> b ∈ s -> f a = f b -> a = b).
Proof.
  split.
  - intros Hsize.
    intros a b Ha Hb Hfab.
    destruct (decide (a = b)) as [Hab|Hab]; [easy|].
    exfalso.
    assert (Hrw : s ≡ ({[a; b]} ∪ s ∖ {[a; b]})). 1: {
      intros x.
      rewrite elem_of_union, elem_of_difference, not_elem_of_union, 
        2!not_elem_of_singleton.
      rewrite elem_of_union, 2!elem_of_singleton.
      destruct (decide (x = a)); [|destruct (decide (x = b))];
      subst;
      naive_solver.
    }
    rewrite Hrw in Hsize.
    rewrite size_union in Hsize 
      by (intros x Hx (_ & Hx')%elem_of_difference; apply Hx', Hx).
    revert Hsize.
    rewrite size_union 
      by (intros x ?%elem_of_singleton ?%elem_of_singleton; congruence).
    rewrite set_map_union.
    rewrite set_map_union, 2!set_map_singleton. 
    rewrite Hfab.
    rewrite (union_idemp _).
    rewrite size_union_alt.
    rewrite 3!size_singleton.
    enough (size (set_map f (s ∖ {[a; b]}) ∖ {[f b]} :> SB) ≤ size (s ∖ {[a;b]})) 
      by lia.
    erewrite subseteq_size by (apply subseteq_difference_l; reflexivity).
    apply size_set_map_le.
  - pattern s; revert s.
    apply set_ind.
    + intros s s' Hs Happ Hinj.
      rewrite <- Hs.
      apply Happ.
      intros ? ? ? ?; apply Hinj; by rewrite <- Hs.
    + intros _.
      by rewrite set_map_empty, 2!size_empty.
    + intros a s Ha IH Hinj.
      specialize (IH ltac:(intros ? ? ? ?; apply Hinj; set_solver)).
      rewrite set_map_union, set_map_singleton. 
      rewrite size_union; 
        first by rewrite size_union, 2!size_singleton, IH by set_solver.
      intros x ->%elem_of_singleton (b & Hfab & Hb)%elem_of_map.
      assert (Hab : a ≠ b) by congruence.
      apply Hab.
      apply Hinj; set_solver.
Qed.


Lemma natmap_inj_alt_size (f : natmap nat) :
  natmap_inj f <-> size (dom f :> natset) = size (map_img f :> natset).
Proof.
  rewrite map_img_to_set_map_dom_L.
  rewrite (eq_comm _).
  rewrite size_set_map_eq_iff.
  rewrite natmap_inj_alt'. 
  apply forall_iff => a.
  apply forall_iff => b.
  split.
  - intros Hz (fa & Hfa)%elem_of_dom (fb & Hfb)%elem_of_dom Hfafb.
    rewrite (lookup_total_correct _ _ _ Hfa), 
      (lookup_total_correct _ _ _ Hfb) in Hfafb.
    subst fb.
    eauto.
  - intros IH z Hfa Hfb.
    apply IH; [by eapply elem_of_dom_2; eassumption..|].
    by erewrite 2!lookup_total_correct by eassumption.
Qed.



(* FIXME: Move *)
Lemma gset_to_multiset_union `{Countable A} (g h : gmap.gset A) : 
  gset_to_multiset (g ∪ h) = gset_to_multiset g ∪ gset_to_multiset h.
Proof.
  apply gmultiset_eq => a.
  rewrite multiplicity_union, 3!multiplicity_gset_to_multiset.
  destruct (decide (a ∈ g ∪ h)) as [e|e], (decide (a ∈ g)), (decide (a ∈ h));
  rewrite elem_of_union in e; done + naive_solver. 
Qed.

Lemma dom_gmultiset_map {A B} `{Countable A} `{Countable B}
  (g : gmultiset A) (f : A -> B) : 
  dom (gmultiset_map f g) = set_map f $ dom g.
Proof.
  apply set_eq => x.
  rewrite gmultiset_elem_of_dom, elem_of_gmultiset_map, elem_of_map.
  setoid_rewrite gmultiset_elem_of_dom.
  reflexivity.
Qed.

Lemma dom_gmultiset_union {A} `{Countable A}
  (g h : gmultiset A) : 
  dom (g ∪ h) = dom g ∪ dom h.
Proof.
  apply set_eq => x.
  rewrite elem_of_union, 3!gmultiset_elem_of_dom.
  apply gmultiset_elem_of_union.
Qed.

(* FIXME: Move *)
Lemma set_map_id `{FinSet A SA} (s : SA) :
  set_map (λ x, x) s ≡ s.
Proof. set_solver. Qed.

Lemma set_map_id_L `{FinSet A SA} `{!LeibnizEquiv SA} (s : SA) :
  set_map (λ x, x) s = s.
Proof. set_solver. Qed.

Lemma set_map_id_inhom `{FinSet A SA} `{FinSet A SA'} (s : SA) :
  set_map (λ x, x) s ≡@{SA'} set_cast s.
Proof. set_solver. Qed.

Lemma set_map_id_inhom_L `{FinSet A SA} `{FinSet A SA'} 
  `{!LeibnizEquiv SA} (s : SA) :
  set_map (λ x, x) s =@{SA'} set_cast s.
Proof. set_solver. Qed.

(* FIXME: Move *)
Global Instance set_unfold_elem_of_set_cast `{FinSet A SA, SemiSet A SA'} 
  (a : A) (s : SA) P : 
  SetUnfoldElemOf a s P -> 
  SetUnfoldElemOf a (set_cast s :> SA') P.
Proof. intros []. constructor. by rewrite elem_of_set_cast. Qed.

(* FIXME: Move *)
Lemma gmultiset_map_compose `{Countable A} `{Countable B} `{Countable D}
  (f : A -> B) (g : B -> D) (s : gmultiset A) :
  gmultiset_map (g ∘ f) s = gmultiset_map g (gmultiset_map f s).
Proof.
  induction s using gmultiset_ind; [easy|].
  rewrite 3!gmultiset_map_disj_union, 3!gmultiset_map_singleton.
  unfold compose in *.
  congruence.
Qed.



(* Lemma dom_mg_vert_idx `{FinSet nat A} `{!LeibnizEquiv A} : 
  dom G.(mg_vert_idx) =@{A} G. *)
(* FIXME: Move *)
Lemma set_map_add_seq_set `{FinSet nat SA} `{FinSet nat SB} `{!LeibnizEquiv SB}
  start len diff : 
  set_map (Nat.add diff) (seq_set start len :> SA) =@{SB} seq_set (start + diff) len.
Proof.
  apply set_eq => x. 
  rewrite elem_of_map.
  setoid_rewrite elem_of_seq_set.
  split; [intros []; lia|].
  intros ?.
  exists (x - diff).
  lia.
Qed.

(* FIXME: Move *)
Lemma exists_iff_of_unique {A} {P : A -> Prop} (a : A) : 
  (∀ b, P b -> b = a) ->
  (∃ b, P b) <-> P a.
Proof.
  intros HP.
  split; [|eauto].
  intros [b Hb].
  apply HP in Hb as Hab.
  by subst.
Qed.


Lemma map_img_omap {K A SA B SB M}
  `{FinMap K M} `{FinSet A SA} `{SemiSet B SB}
  (f : M A) (g : A -> option B) :
  map_img (omap g f) ≡@{SB} set_omap g $ (map_img f :> SA).
Proof.
  intros x.
  rewrite elem_of_map_img.
  setoid_rewrite lookup_omap_Some.
  rewrite elem_of_set_omap.
  setoid_rewrite elem_of_map_img.
  naive_solver.
Qed.


Lemma map_img_omap_L {K A SA B SB M}
  `{FinMap K M} `{FinSet A SA} `{SemiSet B SB} `{!LeibnizEquiv SB}
  (f : M A) (g : A -> option B) :
  map_img (omap g f) =@{SB} set_omap g $ (map_img f :> SA).
Proof.
  apply set_eq, map_img_omap.
Qed.




(* FIXME: Move *)
Lemma exists_or {A} {P Q : A -> Prop} :
  (∃ a, (P a ∨ Q a)) <->
  (∃ a, P a) ∨ (∃ a, Q a).
Proof. naive_solver. Qed.

Lemma edgeset_dom_union `{SemiSet A SA} `{FinSet (A * A) SAA}
  (f g : SAA) : 
  edgeset_dom (f ∪ g) ≡@{SA} edgeset_dom f ∪ edgeset_dom g.
Proof.
  intros x.
  rewrite elem_of_union, 3!elem_of_edgeset_dom.
  setoid_rewrite elem_of_union.
  setoid_rewrite <- and_or_distr_same_r; [|reflexivity].
  rewrite exists_or.
  reflexivity.
Qed.

Lemma edgeset_dom_union_L `{SemiSet A SA} `{FinSet (A * A) SAA} 
  `{!LeibnizEquiv SA} (f g : SAA) : 
  edgeset_dom (f ∪ g) =@{SA} edgeset_dom f ∪ edgeset_dom g.
Proof.
  apply set_eq.
  apply edgeset_dom_union.
Qed.

Lemma edgeset_dom_prod_map `{FinSet A SA} `{SemiSet B SB} 
  `{FinSet (A * A) SAA} `{FinSet (B * B) SBB} 
  (f : SAA) (g : A -> B) : 
  edgeset_dom (set_map (prod_map g g) f :> SBB) ≡@{SB} 
    set_map g $ (edgeset_dom f :> SA).
Proof.
  intros x.
  rewrite elem_of_map, elem_of_edgeset_dom.
  setoid_rewrite elem_of_edgeset_dom.
  setoid_rewrite elem_of_map.
  naive_solver.
Qed.

Lemma edgeset_dom_prod_map_L `{FinSet A SA} `{SemiSet B SB} `{!LeibnizEquiv SB}
  `{FinSet (A * A) SAA} `{FinSet (B * B) SBB} 
  (f : SAA) (g : A -> B) : 
  edgeset_dom (set_map (prod_map g g) f :> SBB) =@{SB} 
    set_map g $ (edgeset_dom f :> SA).
Proof.
  apply set_eq, edgeset_dom_prod_map.
Qed.

Lemma dom_gmultiset_disj_union `{Countable A} 
  (d d' : gmultiset A) :
  dom (d ⊎ d') = dom d ∪ dom d'.
Proof.
  apply set_eq => x.
  rewrite elem_of_union, 3!gmultiset_elem_of_dom.
  by rewrite gmultiset_elem_of_disj_union.
Qed.


Lemma not_elem_of_gmultiset `{Countable A} (s : gmultiset A) (a : A) :
  a ∉ s <-> multiplicity a s = 0.
Proof.
  unfold elem_of, gmultiset_elem_of.
  lia.
Qed.

Lemma multiplicity_eq `{Countable A} (s : gmultiset A) (a : A) (n : nat) : 
  (a ∈ s -> multiplicity a s = n) ->
  (a ∉ s -> 0 = n) ->
  multiplicity a s = n.
Proof.
  intros Helem Hnelem.
  destruct (decide (a ∈ s)) as [e|e]; [by apply Helem|].
  rewrite <- Hnelem by apply e.
  by apply not_elem_of_gmultiset.
Qed.



(* FIXME: This isn't in there??? *)
Definition dec_of_iff {P Q} (H : Decision P) (HPQ : P <-> Q) : Decision Q :=
  match H with 
  | left HP => left (proj1 HPQ HP)
  | right HnP => right (fun HQ => HnP (proj2 HPQ HQ))
  end.

Definition dec_of_iff' {P Q} (H : Decision P) (HPQ : Q <-> P) : Decision Q :=
  dec_of_iff H (iff_sym HPQ).

Lemma decide_rw {A P Q} {H : Decision P} (HPQ : P <-> Q) (x y : A) :
  (if decide P then x else y) =
  if (@decide Q (dec_of_iff H HPQ)) then x else y.
Proof.
  unfold dec_of_iff.
  unfold decide.
  by destruct H.
Qed.



(* FIXME: Move *)
Class Comm_Monoid A `{Monoid A} :=
  Gplus_comm' : ∀ x y : A, Gplus x y = Gplus y x.

#[export] 
Instance comm_group_is_comm_monoid `{Comm_Group A} : 
  Comm_Monoid A | 5 := Gplus_comm.

#[export] 
Instance nat_is_comm_monoid : Comm_Monoid nat := Nat.add_comm.

#[export] 
Instance nat_max_is_comm_monoid : 
  @Comm_Monoid nat nat_max_is_monoid := Nat.max_comm.


Lemma Gplus_assoc_comm `{Comm_Monoid A} (x y z : A) : 
  (x + (y + z))%G = (y + (x + z))%G.
Proof.
  rewrite 2!Gplus_assoc.
  f_equal.
  apply Gplus_comm'.
Qed.

Definition set_sum {A SA} `{Elements A SA} `{Monoid A}
  (s : SA) : A :=
  set_fold Gplus Gzero s.

#[global]
Add Parametric Morphism `{FinSet A SA} `{Comm_Monoid A} 
  (* `{H : TCOr (Comm_Group A) (!LeibnizEquiv SA)} *) : 
  set_sum with signature
  (≡@{SA}) ==> eq as set_sum_comm_group_proper.
Proof.
  intros x y Hxy.
  unfold set_sum.
  apply set_fold_proper;
  [try typeclasses eauto.. | | easy].
  intros; apply Gplus_assoc_comm.
Qed.


#[export]
Instance gplus_is_assoc `{Monoid A} : Assoc (=@{A}) Gplus := Gplus_assoc.

#[export]
Instance gplus_is_comm `{Comm_Monoid A} : Comm (=@{A}) Gplus := Gplus_comm'.


Section set_sum.

Lemma set_sum_empty {A SA} `{FinSet A SA} `{Monoid A} : 
  set_sum (@empty SA _) = Gzero.
Proof. 
  unfold set_sum. 
  apply set_fold_empty.
Qed.

Lemma set_sum_singleton {A SA} `{FinSet A SA} `{Monoid A} (a : A) : 
  set_sum ({[a]} :> SA) = a.
Proof.
  unfold set_sum.
  rewrite set_fold_singleton.
  apply Gplus_0_r.
Qed.

Lemma set_sum_disj_union 
  {A SA} `{FinSet A SA} `{Comm_Monoid A} (s t : SA) : s ## t ->
  set_sum (s ∪ t) = (set_sum s + set_sum t)%G.
Proof.
  intros Hst.
  unfold set_sum.
  rewrite set_fold_disj_union by apply Hst + typeclasses eauto.
  generalize (set_fold Gplus Gzero s) => a.
  replace a with (Gplus a Gzero) at 1 by apply Gplus_0_r.
  apply set_fold_comm_acc.
  intros; apply Gplus_assoc_comm.
Qed.

Definition FinSet_elem_of_dec A SA `{FinSet A SA} : 
  @RelDecision A SA (@elem_of A SA _) :=
  fun x y => 
    dec_of_iff (elem_of_list_dec x (elements y)) 
    (elem_of_elements y x).

(* Lemma set_fold_union_singleton_l *)

Lemma set_sum_difference_subseteq 
  {A SA} `{FinSet A SA} `{Comm_Group A} (s t : SA) : 
  t ⊆ s -> 
  set_sum (s ∖ t) = (set_sum s - set_sum t)%G.
Proof.
  pose proof (FinSet_elem_of_dec A SA).
  revert t.
  pattern (set_sum s), s.
  revert s.
  apply set_fold_ind.
  { intros _ s t Hst.
    hnf.
    by setoid_rewrite Hst. }
  - intros t ->%equiv_empty.
    rewrite difference_empty, set_sum_empty.
    by unfold Gminus; rewrite Gopp_0, Gplus_0_r.
  - intros x s _ Hx IH t Ht.
    destruct (decide (x ∈ t)) as [Hxt | Hxt].
    + rewrite (ltac:(set_solver) : (({[x]} ∪ s) ∖ t ≡ s ∖ (t ∖ {[x]}))).
      rewrite IH by set_solver.
      rewrite (set_sum_disj_union {[x]}) by set_solver.
      replace (set_sum t) with (set_sum ({[x]} ∪ (t ∖ {[x]}))) by
        (eapply set_sum_comm_group_proper; typeclasses eauto + set_solver).
      rewrite (set_sum_disj_union {[x]}) by set_solver.
      symmetry. 
      unfold Gminus.
      rewrite Gopp_plus_distr, Gplus_assoc.
      rewrite Gplus_comm, 2!Gplus_assoc.
      rewrite Gopp_l, Gplus_0_l.
      reflexivity.
    + rewrite (ltac:(set_solver) : (({[x]} ∪ s) ∖ t ≡ {[x]} ∪ s ∖ t)).
      rewrite 2!(set_sum_disj_union {[x]}) by set_solver.
      rewrite IH by set_solver.
      apply Gplus_assoc.
Qed.


Lemma set_sum_union {A SA} `{FinSet A SA} (* `{@RelDecision A SA (@elem_of A SA _)} *)
  `{Comm_Group A} (s t : SA) : 
  set_sum (s ∪ t) = (set_sum s + set_sum t - set_sum (s ∩ t))%G.
Proof.
  pose proof (FinSet_elem_of_dec A SA).
  assert (Hrw : s ∪ t ≡ s ∪ (t ∖ (s ∩ t))).
  { intros x. 
    rewrite 2!elem_of_union, elem_of_difference, elem_of_intersection.
    destruct (decide (x ∈ s)), (decide (x ∈ t)); naive_solver. }
  rewrite Hrw.
  rewrite set_sum_disj_union by set_solver.
  rewrite set_sum_difference_subseteq by set_solver.
  apply Gplus_assoc.
Qed.


Definition set_Nsum {A SA} `{Elements A SA} (f : A -> nat) (s : SA) : nat :=
  set_fold (Nat.add ∘ f) 0 s.

Lemma set_Nsum_alt `{FinSet A SA} (f : A -> nat) `{!Inj (=) (=) f} (s : SA) : 
  set_Nsum f s = set_sum (set_map f s :> natset).
Proof.
  unfold set_Nsum.
  unfold set_sum, set_fold, set_map.
  simpl.
  rewrite elements_list_to_set.
  - induction (elements s); [easy | simpl in *; by rewrite IHl].
  - apply NoDup_fmap; [easy | apply NoDup_elements].
Qed.


Lemma set_fold_eq_on {A SA B} `{FinSet A SA} (f f' : A -> B -> B) (s : SA) 
  (b : B) (R : relation B) `{!Equivalence R} :
  (∀ a a' b, R (f a (f a' b)) (f a' (f a b))) ->
  (∀ a a' b, R (f' a (f' a' b)) (f' a' (f' a b))) ->
  (∀ a, Proper (R ==> R) (f' a)) ->
  (∀ a b, a ∈ s -> f a b = f' a b) -> 
  R (set_fold f b s) (set_fold f' b s).
Proof.
  intros Hf Hf' Hf'prop Hff'.
  revert Hff'.
  revert s.
  apply (set_fold_ind
    ((λ (b0 : B) (t : SA),
    (∀ (a : A) (b1 : B), a ∈ t → f a b1 = f' a b1)
      → R b0 (set_fold f' b t)))
      f b).
  - intros folded s s' Hs Himpl Hff'.
    erewrite <- set_fold_proper;
    [| typeclasses eauto..| apply Hf' |apply Hs].
    apply Himpl.
    intros; apply Hff'. 
    by rewrite <- Hs.
  - intros Hff'.
    rewrite set_fold_empty.
    reflexivity.
  - intros a s r Ha IH Hff'.
    specialize (IH ltac:(intros; apply Hff'; set_solver)).
    erewrite set_fold_proper;
    [| typeclasses eauto..| apply Hf' |apply union_comm].
    rewrite set_fold_disj_union_strong by 
      first [intros ? ? ? **; apply Hf'; set_solver | 
        typeclasses eauto | set_solver].
    rewrite set_fold_singleton.
    rewrite Hff' by set_solver.
    apply Hf'prop.
    apply IH.
Qed.

#[global]
Add Parametric Morphism `{FinSet A SA} f : (set_Nsum f) with signature
  (* pointwise_relation A eq ==> *) (≡@{SA}) ==> eq as set_Nsum_proper.
Proof.
  intros (* f f' Hf *) s s' Hs.
  unfold set_Nsum.
  apply set_fold_proper;
  [typeclasses eauto..| intros; simpl; lia | apply Hs].
Qed.

Lemma set_Nsum_ext `{FinSet A SA} (f f' : A -> nat) (s s' : SA) : 
  (forall a, a ∈ s -> f a = f' a) -> s ≡ s' -> 
  set_Nsum f s = set_Nsum f' s'.
Proof.
  intros Hf <-.
  unfold set_Nsum.
  apply set_fold_eq_on.
  - typeclasses eauto.
  - simpl; lia.
  - simpl; lia.
  - typeclasses eauto.
  - simpl.
    intros; now rewrite Hf.
Qed.




Lemma set_Nsum_empty {A SA} `{FinSet A SA} f : 
  set_Nsum f (@empty SA _) = 0.
Proof.
  apply set_fold_empty.
Qed.

Lemma set_Nsum_singleton {A SA} `{FinSet A SA} f (a : A) : 
  set_Nsum f ({[a]} :> SA) = f a.
Proof.
  unfold set_Nsum.
  rewrite set_fold_singleton.
  apply Nat.add_0_r.
Qed.

Lemma set_Nsum_disj_union 
  {A SA} `{FinSet A SA}f (s t : SA) : s ## t ->
  set_Nsum f (s ∪ t) = (set_Nsum f s + set_Nsum f t).
Proof.
  intros Hst.
  unfold set_Nsum.
  rewrite set_fold_disj_union_strong by 
    first [assumption | intros ? ? ? ? **; simpl; lia | typeclasses eauto].
  (* rewrite <- (Nat.add_0_r *)
  rewrite <- set_fold_comm_acc_strong by 
    first [intros ? ? ?; simpl; lia | typeclasses eauto].
  by rewrite Nat.add_0_r.
Qed.

Lemma set_Nsum_mono {A SA} `{FinSet A SA} (f : A -> nat) (s t : SA) : 
  s ⊆ t -> set_Nsum f s <= set_Nsum f t.
Proof.
  pose proof (FinSet_elem_of_dec A SA).
  intros Hst.
  rewrite (union_difference _ _ Hst).
  rewrite set_Nsum_disj_union by set_solver.
  lia.
Qed.

(* Lemma set_Nsum_difference_singleton_mem *)

Lemma set_Nsum_difference_subseteq 
  {A SA} `{FinSet A SA} (f : A -> nat) (s t : SA) : 
  t ⊆@{SA} s -> 
  set_Nsum f (s ∖ t) = set_Nsum f s - set_Nsum f t.
Proof.
  pose proof (FinSet_elem_of_dec A SA).
  revert t.
  pattern s.
  revert s.
  apply set_ind.
  - intros s s' Hs.
    by setoid_rewrite Hs.
  - intros t ->%equiv_empty.
    rewrite difference_empty, set_Nsum_empty.
    reflexivity.
  - intros x s Hx IH t Ht.
    destruct (decide (x ∈ t)) as [Hxt | Hxt].
    + rewrite (ltac:(set_solver) : (({[x]} ∪ s) ∖ t ≡ s ∖ (t ∖ {[x]}))).
      generalize (set_Nsum_mono f _ _ Ht).
      (* intros Hsumt. *)
      replace (set_Nsum f t) with (set_Nsum f ({[x]} ∪ (t ∖ {[x]}))) by
        (eapply set_Nsum_proper; typeclasses eauto + set_solver).
      rewrite 2!(set_Nsum_disj_union f {[x]}), set_Nsum_singleton by set_solver.
      simpl.
      intros Hle.
      rewrite IH by set_solver.
      lia.
    + rewrite (ltac:(set_solver) : (({[x]} ∪ s) ∖ t ≡ {[x]} ∪ s ∖ t)).
      rewrite 2!(set_Nsum_disj_union f {[x]}) by set_solver.
      rewrite IH by set_solver.
      rewrite set_Nsum_singleton.
      pose proof (set_Nsum_mono f t s ltac:(set_solver)).
      lia.
Qed.


Lemma set_Nsum_union {A SA} `{FinSet A SA} (f : A -> nat) (s t : SA) : 
  set_Nsum f (s ∪ t) = set_Nsum f s + set_Nsum f t - set_Nsum f (s ∩ t).
Proof.
  pose proof (FinSet_elem_of_dec A SA).
  assert (Hrw : s ∪ t ≡ s ∪ (t ∖ (s ∩ t))).
  { intros x. 
    rewrite 2!elem_of_union, elem_of_difference, elem_of_intersection.
    destruct (decide (x ∈ s)), (decide (x ∈ t)); naive_solver. }
  rewrite Hrw.
  rewrite set_Nsum_disj_union by set_solver.
  rewrite set_Nsum_difference_subseteq by set_solver.
  pose proof (set_Nsum_mono f (s ∩ t) t ltac:(set_solver)).
  lia.
Qed.

Lemma set_Nsum_sum `{FinSet A SA} (f g : A -> nat) (s : SA) :
  set_Nsum f s + set_Nsum g s = set_Nsum (λ a, f a + g a) s.
Proof.
  revert s.
  apply set_ind.
  - by intros s s' ->.
  - by rewrite 3!set_Nsum_empty.
  - intros a s Ha IH.
    rewrite 3!set_Nsum_disj_union, 3!set_Nsum_singleton by set_solver.
    lia.
Qed.

End set_sum.


Lemma multiplicity_singleton_eq `{Countable A} (a b : A) : 
  multiplicity a {[+ b +]} = if decide (a = b) then 1 else 0.
Proof.
  case_decide.
  - subst.
    apply multiplicity_singleton.
  - apply not_elem_of_gmultiset.
    by rewrite gmultiset_elem_of_singleton.
Qed.

Lemma multiplicity_gmultiset_map_to_sum `{Countable A} `{Countable B} 
  (f : A -> B) (s : gmultiset A) (b : B) :
  multiplicity b (gmultiset_map f s) =
  set_Nsum (fun a => if decide (f a = b) then multiplicity a s else 0) (dom s).
Proof.
  induction s using gmultiset_ind; [reflexivity|].
  rewrite gmultiset_map_disj_union, multiplicity_disj_union, 
    dom_gmultiset_disj_union.
  simpl.
  rewrite dom_singleton_L.
  rewrite gmultiset_map_singleton, multiplicity_singleton_eq.
  rewrite (decide_ext _ _ _ _ (eq_comm _ _)).
  rewrite IHs.
  destruct (decide (x ∈ dom s)) as [Hx | Hx].
  - rewrite (ltac:(set_solver) : {[x]} ∪ dom s = dom s).
    rewrite (union_difference {[x]} (dom s)) by set_solver.
    rewrite 2!(set_Nsum_disj_union _ {[x]}) by set_solver.
    rewrite 2!set_Nsum_singleton.
    rewrite Nat.add_assoc.
    f_equal.
    + rewrite multiplicity_disj_union, multiplicity_singleton.
      by case_decide.
    + apply set_Nsum_ext; [|easy].
      intros a Ha.
      case_decide; [|easy].
      rewrite multiplicity_disj_union, multiplicity_singleton_eq.
      case_decide; [|easy].
      subst.
      set_solver.
  - rewrite set_Nsum_disj_union, set_Nsum_singleton by set_solver.
    f_equal.
    + case_decide; [|easy].
      rewrite multiplicity_disj_union, multiplicity_singleton.
      rewrite gmultiset_elem_of_dom, not_elem_of_gmultiset in Hx.
      by rewrite Hx.
    + apply set_Nsum_ext; [|easy].
      intros a Ha.
      case_decide; [|easy].
      rewrite multiplicity_disj_union, multiplicity_singleton_eq.
      case_decide; [congruence | easy].
Qed.



(* Lemma mg_WF_multiplicity_mdegrees *)

(* FIXME: Move *)
Lemma multiplicity_to_if_decide `{Countable A} (g : gmultiset A) a : 
  multiplicity a g = if decide (a ∈ g) then multiplicity a g else 0.
Proof.
  apply multiplicity_eq; case_decide; easy.
Qed.

Lemma multiplicity_to_if_decide_dom `{Countable A} (g : gmultiset A) a : 
  multiplicity a g = if decide (a ∈ dom g) then multiplicity a g else 0.
Proof.
  rewrite multiplicity_to_if_decide at 1.
  apply decide_ext.
  by rewrite gmultiset_elem_of_dom.
Qed.


(* FIXME: Move *)
Lemma if_decide_eq P `{Decision P} {A} (x y x' y' : A) : 
  (P -> x = x') -> (¬ P -> y = y') ->
  (if decide P then x else y) = (if decide P then x' else y').
Proof.
  case_decide; auto.
Qed.

Lemma if_and P Q `{Decision P, Decision Q} {A} (x y : A) : 
  (if decide P then if decide Q then x else y else y) =
  if decide (P ∧ Q) then x else y.
Proof.
  repeat case_decide; reflexivity + intuition auto.
Qed.

Lemma if_or P Q `{Decision P, Decision Q} {A} (x y : A) : 
  (if decide P then x else if decide Q then x else y) =
  if decide (P ∨ Q) then x else y.
Proof.
  repeat case_decide; reflexivity + intuition auto.
Qed.

Lemma if_not P `{Decision P} {A} (x y : A) : 
  (if decide (¬ P) then x else y) =
  if decide P then y else x.
Proof.
  repeat case_decide; reflexivity + intuition auto.
Qed.

Lemma if_same P `{Decision P} {A} (x : A) : 
  (if decide P then x else x) = x.
Proof. by case_decide. Qed.

Lemma if_True P `{Decision P} {A} (x y : A) : 
  P -> (if decide P then x else y) = x.
Proof. by case_decide. Qed.

Lemma if_False P `{Decision P} {A} (x y : A) : 
  ¬ P -> (if decide P then x else y) = y.
Proof. by case_decide. Qed.


(* FIXME: Move*)

Lemma set_Nsum_const_on `{FinSet A SA} (f : A -> nat) (s : SA) n :
  (∀ a, a ∈ s -> f a = n) ->
  set_Nsum f s = n * size s.
Proof.
  pattern s.
  revert s.
  eapply set_ind.
  - intros s s' Hs.
    rewrite Hs.
    intros Himp Hs'; apply Himp.
    intros; apply Hs'; set_solver.
  - intros; rewrite set_Nsum_empty, size_empty; lia.
  - intros a s Ha IH Hf.
    rewrite set_Nsum_disj_union, set_Nsum_singleton by set_solver.
    rewrite size_union, size_singleton by set_solver.
    by rewrite Hf, IH by set_solver; lia.
Qed.

Lemma set_Nsum_0_on `{FinSet A SA} (f : A -> nat) (s : SA) :
  (∀ a, a ∈ s -> f a = 0) ->
  set_Nsum f s = 0.
Proof.
  intros Hf.
  by rewrite (set_Nsum_const_on _ _ 0).
Qed.


Lemma set_Nsum_0 `{FinSet A SA} (f : A -> nat) (s : SA) :
  (∀ a, f a = 0) ->
  set_Nsum f s = 0.
Proof.
  intros Hf.
  by rewrite set_Nsum_0_on.
Qed.


Lemma set_Nsum_restrict `{FinSet A SA} (f : A -> nat) (t s : SA) :
  t ⊆ s -> (∀ a, a ∈ s ∖ t -> f a = 0) ->
  set_Nsum f s = set_Nsum f t.
Proof.
  pose proof (FinSet_elem_of_dec A SA).
  intros Ht Hf.
  erewrite (union_difference t s) by set_solver. 
  rewrite set_Nsum_disj_union by set_solver.
  rewrite Nat.add_comm.
  rewrite set_Nsum_0_on by easy.
  reflexivity.
Qed.

(* FIXME: Move *)
Lemma minverses_natmap_inj_l (f g : natmap nat) : minverses f g -> 
  natmap_inj f.
Proof.
  intros Hfg x y ((fx & Hfx) & (fy & Hfy) & Hfxfy).
  apply Hfg in Hfx as Hfx'.
  apply Hfg in Hfy as Hfy'.
  congruence.
Qed.

Lemma minverses_natmap_inj_r (f g : natmap nat) : minverses f g -> 
  natmap_inj g.
Proof.
  intros Hfg x y ((fx & Hfx) & (fy & Hfy) & Hfxfy).
  apply Hfg in Hfx as Hfx'.
  apply Hfg in Hfy as Hfy'.
  congruence.
Qed.


(* FIXME: Move *)
Lemma set_map_disjoint `{FinSet A SA} `{FinSet B SB} 
  (f : A -> B) (s t : SA) : 
  (∀ a b, a ∈ s ∪ t -> b ∈ s ∪ t -> f a = f b -> a = b) ->
  s ## t -> set_map f s ##@{SB} set_map f t.
Proof.
  intros Hf Hst.
  intros x.
  rewrite 2!elem_of_map.
  intros (a & Haeq & Ha) (b & Hbeq & Hb).
  apply Hst with a; [easy|].
  enough (a = b) by by subst.
  apply Hf; [set_solver..|congruence].
Qed.

Lemma set_Nsum_set_map `{FinSet A SA} `{FinSet B SB} 
  (f : A -> B) (g : B -> nat) (s : SA) : 
  (∀ a b, a ∈ s -> b ∈ s -> f a = f b -> a = b) ->
  set_Nsum g (set_map f s :> SB) = set_Nsum (g ∘ f) s.
Proof.
  pattern s;
  revert s; apply set_ind.
  - intros s s' Hs Himp Hf.
    rewrite <- Hs.
    apply Himp.
    intros ? ? ? ?; apply Hf; by apply Hs.
  - by rewrite set_map_empty, 2!set_Nsum_empty.
  - intros a s Ha IH Hf.
    rewrite set_map_union.
    rewrite 2!set_Nsum_disj_union;
      [|set_solver|apply set_map_disjoint; [apply Hf|set_solver]]. 
    rewrite set_map_singleton, set_Nsum_singleton, IH by set_solver.
    rewrite set_Nsum_singleton.
    reflexivity.
Qed.

Lemma map_to_set_to_map_dom {A} `{FinMapDom K M SK} 
  `{!Elements K SK} `{!FinSet K SK} `{FinSet B SB}
  `{Inhabited A} (f : K -> A -> B) (m : M A) :
  map_to_set f m ≡@{SB} set_map (fun k => f k (m !!! k)) (dom m :> SK).
Proof.
  intros b.
  rewrite elem_of_map, elem_of_map_to_set.
  apply exists_iff => k.
  rewrite elem_of_dom.
  split.
  - intros (a & Hmk & Hfka).
    by rewrite (lookup_total_correct _ _ _ Hmk), Hmk.
  - intros (Hb & (a & Hmk)).
    rewrite (lookup_total_correct _ _ _ Hmk) in Hb.
    by exists a.
Qed.


Lemma lookup_Some_iff_total_dom {A} `{FinMapDom K M SK} `{Inhabited A}
  (m : M A) (k : K) (a : A) :
  m !! k = Some a <-> m !!! k = a ∧ k ∈ dom m.
Proof.
  split.
  - intros Hm.
    split; [by apply lookup_total_correct|].
    by apply elem_of_dom_2 in Hm.
  - intros [Hm Hk].
    rewrite lookup_lookup_total_dom; congruence.
Qed.




(* FIXME: Move *)
Lemma minverses_lookup_total_linv 
  `{Inhabited A, Inhabited B} `{FinMapDom A M SA} `{FinMap B M'} 
  (f : M B) (g : M' A) : minverses f g -> ∀ x, 
  x ∈ dom f -> g !!! (f !!! x) = x.
Proof.
  intros Hfg x Hx.
  apply lookup_total_correct.
  apply Hfg.
  by apply lookup_lookup_total_dom.
Qed.

Lemma minverses_lookup_total_rinv 
  `{Inhabited A, Inhabited B} `{FinMap A M} `{FinMapDom B M' SB} 
  (f : M B) (g : M' A) : minverses f g -> ∀ x, 
  x ∈ dom g -> f !!! (g !!! x) = x.
Proof.
  intros Hfg x Hx.
  apply lookup_total_correct.
  apply Hfg.
  by apply lookup_lookup_total_dom.
Qed.



Lemma set_cast_seq_set `{FinSet nat SA} `{FinSet nat SA'} s l :
  set_cast (seq_set s l :> SA) ≡@{SA'} seq_set s l.
Proof.
  set_solver.
Qed.


Lemma singleton_subseteq_iff `{SemiSet A SA} (a : A) (s : SA) :
  {[a]} ⊆ s <-> a ∈ s.
Proof. set_solver. Qed.


Lemma lookup_total_elem_of_of_dom `{FinMapDom K M SK} `{Inhabited A} 
  `{FinSet A SA} (f : M A) (k : K) (s : SA) : 
  map_img f ⊆ s -> k ∈ dom f -> f !!! k ∈ s.
Proof.
  intros Hf Hk.
  apply Hf.
  apply elem_of_map_img_2 with k.
  by apply lookup_lookup_total_dom.
Qed.

Lemma nat_add_pos n m : 0 < n + m <-> 0 < n ∨ 0 < m.
Proof. lia. Qed.

Lemma set_Nsum_pos `{FinSet A SA} (f : A -> nat) (s : SA) : 
  0 < set_Nsum f s <-> ∃ a, a ∈ s /\ 0 < f a.
Proof.
  revert s.
  apply set_ind.
  - intros s s' Hs Himpl.
    rewrite <- Hs. 
    rewrite Himpl.
    apply exists_iff => x.
    by rewrite Hs.
  - rewrite set_Nsum_empty.
    setoid_rewrite elem_of_empty.
    split; [easy|].
    naive_solver.
  - intros a s Ha IH. 
    rewrite set_Nsum_disj_union, set_Nsum_singleton, 
      nat_add_pos by set_solver.
    rewrite IH.
    split.
    + intros [Hfa | (a' & Ha' & Hfa)].
      * exists a; set_solver.
      * exists a'; set_solver.
    + intros (a' & [<-%elem_of_singleton | Ha']%elem_of_union & Hf).
      * by left.
      * right.
        by exists a'.
Qed.

(* FIXME: Move *)
Lemma gmultiset_map_id `{Countable A} (s : gmultiset A) : 
  gmultiset_map (λ x, x) s = s.
Proof.
  apply gmultiset_eq => a.
  change a with ((λ x, x) a) at 1.
  rewrite multiplicity_gmultiset_map by easy.
  reflexivity.
Qed.

Lemma gmultiset_map_ext `{Countable A, Countable B} 
  (f f' : A -> B) (s : gmultiset A) 
  (Hff' : forall a, a ∈ s -> f a = f' a) :
  gmultiset_map f s = gmultiset_map f' s.
Proof.
  apply gmultiset_eq => b.
  rewrite 2!multiplicity_gmultiset_map_to_sum.
  apply set_Nsum_ext; [|easy].
  intros a Ha%gmultiset_elem_of_dom.
  apply decide_ext.
  by rewrite Hff'.
Qed.

Lemma gmultiset_map_id_on `{Countable A} (s : gmultiset A) f :
  (forall a, a ∈ s -> f a = a) ->
  gmultiset_map f s = s.
Proof.
  intros Hf.
  rewrite (gmultiset_map_ext f (λ x, x) s Hf).
  apply gmultiset_map_id.
Qed.

Lemma multiplicity_gmultiset_map' `{Countable A} `{Countable B} 
  (f : A -> B) (s : gmultiset A) x : 
  (∀ a b, a ∈ {[x]} ∪ dom s -> b ∈ {[x]} ∪ dom s -> f a = f b -> a = b) -> 
  multiplicity (f x) (gmultiset_map f s) = multiplicity x s.
Proof.
  intros Hf.
  symmetry.
  apply multiplicity_eq.
  - intros Hx%gmultiset_elem_of_dom.
    symmetry.
    rewrite multiplicity_gmultiset_map_to_sum.
    rewrite (set_Nsum_restrict _ {[x]}).
    + rewrite set_Nsum_singleton.
      by apply if_True.
    + set_solver.
    + intros a (Ha & Hax%not_elem_of_singleton)%elem_of_difference.
      apply if_False.
      intros Hfeq%Hf; multiset_solver.
  - intros Hx.
    symmetry.
    apply not_elem_of_gmultiset.
    rewrite <- gmultiset_elem_of_dom.
    rewrite dom_gmultiset_map.
    rewrite elem_of_map.
    intros (y & Hy & Hys).
    apply Hx.
    enough (x = y) by (by subst; apply gmultiset_elem_of_dom).
    apply Hf; multiset_solver.
Qed.


Lemma big_sum_of_1_r (f : nat -> nat) 
  n m (Hf : perm_eq m (f ∘ rshift n) (λ _, 1)) : 
  big_sum f (n + m) = big_sum f n + m.
Proof.
  rewrite big_sum_sum.
  f_equal.
  erewrite big_sum_eq_bounded. 2:{
    intros x Hx.
    rewrite Nat.add_comm.
    apply Hf, Hx.
  }
  apply Nsum_1.
Qed.

Lemma set_Nsum_seq_set_big_sum `{FinSet nat SA} (f : nat -> nat) (m l : nat) :
  set_Nsum f (seq_set m l :> SA) = big_sum (f ∘ rshift m) l.
Proof.
  induction l.
  - apply set_Nsum_empty. 
  - simpl. 
    replace (S l) with (l + 1) by lia. 
    rewrite seq_set_split, set_Nsum_disj_union by 
      (intros ?; rewrite 2!elem_of_seq_set; lia).
    rewrite IHl.
    f_equal.
    unfold seq_set.
    simpl.
    rewrite (union_empty_r {[m + l]}).
    rewrite set_Nsum_singleton.
    by rewrite Nat.add_comm.
Qed.

Lemma set_Nsum_seq_set_0_big_sum `{FinSet nat SA} (f : nat -> nat) (l : nat) :
  set_Nsum f (seq_set 0 l :> SA) = big_sum f l.
Proof.
  rewrite set_Nsum_seq_set_big_sum.
  apply big_sum_eq_bounded.
  simpl.
  unfold rshift.
  intros; by rewrite Nat.add_0_r.
Qed.

Lemma gmultiset_dom_ind `{Countable A} (P : gmultiset A -> Prop) : 
  P ∅ -> (∀ (x : A) (n : nat) g, 0 < n -> x ∉ dom g -> P g -> P ((n *: {[+x+]}) ⊎ g)) -> 
  ∀ g, P g.
Proof.
  intros HPemp HPind.
  intros (g).
  induction g as [|x n g Hgi Hfirst IHg] using map_first_key_ind.
  - apply HPemp.
  - replace {| gmultiset_car := <[x:=n]> g |} with
      (Pos.to_nat n *: {[+ x +]} ⊎ GMultiSet g).
      { apply HPind, IHg.
        - lia.
        - simpl.
          apply not_elem_of_dom.
          apply Hgi. }
    apply gmultiset_eq => a.
    rewrite multiplicity_disj_union, multiplicity_scalar_mul.
    rewrite multiplicity_singleton_eq.
    unfold multiplicity.
    simpl.
    case_decide as Hax.
    + subst a.
      rewrite Hgi, lookup_insert.
      lia.
    + rewrite lookup_insert_ne by done.
      lia.
Qed.

(* FIXME: MOve *)
Lemma dom_gmultiset_scalar_mul_pos `{Countable A} 
  (s : gmultiset A) n : 0 < n -> 
  dom (n *: s) = dom s.
Proof.
  intros Hn.
  apply set_eq => a.
  rewrite 2!gmultiset_elem_of_dom, 2!elem_of_multiplicity.
  rewrite multiplicity_scalar_mul.
  lia.
Qed.

Lemma dom_gmultiset_singleton `{Countable A} (a : A) : 
  dom ({[+ a +]} :> gmultiset A) = {[ a ]}.
Proof.
  apply set_eq => x.
  rewrite gmultiset_elem_of_dom, elem_of_multiplicity.
  rewrite multiplicity_singleton_eq, elem_of_singleton.
  case_decide; split; easy + lia.
Qed.

Lemma sum_multiplicities_size `{Countable A}
  (s : gmultiset A) : 
  set_Nsum (λ x, multiplicity x s) (dom s) = size s.
Proof.
  induction s as [|x n s Hn Hx IHs] using gmultiset_dom_ind; first by reflexivity.
  rewrite dom_gmultiset_disj_union.
  rewrite dom_gmultiset_scalar_mul_pos, dom_gmultiset_singleton by easy.
  rewrite set_Nsum_disj_union by set_solver.
  rewrite gmultiset_size_disj_union, gmultiset_size_scalar_mul.
  f_equal.
  - rewrite gmultiset_size_singleton.
    rewrite set_Nsum_singleton, multiplicity_disj_union.
    rewrite multiplicity_scalar_mul, multiplicity_singleton.
    rewrite gmultiset_elem_of_dom, not_elem_of_gmultiset in Hx.
    rewrite Hx.
    apply Nat.add_0_r.
  - rewrite <- IHs.
    apply set_Nsum_ext; [|reflexivity].
    intros a Ha.
    rewrite multiplicity_disj_union, multiplicity_scalar_mul, 
      multiplicity_singleton_eq.
    rewrite if_False by congruence.
    lia. 
Qed.

Lemma set_cast_union `{FinSet A SA, SemiSet A SA'} 
  (s t : SA) : 
  set_cast (s ∪ t) ≡@{SA'} set_cast s ∪ set_cast t.
Proof. set_unfold. set_solver. Qed.

Lemma set_cast_difference `{FinSet A SA, Set_ A SA'} 
  (s t : SA) : 
  set_cast (s ∖ t) ≡@{SA'} set_cast s ∖ set_cast t.
Proof. set_solver. Qed.

Lemma set_cast_singleton `{FinSet A SA, SemiSet A SA'} 
  (a : A) : 
  set_cast ({[a]} :> SA) ≡@{SA'} {[a]}.
Proof. set_solver. Qed.

Lemma set_cast_empty `{FinSet A SA, SemiSet A SA'} : 
  set_cast (∅ :> SA) ≡@{SA'} ∅.
Proof. set_solver. Qed.

Lemma set_cast_set_cast `{FinSet A SA, FinSet A SA', SemiSet A SA''} (s : SA) : 
  set_cast (set_cast s :> SA') ≡@{SA''} set_cast s.
Proof. set_solver. Qed.

Lemma set_cast_id `{FinSet A SA} (s : SA) :
  set_cast s ≡@{SA} s.
Proof. set_solver. Qed.

#[global]
Add Parametric Morphism `{FinSet A SA, SemiSet A SA'} : set_cast
  with signature (≡@{SA}) ==> (≡@{SA'}) as set_cast_proper.
Proof. intros x y Hxy a. by rewrite 2!elem_of_set_cast. Qed. 


(* FIXME: Move *)
Lemma set_Nsum_set_cast `{FinSet A SA, FinSet A SA'} 
  (f : A -> nat) (s : SA) : 
  set_Nsum f (set_cast s :> SA') = set_Nsum f s.
Proof.
  revert s.
  apply set_ind.
  - by intros x x' ->.
  - by rewrite set_cast_empty, 2!set_Nsum_empty.
  - intros a s Ha IH.
    rewrite set_cast_union, set_cast_singleton.
    rewrite 2!set_Nsum_disj_union, 2!set_Nsum_singleton by set_solver.
    congruence.
Qed.

Lemma sum_multiplicities_size_subseteq `{Countable A} `{FinSet A SA}
  (s : gmultiset A) (d : SA) : dom s ⊆ set_cast d ->
  set_Nsum (λ x, multiplicity x s) d = size s.
Proof.
  intros Hd.
  rewrite (set_Nsum_restrict _ (set_cast (dom s))).
  - by rewrite set_Nsum_set_cast, sum_multiplicities_size.
  - set_solver.
  - intros a (_ & Ha)%elem_of_difference.
    apply not_elem_of_gmultiset.
    by rewrite elem_of_set_cast, gmultiset_elem_of_dom in Ha.
Qed.

Lemma size_gmultiset_map `{Countable A, Countable B} (f : A -> B) s : 
  size (gmultiset_map f s) = size s.
Proof.
  induction s using gmultiset_ind; first by reflexivity.
  rewrite gmultiset_map_disj_union, gmultiset_map_singleton.
  rewrite 2!gmultiset_size_disj_union, 2!gmultiset_size_singleton.
  congruence.
Qed.


Lemma minverses_restrict `{FinMapDom A MA SA} `{FinMapDom B MB SB}
  `{!Elements A SA} `{!FinSet A SA}
  (f : MA B) (g : MB A) : 
  minverses f g <-> 
  map_img f ≡ dom g ∧
  Forall (fun a : A => f !! a ≫= (g !!.) = Some a) (elements (dom f)).
Proof.
  split.
  - intros Hfg.
    split; [by apply minverses_map_img_eq_dom|].
    rewrite Forall_forall.
    intros a.
    rewrite elem_of_elements, elem_of_dom.
    intros (fa & Hfa).
    rewrite Hfa.
    simpl.
    by apply Hfg.
  - intros (Himg & Hfg).
    rewrite Forall_forall in Hfg.
    setoid_rewrite elem_of_elements in Hfg.
    intros a b.
    split.
    + intros Hfa.
      rewrite <- Hfg by (by apply elem_of_dom_2 in Hfa).
      rewrite Hfa.
      reflexivity.
    + intros Hgb.
      apply elem_of_dom_2 in Hgb as Hdom.
      rewrite <- Himg in Hdom.
      apply elem_of_map_img in Hdom as Hdom'. 
      destruct Hdom' as (a' & Hfa').
      rewrite <- Hfa'.
      f_equal.
      enough (Some a = Some a') by congruence.
      symmetry.
      rewrite <- Hfg; first by rewrite Hfa'.
      by apply elem_of_dom_2 in Hfa'.
Qed.











(* FIXME: Move *)
#[export] Instance R_inhabited : Inhabited R := populate R0.

Record ZX_map_graph := {
  mg_verts : natmap (bool * R);
  mg_inputs : natmap (nat + nat); (* verts + outputs *)
  mg_vert_outputs : natmap nat; (* only verts!! *)
  mg_vert_edges : gmultiset (nat * nat);

  (* Extra definitions, convenient to make them accessible by dot *)
  mg_vert_inputs : natmap nat (* only verts! *) 
    := omap sum_to_l mg_inputs;
  mg_boundary_inputs : natmap nat 
    := omap sum_to_r mg_inputs;
  
  mg_boundary_outputs : natmap nat 
    := natmap_inv mg_boundary_inputs;
  mg_outputs : natmap (nat + nat)
    := (inl <$> mg_vert_outputs) ∪ (inr <$> mg_boundary_outputs);

  mg_numspi : nat := size mg_verts;
  mg_insize : nat := size mg_inputs;
  mg_outsize : nat := size mg_outputs;

  mg_vert_set : natset := dom mg_verts;
  mg_input_set : natset := dom mg_inputs;
  mg_output_set : natset := dom mg_outputs;

  mg_vert_idx : natmap nat :=
    natset_idx mg_vert_set;
  mg_vert_nth : natmap nat :=
    natset_nth mg_vert_set;
  
  mg_input_idx : natmap nat :=
    natset_idx mg_input_set;
  mg_input_nth : natmap nat :=
    natset_nth mg_input_set;
  
  mg_output_idx : natmap nat :=
    natset_idx mg_output_set;
  mg_output_nth : natmap nat :=
    natset_nth mg_output_set;
    
  mg_indices : gmap.gset (nat + nat + nat) :=
    sum_set (sum_set mg_vert_set mg_input_set :> gmap.gset (nat + nat)) mg_output_set;
    (* set_map (inl ∘ inl) mg_vert_set ∪
    set_map (inl ∘ inr) mg_input_set ∪
    set_map inr mg_output_set *)

  mg_to_idx : gmap.gmap (nat + nat + nat) nat :=
    set_to_map 
      (fun a =>
        ( a ,
        sum_elim (sum_elim (mg_vert_idx !!!.)
          (Nat.add mg_numspi ∘ (mg_input_idx !!!.))) 
          (Nat.add (mg_numspi + mg_insize) ∘ (mg_output_idx !!!.)) a)
      )
      mg_indices;
  
  mg_from_idx : gmap.gmap nat (nat + nat + nat) :=
    set_to_map 
      (fun a => (a,  
      if decide (a < mg_numspi) then
        inl (inl (mg_vert_nth !!! a)) else
      if decide (a < mg_numspi + mg_insize) then
        inl (inr (mg_input_nth !!! (a - mg_numspi))) else
        inr (mg_output_nth !!! (a - (mg_numspi + mg_insize)))
      ))
      (seq_set 0 (mg_numspi + mg_insize + mg_outsize) :> natset);

  mg_input_edges : gmap.gset (nat * nat) :=
    map_to_set (λ i v, (mg_numspi + mg_input_idx !!! i, 
      mg_vert_idx !!! v)) mg_vert_inputs;

  mg_output_edges : gmap.gset (nat * nat) :=
    map_to_set (λ i v, (mg_numspi + mg_insize + mg_output_idx !!! i, 
      mg_vert_idx !!! v)) mg_vert_outputs;

  mg_io_edges : gmap.gset (nat * nat) :=
    map_to_set (λ i o, (mg_numspi + mg_input_idx !!! i, 
      mg_numspi + mg_insize + mg_output_idx !!! o))
      mg_boundary_inputs;

  mg_input_medges : gmap.gset ((nat + nat + nat) * (nat + nat + nat)) :=
    map_to_set (λ i v, (inl (inr i), inl (inl v))) mg_vert_inputs;
  
  mg_output_medges : gmap.gset ((nat + nat + nat) * (nat + nat + nat)) :=
    map_to_set (λ o v, (inr o, inl (inl v))) mg_vert_outputs;
  
  mg_io_medges : gmap.gset ((nat + nat + nat) * (nat + nat + nat)) :=
    map_to_set (λ i o, (inl (inr i), inr o)) mg_boundary_inputs;
  
  mg_vert_medges : gmultiset ((nat + nat + nat) * (nat + nat + nat)) :=
    gmultiset_map (prod_map (inl ∘ inl) (inl ∘ inl)) mg_vert_edges;

  mg_medges : gmultiset ((nat + nat + nat) * (nat + nat + nat)) :=
    mg_vert_medges ⊎
    gset_to_multiset 
      (mg_input_medges ∪ mg_output_medges ∪ mg_io_medges);

  mg_mdegrees : gmultiset (nat + nat + nat) :=
    gmultiset_map fst mg_medges ⊎ gmultiset_map snd mg_medges;

  mg_edges : gmultiset (nat * nat) :=
    gmultiset_map
      (prod_map (mg_to_idx !!!.) (mg_to_idx !!!.))
      mg_medges;
    (* gmultiset_map (mg_vert_idx !!!.) mg_vert_edges 
    ∪ gset_to_multiset (mg_input_edges
      ∪ mg_output_edges
      ∪ mg_io_edges); *)
  
  mg_degrees : gmultiset nat :=
    gmultiset_map fst mg_edges ⊎ gmultiset_map snd mg_edges;

  (* TODO: multiplicity mg_degrees i = multiplicity mg_degrees o = 1
    for i, o inputs and outputs. *)
  
  mg_numedges : nat := size mg_edges;
  
  mg_edge_func : nat -> nat * nat := 
    (elements mg_edges !!!.);

  mg_io_diag : ZX (mg_numedges * 2) 0 :=
    ZX_of_edgefunc (mg_numedges) mg_edge_func;

  mg_spider_stack : ZX (mg_insize + mg_outsize) _ :=
    ZX_of_stack_uncast mg_insize mg_outsize mg_numspi 
      (λ x, multiplicity x mg_degrees)
      (snd ∘ (mg_verts !!!.))
      (fst ∘ (mg_verts !!!.))
}.


(* FIXME: Move *)
Set Printing Projections.


(* TODO: Typeclass / record? *)
Class WF_ZX_map_graph (G : ZX_map_graph) := {
  mg_WF_vert_inputs : map_img G.(mg_vert_inputs) ⊆ G.(mg_vert_set);
  mg_WF_vert_outputs : map_img G.(mg_vert_outputs) ⊆ G.(mg_vert_set);
  mg_WF_vert_edges : 
    edgeset_dom $ dom G.(mg_vert_edges) 
      ⊆ G.(mg_vert_set);
  mg_WF_boundary_inputs_img : 
    map_img G.(mg_boundary_inputs) ## dom G.(mg_vert_outputs);
  mg_WF_boundary_inputs_inj : 
    natmap_inj G.(mg_boundary_inputs);
}.



Lemma mg_WF_io_minverses `{HG: WF_ZX_map_graph G} :
  minverses G.(mg_boundary_inputs) G.(mg_boundary_outputs).
Proof.
  apply natmap_inv_minverses, HG.
Qed.


(* FIXME: RE-Move *) (*
Reserved Notation "f ^~ y" (at level 10, y at level 8, no associativity,
  format "f ^~ y").

Notation "f ^~ y" := (fun x => f x y). *)

Record WF_ZX_map_graph_raw {G : ZX_map_graph} := {
  mg_raw_WF_inputs : 
    map_Forall (fun k v => 
      sum_elim 
        (* to vert: *) (λ v, v ∈ dom G.(mg_verts))
        (* to output: *) (λ v, v ∉ dom G.(mg_vert_outputs))
        v)
      G.(mg_inputs);
  mg_raw_WF_vert_outputs : 
    map_img G.(mg_vert_outputs) ⊆ dom G.(mg_verts);
  mg_raw_WF_vert_edges : 
    set_Forall 
      (fun '(i, j) => i ∈ dom G.(mg_verts) ∧ j ∈ dom G.(mg_verts))
      (dom G.(mg_vert_edges));
  mg_raw_WF_boundary_inputs_inj : 
    natmap_inj G.(mg_boundary_inputs);
}.

Global Arguments WF_ZX_map_graph_raw _ : clear implicits.


Lemma WF_ZX_map_graph_to_prop G : 
  WF_ZX_map_graph G <-> 
  map_img G.(mg_vert_inputs) ⊆ G.(mg_vert_set)
	∧ map_img G.(mg_vert_outputs) ⊆ G.(mg_vert_set)
  ∧ edgeset_dom (dom G.(mg_vert_edges)) ⊆ G.(mg_vert_set)
  ∧ map_img G.(mg_boundary_inputs) ## dom G.(mg_vert_outputs)
  ∧ natmap_inj G.(mg_boundary_inputs).
Proof.
  split; intros []; constructor; naive_solver.
Qed.

Lemma WF_ZX_map_graph_iff_1 G : 
  WF_ZX_map_graph G <-> 
  (map_img G.(mg_vert_inputs) ∪ 
    map_img G.(mg_vert_outputs) ∪ 
    edgeset_dom (dom G.(mg_vert_edges))) ⊆ G.(mg_vert_set)
  ∧ map_img G.(mg_boundary_inputs) ## dom G.(mg_vert_outputs)
  ∧ size (dom G.(mg_boundary_inputs) :> natset) 
    = size (map_img G.(mg_boundary_inputs) :> natset).
Proof.
  rewrite WF_ZX_map_graph_to_prop.
  rewrite 2!union_subseteq, <- !(and_assoc _).
  by rewrite natmap_inj_alt_size.
Qed.

Definition WF_ZX_map_graph_dec G : Decision (WF_ZX_map_graph G) :=
  dec_of_iff' _ (WF_ZX_map_graph_iff_1 G).
(* TODO: Set arguments of dec_of_iff / dec_of_iff' *)


Lemma ZX_map_graph_WF_iff_raw G : 
  WF_ZX_map_graph G <-> WF_ZX_map_graph_raw G.
Proof.
  split.
  - intros HWF.
    constructor.
    + intros k [v | o] Hkv; simpl.
      * apply HWF.
        rewrite elem_of_map_img.
        exists k.
        apply lookup_omap_Some.
        now exists (inl v).
      * refine (mg_WF_boundary_inputs_img o _).
        rewrite elem_of_map_img.
        exists k.
        apply lookup_omap_Some.
        now exists (inr o).
    + by apply HWF.
    + intros (i, j) Hij.
      split; apply mg_WF_vert_edges;
      rewrite elem_of_edgeset_dom;
      exists (i, j); 
      (split; [easy|]);
      auto.
    + by apply HWF.
  - intros HWF.
    constructor.
    + intros v (k & Hk)%elem_of_map_img.
      pose proof (HWF.(mg_raw_WF_inputs) k (inl v)) as Hv.
      apply lookup_omap_Some in Hk as ([v' |] & [=->] & Hgk).
      apply (Hv Hgk).
    + by apply HWF.
    + intros v ((i, j) & Hij & [-> | ->])%elem_of_edgeset_dom;
      now apply (HWF.(mg_raw_WF_vert_edges) (i, j)).
    + intros o (k & Hk)%elem_of_map_img.
      pose proof (HWF.(mg_raw_WF_inputs) k (inr o)) as Ho.
      apply lookup_omap_Some in Hk as ([|o' ] & [=->] & Hgk).
      apply (Ho Hgk).
    + by apply HWF.
Qed.

Section WF_mapgraph.

Context {G : ZX_map_graph}.

Lemma dom_mg_degrees_eq_bind_dom_mg_edges : 
  dom G.(mg_degrees) = 
  edgeset_dom
    (dom G.(mg_edges)).
Proof.
  apply set_eq => k.
  rewrite gmultiset_elem_of_dom.
  unfold mg_degrees.
  rewrite elem_of_edgeset_dom.
  rewrite gmultiset_elem_of_disj_union, 2!elem_of_gmultiset_map.
  setoid_rewrite gmultiset_elem_of_dom.
  split.
  - intros [((i,j) & -> & ?) | ((i,j) & -> & ?)]; 
    (exists (i, j); split; [easy|]; simpl; naive_solver).
  - intros ((i, j) & Hij & 
      [-> | ->]);
    [left | right];
    by exists (i, j).
Qed.





(* Lemma dom_mg_edges_eq : 
  dom G.(mg_edges) = 
  dom G.(mg_vert_edges) ∪
  G.(mg_input_edges) ∪ G.(mg_output_edges) ∪ G.(mg_io_edges).
Proof.
  unfold mg_edges.
  rewrite dom_gmultiset_map.
  apply set_eq => ij.
  rewrite gmultiset_elem_of_dom.
  rewrite gmultiset_elem_of_union.
  rewrite <- 2!(gmultiset_elem_of_dom ij).
  rewrite dom_gset_to_multiset.
  symmetry.
  rewrite <- 2!(union_assoc (dom G.(mg_vert_edges))).
  apply elem_of_union.
Qed. *)



Lemma dom_mg_to_idx : dom G.(mg_to_idx) = 
  G.(mg_indices).
Proof.
  unfold mg_to_idx.
  rewrite dom_set_to_map_L.
  unfold compose.
  simpl.
  apply set_map_id_L.
Qed.


Lemma mg_degrees_eq_map_mdegrees : 
  G.(mg_degrees) = 
  gmultiset_map (G.(mg_to_idx) !!!.) G.(mg_mdegrees).
Proof.
  unfold mg_degrees, mg_mdegrees.
  rewrite gmultiset_map_disj_union.
  rewrite <- 2!gmultiset_map_compose.
  unfold mg_edges.
  rewrite <- 2!gmultiset_map_compose.
  reflexivity.
Qed.



Lemma map_img_mg_to_idx `{FinSet nat A} `{!LeibnizEquiv A} : 
  map_img G.(mg_to_idx) =
  seq_set 0 (G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize)) :> A.
Proof.
  unfold mg_to_idx.
  erewrite map_img_set_to_map_L by easy.
  unfold mg_indices.
  unfold sum_set, set_inl, set_inr.
  erewrite 3!set_map_union_L, !set_map_set_map_L.
  unfold compose.
  simpl.
  erewrite 2!seq_set_split_L.
  f_equal; [f_equal|].
  - rewrite set_map_lookup_total_eq_map_img_L 
      by (symmetry; apply dom_natset_idx).
    unfold mg_vert_idx.
    rewrite map_img_natset_idx.
    unfold mg_vert_set.
    rewrite size_dom.
    reflexivity.
  - change (λ x, _) with 
      ((Nat.add G.(mg_numspi) ∘ (G.(mg_input_idx) !!!.))).
    rewrite <- (set_map_set_map_L (E:=natset)).
    rewrite set_map_lookup_total_eq_map_img_L
      by (symmetry; apply dom_natset_idx).
    unfold mg_input_idx.
    rewrite map_img_natset_idx.
    rewrite set_map_add_seq_set.
    unfold mg_input_set.
    by rewrite size_dom.
  - change (λ x, _) with 
      ((Nat.add (G.(mg_numspi) + G.(mg_insize)) ∘ (G.(mg_output_idx) !!!.))).
    rewrite <- (set_map_set_map_L (E:=natset)).
    rewrite set_map_lookup_total_eq_map_img_L
      by (symmetry; apply dom_natset_idx).
    unfold mg_output_idx.
    rewrite map_img_natset_idx.
    rewrite set_map_add_seq_set.
    unfold mg_output_set.
    by rewrite size_dom.
Qed.

Lemma lookup_mg_to_idx_inr i : 
  G.(mg_to_idx) !! (inr i) = 
  Nat.add (G.(mg_numspi) + G.(mg_insize)) <$> G.(mg_output_idx) !! i.
Proof.
  apply option_eq => v.
  unfold mg_to_idx.
  rewrite lookup_set_to_map by done.
  setoid_rewrite pair_eq.
  setoid_rewrite (and_comm (_ ∈ _)).
  setoid_rewrite <- (and_assoc _).
  rewrite exists_eq_l_iff.
  simpl.
  split.
  - intros [Hlookup Hi].
    rewrite lookup_lookup_total_dom.
    { simpl. by rewrite Hlookup. }
    unfold mg_indices in Hi.
    rewrite elem_of_sum_set_cases in Hi.
    unfold mg_output_idx.
    rewrite dom_natset_idx.
    apply Hi.
  - destruct (G.(mg_output_idx) !! i) as [Gi|] eqn:e; [|easy].
    simpl.
    intros [=<-].
    rewrite (lookup_total_correct _ _ _ e).
    split; [easy|].
    apply elem_of_dom_2 in e as Hi.
    unfold mg_output_idx in Hi.
    rewrite dom_natset_idx in Hi.
    unfold mg_indices.
    by rewrite elem_of_sum_set_cases.
Qed.

Lemma lookup_mg_to_idx_inl_inr i : 
  G.(mg_to_idx) !! (inl (inr i)) = 
  Nat.add G.(mg_numspi) <$> G.(mg_input_idx) !! i.
Proof. 
  apply option_eq => v.
  unfold mg_to_idx.
  rewrite lookup_set_to_map by done.
  setoid_rewrite pair_eq.
  setoid_rewrite (and_comm (_ ∈ _)).
  setoid_rewrite <- (and_assoc _).
  rewrite exists_eq_l_iff.
  simpl.
  split.
  - intros [Hlookup Hi].
    rewrite lookup_lookup_total_dom.
    { simpl. by rewrite Hlookup. }
    unfold mg_indices in Hi.
    rewrite 2!elem_of_sum_set_cases in Hi.
    unfold mg_input_idx.
    rewrite dom_natset_idx.
    apply Hi.
  - destruct (G.(mg_input_idx) !! i) as [Gi|] eqn:e; [|easy].
    simpl.
    intros [=<-].
    rewrite (lookup_total_correct _ _ _ e).
    split; [easy|].
    apply elem_of_dom_2 in e as Hi.
    unfold mg_input_idx in Hi.
    rewrite dom_natset_idx in Hi.
    unfold mg_indices.
    by rewrite 2!elem_of_sum_set_cases.
Qed.


Lemma lookup_mg_to_idx_inl_inl i : 
  G.(mg_to_idx) !! (inl (inl i)) = 
  G.(mg_vert_idx) !! i.
Proof. 
  apply option_eq => v.
  unfold mg_to_idx.
  rewrite lookup_set_to_map by done.
  setoid_rewrite pair_eq.
  setoid_rewrite (and_comm (_ ∈ _)).
  setoid_rewrite <- (and_assoc _).
  rewrite exists_eq_l_iff.
  simpl.
  unfold mg_indices.
  rewrite 2!elem_of_sum_set_cases.
  split.
  - intros [Hlookup Hi].
    rewrite lookup_lookup_total_dom.
    { simpl. by rewrite Hlookup. }
    unfold mg_vert_idx.
    rewrite dom_natset_idx.
    apply Hi.
  - destruct (G.(mg_vert_idx) !! i) as [Gi|] eqn:e; [|easy].
    simpl.
    intros [=<-].
    rewrite (lookup_total_correct _ _ _ e).
    split; [easy|].
    apply elem_of_dom_2 in e as Hi.
    unfold mg_vert_idx in Hi.
    rewrite dom_natset_idx in Hi.
    apply Hi.
Qed.


Lemma lookup_mg_to_idx_cases i : 
  G.(mg_to_idx) !! i = 
  match i with
  | inl (inl i) => G.(mg_vert_idx) !! i
  | inl (inr i) => Nat.add G.(mg_numspi) <$> G.(mg_input_idx) !! i
  | inr i => Nat.add (G.(mg_numspi) + G.(mg_insize)) <$> G.(mg_output_idx) !! i
  end.
Proof.
  destruct i as [[i | i] | i].
  - apply lookup_mg_to_idx_inl_inl.
  - apply lookup_mg_to_idx_inl_inr.
  - apply lookup_mg_to_idx_inr.
Qed.


Lemma mg_vert_outputs_eq_omap : 
  G.(mg_vert_outputs) = omap sum_to_l G.(mg_outputs).
Proof.
  symmetry.
  apply map_eq => i.
  apply option_eq => v.
  unfold mg_outputs.
  rewrite lookup_omap_Some.
  simpl.
  rewrite (exists_iff_of_unique (inl v)) by
    (intros [] []; simpl in *; congruence).
  simpl.
  rewrite lookup_union, 2!lookup_fmap, union_Some, fmap_None.
  rewrite 2!fmap_Some.
  setoid_rewrite (inj_iff inl).
  rewrite exists_eq_r_iff'.
  naive_solver.
Qed.


Lemma mg_boundary_inputs_img_subseteq : 
  map_img G.(mg_boundary_inputs) ⊆ G.(mg_output_set).
Proof.
  unfold mg_output_set, mg_outputs.
  rewrite dom_union, 2!dom_fmap.
  rewrite <- union_subseteq_r.
  unfold mg_boundary_outputs.
  rewrite dom_natmap_inv.
  reflexivity.
Qed.


Lemma mg_boundary_outputs_img_subseteq : 
  map_img G.(mg_boundary_outputs) ⊆ G.(mg_input_set).
Proof.
  unfold mg_boundary_outputs.
  rewrite map_img_natmap_inv_subseteq.
  apply dom_omap_subseteq.
Qed.


Context {HG : WF_ZX_map_graph G}.




Lemma mg_WF_input_medges :
  edgeset_dom G.(mg_input_medges) ⊆
  G.(mg_indices).
Proof.
  intros x.
  intros ((i,v) & 
    (i' & v' & Hi' & (<- & <-)%pair_eq)%elem_of_map_to_set 
    & [-> | ->])%elem_of_edgeset_dom;
  apply elem_of_sum_set_cases; simpl;
  rewrite elem_of_sum_set_cases.
  - apply elem_of_dom_2 in Hi'.
    apply dom_omap_subseteq in Hi'.
    apply Hi'.
  - apply mg_WF_vert_inputs.
    apply (elem_of_map_img_2 (SA:=natset)) in Hi'.
    apply Hi'.
Qed.

Lemma mg_WF_ouput_medges :
  edgeset_dom G.(mg_output_medges) ⊆
  G.(mg_indices).
Proof.
  intros x.
  intros ((i,v) & 
    (i' & v' & Hi' & (<- & <-)%pair_eq)%elem_of_map_to_set 
    & [-> | ->])%elem_of_edgeset_dom;
  apply elem_of_sum_set_cases; simpl;
  rewrite 1?elem_of_sum_set_cases.
  - apply elem_of_dom_2 in Hi'.
    unfold mg_output_set. 
    unfold mg_outputs.
    rewrite dom_union, elem_of_union.
    left.
    rewrite dom_fmap.
    apply Hi'.
  - apply mg_WF_vert_outputs.
    apply (elem_of_map_img_2 (SA:=natset)) in Hi'.
    apply Hi'.
Qed.

Lemma mg_WF_io_medges : 
  edgeset_dom G.(mg_io_medges) ⊆
  G.(mg_indices).
Proof.
  intros x.
  intros ((i,v) & 
    (i' & v' & Hi' & (<- & <-)%pair_eq)%elem_of_map_to_set 
    & [-> | ->])%elem_of_edgeset_dom;
  apply elem_of_sum_set_cases; simpl;
  rewrite 1?elem_of_sum_set_cases.
  - apply elem_of_dom_2 in Hi'.
    apply dom_omap_subseteq in Hi'.
    apply Hi'.
  - unfold mg_output_set. 
    unfold mg_outputs.
    rewrite dom_union, elem_of_union.
    right.
    rewrite dom_fmap.
    unfold mg_boundary_outputs.
    rewrite dom_natmap_inv.
    eapply elem_of_map_img_2, Hi'.
Qed.





Lemma mg_WF_vert_medges : 
  edgeset_dom (dom G.(mg_vert_medges)) ⊆
  G.(mg_indices).
Proof.
  intros x.
  intros ((i,v) & 
    Hiv
    & Heqs)%elem_of_edgeset_dom;
  apply elem_of_sum_set_cases.
  simpl in Heqs.
  unfold mg_vert_medges in Hiv.
  rewrite dom_gmultiset_map in Hiv.
  apply elem_of_map in Hiv as ((i', v') & [-> ->]%pair_eq & Hs).
  destruct Heqs as [-> | ->]; simpl;
  rewrite elem_of_sum_set_cases;
  apply mg_WF_vert_edges, elem_of_edgeset_dom;
  exists (i', v'); naive_solver.
Qed.


Lemma mg_WF_medges : 
  edgeset_dom (dom G.(mg_medges)) ⊆
  G.(mg_indices).
Proof.
  unfold mg_medges.
  rewrite dom_gmultiset_disj_union.
  rewrite edgeset_dom_union_L.
  apply union_subseteq; split.
  { apply mg_WF_vert_medges. }
  rewrite dom_gset_to_multiset.
  rewrite 2!edgeset_dom_union_L.
  apply union_subseteq; split; [apply union_subseteq; split|].
  - apply mg_WF_input_medges.
  - apply mg_WF_ouput_medges.
  - apply mg_WF_io_medges.
Qed.

Lemma mg_WF_edges `{FinSet nat SA} `{!LeibnizEquiv SA}:
  edgeset_dom (dom G.(mg_edges)) ⊆@{SA}
  seq_set 0 (G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize)).
Proof.
  rewrite <- map_img_mg_to_idx.
  unfold mg_edges.
  rewrite dom_gmultiset_map.
  rewrite (edgeset_dom_prod_map_L (SA:=gmap.gset _)).
  erewrite <- set_map_lookup_total_eq_map_img_L by reflexivity.
  apply set_map_mono; [easy|].
  rewrite dom_mg_to_idx.
  apply mg_WF_medges.
Qed.


Lemma dom_mg_degrees_WF : 
  dom (mg_degrees G) ⊆ seq_set 0 (G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize)).
Proof.
  rewrite dom_mg_degrees_eq_bind_dom_mg_edges.
  apply mg_WF_edges.
Qed.

(* Definition gmultiset_bind `{Countable A} `{Countable B} 
  (f : A -> gmultiset B) (d : gmultiset A) : gmultiset B :=
  foldr disj_union ∅ (f <$> elements d).

Lemma multiplicity_gmultiset_bind `{Countable A} `{Countable B} 
  (f : A -> gmultiset B) (d : gmultiset A) b : 
  multiplicity b (gmultiset_bind f d) = 
    foldr (λ a n, n + multiplicity b (f a)) 0 (elements d).
Proof.
  unfold gmultiset_bind.
  induction (elements d) as [|a ds]; [easy|].
  simpl.
  rewrite multiplicity_disj_union.
  rewrite <- IHds.
  apply Nat.add_comm.
Qed. *)



(* Lemma gmultiset_map_gset_to_multiset `{Countable A} `{Countable B}
  (f : A -> B) (d : gmap.gset A) 
  (Hf : forall a b, a ∈ d -> b ∈ d -> f a = f b -> a = b) : 
  gmultiset_map f (gset_to_multiset d) = 
  gset_to_multiset (set_map f d). *)

(* Lemma mg_WF_mdegrees_outputs vio K : 
  multiplicity vio G.(mg_mdegrees) =
  K.
Proof.
  unfold mg_mdegrees.
  rewrite multiplicity_disj_union.
  unfold mg_medges.
  rewrite 2!gmultiset_map_disj_union.
  rewrite  *)

(* Lemma gset_to_multiset_union *)

Lemma elem_of_mg_input_medges_cases iv : 
  iv ∈ G.(mg_input_medges) <->
  match iv with 
  | (inl (inr i), inl (inl v)) =>
    G.(mg_vert_inputs) !! i = Some v
  | _ => False
  end.
Proof.
  unfold mg_input_medges.
  rewrite elem_of_map_to_set.
  destruct iv as ([[|]|], [[|]|]);
  naive_solver.
Qed.

Lemma elem_of_mg_output_medges_cases iv : 
  iv ∈ G.(mg_output_medges) <->
  match iv with 
  | (inr o, inl (inl v)) =>
    G.(mg_vert_outputs) !! o = Some v
  | _ => False
  end.
Proof.
  unfold mg_output_medges.
  rewrite elem_of_map_to_set.
  destruct iv as ([[|]|], [[|]|]);
  naive_solver.
Qed.

Lemma elem_of_mg_io_medges_cases iv : 
  iv ∈ G.(mg_io_medges) <->
  match iv with 
  | (inl (inr i), inr o) =>
    G.(mg_boundary_inputs) !! i = Some o
  | _ => False
  end.
Proof.
  unfold mg_io_medges.
  rewrite elem_of_map_to_set.
  destruct iv as ([[|]|], [[|]|]);
  naive_solver.
Qed.

Lemma multiplicity_mg_vert_medges_cases uv : 
  multiplicity uv G.(mg_vert_medges) =
  match uv with 
  | (inl (inl u), inl (inl v)) =>
    multiplicity (u, v) G.(mg_vert_edges)
  | _ => 0
  end.
Proof.
  unfold mg_vert_medges.
  destruct uv as (u, v).
  apply multiplicity_eq.
  - rewrite elem_of_gmultiset_map.
    intros ((u', v') & [-> ->]%pair_eq & Huv').
    etransitivity; 
      [apply (multiplicity_gmultiset_map (prod_map (inl ∘ inl) (inl ∘ inl))
        _ (u', v'));
        by intros [] [] [[= ->] [= ->]]%pair_eq
        |].
    reflexivity.
  - rewrite elem_of_gmultiset_map.
    intros H.
    destruct u as [[u|]|], v as [[v|]|]; try reflexivity.
    symmetry.
    apply not_elem_of_gmultiset.
    intros Helem.
    apply H.
    eexists.
    split; [|eassumption].
    reflexivity.
Qed. 




Lemma multiplicity_mg_input_output_io_medges_cases iv : 
  multiplicity iv (gset_to_multiset 
    (G.(mg_input_medges) ∪ G.(mg_output_medges) ∪ G.(mg_io_medges))) =
  match iv with 
  | (inl (inr i), inl (inl v)) =>
    if decide (G.(mg_vert_inputs) !! i = Some v) then 1 else 0
  | (inr o, inl (inl v)) =>
    if decide (G.(mg_vert_outputs) !! o = Some v) then 1 else 0
  | (inl (inr i), inr o) =>
    if decide (G.(mg_boundary_inputs) !! i = Some o) then 1 else 0
  | _ => 0
  end.
Proof.
  rewrite multiplicity_gset_to_multiset.
  erewrite decide_rw. 
  unshelve (instantiate (1 := _)). 1:{
    rewrite 2!elem_of_union.
    rewrite elem_of_mg_input_medges_cases,
      elem_of_mg_output_medges_cases,
      elem_of_mg_io_medges_cases.
    reflexivity.
  }
  destruct iv as ([[|]|], [[|]|]); 
  ((apply decide_ext; naive_solver) || case_decide; naive_solver).
Qed.

Lemma multiplicity_mg_medges_cases iv : 
  multiplicity iv G.(mg_medges) =
  match iv with 
  | (inl (inr i), inl (inl v)) =>
    if decide (G.(mg_vert_inputs) !! i = Some v) then 1 else 0
  | (inr o, inl (inl v)) =>
    if decide (G.(mg_vert_outputs) !! o = Some v) then 1 else 0
  | (inl (inr i), inr o) =>
    if decide (G.(mg_boundary_inputs) !! i = Some o) then 1 else 0
  | (inl (inl u), inl (inl v)) =>
    multiplicity (u, v) G.(mg_vert_edges)
  | _ => 0
  end.
Proof.
  unfold mg_medges.
  rewrite multiplicity_disj_union.
  rewrite multiplicity_mg_vert_medges_cases, 
    multiplicity_mg_input_output_io_medges_cases.
  by destruct iv as ([[|]|], [[|]|]).
Qed.



Lemma dom_mg_medges_cases a : 
  a ∈ dom G.(mg_medges) <-> 
  match a with 
  | (inl (inr i), inl (inl v)) =>
    G.(mg_vert_inputs) !! i = Some v
  | (inr o, inl (inl v)) =>
    G.(mg_vert_outputs) !! o = Some v
  | (inl (inr i), inr o) =>
    G.(mg_boundary_inputs) !! i = Some o
  | (inl (inl u), inl (inl v)) =>
    (u, v) ∈ dom G.(mg_vert_edges)
  | _ => False
  end.
Proof using.
  rewrite gmultiset_elem_of_dom. 
  unfold elem_of at 1, gmultiset_elem_of at 1.
  rewrite multiplicity_mg_medges_cases.
  destruct a as ([[|]|], [[|]|]); [|try case_decide; split; lia + easy..].
  rewrite gmultiset_elem_of_dom. 
  reflexivity.
Qed.

(* Lemma dom_mg_medges_eq : 
  dom G.(mg_medges) =
   *)



Lemma size_mg_degrees : size G.(mg_degrees) = G.(mg_numedges) * 2.
Proof.
  unfold mg_degrees.
  rewrite gmultiset_size_disj_union, 2!size_gmultiset_map.
  unfold mg_numedges.
  lia.
Qed.


Lemma disjoint_dom_mg_vert_outputs_mg_boundary_outputs : 
  dom G.(mg_vert_outputs) ## dom G.(mg_boundary_outputs).
Proof.
  unfold mg_boundary_outputs.
  rewrite dom_natmap_inv.
  apply disjoint_sym.
  apply mg_WF_boundary_inputs_img.
Qed.



Lemma natmap_inj_mg_boundary_inputs : natmap_inj G.(mg_boundary_inputs).
Proof.
  by eapply minverses_natmap_inj_l, mg_WF_io_minverses.
Qed.

Lemma natmap_inj_mg_boundary_outputs : natmap_inj G.(mg_boundary_outputs).
Proof.
  by eapply minverses_natmap_inj_r, mg_WF_io_minverses. 
Qed.


Lemma mg_WF_mdegrees_outputs o : 
  multiplicity (inr o) G.(mg_mdegrees) =
  if decide (o ∈ G.(mg_output_set)) then 1 else 0.
Proof using HG.
  unfold mg_mdegrees.
  rewrite multiplicity_disj_union.
  rewrite 2!multiplicity_gmultiset_map_to_sum.
  rewrite set_Nsum_sum.
  erewrite (set_Nsum_ext _ 
    (fun a => (if decide (a.1 = inr o) then 1 else 0) +
      (* (if decide (G.(mg_vert_outputs) !! o = Some a.2) then 1 else 0) else 0) + *)
      (if decide (a.2 = inr o) then 1 else 0)
      (* (if decide (G.(mg_boundary_inputs) !! a.2 = Some o) then 1 else 0) else 0 *)
      )). 3: reflexivity.
  2: {
    intros (a1, a2) Ha.
    simpl.
    case_decide.
    - subst a1.
      rewrite dom_mg_medges_cases in Ha.
      destruct a2 as [[a2|]|]; [|easy..].
      rewrite multiplicity_mg_medges_cases.
      rewrite if_True, if_False by done.
      done.
    - case_decide; [|easy].
      subst.
      rewrite dom_mg_medges_cases in Ha.
      destruct a1 as [[|a1]|]; [easy| |easy].
      rewrite multiplicity_mg_medges_cases.
      rewrite if_True by done.
      done.
  }
  case_decide as Hoout.
  - destruct (decide (o ∈ dom G.(mg_vert_outputs))) as [Hovert | Honvert].
    + apply elem_of_dom in Hovert as [Go HGo].
      rewrite (set_Nsum_restrict _ {[(inr o, inl (inl Go))]}).
      * rewrite set_Nsum_singleton.
        simpl.
        by rewrite decide_True.
      * enough ((inr o, inl (inl Go)) ∈ dom G.(mg_medges)) by set_solver.
        by rewrite dom_mg_medges_cases.
      * intros (a1, a2).
        rewrite elem_of_difference, not_elem_of_singleton.
        intros (Ha & Hane).
        rewrite dom_mg_medges_cases in Ha.
        destruct a1 as [[|]|], a2 as [[|]|]; try done.
        --simpl.
          apply if_False.
          intros [=->].
          apply (mg_WF_boundary_inputs_img o).
          ++by apply elem_of_map_img_2 with n.
          ++rewrite elem_of_dom, HGo; done.
        --simpl.
          rewrite if_False; [reflexivity|].
          congruence.
    + assert (Hobound: o ∈ dom G.(mg_boundary_outputs)). 1: {
        unfold mg_output_set, mg_outputs in Hoout.
        rewrite dom_union, 2!dom_fmap, elem_of_union in Hoout.
        naive_solver.
      }
      apply elem_of_dom in Hobound as [i Hi].
      rewrite (set_Nsum_restrict _ {[(inl (inr i), inr o)]}).
      * rewrite set_Nsum_singleton.
        simpl.
        by rewrite decide_True.
      * enough ((inl (inr i), inr o) ∈ dom G.(mg_medges)) by set_solver.
        rewrite dom_mg_medges_cases.
        by apply lookup_natmap_inv_Some_inv in Hi.
      * intros (a1, a2).
        rewrite elem_of_difference, not_elem_of_singleton.
        intros (Ha & Hane).
        rewrite dom_mg_medges_cases in Ha.
        destruct a1 as [[|]|], a2 as [[|]|]; try done.
        --simpl.
          apply if_False.
          intros [=->].
          apply lookup_natmap_inv_Some_inv in Hi.
          pose proof natmap_inj_mg_boundary_inputs as Hinj.
          rewrite natmap_inj_alt' in Hinj.
          specialize (Hinj i n o Hi Ha).
          by subst.
        --simpl.
          rewrite if_False; [reflexivity|].
          intros [=->].
          unfold mg_boundary_outputs in Hi.
          apply disjoint_dom_mg_vert_outputs_mg_boundary_outputs with o;
          rewrite elem_of_dom; eexists; eauto.
  - apply set_Nsum_0_on.
    intros (a1, a2) Ha.
    rewrite dom_mg_medges_cases in Ha.
    simpl.
    case_decide; [exfalso| case_decide; [|easy]];
    destruct a1 as [[|a1]|a1], a2 as [[a2|]|a2]; try done.
    + apply Hoout.
      replace a1 with o in * by congruence.
      apply elem_of_dom.
      unfold mg_outputs.
      rewrite lookup_union, lookup_fmap, Ha.
      simpl.
      rewrite union_Some_l.
      done.
    + replace a2 with o in * by congruence.
      exfalso.
      apply mg_WF_io_minverses in Ha.
      apply Hoout.
      apply elem_of_dom.
      unfold mg_outputs.
      rewrite lookup_union, 2!lookup_fmap, Ha.
      simpl.
      rewrite union_Some_r.
      done.
Qed.

Lemma mg_WF_mdegrees_inputs i : 
  multiplicity (inl (inr i)) G.(mg_mdegrees) =
  if decide (i ∈ G.(mg_input_set)) then 1 else 0.
Proof using HG.
  unfold mg_mdegrees.
  rewrite multiplicity_disj_union.
  rewrite 2!multiplicity_gmultiset_map_to_sum.
  rewrite set_Nsum_sum.
  erewrite (set_Nsum_ext _ 
    (fun a => if decide (a.1 = inl (inr i)) then 1 else 0)). 3: reflexivity.
  2: {
    intros (a1, a2) Ha.
    simpl.
    rewrite (if_False (a2 = _)). 2: {
      intros ->.
      rewrite dom_mg_medges_cases in Ha.
      by destruct a1 as [[|]|].
    }
    case_decide; [|reflexivity].
    subst a1.
    rewrite dom_mg_medges_cases in Ha.
    destruct a2 as [[v|]|o]; [|easy|].
    - rewrite multiplicity_mg_medges_cases.
      by rewrite if_True.
    - rewrite multiplicity_mg_medges_cases.
      by rewrite if_True.
  }
  case_decide as Hoout.
  - pose proof Hoout as HGi.
    unfold mg_input_set in HGi.
    apply elem_of_dom in HGi as ([v | o] & Hv).
    + rewrite (set_Nsum_restrict _ {[(inl (inr i), inl (inl v))]}).
      * rewrite set_Nsum_singleton.
        simpl.
        by rewrite decide_True.
      * enough ((inl (inr i), inl (inl v)) ∈ dom G.(mg_medges)) by set_solver.
        rewrite dom_mg_medges_cases.
        apply lookup_omap_Some; by exists (inl v).
      * intros (a1, a2).
        rewrite elem_of_difference, not_elem_of_singleton.
        intros (Ha & Hane).
        simpl.
        apply if_False.
        intros ->.
        rewrite dom_mg_medges_cases in Ha.
        destruct a2 as [[v'|]|o']; [|done|].
        --apply lookup_omap_Some in Ha as ([] & [= ?] & ?).
          congruence.
        --apply lookup_omap_Some in Ha as ([] & [= ?] & ?).
          congruence.
    + rewrite (set_Nsum_restrict _ {[(inl (inr i), inr o)]}).
      * rewrite set_Nsum_singleton.
        simpl.
        by rewrite decide_True.
      * enough ((inl (inr i), inr o) ∈ dom G.(mg_medges)) by set_solver.
        rewrite dom_mg_medges_cases.
        apply lookup_omap_Some; by exists (inr o).
      * intros (a1, a2).
        rewrite elem_of_difference, not_elem_of_singleton.
        intros (Ha & Hane).
        rewrite dom_mg_medges_cases in Ha.
        destruct a1 as [[|]|], a2 as [[|]|]; try done.
        --simpl.
          apply if_False.
          intros [=->].
          apply lookup_omap_Some in Ha as ([] & [= ?] & ?).
          congruence.
        --simpl.
          apply if_False.
          intros [=->].
          apply lookup_omap_Some in Ha as ([] & [= ?] & ?).
          congruence.
  - apply set_Nsum_0_on.
    intros (a1, a2) Ha.
    rewrite dom_mg_medges_cases in Ha.
    simpl.
    apply if_False.
    destruct a1 as [[|a1]|], a2 as [[a2|]|a2]; try done.
    + intros [= ->].
      apply Hoout.
      apply elem_of_dom.
      by apply lookup_omap_Some in Ha as ([] & [= ?] & ->).
    + intros [= ->].
      apply Hoout.
      apply elem_of_dom.
      by apply lookup_omap_Some in Ha as ([] & [= ?] & ->).
Qed.


Lemma mg_WF_mdegrees_verts v : 
  multiplicity (inl (inl v)) G.(mg_mdegrees) =
  set_Nsum 
    (fun i => if decide (G.(mg_vert_inputs) !! i = Some v) then 1 else 0) 
    (dom G.(mg_vert_inputs)) + 
  set_Nsum 
    (fun o => if decide (G.(mg_vert_outputs) !! o = Some v) then 1 else 0)
    (dom G.(mg_vert_outputs)) + 
  (* from_option size 0 ((map_preimg G.(mg_vert_inputs) :> natmap natset) !! v) + 
  from_option size 0 ((map_preimg G.(mg_vert_outputs) :> natmap natset) !! v) + *)
  set_Nsum (fun a => 
    (if decide (a.1 = v) then multiplicity a G.(mg_vert_edges) else 0) + 
    (if decide (a.2 = v) then multiplicity a G.(mg_vert_edges) else 0))
    (dom G.(mg_vert_edges)).
Proof using HG.
  unfold mg_mdegrees.
  rewrite multiplicity_disj_union.
  rewrite 2!multiplicity_gmultiset_map_to_sum.
  rewrite set_Nsum_sum.
  erewrite (set_Nsum_ext _ 
    (fun a => 
    (if decide (a.2 = inl (inl v)) then
      match a.1 with
      | inl (inr i) => 
        if decide (G.(mg_vert_inputs) !! i = Some v) then 1 else 0
      | _ => 0
      end else 0) +
    (if decide (a.2 = inl (inl v)) then
      match a.1 with
      | inr o => 
        if decide (G.(mg_vert_outputs) !! o = Some v) then 1 else 0
      | _ => 0
      end else 0) +
    ( (if decide (a.2 = inl (inl v)) then
        match a.1 with
        | inl (inl u) => 
          multiplicity (u, v) G.(mg_vert_edges)
        | _ => 0
        end else 0) +
      (if decide (a.1 = inl (inl v)) then 
        match a.2 with 
        | inl (inl u) => multiplicity (v, u) G.(mg_vert_edges)
        | _ => 0
        end else 0) )
    )). 3: reflexivity.
  2: {
    intros (a1, a2).
    rewrite multiplicity_mg_medges_cases;
    rewrite dom_mg_medges_cases;
    simpl;
    destruct a1 as [[v'|i]|o];
    (destruct a2 as [[u'|]|]; [|done..]).
    - intros Hv'u'.
      (repeat case_decide);
      repeat match goal with 
      | Hut : _ = _ |- _ => pose proof Hut as [= -> ]
      end; lia.
    - intros HGi.
      rewrite if_False by easy.
      rewrite (if_True _ _ _ HGi).
      case_decide as Heq.
      + pose proof Heq as [= ->].
        rewrite if_True, if_False by done.
        reflexivity.
      + by rewrite if_False.
    - intros HGo.
      rewrite if_False by done.
      rewrite (if_True _ _ _ HGo).
      case_decide as Heq.
      + pose proof Heq as [= ->].
        rewrite if_True, if_False by done.
        reflexivity.
      + by rewrite if_False.
  }
  rewrite <- 2!set_Nsum_sum.
  f_equal; [f_equal|].
  - rewrite (set_Nsum_restrict _ (G.(mg_input_medges))).
    + unfold mg_input_medges.
      rewrite map_to_set_to_map_dom.
      rewrite set_Nsum_set_map by congruence.
      apply set_Nsum_ext; [|easy].
      intros a Ha.
      simpl.
      rewrite if_and.
      apply decide_ext.
      apply elem_of_dom in Ha as (v' & Hv').
      rewrite (lookup_total_correct _ _ _ Hv').
      naive_solver.
    + unfold mg_medges.
      rewrite dom_gmultiset_disj_union.
      apply union_subseteq_r'.
      rewrite dom_gset_to_multiset.
      apply union_subseteq_l'.
      apply union_subseteq_l.
    + intros (a1, a2) (Ha & Hani)%elem_of_difference.
      simpl.
      destruct a1 as [[|i]|]; [apply if_same| |apply if_same].
      rewrite if_and.
      apply if_False.
      intros (-> & HGi).
      apply Hani.
      by rewrite elem_of_mg_input_medges_cases.
  - rewrite (set_Nsum_restrict _ (G.(mg_output_medges))).
    + unfold mg_output_medges.
      rewrite map_to_set_to_map_dom.
      rewrite set_Nsum_set_map by congruence.
      apply set_Nsum_ext; [|easy].
      intros a Ha.
      simpl.
      rewrite if_and.
      apply decide_ext.
      apply elem_of_dom in Ha as (v' & Hv').
      rewrite (lookup_total_correct _ _ _ Hv').
      naive_solver.
    + unfold mg_medges.
      rewrite dom_gmultiset_disj_union.
      apply union_subseteq_r'.
      rewrite dom_gset_to_multiset.
      apply union_subseteq_l'.
      apply union_subseteq_r.
    + intros (a1, a2) (Ha & Hani)%elem_of_difference.
      simpl.
      destruct a1 as [[|]|o]; [apply if_same..|].
      rewrite if_and.
      apply if_False.
      intros (-> & HGi).
      apply Hani.
      by rewrite elem_of_mg_output_medges_cases.
  - rewrite (set_Nsum_restrict _ (dom G.(mg_vert_medges))); cycle 1.
    + unfold mg_medges.
      rewrite dom_gmultiset_disj_union.
      apply union_subseteq_l.
    + intros (a1, a2) (Ha & Hanv)%elem_of_difference.
      simpl.
      case_decide as Ha2;
      case_decide as Ha1.
      * subst.
        rewrite dom_mg_medges_cases in Ha.
        rewrite gmultiset_elem_of_dom, not_elem_of_gmultiset in Hanv.
        rewrite multiplicity_mg_vert_medges_cases in Hanv.
        rewrite gmultiset_elem_of_dom in Ha.
        unfold elem_of, gmultiset_elem_of in Ha.
        rewrite Hanv in Ha.
        easy.
      * subst.
        destruct a1 as [[v'|]|]; [|done..].
        rewrite Nat.add_0_r.
        apply not_elem_of_gmultiset.
        rewrite <- gmultiset_elem_of_dom.
        intros HF.
        apply Hanv.
        rewrite dom_mg_medges_cases in Ha.
        rewrite gmultiset_elem_of_dom.
        unfold elem_of, gmultiset_elem_of.
        rewrite multiplicity_mg_vert_medges_cases.
        apply gmultiset_elem_of_dom.
        apply Ha.
      * subst a1.
        destruct a2 as [[v'|]|]; [|done..].
        rewrite Nat.add_0_l.
        apply not_elem_of_gmultiset.
        rewrite <- gmultiset_elem_of_dom.
        intros HF.
        apply Hanv.
        rewrite dom_mg_medges_cases in Ha.
        rewrite gmultiset_elem_of_dom.
        unfold elem_of, gmultiset_elem_of.
        rewrite multiplicity_mg_vert_medges_cases.
        apply gmultiset_elem_of_dom.
        apply Ha.
      * reflexivity.
    + unfold mg_vert_medges.
      rewrite dom_gmultiset_map.
      rewrite set_Nsum_set_map by naive_solver.
      apply set_Nsum_ext; [|easy].
      intros (a1, a2) Ha.
      simpl.
      rewrite Nat.add_comm.
      f_equal;
      (repeat case_decide); congruence.
Qed.



Lemma mg_WF_mdegrees_cases a : 
  multiplicity a G.(mg_mdegrees) =
  match a with 
  | inl (inl v) => 
    set_Nsum 
      (fun i => if decide (G.(mg_vert_inputs) !! i = Some v) then 1 else 0) 
      (dom G.(mg_vert_inputs)) + 
    set_Nsum 
      (fun o => if decide (G.(mg_vert_outputs) !! o = Some v) then 1 else 0)
      (dom G.(mg_vert_outputs)) + 
    (* from_option size 0 ((map_preimg G.(mg_vert_inputs) :> natmap natset) !! v) + 
    from_option size 0 ((map_preimg G.(mg_vert_outputs) :> natmap natset) !! v) + *)
    set_Nsum (fun a => 
      (if decide (a.1 = v) then multiplicity a G.(mg_vert_edges) else 0) + 
      (if decide (a.2 = v) then multiplicity a G.(mg_vert_edges) else 0))
      (dom G.(mg_vert_edges))
  | inl (inr i) => 
    if decide (i ∈ G.(mg_input_set)) then 1 else 0
  | inr o => 
    if decide (o ∈ G.(mg_output_set)) then 1 else 0
  end.
Proof.
  destruct a as [[v | i] | o].
  - apply mg_WF_mdegrees_verts.
  - apply mg_WF_mdegrees_inputs.
  - apply mg_WF_mdegrees_outputs.
Qed.

Lemma elem_of_mg_indices_cases a : 
  a ∈ G.(mg_indices) <->
  match a with
  | inl (inl v) => v ∈ G.(mg_vert_set)
  | inl (inr i) => i ∈ G.(mg_input_set)
  | inr o => o ∈ G.(mg_output_set)
  end.
Proof.
  unfold mg_indices.
  rewrite elem_of_sum_set_cases.
  destruct a as [a|]; [|reflexivity].
  apply elem_of_sum_set_cases.
Qed.

Lemma mg_to_from_idx_minverses : 
  minverses G.(mg_to_idx) G.(mg_from_idx).
Proof.
  intros i idx.
  unfold mg_to_idx, mg_from_idx.
  rewrite 2!lookup_set_to_map by (simpl; congruence).
  setoid_rewrite pair_eq.
  setoid_rewrite (and_comm (_ ∈ _)).
  setoid_rewrite <- (and_assoc _).
  rewrite 2!exists_eq_l_iff.
  destruct i as [[v|i]|o]; simpl; 
  rewrite elem_of_mg_indices_cases.
  - rewrite <- (dom_natset_idx (G.(mg_vert_set))), 
      <- lookup_Some_iff_total_dom.
    split.
    + intros Hv.
      apply (elem_of_map_img_2 (SA:=natset)) in Hv as Hv'.
      unfold mg_vert_idx in Hv'.
      rewrite map_img_natset_idx in Hv'.
      rewrite elem_of_seq_set_0 in *.
      unfold mg_vert_set in Hv'.
      rewrite size_dom in Hv'.
      fold G.(mg_numspi) in Hv'.
      split; [|lia].
      rewrite if_True by easy.
      apply natset_nth_idx_minverses in Hv.
      by rewrite (lookup_total_correct _ _ _ Hv).
    + intros (Hidx & _).
      case_decide; [|by case_decide].
      apply inl_inj, inl_inj in Hidx.
      apply natset_nth_idx_minverses.
      fold G.(mg_vert_nth).
      rewrite lookup_lookup_total_dom; [congruence|].
      unfold mg_vert_nth.
      rewrite dom_natset_nth, elem_of_seq_set_0.
      unfold mg_vert_set.
      rewrite size_dom.
      assumption.
  - split.
    + intros (Hidx & Hi).
      rewrite if_False by lia.
      assert (HGi : G.(mg_input_idx) !! i = Some (idx - G.(mg_numspi))). 1: {
        rewrite lookup_lookup_total_dom by 
          (unfold mg_input_idx; now rewrite dom_natset_idx).
        f_equal.
        lia.
      }
      assert (idx < G.(mg_numspi) + G.(mg_insize)). 1:{
        apply (elem_of_map_img_2 (SA:=natset)) in HGi.
        unfold mg_input_idx in HGi.
        rewrite map_img_natset_idx, elem_of_seq_set_0 in HGi.
        unfold mg_input_set in HGi.
        rewrite size_dom in HGi.
        fold G.(mg_insize) in HGi.
        lia.
      }
      rewrite if_True by done.
      apply lookup_total_correct in HGi as HGi'.
      rewrite <- HGi'.
      rewrite elem_of_seq_set_0.
      split; [|lia].
      f_equal.
      f_equal.
      apply lookup_total_correct.
      apply natset_nth_idx_minverses.
      rewrite HGi'.
      apply HGi.
    + case_decide as Hidxbig; [easy|].
      case_decide as Hidxsmall; [|easy].
      intros [[= HGidx] _].
      assert (Hdom : idx - G.(mg_numspi) ∈ dom G.(mg_input_nth)). 1: {
        unfold mg_input_nth.
        rewrite dom_natset_nth.
        unfold mg_input_set.
        rewrite size_dom.
        fold G.(mg_insize).
        rewrite elem_of_seq_set_0.
        lia.
      }
      apply lookup_lookup_total_dom in Hdom.
      rewrite HGidx in Hdom.
      apply (elem_of_map_img_2 (SA:=natset)) in Hdom as Hi.
      unfold mg_input_nth in Hi.
      rewrite map_img_natset_nth in Hi.
      split; [|easy].
      enough (G.(mg_input_idx) !!! i = idx - G.(mg_numspi)) by lia.
      apply lookup_total_correct.
      apply natset_nth_idx_minverses.
      apply Hdom.
  - rewrite elem_of_seq_set_0.
    split.
    + intros (HGo & Ho).
      rewrite 2!if_False by lia.
      split.
      * f_equal.
        apply lookup_total_correct.
        apply natset_nth_idx_minverses.
        rewrite lookup_lookup_total_dom by by rewrite dom_natset_idx.
        f_equal.
        fold G.(mg_output_idx).
        lia.
      * enough (G.(mg_output_idx) !!! o < G.(mg_outsize)) by lia.
        rewrite <- (elem_of_seq_set_0 (A:=natset)).
        unfold mg_outsize.
        rewrite <- size_dom.
        fold G.(mg_output_set).
        rewrite <- map_img_natset_idx.
        apply elem_of_map_img_2 with o.
        apply lookup_lookup_total_dom.
        unfold mg_output_idx.
        now rewrite dom_natset_idx.
    + case_decide as _h; [easy|clear _h].
      case_decide as Hidxbig; [easy|].
      intros [[= Ho] Hidx].
      assert (Hdom : idx - (G.(mg_numspi) + G.(mg_insize)) 
        ∈ dom G.(mg_output_nth)). 1:{
        unfold mg_output_nth.
        rewrite dom_natset_nth, elem_of_seq_set_0.
        unfold mg_output_set.
        rewrite size_dom.
        fold G.(mg_outsize).
        lia.
      }
      apply lookup_lookup_total_dom in Hdom as Hdom'.
      rewrite Ho in Hdom'.
      apply natset_nth_idx_minverses in Hdom'.
      apply elem_of_dom_2 in Hdom' as Hdom''.
      rewrite dom_natset_idx in Hdom''.
      apply lookup_total_correct in Hdom'.
      fold G.(mg_output_idx) in Hdom'.
      rewrite Hdom'.
      split; [lia | apply Hdom''].
Qed.



(* FIXME: Move *)
Lemma dom_mg_from_idx : 
  dom G.(mg_from_idx) = 
  seq_set 0 (G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize)).
Proof.
  apply set_eq => x.
  unfold mg_from_idx.
  rewrite dom_set_to_map.
  unfold compose.
  simpl.
  rewrite set_map_id_inhom.
  rewrite set_cast_seq_set.
  reflexivity.
Qed.

Lemma map_img_mg_from_idx : 
  map_img G.(mg_from_idx) = G.(mg_indices).
Proof.
  rewrite (minverses_map_img_eq_dom_L _ _ (minverses_symm _ _ 
    mg_to_from_idx_minverses)).
  apply dom_mg_to_idx.
Qed.




Lemma mg_WF_dom_mdegrees_subseteq :
  dom G.(mg_mdegrees) ⊆ G.(mg_indices).
Proof.
  intros x.
  rewrite gmultiset_elem_of_dom.
  unfold elem_of at 1, gmultiset_elem_of.
  rewrite mg_WF_mdegrees_cases.
  revert x.
  intros [[v|i]|o].
  - rewrite 2!nat_add_pos, 3!set_Nsum_pos.
    intros [[(a & Ha & Hdec)|(a & Ha & Hdec)]|((a1, a2) & Ha & Hdec)];
    apply elem_of_mg_indices_cases.
    + case_decide as Ha'; [|easy].
      apply (elem_of_map_img_2 (SA:=natset)) in Ha' as Himg.
      by apply mg_WF_vert_inputs in Himg.
    + case_decide as Ha'; [|easy].
      apply (elem_of_map_img_2 (SA:=natset)) in Ha' as Himg.
      by apply mg_WF_vert_outputs in Himg.
    + simpl in Hdec.
      case_decide as Ha1; case_decide as Ha2.
      * rewrite nat_add_pos in Hdec.
        assert (Hdec' : 0 < multiplicity (a1, a2) G.(mg_vert_edges)) by 
          by destruct Hdec.
        pose proof (Hdec' : (a1, a2) ∈ G.(mg_vert_edges)) as Hdec''.
        rewrite <- gmultiset_elem_of_dom in Hdec''.
        apply mg_WF_vert_edges.
        rewrite elem_of_edgeset_dom.
        exists (a1, a2).
        simpl.
        split; by try left.
      * rewrite Nat.add_0_r in Hdec.
        pose proof (Hdec : (a1, a2) ∈ G.(mg_vert_edges)) as Hdec'.
        rewrite <- gmultiset_elem_of_dom in Hdec'.
        apply mg_WF_vert_edges.
        rewrite elem_of_edgeset_dom.
        exists (a1, a2).
        simpl.
        split; by try left.
      * rewrite Nat.add_0_l in Hdec.
        pose proof (Hdec : (a1, a2) ∈ G.(mg_vert_edges)) as Hdec'.
        rewrite <- gmultiset_elem_of_dom in Hdec'.
        apply mg_WF_vert_edges.
        rewrite elem_of_edgeset_dom.
        exists (a1, a2).
        simpl.
        split; by try right.
      * easy.
  - rewrite elem_of_mg_indices_cases.
    now case_decide.
  - rewrite elem_of_mg_indices_cases. 
    now case_decide.
Qed.


Lemma mg_mdegrees_eq_map_degrees : 
  G.(mg_mdegrees) = gmultiset_map (G.(mg_from_idx) !!!.) G.(mg_degrees).
Proof.
  rewrite mg_degrees_eq_map_mdegrees.
  rewrite <- gmultiset_map_compose.
  symmetry.
  apply gmultiset_map_id_on.
  intros a Ha%gmultiset_elem_of_dom.
  apply mg_WF_dom_mdegrees_subseteq in Ha.
  apply minverses_lookup_total_linv.
  - apply mg_to_from_idx_minverses.
  - by rewrite dom_mg_to_idx.
Qed.


Lemma mg_WF_degrees_inv a : 
  a < G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize) -> 
  multiplicity a G.(mg_degrees) =
  multiplicity (G.(mg_from_idx) !!! a) G.(mg_mdegrees).
Proof.
  intros Hasmall%(elem_of_seq_set_0 (A:=natset)).
  rewrite mg_mdegrees_eq_map_degrees.
  rewrite (multiplicity_gmultiset_map' (G.(mg_from_idx) !!!.)); [easy|].
  intros b c.
  assert (Hle : {[a]} ∪ dom G.(mg_degrees) ⊆ seq_set 0
    (G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize))) 
    by (rewrite union_subseteq; split; [set_solver | apply dom_mg_degrees_WF]).
  intros Hb%Hle Hc%Hle.
  intros Heq%(f_equal (G.(mg_to_idx) !!!.)).
  rewrite 2!(minverses_lookup_total_rinv _ _ 
    mg_to_from_idx_minverses) in Heq
    by (by rewrite dom_mg_from_idx).
  apply Heq.
Qed.

Lemma lookup_mg_from_idx a : 
  G.(mg_from_idx) !! a =
  if decide (a < G.(mg_numspi)) then
    Some $ inl (inl (G.(mg_vert_nth) !!! a))
  else if decide (a < G.(mg_numspi) + G.(mg_insize)) then
    Some $ inl (inr (G.(mg_input_nth) !!! (a - G.(mg_numspi))))
  else if decide (a < G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize)) then
    Some $ inr (G.(mg_output_nth) !!! (a - (G.(mg_numspi) + G.(mg_insize))))
  else None.
Proof.
  unfold mg_from_idx.
  case_decide as Ha1; [|case_decide as Ha2; [|case_decide as Ha3]].
  - rewrite lookup_set_to_map by easy.
    exists a.
    split; [by rewrite elem_of_seq_set_0; lia|].
    f_equal.
    by apply if_True.
  - rewrite lookup_set_to_map by easy.
    exists a.
    split; [by rewrite elem_of_seq_set_0; lia|].
    f_equal.
    rewrite if_False by done.
    by apply if_True.
  - rewrite lookup_set_to_map by easy.
    exists a.
    split; [by rewrite elem_of_seq_set_0; lia|].
    f_equal.
    rewrite 2!if_False by done.
    done.
  - apply option_eq => vio.
    split; [|easy].
    rewrite lookup_set_to_map by easy.
    intros (? & ?%elem_of_seq_set_0 & []%pair_eq).
    exfalso; lia.
Qed.

Lemma size_mg_input_set : size G.(mg_input_set) = G.(mg_insize).
Proof using. apply size_dom. Qed.

Lemma size_mg_output_set : size G.(mg_output_set) = G.(mg_outsize).
Proof using. apply size_dom. Qed.

Lemma size_mg_vert_set : size G.(mg_vert_set) = G.(mg_numspi).
Proof using. apply size_dom. Qed.

Lemma mg_WF_degrees_large a : 
  G.(mg_numspi) <= a < G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize) ->
  multiplicity a G.(mg_degrees) = 1.
Proof.
  intros Ha.
  rewrite mg_WF_degrees_inv by easy.
  rewrite lookup_total_alt.
  rewrite lookup_mg_from_idx.
  rewrite if_False by lia.
  rewrite mg_WF_mdegrees_cases.
  case_decide as Ha'; [|rewrite if_True by lia].
  - simpl.
    apply if_True.
    apply lookup_total_elem_of_of_dom.
    + unfold mg_input_nth.
      by rewrite map_img_natset_nth.
    + unfold mg_input_nth.
      rewrite dom_natset_nth, elem_of_seq_set_0.
      rewrite size_mg_input_set.
      lia.
  - cbn [default Datatypes.id].
    apply if_True.
    apply lookup_total_elem_of_of_dom.
    + unfold mg_output_nth.
      by rewrite map_img_natset_nth.
    + unfold mg_output_nth.
      rewrite dom_natset_nth, elem_of_seq_set_0.
      rewrite size_mg_output_set.
      lia.
Qed.

(* Lemma mg_WF_degrees_outputs : *)


Lemma mg_size_pf :
  big_sum (λ x, multiplicity x G.(mg_degrees)) G.(mg_numspi) 
    + G.(mg_insize) + G.(mg_outsize)
  = G.(mg_numedges) * 2.
Proof.
  rewrite <- Nat.add_assoc.
  rewrite <- big_sum_of_1_r. 2:{
    intros x Hx.
    unfold rshift; simpl.
    apply mg_WF_degrees_large; lia.
  }
  rewrite <- (set_Nsum_seq_set_0_big_sum (SA:=gmap.gset nat)).
  rewrite <- size_mg_degrees.
  apply sum_multiplicities_size_subseteq.
  rewrite set_cast_id, Nat.add_assoc.
  apply dom_mg_degrees_WF.
Qed.

End WF_mapgraph.




(* FIXME: Move this to by ZX_el_graph *) 

Lemma WF_edgefunc_0 n f : WF_edgefunc 0 n f.
Proof. hnf. by lia. Qed.

Definition ZX_el_graph_X (n m : nat) (a : R) : ZX_el_graph n m. 
refine ({|
  el_edges := n+m; 
  el_numspi := 1;
  el_color := inhabitant; 
  el_phase := inhabitant;
  el_edgefunc := λ k, (1 + k, 0);
|}).
- intros k Hk.
  rewrite rshift_defn.
  simpl.
  unfold edgefunc_deg.
  apply big_sum_unique.
  exists k; split; first by done.
  split.
  + rewrite (proj2 (Nat.eqb_eq _ _)) by (cbn; lia).
    rewrite (proj2 (Nat.eqb_neq _ _)) by (cbn; lia).
    reflexivity.
  + intros k' Hk' Hkk'.
    rewrite 2!(proj2 (Nat.eqb_neq _ _)) by (cbn; lia).
    reflexivity.
- intros k Hk.
  simpl; split; lia.
Qed.

(* Lemma multiplicity_mg_degrees_alt_WF `{HG : WF_ZX_map_graph G} k : 
  multiplicity k G.(mg_degrees) = 
  big_su
*)


Lemma gmultiset_dom_ind' `{Countable A} (P : gmultiset A -> Prop) : 
  P ∅ -> (∀ (x : A) (n : nat) g, 0 < n -> x ∉ dom g -> 
    elements ((n *: {[+x+]}) ⊎ g) = 
    replicate n x ++ elements g -> P g -> P ((n *: {[+x+]}) ⊎ g)) -> 
  ∀ g, P g.
Proof.
  intros HPemp HPind.
  intros (g).
  induction g as [|x n g Hgi Hfirst IHg] using map_first_key_ind.
  - apply HPemp.
  - enough (Hrw : {| gmultiset_car := <[x:=n]> g |}
      = Pos.to_nat n *: {[+ x +]} ⊎ GMultiSet g).
      { rewrite Hrw. 
        apply HPind, IHg.
        - lia.
        - simpl.
          apply not_elem_of_dom.
          apply Hgi.
        - rewrite <- Hrw.
          unfold elements.
          simpl.
          rewrite map_to_list_insert_first_key by done.
          reflexivity. }
    apply gmultiset_eq => a.
    rewrite multiplicity_disj_union, multiplicity_scalar_mul.
    rewrite multiplicity_singleton_eq.
    unfold multiplicity.
    simpl.
    case_decide as Hax.
    + subst a.
      rewrite Hgi, lookup_insert.
      lia.
    + rewrite lookup_insert_ne by done.
      lia.
Qed.

(* FIXME: Move, make more formal *)
Lemma linear_0_eq_0 `{Comm_Monoid A, Comm_Monoid B} 
  (g : A -> B) (Hcharne2 : forall a : B, 
    (a + a)%G = a -> a = 0%G): (∀ a b, g (a + b)%G = (g a + g b)%G) ->
  g 0%G = 0%G.
Proof.
  intros Hg.
  apply Hcharne2.
  rewrite <- Hg.
  f_equal.
  apply Gplus_0_l.
Qed.

Lemma big_sum_compose_linear `{Comm_Monoid A, Comm_Monoid B} 
  (g : A -> B) (f : nat -> A) n 
  (Hg0 : g 0%G = 0%G) (Hg : ∀ a b, g (a + b)%G = (g a + g b)%G) :
  big_sum (g ∘ f) n = g (big_sum f n).
Proof.
  induction n.
  - symmetry; apply Hg0.
  - simpl.
    rewrite IHn.
    symmetry; apply Hg.
Qed.

Lemma multiplicity_0 `{Countable A} a (g : gmultiset A) : 
  a ∉ dom g -> multiplicity a g = 0.
Proof. by rewrite gmultiset_elem_of_dom; apply not_elem_of_gmultiset. Qed.

Lemma set_Nsum_multiplicities_dom_to_elements_gen `{Countable A} `{Inhabited A}
  (g : gmultiset A) (f : A -> nat -> nat) 
  (Hf : forall a k l, a ∈ dom g ->
     f a (k + l) = f a k + f a l) : 
  set_Nsum (λ a, f a (multiplicity a g)) (dom g) = 
  big_sum (λ k, f (elements g !!! k) 1) (size g).
Proof.
  induction g as [|x n g Hn Hx Helem IHg] 
    using gmultiset_dom_ind'; first by reflexivity.
  rewrite dom_gmultiset_disj_union, dom_gmultiset_scalar_mul_pos, 
    dom_gmultiset_singleton by done.
  rewrite set_Nsum_disj_union by set_solver.
  rewrite gmultiset_size_disj_union, gmultiset_size_scalar_mul.
  rewrite gmultiset_size_singleton, Nat.mul_1_r.
  rewrite big_sum_sum.
  simpl.
  rewrite dom_gmultiset_disj_union, 
    dom_gmultiset_scalar_mul_pos, dom_gmultiset_singleton in Hf by done.
  f_equal.
  - rewrite set_Nsum_singleton.
    rewrite multiplicity_disj_union, multiplicity_scalar_mul, 
      multiplicity_singleton.
    rewrite (proj1 (not_elem_of_gmultiset g x)) by 
      (by rewrite <- gmultiset_elem_of_dom).
    rewrite Nat.add_0_r, Nat.mul_1_r.
    erewrite big_sum_eq_bounded. 2:{
      intros k hk.
      rewrite Helem.
      rewrite list_lookup_total_alt.
      rewrite lookup_app.
      rewrite lookup_replicate_2 by done.
      simpl.
      reflexivity.
    }
    assert (Hf' : forall k l, f x (k + l) = f x k + f x l) by
      (intros; apply Hf; set_solver).
    clear -Hf'.
    change (λ _ : nat, f x 1) with (f x ∘ (λ _ : nat, 1)).
    rewrite (big_sum_compose_linear (f x) (λ _, 1)) by
      (exact Hf' || generalize (Hf' 0 0); simpl; lia).
    by rewrite Nsum_1.
  - specialize (IHg ltac:(intros; apply Hf; set_solver)).
    erewrite set_Nsum_ext, IHg; [..|reflexivity].
    + apply big_sum_eq_bounded.
      intros k Hk.
      rewrite Helem.
      f_equal.
      rewrite 2!list_lookup_total_alt, 
        lookup_app, (proj1 (lookup_replicate_None _ _ _)) by lia.
      f_equal.
      f_equal.
      by rewrite length_replicate, add_sub'.
    + intros a Ha.
      simpl.
      f_equal.
      rewrite multiplicity_disj_union, 
        multiplicity_scalar_mul.
      rewrite multiplicity_0 by (rewrite dom_gmultiset_singleton, 
        elem_of_singleton; congruence).
      lia.
Qed.

Lemma set_Nsum_eq `{FinSet A SA} (f f' : A -> nat) (s : SA) : 
  (∀ a, a ∈ s -> f a = f' a) ->
  set_Nsum f s = set_Nsum f' s.
Proof.
  intros; by apply set_Nsum_ext.
Qed.

Lemma decide_to_b2n `{HP : Decision P} : 
  (if decide P then 1 else 0) = Nat.b2n (bool_decide P).
Proof.
  by destruct HP.
Qed.

Lemma b2n_to_decide b : 
  Nat.b2n b = if decide b then 1 else 0.
Proof. 
  by destruct b. 
Qed.

Lemma b2n_to_decide' b : 
  Nat.b2n b = if decide (b = true) then 1 else 0.
Proof. 
  by destruct b. 
Qed.

Lemma size_gset_to_multiset `{Countable A} (g : gmap.gset A) : 
  size (gset_to_multiset g) = size g.
Proof.
  rewrite <- sum_multiplicities_size.
  rewrite <- (Nat.mul_1_l (size g)).
  rewrite <- (set_Nsum_const_on (λ _, 1)) by done.
  rewrite dom_gset_to_multiset.
  apply set_Nsum_eq.
  intros.
  rewrite multiplicity_gset_to_multiset.
  by rewrite decide_True by done.
Qed.

Lemma size_to_set_sum `{FinSet A SA} (s : SA) : 
  size s = set_Nsum (λ _, 1) s.
Proof.
  by rewrite set_Nsum_const_on with _ _ 1 by done.
Qed.

Lemma size_union_to_inter `{FinSet A SA} (s t : SA) : 
  size (s ∪ t) = size s + size t - size (s ∩ t).
Proof.
  rewrite 4!size_to_set_sum.
  apply set_Nsum_union.
Qed.

Lemma set_Nsum_filter `{FinSet A SA} (s : SA) P `{∀ x, Decision (P x)} 
  (f : A -> nat) : 
  set_Nsum f (filter P s) = 
  set_Nsum (λ a, if decide (P a) then f a else 0) s.
Proof.
  revert s.
  apply set_ind.
  - intros s s' Hs Himpl.
    rewrite <- Hs at 2.
    rewrite <- Himpl.
    apply set_Nsum_ext; [done|].
    set_solver.
  - by rewrite filter_empty, 2!set_Nsum_empty.
  - intros a s Ha IH.
    rewrite filter_union.
    rewrite 2!set_Nsum_disj_union by set_solver.
    f_equal; [|apply IH].
    rewrite set_Nsum_singleton.
    case_decide as HPa.
    + by rewrite filter_singleton, set_Nsum_singleton.
    + by rewrite filter_singleton_not, set_Nsum_empty.
Qed.


Lemma mg_insize_alt (G : ZX_map_graph) : 
  G.(mg_insize) = size G.(mg_vert_inputs) + size G.(mg_boundary_inputs).
Proof.
  rewrite <- 2!size_dom.
  rewrite 2!size_to_set_sum.
  unfold mg_vert_inputs, mg_boundary_inputs.
  rewrite 2!dom_omap.
  rewrite 2!set_Nsum_filter.
  rewrite set_Nsum_sum.
  unfold mg_insize.
  rewrite <- size_dom, size_to_set_sum.
  apply set_Nsum_eq.
  simpl.
  intros a ([l|r] & ->)%elem_of_dom; done.
Qed.

(* FIXME: Move *)
(* Lemma size_minverses `{FinMapDom A MA SA, FinMapDom B MB SB} 
  `{!Elements A SA} `{!FinSet A SA} `{!Elements B SB} `{!FinSet B SB}
  (f : MA B) (g : MB A) : minverses f g -> 
  size f = size g.
Proof.
  intros Hinv.
  rewrite <- 2!size_dom.
  
  map_size *)

(* Lemma mg_outsize_alt `{HG : WF_ZX_map_graph G} : 
  G.(mg_outsize) = size G.(mg_vert_outputs) + size G.(mg_boundary_inputs).
Proof.
  rewrite <- 2!size_dom.
  rewrite 2!size_to_set_sum.
  rewrite mg_vert_outputs_eq_omap.
  unfold mg_boundary_inputs.
  rewrite 2!dom_omap_L.
  rewrite 2!set_Nsum_filter.
  rewrite set_Nsum_sum.
  unfold mg_insize.
  rewrite <- size_dom, size_to_set_sum.
  apply set_Nsum_eq.
  simpl.
  intros a ([l|r] & ->)%elem_of_dom; done.
Qed. *)


  

(* Lemma mg_numedges_alt (G : ZX_map_graph) : 
  G.(mg_numedges) = size G.(mg_vert_medges) + 
    G.(mg_insize) + G.(mg_outsize) - size G.(mg_io_edges).
Proof.
  unfold mg_numedges, mg_edges.
  rewrite size_gmultiset_map.
  unfold mg_medges.
  rewrite gmultiset_size_disj_union, size_gset_to_multiset.
  rewrite 2!size_union.
  2: {
   intros x.
   rewrite elem_of_mg_input_medges_cases, elem_of_mg_output_medges_cases.
   by destruct x as ([[|]|], [[|]|]).
  }
  2: {
   intros x.
   rewrite elem_of_union, elem_of_mg_input_medges_cases, 
    elem_of_mg_output_medges_cases, elem_of_mg_io_medges_cases.
   by destruct x as ([[|]|], [[|]|]); intros [].
  } 
*)


Lemma mg_WF_numedges_pos_impl `{HG : WF_ZX_map_graph G} : 
  0 < G.(mg_numedges) -> 0 < G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize).
Proof.
  enough (G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize) = 0 -> 
    G.(mg_numedges) = 0) by lia.
  intros H0.
  unfold mg_numedges.
  apply gmultiset_size_empty_iff.
  apply gmultiset_eq => a.
  rewrite multiplicity_empty.
  apply not_elem_of_gmultiset.
  intros Ha.
  (* intros (x & _ & Hx)%elem_of_gmultiset_map. *)
  assert (a.1 < G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize)). 1: {
    rewrite <- (elem_of_seq_set_0 (A:=natset)).
    apply mg_WF_edges.
    rewrite elem_of_edgeset_dom.
    exists a. 
    rewrite gmultiset_elem_of_dom.
    naive_solver.
  }
  lia.
Qed.








Lemma edgefunc_deg_ZX_map_graph `{HG : WF_ZX_map_graph G} k : 
  edgefunc_deg G.(mg_numedges) G.(mg_edge_func) k = 
  multiplicity k G.(mg_degrees).
Proof.
  unfold edgefunc_deg.
  (* rewrite Nsum_plus. *)
  
  unfold mg_degrees.
  rewrite multiplicity_disj_union.
  erewrite 2!multiplicity_gmultiset_map_to_sum.
  (* erewrite set_Nsum_eq. 2: {intros.
    pattern (multiplicity a (G.(mg_edges))). reflexivity). *)
  rewrite 2!(set_Nsum_multiplicities_dom_to_elements_gen
    G.(mg_edges) (λ a m, if decide (_ = k) then m else 0))
    by (intros; by case_decide).
  fold G.(mg_numedges).
  rewrite <- Nsum_plus.
  apply big_sum_eq_bounded => x Hx.
  rewrite 2!b2n_to_decide'.
  f_equal; apply decide_ext; apply Nat.eqb_eq.
Qed.

Lemma prf_ZX_el_graph_of_map_graph_1 {G} (HG : WF_ZX_map_graph G) : 
  perm_eq (G.(mg_insize) + G.(mg_outsize))
    (edgefunc_deg G.(mg_numedges) G.(mg_edge_func)
      ∘ rshift G.(mg_numspi)) (λ _ : nat, 1).
Proof.
  intros k Hk.
  rewrite rshift_defn; simpl.
  rewrite edgefunc_deg_ZX_map_graph.
  apply mg_WF_degrees_large; lia.
Qed.

Lemma prf_ZX_el_graph_of_map_graph_2 {G} (HG : WF_ZX_map_graph G) : 
  WF_edgefunc G.(mg_numedges)
    (G.(mg_numspi) + G.(mg_insize) + G.(mg_outsize)) 
    G.(mg_edge_func).
Proof.
  intros k Hk.
  assert (Hdom : G.(mg_edge_func) k ∈ dom G.(mg_edges)). 1:{
    unfold mg_edge_func.
    apply elem_of_list_lookup_total_2 in Hk as Hk'.
    rewrite gmultiset_elem_of_elements in Hk'.
    by rewrite gmultiset_elem_of_dom.
  }
  split; apply (elem_of_seq_set_0 (A:=natset));
  apply mg_WF_edges;
  apply elem_of_edgeset_dom;
  exists (G.(mg_edge_func) k);
  (split; [|solve [by right | by left]]);
  apply Hdom.
Qed.

Definition ZX_el_graph_of_map_graph (G : ZX_map_graph) : 
  ZX_el_graph G.(mg_insize) G.(mg_outsize) :=
  match @decide _ (WF_ZX_map_graph_dec G) with
  | left HG =>
    {|
      el_edges := G.(mg_numedges); 
      el_numspi := G.(mg_numspi);
      el_color := fst ∘ (G.(mg_verts) !!!.); 
      el_phase := snd ∘ (G.(mg_verts) !!!.); 
      el_edgefunc := G.(mg_edge_func);
      el_io_deg_1 := prf_ZX_el_graph_of_map_graph_1 HG;
      el_edgefunc_WF := prf_ZX_el_graph_of_map_graph_2 HG;
    |}
  | right _ => ZX_el_graph_X _ _ 0
  end.












(* Definition WF_ZX_map_graph (f : natmap nat) :=
  map_img f ⊆ .
  map_img (sum_elim Datatypes.id Datatypes.id <$> G.(mg_inputs)) 
    ⊆ (* Some <$> *)dom G.(mg_verts). *)


(*
Definition WF_ZX_map_graph (G : ZX_map_graph) :=
  map_img (mg_vert_inputs G) ⊆ dom G.(mg_verts) ∧
  map_img (mg_vert_outputs G) ⊆ dom G.(mg_verts) ∧
  set_bind (fun '(i, j) => {[i; j]} ) 
    $ dom G.(mg_vert_edges) ⊆ dom G.(mg_verts) ∧
  map_img (mg_boundary_inputs G) ## dom G.(mg_outputs) ∧
  minverses (mg_boundary_inputs G) (mg_boundary_outputs G).

(* Definition WF_ZX_map_graph (G : ZX_map_graph) :=
  map_img (mg_vert_inputs G) ⊆ dom G.(mg_verts) ∧
  map_img (mg_vert_outputs G) ⊆ dom G.(mg_verts) ∧
  set_bind (fun '(i, j) => {[i; j]} ) 
    $ dom G.(mg_edges) ⊆ dom G.(mg_verts) ∧
  (* set_map fst $ dom G.(mg_edges) ⊆ dom G.(mg_verts) ∧
  set_map snd $ dom G.(mg_edges) ⊆ dom G.(mg_verts) ∧ *)
  minverses (mg_boundary_inputs G) (mg_boundary_outputs G). *)

Lemma WF_map_fst_subset_dom_verts G (HG : WF_ZX_map_graph G) : 
  set_map fst $ dom G.(mg_edges) ⊆ dom G.(mg_verts).
Proof.
  rewrite <- (proj1 (proj2 (proj2 HG))).
  intros i.
  rewrite elem_of_map, elem_of_set_bind.
  intros (x & -> & Hx).
  exists x.
  split; [easy|].
  case_match.
  set_solver.
Qed.

Lemma WF_map_snd_subset_dom_verts G (HG : WF_ZX_map_graph G) : 
  set_map snd $ dom G.(mg_edges) ⊆ dom G.(mg_verts).
Proof.
  rewrite <- (proj1 (proj2 (proj2 HG))).
  intros i.
  rewrite elem_of_map, elem_of_set_bind.
  intros (x & -> & Hx).
  exists x.
  split; [easy|].
  case_match.
  set_solver.
Qed.



Definition mg_numspi (G : ZX_map_graph) : nat :=
  size G.(mg_verts).

Definition mg_insize (G : ZX_map_graph) : nat :=
  size G.(mg_inputs).

Definition mg_outsize (G : ZX_map_graph) : nat :=
  size G.(mg_outputs).

Definition mg_input_edges (G : ZX_map_graph)

Definition ZX_map_graph_edge_multiset (G : ZX_map_graph) : gmultiset (nat * nat) :=
  G.(mg_edges) ∪ 












Require Import FMaps.

(* Module NatMap := . *)

Module NatMap <: Sord.

Include Make_ord Nat_as_OT Nat_as_OT.

Include OrdProperties MapS.

End NatMap.

Search (_ -> NatMap.t).
*)















































(*

Definition edgeperm_of_edgefunc n (f : nat -> nat * nat) : nat -> nat * nat :=
  edgefunc_of_infunc (perm_of_input_func (n * 2) (infunc_of_edgefunc f)).

Lemma ZX_of_edgefunc_to_ZX_of_edgeperm n f : 
  ZX_of_edgefunc n f = 
  ZX_of_edgeperm n (edgeperm_of_edgefunc n f).
Proof.
  unfold ZX_of_edgeperm.
  unfold edgeperm_of_edgefunc.
  now rewrite infunc_of_edgefunc_of_infunc.
Qed.

(* Add Parametric Morphism  *)

(* Find the index of the [t]th edge of [f] (up to size [n]) containing [k] *)
Fixpoint edgefunc_idx n f k t :=
  match n with 
  | 0 => 0
  | S n' => 
    if edge_mem k (f 0) then
      if t =? 0 then 
        0
      else
        1 + (edgefunc_idx n' (f ∘ rshift 1) k (t - 1))
    else
        1 + (edgefunc_idx n' (f ∘ rshift 1) k t)
  end.

(* Search count_func_vals infunc_of_edgefunc. *)

Lemma edgefunc_idx_correct n f k t 
  (Hk : t < count_func_vals (n * 2) (infunc_of_edgefunc f) k) : 


Fixpoint get_edgeperm_partner n (f : nat -> nat * nat) (k : nat) :=
  match n with 
  | 0 => k
  | S n' => if edge_mem k (f n') then edge_partner k (f n') else 
    get_edgeperm_partner n' f k
  end.

Lemma get_edgeperm_partner_present n f k : 
  forall a, a < n -> edge_mem k (f a) = true ->
    (forall b, b < a -> edge_mem k (f b) = ) 
    get_edgeperm_partner n f k = edge_partner k (f a).
Proof.
  induction n; intros a Ha; [lia|].
  bdestruct (a =? n).
  - subst.
    simpl.
    now intros ->.
  - simpl.
  intros a Ha.
  induction Ha.
  - 

Lemma edgeperm_partner_defn

Lemma edgeperm_partner_edgeperm_of_edgefunc_unique n f k 
  (Hk : count_func_vals (n * 2) (infunc_of_edgefunc f) = 1) : 
  edgeperm_partner 


Definition ZX_of_el_data n m edges numspi deg 
  color phase edgefunc (size_pf : big_sum deg numspi + n + m = edges * 2) : 
  ZX (n + m) 0 := 
  ZX_of_stack n m numspi deg phase color edges size_pf ⟷
  ZX_of_edgefunc edges edgefunc.


perm_of_input_func
perm_of_input_func_decomp


Lemma compose_arb_cup_ZX_of_edgeperm n k l f (Hf : edgepermutation n f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) : 
  zx_arb_cup k l (n * 2) ⟷ ZX_of_edgeperm n f ∝
  cast _ _ (eq_sym (Nat.mul_sub_distr_r n 1 2)) eq_refl (
    ZX_of_edgeperm (n - 1) (
    if edgeperm_idx n f k =? edgeperm_idx n f l then 
      pairmap (lshift 2 ∘ swap_to_0_1_perm k l (n * 2)) ∘ f 
      ∘ swap_from_0_perm (edgeperm_idx n f k) n
      ∘ rshift 1
    else
    (fun a => if a =? 0 then 
        (edgeperm_partner n f k, edgeperm_partner n f l)
      else 
        f (swap_from_0_1_perm (edgeperm_idx n f k) (edgeperm_idx n f l) n a) 
    )
  )).



Definition ZXvert_of_edge_list {n m} (G : ZX_el_graph n m) : ZX (n + m) 0 :=
  ZX_of_el_data n m G.(el_edges) G.(el_numspi) G.(el_deg)
  G.(el_color) G.(el_phase) G.(el_edgefunc) G.(el_size_pf).





Lemma ZX_of_edgeperm_data_defn n m numspi deg phase color edges sizepf edgefunc : 
  ZX_of_edgeperm_data n m numspi deg phase color edges sizepf edgefunc =
  
Proof. 
  unfold ZX_of_edgeperm_data.
  unfold ZX_of_infunc_data.
  unfold ZX_of_edgefunc.
  ZX_el_graph  
  reflexivity.

Lemma ZXvert_of_edge_list_definition 



ZX_of_infunc_data

ZXvert_of_edge_list

ZX_el_graph



(* TODO: These cases can (maybe?) be unified using [swap_to_front_perm k l n]
  which is [swap_to_0_perm k n] if [k = l] and [swap_to_0_1_perm k l n] 
  otherwise. This doesn't address the issue of where 
  to contract (0 1 vs 1 2), though. *)






Lemma compose_arb_cup_ZX_of_edgeperm_neq_base n k l f 
  (Hf : edgepermutation n f) (Hn : 1 < n)
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k < l)
  (Hf1 : infunc_of_edgefunc f 1 = k) (Hf2 : infunc_of_edgefunc f 2 = l) : 
  zx_arb_cup k l (n * 2) ⟷ ZX_of_edgeperm n f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r n 1 2)) eq_refl (
  ZX_of_edgeperm (n - 1) 
    (pairmap (fun k' => (if k' <? Init.Nat.min k l then k' + 2
    else if k' <? Init.Nat.max k l then k' + 1 else k') - 2) ∘ 
    (fun a => 
    if a =? 0 then (infunc_of_edgefunc f 0, infunc_of_edgefunc f 3)
    else f (a + 1)))).
Proof.
  unfold ZX_of_edgeperm.
  rewrite compose_arb_cup_ZX_of_infunc_neq_base by assumption.
  apply cast_simplify.
  ereflexivity.
  apply ZX_of_infunc_eq_of_perm_eq.
  rewrite perm_eq_split_times_2_iff.
  intros i Hi.
  replace_bool_lia (i * 2 =? 0) (i =? 0).
  replace_bool_lia (i * 2 + 1 =? 0) false.
  rewrite infunc_of_edgefunc_twice', infunc_of_edgefunc_twice_plus'.
  split.
  - cbv delta [compose] beta.
    bdestruct_one; cbn zeta.
    + simpl.
      rewrite infunc_of_edgefunc_twice'.
      subst i.
      reflexivity.
    + replace (i * 2 + 2) with ((i + 1) * 2) by lia.
      rewrite infunc_of_edgefunc_twice'.
      reflexivity.
  - cbv delta [compose] beta.
    bdestruct_one; cbn zeta.
    + subst.
      reflexivity.
    + replace (i * 2 + 1 + 2) with ((i + 1) * 2 + 1) by lia.
      rewrite infunc_of_edgefunc_twice_plus'.
      reflexivity.
Qed.

(* FIXME: Move *)
Lemma ltb_defn k l : 
  (k <? l) = (S k <=? l).
Proof. reflexivity. Qed.

Lemma compose_arb_cup_ZX_of_edgeperm_neq_base_gen' n k l f 
  (Hf : edgepermutation n f) (Hn : 1 < n)
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l)
  (Hf1 : infunc_of_edgefunc f 1 = k) (Hf2 : infunc_of_edgefunc f 2 = l) : 
  zx_arb_cup k l (n * 2) ⟷ ZX_of_edgeperm n f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r n 1 2)) eq_refl (
  ZX_of_edgeperm (n - 1) 
    (pairmap (fun k' => (if k' <? Init.Nat.min k l then k' + 2
    else if k' <? Init.Nat.max k l then k' + 1 else k') - 2) ∘ 
    (fun a => 
    if a =? 0 then (infunc_of_edgefunc f 0, infunc_of_edgefunc f 3)
    else f (a + 1)))).
Proof.
  unfold ZX_of_edgeperm.
  rewrite compose_arb_cup_ZX_of_infunc_neq_base_gen by assumption.
  apply cast_simplify.
  transitivity (
    ZX_of_infunc (n - 1)
    (infunc_of_edgefunc (pairmap
          (fun k' => (if k' <? Init.Nat.min k l
            then k' + 2 else if k' <? Init.Nat.max k l then k' + 1 else k') - 2)
        ∘ (fun a => if a =? 0
           then if k <? l then (infunc_of_edgefunc f 0, infunc_of_edgefunc f 3)
            else (infunc_of_edgefunc f 3, infunc_of_edgefunc f 0)
           else f (a + 1))))
  ).
  - ereflexivity.
    apply ZX_of_infunc_eq_of_perm_eq.
    rewrite perm_eq_split_times_2_iff.
    intros i Hi.
    replace_bool_lia (i * 2 =? 0) (i =? 0).
    replace_bool_lia (i * 2 + 1 =? 0) false.
    rewrite infunc_of_edgefunc_twice', infunc_of_edgefunc_twice_plus'.
    split.
    + bdestruct (i =? 0).
      * subst i.
        simpl.
        now bdestruct_one.
      * if_false_lia.
        replace (i * 2 + 2) with ((i + 1) * 2) by lia.
        cbn zeta.
        change ((?f ∘ ?g) ?x) with ((f ∘ (fun a=>a)) (g x)).
        cbv beta.
        symmetry.
        if_false_lia.
        simpl.
        rewrite infunc_of_edgefunc_twice'.
        reflexivity.
    + change ((?f ∘ ?g) ?x) with ((f ∘ (fun a=>a)) (g x)).
      cbv beta.
      bdestruct (i =? 0).
      * subst i.
        simpl.
        now bdestruct_one.
      * if_false_lia.
        replace (i * 2 + 1 + 2) with ((i + 1) * 2 + 1) by lia.
        cbn zeta.
        simpl.
        rewrite infunc_of_edgefunc_twice_plus'.
        reflexivity.
  - symmetry. 
    apply ZX_of_edgeperm_perm_edge_eq_simplify.
  1: {
    unfold edgepermutation.
    replace ((n - 1) * 2) with (n * 2 - 2) by lia.
    apply (permutation_perm_eq_proper _ (contract_biperm 1 2 (infunc_of_edgefunc f)));
    [|now auto_perm].
    intros a Ha.
    unfold contract_biperm.
    if_true_lia.
    rewrite infunc_of_edgefunc_compose_pairmap_l.
    pose proof (Hf1 : snd (f 0) = k) as Hf1'.
    pose proof (Hf2 : fst (f 1) = l) as Hf2'.
    change ((?f ∘ ?g) ?x) with ((f ∘ (fun a=>a)) (g x)).
    assert (Hval21 : contract_perm (infunc_of_edgefunc f) 2 1 = if k <? l then k else k - 1). 1: {
      cbn.
      rewrite Hf1', Hf2'.
      reflexivity.
    }
    bdestruct (a <? 2).
    - unfold infunc_of_edgefunc at 2.
      assert (a / 2 = 0) by (rewrite Nat.div_small_iff; lia).
      if_true_lia.
      bdestruct (a =? 0).
      + subst a.
        cbn.
        rewrite Hf1', Hf2'.
        rewrite <- !ltb_defn.
        unfold compose.
        rewrite min_ltb, max_ltb.
        bdestructΩ'.
      + replace a with 1 in * by lia.
        cbn.
        rewrite Hf1', Hf2'.
        rewrite <- !ltb_defn.
        unfold compose.
        rewrite min_ltb, max_ltb.
        bdestructΩ'.
    - unfold infunc_of_edgefunc at 2.
      assert (~ (a / 2 = 0)) by (rewrite Nat.div_small_iff; lia).
      if_false_lia.
      unfold contract_perm at 1.
      if_false_lia.
      rewrite Hval21.
      unfold contract_perm at 1.
      replace_bool_lia (a + 1 <? 2) false.
      assert (Hval11 : infunc_of_edgefunc f (a + 1 + 1) = 
        edge_to_func (f (a/2 + 1)) (a mod 2)). 1: {
        replace (a + 1 + 1) with (a + 1 * 2) by lia.
        unfold infunc_of_edgefunc.
        rewrite Nat.div_add, Nat.Div0.mod_add; lia.
      }
      rewrite Hval11, Hf2.
      replace (contract_perm (infunc_of_edgefunc f) 2 (a + 1)) with 
        (if edge_to_func (f (a / 2 + 1)) (a mod 2) <? l
        then edge_to_func (f (a / 2 + 1)) (a mod 2)
        else edge_to_func (f (a / 2 + 1)) (a mod 2) - 1). 2:{
        unfold contract_perm.
        symmetry.
        if_false_lia.
        rewrite Hval11, Hf2.
        reflexivity.
      }
      unfold compose.
      rewrite min_ltb, max_ltb.
      bdestructΩ'.
  }
    + intros a Ha.
      unfold compose.
      bdestruct (a =? 0).
      * apply pairmap_edge_eq_mor.
        bdestruct_one; easy + apply edge_eq_swap.
      * reflexivity.
Qed.

Lemma compose_arb_cup_ZX_of_edgeperm_neq_base_gen n k l f 
  (Hf : edgepermutation n f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l)
  (Hf0 : edgeperm_idx n f k = 0) (Hf1 : edgeperm_idx n f l = 1) : 
  zx_arb_cup k l (n * 2) ⟷ ZX_of_edgeperm n f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r n 1 2)) eq_refl (
  ZX_of_edgeperm (n - 1) 
    (pairmap (fun k' => (if k' <? Init.Nat.min k l then k' + 2
    else if k' <? Init.Nat.max k l then k' + 1 else k') - 2) ∘ 
    (fun a => 
    if a =? 0 then (edgeperm_partner n f k, edgeperm_partner n f l)
    else f (a + 1)))).
Proof.
  rewrite <- (ZX_of_edgeperm_absorb_swaps n f
    (fun ij => 
    if edge_mem k ij then 
      if snd ij =? k then ij else (snd ij, fst ij)
    else 
    if edge_mem l ij then 
      if fst ij =? l then ij else (snd ij, fst ij)
    else ij) Hf).
  2: {
    intros i Hi.
    unfold compose, edge_mem.
    rewrite 2!orb_if.
    bdestruct_all; hnf; simpl; lia.
  }
  assert (Hn : 1 < n) by (pose proof (edgeperm_idx_bounded n f l); lia).
  rewrite compose_arb_cup_ZX_of_edgeperm_neq_base_gen';
  [| | auto.. | |].
  - apply cast_simplify.
    unfold ZX_of_edgeperm.
    ereflexivity.
    apply ZX_of_infunc_eq_of_perm_eq.

    rewrite 2!((fun a (Ha : a < (n-1)*2) => infunc_of_edgefunc_compose_pairmap_l _ _ a)
      : perm_eq _ _ _).
    apply compose_perm_eq_proper_r.
    apply infunc_of_edgefunc_perm_eq_proper.
    intros a Ha.
    bdestruct (a =? 0).
    + unfold compose. 
      cbn.
      rewrite 4!(edge_mem_iff_edgeperm_idx_eqb _ _ _ _ Hf) by lia.
      if_true_lia.
      f_equal.
      * unfold edgeperm_partner.
        rewrite Hf0.
        unfold edge_partner.
        rewrite edgeperm_idx_eq_iff_fst_or_snd in Hf0 by auto_perm.
        bdestructΩ'.
      * if_false_lia; if_true_lia.
        unfold edgeperm_partner.
        rewrite Hf1.
        unfold edge_partner.
        rewrite edgeperm_idx_eq_iff_fst_or_snd in Hf1 by auto_perm.
        bdestructΩ'.
    + unfold compose.
      rewrite 2!(edge_mem_iff_edgeperm_idx_eqb _ _ _ _ Hf) by lia.
      if_false_lia.
      if_false_lia.
      reflexivity.
  - eapply edgepermutation_perm_edge_eq_iff; [|apply Hf].
    intros a Ha.
    unfold compose.
    rewrite 2!(edge_mem_iff_edgeperm_idx_eqb _ _ _ _ Hf) by lia.
    bdestruct_all;
    reflexivity + 
    apply edge_eq_swap.
  - unfold compose.
    cbn.
    rewrite (edge_mem_iff_edgeperm_idx_eqb _ _ _ _ Hf) by lia.
    if_true_lia.
    rewrite edgeperm_idx_eq_iff_fst_or_snd in Hf0 by auto_perm.
    rewrite if_dist.
    simpl. 
    bdestructΩ'.
  - unfold compose.
    cbn.
    rewrite 2!(edge_mem_iff_edgeperm_idx_eqb _ _ _ _ Hf) by lia.
    if_false_lia; if_true_lia.
    rewrite edgeperm_idx_eq_iff_fst_or_snd in Hf1 by auto_perm.
    rewrite if_dist.
    simpl.
    bdestructΩ'.
Qed.

Lemma contract_biperm_defn k l f n 
  (Hfkl : f k <> f l) : 
  perm_eq n (contract_biperm k l f) 
  ((fun fa => if fa <? min (f k) (f l) then fa else
    if fa <? max (f k) (f l) then fa - 1 else fa - 2) 
    ∘ f ∘ (fun a => if a <? min k l then a else 
    if a <? max k l then a + 1 else a + 2)).
Proof.
  assert (Hor : k < l \/ l < k) by ((assert (k <> l) by now intros ->); lia).
  by_symmetry Hor. 2:{
    intros a b IH Hab.
    rewrite contract_biperm_comm.
    rewrite Nat.min_comm, Nat.max_comm, (Nat.min_comm b), (Nat.max_comm b).
    now apply IH.
  }
  assert (Hor' : f k < f l \/ f l < f k) by lia.
  by_symmetry Hor'. 2:{
    intros a b IH Hab.
    rewrite contract_biperm_comm.
    rewrite Nat.min_comm, Nat.max_comm, (Nat.min_comm b), (Nat.max_comm b).
    now apply IH.
  }
  rewrite (Nat.min_l)
  unfold contract_biperm_to_min_max

Lemma compose_arb_cup_edgeperm_gen_edge_eq_edgepermutation n k l f 
  (Hf : edgepermutation n f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l)
  (Hf01 : edge_eq (edgeperm_idx n f k, edgeperm_idx n f l) (0, 1)) : 
  edgepermutation (n - 1)
    (pairmap (fun k' => (if k' <? Init.Nat.min k l then k' + 2
    else if k' <? Init.Nat.max k l then k' + 1 else k') - 2) ∘ 
    (fun a => 
    if a =? 0 then (edgeperm_partner n f k, edgeperm_partner n f l)
    else f (a + 1))).
Proof.
  apply (edgepermutation_perm_edge_eq_iff n (edgefunc_of_infunc (contract_biperm ))

  assert (Hn : 1 < n) by (pose proof (edgeperm_idx_bounded n f k); 
    pose proof (edgeperm_idx_bounded n f l); hnf in Hf01; simpl in Hf01; lia).
  
  unfold edgepermutation.
  replace ((n - 1) * 2) with (n * 2 - 2) by lia.
  rewrite infunc_of_edgefunc_compose_pairmap_l_perm_eq.
  apply permutation_iff_surjective.
  apply surjective_of_injective_and_bounded.
  split.
  - assert (Haux: forall a b, 
    a <> k -> a <> l -> b <> k -> b <> l ->
    (fun k' => (if k' <? Init.Nat.min k l then k' + 2 else 
    if k' <? Init.Nat.max k l then k' + 1 else k') - 2) a =
    (fun k' => (if k' <? Init.Nat.min k l then k' + 2 else 
    if k' <? Init.Nat.max k l then k' + 1 else k') - 2) b -> 
    a = b). 1:{ 
      intros a b Hak Hal Hbk Hbl.
      bdestructΩ'.
    }
    intros a b Ha Hb Hab.
    apply Haux in Hab; clear Haux.
    + 

  intros a Ha.
  
  apply (permutation_perm_eq_proper _ (contract_biperm 
    (perm_inv (n * 2) (infunc_of_edgefunc f) k) 
    (perm_inv (n * 2) (infunc_of_edgefunc f) l) 
    (infunc_of_edgefunc f)));
  [|apply contract_biperm_permutation; unfold edgepermutation in Hf; auto_perm;
    apply (permutation_neq (n:=(n*2))); auto_perm].
  (* rewrite contract_biperm_to_min_max. *)
  intros a Ha.
  rewrite infunc_of_edgefunc_compose_pairmap_l.
  unfold contract_biperm.
  bdestruct_one.
  - 
  (* pose proof (Hf1 : snd (f 0) = k) as Hf1'.
  pose proof (Hf2 : fst (f 1) = l) as Hf2'. *)
  change ((?f ∘ ?g) ?x) with ((f ∘ (fun a=>a)) (g x)).
  unfold contract_perm at 1.
  assert (Hval_lk : 
    contract_perm (infunc_of_edgefunc f)
     (perm_inv (n * 2) (infunc_of_edgefunc f) l)
     (perm_inv (n * 2) (infunc_of_edgefunc f) k) = 
     if k <? l then k else k - 1). 1:{
    unfold contract_perm.
    if_true_lia.
    now rewrite !perm_inv_is_rinv_of_permutation by auto.
  }
  rewrite Hval_lk.
  assert (Hfinvk: perm_inv (n * 2) (infunc_of_edgefunc f) k < 2) by admit. (* This is true *)
  bdestruct (a <? 2).
  + bdestruct (a =? 0).
    * subst a.
      cbn.
  contract_perm
  assert (Hval21 : contract_perm (infunc_of_edgefunc f) 2 1 = if k <? l then k else k - 1). 1: {
    cbn.
    rewrite Hf1', Hf2'.
    reflexivity.
  }
  bdestruct (a <? 2).
  - unfold infunc_of_edgefunc at 2.
    assert (a / 2 = 0) by (rewrite Nat.div_small_iff; lia).
    if_true_lia.
    bdestruct (a =? 0).
    + subst a.
      cbn.
      rewrite Hf1', Hf2'.
      rewrite <- !ltb_defn.
      unfold compose.
      rewrite min_ltb, max_ltb.
      bdestructΩ'.
    + replace a with 1 in * by lia.
      cbn.
      rewrite Hf1', Hf2'.
      rewrite <- !ltb_defn.
      unfold compose.
      rewrite min_ltb, max_ltb.
      bdestructΩ'.
  - unfold infunc_of_edgefunc at 2.
    assert (~ (a / 2 = 0)) by (rewrite Nat.div_small_iff; lia).
    if_false_lia.
    unfold contract_perm at 1.
    if_false_lia.
    rewrite Hval21.
    unfold contract_perm at 1.
    replace_bool_lia (a + 1 <? 2) false.
    assert (Hval11 : infunc_of_edgefunc f (a + 1 + 1) = 
      edge_to_func (f (a/2 + 1)) (a mod 2)). 1: {
      replace (a + 1 + 1) with (a + 1 * 2) by lia.
      unfold infunc_of_edgefunc.
      rewrite Nat.div_add, Nat.Div0.mod_add; lia.
    }
    rewrite Hval11, Hf2.
    replace (contract_perm (infunc_of_edgefunc f) 2 (a + 1)) with 
      (if edge_to_func (f (a / 2 + 1)) (a mod 2) <? l
      then edge_to_func (f (a / 2 + 1)) (a mod 2)
      else edge_to_func (f (a / 2 + 1)) (a mod 2) - 1). 2:{
      unfold contract_perm.
      symmetry.
      if_false_lia.
      rewrite Hval11, Hf2.
      reflexivity.
    }
    unfold compose.
    rewrite min_ltb, max_ltb.
    bdestructΩ'.
  

Lemma compose_arb_cup_ZX_of_edgeperm_neq_base_gen_edge_eq n k l f 
  (Hf : edgepermutation n f) 
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l)
  (Hf01 : edge_eq (edgeperm_idx n f k, edgeperm_idx n f l) (0, 1)) : 
  zx_arb_cup k l (n * 2) ⟷ ZX_of_edgeperm n f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r n 1 2)) eq_refl (
  ZX_of_edgeperm (n - 1) 
    (pairmap (fun k' => (if k' <? Init.Nat.min k l then k' + 2
    else if k' <? Init.Nat.max k l then k' + 1 else k') - 2) ∘ 
    (fun a => 
    if a =? 0 then (edgeperm_partner n f k, edgeperm_partner n f l)
    else f (a + 1)))).
Proof.
  destruct Hf01 as [[Hf0 Hf1] | [Hf1 Hf0]];
  simpl in Hf0, Hf1;
  [now apply compose_arb_cup_ZX_of_edgeperm_neq_base_gen|].
  assert (Hn : 1 < n) by (pose proof (edgeperm_idx_bounded n f k); lia).
  pose proof (permutation_of_le_permutation_WF swap_2_perm 2 n
    ltac:(lia) ltac:(auto_perm) ltac:(auto_perm)) as Hpadswap.
  rewrite <- (ZX_of_edgeperm_absorb_perm_r n f _ Hf Hpadswap).
  rewrite zx_arb_cup_comm.
  rewrite compose_arb_cup_ZX_of_edgeperm_neq_base_gen;
  [|auto_perm..| |].
  - apply cast_simplify.
    ereflexivity.
    apply ZX_of_infunc_eq_of_perm_eq.
    rewrite 2!((fun a (Ha : a < (n-1)*2) => 
      infunc_of_edgefunc_compose_pairmap_l _ _ a) : perm_eq _ _ _).
    rewrite Nat.min_comm, Nat.max_comm.
    apply compose_perm_eq_proper_r.
    apply infunc_of_edgefunc_perm_eq_proper.
    intros a Ha.
    bdestruct_one.
    + rewrite 2!edgeperm_partner_compose_r by easy.
      apply 

    apply ZX_of_edgefunc_prop_of_perm_edge_eq.


Definition normalizer_rperm n (f : nat -> nat * nat) k l : nat -> nat :=
  if edgeperm_idx n f k =? edgeperm_idx n f l then
    swap_perm 0 (edgeperm_idx n f k) n
  else 
    swap_from_0_1_perm (edgeperm_idx n f k) (edgeperm_idx n f l) n.

Lemma normalizer_rperm_permutation n k l f 
  (Hf : edgepermutation n f) (Hk : k < n * 2) (Hl : l < n * 2) :
  permutation n (normalizer_rperm n f k l ).
Proof.
  unfold normalizer_rperm.
  bdestruct_one; auto_perm.
Qed.

#[export] Hint Resolve normalizer_rperm_permutation : perm_db.



Lemma edgeperm_of_compose_normalizer_r_spec_eq n f k l 
  (Hf : edgepermutation n f) (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) :
  edgeperm_idx n f k = edgeperm_idx n f l ->
  edge_eq ((f ∘ normalizer_rperm n f k l) 0) (k, l).
Proof.
  intros Heq.
  unfold normalizer_rperm.
  rewrite Heq, Nat.eqb_refl.
  unfold compose.
  rewrite swap_perm_left by lia.
  rewrite edgeperm_idx_rinv_edge_eq by auto.
  rewrite edge_eq_swap.
  apply edge_eq_of_parts; [simpl|easy].
  apply edgeperm_partner_eq_iff_edgeperm_idx_eq; easy.
Qed.

Lemma edgeperm_of_compose_normalizer_r_spec_neq n f k l 
  (Hf : edgepermutation n f) (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) :
  edgeperm_idx n f k < edgeperm_idx n f l ->
  edgeperm_idx n (f ∘ normalizer_rperm n f k l) k = 0 /\
  edgeperm_idx n (f ∘ normalizer_rperm n f k l) l = 1.
Proof.
  intros Hlt.
  unfold normalizer_rperm.
  if_false_lia.
  pose proof Hlt as Hneq%Nat.lt_neq.
  rewrite 2!edgeperm_idx_compose_r by auto_perm.
  unfold compose.
  rewrite 2!swap_from_0_1_perm_inv by auto_perm.
  rewrite 2!swap_to_0_1_perm_defn by auto_perm.
  rewrite min_l, max_r by lia.
  rewrite !Nat.eqb_refl.
  now if_false_lia.
Qed.

Lemma edgeperm_of_compose_normalizer_r_spec_neq_gen n f k l 
  (Hf : edgepermutation n f) (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k <> l) :
  edgeperm_idx n f k <> edgeperm_idx n f l ->
  edge_eq (edgeperm_idx n (f ∘ normalizer_rperm n f k l) k,
    edgeperm_idx n (f ∘ normalizer_rperm n f k l) l)
    (0, 1).
Proof.
  intros Hlt.
  unfold normalizer_rperm.
  if_false_lia.
  rewrite 2!edgeperm_idx_compose_r by auto_perm.
  unfold compose.
  rewrite 2!swap_from_0_1_perm_inv by auto_perm.
  rewrite 2!swap_to_0_1_perm_defn by auto_perm.
  rewrite min_ltb, max_ltb.
  bdestructΩ'; reflexivity + apply edge_eq_swap.
Qed.





Lemma compose_arb_cup_ZX_of_infunc_base edges f
  (Hedges : 1 < edges) (Hf : permutation (edges * 2) f) 
  (Hf0 : f 1 = 0) (Hf1 : f 2 = 1) : 
  zx_arb_cup 0 1 (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl (
  ZX_of_infunc (edges - 1)
  (fun k => if k =? 0 then f k - 2 else f (k + 2) - 2)).




Lemma compose_arb_cup_ZX_of_edgeperm_neq_base_alt n k l f 
  (Hf : edgepermutation n f) (Hn : 1 < n)
  (Hk : k < n * 2) (Hl : l < n * 2) (Hkl : k < l)
  kin lin (Hkin : kin < n * 2) (Hlin : lin < n * 2) 

  (Hf1 : infunc_of_edgefunc f 1 = k) (Hf2 : infunc_of_edgefunc f 2 = l) : 
  zx_arb_cup k l (n * 2) ⟷ ZX_of_edgeperm n f ∝ 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r n 1 2)) eq_refl (
  ZX_of_edgeperm (n - 1) 
    (pairmap (fun k' => (if k' <? Init.Nat.min k l then k' + 2
    else if k' <? Init.Nat.max k l then k' + 1 else k') - 2) ∘ 
    (fun a => 
    if a =? 0 then (infunc_of_edgefunc f 0, infunc_of_edgefunc f 3)
    else f (a + 1)))).

Definition ZX_of_edgeperm


Definition edge_to_norm_perm n f k l :=
  if perm_inv (n * 2) f k =?
  Search "pull" "perm".


Lemma compose_arb_cup_ZX_of_infunc edges f
  k l (Hk : k < edges * 2) (Hl : l < edges * 2) (Hkl : k <> l)  
  (Hf : permutation (edges * 2) f) : 
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_infunc edges f ∝ 
  if perm_inv (edges * 2) f k / 2 =? perm_inv (edges * 2) f l / 2 then
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl 
  (ZX_of_infunc (edges - 1) 
    (contract_biperm (perm_inv (edges * 2) f k) (perm_inv (edges * 2) f l) f))
  else
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl 
  (ZX_of_infunc (edges - 1) (
    fun a => 
    if a =? 0 then min k l else if a =? 1 then max k l else 
    let a' := a - 2 in 
    let f'k := perm_inv (edges * 2) f k / 2 in 
    let f'l := perm_inv (edges * 2) f l / 2 in 
    let ain := if a' / 2 <? min f'k f'l then a' 
      else if a' / 2 <? max f'k f'l - 1 then a' + 2 else a' + 4 in
    if f ain <? min k l then f ain else 
    if f ain <? max k l - 1 then f ain - 1 else f ain - 2
  ))
  (* @cast (edges * 2 - 2) 0 (edges * 2 - 2) (edges * 0) eq_refl 
    (eq_sym (Nat.mul_0_r edges))
    (zx_of_perm (edges * 2 - 2)
      (contract_biperm (perm_inv (edges * 2) f k) (perm_inv (edges * 2) f l) f)
    ⟷ (
       zx_arb_cap (2 * (Init.Nat.min (perm_inv (edges * 2) f k) (perm_inv (edges * 2) f l) / 2))
         (2 * (Init.Nat.max (perm_inv (edges * 2) f k) (perm_inv (edges * 2) f l) / 2) - 1)
         (edges * 2 - 2)
       ⟷ @cast (edges * 2 - 2 - 2) (edges * 0) ((edges - 2) * 2) ((edges - 2) * 0)
           comp_zx_cap_n_stack_prf mul_0_r_eq ((edges - 2) ⇑ ⊃))) *)
           
           .
Proof.
  cbv delta [ZX_of_infunc] beta.
  rewrite cast_compose_r_eq_mid.
  rewrite <- compose_assoc.
  rewrite zx_arb_cup_compose_zx_of_perm_r by auto_perm.
  rewrite compose_assoc.
  rewrite compose_arb_cup_n_stack_caps by 
    (try apply (@permutation_neq (edges * 2)); auto_perm).
  bdestruct_one.
  - rewrite cast_contract_eq.
    rewrite cast_compose_distribute_r_eq_mid.
    rewrite cast_compose_distribute, cast_zx_of_perm_natural_l.
    rewrite cast_compose_l.
    rewrite cast_compose_distribute_r_eq_mid.
    apply compose_simplify_r.
    rewrite 3!cast_contract_eq.
    cast_irrelevance.
  - rewrite cast_backwards_fwd.
    cbv delta [zx_arb_cap] beta.
    rewrite <- 2!compose_assoc, compose_assoc.
    rewrite 2!cast_contract_eq.
    rewrite cast_compose_distribute.
    assert (2 < edges * 2). 1:{
      apply (diff_divs_lower_bound 
        (perm_inv (edges * 2) f k) (perm_inv (edges * 2) f l)); [auto_perm..|].
      assumption.
    }
    assert (permutation (edges * 2 - 2) (swap_from_0_1_perm 
      (2 * (min (perm_inv (edges * 2) f k) (perm_inv (edges * 2) f l) / 2))
      (2 * (max (perm_inv (edges * 2) f k) (perm_inv (edges * 2) f l) / 2) - 1)
      (edges * 2 - 2))). 1: {
      set (finv := perm_inv (edges * 2) f) in *.
      assert (finv k / 2 < edges /\ finv l / 2 < edges) by 
        (split; apply Nat.Div0.div_lt_upper_bound;
        rewrite Nat.mul_comm;
        subst finv; auto_perm).
      apply swap_from_0_1_perm_permutation.
      - apply Nat.lt_le_trans with (2 * (edges - 1)); [|lia].
        apply Nat.mul_lt_mono_pos_l; [lia|].
        rewrite min_div.
        lia.
      - unfold lt.
        rewrite max_div.  
        rewrite <- Nat.add_1_l.
        rewrite Nat.add_sub_assoc, add_sub' by lia.
        apply Nat.le_trans with (2 * (edges - 1)); [|lia].
        apply Nat.mul_le_mono_pos_l; [lia|].
        lia.
      - rewrite min_div, max_div.
        intros Heq.
        apply (f_equal (fun x => x mod 2)) in Heq.
        revert Heq.
        rewrite 2!(Nat.mul_comm 2).
        rewrite Nat.Div0.mod_mul.
        rewrite mod_mul_sub_le; [cbn..|]; lia.
    }
    rewrite compose_zx_of_perm; [|auto_perm..].
    apply (cast_diagrams _ 0 (Nat.mul_sub_distr_r edges 1 2)
      (eq_sym (Nat.mul_0_r edges))).
    etransitivity; [|etransitivity; [|symmetry]; cycle 1];
    [instantiate (1:=ZX_of_infunc (edges - 1) _)..|].
    1: {
      cbv delta [ZX_of_infunc] beta.
      rewrite cast_backwards_fwd.
      rewrite cast_contract_eq.
      rewrite cast_compose_distribute.
      apply compose_simplify_casted_abs; [lia|..]; intros ?.
      - rewrite cast_contract_eq, cast_zx_of_perm.
        reflexivity.
      - unfold zx_padded_cap.
        assert (Hle : 2 <= edges * 2 - 2) by lia.
        rewrite (le_lt_dec_le Hle).
        rewrite cast_compose_l_eq_mid.
        rewrite <- pull_out_top.
        rewrite cast_stack_r_fwd.
        change (⊃ ↕ (edges - 2) ⇑ ⊃) with ((S (edges - 2)) ⇑ ⊃).
        rewrite 2!cast_contract_eq.
        apply ZX_prop_by_mat_prop.
        simpl_cast_semantics.
        assert (Hrw : S (edges - 2) = edges - 1) by lia.
        rewrite n_stack_semantics.
        rewrite <- Hrw.
        restore_dims.
        rewrite <- n_stack_semantics.
        reflexivity.
    }
    1: {
      cbv delta [ZX_of_infunc] beta.
      rewrite cast_backwards_fwd.
      rewrite cast_contract_eq.
      rewrite cast_compose_distribute.
      apply compose_simplify_casted_abs; [lia|..]; intros ?.
      - rewrite cast_backwards_fwd, 2!cast_contract_eq, cast_zx_of_perm.
        reflexivity.
      - rewrite cast_contract_eq.
        cast_irrelevance.
    }
    apply ZX_of_infunc_edgeperm_eq_simplify.
    1: {
      rewrite Nat.mul_sub_distr_r.
      apply permutation_compose; [auto_perm|assumption].
    }
    intros a Ha.
    bdestruct (a =? 0).
    + subst.
      if_true_lia; if_false_lia; if_true_lia.
      unfold compose.
      unfold swap_from_0_1_perm.
      if_false_lia.
      rewrite !(Nat.mul_comm 2 _).
      cbn [Nat.eqb Nat.mul Nat.add].
      if_false_lia.
      rewrite !(Nat.mul_comm _ 2), (Nat.mul_comm 2 edges).
      rewrite min_div, max_div.
      rewrite min_l, max_r by lia.
      Import Init.Nat.
      (* set (f'k := perm_inv (edges * 2) f k) in *.
      set (f'l := perm_inv (edges * 2) f l) in *. *)
      assert (Hf'kl : perm_inv (edges * 2) f k <> 
        perm_inv (edges * 2) f l) by (intros Hrw; rewrite Hrw in *; lia).
      assert (Hor : perm_inv (edges * 2) f k < perm_inv (edges * 2) f l 
        \/ perm_inv (edges * 2) f l < perm_inv (edges * 2) f k) by lia.
      
      (* by_symmetry Hor by (
        intros a b Hab ? Hab' **;
        rewrite contract_biperm_comm, Nat.min_comm, Nat.max_comm;
        rewrite Nat.min_comm, Nat.max_comm in Hab';
        auto). *)
      
      set (f'k := perm_inv (edges * 2) f k) in *.
      set (f'l := perm_inv (edges * 2) f l) in *.
      (* assert (Hf'kl : f'k <> f'l) by (intros ->; lia).
      assert (Hor : f'k < f'l \/ f'l < f'k) by lia. *)
      (* by_symmetry Hor by (
        intros a b Hab ? Hab' **;
        rewrite contract_biperm_comm, Nat.min_comm, Nat.max_comm;
        rewrite Nat.min_comm, Nat.max_comm in Hab';
        auto). *)
      assert (Hff's : edge_eq (f f'k, f f'l) (k, l)) by 
        (left; split; subst f'k f'l; 
        apply perm_inv_is_rinv_of_permutation; auto_perm).
      rewrite <- min_div, <- max_div.
      by_symmetry Hor. 2: {
        intros ? ? Hab **.
        rewrite Nat.max_comm, Nat.min_comm, contract_biperm_comm.
        apply Hab; [easy|now rewrite Nat.min_comm, Nat.max_comm|easy|].
        rewrite <- Hff's.
        apply edge_eq_swap.
      }
      transitivity (k, l).
      2: {
        bdestruct (k <? l); 
        [rewrite min_l, max_r by lia; reflexivity|
         rewrite min_r, max_l by lia; apply edge_eq_swap].
      }
      rewrite <- Hff's.
      left; cbn [fst snd].
      unfold contract_biperm.
      if_true_lia.
      rewrite min_l, max_r by lia.
      split.
      * (* assert (edges = 5) by admit.
        assert (f = nth_default 0 [1;3;2;4;0]) by admit.
        assert (k = 2) by admit.
        assert (l = 3) by admit.
        assert (f'k = )
        subst.
        lazy *)
        
        unfold contract_perm at 1.
        replace (contract_perm f f'l f'k) 
          with (if f f'k <? f f'l then f f'k else f f'k - 1). 2:{
          unfold contract_perm.
          symmetry.
          if_true_lia.
          reflexivity.
        }
        bdestruct_one.
        1: {
          assert (f'k mod 2 = 1) by (
            assert (f'k mod 2 < 2) by (clear; dmlia);
            pose proof (Nat.div_mod_eq f'k 2); lia).
          replace (contract_perm f f'l (2 * (f'k / 2)))
            with 0. 2:{
            unfold contract_perm.
            symmetry.
            pose proof (Nat.div_mod_eq f'k 2).

            if_true_lia.
            reflexivity.
          }
          
        }
      (* assert (Hff'k : f f'k = k) by (subst f'k; 
        apply perm_inv_is_rinv_of_permutation; auto_perm).
      assert (Hff'l : f f'l = l) by (subst f'l; 
        apply perm_inv_is_rinv_of_permutation; auto_perm). *)
      rewrite contract_biperm_to_min_max.
      by_symmetry Hor. 2: {
        intros ? ? Hab **.
        rewrite Nat.max_comm, Nat.min_comm.
        apply Hab.
      }
      etransitivity;
      [instantiate (1:=(_,_)); left; cbn [fst snd]; split|].
      * unfold contract_perm at 1.
        replace (contract_perm f (max f'k f'l) (min f'k f'l)) with k. 2:{
          unfold contract_perm.
          if_true_lia.
        }


      assert (Hor : k < l \/ l < k) by lia.
      by_symmetry Hor by 
        (intros a b Hab **;
        rewrite contract_biperm_comm, Nat.min_comm, 
          (Nat.min_comm b a);
        auto).
    
    auto_cast_eqn eapply compose_simplify_casted; cycle 1.
    + 
    + 
      rewrite cast_contract_eq, cast_zx_of_perm.
      ereflexivity.
      apply zx_of_perm_eq_of_perm_eq.
      intros a Ha.
      assert (Ha2 : a / 2 < edges - 1) by (clear -Ha; dmlia).
      bdestruct (a =? 0); [|bdestruct (a =? 1)].
      * unfold compose.
        subst a.
        unfold swap_from_0_1_perm.
        if_false_lia.
        cbn [Nat.eqb].
        Import Init.Nat.
        rewrite min_div, max_div.
        rewrite min_l by lia.
        rewrite <- min_div.
        assert (Hor : k < l \/ l < k) by lia.
        by_symmetry Hor by 
          (intros a b Hab **;
          rewrite contract_biperm_comm, Nat.min_comm, 
            (Nat.min_comm b a);
          auto).
        


        rewrite contract_biperm_to_min_max.






    

  set (cast' := @cast).








Definition edgeperm_idx n (f : nat -> nat * nat) k :=
  perm_inv (n * 2) (infunc_of_edgefunc f) k / 2.

Lemma compose_arb_cup_ZX_of_edgeperm edges f
  k l (Hk : k < edges * 2) (Hl : l < edges * 2) (Hkl : k <> l)  
  (Hf : permutation (edges * 2) (infunc_of_edgefunc f)) : 
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_edgeperm edges f ∝ 
  if edgeperm_idx edges f k =? edgeperm_idx edges f l then
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl 
    (ZX_of_edgeperm (edges - 1)
    (fun i => f (if i <? edgeperm_idx edges f k then i else i + 1)))
  else 
  cast _ _ (eq_sym (Nat.mul_sub_distr_r edges 1 2)) eq_refl 
  (ZX_of_edgeperm (edges - 1)
    (fun i => 
    if i =? 0 then (k, l) else 
    f (if i <? min (edgeperm_idx edges f k) (edgeperm_idx edges f l) 
      then i else 
      if i <? max (edgeperm_idx edges f k) (edgeperm_idx edges f l) - 1
      then i + 1 else i + 2))).
Proof.



  


Lemma compose_arb_cup_ZX_of_edgeperm edges f
  k l (Hk : k < edges * 2) (Hl : l < edges * 2) (Hkl : k <> l) K : 
  zx_arb_cup k l (edges * 2) ⟷ 
  ZX_of_infunc_data n m numspi deg phase color 
    edges size_pf (infunc_of_edgefunc f) ∝ K.























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
  f ∘ tensor_perms edges 2 
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



*)
