Require Import ZXCore.
Require Import QuantumLib.Permutations.

Require Import StackComposeRules.
Require Import CastRules.

Local Open Scope nat.
Local Open Scope prg.

Open Scope ZX_scope.

Ltac bdest_lia_replace b0 b1 :=
  replace b0 with b1 by (bdestruct b0; lia).

Ltac show_permutation :=
  repeat first [
    split
  | simpl; solve [auto with perm_db]
  | subst; solve [auto with perm_db]
  | auto with perm_db
  | solve [eauto using permutation_compose with perm_db]
  | easy
  | lia
  ].

Ltac enumerate_value i :=
  destruct i; [|tryif lia then idtac else enumerate_value i].

Ltac enumerate_matrix Hi Hj :=
  match type of Hi with (?i < ?n) =>
  match type of Hj with (?j < ?m) => 
  enumerate_value i; enumerate_value j
  (* repeat first [destruct i; destruct j; try lia] *)
  end end.

Ltac check_finite_matrix :=
  apply mat_equiv_eq;
  try auto with wf_db;
  intros i j Hi Hj; simpl in *;
  enumerate_matrix Hi Hj;
  try lia;
  try easy.

Ltac tryeasylia :=
  try easy; try lia. 

Ltac bdestshoweq := (* goal of form b0 = b1, bools *)
	match goal with 
	| |- ?b0 = ?b1 =>
		bdestruct b0; bdestruct b1; auto; try easy; lia
	end.

Ltac destruct_if :=
  match goal with
  | |- (if ?b then _ else _)     => bdestruct b
  | |- (if ?b then _ else _) = _ => bdestruct b
  | |- _ = (if ?b then _ else _) => bdestruct b
  | |- _ (if ?b then _ else _) _ => bdestruct b
  | |- _ _ (if ?b then _ else _) => bdestruct b
  end.

Ltac destruct_if_solve :=
  repeat (destruct_if; tryeasylia);
  tryeasylia.

Ltac solve_stack_perm n0 n1 :=
  unfold stack_permutations;
  apply functional_extensionality; intros k;
  bdestruct (k <? n0); [tryeasylia|];
  try bdestruct (k <? n0 + n1); tryeasylia.
  
Ltac solve_stack_perm_strong n0 n1 :=
  unfold stack_permutations; 
  apply functional_extensionality; intros k;
  bdestruct (k <? n0); [tryeasylia | ]; try bdestruct (k <? n0 + n1);
  destruct_if_solve.

Ltac apply_f H k :=
  unfold compose in H;
  apply (f_equal (fun x => x k)) in H.

Lemma is_inv_iff_inv_is n f finv :
  (forall k, k < n -> finv k < n /\ f k < n /\ f (finv k) = k /\ finv (f k) = k)
  <-> (forall k, k < n -> f k < n /\ finv k < n /\ finv (f k) = k /\ f (finv k) = k).
Proof.
  split; intros H k Hk; specialize (H k Hk); easy.
Qed.

#[export] Hint Rewrite is_inv_iff_inv_is : perm_inv_db.

Tactic Notation "cleanup_perm_inv" := 
  auto_cast_eqn (autorewrite with perm_inv_db).

Tactic Notation "cleanup_perm" :=
  auto_cast_eqn (autorewrite with perm_inv_db perm_cleanup_db).

Tactic Notation "cleanup_perm_of_zx" :=
  auto_cast_eqn (autorewrite with perm_of_zx_cleanup_db perm_inv_db perm_cleanup_db).

Lemma compose_id_of_compose_idn {f g : nat -> nat} 
  (H : f ∘ g = (fun n => n)) {k : nat} : f (g k) = k.
Proof.
  apply_f H k.
  easy.
Qed.

Ltac perm_by_inverse finv :=
  exists finv;
  intros k Hk; repeat split;
  only 3,4 : (try apply compose_id_of_compose_idn; cleanup_perm; tryeasylia) 
            || cleanup_perm; tryeasylia;
  only 1,2 : auto with perm_bdd_db; tryeasylia.

(* Showing things are permutations *)

Local Notation idn := (fun (k : nat) => k).

Lemma idn_permutation : forall n, permutation n idn.
Proof. exists idn. easy. Qed.

Global Hint Resolve idn_permutation : perm_db.

Lemma compose_idn_l {T} {f: T -> nat} : (idn ∘ f = f)%prg.
Proof.
	unfold compose.
	apply functional_extensionality; easy.
Qed.

Lemma compose_idn_r {T} {f: nat -> T} : (f ∘ idn = f)%prg.
Proof.
	unfold compose.
	apply functional_extensionality; easy.
Qed.

#[export] Hint Rewrite @compose_idn_r @compose_idn_l : perm_cleanup_db.

Lemma WF_of_linv_WF {n} {f finv}
	(HfWF : forall k, n <= k -> f k = k) (Hinv : finv ∘ f = idn) :
	forall k, n <= k -> finv k = k.
Proof.
	intros k Hk.
	rewrite <- (HfWF k Hk).
  apply_f Hinv k.
	rewrite Hinv, (HfWF k Hk).
	easy.
Qed.

Lemma bdd_of_WF_linv {n} {f finv}  
  (HWF: forall k, n <= k -> f k = k) (Hinv : finv ∘ f = idn) : 
  forall k, k < n -> f k < n.
Proof.
  intros k Hk.
  pose proof (WF_of_linv_WF HWF Hinv) as HWFinv.
  apply_f Hinv k.
  bdestruct (f k <? n); [easy|].
  specialize (HWFinv (f k) H).
  lia.
Qed.

Lemma rinv_bdd_of_WF {n} {f finv} (Hinv : f ∘ finv = idn) 
  (HWF : forall k, n <= k -> f k = k) :
  forall k, k < n -> finv k < n.
Proof.
  intros k Hk.
  apply_f Hinv k.
  bdestruct (finv k <? n).
  - easy.
  - specialize (HWF _ H).
    lia.
Qed.

Lemma WF_permutation_inverse_injective (f : nat->nat) (n:nat) {finv finv'}
  (Hf: permutation n f) (HfWF : forall k, n <= k -> f k = k)
  (Hfinv : (finv ∘ f = idn)%prg) (Hfinv' : (finv' ∘ f = idn)%prg) :
  finv = finv'.
Proof.
	apply functional_extensionality; intros k.
	pose proof (WF_of_linv_WF HfWF Hfinv) as HfinvWF.
	pose proof (WF_of_linv_WF HfWF Hfinv') as Hfinv'WF.
	bdestruct (n <=? k).
	- rewrite HfinvWF, Hfinv'WF; easy.
	- destruct Hf as [fi Hfi].
	  specialize (Hfi k H).
	  apply_f Hfinv (fi k); apply_f Hfinv' (fi k).
	  replace (f (fi k)) with k in * by easy.
	  rewrite Hfinv, Hfinv'.
	  easy.
Qed.

Ltac by_inverse_injective f n :=
  apply (WF_permutation_inverse_injective f n); [
    tryeasylia; auto with perm_db |
    tryeasylia; auto with perm_WF_db |
    try solve [cleanup_perm; auto] |
    try solve [cleanup_perm; auto]]; tryeasylia.

Lemma swap_permutation_inv : 
  swap_permutation ∘ swap_permutation = idn.
Proof.
  apply functional_extensionality; intros k.
  repeat first [easy | destruct k].
Qed.

#[export] Hint Rewrite swap_permutation_inv : perm_inv_db.

Lemma swap_permutation_bdd k :
  k < 2 -> swap_permutation k < 2.
Proof.
  intros Hk.
  repeat first [easy | destruct k | cbn; lia].
Qed.

#[export] Hint Resolve swap_permutation_bdd : perm_bdd_db.

Lemma swap_permutation_WF k : 1 < k -> swap_permutation k = k.
Proof.
  intros. 
  repeat first [easy | lia | destruct k].
Qed.

Global Hint Resolve swap_permutation_WF : perm_WF_db.

Lemma swap_permutation_2permutation : permutation 2 swap_permutation.
Proof. 
  perm_by_inverse swap_permutation.
Qed.

Global Hint Resolve swap_permutation_2permutation : perm_db.

Lemma stack_permutations_left {n0 n1} {f g} {k} :
  k < n0 -> stack_permutations n0 n1 f g k = f k.
Proof.
  intros Hk.
  unfold stack_permutations.
  bdest_lia_replace (k <? n0) true.
  easy.
Qed.

Lemma stack_permutations_right {n0 n1} {f g} {k} :
  n0 <= k < n0 + n1 -> stack_permutations n0 n1 f g k = g (k - n0) + n0.
Proof.
  intros Hk.
  unfold stack_permutations.
  bdest_lia_replace (k <? n0) false.
  bdest_lia_replace (k <? n0 + n1) true.
  easy.
Qed.

Lemma stack_permutations_right_add {n0 n1} {f g} {k} :
  k < n1 -> stack_permutations n0 n1 f g (k + n0) = g k + n0.
Proof.
  intros Hk.
  rewrite stack_permutations_right; [|lia].
  replace (k + n0 - n0) with k by lia.
  easy.
Qed.

Lemma stack_permutations_add_right {n0 n1} {f g} {k} :
  k < n1 -> stack_permutations n0 n1 f g (n0 + k) = g k + n0.
Proof.
  rewrite Nat.add_comm.
  exact stack_permutations_right_add.
Qed.

Lemma stack_permutations_high {n0 n1} {f g} {k} :
	n0 + n1 <= k -> (stack_permutations n0 n1 f g) k = k.
Proof.
	intros H.
	unfold stack_permutations.
	bdest_lia_replace (k <? n0) false.
	bdest_lia_replace (k <? n0 + n1) false.
	easy.
Qed.

Lemma stack_permutations_f_idn n0 n1 f :
	stack_permutations n0 n1 f idn = fun k => if k <? n0 then f k else k.
Proof. solve_stack_perm n0 n1. Qed.

Lemma stack_permutations_idn_f n0 n1 f : 
	stack_permutations n0 n1 idn f = 
	fun k => if (¬ k <? n0) && (k <? n0 + n1) then f (k - n0) + n0 else k.
Proof. solve_stack_perm n0 n1. Qed.

Lemma stack_permutations_idn_idn n0 n1 :
	stack_permutations n0 n1 idn idn = idn.
Proof. solve_stack_perm n0 n1. Qed.

#[export] Hint Rewrite stack_permutations_idn_idn : perm_cleanup_db.

Lemma stack_permutations_WF_idn {n0 n1} {f} 
	(H : forall k, n0 <= k -> f k = k): 
	stack_permutations n0 n1 f idn = f.
Proof.
	solve_stack_perm n0 n1;
	rewrite H; lia.
Qed.

Lemma stack_permutations_WF {n0 n1} {f g} k :
  n0 + n1 <= k -> stack_permutations n0 n1 f g k = k.
Proof.
  intros H.
  unfold stack_permutations.
  destruct_if_solve.
Qed.

Global Hint Resolve stack_permutations_WF : perm_WF_db.

Lemma stack_permutations_bdd {n0 n1} {f g}
  (Hf : forall k, k < n0 -> f k < n0) (Hg : forall k, k < n1 -> g k < n1) :
  forall k, k < n0 + n1 -> stack_permutations n0 n1 f g k < n0 + n1.
Proof.
  intros k Hk.
  unfold stack_permutations.
  bdestruct (k <? n0).
  - specialize (Hf k H). lia.
  - bdestruct (k <? n0 + n1); [|easy].
    assert (Hkn0 : k - n0 < n1) by lia.
    specialize (Hg _ Hkn0). lia.
Qed. 

Global Hint Resolve stack_permutations_bdd : perm_bdd_db.

Lemma stack_permutations_compose {n0 n1} {f g} {f' g'} 
	(Hf' : permutation n0 f') (Hg' : permutation n1 g') :
	(stack_permutations n0 n1 f g ∘ stack_permutations n0 n1 f' g'
	= stack_permutations n0 n1 (f ∘ f') (g ∘ g'))%prg.
Proof.
	destruct Hf' as [Hf'inv Hf'].
	destruct Hg' as [Hg'inv Hg'].
	unfold compose.
	solve_stack_perm_strong n0 n1. 
	1,2: specialize (Hf' k H); lia.
	- f_equal; f_equal. lia.
	- assert (Hk: k - n0 < n1) by lia.
	  specialize (Hg' _ Hk); lia.
Qed.

Lemma stack_permutations_id_of_left_right {n0 n1} {f g} 
  (Hf : forall k, k < n0 -> f k = k) (Hg : forall k, k < n1 -> g k = k) :
  stack_permutations n0 n1 f g = idn.
Proof.
  solve_stack_perm n0 n1.
  - apply Hf; easy.
  - rewrite Hg; lia.
Qed.

Lemma stack_permutations_rinv {n0 n1} {f g} {finv ginv}
  (Hf: forall k, k < n0 -> (f k < n0 /\ finv k < n0 /\ finv (f k) = k /\ f (finv k) = k))
  (Hg: forall k, k < n1 -> (g k < n1 /\ ginv k < n1 /\ ginv (g k) = k /\ g (ginv k) = k)) : 
  stack_permutations n0 n1 f g ∘ stack_permutations n0 n1 finv ginv = idn.
Proof.
  unfold compose.
  solve_stack_perm_strong n0 n1.
  1-3: specialize (Hf _ H); lia.
  - replace (ginv (k - n0) + n0 - n0) with (ginv (k - n0)) by lia.
    assert (Hkn0: k - n0 < n1) by lia.
    specialize (Hg _ Hkn0).
    lia.
  - assert (Hkn0: k - n0 < n1) by lia.
    specialize (Hg _ Hkn0).
    lia.
Qed.

Lemma stack_permutations_linv {n0 n1} {f g} {finv ginv}
  (Hf: forall k, k < n0 -> (f k < n0 /\ finv k < n0 /\ finv (f k) = k /\ f (finv k) = k))
  (Hg: forall k, k < n1 -> (g k < n1 /\ ginv k < n1 /\ ginv (g k) = k /\ g (ginv k) = k)) : 
  stack_permutations n0 n1 finv ginv ∘ stack_permutations n0 n1 f g = idn.
Proof.
  rewrite stack_permutations_rinv.
  2,3: rewrite is_inv_iff_inv_is.
  all: easy.
Qed.

#[export] Hint Rewrite @stack_permutations_rinv @stack_permutations_linv : perm_inv_db.

Lemma stack_permutations_permutation {n0 n1 f g} (Hf : permutation n0 f) (Hg: permutation n1 g) :
  permutation (n0 + n1) (stack_permutations n0 n1 f g).
Proof.
  destruct Hf as [f' Hf'].
  destruct Hg as [g' Hg'].
  perm_by_inverse (stack_permutations n0 n1 f' g').
  1,2: apply stack_permutations_bdd; try easy; intros k' Hk'; 
       try specialize (Hf' _ Hk'); try specialize (Hg' _ Hk'); easy.
  1,2: rewrite is_inv_iff_inv_is; easy.
Qed.

Global Hint Resolve stack_permutations_permutation : perm_db.

Global Hint Resolve permutation_compose : perm_db.

Lemma zxperm_permutation n zx : 
  ZX_Perm n zx -> permutation n (perm_of_zx zx).
Proof. 
  intros H.
  induction H; show_permutation.
Qed.

Global Hint Resolve zxperm_permutation : perm_db.

(* top_to_bottom and bottom_to_top permutations, and their generalizations to rotr / rotl *)

Lemma bottom_to_top_perm_bdd {n} k : 
	k < n -> bottom_to_top_perm n k < n.
Proof.
	intros Hk.
	unfold bottom_to_top_perm.
	bdest_lia_replace (n <=? k) false.
	destruct k; lia.
Qed.

Lemma top_to_bottom_perm_bdd {n} k :
	k < n -> top_to_bottom_perm n k < n.
Proof.
	intros Hk.
	unfold top_to_bottom_perm.
	bdest_lia_replace (n <=? k) false.
	bdestruct (k =? n - 1); lia.
Qed.

Global Hint Resolve bottom_to_top_perm_bdd top_to_bottom_perm_bdd : perm_bdd_db.

Lemma bottom_to_top_perm_WF {n} k : n <= k ->
	bottom_to_top_perm n k = k.
Proof.
	intros Hk.
	unfold bottom_to_top_perm.
	bdest_lia_replace (n <=? k) true.
	easy.
Qed.

Lemma top_to_bottom_perm_WF {n} k : n <= k ->
	top_to_bottom_perm n k = k.
Proof.
	intros Hk.
	unfold top_to_bottom_perm.
	bdest_lia_replace (n <=? k) true.
	easy.
Qed.
	
Global Hint Resolve bottom_to_top_perm_WF top_to_bottom_perm_WF : perm_WF_db.

Lemma bottom_to_top_to_bottom_inv n : 
	bottom_to_top_perm n ∘ top_to_bottom_perm n = idn.
Proof.
	apply functional_extensionality; intros k.
	unfold compose, bottom_to_top_perm, top_to_bottom_perm.
	bdestruct (n <=? k).
	1: bdest_lia_replace (n <=? k) true; easy.
	bdestruct (k =? n - 1).
	- destruct n.
	  + easy.
	  + bdest_lia_replace (S n <=? 0) false.
	  	lia.
	- bdest_lia_replace (n <=? k + 1) false.
	  replace (k + 1) with (S k) by lia.
	  easy.
Qed.

Lemma top_to_bottom_to_top_inv n :
	top_to_bottom_perm n ∘ bottom_to_top_perm n = idn.
Proof.
	apply functional_extensionality; intros k.
	unfold compose, bottom_to_top_perm, top_to_bottom_perm.
	bdestruct (n <=? k).
	1: bdest_lia_replace (n <=? k) true; easy.
	destruct k.
	- destruct n; [easy|].
	  bdest_lia_replace (S n <=? S n - 1) false.
	  rewrite Nat.eqb_refl.
	  easy.
	- bdest_lia_replace (n <=? k) false.
	  bdest_lia_replace (k =? n - 1) false.
	  lia.
Qed.

Lemma bottom_to_top_to_bottom_inv' {n k} :
	bottom_to_top_perm n (top_to_bottom_perm n k) = k.
Proof.
	pose proof (bottom_to_top_to_bottom_inv n) as H.
	apply (f_equal (fun g => g k)) in H.
	unfold compose in H.
	easy.
Qed.

Lemma top_to_bottom_to_top_inv' {n k} :
	top_to_bottom_perm n (bottom_to_top_perm n k) = k.
Proof.
	pose proof (top_to_bottom_to_top_inv n) as H.
	apply (f_equal (fun g => g k)) in H.
	unfold compose in H.
	easy.
Qed.

#[export] Hint Rewrite 
  (fun n => @bottom_to_top_to_bottom_inv n)
  (fun n => @bottom_to_top_to_bottom_inv' n)
  (fun n => @top_to_bottom_to_top_inv n)
  (fun n => @top_to_bottom_to_top_inv' n)
  : perm_inv_db.


Lemma top_to_bottom_permutation {n} :
	permutation n (top_to_bottom_perm n).
Proof.
  perm_by_inverse (bottom_to_top_perm n).
Qed.

Lemma bottom_to_top_permutation {n} :
	permutation n (bottom_to_top_perm n). 
Proof.
	perm_by_inverse (top_to_bottom_perm n).
Qed.

Global Hint Resolve top_to_bottom_permutation bottom_to_top_permutation : perm_db.

Lemma rotr_WF {n m} : 
	forall k, n <= k -> (rotr n m) k = k.
Proof. intros. unfold rotr. destruct_if; lia. Qed.

Lemma rotl_WF {n m} : 
	forall k, n <= k -> (rotl n m) k = k.
Proof. intros. unfold rotl. destruct_if; lia. Qed.

Global Hint Resolve rotr_WF rotl_WF : perm_WF_db.

Lemma rotr_bdd {n m} : 
	forall k, k < n -> (rotr n m) k < n.
Proof.
	intros. unfold rotr. destruct_if; [lia|].
	apply Nat.mod_upper_bound; lia.
Qed.

Lemma rotl_bdd {n m} : 
	forall k, k < n -> (rotl n m) k < n.
Proof.
	intros. unfold rotl. destruct_if; [lia|].
	apply Nat.mod_upper_bound; lia.
Qed.

Global Hint Resolve rotr_bdd rotl_bdd : perm_bdd_db.

Lemma rotr_rotl_inv n m :
	((rotr n m) ∘ (rotl n m) = idn)%prg.
Proof.
	apply functional_extensionality; intros k.
	unfold compose, rotl, rotr.
	bdestruct (n <=? k); [destruct_if_solve|].
	assert (Hn0 : n <> 0) by lia.
	destruct_if.
	- pose proof (Nat.mod_upper_bound (k + (n - m mod n)) n Hn0) as Hbad.
	  lia. (* contradict Hbad *)
	- rewrite Nat.add_mod_idemp_l; [|easy].
	  rewrite <- Nat.add_assoc.
	  replace (n - m mod n + m) with
	    (n - m mod n + (n * (m / n) + m mod n)) by
	    (rewrite <- (Nat.div_mod m n Hn0); easy).
	  pose proof (Nat.mod_upper_bound m n Hn0).
	  replace (n - m mod n + (n * (m / n) + m mod n)) with
	    (n * (1 + m / n)) by lia.
	  rewrite Nat.mul_comm, Nat.mod_add; [|easy].
	  apply Nat.mod_small, H.
Qed.

Lemma rotl_rotr_inv n m : 
	((rotl n m) ∘ (rotr n m) = idn)%prg.
Proof.
	apply functional_extensionality; intros k.
	unfold compose, rotl, rotr.
	bdestruct (n <=? k); [destruct_if_solve|].
	assert (Hn0 : n <> 0) by lia.
	destruct_if.
	- pose proof (Nat.mod_upper_bound (k + m) n Hn0) as Hbad.
	  lia. (* contradict Hbad *)
	- rewrite Nat.add_mod_idemp_l; [|easy].
	  rewrite <- Nat.add_assoc.
	  replace (m + (n - m mod n)) with
	    ((n * (m / n) + m mod n) + (n - m mod n)) by
	    (rewrite <- (Nat.div_mod m n Hn0); easy).
	  pose proof (Nat.mod_upper_bound m n Hn0).
	  replace ((n * (m / n) + m mod n) + (n - m mod n)) with
	    (n * (1 + m / n)) by lia.
	  rewrite Nat.mul_comm, Nat.mod_add; [|easy].
	  apply Nat.mod_small, H.
Qed.

#[export] Hint Rewrite rotr_rotl_inv rotl_rotr_inv : perm_inv_db.

Lemma rotr_perm {n m} : permutation n (rotr n m).
Proof. 
	perm_by_inverse (rotl n m).
Qed.

Lemma rotl_perm {n m} : permutation n (rotl n m).
Proof. 
	perm_by_inverse (rotr n m).
Qed.

Global Hint Resolve rotr_perm rotl_perm : perm_db.

Lemma rotr_0_r n : rotr n 0 = idn.
Proof.
	apply functional_extensionality; intros k.
	unfold rotr.
	destruct_if_solve.
	rewrite Nat.mod_small; lia.
Qed.

Lemma rotl_0_r n : rotl n 0 = idn.
Proof.
	apply functional_extensionality; intros k.
	unfold rotl.
	destruct_if_solve.
	rewrite Nat.mod_0_l, Nat.sub_0_r; [|lia].
	replace (k + n) with (k + 1 * n) by lia.
	rewrite Nat.mod_add, Nat.mod_small; lia.
Qed.

Lemma rotr_0_l k : rotr 0 k = idn.
Proof.
	apply functional_extensionality; intros a.
	unfold rotr.
	destruct_if_solve.
Qed.
	
Lemma rotl_0_l k : rotl 0 k = idn.
Proof.
	apply functional_extensionality; intros a.
	unfold rotl.
	destruct_if_solve.
Qed.

#[export] Hint Rewrite rotr_0_r rotl_0_r rotr_0_l rotl_0_l : perm_cleanup_db.

Lemma rotr_rotr n k l :
	((rotr n k) ∘ (rotr n l) = rotr n (k + l))%prg.
Proof.
	apply functional_extensionality; intros a.
	unfold compose, rotr.
	symmetry.
	destruct_if_solve; assert (Hn0 : n <> 0) by lia.
	- pose proof (Nat.mod_upper_bound (a + l) n Hn0); lia.
	- rewrite Nat.add_mod_idemp_l; [|easy].
	  f_equal; lia.
Qed.

Lemma rotl_rotl n k l :
	((rotl n k) ∘ (rotl n l) = rotl n (k + l))%prg.
Proof.
	apply (WF_permutation_inverse_injective (rotr n (k + l)) n).
	- apply rotr_perm.
	- apply rotr_WF.
	- rewrite Nat.add_comm, <- rotr_rotr, 
		<- Combinators.compose_assoc, (Combinators.compose_assoc _ _ _ _ (rotr n l)).
	  cleanup_perm; easy. (* rewrite rotl_rotr_inv, compose_idn_r, rotl_rotr_inv. *)
	- rewrite rotl_rotr_inv; easy.
Qed.

#[export] Hint Rewrite rotr_rotr rotl_rotl : perm_cleanup_db.

Lemma rotr_n n : rotr n n = idn.
Proof.
	apply functional_extensionality; intros a.
	unfold rotr.
	destruct_if_solve.
	replace (a + n) with (a + 1 * n) by lia.
	destruct n; [lia|].
	rewrite Nat.mod_add; [|easy].
	rewrite Nat.mod_small; easy.
Qed.

#[export] Hint Rewrite rotr_n : perm_cleanup_db.

Lemma rotr_eq_rotr_mod n k : rotr n k = rotr n (k mod n).
Proof.
	strong induction k.
	bdestruct (k <? n).
	- rewrite Nat.mod_small; easy.
	- specialize (H (k - 1 * n)).
	  replace (rotr n k) with (rotr n (k - 1*n + n)) by (f_equal;lia).
	  destruct n.
    1: cleanup_perm; easy. (* rewrite rotr_0_l. symmetry. rewrite rotr_0_l. easy. *)
	  rewrite <- rotr_rotr, rotr_n, H; [|lia].
	  rewrite compose_idn_r.
	  rewrite sub_mul_mod; [easy|lia].
Qed.

Lemma rotl_n n : rotl n n = idn.
Proof.
  by_inverse_injective (rotr n n) n.
Qed.

#[export] Hint Rewrite rotl_n : perm_cleanup_db.

Lemma rotl_eq_rotl_mod n k : rotl n k = rotl n (k mod n).
Proof. 
  by_inverse_injective (rotr n k) n.
  rewrite rotr_eq_rotr_mod, rotl_rotr_inv; easy.
Qed.

Lemma rotr_eq_rotl_sub n k : 
	rotr n k = rotl n (n - k mod n).
Proof.
	rewrite rotr_eq_rotr_mod.
  by_inverse_injective (rotl n (k mod n)) n.
  cleanup_perm.
	destruct n; [rewrite rotl_0_l; easy|].
  assert (H': S n <> 0) by easy.
  pose proof (Nat.mod_upper_bound k _ H'). 
  rewrite <- (rotl_n (S n)).
  f_equal.
  lia.
Qed.

Lemma rotl_eq_rotr_sub n k : 
	rotl n k = rotr n (n - k mod n).
Proof.
  by_inverse_injective (rotr n k) n.
	destruct n; [cbn; rewrite 2!rotr_0_l, compose_idn_l; easy|].
  rewrite (rotr_eq_rotr_mod _ k), rotr_rotr, <- (rotr_n (S n)).
  f_equal.
  assert (H' : S n <> 0) by easy.
  pose proof (Nat.mod_upper_bound k (S n) H').
  lia.
Qed.

Lemma top_to_bottom_perm_eq_rotr n :
	top_to_bottom_perm n = rotr n 1.
Proof.
	apply functional_extensionality; intros k.
	unfold top_to_bottom_perm, rotr.
	destruct_if_solve.
	- subst. 
	  replace (n - 1 + 1) with n by lia.
	  rewrite Nat.mod_same; lia.
	- rewrite Nat.mod_small; lia.
Qed.

#[export] Hint Rewrite top_to_bottom_perm_eq_rotr : perm_cleanup_db.

Lemma bottom_to_top_perm_eq_rotl n :
	bottom_to_top_perm n = rotl n 1.
Proof.
  by_inverse_injective (top_to_bottom_perm n) n.
Qed.

#[export] Hint Rewrite bottom_to_top_perm_eq_rotl : perm_cleanup_db.

(* We're about to show the correctness of zxperm semantics (i.e., 
   matrix of (perm_of_zx zx) is ⟦ zx ⟧ for zx a ZX_Perm), but first, 
   we need a tremendous amount of machinery to show that stack_permutation
   behaves like the kronecker product. [The rest of the proof of
   correctness is a third length of just correctness of stacking.]*)

Lemma testbit_binlist {n : nat} {k : list bool} :
  Nat.testbit (binlist_to_nat k) n = nth n k false.
Proof.
  revert k;
  induction n;
  intros k.
  - cbn.
    destruct k; [easy|].  
    destruct b; cbn;
    rewrite Nat.add_0_r.
    2: rewrite <- Nat.negb_even;
      symmetry; apply negb_sym; cbn.
    1: rewrite Nat.odd_succ.
    all: rewrite Nat.even_add;
      apply eqb_reflx.
  - destruct k.
    + rewrite Nat.testbit_0_l; easy.
    + simpl. 
      destruct b;
      simpl Nat.b2n.
      * rewrite Nat.add_1_l.
        rewrite Nat.add_0_r, double_mult.
        rewrite div2_S_double.
        apply IHn.
      * rewrite Nat.add_0_l, Nat.add_0_r, double_mult.
        rewrite Nat.div2_double.
        apply IHn.
Qed.

Lemma binlist_mod {k : list bool} {n0 : nat} :
  (binlist_to_nat k) mod (2^n0) = binlist_to_nat (firstn n0 k).
Proof.
  apply Nat.bits_inj.
  intros n.
  rewrite testbit_binlist.
  bdestruct (n <? n0).
  - rewrite Nat.mod_pow2_bits_low.
    rewrite testbit_binlist.
    rewrite nth_firstn.
    easy.
    1,2: exact H.
  - rewrite Nat.mod_pow2_bits_high; [|easy].
    rewrite nth_overflow; [easy|].
    transitivity n0; [|easy].
    apply firstn_le_length.
Qed.

Lemma nth_skipn {T:Type} {n0 n : nat} {k : list T} {d : T} : 
  nth n (skipn n0 k) d = nth (n0 + n) k d.
Proof.
  bdestruct (n0 <? length k).
  - replace (nth _ k d) with 
      (nth (n0+n) (firstn n0 k ++ skipn n0 k) d) 
      by (rewrite (firstn_skipn n0 k); easy).
    replace (n0 + n) with (length (firstn n0 k) + n).
    + rewrite app_nth2_plus.
      easy. 
    + rewrite firstn_length_le; lia.
  - rewrite skipn_all2; [|easy].
    rewrite 2!nth_overflow; cbn; try easy; try lia.
Qed.

Lemma binlist_div {k : list bool} {n0 : nat} :
  (binlist_to_nat k) / (2^n0) = binlist_to_nat (skipn n0 k).
Proof.
  apply Nat.bits_inj.
  intros n.
  rewrite Nat.div_pow2_bits.
  rewrite 2!testbit_binlist.
  rewrite nth_skipn.
  rewrite Nat.add_comm.
  easy. 
Qed.

Lemma funbool_to_nat_div {n0 n1 : nat} {f}:
  (funbool_to_nat (n0 + n1) f) / (2^n1) = funbool_to_nat n0 f.
Proof.
  destruct n1.
  - rewrite Nat.pow_0_r, Nat.div_1_r, Nat.add_0_r.
    easy.
  - rewrite (funbool_to_nat_shift _ _ n0); [|lia].
    replace (n0 + S n1 - n0) with (S n1) by lia.
    rewrite Nat.mul_comm.
    rewrite Nat.div_add_l; [|apply Nat.pow_nonzero; easy].
    rewrite Nat.div_small; [easy|].
    apply funbool_to_nat_bound.
Qed.

Lemma funbool_to_nat_mod {n0 n1 : nat} {f}:
  (funbool_to_nat (n0 + n1) f) mod (2^n1) = funbool_to_nat n1 (shift f n0).
Proof.
  destruct n1.
  - rewrite Nat.pow_0_r, Nat.mod_1_r.
    easy.
  - rewrite (funbool_to_nat_shift _ _ n0); [|lia].
    replace (n0 + S n1 - n0) with (S n1) by lia.
    rewrite Nat.add_comm, Nat.mul_comm, Nat.mod_add;
    [|apply Nat.pow_nonzero; easy].
    rewrite Nat.mod_small; [|apply funbool_to_nat_bound].
    easy.
Qed.

Lemma testbit_funbool_to_nat {n0 n} {f} :
  Nat.testbit (funbool_to_nat n0 f) n = if n <? n0 then f (n0 - (S n)) else false.
Proof.
  unfold funbool_to_nat.
  rewrite testbit_binlist.
  gen n0 f;
  induction n; intros n0 f.
  - induction n0.
    + cbn. easy.
    + replace (0 <? S n0) with true by easy.
      cbn.
      rewrite Nat.sub_0_r.
      easy.
  - induction n0.
    + cbn. easy.
    + cbn. rewrite IHn. easy.
Qed.

Lemma list_to_funbool_eq {k : list bool} {n0} :
  (list_to_funbool n0 k) = fun n => if n <=? (n0 - 1) then nth (n0 - S n) k false else false.
Proof.
  gen n0;
  induction k; intros n0.
  - apply functional_extensionality; intros n.
    destruct (n0 - S n); rewrite Tauto.if_same; easy.
  - destruct n0.
    1: apply functional_extensionality; intros n; destruct n; try easy.
      simpl. rewrite IHk.
      unfold update. easy.
    simpl list_to_funbool. 
    rewrite IHk.
    apply functional_extensionality.
    intros n.
    unfold update.
    rewrite Nat.sub_0_r.
    replace (S n0 - 1) with n0 by lia.
    bdestruct (n <=? n0).
    + bdestruct (n =? n0).
      * subst.
        replace (S n0 - S n0) with 0 by lia.
        easy.
      * bdestruct (n <=? n0 - 1); [|lia].
        destruct (S n0 - S n) as [|n'] eqn:Hn'; [lia|].
        simpl nth.
        replace (n0 - S n) with n' by lia.
        easy.
    + bdestruct (n =? n0); subst; try lia.
      bdestruct (n <=? n0 - 1); subst; try lia.
Qed.

Lemma list_to_funbool_eq' {k : list bool} {n0 n} :
  list_to_funbool n0 k n = if n <=? (n0 - 1) then nth (n0 - S n) k false else false.
Proof.
  rewrite list_to_funbool_eq. easy.
Qed.

Lemma nth_nat_to_binlist {len n} : forall k,
  nth k (nat_to_binlist len n) false = Nat.testbit n k.
Proof.
  intros k.
  rewrite <- testbit_binlist, nat_to_binlist_inverse.
  easy.
Qed.

Lemma nat_to_funbool_eq {n j} :
  nat_to_funbool n j = fun k => if k <=? n - 1 then Nat.testbit j (n - S k) else false.
Proof.
  apply functional_extensionality; intros k.
  unfold nat_to_funbool.
  rewrite list_to_funbool_eq', nth_nat_to_binlist.
  easy.
Qed.

Lemma nat_to_funbool_mod {n1 j} {k} (n0:nat) : k < n1 ->
  nat_to_funbool n1 (j mod 2 ^ n1) k = nat_to_funbool (n0 + n1) j (k + n0).
Proof.
  intros Hk.
  rewrite 2!nat_to_funbool_eq.
  bdest_lia_replace (k <=? n1 - 1) true.
  bdest_lia_replace (k + n0 <=? n0 + n1 - 1) true.
  rewrite Nat.mod_pow2_bits_low; [|lia].
  f_equal.
  lia.
Qed.

Lemma nat_to_funbool_div {n0 n1 j} {k} : k < n0 -> 
  nat_to_funbool n0 (j / 2 ^ n1) k = nat_to_funbool (n0 + n1) j k.
Proof.
  intros Hk.
  rewrite 2!nat_to_funbool_eq.
  bdest_lia_replace (k <=? n0 - 1) true.
  bdest_lia_replace (k <=? n0 + n1 - 1) true.
  rewrite Nat.div_pow2_bits.
  f_equal.
  lia.
Qed.

Lemma div_mod_inj {a b} (c:nat) : c > 0 ->
  (a mod c) = (b mod c) /\ (a / c) = (b / c) -> a = b.
Proof.
  intros Hc.
  intros [Hmod Hdiv].
  rewrite (Nat.div_mod_eq a c).
  rewrite (Nat.div_mod_eq b c).
  rewrite Hmod, Hdiv.
  easy.
Qed.

Lemma eqb_iff {b c : bool} :
  b = c <-> ((b = true) <-> (c = true)).
Proof.
  destruct b; destruct c; split;
  intros; try split; auto; lia.
Qed.

(* Now, on to correctness. *)

Lemma empty_permutation_semantics : ⟦ Empty ⟧ = zxperm_to_matrix 0 Empty.
Proof. check_finite_matrix. Qed.

Lemma wire_permutation_semantics : ⟦ Wire ⟧ = zxperm_to_matrix 1 Wire.
Proof. check_finite_matrix. Qed.

Lemma swap_permutation_semantics : ⟦ Swap ⟧ = zxperm_to_matrix 2 Swap.
Proof. check_finite_matrix. Qed.

Lemma stack_permutations_matrix_helper {n0 n1 i j} {f g} (Hi : i < 2 ^ (n0 + n1)) (Hj: j < 2 ^ (n0 + n1)) :
  permutation n0 f -> permutation n1 g ->
  i =? qubit_perm_to_nat_perm (n0 + n1) (stack_permutations n0 n1 f g) j = 
  (i / 2 ^ n1 =? qubit_perm_to_nat_perm n0 f (j / 2 ^ n1)) &&
  (i mod 2 ^ n1 =? qubit_perm_to_nat_perm n1 g (j mod 2 ^ n1)).
Proof.
  intros Hfperm Hgperm. 
  pose proof Hfperm as [finv Hf].
  pose proof Hgperm as [ginv Hg].
  pose proof (stack_permutations_permutation Hfperm Hgperm) as Hstackperm.
  pose proof Hstackperm as [stackinv Hstack].
  unfold qubit_perm_to_nat_perm.
  rewrite eqb_iff, Bool.andb_true_iff, 3!Nat.eqb_eq.
  split.
  - intros Heq.
    split.
    + apply Nat.bits_inj.
      intros k.
      rewrite Heq, funbool_to_nat_div.
      rewrite 2!nat_to_funbool_eq.
      rewrite 2!testbit_funbool_to_nat.
      bdestruct (k <? n0); [|easy].
      unfold compose.
      assert (Hlt:n0 - S k < n0) by lia.
      replace (stack_permutations n0 n1 f g (n0 - S k) <=? n0 + n1 - 1) with true by (
        assert (Hlt2: n0 - S k < n0 + n1) by lia;
        specialize (Hstack (n0 - S k) Hlt2);
        bdestruct (stack_permutations n0 n1 f g (n0 - S k) <=? n0 + n1 - 1); lia
      ).
      replace (f (n0 - S k) <=? n0 - 1) with true by (
        specialize (Hf (n0 - S k) Hlt);
        bdestruct (f (n0 - S k) <=? n0 - 1); lia
      ).
      unfold stack_permutations.
      replace (n0 - S k <? n0) with true by (bdestruct (n0 - S k <? n0); lia).
      rewrite Nat.div_pow2_bits.
      f_equal.
      assert (S (f (n0 - S k)) <= n0). {
        specialize (Hf (n0 - S k) Hlt).
        lia. }
      lia.
    + apply Nat.bits_inj.
      intros k.
      rewrite Heq, funbool_to_nat_mod.
      rewrite 2!nat_to_funbool_eq.
      rewrite 2!testbit_funbool_to_nat.
      bdestruct (k <? n1); [|easy].
      unfold compose.
      assert (Hlt:n1 - S k < n1) by lia.
      rewrite Nat.mod_pow2_bits_low; [|lia].
      unfold shift.
      replace (stack_permutations n0 n1 f g (n1 - S k + n0) <=? n0 + n1 - 1) with true by (
        assert (Hlt2: n1 - S k + n0 < n0 + n1) by lia;
        specialize (Hstack _ Hlt2);
        bdestruct (stack_permutations n0 n1 f g (n1 - S k + n0) <=? n0 + n1 - 1); lia
      ).
      replace (g (n1 - S k) <=? n1 - 1) with true by (
        specialize (Hg (n1 - S k) Hlt);
        bdestruct (g (n1 - S k) <=? n1 - 1); lia
      ).
      f_equal.
      unfold stack_permutations.
      replace (n1 - S k + n0 <? n0) with false by (bdestruct (n1 - S k + n0 <? n0); lia).
      replace (n1 - S k + n0 <? n0 + n1) with true by (bdestruct (n1 - S k + n0 <? n0 + n1); lia).
      replace (n1 - S k + n0 - n0) with (n1 - S k) by lia.
      lia.
  - intros [Hdiv Hmod].
    apply (div_mod_inj (2^n1)); [pose proof (Nat.pow_nonzero 2 n1); lia|].
    split.
    + rewrite Hmod.
      rewrite funbool_to_nat_mod.
      apply funbool_to_nat_eq.
      intros k Hk.
      rewrite shift_simplify.
      unfold compose.
      rewrite (stack_permutations_right_add Hk).
      
      apply nat_to_funbool_mod.
      specialize (Hg _ Hk); lia.
    + rewrite Hdiv.
      rewrite funbool_to_nat_div.
      apply funbool_to_nat_eq.
      intros k Hk.
      unfold compose.
      rewrite (stack_permutations_left Hk).
      apply nat_to_funbool_div.
      specialize (Hf _ Hk); lia.
Qed.

Lemma apply_if2 {T1 T2 T3 : Type} {b1 b2 : bool} {x1 x2} {x3 x4} (f : T1 -> T2 -> T3) :
  f (if b1 then x1 else x2) (if b2 then x3 else x4) = 
  if b1 && b2 then f x1 x3 else (if b1 then f x1 x4 else (if b2 then f x2 x3 else f x2 x4)).
Proof. destruct b1; destruct b2; easy. Qed.

Lemma stack_permutations_matrix {n0 n1 : nat} {f g : nat -> nat} :
  permutation n0 f -> permutation n1 g ->
  perm_to_matrix (n0 + n1) (stack_permutations n0 n1 f g) =
  (perm_to_matrix n0 f) ⊗ (perm_to_matrix n1 g).
Proof.
  intros Hf Hg.
  apply mat_equiv_eq.
  1,2:auto with wf_db.
  intros i j Hi Hj.
  
  unfold kron, perm_to_matrix, perm_mat.
  rewrite (proj2 (Nat.ltb_lt _ _) Hi), (proj2 (Nat.ltb_lt _ _) Hj).
  replace (i / 2 ^ n1 <? 2 ^ n0) with true.
  replace (j / 2 ^ n1 <? 2 ^ n0) with true.
  replace (i mod 2 ^ n1 <? 2 ^ n1) with true.
  replace (j mod 2 ^ n1 <? 2 ^ n1) with true.
  repeat rewrite andb_true_r.
  rewrite (apply_if2 Cmult), Cmult_0_l, Cmult_0_l, 
  Cmult_1_l, Cmult_1_l, Tauto.if_same, Tauto.if_same.
  rewrite (stack_permutations_matrix_helper Hi Hj Hf Hg).
  easy.
  all: symmetry; rewrite Nat.ltb_lt.
  1,2: apply Nat.mod_upper_bound; apply Nat.pow_nonzero; easy.
  1,2: apply Nat.div_lt_upper_bound; try (apply Nat.pow_nonzero; easy).
  1,2: rewrite Nat.pow_add_r, Nat.mul_comm in Hi, Hj; easy.
Qed.

Lemma stack_permutations_semantics {n0 n1} {zx0 zx1} 
  (Hzx0 : ⟦ zx0 ⟧ = zxperm_to_matrix n0 zx0) 
  (Hzx1 : ⟦ zx1 ⟧ = zxperm_to_matrix n1 zx1) 
  (Hzx0perm : permutation n0 (perm_of_zx zx0))
  (Hzx1perm : permutation n1 (perm_of_zx zx1)) : 
  ⟦ zx0 ↕ zx1 ⟧ = zxperm_to_matrix (n0 + n1) (zx0 ↕ zx1).
Proof.
  simpl.
  rewrite stack_permutations_matrix; [|easy|easy].
  rewrite Hzx0, Hzx1.
  easy.
Qed.

Lemma compose_permutation_semantics {n} {zx0 zx1}
  (Hzx0 : ⟦ zx0 ⟧ = zxperm_to_matrix n zx0)
  (Hzx1 : ⟦ zx1 ⟧ = zxperm_to_matrix n zx1) 
  (Hzx0perm : permutation n (perm_of_zx zx0))
  (Hzx1perm : permutation n (perm_of_zx zx1)) :
  ⟦ zx0 ⟷ zx1 ⟧ = zxperm_to_matrix n (zx0 ⟷ zx1).
Proof.
  cbn.
  unfold perm_to_matrix.
  rewrite <- qubit_perm_to_nat_perm_compose.
  - rewrite <- perm_mat_Mmult.
    + rewrite Hzx0, Hzx1.
      easy.
    + apply qubit_perm_to_nat_perm_bij.
      easy.
  - easy.
Qed.

Lemma cast_permutations_semantics {n m} {zx} {Heq : n = m} 
  (Hzx : ⟦ zx ⟧ = zxperm_to_matrix m zx) :
  ⟦ cast _ _ Heq Heq zx ⟧ = zxperm_to_matrix n (cast _ _ Heq Heq zx).
Proof. subst; easy. Qed.

Lemma zxperm_permutation_semantics {n zx} : 
  ZX_Perm n zx -> ⟦ zx ⟧ = zxperm_to_matrix n zx.
Proof.
  intros H.
  induction H.
  - apply empty_permutation_semantics.
  - apply wire_permutation_semantics.
  - apply swap_permutation_semantics.
  - eapply stack_permutations_semantics; auto.
    all: apply zxperm_permutation; easy.
  - apply compose_permutation_semantics; auto.
    all: apply zxperm_permutation; easy. 
  - apply cast_permutations_semantics.
    easy.
Qed.

(* ... which enables the main result: *)

Lemma prop_of_equal_perm {n} {zx0 zx1 : ZX n n}
	(Hzx0 : ZX_Perm n zx0) (Hzx1 : ZX_Perm n zx1)
	(Hperm : perm_of_zx zx0 = perm_of_zx zx1) :
	zx0 ∝ zx1.
Proof.
	prop_exists_nonzero (RtoC 1).
	rewrite Mscale_1_l.
	rewrite (zxperm_permutation_semantics Hzx0),
		(zxperm_permutation_semantics Hzx1).
	f_equal; easy.
Qed.

(* Now, we develop some tools for showing things are ZX_Perms *)

Global Hint Resolve PermEmpty PermWire PermSwap PermStack PermComp PermCast : zxperm_db.

Lemma ZX_Perm_iff_cast {n m} {zx} (H : n = m) :
	ZX_Perm m zx <-> ZX_Perm n (cast _ _ H H zx).
Proof.
	split.
	- constructor; easy.
	- intros Hperm.
	  subst; easy.
Qed.

Lemma cast_stack_ZX_Perm {n m o} {zx0} {zx1}
	(H0 : ZX_Perm n zx0) (H1 : ZX_Perm m zx1) 
	(Heq : o = n + m) :
	ZX_Perm o (cast _ _ Heq Heq (zx0 ↕ zx1)).
Proof.
  auto with zxperm_db.
Qed.

Global Hint Resolve cast_stack_ZX_Perm : zxperm_db.

Lemma transpose_ZX_Perm {n} {zx} (H : ZX_Perm n zx) :
	ZX_Perm n (zx ⊤).
Proof.
	induction H; try solve [simpl; constructor; try easy].
	(* Only cast left *)
	subst. easy.
Qed.

Global Hint Resolve transpose_ZX_Perm : zxperm_db.

Lemma n_wire_ZX_Perm {n} : 
	ZX_Perm n (n_wire n).
Proof.
	induction n.
	- constructor.
	- simpl.
    apply (PermStack PermWire IHn).
Qed.

Global Hint Resolve n_wire_ZX_Perm : zxperm_db.

Lemma n_compose_ZX_Perm {n} {zx} (H : ZX_Perm n zx) k :
	ZX_Perm _ (n_compose k zx).
Proof.
	induction k; simpl; auto with zxperm_db.
Qed.

Global Hint Resolve n_compose_ZX_Perm : zxperm_db.

Lemma top_to_bottom_helper_ZX_Perm n :
	ZX_Perm (S n) (top_to_bottom_helper n).
Proof.
	induction n.
	- constructor.
	- simpl.
	  constructor.
	  + apply (PermStack PermSwap n_wire_ZX_Perm).
	  + apply (PermStack PermWire IHn).
Qed.

Global Hint Resolve top_to_bottom_helper_ZX_Perm : zxperm_db.

Lemma top_to_bottom_ZX_Perm {n} :
	ZX_Perm n (top_to_bottom n).
Proof.
	destruct n; simpl; auto with zxperm_db.
Qed.

Lemma bottom_to_top_ZX_Perm {n} :
	ZX_Perm n (bottom_to_top n).
Proof.
	apply transpose_ZX_Perm.
	apply top_to_bottom_ZX_Perm.
Qed.

Global Hint Resolve top_to_bottom_ZX_Perm bottom_to_top_ZX_Perm : zxperm_db.

(* Some properties of perm_of_zx, and specific values.*)

Lemma perm_of_zx_WF {n} {zx} (H : ZX_Perm n zx) : forall k, 
	n <= k -> (perm_of_zx zx) k = k.
Proof.
	induction H; intros k Hk; try easy.
	- simpl.
	  destruct k; [|destruct k]; cbn; lia.
	- simpl. 
	  rewrite stack_permutations_high; easy.
	- simpl.
	  unfold compose.
	  rewrite IHZX_Perm1; rewrite IHZX_Perm2; lia.
	- subst. apply IHZX_Perm, Hk. 
Qed.

Global Hint Resolve perm_of_zx_WF : perm_WF_db.

Lemma stack_permutations_zx_idn {n0 n1} {zx} (H : ZX_Perm n0 zx) :
	stack_permutations n0 n1 (perm_of_zx zx) idn = 
	perm_of_zx zx.
Proof.
	apply stack_permutations_WF_idn.
  auto with perm_WF_db.
Qed.

#[export] Hint Rewrite @stack_permutations_zx_idn : perm_of_zx_cleanup_db.

Lemma stack_permutations_idn_zx {n0 n1} {zx} (H : ZX_Perm n1 zx) :
	stack_permutations n0 n1 idn (perm_of_zx zx) = 
	fun k => if k <? n0 then k else (perm_of_zx zx (k - n0)) + n0.
Proof.
	solve_stack_perm n0 n1.
	rewrite perm_of_zx_WF; [lia|easy|lia].
Qed.

Lemma perm_of_n_wire n :
	perm_of_zx (n_wire n) = idn.
Proof.
	induction n.
	- easy.
	- simpl.
	  rewrite IHn.
	  rewrite stack_permutations_idn_idn.
	  easy.
Qed.

Lemma perm_of_zx_compose_spec {n m o} {zx0 : ZX n m} {zx1 : ZX m o} :
	perm_of_zx (zx0 ⟷ zx1) = 
	(perm_of_zx zx0 ∘ perm_of_zx zx1)%prg.
Proof. easy. Qed.

Lemma perm_of_zx_stack_spec {n m o p} {zx0 : ZX n m} {zx1 : ZX o p} :
	perm_of_zx (zx0 ↕ zx1) = 
	stack_permutations n o (perm_of_zx zx0) (perm_of_zx zx1).
Proof. easy. Qed.

Lemma perm_of_zx_stack_n_wire {n} {zx} (H : ZX_Perm n zx) {m} :
	perm_of_zx (zx ↕ (n_wire m)) = perm_of_zx zx.
Proof.
	simpl.
	rewrite perm_of_n_wire.
	rewrite (stack_permutations_zx_idn H).
	easy. 
Qed.

#[export] Hint Rewrite 
  perm_of_n_wire
  @perm_of_zx_compose_spec
  @perm_of_zx_stack_spec
  @perm_of_zx_stack_n_wire : perm_of_zx_cleanup_db.

Lemma perm_of_top_to_bottom_helper_eq {n} :
	perm_of_zx (top_to_bottom_helper n) = top_to_bottom_perm (S n).
Proof.
	strong induction n; 
	apply functional_extensionality; intros k.
	destruct n; [destruct k; easy|].
	simpl.
	rewrite perm_of_n_wire.
	rewrite stack_permutations_WF_idn; [|apply swap_permutation_WF].
	rewrite stack_permutations_idn_zx; [|apply top_to_bottom_helper_ZX_Perm].
	rewrite H; [|auto].
	unfold compose.
	bdestruct (k <? 1). 
	- replace k with 0 by lia. easy.
	- destruct n.
	  1: destruct k; [easy|];
	     destruct k; [easy|];
		   cbn; destruct (k + 1) eqn:e; lia.
	  destruct k; [lia|].
	  replace (S k - 1) with k by lia.
	  unfold top_to_bottom_perm.
	  replace (S (S (S n)) <=? S k) with (S (S n) <=? k) by bdestshoweq.
	  replace (S k =? S (S (S n)) - 1) with (k =? S (S n) - 1) by bdestshoweq.
	  bdestruct (S (S n) <=? k).
	  + rewrite swap_permutation_WF; lia.
	  + bdestruct (k =? S (S n) - 1); [easy|].
	    rewrite swap_permutation_WF; lia.
Qed.

#[export] Hint Rewrite @perm_of_top_to_bottom_helper_eq : perm_of_zx_cleanup_db.

Lemma perm_of_top_to_bottom_eq {n} :
	perm_of_zx (top_to_bottom n) = top_to_bottom_perm n.
Proof.
	destruct n.
	- apply functional_extensionality; intros k.
	  easy.
	- simpl.
	  rewrite perm_of_top_to_bottom_helper_eq.
	  easy.
Qed.

#[export] Hint Rewrite @perm_of_top_to_bottom_eq : perm_of_zx_cleanup_db.

Lemma perm_of_zx_cast {n m n' m'} {zx : ZX n' m'} 
  (Hn : n = n') (Hm : m = m') :
  perm_of_zx (cast _ _ Hn Hm zx) = perm_of_zx zx.
Proof. subst. easy. Qed.

#[export] Hint Rewrite @perm_of_zx_cast : perm_of_zx_cleanup_db.

Lemma cast_transpose_eq {n0 m0 n1 m1} {zx} {Hn: n0 = n1} {Hm : m0 = m1} :
	(cast _ _ Hn Hm zx)⊤ = (cast _ _ Hm Hn zx⊤).
Proof. subst; easy. Qed.

Lemma perm_of_transpose_is_rinv {n} {zx} (H : ZX_Perm n zx) :
	(perm_of_zx zx ∘ perm_of_zx zx⊤)%prg = idn.
Proof.
	rewrite <- perm_of_zx_compose_spec.
	induction H; apply functional_extensionality; intros k; try easy.
	- cbn. 
	  destruct k; [easy|destruct k; [easy|]].
	  rewrite swap_permutation_WF; rewrite swap_permutation_WF; lia.
	- simpl.
	  rewrite stack_permutations_compose.
	  2,3: auto with perm_db zxperm_db.
	  rewrite <- 2!perm_of_zx_compose_spec.
	  rewrite IHZX_Perm1, IHZX_Perm2; cleanup_perm.
	- rewrite 2!perm_of_zx_compose_spec.
	  simpl.
	  rewrite <- Combinators.compose_assoc,
	  	(Combinators.compose_assoc _ _ _ _ (perm_of_zx zx1 ⊤)).
	  rewrite <- perm_of_zx_compose_spec, IHZX_Perm2, compose_idn_r.
	  rewrite <- perm_of_zx_compose_spec, IHZX_Perm1.
	  easy.
	- simpl. 
	  rewrite cast_transpose_eq, 2!perm_of_zx_cast.
	  rewrite <- perm_of_zx_compose_spec, IHZX_Perm.
	  easy.
Qed.

Lemma perm_of_transpose_is_linv {n} {zx} (H : ZX_Perm n zx) :
	(perm_of_zx zx⊤ ∘ perm_of_zx zx)%prg = idn.
Proof.
	pose proof (perm_of_transpose_is_rinv (transpose_ZX_Perm H)) as Hinv.
	rewrite <- transpose_involutive_eq in Hinv.
	easy.
Qed.

#[export] Hint Rewrite 
  @perm_of_transpose_is_rinv 
  @perm_of_transpose_is_linv : perm_of_zx_cleanup_db.

Lemma perm_of_bottom_to_top_eq n :
	perm_of_zx (bottom_to_top n) = bottom_to_top_perm n.
Proof.
  by_inverse_injective (top_to_bottom_perm n) n.
  rewrite <- perm_of_top_to_bottom_eq.
	unfold bottom_to_top.
  cleanup_perm_of_zx; auto with zxperm_db.
Qed.

#[export] Hint Rewrite perm_of_bottom_to_top_eq : perm_of_zx_cleanup_db.

Lemma perm_of_kcompose_top_to_bot_eq_rotr n k :
	perm_of_zx (n_compose k (top_to_bottom n)) =
	rotr n k.
Proof.
	induction k; simpl; try rewrite IHk; cleanup_perm_of_zx; easy.
Qed.

Lemma perm_of_kcompose_bot_to_top_eq_rotl n k :
	perm_of_zx (n_compose k (bottom_to_top n)) =
	rotl n k.
Proof.
	induction k; simpl; try rewrite IHk; cleanup_perm_of_zx; easy.
Qed.

#[export] Hint Rewrite 
  perm_of_kcompose_top_to_bot_eq_rotr
  perm_of_kcompose_bot_to_top_eq_rotl : perm_of_zx_cleanup_db.

(* We can prove the rest (and really, whatever we want) easily. 
   The main results are secitoned here so they don't overlap 
   with the (same) proofs in SwapRules.v *)

Lemma perm_of_top_to_bottom_1 n :
	perm_of_zx (top_to_bottom (S n)) = perm_of_zx (n_compose n (bottom_to_top (S n))).
Proof.
    cleanup_perm_of_zx.
	destruct n; [rewrite rotr_n, rotl_0_r; easy|].
	rewrite rotr_eq_rotl_sub.
	rewrite Nat.mod_small; [f_equal|]; lia.
Qed.

Lemma perm_of_n_compose_n_top_to_bottom n :
	perm_of_zx (n_compose n (top_to_bottom n)) = perm_of_zx (n_wire n).
Proof.
	cleanup_perm_of_zx.
	easy.
Qed.

#[export] Hint Rewrite perm_of_n_compose_n_top_to_bottom : perm_of_zx_cleanup_db.

Close Scope nat.
Close Scope prg.

(* For possible future expansion to other things: you can easily prove
  perm_of_zx (n_compose k zx) = ncompose k (perm_of_zx zx) 
  (for zx a ZX_Perm, that is)

Fixpoint ncompose {T} (n : nat) (f : T -> T) : T -> T :=
	match n with
	| 0 => fun x => x
	| S n' => (f ∘ (ncompose n' f))%prg
	end.

Fixpoint ncompose_eval {T} (n : nat) (f : T -> T) (t : T) : T :=
	match n with 
	| 0 => t
	| S n' => f (ncompose_eval n' f t)
	end.

Lemma ncompose_eq {T} (n:nat) (f:T -> T) :
	ncompose n f = fun t => ncompose_eval n f t.
Proof.
	induction n.
	- easy.
	- simpl. unfold compose.
	  rewrite IHn.
	  easy.
Qed.

Lemma ncompose_eq' {T} (n:nat) (f:T -> T) {t}:
	ncompose n f t = ncompose_eval n f t.
Proof.
	rewrite ncompose_eq.
	easy.
Qed. *)

Local Close Scope nat.
Local Close Scope prg.
