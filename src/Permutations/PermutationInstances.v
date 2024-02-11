Require Export PermutationFacts.
Require Import PermutationAutomation.
Require Import ZXperm.


Local Open Scope nat.
Local Open Scope prg.



Lemma idn_permutation n : permutation n idn.
Proof. exists idn. easy. Qed.

Global Hint Resolve idn_permutation : perm_db.



(* Section for swap_2_perm *)
Lemma swap_2_perm_inv : 
  swap_2_perm ∘ swap_2_perm = idn.
Proof.
  apply functional_extensionality; intros k.
  repeat first [easy | destruct k].
Qed.

#[export] Hint Rewrite swap_2_perm_inv : perm_inv_db.

Lemma swap_2_perm_bdd k :
  k < 2 -> swap_2_perm k < 2.
Proof.
  intros Hk.
  repeat first [easy | destruct k | cbn; lia].
Qed.

#[export] Hint Resolve swap_2_perm_bdd : perm_bdd_db.

Lemma swap_2_WF_perm k : 1 < k -> swap_2_perm k = k.
Proof.
  intros. 
  repeat first [easy | lia | destruct k].
Qed.

Global Hint Resolve swap_2_WF_perm : WF_perm_db.

Lemma swap_2_perm_permutation : permutation 2 swap_2_perm.
Proof. 
  perm_by_inverse swap_2_perm.
Qed.

Global Hint Resolve swap_2_perm_permutation : perm_db.










(* Section for stack_perms *)
Lemma stack_perms_WF_idn {n0 n1} {f} 
	(H : forall k, n0 <= k -> f k = k): 
	stack_perms n0 n1 f idn = f.
Proof.
	solve_modular_permutation_equalities;
	rewrite H; lia.
Qed.

Lemma stack_perms_WF {n0 n1} {f g} k :
  n0 + n1 <= k -> stack_perms n0 n1 f g k = k.
Proof.
  intros H.
  unfold stack_perms.
  bdestructΩ'.
Qed.

Global Hint Resolve stack_perms_WF : WF_perm_db.

Lemma stack_perms_bdd {n0 n1} {f g}
  (Hf : forall k, k < n0 -> f k < n0) (Hg : forall k, k < n1 -> g k < n1) :
  forall k, k < n0 + n1 -> stack_perms n0 n1 f g k < n0 + n1.
Proof.
  intros k Hk.
  unfold stack_perms.
  bdestruct (k <? n0).
  - specialize (Hf k H). lia.
  - bdestruct (k <? n0 + n1); [|easy].
    assert (Hkn0 : k - n0 < n1) by lia.
    specialize (Hg _ Hkn0). lia.
Qed. 

Global Hint Resolve stack_perms_bdd : perm_bdd_db.

Lemma stack_perms_rinv {n0 n1} {f g} {finv ginv}
  (Hf: forall k, k < n0 -> (f k < n0 /\ finv k < n0 /\ finv (f k) = k /\ f (finv k) = k))
  (Hg: forall k, k < n1 -> (g k < n1 /\ ginv k < n1 /\ ginv (g k) = k /\ g (ginv k) = k)) : 
  stack_perms n0 n1 f g ∘ stack_perms n0 n1 finv ginv = idn.
Proof.
  unfold compose.
  solve_modular_permutation_equalities.
  1-3: specialize (Hf _ H); lia.
  - replace (ginv (k - n0) + n0 - n0) with (ginv (k - n0)) by lia.
    assert (Hkn0: k - n0 < n1) by lia.
    specialize (Hg _ Hkn0).
    lia.
  - assert (Hkn0: k - n0 < n1) by lia.
    specialize (Hg _ Hkn0).
    lia.
Qed.

Lemma stack_perms_linv {n0 n1} {f g} {finv ginv}
  (Hf: forall k, k < n0 -> (f k < n0 /\ finv k < n0 /\ finv (f k) = k /\ f (finv k) = k))
  (Hg: forall k, k < n1 -> (g k < n1 /\ ginv k < n1 /\ ginv (g k) = k /\ g (ginv k) = k)) : 
  stack_perms n0 n1 finv ginv ∘ stack_perms n0 n1 f g = idn.
Proof.
  rewrite stack_perms_rinv.
  2,3: rewrite is_inv_iff_inv_is.
  all: easy.
Qed.

#[export] Hint Rewrite @stack_perms_rinv @stack_perms_linv : perm_inv_db.

Lemma stack_perms_permutation {n0 n1 f g} (Hf : permutation n0 f) (Hg: permutation n1 g) :
  permutation (n0 + n1) (stack_perms n0 n1 f g).
Proof.
  destruct Hf as [f' Hf'].
  destruct Hg as [g' Hg'].
  perm_by_inverse (stack_perms n0 n1 f' g').
  1,2: apply stack_perms_bdd; try easy; intros k' Hk'; 
       try specialize (Hf' _ Hk'); try specialize (Hg' _ Hk'); easy.
  1,2: rewrite is_inv_iff_inv_is; easy.
Qed.

Global Hint Resolve stack_perms_permutation : perm_db.










(* Section on rotr/rotl *)
(* Lemma rotr_WF {n m} : 
	forall k, n <= k -> (rotr n m) k = k.
Proof. intros. unfold rotr. bdestruct_one; lia. Qed.

Lemma rotl_WF {n m} : 
	forall k, n <= k -> (rotl n m) k = k.
Proof. intros. unfold rotl. bdestruct_one; lia. Qed.

Global Hint Resolve rotr_WF rotl_WF : WF_perm_db.

Lemma rotr_bdd {n m} : 
	forall k, k < n -> (rotr n m) k < n.
Proof.
	intros. unfold rotr. bdestruct_one; [lia|].
	apply Nat.mod_upper_bound; lia.
Qed.

Lemma rotl_bdd {n m} : 
	forall k, k < n -> (rotl n m) k < n.
Proof.
	intros. unfold rotl. bdestruct_one; [lia|].
	apply Nat.mod_upper_bound; lia.
Qed.

Global Hint Resolve rotr_bdd rotl_bdd : perm_bdd_db.

Lemma rotr_rotl_inv n m :
	((rotr n m) ∘ (rotl n m) = idn)%prg.
Proof.
	apply functional_extensionality; intros k.
	unfold compose, rotl, rotr.
	bdestruct (n <=? k); [bdestructΩ'|].
	assert (Hn0 : n <> 0) by lia.
	bdestruct_one.
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
	bdestruct (n <=? k); [bdestructΩ'|].
	assert (Hn0 : n <> 0) by lia.
	bdestruct_one.
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

Global Hint Resolve rotr_perm rotl_perm : perm_db. *)

















(* Section on top_to_bottom and bottom_to_top *)
Lemma bottom_to_top_perm_bdd {n} k : 
	k < n -> bottom_to_top_perm n k < n.
Proof.
	intros Hk.
	unfold bottom_to_top_perm.
	replace_bool_lia (n <=? k) false.
	destruct k; lia.
Qed.

Lemma top_to_bottom_perm_bdd {n} k :
	k < n -> top_to_bottom_perm n k < n.
Proof.
	intros Hk.
	unfold top_to_bottom_perm.
	replace_bool_lia (n <=? k) false.
	bdestruct (k =? n - 1); lia.
Qed.

Global Hint Resolve bottom_to_top_perm_bdd top_to_bottom_perm_bdd : perm_bdd_db.

Lemma bottom_to_top_WF_perm {n} k : n <= k ->
	bottom_to_top_perm n k = k.
Proof.
	intros Hk.
	unfold bottom_to_top_perm.
	replace_bool_lia (n <=? k) true.
	easy.
Qed.

Lemma top_to_bottom_WF_perm {n} k : n <= k ->
	top_to_bottom_perm n k = k.
Proof.
	intros Hk.
	unfold top_to_bottom_perm.
	replace_bool_lia (n <=? k) true.
	easy.
Qed.
	
Global Hint Resolve bottom_to_top_WF_perm top_to_bottom_WF_perm : WF_perm_db.

Lemma bottom_to_top_to_bottom_inv n : 
	bottom_to_top_perm n ∘ top_to_bottom_perm n = idn.
Proof.
	apply functional_extensionality; intros k.
	unfold compose, bottom_to_top_perm, top_to_bottom_perm.
	bdestruct (n <=? k).
	1: replace_bool_lia (n <=? k) true; easy.
	bdestruct (k =? n - 1).
	- destruct n.
	  + easy.
	  + replace_bool_lia (S n <=? 0) false.
	  	lia.
	- replace_bool_lia (n <=? k + 1) false.
	  replace (k + 1) with (S k) by lia.
	  easy.
Qed.

Lemma top_to_bottom_to_top_inv n :
	top_to_bottom_perm n ∘ bottom_to_top_perm n = idn.
Proof.
	apply functional_extensionality; intros k.
	unfold compose, bottom_to_top_perm, top_to_bottom_perm.
	bdestruct (n <=? k).
	1: replace_bool_lia (n <=? k) true; easy.
	destruct k.
	- destruct n; [easy|].
	  replace_bool_lia (S n <=? S n - 1) false.
	  rewrite Nat.eqb_refl.
	  easy.
	- replace_bool_lia (n <=? k) false.
	  replace_bool_lia (k =? n - 1) false.
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


Lemma top_to_bottom_perm_eq_rotr n :
	top_to_bottom_perm n = rotr n 1.
Proof.
	apply functional_extensionality; intros k.
	unfold top_to_bottom_perm, rotr.
	bdestructΩ'.
	- subst. 
	  replace (n - 1 + 1) with n by lia.
	  rewrite Nat.mod_same; lia.
	- rewrite Nat.mod_small; lia.
Qed.

#[export] Hint Rewrite top_to_bottom_perm_eq_rotr : perm_cleanup_db.

Lemma bottom_to_top_perm_eq_rotl n :
	bottom_to_top_perm n = rotl n 1.
Proof.
  perm_eq_by_WF_inv_inj (top_to_bottom_perm n) n.
Qed.

#[export] Hint Rewrite bottom_to_top_perm_eq_rotl : perm_cleanup_db.

(* Section for a_perm *)
(* TODO: Add. *)






Local Close Scope nat.
Local Close Scope prg.
