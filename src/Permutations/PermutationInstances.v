Require Export PermutationFacts.
Require Import PermutationAutomation.
Require Import ZXperm.


Local Open Scope nat.
Local Open Scope prg.

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


Local Close Scope nat.
Local Close Scope prg.
