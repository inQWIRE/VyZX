Require Export PermutationDefinitions.
Require Import PermutationAutomation. 
Require Import CoreData.StrongInduction.


Local Open Scope nat.
Local Open Scope prg.



(* Section for prelude lemmas that don't directly involve permutations *)
(* TODO: Prove these: *)
(* 
Lemma bdd_of_is_inj_is_surj n f :
  (forall k, k < n -> exists k', k' < n /\ f k' = k) -> 
  (forall k l, k < n -> l < n -> f k = f l -> k = l) ->
  forall k, k < n -> f k < n.
Proof.
  Abort.

Lemma surj_of_is_bdd_is_inj n f : 
  forall k, k < n -> f k < n ->
  (forall k l, k < n -> l < n -> f k = f l -> k = l) ->
  (forall k, k < n -> exists k', k' < n /\ f k' = k).
Proof.
  Abort.

Lemma inj_of_is_surj_is_bdd n f :
  (forall k, k < n -> exists k', k' < n /\ f k' = k) -> 
  forall k, k < n -> f k < n ->
  (forall k l, k < n -> l < n -> f k = f l -> k = l).
Proof.
  Abort. 
*)




(* Section on general permutation properties *)
Lemma permutation_is_surjective {n f} : permutation n f ->
  forall k, k < n -> exists k', k' < n /\ f k' = k.
Proof.
  intros Hf k Hk.
  destruct Hf as [finv Hfinv].
  specialize (Hfinv k Hk).
  exists (finv k).
  intuition.
Qed.

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

Lemma linv_WF_of_WF {n} {f finv}
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
  pose proof (linv_WF_of_WF HWF Hinv) as HWFinv.
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
	pose proof (linv_WF_of_WF HfWF Hfinv) as HfinvWF.
	pose proof (linv_WF_of_WF HfWF Hfinv') as Hfinv'WF.
	bdestruct (n <=? k).
	- rewrite HfinvWF, Hfinv'WF; easy.
	- destruct Hf as [fi Hfi].
	  specialize (Hfi k H).
	  apply_f Hfinv (fi k); apply_f Hfinv' (fi k). 
	  replace (f (fi k)) with k in * by easy.
	  rewrite Hfinv, Hfinv'.
	  easy.
Qed.

(* FIXME: TODO: This is *really* not where this goes! But right now, it needs to. *)
Ltac by_inverse_injective f n :=
  apply (WF_permutation_inverse_injective f n); [
    tryeasylia; auto with perm_db |
    tryeasylia; auto with perm_WF_db |
    try solve [cleanup_perm; auto] |
    try solve [cleanup_perm; auto]]; tryeasylia.

Lemma permutation_of_le_permutation_WF f m n : (m <= n)%nat -> permutation m f ->
  perm_WF m f -> permutation n f.
Proof.
  intros Hmn [finv_m Hfinv_m] HWF.
  exists (fun k => if m <=? k then k else finv_m k).
  intros k Hk.
  bdestruct (m <=? k).
  - rewrite HWF; destruct_if_solve.
  - specialize (Hfinv_m _ H).
    repeat split; destruct_if_solve.
Qed.

Lemma compose_WF n f g : perm_WF n f -> perm_WF n g -> 
  perm_WF n (f ∘ g).
Proof.
  unfold compose.
  intros Hf Hg k Hk.
  rewrite Hg, Hf; easy.
Qed.

Global Hint Resolve compose_WF : perm_WF_db.





(* Section on perm_inv *)
Lemma perm_inv_bdd_S n f k : 
  perm_inv (S n) f k < S n.
Proof.
  induction n; simpl;
  [destruct_if_solve|]. 
  destruct_if; [|transitivity (S n); [apply IHn|]]. 
  all: apply Nat.lt_succ_diag_r.
Qed.

Lemma perm_inv_bdd n f k : k < n ->
  perm_inv n f k < n.
Proof.
  induction n.
  - easy.
  - intros. apply perm_inv_bdd_S.
Qed.

Global Hint Resolve perm_inv_bdd_S perm_inv_bdd : perm_bdd_db.

Lemma perm_inv_is_linv_of_inj {n f} : 
  (forall k l, k < n -> l < n -> f k = f l -> k = l) ->
  forall k, k < n -> 
  perm_inv n f (f k) = k.
Proof.
  intros Hinj k Hk.
  induction n.
  - easy.
  - simpl.
    bdestruct (f n =? f k).
    + apply Hinj; lia.
    + assert (k <> n) by (intros Heq; subst; easy).
      apply IHn; [auto|].
      assert (k <> n) by (intros Heq; subst; easy).
      lia.
Qed.

Lemma perm_inv_is_rinv_of_surj {n f} k :
  (exists l, l < n /\ f l = k) ->
  f (perm_inv n f k) = k.
Proof.
  induction n.
  - intros []; easy.
  - intros [l [Hl Hfl]].
    simpl.
    bdestruct (f n =? k); [easy|].
    apply IHn.
    exists l.
    split; [|easy].
    bdestruct (l =? n); [subst; easy|].
    lia.
Qed.

Lemma perm_inv_is_linv_of_permutation n f : permutation n f ->
  forall k, k < n -> perm_inv n f (f k) = k.
Proof.
  intros Hperm.
  apply perm_inv_is_linv_of_inj, permutation_is_injective, Hperm.
Qed.

Lemma perm_inv_is_rinv_of_permutation n f : permutation n f ->
  forall k, k < n -> f (perm_inv n f k) = k.
Proof.
  intros Hperm k Hk.
  apply perm_inv_is_rinv_of_surj, (permutation_is_surjective Hperm _ Hk).
Qed.

Lemma perm_inv_is_inv_of_is_surj_is_inj_is_bdd n f :
  (forall k, k < n -> exists k', k' < n /\ f k' = k) -> 
  (forall k l, k < n -> l < n -> f k = f l -> k = l) ->
  (forall k, k < n -> f k < n) ->
  (forall k, k < n -> 
    f k < n /\ perm_inv n f k < n /\ perm_inv n f (f k) = k /\ f (perm_inv n f k) = k).
Proof.
  intros Hsurj Hinj Hbdd.
  intros k Hk; repeat split.
  - apply Hbdd, Hk.
  - apply perm_inv_bdd, Hk.
  - rewrite perm_inv_is_linv_of_inj; easy.
  - rewrite perm_inv_is_rinv_of_surj; [easy|].
    apply Hsurj; easy.
Qed.








(* Section on stack_perms *)
Lemma stack_perms_left {n0 n1} {f g} {k} :
  k < n0 -> stack_perms n0 n1 f g k = f k.
Proof.
  intros Hk.
  unfold stack_perms.
  bdest_lia_replace (k <? n0) true.
  easy.
Qed.

Lemma stack_perms_right {n0 n1} {f g} {k} :
  n0 <= k < n0 + n1 -> stack_perms n0 n1 f g k = g (k - n0) + n0.
Proof.
  intros Hk.
  unfold stack_perms.
  bdest_lia_replace (k <? n0) false.
  bdest_lia_replace (k <? n0 + n1) true.
  easy.
Qed.

Lemma stack_perms_right_add {n0 n1} {f g} {k} :
  k < n1 -> stack_perms n0 n1 f g (k + n0) = g k + n0.
Proof.
  intros Hk.
  rewrite stack_perms_right; [|lia].
  replace (k + n0 - n0) with k by lia.
  easy.
Qed.

Lemma stack_perms_add_right {n0 n1} {f g} {k} :
  k < n1 -> stack_perms n0 n1 f g (n0 + k) = g k + n0.
Proof.
  rewrite Nat.add_comm.
  exact stack_perms_right_add.
Qed.

Lemma stack_perms_high {n0 n1} {f g} {k} :
	n0 + n1 <= k -> (stack_perms n0 n1 f g) k = k.
Proof.
	intros H.
	unfold stack_perms.
	bdest_lia_replace (k <? n0) false. 
	bdest_lia_replace (k <? n0 + n1) false.
	easy.
Qed.

Lemma stack_perms_f_idn n0 n1 f :
	stack_perms n0 n1 f idn = fun k => if k <? n0 then f k else k.
Proof. solve_stack_perm n0 n1. Qed. 

Lemma stack_perms_idn_f n0 n1 f : 
	stack_perms n0 n1 idn f = 
	fun k => if (¬ k <? n0) && (k <? n0 + n1) then f (k - n0) + n0 else k.
Proof. solve_stack_perm n0 n1. Qed. 

Lemma stack_perms_idn_idn n0 n1 :
	stack_perms n0 n1 idn idn = idn.
Proof. solve_stack_perm n0 n1. Qed.

#[export] Hint Rewrite stack_perms_idn_idn : perm_cleanup_db.

Lemma stack_perms_compose {n0 n1} {f g} {f' g'} 
	(Hf' : permutation n0 f') (Hg' : permutation n1 g') :
	(stack_perms n0 n1 f g ∘ stack_perms n0 n1 f' g'
	= stack_perms n0 n1 (f ∘ f') (g ∘ g'))%prg.
Proof.
	destruct Hf' as [Hf'inv Hf'].
	destruct Hg' as [Hg'inv Hg'].
	unfold compose.
	(* destruct_if. *)
	solve_stack_perm_strong n0 n1.
	1,2: specialize (Hf' k H); lia.
	- f_equal; f_equal. lia.
	- assert (Hk: k - n0 < n1) by lia.
	  specialize (Hg' _ Hk); lia.
Qed.

Lemma stack_perms_assoc {n0 n1 n2} {f g h} :
  stack_perms (n0 + n1) n2 (stack_perms n0 n1 f g) h =
  stack_perms n0 (n1 + n2) f (stack_perms n1 n2 g h).
Proof.
  apply functional_extensionality; intros k.
  unfold stack_perms.
  destruct_if_solve.
  rewrite (Nat.add_comm n0 n1), Nat.add_assoc.
  f_equal; f_equal; f_equal.
  lia.
Qed.

Lemma stack_perms_idn_of_left_right_idn {n0 n1} {f g} 
  (Hf : forall k, k < n0 -> f k = k) (Hg : forall k, k < n1 -> g k = k) :
  stack_perms n0 n1 f g = idn.
Proof.
  solve_stack_perm n0 n1.
  - apply Hf; easy.
  - rewrite Hg; lia.
Qed.







(* Section on rotr / rotl *)
(* FIXME: Decide whether/how to put this back where it goes in PermutationInstances *)
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


(* This is the start of the actual section *)
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




Local Close Scope nat.
Local Close Scope prg.

