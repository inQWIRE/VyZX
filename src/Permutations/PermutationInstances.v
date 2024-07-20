Require Import PermutationAuxiliary.
Require Export PermutationFacts.
Require Import PermutationAutomation.


Local Open Scope nat.
Local Open Scope prg.





(* Section for swap_2_perm *)
Lemma swap_2_perm_invol : 
  swap_2_perm ∘ swap_2_perm = idn.
Proof.
  apply functional_extensionality; intros k.
  repeat first [easy | destruct k].
Qed.

#[export] Hint Rewrite swap_2_perm_invol : perm_inv_db.

Lemma swap_2_perm_bounded k :
  k < 2 -> swap_2_perm k < 2.
Proof.
  intros Hk.
  repeat first [easy | destruct k | cbn; lia].
Qed.

#[export] Hint Resolve swap_2_perm_bounded : perm_bounded_db.

Lemma swap_2_WF k : 1 < k -> swap_2_perm k = k.
Proof.
  intros. 
  repeat first [easy | lia | destruct k].
Qed.

Lemma swap_2_WF_Perm : WF_Perm 2 swap_2_perm.
Proof.
  intros k. 
  repeat first [easy | lia | destruct k].
Qed.

Global Hint Resolve swap_2_WF_Perm : WF_Perm_db.

Lemma swap_2_perm_permutation : permutation 2 swap_2_perm.
Proof. 
  perm_by_inverse swap_2_perm.
Qed.

Global Hint Resolve swap_2_perm_permutation : perm_db.

Lemma swap_2_perm_inv :
	perm_eq 2 
  (perm_inv 2 swap_2_perm) swap_2_perm.
Proof.
	perm_eq_by_inv_inj swap_2_perm 2.
Qed.

Lemma swap_2_perm_inv' :
	perm_inv' 2 swap_2_perm = swap_2_perm.
Proof.
	permutation_eq_by_WF_inv_inj swap_2_perm 2.
Qed.

#[export] Hint Resolve swap_2_perm_inv : perm_inv_db.
#[export] Hint Rewrite swap_2_perm_inv' : perm_inv_db.







(* Section for stack_perms *)
Lemma stack_perms_WF_idn n0 n1 f 
	(H : WF_Perm n0 f) : 
	stack_perms n0 n1 f idn = f.
Proof.
	solve_modular_permutation_equalities;
	rewrite H; lia.
Qed.

#[export] Hint Rewrite stack_perms_WF_idn 
	using (solve [auto with WF_Perm_db]) : perm_inv_db.

Lemma stack_perms_WF n0 n1 f g :
	WF_Perm (n0 + n1) (stack_perms n0 n1 f g).
Proof.
  intros k Hk.
  unfold stack_perms.
  bdestructΩ'.
Qed.

Global Hint Resolve stack_perms_WF : WF_Perm_db.

Lemma stack_perms_bounded {n0 n1} {f g} : 
	perm_bounded n0 f -> perm_bounded n1 g ->
  perm_bounded (n0 + n1) (stack_perms n0 n1 f g).
Proof.
	intros Hf Hg.
  intros k Hk.
  unfold stack_perms.
  bdestruct (k <? n0).
  - specialize (Hf k H). lia.
  - bdestruct (k <? n0 + n1); [|easy].
    assert (Hkn0 : k - n0 < n1) by lia.
    specialize (Hg _ Hkn0). lia.
Qed. 

#[export] Hint Resolve stack_perms_bounded : perm_bounded_db.

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

Lemma stack_perms_perm_eq_inv_of_perm_eq_inv {n0 n1} {f g} {finv ginv}
  (Hf : perm_eq n0 (f ∘ finv) idn) 
	(Hg : perm_eq n1 (g ∘ ginv) idn) 
	(Hfinv : perm_bounded n0 finv)
	(Hginv : perm_bounded n1 ginv) :
	perm_eq (n0 + n1) 
	(stack_perms n0 n1 f g ∘ stack_perms n0 n1 finv ginv)
	idn.
Proof.
  unfold compose in *.
	intros k Hk.
	unfold stack_perms.
	specialize (Hfinv k).
	specialize (Hginv (k - n0)).
	bdestructΩ'; auto.
	rewrite Nat.add_sub.
	rewrite Hg; lia.
Qed.

#[export] Hint Resolve stack_perms_perm_eq_inv_of_perm_eq_inv : perm_inv_db.

Lemma stack_perms_inv_of_perm_eq_inv {n0 n1} {f g} {finv ginv}
  (Hf : perm_eq n0 (f ∘ finv) idn) 
	(Hg : perm_eq n1 (g ∘ ginv) idn) 
	(Hfinv : perm_bounded n0 finv)
	(Hginv : perm_bounded n1 ginv) :
	stack_perms n0 n1 f g ∘ stack_perms n0 n1 finv ginv = idn.
Proof.
	eq_by_WF_perm_eq (n0 + n1).
	auto with perm_inv_db.
Qed.

#[export] Hint Resolve stack_perms_inv_of_perm_eq_inv : perm_inv_db.

#[export] Hint Resolve permutation_is_bounded : perm_bounded_db.

Lemma stack_perms_permutation {n0 n1 f g} (Hf : permutation n0 f) (Hg: permutation n1 g) :
  permutation (n0 + n1) (stack_perms n0 n1 f g).
Proof.
  perm_by_inverse (stack_perms n0 n1 (perm_inv n0 f) (perm_inv n1 g)).
Qed.

#[export] Hint Resolve stack_perms_permutation : perm_db.

Lemma perm_inv_stack_perms n m f g 
  (Hf : permutation n f) (Hg : permutation m g) : 
  perm_eq (n + m)
  (perm_inv (n + m) (stack_perms n m f g))
  (stack_perms n m (perm_inv n f) (perm_inv m g)).
Proof.
  perm_eq_by_inv_inj (stack_perms n m f g) (n+m).
Qed.

#[export] Hint Resolve stack_perms_idn_of_left_right_idn 
	stack_perms_compose : perm_inv_db.
#[export] Hint Rewrite @stack_perms_compose 
	using auto with perm_db : perm_inv_db.



Lemma stack_perms_proper {n0 n1} {f f' g g'} 
  (Hf : perm_eq n0 f f') (Hg : perm_eq n1 g g') : 
  perm_eq (n0 + n1) 
    (stack_perms n0 n1 f g)
    (stack_perms n0 n1 f' g').
Proof.
  intros k Hk.
  unfold stack_perms.
  bdestructΩ'; [apply Hf | f_equal; apply Hg]; lia.
Qed.

#[export] Hint Resolve stack_perms_proper : perm_inv_db.

Lemma stack_perms_proper_eq {n0 n1} {f f' g g'} 
  (Hf : perm_eq n0 f f') (Hg : perm_eq n1 g g') : 
  stack_perms n0 n1 f g =
  stack_perms n0 n1 f' g'.
Proof.
  eq_by_WF_perm_eq (n0 + n1); cleanup_perm_inv.
Qed.

#[export] Hint Resolve stack_perms_proper_eq : perm_inv_db.

Lemma perm_inv'_stack_perms n m f g 
  (Hf : permutation n f) (Hg : permutation m g) : 
  perm_inv' (n + m) (stack_perms n m f g) = 
  stack_perms n m (perm_inv' n f) (perm_inv' m g).
Proof.
  permutation_eq_by_WF_inv_inj (stack_perms n m f g) (n+m).
Qed.

#[export] Hint Rewrite @perm_inv'_stack_perms 
	using auto with perm_db : perm_inv_db.

Lemma rotr_inv n m : 
	perm_eq n (perm_inv n (rotr n m)) (rotl n m).
Proof.
	perm_eq_by_inv_inj (rotr n m) n.
Qed.

Lemma rotr_inv' n m : 
	perm_inv' n (rotr n m) = rotl n m.
Proof.
	permutation_eq_by_WF_inv_inj (rotr n m) n.
Qed.

Lemma rotl_inv n m : 
	perm_eq n (perm_inv n (rotl n m)) (rotr n m).
Proof.
	perm_eq_by_inv_inj (rotl n m) n.
Qed.

Lemma rotl_inv' n m : 
	perm_inv' n (rotl n m) = rotr n m.
Proof.
	permutation_eq_by_WF_inv_inj (rotl n m) n.
Qed.

#[export] Hint Resolve rotr_inv rotl_inv : perm_inv_db.
#[export] Hint Rewrite rotr_inv rotr_inv' rotl_inv rotl_inv' : perm_inv_db.









(* Section on top_to_bottom and bottom_to_top *)
Lemma bottom_to_top_perm_bounded {n} k : 
	k < n -> bottom_to_top_perm n k < n.
Proof.
	intros Hk.
	unfold bottom_to_top_perm.
	replace_bool_lia (n <=? k) false.
	destruct k; lia.
Qed.

Lemma top_to_bottom_perm_bounded {n} k :
	k < n -> top_to_bottom_perm n k < n.
Proof.
	intros Hk.
	unfold top_to_bottom_perm.
	replace_bool_lia (n <=? k) false.
	bdestruct (k =? n - 1); lia.
Qed.

Global Hint Resolve bottom_to_top_perm_bounded top_to_bottom_perm_bounded : perm_bounded_db.

Lemma bottom_to_top_WF_perm n :
	WF_Perm n (bottom_to_top_perm n).
Proof.
	intros k Hk.
	unfold bottom_to_top_perm.
	replace_bool_lia (n <=? k) true.
	easy.
Qed.

Lemma top_to_bottom_WF_perm n : 
	WF_Perm n (top_to_bottom_perm n).
Proof.
	intros k Hk.
	unfold top_to_bottom_perm.
	replace_bool_lia (n <=? k) true.
	easy.
Qed.
	
Global Hint Resolve bottom_to_top_WF_perm top_to_bottom_WF_perm : WF_Perm_db.

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

Lemma bottom_to_top_to_bottom_inv' n k :
	bottom_to_top_perm n (top_to_bottom_perm n k) = k.
Proof.
	pose proof (bottom_to_top_to_bottom_inv n) as H.
	apply (f_equal (fun g => g k)) in H.
	unfold compose in H.
	easy.
Qed.

Lemma top_to_bottom_to_top_inv' n k :
	top_to_bottom_perm n (bottom_to_top_perm n k) = k.
Proof.
	pose proof (top_to_bottom_to_top_inv n) as H.
	apply (f_equal (fun g => g k)) in H.
	unfold compose in H.
	easy.
Qed.

#[export] Hint Rewrite 
  bottom_to_top_to_bottom_inv
  bottom_to_top_to_bottom_inv'
  top_to_bottom_to_top_inv
  top_to_bottom_to_top_inv'
  : perm_inv_db.

Lemma top_to_bottom_permutation n :
	permutation n (top_to_bottom_perm n).
Proof.
  perm_by_inverse (bottom_to_top_perm n).
Qed.

Lemma bottom_to_top_permutation n :
	permutation n (bottom_to_top_perm n). 
Proof.
	perm_by_inverse (top_to_bottom_perm n).
Qed.

Global Hint Resolve top_to_bottom_permutation bottom_to_top_permutation : perm_db.

Lemma top_to_bottom_inv n : 
	perm_eq n (perm_inv n (top_to_bottom_perm n)) (bottom_to_top_perm n).
Proof.
	perm_eq_by_inv_inj (top_to_bottom_perm n) n.
Qed.

Lemma bottom_to_top_inv n : 
	perm_eq n (perm_inv n (bottom_to_top_perm n)) (top_to_bottom_perm n).
Proof.
	perm_eq_by_inv_inj (bottom_to_top_perm n) n.
Qed.

Lemma top_to_bottom_inv' n : 
	perm_inv' n (top_to_bottom_perm n) = bottom_to_top_perm n.
Proof.
	permutation_eq_by_WF_inv_inj (top_to_bottom_perm n) n.
Qed.

Lemma bottom_to_top_inv' n : 
	perm_inv' n (bottom_to_top_perm n) = top_to_bottom_perm n.
Proof.
	permutation_eq_by_WF_inv_inj (bottom_to_top_perm n) n.
Qed.

#[export] Hint Rewrite top_to_bottom_inv top_to_bottom_inv'
	bottom_to_top_inv bottom_to_top_inv' : perm_inv_db.

Lemma top_to_bottom_perm_eq_rotr n :
	top_to_bottom_perm n = rotr n 1.
Proof.
	apply functional_extensionality; intros k.
	unfold top_to_bottom_perm, rotr.
	bdestructΩ'.
	- subst. 
	  replace (n - 1 + 1) with n by lia.
	  rewrite Nat.Div0.mod_same; lia.
	- rewrite Nat.mod_small; lia.
Qed.

#[export] Hint Rewrite top_to_bottom_perm_eq_rotr : perm_cleanup_db.

Lemma bottom_to_top_perm_eq_rotl n :
	bottom_to_top_perm n = rotl n 1.
Proof.
  permutation_eq_by_WF_inv_inj (top_to_bottom_perm n) n.
Qed.

#[export] Hint Rewrite bottom_to_top_perm_eq_rotl : perm_cleanup_db.




Definition kron_comm_perm p q :=
  fun k => if p * q <=? k then k else
  k mod p * q + k / p.

Lemma kron_comm_perm_WF p q : 
	WF_Perm (p * q) (kron_comm_perm p q).
Proof.
	intros k Hk; unfold kron_comm_perm; bdestructΩ'.
Qed.

Lemma kron_comm_perm_WF_alt p q : 
	WF_Perm (q * p) (kron_comm_perm p q).
Proof.
	rewrite Nat.mul_comm; apply kron_comm_perm_WF.
Qed.

#[export] Hint Resolve kron_comm_perm_WF kron_comm_perm_WF_alt : WF_Perm_db.

Lemma kron_comm_perm_bounded p q : 
	perm_bounded (p * q) (kron_comm_perm p q).
Proof.
	intros k Hk.
	unfold kron_comm_perm.
	bdestructΩ'.
	show_moddy_lt.
Qed.

Lemma kron_comm_perm_bounded_alt p q : 
	perm_bounded (q * p) (kron_comm_perm p q).
Proof.
	rewrite Nat.mul_comm.
	apply kron_comm_perm_bounded.
Qed.

#[export] Hint Resolve kron_comm_perm_bounded 
	kron_comm_perm_bounded_alt : perm_bounded_db.

Lemma kron_comm_perm_pseudo_invol_perm_eq p q : 
  perm_eq (p * q) (kron_comm_perm p q ∘ kron_comm_perm q p)%prg idn.
Proof.
	intros k Hk.
	unfold compose, kron_comm_perm.
	simplify_bools_lia_one_kernel.
	simplify_bools_moddy_lia_one_kernel.
	rewrite (Nat.add_comm _ (k/q)).
	rewrite Nat.Div0.mod_add, Nat.div_add by show_nonzero.
	rewrite Nat.Div0.div_div, Nat.mod_small by show_moddy_lt.
	rewrite (Nat.div_small k (q*p)) by lia.
	symmetry. 
	rewrite (Nat.div_mod_eq k q) at 1; lia.
Qed.

#[export] Hint Resolve kron_comm_perm_pseudo_invol_perm_eq : perm_inv_db.

Lemma kron_comm_perm_pseudo_invol_alt_perm_eq p q : 
  perm_eq (q * p) (kron_comm_perm p q ∘ kron_comm_perm q p)%prg idn.
Proof.
	rewrite Nat.mul_comm; cleanup_perm_inv.
Qed.

#[export] Hint Resolve kron_comm_perm_pseudo_invol_alt_perm_eq : perm_inv_db.

Lemma kron_comm_perm_pseudo_invol p q : 
	kron_comm_perm p q ∘ kron_comm_perm q p = idn.
Proof.
	eq_by_WF_perm_eq (p*q); cleanup_perm_inv.
Qed.

#[export] Hint Rewrite kron_comm_perm_pseudo_invol : perm_inv_db.

Lemma kron_comm_perm_permutation p q : 
	permutation (p * q) (kron_comm_perm p q).
Proof.
	perm_by_inverse (kron_comm_perm q p).
Qed.

Lemma kron_comm_perm_permutation_alt p q : 
	permutation (q * p) (kron_comm_perm p q).
Proof.
	perm_by_inverse (kron_comm_perm q p).
Qed.

#[export] Hint Resolve kron_comm_perm_permutation 
	kron_comm_perm_permutation_alt : perm_db.

Lemma kron_comm_perm_inv p q : 
	perm_eq (p * q) 
		(perm_inv (p * q) (kron_comm_perm p q))
		(kron_comm_perm q p).
Proof.
	perm_eq_by_inv_inj (kron_comm_perm p q) (p * q).
Qed.

Lemma kron_comm_perm_inv_alt p q : 
	perm_eq (q * p) 
		(perm_inv (p * q) (kron_comm_perm p q))
		(kron_comm_perm q p).
Proof.
	perm_eq_by_inv_inj (kron_comm_perm p q) (q * p).
Qed.

Lemma kron_comm_perm_swap_inv p q : 
	perm_eq (p * q) 
		(perm_inv (p * q) (kron_comm_perm q p))
		(kron_comm_perm p q).
Proof.
	perm_eq_by_inv_inj (kron_comm_perm q p) (p * q).
Qed.

Lemma kron_comm_perm_swap_inv_alt p q : 
	perm_eq (q * p) 
		(perm_inv (p * q) (kron_comm_perm q p))
		(kron_comm_perm p q).
Proof.
	perm_eq_by_inv_inj (kron_comm_perm q p) (q * p).
Qed.

#[export] Hint Resolve kron_comm_perm_inv
	kron_comm_perm_inv_alt 
	kron_comm_perm_swap_inv 
	kron_comm_perm_swap_inv_alt : perm_inv_db.

Lemma kron_comm_perm_inv' p q : 
	perm_inv' (p * q) (kron_comm_perm p q) =
	kron_comm_perm q p.
Proof.
	eq_by_WF_perm_eq (p * q).
	cleanup_perm_inv.
Qed.

Lemma kron_comm_perm_inv'_alt p q : 
	perm_inv' (q * p) (kron_comm_perm p q) =
	kron_comm_perm q p.
Proof.
	eq_by_WF_perm_eq (q * p).
	cleanup_perm_inv.
Qed.

#[export] Hint Rewrite kron_comm_perm_inv'
	kron_comm_perm_inv'_alt : perm_inv_db.

#[export] Hint Resolve compose_WF_Perm : WF_Perm_db.

Lemma swap_block_perm_decomp_eq padl padr padm a : 
  swap_block_perm padl padm a = 
  stack_perms padl (a + padm + a + padr) idn 
    (stack_perms (a + padm + a) padr
     ((stack_perms (a + padm) a (rotr (a + padm) a) idn) ∘
     rotr (a + padm + a) (a + padm)) idn).
Proof.
  rewrite 2!stack_perms_WF_idn by 
		eauto using monotonic_WF_Perm with WF_Perm_db zarith.
  rewrite 2!rotr_decomp.
  pose proof (Nat.mod_small (a + padm) (a + padm + a)) as Hsm.
  pose proof (Nat.mod_small (a) (a + padm)) as Hsm'.
  pose proof (Nat.mod_upper_bound (a + padm) (a + padm + a)) as Hl.
  pose proof (Nat.mod_upper_bound (a) (a + padm)) as Hl'.
  assert (Hpadm0: padm = 0 -> a mod (a + padm) = 0) by 
    (intros ->; rewrite Nat.add_0_r, Nat.Div0.mod_same; easy).
  rewrite stack_perms_idn_f.
  unfold swap_block_perm.
  apply functional_extensionality; intros k.
  unfold compose.
  bdestruct (a =? 0); 
  [subst; 
  rewrite ?Nat.add_0_r, ?Nat.add_0_l, ?Nat.Div0.mod_same in *;
  bdestructΩ'|].
  rewrite Hsm in * by lia.
  bdestruct (padm =? 0);
  [subst; 
  rewrite ?Nat.add_0_r, ?Nat.add_0_l, ?Nat.Div0.mod_same in *;
  bdestructΩ'|].
  rewrite Hsm' in * by lia.
  bdestructΩ'.
Qed.



Lemma tensor_perms_bounded n0 n1 f g : 
	perm_bounded n0 f -> perm_bounded n1 g ->
	perm_bounded (n0 * n1) (tensor_perms n0 n1 f g).
Proof.
	intros Hf Hg k Hk.
	unfold tensor_perms.
	simplify_bools_lia_one_kernel.
	pose proof (Hf (k / n1) ltac:(show_moddy_lt)).
	pose proof (Hg (k mod n1) ltac:(show_moddy_lt)).
	show_moddy_lt.
Qed.

#[export] Hint Resolve tensor_perms_bounded : perm_bounded_db.

Lemma tensor_perms_WF n0 n1 f g :
	WF_Perm (n0 * n1) (tensor_perms n0 n1 f g).
Proof.
	intros k Hk.
	unfold tensor_perms.
	bdestructΩ'.
Qed.

#[export] Hint Resolve tensor_perms_WF : WF_Perm_db.
#[export] Hint Extern 100 (WF_Perm ?n01 (tensor_perms ?n0 ?n1 ?f ?g)) =>
	replace n01 with (n0 * n1) by nia : WF_Perm_db.

Lemma tensor_perms_compose n0 n1 f0 f1 g0 g1 : 
	perm_bounded n0 f1 -> perm_bounded n1 g1 ->
	tensor_perms n0 n1 f0 g0 ∘ tensor_perms n0 n1 f1 g1 = 
	tensor_perms n0 n1 (f0 ∘ f1) (g0 ∘ g1).
Proof.
	intros Hf1 Hg1.
	eq_by_WF_perm_eq (n0*n1).
	intros k Hk.
	unfold compose.
	generalize (tensor_perms_bounded n0 n1 f1 g1 Hf1 Hg1 k Hk).
	unfold tensor_perms.
	simplify_bools_lia_one_kernel.
	intros ?.
	simplify_bools_lia_one_kernel.
	rewrite Nat.div_add_l by lia.
	pose proof (Hf1 (k / n1) ltac:(show_moddy_lt)).
	pose proof (Hg1 (k mod n1) ltac:(show_moddy_lt)).
	rewrite (Nat.div_small (g1 _)), mod_add_l, Nat.mod_small by easy.
	now rewrite Nat.add_0_r.
Qed.

#[export] Hint Rewrite tensor_perms_compose : perm_cleanup_db perm_inv_db.

Lemma tensor_perms_0_l n1 f g : 
	tensor_perms 0 n1 f g = idn.
Proof.
	eq_by_WF_perm_eq (0 * n1).
Qed.

Lemma tensor_perms_0_r n0 f g : 
	tensor_perms n0 0 f g = idn.
Proof.
	eq_by_WF_perm_eq (n0 * 0).
	lia.
Qed.

#[export] Hint Rewrite tensor_perms_0_l 
	tensor_perms_0_r : perm_cleanup_db perm_inv_db.

Lemma tensor_perms_perm_eq_proper n0 n1 f f' g g' : 
	perm_eq n0 f f' -> perm_eq n1 g g' ->
	tensor_perms n0 n1 f g = tensor_perms n0 n1 f' g'.
Proof.
	intros Hf' Hg'.
	eq_by_WF_perm_eq (n0 * n1).
	intros k Hk.
	unfold tensor_perms.
	simplify_bools_lia_one_kernel.
	now rewrite Hf', Hg' by show_moddy_lt.
Qed.

#[export] Hint Resolve tensor_perms_perm_eq_proper : perm_inv_db.

Lemma tensor_perms_idn_idn n0 n1 :
	tensor_perms n0 n1 idn idn = idn.
Proof.
	eq_by_WF_perm_eq (n0 * n1).
	unfold tensor_perms.
	intros k Hk.
	simplify_bools_lia_one_kernel.
	pose proof (Nat.div_mod_eq k n1).
	lia.
Qed.

#[export] Hint Rewrite tensor_perms_idn_idn : perm_cleanup_db.

Lemma tensor_perms_idn_idn' n0 n1 f g :
	perm_eq n0 f idn -> perm_eq n1 g idn ->
	tensor_perms n0 n1 f g = idn.
Proof.
	intros Hf Hg.
	rewrite <- (tensor_perms_idn_idn n0 n1).
	cleanup_perm_inv.
Qed.

#[export] Hint Rewrite tensor_perms_idn_idn'
	using (solve [cleanup_perm_inv]) : perm_inv_db.

Lemma tensor_perms_permutation n0 n1 f g
	(Hf : permutation n0 f) (Hg : permutation n1 g) : 
	permutation (n0 * n1) (tensor_perms n0 n1 f g).
Proof.
	perm_by_inverse (tensor_perms n0 n1 (perm_inv n0 f) (perm_inv n1 g)).
Qed.

#[export] Hint Resolve tensor_perms_permutation : perm_db.

Lemma tensor_perms_inv n0 n1 f g 
	(Hf : permutation n0 f) (Hg : permutation n1 g) : 
	perm_eq (n0 * n1) 
		(perm_inv (n0 * n1) (tensor_perms n0 n1 f g))
		(tensor_perms n0 n1 (perm_inv n0 f) (perm_inv n1 g)).
Proof.
	perm_eq_by_inv_inj (tensor_perms n0 n1 f g) (n0*n1).
Qed.

#[export] Hint Resolve tensor_perms_inv : perm_inv_db.

Lemma tensor_perms_inv' n0 n1 f g 
	(Hf : permutation n0 f) (Hg : permutation n1 g) : 
	perm_inv' (n0 * n1) (tensor_perms n0 n1 f g) =
	tensor_perms n0 n1 (perm_inv' n0 f) (perm_inv' n1 g).
Proof.
	permutation_eq_by_WF_inv_inj (tensor_perms n0 n1 f g) (n0*n1).
Qed.

#[export] Hint Rewrite tensor_perms_inv' 
	using auto with perm_db : perm_inv_db.

#[export] Hint Extern 100 (WF_Perm ?npow2 (qubit_perm_to_nat_perm ?n _)) =>
	replace npow2 with (2^n) by (show_pow2_le + unify_pows_two; nia) 
		: WF_Perm_db.

Section qubit_perm_lemmas.

Import Bits.

Lemma qubit_perm_to_nat_perm_stack_perms n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
	perm_eq (2^n0 * 2^n1)
		(qubit_perm_to_nat_perm (n0 + n1) (stack_perms n0 n1 f g))
		(tensor_perms (2^n0) (2^n1)
			(qubit_perm_to_nat_perm n0 f)
			(qubit_perm_to_nat_perm n1 g)).
Proof.
	intros k Hk.
	unfold tensor_perms.
	simplify_bools_lia_one_kernel.
	unfold qubit_perm_to_nat_perm.
	rewrite funbool_to_nat_add_pow2_join.
	apply funbool_to_nat_eq.
	intros a Ha.
	unfold compose.
	bdestruct (a <? n0).
	- rewrite stack_perms_left by easy.
		now rewrite nat_to_funbool_div by cleanup_perm.
	- rewrite stack_perms_right by easy.
		now rewrite <- nat_to_funbool_mod by auto with perm_bounded_db zarith.
Qed.

Lemma qubit_perm_to_nat_perm_stack_perms_alt n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
	perm_eq (2^(n0 + n1))
		(qubit_perm_to_nat_perm (n0 + n1) (stack_perms n0 n1 f g))
		(tensor_perms (2^n0) (2^n1)
			(qubit_perm_to_nat_perm n0 f)	
			(qubit_perm_to_nat_perm n1 g)).
Proof.
	rewrite Nat.pow_add_r.
	now apply qubit_perm_to_nat_perm_stack_perms.
Qed.

Lemma qubit_perm_to_nat_perm_bounded n f : 
	perm_bounded (2 ^ n) (qubit_perm_to_nat_perm n f).
Proof.
	intros k Hk.
	unfold qubit_perm_to_nat_perm.
	apply funbool_to_nat_bound.
Qed.

End qubit_perm_lemmas.

#[export] Hint Resolve qubit_perm_to_nat_perm_bounded : perm_bounded_db.
#[export] Hint Resolve qubit_perm_to_nat_perm_stack_perms
	qubit_perm_to_nat_perm_stack_perms_alt : perm_inv_db.

Lemma rotr_add_l_eq n m :
	rotr (n + m) n = 
	(fun k => if n + m <=? k then k else
	if k <? m then k + n else k - m).
Proof.
	eq_by_WF_perm_eq (n + m);
	[intros k Hk; bdestructΩ'|].
	intros k Hk.
	unfold rotr.
	simplify_bools_lia_one_kernel.
	bdestructΩ';
	solve_simple_mod_eqns.
Qed.

Lemma rotr_add_r_eq n m :
	rotr (m + n) n = 
	(fun k => if m + n <=? k then k else
	if k <? m then k + n else k - m).
Proof.
	eq_by_WF_perm_eq (m + n);
	[intros k Hk; bdestructΩ'|].
	intros k Hk.
	unfold rotr.
	simplify_bools_lia_one_kernel.
	bdestructΩ';
	solve_simple_mod_eqns.
Qed.

Lemma stack_perms_rotr_natural n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
	stack_perms n0 n1 f g ∘ rotr (n0 + n1) n0 =
	rotr (n0 + n1) n0 ∘ stack_perms n1 n0 g f.
Proof.
	eq_by_WF_perm_eq (n0 + n1);
	[eauto using monotonic_WF_Perm with WF_Perm_db zarith|].
	intros k Hk.
	rewrite rotr_add_l_eq.
	unfold compose.
	assert (stack_perms n1 n0 g f k < n1 + n0) by 
		auto with perm_bounded_db zarith.
	do 2 simplify_bools_lia_one_kernel.
	bdestruct (k <? n1).
	- rewrite stack_perms_right, stack_perms_left by lia.
		pose proof (Hg k).
		simplify_bools_lia_one_kernel.
		do 2 f_equal; lia.
	- rewrite stack_perms_left, stack_perms_right by lia.
		bdestructΩ'.
Qed.

Lemma stack_perms_rotl_natural n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
	stack_perms n0 n1 f g ∘ rotl (n0 + n1) n1 =
	rotl (n0 + n1) n1 ∘ stack_perms n1 n0 g f.
Proof.
	rewrite rotl_eq_rotr_sub.
	eq_by_WF_perm_eq (n0 + n1);
	[eauto using monotonic_WF_Perm with WF_Perm_db zarith|].
	intros k Hk.
	pose proof (Nat.mod_small n1 (n0 + n1)).
	assert (n0 = 0 -> n1 mod (n0 + n1) = 0) by 
		(intros ->; apply Nat.Div0.mod_same).
	rewrite <- Nat.add_sub_assoc by lia.
	rewrite rotr_eq_rotr_mod.
	rewrite Nat.Div0.add_mod.
	replace ((n1 - n1 mod (n0 + n1)) mod (n0 + n1)) with 0 by
	  (bdestruct (n0 =? 0); [subst; symmetry; 
		rewrite Nat.Div0.mod_same, Nat.sub_0_r, Nat.Div0.mod_same|
		rewrite (Nat.mod_small n1), Nat.sub_diag, Nat.Div0.mod_0_l];
		lia).
	rewrite Nat.add_0_r, <- !rotr_eq_rotr_mod.
	now rewrite stack_perms_rotr_natural.
Qed.


Lemma tensor_perms_kron_comm_perm_natural n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) :
	tensor_perms n0 n1 f g ∘ kron_comm_perm n0 n1 =
	kron_comm_perm n0 n1 ∘ tensor_perms n1 n0 g f.
Proof.
	eq_by_WF_perm_eq (n0 * n1).
	intros k Hk.
	unfold compose, kron_comm_perm. 
	assert (tensor_perms n1 n0 g f k < n1 * n0) 
		by auto with perm_bounded_db zarith.
	do 2 simplify_bools_lia_one_kernel.
	unfold tensor_perms.
	simplify_bools_moddy_lia_one_kernel.
	simplify_bools_lia_one_kernel.
	rewrite !Nat.div_add_l, !mod_add_l by lia.
	pose proof (Hf (k mod n0) ltac:(show_moddy_lt)).
	pose proof (Hg (k / n0) ltac:(show_moddy_lt)).
	rewrite Nat.Div0.div_div, Nat.div_small, Nat.add_0_r by lia.
	rewrite (Nat.mod_small (k / n0)) by (show_moddy_lt).
	rewrite (Nat.mod_small (f _)), (Nat.div_small (f _)) by lia.
	lia.
Qed.

