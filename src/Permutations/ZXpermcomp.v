(* A variant of ZXperm using computing proofs *)
Require Import ZXperm ZXpermAutomation ZXpermFacts.
Import CoreData.

Section nat_comp_proofs.

Local Open Scope nat_scope.

Definition add_0_r_comp {n} : n + 0 = n :=
  nat_ind (fun k => k + 0 = k) eq_refl (fun k H => f_equal S H) n.
Definition add_0_r_comp' {n} := eq_sym (@add_0_r_comp n).

Definition add_succ_r_comp {n m} : n + (S m) = S (n + m) := 
  nat_ind (fun k => k + S m = S (k + m)) eq_refl (fun k H => f_equal S H) n.
Definition add_succ_r_comp' {n m} := eq_sym (@add_succ_r_comp n m).

Definition add_comm_comp {n m} : n + m = m + n := 
  nat_ind (fun k => k + m = m + k) (eq_sym (add_0_r_comp))
    (fun k H => eq_trans (f_equal S H) (add_succ_r_comp')) n.
Definition add_comm_comp' {n m} := eq_sym (@add_comm_comp n m).

Definition add_assoc_comp {n m o} : n + (m + o) = n + m + o :=
  nat_ind (fun k => k + (m + o) = k + m + o) eq_refl 
  (fun k H => f_equal S H) n.
Definition add_assoc_comp' {n m o} := eq_sym (@add_assoc_comp n m o).

Definition zx_to_bot_pf_comp : forall {a n}, n = n - a + min a n := 
  fun a n => nat_ind (fun n => forall a, n = n - a + min a n) 
    (fun a => match a as b return 0 = 0 - b + min b 0 with 
    | 0 => eq_refl | S a' => eq_refl end)
    (fun n IHn a => 
      match a as b return S n = S n - b + min b (S n) with 
      | 0 => add_0_r_comp'
      | S a' => eq_trans (f_equal S (IHn a')) add_succ_r_comp'
      end) n a.

End nat_comp_proofs.

Definition zx_to_bot_comp (a n : nat) : ZX n n :=
  cast _ _ zx_to_bot_pf_comp zx_to_bot_pf_comp 
  ((n_wire (n - (n-a))) ↕ a_swap (min (n-a) n)).


Fixpoint zx_of_swap_list_comp (l : list nat) : ZX (length l) (length l) :=
	match l with 
	| [] => ⦰
	| a::l' => 
		zx_to_bot_comp a (1+length l')
		⟷ (cast (1 + length l') (1 + length l') 
			  add_comm_comp add_comm_comp (zx_of_swap_list_comp l' ↕ —))
	end.


Definition length_insertion_sort_list_comp :=
  nat_ind (fun n => forall f, length (insertion_sort_list n f) = n)
  (fun f => eq_refl)
  (fun n IHn f => f_equal S (IHn _)).

Definition zx_of_perm_comp n f :=
	cast n n 
		(eq_sym (length_insertion_sort_list_comp n (perm_inv n f))) 
		(eq_sym (length_insertion_sort_list_comp n (perm_inv n f)))
	(zx_of_swap_list_comp (insertion_sort_list n (perm_inv n f))).

Lemma cast_simplify_eq {n m n' m'} (zx0 zx1 : ZX n m)
  prfn prfn' prfm prfm' : 
  zx0 = zx1 ->
  cast n' m' prfn prfm zx0 = cast n' m' prfn' prfm' zx1.
Proof.
  intros.
  subst.
  cbn.
  now rewrite cast_id_eq.
Qed.

Lemma zx_to_bot_comp_eq a n : 
  zx_to_bot_comp a n = zx_to_bot a n.
Proof.
  now apply cast_simplify_eq.
Qed.

Lemma zx_of_swap_list_comp_eq l : 
  zx_of_swap_list_comp l = zx_of_swap_list l.
Proof.
  induction l; [reflexivity|].
  cbn.
  f_equal; [apply zx_to_bot_comp_eq|].
  apply cast_simplify_eq.
  now rewrite IHl.
Qed.

Lemma zx_of_perm_comp_eq n f : 
  zx_of_perm_comp n f = zx_of_perm n f.
Proof.
  apply cast_simplify_eq.
  apply zx_of_swap_list_comp_eq.
Qed.




(* A computing version of zx_comm whose casts are with
	 equalities that evaluate to eq_refl for concrete inputs *)
Definition zx_comm_comp p q : ZX (p + q) (q + p) :=
  cast _ _ eq_refl add_comm_comp
    (zx_of_perm_comp (p + q) (big_swap_perm q p)).

Lemma zx_comm_comp_eq p q : 
  zx_comm_comp p q = zx_comm p q.
Proof.
  unfold zx_comm_comp, zx_comm, zx_of_perm_cast.
  rewrite zx_of_perm_comp_eq.
  now apply cast_simplify_eq.
Qed.