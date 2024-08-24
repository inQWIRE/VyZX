Require Import CoreRules.
Import CoreData CoreAutomation.
Import CastRules.
From QuantumLib Require Import Bits.
Require Export QuantumLib.Permutations.
Import QuantumLib.VectorStates Modulus Kronecker.

Open Scope prg.
Open Scope nat_scope.

(* Section Preliminary.v *)

(* FIXME: TODO: Move, probably to Modulus *)
Lemma and_True_l P : True /\ P <-> P.
Proof. tauto. Qed.

Lemma and_True_r P : P /\ True <-> P.
Proof. tauto. Qed.

Lemma and_iff_distr_l P Q R : 
  (P -> (Q <-> R)) <-> (P /\ Q <-> P /\ R).
Proof. tauto. Qed.

Lemma and_iff_distr_r P Q R : 
  (P -> (Q <-> R)) <-> (Q /\ P <-> R /\ P).
Proof. rewrite and_iff_distr_l. now rewrite 2!(and_comm P). Qed.


Section bool_lemmas.

Lemma eqb_true_l b : eqb true b = b.
Proof. now destruct b. Qed.

Lemma eqb_true_r b : eqb b true = b.
Proof. now destruct b. Qed.

End bool_lemmas.

Lemma diff_divs_lower_bound a b k n : 
  (a < n -> b < n -> a / k <> b / k -> k < n)%nat.
Proof.
  intros Ha Hb Hne.
  bdestructΩ (k <? n).
  exfalso; apply Hne.
  now rewrite 2!Nat.div_small by lia.
Qed.

Lemma even_eqb n : Nat.even n = (n mod 2 =? 0).
Proof.
  rewrite (Nat.div_mod_eq n 2) at 1.
  rewrite Nat.even_add, Nat.even_mul.
  cbn [Nat.even orb].
  rewrite eqb_true_l.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)).
  now destruct ((ltac:(lia) : n mod 2 = O \/ n mod 2 = 1%nat)) as
    [-> | ->].
Qed.

Lemma even_le_even_of_le_succ m n 
  (Hm : Nat.even m = true) (Hn : Nat.even n = true) : 
  (n <= S m -> n <= m)%nat.
Proof.
  intros Hnm.
  bdestructΩ (n =? S m).
  replace -> n in Hn.
  rewrite Nat.even_succ, <- Nat.negb_even in Hn.
  now rewrite Hm in Hn.
Qed.

(* Section on extra permutation lemmas, in Preliminary.v *)

Lemma perm_big_of_small_eq_idn n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) : 
  forall k, n <= k < m -> n <= f k.
Proof.
  assert (Hfeqinv : forall k, k < m -> f k < n -> k < n). 1:{
    intros k Hk Hfk.
    enough (f k = k) by lia.
    apply (permutation_is_injective m f Hf); [lia..|].
    now apply Hfeq.
  }
  intros k [].
  bdestructΩ (n <=? f k).
  specialize (Hfeqinv k); lia.
Qed.

Lemma perm_inv_perm_eq_idn_of_perm_eq_idn_up_to n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) :
  perm_eq n (perm_inv m f) idn.
Proof.
  intros k Hk.
  apply (permutation_is_injective m f Hf); [auto with perm_bounded_db..|].
  cleanup_perm.
  symmetry.
  now apply Hfeq.
Qed.

Lemma perm_shift_permutation_of_small_eq_idn n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) : 
  permutation (m - n) (fun k => f (k + n) - n).
Proof.
  pose proof (perm_big_of_small_eq_idn n m f Hm Hf Hfeq) as Hfbig.
  pose proof (perm_big_of_small_eq_idn n m _ Hm (perm_inv_permutation m f Hf) 
    (perm_inv_perm_eq_idn_of_perm_eq_idn_up_to n m f Hm Hf Hfeq))
    as Hfinvbig.
  exists (fun k => (perm_inv m f (k + n) - n)).
  intros k Hk; repeat split.
  - pose proof (permutation_is_bounded m f Hf (k + n)).
    lia.
  - pose proof (perm_inv_bounded m f (k + n)).
    lia.
  - rewrite Nat.sub_add by (apply Hfbig; lia).
    cleanup_perm;
    lia.
  - rewrite Nat.sub_add by (apply Hfinvbig; lia).
    cleanup_perm;
    lia.
Qed.
  
#[export] Hint Resolve perm_shift_permutation_of_small_eq_idn : perm_db.


Lemma perm_eq_of_small_eq_idn n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) : 
  perm_eq m f (stack_perms n (m - n) idn (fun k => f (k + n) - n)).
Proof.
  assert (Hfeqinv : forall k, k < m -> f k < n -> k < n). 1:{
    intros k Hk Hfk.
    enough (f k = k) by lia.
    apply (permutation_is_injective m f Hf); [lia..|].
    now apply Hfeq.
  }
  assert (Hfbig : forall k, n <= k < m -> n <= f k). 1: {
    intros k [].
    bdestructΩ (n <=? f k).
    specialize (Hfeqinv k); lia.
  }
  intros k Hk.
  bdestruct (k <? n).
  - rewrite stack_perms_left by lia.
    now apply Hfeq.
  - rewrite stack_perms_right by lia.
    rewrite (Nat.sub_add n k) by lia.
    specialize (Hfbig k).
    lia.
Qed.

(* TODO: Move, ideally to Qlib *)
Lemma perm_eq_dim_change_if_nonzero n m f g :  
  perm_eq m f g -> (n <> 0 -> n = m) -> perm_eq n f g.
Proof.
  intros Hfg H k Hk.
  rewrite H in Hk by lia.
  now apply Hfg.
Qed.

Lemma big_swap_perm_conj_reflect_eq' n p q : n = p + q ->
  reflect_perm n ∘ big_swap_perm p q ∘ reflect_perm n =
  big_swap_perm q p.
Proof.
  intros ->.
  eq_by_WF_perm_eq (p + q).
  rewrite reflect_perm_defn at 2.
  rewrite reflect_perm_defn.
  intros k Hk.
  unfold compose, big_swap_perm.
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_perm_permutation_alt | 10 : perm_db.

#[export] Hint Extern 100 (WF_Matrix _) => 
  apply WF_Matrix_dim_change : wf_db.

Definition swap_2_to_2_perm a b c d n := 
  fun k =>
  if n <=? k then k else
  if b =? c then (
    if k =? a then b else
    if k =? b then d else
    if k =? d then a else k
  ) else if a =? d then (
    if k =? a then c else
    if k =? c then b else
    if k =? b then a else k
  ) else (
    if k =? a then c else 
    if k =? b then d else
    if k =? c then a else
    if k =? d then b else k).

Lemma swap_2_to_2_perm_WF a b c d n :
  WF_Perm n (swap_2_to_2_perm a b c d n).
Proof.
  intros k Hk.
  unfold swap_2_to_2_perm; bdestructΩ'.
Qed.

#[export] Hint Resolve swap_2_to_2_perm_WF : WF_Perm_db.

Lemma swap_2_to_2_perm_invol a b c d n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hd : d < n) 
  (Hab : a <> b) (Hbc : b <> c) (Hcd : c <> d) 
  (Had : a <> d) :
  swap_2_to_2_perm a b c d n ∘ swap_2_to_2_perm a b c d n = idn.
Proof.
  eq_by_WF_perm_eq n.
  intros k Hk.
  unfold swap_2_to_2_perm, compose.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_2_to_2_perm_invol : perm_inv_db.

Lemma swap_2_to_2_perm_bounded a b c d n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hd : d < n) : 
  perm_bounded n (swap_2_to_2_perm a b c d n).
Proof.
  intros k Hk.
  unfold swap_2_to_2_perm.
  simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_2_to_2_perm_bounded : perm_bounded_db.

Lemma swap_2_to_2_perm_permutation a b c d n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hd : d < n) 
  (Hab : a <> b) (Hcd : c <> d) : 
  permutation n (swap_2_to_2_perm a b c d n).
Proof.
  bdestruct (b =? c);
  [|bdestruct (a =? d)].
  - exists (swap_2_to_2_perm d b b a n).
    intros k Hk; repeat split;
    unfold swap_2_to_2_perm;
    do 2 simplify_bools_lia_one_kernel;
    bdestructΩ'.
  - exists (swap_2_to_2_perm a c b a n).
    intros k Hk; repeat split;
    unfold swap_2_to_2_perm;
    do 2 simplify_bools_lia_one_kernel;
    bdestructΩ'.
  - perm_by_inverse (swap_2_to_2_perm a b c d n).
Qed.

#[export] Hint Resolve swap_2_to_2_perm_permutation : perm_db.

Lemma swap_2_to_2_perm_first a b c d n (Ha : a < n) : 
  swap_2_to_2_perm a b c d n a = c.
Proof.
  unfold swap_2_to_2_perm; bdestructΩ'.
Qed.

Lemma swap_2_to_2_perm_second a b c d n (Ha : b < n) (Hab : a <> b) : 
  swap_2_to_2_perm a b c d n b = d.
Proof.
  unfold swap_2_to_2_perm.
  bdestructΩ'.
Qed.



Import Setoid.

Definition mat_prop (n m : nat) (A B : Matrix n m) : Prop :=
  exists c : C, A = c .* B /\ c <> 0%R.

Notation "A '[∝]' B" := (mat_prop _ _ A B) (at level 70) : matrix_scope.

Lemma mat_prop_is_general {n m} (A B : Matrix n m) : 
  mat_prop n m A B = 
  (Proportional.proportional_general Datatypes.id Datatypes.id A B).
Proof.
  easy.
Qed.

(* #[global] *) Add Parametric Relation n m : (Matrix n m) (@mat_prop n m) 
  reflexivity proved by ltac:(intros A; 
    apply (Proportional.proportional_general_refl _ n m (fun k => k) A))
  symmetry proved by ltac:(intros A B;
    apply (Proportional.proportional_general_symm
    _ n m _ n m (fun k => k) (fun k => k) A B))
  transitivity proved by ltac:(intros A B C;  
  now apply (Proportional.proportional_general_trans 
    _ n m (fun k => k) A
    _ n m (fun k => k) B
    _ n m (fun k => k) C))
  as mat_prop_Setoid.

(* #[global] *) Add Parametric Morphism n m o : (@Mmult n m o) with signature
  mat_prop n m ==> mat_prop m o ==> mat_prop n o as Mmult_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB) C D (cCD & HCD & HcCD).
  Proportional.prop_exists_nonzero (cAB * cCD)%C.
  2: now apply Cmult_neq_0.
  rewrite HAB, HCD.
  now rewrite Mscale_mult_dist_l, Mscale_mult_dist_r, Mscale_assoc.
Qed.

(* #[global] *) Add Parametric Morphism n m o p : (@kron n m o p) with signature
  mat_prop n m ==> mat_prop o p ==> mat_prop (n*o) (m*p) as kron_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB) C D (cCD & HCD & HcCD).
  Proportional.prop_exists_nonzero (cAB * cCD)%C.
  2: now apply Cmult_neq_0.
  rewrite HAB, HCD.
  now rewrite Mscale_kron_dist_l, Mscale_kron_dist_r, Mscale_assoc.
Qed.

(* #[global] *) Add Parametric Morphism n m c : (@scale n m c) with signature
  mat_prop n m ==> mat_prop n m as Mscale_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB).
  Proportional.prop_exists_nonzero (cAB)%C.
  2: easy.
  rewrite HAB.
  now rewrite 2!Mscale_assoc, Cmult_comm.
Qed.

(* #[global] *) Add Parametric Morphism n m : (@transpose n m) with signature
  mat_prop n m ==> mat_prop m n as transpose_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB).
  Proportional.prop_exists_nonzero (cAB)%C.
  2: easy.
  rewrite HAB.
  now rewrite Mscale_trans.
Qed.

(* #[global] *) Add Parametric Morphism n m k : (@kron_n k n m) with signature
  mat_prop n m ==> mat_prop _ _ as kron_n_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB).
  Proportional.prop_exists_nonzero (cAB ^ k)%C.
  2: now apply Cpow_nonzero.
  rewrite HAB.
  now rewrite Mscale_kron_n_distr_r.
Qed.

(* Notation "A '[∝]' B" := (mat_prop _ _ A B) (at level 70) : matrix_scope. *)
Notation "A '[∝@' n m ']' B" := (mat_prop n m A B) 
  (at level 70, n at level 0, m at level 0, only parsing) : matrix_scope.

Ltac restore_dims_prop :=
  match goal with 
  |- context[?A [∝] ?B] =>
    let B' := restore_dims_rec B in 
    let A' := restore_dims_rec A in 
    replace A with A' by (unify_matrix_dims restore_dims_tac);
    replace B with B' by (unify_matrix_dims restore_dims_tac)
  end. 


