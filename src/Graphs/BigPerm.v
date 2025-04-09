Require Import CoreRules. 
Require Import ZXpermFacts.
Require Import BipermAux. 
From QuantumLib Require Import Modulus. 
Import Setoid. 


(* Permutation results *)
Import ComposeRules.
Import Modulus. 
Open Scope ZX_scope.
Open Scope prg.
Open Scope nat_scope.










(* Section on inputs (which we'll turn into outputs with cap/cup wizardry) *)

(* A WF input function to connect m inputs to n spiders*)
Definition WF_input_func m n f := forall i, i < m -> f i < n.

Definition count_func_vals m f k : nat :=
  big_sum (fun i => if f i =? k then 1 else 0) m.

Add Parametric Morphism m : (count_func_vals m) with signature
  perm_eq m ==> eq as count_func_vals_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  apply functional_extensionality.
  intros k.
  unfold count_func_vals.
  apply big_sum_eq_bounded.
  intros i Hi; now rewrite Hfg.
Qed.



Lemma sum_count_func_vals_upto m f n :
  big_sum (count_func_vals m f) n = 
  big_sum (fun k => if f k <? n then 1 else 0) m.
Proof.
  induction n.
  - cbn; now rewrite big_sum_0 by easy.
  - cbn. 
    rewrite IHn.
    unfold count_func_vals.
    rewrite <- Nsum_plus.
    apply big_sum_eq_bounded.
    intros k Hk; bdestruct_all; lia.
Qed.

Lemma sum_count_func_vals m n f (Hf : WF_input_func m n f) :
  big_sum (count_func_vals m f) n = m.
Proof.
  unfold WF_input_func in *.
  induction m.
  - now rewrite big_sum_0 by easy.
  - unfold count_func_vals.
    cbn.
    rewrite Nsum_plus.
    replace (S m) with (m + 1) by lia.
    f_equal.
    + apply IHm; auto.
    + apply big_sum_unique.
      exists (f m).
      split; [auto|];
      split; intros; bdestructΩ'.
Qed.

(* FIXME: Move, and use in above proof of perm_of_input_func pullthrough *)
Lemma count_func_vals_compose_perm_r m n f g 
  (Hf : WF_input_func m n f) (Hg : permutation n g) : 
  perm_eq n (count_func_vals m f ∘ g)
  (count_func_vals m (perm_inv' n g ∘ f)).
Proof.
  intros k Hk.
  unfold compose.
  apply big_sum_eq_bounded.
  intros l Hl.
  now rewrite perm_inv'_eq, perm_inv_eqb_iff by auto.
Qed.

Lemma count_func_vals_reorder m f g (Hg : permutation m g) : 
  count_func_vals m (f ∘ g) = count_func_vals m f.
Proof.
  apply functional_extensionality.
  intros k.
  unfold count_func_vals.
  symmetry.
  exact (Nsum_reorder m _ g Hg).
Qed.

Lemma count_func_vals_Nsum_index n ns : 
  perm_eq n (count_func_vals (big_sum ns n) (Nsum_index n ns)) ns.
Proof.
  intros l Hl.
  unfold count_func_vals.
  erewrite big_sum_eq_bounded.
  2: {
    intros k Hk.
    rewrite Nsum_index_eqb_iff by lia.
    rewrite Nat.leb_antisym.
    rewrite andb_if, negb_if.
    apply f_equal_if_precedent_same; [reflexivity|].
    rewrite Nat.ltb_nlt.
    intros Hkl.
    cbn [big_sum Gplus nat_is_monoid].
    replace_bool_lia (k <? big_sum ns l + ns l) 
      (k - big_sum ns l <? ns l).
    reflexivity.
  }
  rewrite (big_sum_split n l ns Hl).
  rewrite <- Nat.add_assoc.
  rewrite (Nsum_if_lt (big_sum ns l) _ (fun _ => 0)
    (fun i => if i <? ns l then 1 else 0)).
  rewrite Nsum_constant, Nat.mul_0_r.
  rewrite (Nsum_if_lt (ns l) _ (fun _ => 1) (fun _ => 0)).
  rewrite Nsum_1, Nsum_constant.
  lia.
Qed.

Lemma count_func_vals_1_defn n f k : 
  count_func_vals n f k = 1 <->
  exists l, l < n /\ f l = k /\ 
  forall i, i < n -> i <> l -> f i <> k.
Proof.
  unfold count_func_vals.
  rewrite Nsum_if_1_0_unique_iff.
  apply exists_iff.
  intros l.
  rewrite Nat.eqb_eq.
  setoid_rewrite Nat.eqb_neq.
  reflexivity.
Qed.

Lemma count_func_vals_1_defn_alt n f k : 
  count_func_vals n f k = 1 <->
  exists l, l < n /\ f l = k /\ 
  forall i, i < n -> f i = k -> i = l.
Proof.
  rewrite count_func_vals_1_defn.
  apply exists_iff.
  intros l.
  apply and_iff_distr_l; intros _.
  apply and_iff_distr_l; intros _.
  apply forall_lt_iff; intros i Hi.
  lia.
Qed.


(* Decompose such a func into a perm and direct contractions, 
  realized as a zxperm and a stack of spiders *)
Definition perm_of_input_func m f :=
  fun k => 
  if m <=? k then k else
  big_sum (count_func_vals m f) (f k) +
  big_sum (fun i => if f i =? f k then 1 else 0) k.

Lemma perm_of_input_func_WF m f : WF_Perm m (perm_of_input_func m f).
Proof. intros k Hk. unfold perm_of_input_func. bdestructΩ'. Qed.

#[export] Hint Resolve perm_of_input_func_WF : WF_Perm_db.

Lemma perm_of_input_func_defn m f : 
  perm_eq m (perm_of_input_func m f)
  (fun k => big_sum (count_func_vals m f) (f k) +
  big_sum (fun i => if f i =? f k then 1 else 0) k).
Proof. intros k Hk. unfold perm_of_input_func. bdestructΩ'. Qed.


Add Parametric Morphism m : (perm_of_input_func m) with signature
  perm_eq m ==> eq as perm_of_input_func_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  eq_by_WF_perm_eq m.
  rewrite 2!perm_of_input_func_defn.
  intros k Hk.
  rewrite Hfg by auto.
  rewrite Hfg.
  f_equal.
  apply big_sum_eq_bounded.
  intros i Hi.
  now rewrite Hfg by lia.
Qed.



Lemma perm_of_input_func_bounded' m n f (Hf : WF_input_func m n f) : 
  perm_bounded m (perm_of_input_func m f).
Proof.
  intros k Hk.
  rewrite perm_of_input_func_defn by auto.
  assert (f k < n) by now apply Hf.
  apply (Nat.lt_le_trans _ 
    (big_sum (count_func_vals m f) (f k) + 
     big_sum (fun i => if f i =? f k then 1 else 0) m));
  [rewrite (big_sum_split m k); cbn; bdestructΩ'|].
  change (big_sum (count_func_vals m f) (S (f k)) <= m).
  rewrite <- (sum_count_func_vals m n f Hf) at 2.
  apply Nsum_le_r; lia.
Qed.

Lemma perm_of_input_func_bounded m f : 
  perm_bounded m (perm_of_input_func m f).
Proof.
  apply (perm_of_input_func_bounded' m (S (big_sum f m))).
  intros k Hk.
  enough (f k <= big_sum f m) by lia.
  rewrite (big_sum_split m k _ Hk).
  cbn; lia.
Qed.

#[export] Hint Resolve perm_of_input_func_bounded : perm_bounded_db.



Lemma perm_of_input_func_upper_bound m f :
  forall k, k < m ->
  perm_of_input_func m f k <
  big_sum (count_func_vals m f) (S (f k)).
Proof.
  intros k Hk.
  rewrite perm_of_input_func_defn by auto.
  cbn.
  unfold count_func_vals at 3.
  rewrite (big_sum_split m k _ Hk).
  cbn; bdestructΩ'.
Qed.

Lemma perm_of_input_func_lower_bound m f :
  forall k, k < m ->
  big_sum (count_func_vals m f) (f k) <=
  perm_of_input_func m f k.
Proof.
  intros k Hk.
  rewrite perm_of_input_func_defn by auto.
  lia.
Qed.

Lemma perm_of_input_func_spec m f : 
  forall k, k < m -> 
  big_sum (count_func_vals m f) (f k) <=
  perm_of_input_func m f k <
  big_sum (count_func_vals m f) (S (f k)).
Proof.
  auto using perm_of_input_func_upper_bound, 
    perm_of_input_func_lower_bound.
Qed.


Lemma perm_of_input_func_inj_helper m f :
  forall k l, k < m -> l < m ->
  perm_of_input_func m f k = perm_of_input_func m f l ->
  f k = f l.
Proof.
  intros k l Hk Hl.
  pose proof (perm_of_input_func_spec m f k Hk).
  pose proof (perm_of_input_func_spec m f l Hl).
  pose proof (Nsum_le_r (S (f k)) (f l) (count_func_vals m f)).
  pose proof (Nsum_le_r (S (f l)) (f k) (count_func_vals m f)).
  lia.
Qed.

Lemma perm_of_input_func_inj m f : 
  perm_inj m (perm_of_input_func m f).
Proof.
  intros k l Hk Hl.
  intros Heq.
  pose proof Heq as Heqf.
  apply perm_of_input_func_inj_helper in Heqf; [|auto..].
  revert Heq.
  rewrite 2!perm_of_input_func_defn by auto.
  bdestructΩ (k =? l).
  assert (Hkl : k < l \/ l < k) by lia.
  by_symmetry Hkl by lia.
  rewrite Heqf.
  rewrite (big_sum_split _ _ _ Hkl).
  cbn; bdestructΩ'.
Qed.

Lemma perm_of_input_func_permutation m f : 
  permutation m (perm_of_input_func m f).
Proof.
  apply permutation_iff_surjective,
    surjective_of_injective_and_bounded.
  split; [|auto_perm].
  apply perm_of_input_func_inj.
Qed.

#[export] Hint Resolve perm_of_input_func_permutation : perm_db.

Lemma perm_of_input_func_decomp m n f (Hf : WF_input_func m n f) : 
  perm_eq m 
    (Nsum_index n (count_func_vals m f) ∘
    perm_of_input_func m f) f.
Proof.
  rewrite perm_of_input_func_defn.
  intros k Hk.
  pose proof (sum_count_func_vals m n f Hf).
  unfold compose.
  rewrite Nsum_index_add_big_sum_l;
  [auto | | now apply Hf].
  unfold count_func_vals.
  rewrite (big_sum_split _ _ _ Hk); cbn; bdestructΩ'.
Qed.

Lemma perm_of_input_func_decomp_alt m n f (Hf : WF_input_func m n f) : 
  forall k, k < m ->
    (Nsum_index n (count_func_vals m f)
    (perm_of_input_func m f k)) = f k.
Proof.
  exact (perm_of_input_func_decomp m n f Hf).
Qed.

Lemma perm_of_input_func_enlarge_permutation_l 
  m n f (Hf : WF_input_func m n f) g (Hg : permutation n g) : 
  enlarge_permutation n g (count_func_vals m f) ∘ 
  perm_of_input_func m f = perm_of_input_func m (perm_inv' n g ∘ f).
Proof.
  pose proof (sum_count_func_vals _ _ _ Hf) as Heq.
  assert (forall h, WF_Perm (big_sum (count_func_vals m f) n) h ->
    WF_Perm m h) by (now rewrite Heq).
  eq_by_WF_perm_eq m.
  assert (forall h, perm_bounded m h ->
    perm_bounded (big_sum (count_func_vals m f) n) h) by (now rewrite Heq).
  rewrite <- Heq at 1.
  rewrite enlarge_permutation_defn.
  rewrite Heq.
  rewrite 2!perm_of_input_func_defn.
  intros k Hk.
  unfold compose.
  rewrite Nsum_index_add_big_sum_l, Nsum_offset_add_big_sum_l
    by first [ now apply Hf |
    unfold count_func_vals;
    rewrite (big_sum_split _ _ _ Hk);
    cbn; bdestructΩ'].
  f_equal.
  - apply big_sum_eq_bounded.
    intros i Hi.
    apply big_sum_eq_bounded.
    intros l Hl.
    rewrite perm_inv'_eq by auto.
    assert (perm_inv' n g (f k) < n) by auto_perm.
    now rewrite perm_inv_eqb_iff by auto_perm.
  - apply big_sum_eq_bounded.
    intros l Hl.
    now rewrite (permutation_eqb_iff _ _ 
      (perm_inv'_permutation n g Hg)) by auto with zarith.
Qed.







Fixpoint big_stack (ns ms : nat -> nat) 
  (zxs : forall i, ZX (ns i) (ms i)) (n : nat) 
  : ZX (big_sum ns n) (big_sum ms n) :=
  match n with
  | O => ⦰
  | S n' => big_stack ns ms zxs n' ↕ (zxs n')
  end. 

#[export] Hint Resolve WF_big_kron' : wf_db.

Lemma big_stack_semantics ns ms zxs n : 
  ⟦ big_stack ns ms zxs n ⟧ = 
  big_kron' ms ns (fun i => ⟦ zxs i ⟧) n.
Proof.
  induction n;
  now cbn; f_equal.
Qed.

Lemma big_stack_transpose ns ms zxs n : 
  (big_stack ns ms zxs n) ⊤ =
  big_stack ms ns (fun k => (zxs k) ⊤) n.
Proof.
  induction n; cbn; f_equal; easy.
Qed.

Lemma colorswap_big_stack ns ms zxs n : 
  ⊙ (big_stack ns ms zxs n) = 
  big_stack ns ms (fun k => ⊙ (zxs k)) n.
Proof.
  induction n; cbn; now f_equal.
Qed.

#[export] Hint Rewrite colorswap_big_stack : colorswap_db.



Lemma big_stack_simplify ns ms zx0s zx1s n 
  (Hzxs : forall k, k < n -> zx0s k ∝ zx1s k) : 
  big_stack ns ms zx0s n ∝
  big_stack ns ms zx1s n.
Proof.
  induction n; [easy|].
  cbn.
  apply stack_simplify; [|now apply Hzxs; auto].
  apply IHn.
  auto.
Qed.

Lemma big_stack_simplify_casted_len ns ms 
  (zxs : forall k, ZX (ns k) (ms k)) ns' ms' 
  (zxs' : forall k, ZX (ns' k) (ms' k)) n n'
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms')
  (Hzxs : forall k (Hk : k < n), zxs k ∝ 
    cast _ _ (Hns k Hk) (Hms k Hk) (zxs' k)) 
  (Hn : n = n') prfns prfms : 
  big_stack ns ms zxs n ∝
  cast _ _ prfns prfms (big_stack ns' ms' zxs' n').
Proof.
  match goal with |- ?A ∝ ?B => 
  change (⟦ A ⟧ [∝] ⟦ B ⟧) end.
  simpl_cast_semantics.
  rewrite 2!big_stack_semantics.
  subst n'.
  apply big_kron'_prop_bounded_dims; [now auto..|].
  intros k Hk.
  rewrite (Hzxs k Hk).
  now simpl_cast_semantics.
Qed.


Lemma big_stack_simplify_casted ns ms zxs ns' ms' zxs' n 
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms')
  (Hzxs : forall k (Hk : k < n), zxs k ∝ 
    cast _ _ (Hns k Hk) (Hms k Hk) (zxs' k)) 
  prfns prfms : 
  big_stack ns ms zxs n ∝
  cast _ _ prfns prfms (big_stack ns' ms' zxs' n).
Proof.
  unshelve (eapply big_stack_simplify_casted_len); easy.
Qed.

Lemma big_stack_simplify_casted_abs ns ms zxs ns' ms' zxs' n 
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms')
  (Hzxs : forall k prfn prfm, k < n -> zxs k ∝ 
    cast _ _ prfn prfm (zxs' k)) 
  prfns prfms : 
  big_stack ns ms zxs n ∝
  cast _ _ prfns prfms (big_stack ns' ms' zxs' n).
Proof.
  unshelve (eapply big_stack_simplify_casted); now auto.
Qed.

Lemma big_stack_simplify_casted_casted_abs ns ms zxs ns' ms' zxs' n 
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms')
  (Hzxs : forall k prfn prfm, k < n -> zxs k ∝ 
    cast _ _ prfn prfm (zxs' k)) 
  n' m' prfns prfms prfns' prfms' : 
  cast n' m' prfns prfms (big_stack ns ms zxs n) ∝
  cast n' m' prfns' prfms' (big_stack ns' ms' zxs' n).
Proof.
  revert prfns prfms.
  intros -> ->.
  rewrite cast_id.
  apply big_stack_simplify_casted_abs; now auto.
Qed.

Lemma big_stack_resize {n ns ms ns' ms'}
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms') zxs : 
  big_stack ns ms zxs n ∝
  cast _ _ (big_sum_eq_bounded _ _ n (Hns))
    (big_sum_eq_bounded _ _ n (Hms))
    (big_stack ns' ms' 
    (fun k => 
    match lt_dec k n with
    | left Hk => cast (ns' k) (ms' k) 
      (eq_sym (Hns k Hk)) (eq_sym (Hms k Hk)) (zxs k)
    | right _ => zx_dummy (ns' k) (ms' k)
    end ) n).
Proof.
  apply big_stack_simplify_casted_abs; [now auto..|].
  intros k ? ? Hk.
  destruct (lt_dec k n); [|lia].
  now rewrite cast_contract_eq, cast_id.
Qed.

Lemma big_stack_resize_unbounded {n ns ms ns' ms'}
  (Hns : forall k, ns k = ns' k) (Hms : forall k, ms k = ms' k) zxs : 
  big_stack ns ms zxs n ∝
  cast _ _ (big_sum_eq_bounded _ _ n (fun k _ => Hns k))
    (big_sum_eq_bounded _ _ n (fun k _ => Hms k))
    (big_stack ns' ms' 
    (fun k => cast (ns' k) (ms' k) 
      (eq_sym (Hns k)) (eq_sym (Hms k)) (zxs k)) n).
Proof.
  apply big_stack_simplify_casted_abs; [intros k Hk; now auto..|].
  intros k ? ? Hk.
  now rewrite cast_contract_eq, cast_id.
Qed.

Lemma big_stack_compose ns ms os zx0s zx1s n : 
  big_stack ns ms zx0s n ⟷ big_stack ms os zx1s n ∝
  big_stack ns os (fun k => zx0s k ⟷ zx1s k) n.
Proof.
  induction n; [apply compose_empty_l|].
  cbn.
  rewrite <- stack_compose_distr.
  now rewrite IHn.
Qed.




Lemma big_stack_big_stack nss mss zxss ns n : 
  big_stack (fun k => big_sum (nss k) (ns k))
    (fun k => big_sum (mss k) (ns k))
    (fun k => big_stack (nss k) (mss k) (zxss k) (ns k)) n ∝
  cast _ _ (big_sum_double_sum_indexed nss ns n) 
    (big_sum_double_sum_indexed mss ns n)
  (big_stack _ _ (fun k => zxss _ _) _).
Proof.
  apply ZX_prop_by_mat_prop.
  simpl_cast_semantics.
  rewrite 2!big_stack_semantics.
  erewrite big_kron'_eq_bounded;
  [|intros k Hk; apply big_stack_semantics].
  rewrite big_kron'_double_kron'_indexed by (intros; auto_wf).
  reflexivity.
Qed.


Lemma big_stack_stack_prf (n0s n1s : nat -> nat) (n : nat) : 
  big_sum (fun k => n0s k + n1s k) n =
  big_sum(fun k => if k mod 2 =? 0 then n0s (k / 2) else n1s (k / 2)) (n * 2).
Proof.
  change (fun k : nat => n0s k + n1s k) with 
    (fun k => big_sum (fun l => if l =? 0 then n0s k else n1s k) 2).
  now rewrite big_sum_double_sum, Nat.mul_comm.
Qed.

Lemma big_stack_rebound {n n'} (H : n = n') ns ms zxs : 
  big_stack ns ms zxs n ∝
  cast _ _ (f_equal _ H) (f_equal _ H)
    (big_stack ns ms zxs n').
Proof.
  now subst.
Qed.

Lemma big_stack_stack n0s n1s m0s m1s zx0s zx1s n : 
  big_stack (fun k => n0s k + n1s k) (fun k => m0s k + m1s k)
  (fun k => zx0s k ↕ zx1s k) n ∝
  cast _ _ (big_stack_stack_prf n0s n1s n) 
    (big_stack_stack_prf m0s m1s n)
  (big_stack (fun k => if k mod 2 =? 0 then n0s (k / 2) else n1s (k / 2))
    (fun k => if k mod 2 =? 0 then m0s (k / 2) else m1s (k / 2))
    (fun k => 
      if k mod 2 =? 0 as a return 
        ZX (if a then n0s (k / 2) else n1s (k / 2))
           (if a then m0s (k / 2) else m1s (k / 2)) 
      then zx0s (k / 2) else zx1s (k / 2)) (n * 2)). 
Proof.
  rewrite (big_stack_simplify _ _ _ (fun k => 
    big_stack (fun l => if l =? 0 then n0s k else n1s k)
      (fun l => if l =? 0 then m0s k else m1s k)
      (fun l => if l =? 0 as a 
        return ZX (if a then n0s k else n1s k) (if a then m0s k else m1s k) 
        then zx0s k else zx1s k) 2)).
  2: {
    intros k Hk.
    cbn.
    now rewrite stack_empty_l.
  }
  rewrite big_stack_big_stack.
  rewrite (big_stack_rebound (Nsum_constant _ _)).
  rewrite cast_contract_eq.
  apply big_stack_simplify_casted_casted_abs;
  [intros k Hk; now rewrite Nsum_offset_constant, 
    Nsum_index_constant by lia..|].
  intros k prfn prfm Hk; revert prfn prfm.
  rewrite Nsum_offset_constant, Nsum_index_constant by lia.
  intros ? ?; now rewrite cast_id.
Qed.

Lemma big_stack_mult_prf (ns : nat -> nat) n n' :
  big_sum ns (n * n') =
  big_sum (fun k =>
    big_sum (fun i => ns (k * n' + i)) n') n.
Proof.
  rewrite big_sum_double_sum, Nat.mul_comm.
  apply big_sum_eq_bounded.
  intros k Hk.
  f_equal.
  pose proof (Nat.div_mod_eq k n'); lia.
Qed.

Lemma big_stack_mult ns ms zxs n n' : 
  big_stack ns ms zxs (n * n') ∝
  cast _ _ (big_stack_mult_prf ns n n') 
    (big_stack_mult_prf ms n n')
  (big_stack 
    (fun k => big_sum (fun i => (ns (k * n' + i))) n')
    (fun k => big_sum (fun i => (ms (k * n' + i))) n')
    (fun k => 
      big_stack (fun i => (ns (k * n' + i)))
        (fun i => (ms (k * n' + i)))
        (fun i => zxs (k * n' + i)) 
        n')
    n).
Proof.
  prop_exists_nonzero 1%R.
  rewrite Mscale_1_l.
  simpl_cast_semantics.
  rewrite 2!big_stack_semantics.
  rewrite big_kron'_mult by (intros; auto_wf).
  erewrite big_kron'_eq_bounded; [reflexivity|].
  intros k Hk.
  cbn.
  now rewrite big_stack_semantics.
Qed.


Lemma big_stack_split_add ns ms zxs n m :
  big_stack ns ms zxs (n + m) ∝
  cast _ _ (big_sum_sum _ _ _) (big_sum_sum _ _ _)
    (big_stack ns ms zxs n ↕ 
     big_stack (fun k => ns (n + k)) (fun k => ms (n + k))
        (fun k => zxs (n + k)) m).
Proof.
  prop_exists_nonzero 1%R.
  rewrite Mscale_1_l.
  simpl_cast_semantics.
  cbn [ZX_semantics].
  rewrite 3!big_stack_semantics.
  apply big_kron'_split_add.
  intros; auto_wf.
Qed.

Lemma big_stack_join_add ns0 ms0 ns1 ms1 zxs0 zxs1 n m  : 
  big_stack ns0 ms0 zxs0 n ↕
  big_stack ns1 ms1 zxs1 m ∝
  cast _ _ (eq_sym (big_sum_if_lt _ _ _ _)) 
    (eq_sym (big_sum_if_lt _ _ _ _))
    (big_stack (fun k => if k <? n then ns0 k else ns1 (k - n))
      (fun k => if k <? n then ms0 k else ms1 (k - n))
      (fun k => if k <? n as a return 
        (ZX (if a then ns0 k else ns1 (k - n))
         (if a then ms0 k else ms1 (k - n)))
        then zxs0 k else zxs1 (k - n)) (n + m)).
Proof.
  rewrite big_stack_split_add.
  rewrite cast_contract_eq.
  rewrite cast_stack_distribute_fwd_l.
  apply stack_simplify; 
  (apply big_stack_simplify_casted_abs;
  [intros k Hk; bdestruct_one; f_equal; lia..|]).
  - intros k ? ? Hk.
    bdestruct_one; [|lia].
    now rewrite cast_id.
  - intros k ? ? Hk.
    bdestruct_one; [lia|].
    apply ZX_prop_by_mat_prop.
    simpl_cast_semantics.
    now rewrite add_sub'.
Unshelve.
  all: apply big_sum_eq_bounded; 
    intros k Hk; bdestruct_one; f_equal; lia.
Qed.

Lemma big_stack_empty n zxs (Hzxs : forall k, k < n -> zxs k ∝ ⦰) : 
  big_stack (fun _ => 0) (fun _ => 0) zxs n ∝
  cast _ _ (big_sum_0 _ _ (fun k => eq_refl))
    (big_sum_0 _ _ (fun k => eq_refl)) 
    ⦰.
Proof.
  induction n.
  - now rewrite cast_id.
  - cbn.
    rewrite IHn, Hzxs by auto.
    clean_eqns rewrite stack_empty_r, cast_contract_eq.
    cast_irrelevance.
Qed.

Lemma n_stack_to_big_stack {n m} k (zx : ZX n m) : 
  k ⇑ zx ∝
  cast _ _ (eq_sym (Nsum_constant n k)) (eq_sym (Nsum_constant m k))
  (big_stack _ _ (fun _ => zx) k).
Proof.
  induction k; [cbn; now rewrite cast_id|].
  rewrite (@big_stack_rebound (S k) (1 + k) ltac:(lia)).
  rewrite big_stack_split_add.
  cbn; rewrite !cast_contract_eq.
  clean_eqns rewrite cast_stack_distribute_fwd_l.
  apply stack_simplify.
  - now rewrite stack_empty_l, cast_id.
  - rewrite IHk.
    cast_irrelevance.
Qed.

Lemma n_stack1_to_big_stack k (zx : ZX 1 1) : 
  n_stack1 k zx ∝ 
  cast _ _ (eq_sym (Nsum_1 _)) (eq_sym (Nsum_1 _))
    (big_stack _ _ (fun _ => zx) k).
Proof.
  rewrite n_stack1_to_n_stack, n_stack_to_big_stack.
  rewrite cast_contract_eq.
  cast_irrelevance.
Qed.





Definition big_stack_perms n ns fs :=
  fun k => if big_sum ns n <=? k then k else
  big_sum ns (Nsum_index n ns k) + 
  (fs (Nsum_index n ns k)) (Nsum_offset n ns k).

Lemma big_stack_perms_WF n ns fs : 
  WF_Perm (big_sum ns n) (big_stack_perms n ns fs).
Proof.
  intros k Hk;
  unfold big_stack_perms;
  now simplify_bools_lia_one_kernel.
Qed.

#[export] Hint Resolve big_stack_perms_WF : WF_Perm_db.

Lemma big_stack_perms_defn n ns fs : 
  perm_eq (big_sum ns n) (big_stack_perms n ns fs) 
    (fun k => big_sum ns (Nsum_index n ns k) + 
    (fs (Nsum_index n ns k)) (Nsum_offset n ns k)).
Proof.
  intros k Hk;
  unfold big_stack_perms;
  now simplify_bools_lia_one_kernel.
Qed.



Lemma big_stack_perms_constant n d fs : 
  perm_eq (big_sum (fun _ => d) n)
    (big_stack_perms n (fun _ => d) fs) 
    (fun k => 
    k / d * d + fs (k / d) (k mod d)).
Proof.
  rewrite big_stack_perms_defn.
  rewrite big_sum_constant, times_n_nat.
  intros k Hk.
  now rewrite Nsum_index_constant, 
    Nsum_offset_constant, Nsum_constant by lia.
Qed.

Lemma big_stack_perms_constant_alt n d fs : 
  perm_eq (n * d)
    (big_stack_perms n (fun _ => d) fs) 
    (fun k => 
    k / d * d + fs (k / d) (k mod d)).
Proof.
  rewrite <- Nsum_constant; apply big_stack_perms_constant.
Qed.

Lemma big_stack_perms_succ n ns fs : 
  big_stack_perms (S n) ns fs = 
  stack_perms (big_sum ns n) (ns n) 
    (big_stack_perms n ns fs) (fs n).
Proof.
  eq_by_WF_perm_eq (big_sum ns (S n)).
  rewrite big_stack_perms_defn.
  rewrite big_stack_perms_defn.
  rewrite stack_perms_defn.
  intros k Hk.
  unfold Nsum_offset.
  cbn.
  rewrite Nat.leb_antisym.
  bdestruct (k <? big_sum ns n); cbn; lia. 
Qed.

Lemma big_stack_perms_bounded n ns fs 
  (Hfs : forall k, k < n -> perm_bounded (ns k) (fs k)) : 
  perm_bounded (big_sum ns n) (big_stack_perms n ns fs).
Proof.
  induction n; [easy|].
  rewrite big_stack_perms_succ.
  apply stack_perms_bounded;
  auto_perm.
Qed.

#[export] Hint Resolve big_stack_perms_bounded : perm_bounded_db.

Lemma big_stack_perms_permutation n ns fs 
  (Hfs : forall k, k < n -> permutation (ns k) (fs k)) : 
  permutation (big_sum ns n) (big_stack_perms n ns fs).
Proof.
  induction n; [now exists idn|].
  rewrite big_stack_perms_succ.
  apply stack_perms_permutation;
  auto_perm.
Qed.

#[export] Hint Resolve big_stack_perms_permutation : perm_db.

Lemma big_stack_perms_compose n ns fs gs 
  (Hgs : forall k, k < n -> perm_bounded (ns k) (gs k)) : 
  big_stack_perms n ns fs ∘ big_stack_perms n ns gs = 
  big_stack_perms n ns (fun k => fs k ∘ gs k).
Proof.
  induction n; [now eq_by_WF_perm_eq _|].
  specialize (IHn ltac:(auto)).
  rewrite 3!big_stack_perms_succ.
  rewrite stack_perms_compose by auto_perm.
  now rewrite IHn.
Qed.

Lemma big_stack_perms_inv n ns fs 
  (Hgs : forall k, k < n -> permutation (ns k) (fs k)) : 
  perm_eq (big_sum ns n) 
    (perm_inv (big_sum ns n) (big_stack_perms n ns fs))
    (big_stack_perms n ns (fun k => perm_inv (ns k) (fs k))).
Proof.
  induction n; [easy|].
  specialize (IHn ltac:(auto)).
  rewrite 2!big_stack_perms_succ.
  cbn.
  rewrite perm_inv_stack_perms, IHn by auto_perm.
  reflexivity.
Qed.


Lemma big_stack_perms_inv' n ns fs 
  (Hgs : forall k, k < n -> permutation (ns k) (fs k)) : 
  perm_inv' (big_sum ns n) (big_stack_perms n ns fs) = 
  big_stack_perms n ns (fun k => perm_inv' (ns k) (fs k)).
Proof.
  induction n; [easy|].
  specialize (IHn ltac:(auto)).
  rewrite 2!big_stack_perms_succ.
  cbn.
  rewrite perm_inv'_stack_perms, IHn by auto_perm.
  reflexivity.
Qed.

Hint Rewrite big_stack_perms_inv big_stack_perms_inv' 
  using solve [auto_perm] : perm_cleanup_db.


Lemma big_stack_perms_constant_permutation n d fs : 
  (forall k, k < n -> permutation d (fs k)) -> 
  permutation (n * d) (big_stack_perms n (fun _ => d) fs).
Proof.
  intros Hfs.
  rewrite <- Nsum_constant.
  auto_perm.
Qed.

Lemma big_stack_perms_constant_permutation_alt n d fs : 
  (forall k, k < n -> permutation d (fs k)) -> 
  permutation (d * n) (big_stack_perms n (fun _ => d) fs).
Proof.
  intros Hfs.
  rewrite Nat.mul_comm, <- Nsum_constant.
  auto_perm.
Qed.

#[export] Hint Resolve big_stack_perms_constant_permutation : perm_db.
#[export] Hint Resolve big_stack_perms_constant_permutation_alt | 10 : perm_db.


(* FIXME: Move *)


Lemma big_stack_perms_split_add n m ns fs :
  big_stack_perms (n + m) ns fs = 
  stack_perms (big_sum ns n) (big_sum (fun k => ns (n + k)) m)
    (big_stack_perms n ns fs)
    (big_stack_perms m (fun k => ns (n + k)) (fun k => fs (n + k))).
Proof.
  induction m.
  - rewrite Nat.add_0_r, stack_perms_0_r.
    now rewrite make_WF_Perm_of_WF by auto_perm.
  - rewrite Nat.add_succ_r.
    rewrite 2!big_stack_perms_succ.
    cbn.
    rewrite <- stack_perms_assoc.
    rewrite big_sum_sum.
    f_equal.
    apply IHm.
Qed.

(* FIXME: Move *)
Lemma big_stack_perms_simplify n n' ns ns' fss fss' 
  (Hn : n = n') (Hns : perm_eq n ns ns')
  (Hfss : forall k, k < n -> perm_eq (ns k) (fss k) (fss' k)) :
  big_stack_perms n ns fss = big_stack_perms n' ns' fss'.
Proof.
  subst n'.
  induction n; [easy|].
  rewrite 2!big_stack_perms_succ.
  rewrite <- (Hns n) by auto.
  rewrite <- (Hfss n) by auto.
  f_equal.
  - apply big_sum_eq_bounded, (perm_eq_mono n (S n)), Hns; lia.
  - apply IHn; auto using (perm_eq_mono n (S n)).
Qed.

Lemma big_stack_perms_big_stack n ns nss fss :
    (big_stack_perms n (fun k => big_sum (nss k) (ns k)) 
      (fun k => big_stack_perms (ns k) (nss k) (fss k))) =
    (big_stack_perms (big_sum ns n) 
      (fun k => nss (Nsum_index n ns k) (Nsum_offset n ns k))
      (fun k => fss (Nsum_index n ns k) (Nsum_offset n ns k))).
Proof.
  induction n; [easy|].
  cbn -[Nsum_index].
  rewrite big_stack_perms_succ.
  rewrite big_stack_perms_split_add.
  f_equal.
  - rewrite big_sum_double_sum_indexed.
    apply big_sum_eq_bounded.
    intros k Hk.
    rewrite Nsum_index_succ_r, Nsum_offset_succ_r.
    now if_true_lia.
  - apply big_sum_eq_bounded.
    intros k Hk.
    rewrite Nsum_index_succ_r, Nsum_offset_succ_r.
    if_false_lia.
    now rewrite add_sub'.
  - rewrite IHn.
    apply big_stack_perms_simplify;
    [reflexivity| |].
    + intros k Hk.
      rewrite Nsum_index_succ_r, Nsum_offset_succ_r.
      now if_true_lia.
    + intros k Hk.
      rewrite Nsum_index_succ_r, Nsum_offset_succ_r.
      now if_true_lia.
  - apply big_stack_perms_simplify; 
    [reflexivity| |].
    + intros k Hk.
      rewrite Nsum_index_succ_r, Nsum_offset_succ_r.
      if_false_lia.
      now rewrite add_sub'.
    + intros k Hk.
      rewrite Nsum_index_succ_r, Nsum_offset_succ_r.
      if_false_lia.
      now rewrite add_sub'.
Qed.









(* Basic notion of independence / S^×{n_1, ..., n_k} is 
  f ∼ g :=
  Nsum_index k ns ∘ f =[perm] Nsum_index k ns ∘ g.
  One important theoretical result we would want is that this means
  f ⁻¹ ∘ g ∈ ∏_i S_(ns i), which means exactly that
  forall i, i < k -> 
  permutation (ns i) (fun a => (f ⁻¹ ∘ g) (big_sum ns i + a))
  which should actually be <-> (we can prove this by induction?)
  perm_bounded (ns i) (fun a => (f ⁻¹ ∘ g) (big_sum ns i + a))

  ... all of which culminates in 
  zx_of_perm (Nsum ns n) f ∝
  big_stack ns ns (fun k => zx_of_perm (ns k) 
    (fun a => (f ∘ g ⁻¹) (big_sum ns k + a))) ⟷
  zx_of_perm (Nsum ns n) g.
*)

(* That's a lot of work, though. The basic program should be to just
   take a permutation and reconstruct it as a series of swap_2_to_2_perm's,
   then reduce those swap_2_to_2_perm's to depend only on the 
   spider the edges land in, then show by induction on the edges that, up 
   to some spider absorption, we get back the original perm. We should also
   get permutation of the edges *almost* for free, by showing this 
   only adds some (tensor_perms n 2 perm idn), which (n_stack n ⊃) absorbs. *)

Definition perm_indep_wrt n ns f g :=
  perm_eq (big_sum ns n) 
    (Nsum_index n ns ∘ f) (Nsum_index n ns ∘ g).

Notation "f '~[/' n ns ']' g" := (perm_indep_wrt n%nat ns%prg f%prg g%prg)
  (at level 70, n at level 9, ns at level 9) : ZX_scope.

Lemma perm_indep_wrt_refl n ns f : f ~[/ n ns ] f.
Proof. unfold perm_indep_wrt. reflexivity. Qed.

Lemma perm_indep_wrt_sym n ns f g : f ~[/ n ns ] g -> g ~[/ n ns] f.
Proof. unfold perm_indep_wrt. apply perm_eq_sym. Qed.

Lemma perm_indep_wrt_trans n ns f g h : f ~[/ n ns ] g -> g ~[/ n ns] h ->
  f ~[/ n ns] h.
Proof. unfold perm_indep_wrt. apply perm_eq_trans. Qed.

Add Parametric Relation n ns : (nat -> nat) (perm_indep_wrt n ns) 
  reflexivity proved by (perm_indep_wrt_refl n ns)
  symmetry proved by (perm_indep_wrt_sym n ns)
  transitivity proved by (perm_indep_wrt_trans n ns)
  as perm_indep_wrt_setoid.


Add Parametric Morphism n : (perm_indep_wrt n) with signature
  perm_eq n ==> eq as perm_indep_wrt_dim_change_eq.
Proof.
  intros ns ns' Hns.
  unfold perm_indep_wrt.
  erewrite Nsum_index_perm_eq_to_eq by apply Hns.
  now erewrite big_sum_eq_bounded by apply Hns.
Qed.

Lemma perm_shift_lower_permutation_iff_bounded n m f 
  (Hf : permutation n f) (Hm : m <= n) : 
  permutation m f <->
  perm_bounded m f.
Proof.
  split; [apply permutation_is_bounded|].
  intros Hbdd.
  rewrite permutation_iff_surjective.
  apply surjective_of_injective_and_bounded.
  split; [apply (perm_inj_mono _ _ Hm)|]; auto_perm.
Qed.

Lemma perm_shift_upper_bounded_below_of_lower_bounded n m f 
  (Hf : permutation n f) (Hm : m <= n) : 
  perm_bounded m f -> (forall k, k < (n - m) -> m <= f (m + k)).
Proof.
  assert (Hfbdd : perm_bounded n f) by auto_perm.
  intros Hbdd.
  intros k Hk.
  pose proof (Hfbdd (m + k) ltac:(lia)).
  bdestruct (f (m + k) <? m); [|lia].
  rewrite <- (perm_shift_lower_permutation_iff_bounded n m f) in Hbdd by auto.
  rewrite permutation_iff_surjective in Hbdd.
  destruct (Hbdd (f (m + k)) ltac:(auto)) as (k' & Hk' & Hfk').
  apply (permutation_is_injective n f Hf) in Hfk'; lia.
Qed.

Lemma perm_shift_upper_permutation_of_lower_bounded n m f 
  (Hf : permutation n f) (Hm : m <= n) : 
  perm_bounded m f ->
  permutation (n - m) (fun a => f (m + a) - m).
Proof.
  intros Hbdd.
  assert (permutation m f) as Hperm by 
    now apply (perm_shift_lower_permutation_iff_bounded n m).
  pose proof (perm_shift_upper_bounded_below_of_lower_bounded n m f 
    Hf Hm Hbdd) as Hbelow.
  apply permutation_iff_surjective, surjective_of_injective_and_bounded.
  split.
  - intros k l Hk Hl.
    pose proof (Hbelow k Hk).
    pose proof (Hbelow l Hl).
    pose proof (permutation_is_injective n f Hf (m + k) (m + l)).
    lia.
  - intros k Hk.
    pose proof (permutation_is_bounded n f Hf (m + k)).
    lia.
Qed.

Instance perm_eq_perm_indep_wrt_subrel n ns : 
  subrelation (perm_eq (big_sum ns n)) (perm_indep_wrt n ns).
Proof.
  intros f g Hfg.
  unfold perm_indep_wrt.
  now rewrite Hfg.
Qed.

Add Parametric Morphism n ns : compose with signature
  perm_indep_wrt n ns ==> 
  on_predicate_relation_l
    (fun f => perm_bounded (big_sum ns n) f)
    (perm_eq (big_sum ns n)) ==> 
  perm_indep_wrt n ns as compose_perm_indep_wrt_proper_l.
Proof.
  unfold perm_indep_wrt.
  intros f f' Hf g g' [Hgbdd Hg].
  rewrite <- 2!Combinators.compose_assoc.
  rewrite <- Hg.
  now rewrite Hf.
Qed.

Lemma perm_indep_wrt_diff_idn n ns f g (Hf : permutation (big_sum ns n) f)
  (Hg : permutation (big_sum ns n) g) (Hfg : f ~[/ n ns] g) : 
  f ∘ perm_inv (big_sum ns n) g ~[/ n ns] idn.
Proof.
  unfold perm_indep_wrt in *.
  rewrite <- Combinators.compose_assoc.
  rewrite Hfg, Combinators.compose_assoc.
  now rewrite perm_inv_rinv_of_permutation.
Qed.

Lemma perm_eq_stack_parts_of_lower_bounded n m f (Hf : permutation n f)
  (Hm : m <= n) (Hbdd : perm_bounded m f) : 
  perm_eq n f 
    (stack_perms m (n - m) f (fun k => f (m + k) - m)).
Proof.
  intros k Hk.
  bdestruct (k <? m).
  - now rewrite stack_perms_left by lia.
  - rewrite stack_perms_right by lia.
    pose proof (perm_shift_upper_bounded_below_of_lower_bounded 
      n m f Hf Hm Hbdd) as Hup.
    generalize (Hup (k - m) ltac:(lia)).
    replace (m + (k - m)) with k by lia.
    lia.
Qed.

Lemma perm_indep_wrt_idn_succ_perm n ns f
  (Hf : permutation (big_sum ns (S n)) f) (Hfidn : f ~[/ (S n) ns] idn) : 
  permutation (big_sum ns n) f.
Proof.
  assert (big_sum ns n <= big_sum ns (S n)) as Hle by (cbn; lia).
  apply (perm_shift_lower_permutation_iff_bounded _ _ f Hf Hle).
  intros k Hk.
  generalize (Hfidn k ltac:(lia)).
  unfold compose.
  assert (Nsum_index (S n) ns k < n) as Hlt
    by (rewrite Nsum_index_lt_iff; lia).
  revert Hlt.
  cbn.
  simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

Lemma perm_indep_wrt_idn_succ_mono n ns f (Hfidn : f ~[/ (S n) ns] idn) : 
  f ~[/ n ns] idn.
Proof.
  intros k Hk.
  generalize (Hfidn k ltac:(cbn;lia)).
  unfold compose.
  cbn.
  pose proof (Nsum_index_bounded n ns k ltac:(intros ->; cbn in *; lia)).
  bdestructΩ'.
Qed.

Lemma perm_indep_wrt_idn_perm_eq_big_stack_perms n ns f
  (Hf : permutation (big_sum ns n) f) (Hfidn : f ~[/ n ns] idn) : 
  perm_eq (big_sum ns n) f
    (big_stack_perms n ns 
    (fun n' => (fun k => f (big_sum ns n' + k) - big_sum ns n'))).
Proof.
  induction n; [easy|].
  rewrite big_stack_perms_succ.
  assert (big_sum ns n <= big_sum ns (S n)) as Hle by (cbn; lia).
  pose proof (perm_indep_wrt_idn_succ_perm n ns f Hf Hfidn) as Hfnperm.
  assert (Hbdd : perm_bounded (big_sum ns n) f) by auto_perm.
  specialize (IHn Hfnperm).
  assert (f ~[/ n ns] idn) by now apply perm_indep_wrt_idn_succ_mono.
  rewrite <- IHn by auto.
  replace (ns n) with (big_sum ns (S n) - big_sum ns n) by (cbn; lia).
  apply perm_eq_stack_parts_of_lower_bounded;
  solve [auto | cbn;lia].
Qed.

Lemma perm_indep_wrt_idn_all_shifts_perms n ns f
  (Hf : permutation (big_sum ns n) f) (Hfidn : f ~[/ n ns] idn) : 
  forall m, m < n -> permutation (ns m) 
    (fun k => f (big_sum ns m + k) - big_sum ns m).
Proof.
  induction n; [easy|].
  intros m Hm.
  assert (big_sum ns n <= big_sum ns (S n)) as Hle by (cbn; lia).
  pose proof (perm_indep_wrt_idn_succ_perm n ns f Hf Hfidn) as Hfnperm.
  assert (f ~[/ n ns] idn) by now apply perm_indep_wrt_idn_succ_mono.
  bdestruct (m <? n); [now apply IHn|].
  replace m with n in * by lia.
  replace (ns n) with (big_sum ns (S n) - big_sum ns n) by (cbn; lia).
  apply perm_shift_upper_permutation_of_lower_bounded; 
  first [cbn; lia | auto_perm].
Qed.

Lemma perm_indep_wrt_diff_rw {n ns f g} (Hfg : f ~[/ n ns] g)
  (Hf : permutation (big_sum ns n) f)
  (Hg : permutation (big_sum ns n) g) : 
  perm_eq (big_sum ns n) f 
  (big_stack_perms n ns 
    (fun k => (fun l => (f ∘ perm_inv (big_sum ns n) g) 
      (big_sum ns k + l) - big_sum ns k))
  ∘ g).
Proof.
  pose proof (perm_indep_wrt_diff_idn n ns f g Hf Hg Hfg) as Hidn.
  pose proof (perm_indep_wrt_idn_all_shifts_perms 
    n ns (f ∘ perm_inv (big_sum ns n) g) ltac:(auto_perm) Hidn) as Hperm.
  rewrite <- compose_perm_inv_r by auto_perm.
  apply perm_indep_wrt_idn_perm_eq_big_stack_perms; auto_perm.
Qed.

Lemma compose_Nsum_index_l_WF_input_func n ns f : 
  WF_input_func (big_sum ns n) n (Nsum_index n ns ∘ f).
Proof.
  bdestruct (n =? 0); [now subst|].
  intros k Hk.
  unfold compose.
  now apply Nsum_index_bounded.
Qed.

Lemma perm_indep_wrt_perm_of_input_func n ns f 
  (Hf : permutation (big_sum ns n) f) :
  f ~[/ n ns] perm_of_input_func (big_sum ns n) 
  (Nsum_index n ns ∘ f).
Proof.
  unfold perm_indep_wrt.
  symmetry.
  etransitivity;
  [|apply perm_of_input_func_decomp, compose_Nsum_index_l_WF_input_func].
  rewrite count_func_vals_reorder by auto.
  erewrite Nsum_index_perm_eq_to_eq at 1; [reflexivity|].
  now rewrite count_func_vals_Nsum_index.
Qed.

Lemma perm_of_input_func_compose_perm_r m n f g (Hg : permutation m g) 
  (Hf : WF_input_func m n f) :
  perm_of_input_func m (f ∘ g) ~[/ n (count_func_vals m f)]
  (perm_of_input_func m f ∘ g).
Proof.
  unfold perm_indep_wrt.
  rewrite sum_count_func_vals by auto.
  rewrite <- Combinators.compose_assoc.
  rewrite perm_of_input_func_decomp by auto.
  rewrite <- (count_func_vals_reorder _ _ _ Hg).
  rewrite perm_of_input_func_decomp; [reflexivity|].
  intros k Hk.
  apply Hf; auto_perm.
Qed.












Notation "'b2ZX' b n m α" := 
    (if b%bool 
    then X n%nat m%nat α%R 
    else Z n%nat m%nat α%R) 
  (at level 10, b at level 9, n at level 9, 
    m at level 9, α at level 9): ZX_scope.


Lemma Z_spider_big_fusion ns ms n n0 α αs 
  (Hns : forall k, k < n -> ns k <> 0) :
  Z n0 _ α ⟷ big_stack ns ms (fun k => Z (ns k) (ms k) (αs k)) n ∝
  Z n0 _ (α + big_sum αs n).
Proof.
  revert n0 α.
  induction n; intros n0 α.
  - cbn.
    rewrite Rplus_0_r.
    now cleanup_zx.
  - cbn.
    rewrite Z_add_r_base_rot.
    rewrite compose_assoc, <- (@stack_compose_distr 1 _ _ 1).
    rewrite IHn by auto.
    pose proof (Hns n ltac:(auto)).
    destruct (ns n); [easy|].
    rewrite Z_absolute_fusion, Rplus_0_l.
    rewrite <- Z_add_r.
    replace (big_sum αs n + α + (0 + αs n))%R
      with (α + (big_sum αs n + αs n))%R by lra.
    reflexivity.
Qed.

Lemma Z_spider_big_fusion_0 ns ms n n0 α 
  (Hns : forall k, k < n -> ns k <> 0) :
  Z n0 _ α ⟷ big_stack ns ms (fun k => Z (ns k) (ms k) 0) n ∝
  Z n0 _ α.
Proof.
  rewrite Z_spider_big_fusion by auto.
  now rewrite (@big_sum_0 R), Rplus_0_r by auto.
Qed.

Lemma Z_spider_big_fusion_0' ns ms Zs n n0 α 
  (Hns : forall k, k < n -> ns k <> 0)
  (HZs : forall k, k < n -> Zs k ∝ Z _ _ 0) : 
  Z n0 _ α ⟷ big_stack ns ms Zs n ∝
  Z n0 _ α.
Proof.
  rewrite (big_stack_simplify ns ms _ _ n HZs).
  apply Z_spider_big_fusion_0.
  auto.
Qed.



Lemma X_spider_big_fusion ns ms n n0 α αs 
  (Hns : forall k, k < n -> ns k <> 0) :
  X n0 _ α ⟷ big_stack ns ms (fun k => X (ns k) (ms k) (αs k)) n ∝
  X n0 _ (α + big_sum αs n).
Proof. colorswap_of (Z_spider_big_fusion ns ms n n0 α αs Hns). Qed.

Lemma X_spider_big_fusion_0 ns ms n n0 α 
  (Hns : forall k, k < n -> ns k <> 0) :
  X n0 _ α ⟷ big_stack ns ms (fun k => X (ns k) (ms k) 0) n ∝
  X n0 _ α.
Proof. colorswap_of (Z_spider_big_fusion_0 ns ms n n0 α Hns). Qed.

Lemma X_spider_big_fusion_0' ns ms Xs n n0 α 
  (Hns : forall k, k < n -> ns k <> 0) 
  (HXs : forall k, k < n -> Xs k ∝ X _ _ 0) :
  X n0 _ α ⟷ big_stack ns ms Xs n ∝
  X n0 _ α.
Proof.
  colorswap_of (Z_spider_big_fusion_0' ns ms 
  (fun k => ⊙ (Xs k)) n n0 α Hns 
  (fun k Hk => colorswap_compat _ _ _ _ (HXs k Hk))). 
Qed.


Lemma b2ZX_spider_big_fusion (b : bool) ns ms n n0 α αs 
  (Hns : forall k, k < n -> ns k <> 0) :
  b2ZX b n0 _ α ⟷ 
    big_stack ns ms (fun k => b2ZX b (ns k) (ms k) (αs k)) n ∝
  b2ZX b n0 _ (α + big_sum αs n).
Proof.
  destruct b; 
  [now apply X_spider_big_fusion
  |now apply Z_spider_big_fusion].
Qed.

Lemma b2ZX_spider_big_fusion_0 (b : bool) ns ms n n0 α 
  (Hns : forall k, k < n -> ns k <> 0) :
  b2ZX b n0 _ α ⟷ 
    big_stack ns ms (fun k => b2ZX b (ns k) (ms k) 0) n ∝
  b2ZX b n0 _ α.
Proof.
  destruct b; 
  [now apply X_spider_big_fusion_0
  |now apply Z_spider_big_fusion_0].
Qed.

Lemma b2ZX_spider_big_fusion_0' (b : bool) ns ms zxs n n0 α 
  (Hns : forall k, k < n -> ns k <> 0) 
  (Hzxs : forall k, k < n -> zxs k ∝ b2ZX b _ _ 0) :
  b2ZX b n0 _ α ⟷ big_stack ns ms zxs n ∝
  b2ZX b n0 _ α.
Proof.
  destruct b; 
  [now apply X_spider_big_fusion_0'
  |now apply Z_spider_big_fusion_0'].
Qed.

Lemma cast_b2ZX_eq {n n' m m'} prfn prfm (b : bool) α : 
  cast n' m' prfn prfm (b2ZX b n m α) = 
  b2ZX b n' m' α.
Proof. now subst. Qed.

Lemma cast_b2ZX {n n' m m'} prfn prfm (b : bool) α : 
  cast n' m' prfn prfm (b2ZX b n m α) ∝
  b2ZX b n' m' α.
Proof. now subst. Qed.

Lemma b2ZX_if_color_dist (b c c' : bool) n m α : 
  (if b then b2ZX c n m α else b2ZX c' n m α) = 
  b2ZX (if b then c else c') n m α.
Proof.
  now destruct b.
Qed.

Lemma b2ZX_simplify (b b' : bool) n m α α' :
  b = b' -> α = α' -> 
  b2ZX b n m α ∝ b2ZX b' n m α'.
Proof.
  now intros [] [].
Qed.


Lemma b2ZX_zxperm_absorbtion_right (b : bool) n m o α 
  (zx : ZX m o) (Hzx : ZXperm zx) : 
  b2ZX b n m α ⟷ zx ∝ b2ZX b n o α.
Proof.
  destruct b;
  [now apply X_zxperm_absorbtion_right | 
   now apply Z_zxperm_absorbtion_right].
Qed.

Lemma b2ZX_0_0_is_empty (b : bool) : 
  b2ZX b 0 0 0 ∝ ⦰.
Proof.
  destruct b;
  [apply X_0_0_is_empty | apply Z_0_0_is_empty].
Qed.




Section temp.
Import Kronecker.

(* FIXME: move to CapCupFacts.v *)
Lemma n_cup_zx_comm_absorbtion n : 
  zx_comm n n ⟷ n_cup n ∝ n_cup n.
Proof.
  prop_exists_nonzero 1%R.
  rewrite Mscale_1_l.
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  cbn [ZX_semantics].
  rewrite f_to_vec_split'_eq.
  rewrite Mmult_assoc.
  rewrite zx_comm_semantics.
  restore_dims.
  rewrite kron_comm_commutes_l by auto_wf.
  rewrite kron_comm_1_l, Mmult_1_r by auto_wf.
  rewrite 2!(kron_split_diag (f_to_vec _ _) (f_to_vec _ _)) by auto_wf.
  restore_dims.
  unify_pows_two. 
  rewrite <- 2!Mmult_assoc.
  rewrite 2!n_cup_f_to_vec_pullthrough_top.
  rewrite 2!kron_1_l by auto_wf.
  apply Mmult_vec_comm; auto_wf.
Qed.
End temp.







(* Lemma enlarge_permutation_big_kron'_natural_r (ns ms : nat -> nat) 
  As (n : nat) (HAs : forall k, k < n -> WF_Matrix (As k)) 
  f (Hf : permutation n f) : 
  perm_to_matrix (big_sum ns n) 
    (enlarge_permutation n f ns) × 
    big_kron' ns ms As n =
  @Mmult (2^(big_sum ns n)) (2^(big_sum ms n)) (2^(big_sum ms n))
  (big_kron' (ns ∘ perm_inv' n f) (ms ∘ perm_inv' n f) 
    (fun i => As (perm_inv' n f i)) n)
  (perm_to_matrix (big_sum ms n) 
    (enlarge_permutation n f ns)).
Proof.
  apply transpose_matrices.
  rewrite 2!Mmult_transpose.
  rewrite big_kron'_transpose, perm_to_matrix_transpose_eq by auto_perm.
  rewrite <- perm_inv'_eq.
  rewrite enlarge_permutation_inv' by auto. *)

Definition big_zx_of_permutation_l 
  n (f ns : nat -> nat) (Hf : permutation n f) : 
  ZX (big_sum (ns ∘ f) n) (big_sum ns n) :=
  cast _ _ (eq_sym (Nsum_reorder n ns f Hf)) eq_refl 
  (zx_of_perm (big_sum ns n) (enlarge_permutation n f ns)).


Definition big_zx_of_permutation_r
  n (f ns : nat -> nat) (Hf : permutation n f) : 
  ZX (big_sum ns n) (big_sum (ns ∘ f) n) :=
  cast _ _ (Nsum_reorder n ns f Hf) eq_refl
  (zx_of_perm (big_sum (ns ∘ f) n) 
    (enlarge_permutation n (perm_inv' n f) (ns ∘ f))).

Lemma big_zx_of_permutation_l_zxperm n f ns Hf : 
  ZXperm (big_zx_of_permutation_l n f ns Hf).
Proof.
  unfold big_zx_of_permutation_l.
  auto_zxperm.
Qed.

Lemma big_zx_of_permutation_r_zxperm n f ns Hf : 
  ZXperm (big_zx_of_permutation_r n f ns Hf).
Proof.
  unfold big_zx_of_permutation_r.
  auto_zxperm.
Qed.

#[export] Hint Resolve big_zx_of_permutation_l_zxperm
  big_zx_of_permutation_r_zxperm : zxperm_db.

#[export] Hint Extern 0 (ZXperm (big_zx_of_permutation_l ?n ?f ?ns ?Hf)) =>
  exact (big_zx_of_permutation_l_zxperm n f ns Hf) : zxperm_db.

Lemma big_zx_of_permutation_l_semantics n f ns Hf : 
  ⟦ big_zx_of_permutation_l n f ns Hf ⟧ =
  perm_to_matrix (big_sum ns n) (enlarge_permutation n f ns).
Proof.
  unfold big_zx_of_permutation_l.
  apply zx_of_perm_casted_semantics.
  auto_perm.
Qed.

Lemma big_zx_of_permutation_r_semantics n f ns Hf : 
  ⟦ big_zx_of_permutation_r n f ns Hf ⟧ =
  perm_to_matrix (big_sum (ns ∘ f) n) 
    (enlarge_permutation n (perm_inv' n f) (ns ∘ f)).
Proof.
  unfold big_zx_of_permutation_r.
  apply zx_of_perm_casted_semantics.
  auto_perm.
Qed.

Open Scope ZX_scope.

Lemma big_zx_of_permutation_l_transpose n ns f Hf : 
  (big_zx_of_permutation_l n f ns Hf) ⊤ ∝
  big_zx_of_permutation_r n f ns Hf.
Proof.
  prop_exists_nonzero 1%R.
  rewrite semantics_transpose_comm, Mscale_1_l, 
  (big_zx_of_permutation_l_semantics n f), 
  (big_zx_of_permutation_r_semantics n f).
  rewrite <- Nsum_reorder by auto.
  rewrite perm_to_matrix_transpose_eq by auto_perm.
  apply perm_to_matrix_eq_of_perm_eq.
  now rewrite enlarge_permutation_inv, perm_inv'_eq.
Qed.

Lemma big_zx_of_permutation_r_transpose n ns f Hf : 
  (big_zx_of_permutation_r n f ns Hf) ⊤ ∝
  big_zx_of_permutation_l n f ns Hf.
Proof.
  rewrite <- (big_zx_of_permutation_l_transpose n ns f Hf).
  now rewrite Proportional.transpose_involutive.
Qed.


Lemma big_zx_of_permutation_l_natural n ns ms zxs f Hf : 
  big_zx_of_permutation_l n f ns Hf ⟷ 
  big_stack ns ms zxs n ∝
  big_stack (ns ∘ f) (ms ∘ f) (fun k => zxs (f k)) n ⟷ 
  big_zx_of_permutation_l n f ms Hf.
Proof.
  prop_exists_nonzero 1%R.
  rewrite Mscale_1_l.
  cbn [ZX_semantics].
  rewrite (big_zx_of_permutation_l_semantics n f).
  rewrite big_stack_semantics.
  restore_dims.
  rewrite enlarge_permutation_big_kron'_natural
    by (assumption + intros; auto_wf).
  rewrite (big_zx_of_permutation_l_semantics n f).
  rewrite big_stack_semantics.
  f_equal;
  now rewrite <- Nsum_reorder by auto.
Qed.

Lemma big_zx_of_permutation_r_natural n ns ms zxs f Hf : 
  big_stack ns ms zxs n ⟷ 
  big_zx_of_permutation_r n f ms Hf ∝
  big_zx_of_permutation_r n f ns Hf ⟷ 
  big_stack (ns ∘ f) (ms ∘ f) (fun k => zxs (f k)) n.
Proof.
  apply transpose_diagrams.
  cbn.
  rewrite 2!big_zx_of_permutation_r_transpose, 2!big_stack_transpose.
  now rewrite big_zx_of_permutation_l_natural.
Qed.

Lemma zxperm_to_big_zx_of_permutation_l {n m} (zx : ZX n m) 
  (Hzx : ZXperm zx) : 
  zx ∝ 
  cast n m (eq_sym (Nsum_1 _)) 
  (eq_sym (eq_trans (Nsum_1 _) (zxperm_square zx Hzx)))
  (big_zx_of_permutation_l n (perm_inv' n (perm_of_zx zx)) (fun _ => 1) 
    (perm_inv'_permutation _ _ (perm_of_zx_permutation zx Hzx))).
Proof.
  pose proof (zxperm_square zx Hzx) as Hnm.
  revert zx Hzx.
  subst m.
  intros zx Hzx.
  unfold big_zx_of_permutation_l.
  rewrite cast_contract_eq.
  by_perm_eq.
  rewrite enlarge_permutation_1.
  rewrite perm_of_zx_of_perm_eq by auto_perm.
  now rewrite perm_inv'_perm_inv by auto_perm.
Qed.

Lemma zxperm_to_big_zx_of_permutation_r {n m} (zx : ZX n m) 
  (Hzx : ZXperm zx) : 
  zx ∝ 
  cast n m (eq_sym (Nsum_1 _)) 
  (eq_sym (eq_trans (Nsum_1 _) (zxperm_square zx Hzx)))
  (big_zx_of_permutation_r n (perm_of_zx zx) (fun _ => 1) 
    (perm_of_zx_permutation zx Hzx)).
Proof.
  pose proof (zxperm_square zx Hzx) as Hnm.
  revert zx Hzx.
  subst m.
  intros zx Hzx.
  unfold big_zx_of_permutation_r.
  rewrite cast_contract_eq.
  by_perm_eq.
  rewrite enlarge_permutation_1.
  rewrite perm_of_zx_of_perm_eq by auto_perm.
  now rewrite perm_inv'_perm_inv by auto_perm.
Qed.

Lemma zx_of_perm_to_big_zx_of_permutation_l n f (Hf : permutation n f) : 
  zx_of_perm n f ∝
  cast n n (eq_sym (Nsum_1 _)) 
  (eq_sym (Nsum_1 _))
  (big_zx_of_permutation_l n (perm_inv' n f) (fun _ => 1) 
    (perm_inv'_permutation _ _ Hf)).
Proof.
  rewrite (zxperm_to_big_zx_of_permutation_l _ (zx_of_perm_zxperm n f)).
  apply cast_simplify.
  by_perm_eq.
Qed.

Lemma zx_of_perm_to_big_zx_of_permutation_r n f (Hf : permutation n f) : 
  zx_of_perm n f ∝
  cast n n (eq_sym (Nsum_1 _)) 
  (eq_sym (Nsum_1 _))
  (big_zx_of_permutation_r n f (fun _ => 1) Hf).
Proof.
  rewrite (zxperm_to_big_zx_of_permutation_r _ (zx_of_perm_zxperm n f)).
  apply cast_simplify.
  unfold big_zx_of_permutation_r.
  apply cast_simplify.
  unfold compose.
  now rewrite perm_of_zx_of_perm_eq by auto.
Qed.




(* Enumerating the edges of the complete graph on n vertices *)
Definition idx_to_edge n k : nat * nat :=
  let i := Nsum_index n (reflect_perm n) k in 
  let j := Nsum_offset n (reflect_perm n) k in
  (i, i + S j).

Definition edge_to_idx n ij : nat := 
  big_sum (reflect_perm n) (fst ij) + (snd ij - S (fst ij)).

Lemma idx_to_edge_to_idx n k (Hk : k < n * (n - 1) / 2) : 
  edge_to_idx n (idx_to_edge n k) = k.
Proof.
  pose proof (Nsum_permutation _ _ (reflect_perm_permutation n)).
  pose proof (Nsum_index_offset_spec n (reflect_perm n) k ltac:(lia)).
  unfold idx_to_edge, edge_to_idx.
  cbn.
  lia.
Qed.

Lemma edge_to_idx_to_edge n ij (Hi : fst ij < snd ij) (Hj : snd ij < n) : 
  idx_to_edge n (edge_to_idx n ij) = ij.
Proof.
  unfold edge_to_idx.
  unfold idx_to_edge.
  rewrite Nsum_index_add_big_sum_l, Nsum_offset_add_big_sum_l 
    by (unfold reflect_perm; bdestructΩ').
  destruct ij.
  cbn in *.
  f_equal.
  lia.
Qed.

Lemma idx_to_edge_spec n k (Hk : k < n * (n - 1) / 2) : 
  fst (idx_to_edge n k) < snd (idx_to_edge n k) /\
  snd (idx_to_edge n k) < n.
Proof.
  unfold idx_to_edge.
  cbn [fst snd].
  split; [lia|].
  assert (n <> 0) by (intros ->; cbn in *; lia).
  pose proof (Nsum_permutation _ _ (reflect_perm_permutation n)).
  pose proof (Nsum_index_offset_spec n (reflect_perm n) k ltac:(lia)).
  pose proof (Nsum_index_bounded n (reflect_perm n) k ltac:(auto)).
  rewrite reflect_perm_defn in * by auto.
  lia.
Qed.

Lemma edge_to_idx_bounded n ij (Hi : fst ij < snd ij) (Hj : snd ij < n) : 
  edge_to_idx n ij < n * (n - 1) / 2.
Proof.
  destruct ij as [i j].
  unfold edge_to_idx.
  cbn [fst snd] in *.
  rewrite <- (Nsum_permutation n (reflect_perm n)) by auto_perm.
  replace (big_sum (reflect_perm n) n) 
    with (big_sum (reflect_perm n) (i + (n - i))) by (f_equal; lia).
  rewrite big_sum_sum.
  cbn [Gplus nat_is_monoid].
  enough ((j - S i) < big_sum (fun k => reflect_perm n (i + k)) (n - i))
    by lia.
  rewrite (big_sum_eq_bounded _ (reflect_perm (n - i))).
  2: {
    intros k Hk.
    rewrite 2!reflect_perm_defn by lia.
    lia.
  }
  rewrite Nsum_permutation by auto_perm.
  bdestruct (i =? n - 2).
  - subst.
    replace j with (n - 1) by lia.
    replace (n - (n - 2)) with 2 by lia.
    cbn; lia.
  - apply (Nat.lt_le_trans _ ((n - i) * ((n - i - 1) / 2))); [|
    apply Nat.div_mul_le; lia].
    apply (Nat.lt_le_trans _ (n - i)); [lia|].
    enough ((n - i - 1) / 2 <> 0) by nia.
    rewrite Nat.div_small_iff by lia.
    lia.
Qed.

Lemma edge_to_idx_inj n ij ij' 
  (Hi : fst ij < snd ij) (Hj : snd ij < n)
  (Hi' : fst ij' < snd ij') (Hj' : snd ij' < n) :
  edge_to_idx n ij = edge_to_idx n ij' ->
  ij = ij'.
Proof.
  intros Heq.
  pose proof (edge_to_idx_to_edge n ij Hi Hj).
  pose proof (edge_to_idx_to_edge n ij' Hi' Hj').
  congruence.
Qed.

Lemma idx_to_edge_succ n k (Hk : k < S n * (S n - 1) / 2) : 
  idx_to_edge (S n) k = if k <? n then (0, S k)
  else (fun ij => (S (fst ij), S (snd ij))) (idx_to_edge n (k - n)).
Proof.
  unfold idx_to_edge.
  cbn [fst snd].
  rewrite Nsum_index_succ, Nsum_offset_succ 
    by (rewrite Nsum_permutation; auto_perm).
  replace (reflect_perm (S n) 0) with n by (cbn; lia).
  bdestruct (k <? n); [reflexivity|].
  assert (Hrw : perm_eq n (reflect_perm (S n) ∘ S) (reflect_perm n))
    by (intros l Hl; unfold compose; now rewrite 2!reflect_perm_defn by lia).
  rewrite (Nsum_index_perm_eq_to_eq  _ _ _ Hrw).
  f_equal.
  cbn.
  do 3 f_equal.
  unfold Nsum_offset.
  rewrite (Nsum_index_perm_eq_to_eq  _ _ _ Hrw).
  bdestruct (n =? 0); [now subst|].
  erewrite big_sum_eq_bounded; [reflexivity|].
  intros l Hl.
  pose proof (Nsum_index_bounded n (reflect_perm n) (k - n)).
  apply Hrw; lia.
Qed.

Lemma edge_to_idx_succ n ij (Hi : fst ij < snd ij) (Hj : snd ij < S n) : 
  edge_to_idx (S n) ij = 
  if fst ij =? 0 then snd ij - 1 else
    n + edge_to_idx n ((fst ij - 1, snd ij - 1)).
Proof.
  destruct ij as [i j].
  unfold edge_to_idx; cbn [fst snd] in *.
  bdestruct (i =? 0).
  - subst. reflexivity. 
  - rewrite 2!Nsum_reflect_perm by lia.
    rewrite <- 2!triangle_number'.
    replace (S (i - 1)) with i by lia.
    cbn.
    enough (big_sum idn i <= n * (i - 1)).
    + rewrite Nat.add_assoc.
      f_equal; [|lia].
      nia.
    + destruct i; [easy|].
      replace (S i - 1) with i by lia.
      change (S i) with (1 + i).
      rewrite big_sum_sum.
      rewrite Nat.add_0_l.
      rewrite Nat.mul_comm, <- Nsum_constant.
      apply Nsum_le.
      lia.
Qed.











  



Program Definition nat_max_is_monoid : Monoid nat :=
  {|
    Gzero := 0;
    Gplus := Nat.max
  |}.
Solve All Obligations with lia.

Definition Nmax n f :=
  @big_sum nat nat_max_is_monoid f n.

Add Parametric Morphism n : (Nmax n) with signature
  perm_eq n ==> eq as Nmax_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  induction n; [easy|].
  cbn.
  f_equal; [|auto].
  unfold perm_eq in *; auto.
Qed.

Lemma le_Nmax n f k (Hk : k < n) : 
  f k <= Nmax n f.
Proof.
  unfold Nmax.
  induction n; [easy|].
  cbn.
  bdestruct (k =? n); subst; lia.
Qed.

Lemma Nmax_succ n f : 
  Nmax (S n) f = Nat.max (Nmax n f) (f n).
Proof. reflexivity. Qed.

Lemma Nmax_plus n m f : 
  Nmax (n + m) f = Nat.max (Nmax n f) (Nmax m (fun k => f (n + k))).
Proof.
  exact (big_sum_sum n m f).
Qed.

Lemma Nmax_attained n f (Hn : n <> 0) : 
  exists k, k < n /\ f k = Nmax n f.
Proof.
  induction n; [easy|].
  rewrite Nmax_succ.
  bdestruct (f n <? Nmax n f).
  - destruct (IHn ltac:(intros ->; cbn; easy)) as [k Hk].
    exists k; lia.
  - exists n; lia.
Qed.

Lemma Nmax_defn n f m (Hm : forall k, k < n -> f k <= m) : 
  Nmax n f <= m.
Proof.
  bdestruct (n =? 0); [subst; cbn; lia|].
  destruct (Nmax_attained n f) as (k & Hk & <-); auto.
Qed.

Lemma max_le_l_iff a b c : 
  Nat.max a b <= c <-> (a <= c /\ b <= c).
Proof. lia. Qed.

Lemma max_lt_l_iff a b c : 
  Nat.max a b < c <-> (a < c /\ b < c).
Proof. lia. Qed.

Lemma Nmax_le n f g (Hfg : forall k, k < n -> f k <= g k) : 
  Nmax n f <= Nmax n g.
Proof.
  induction n; [reflexivity|].
  rewrite 2!Nmax_succ.
  apply Nat.max_le_compat; auto.
Qed.

Lemma Nmax_constant n d : 
  Nmax n (fun _ => d) = if n =? 0 then 0 else d.
Proof.
  induction n; [reflexivity|].
  rewrite Nmax_succ, IHn; bdestructΩ'.
Qed.

Lemma Nmax_le_l n m f (Hnm : n <= m) : 
  Nmax n f <= Nmax m f.
Proof.
  replace m with (n + (m - n)) by lia.
  rewrite Nmax_plus.
  auto with arith.
Qed.

Lemma Nmax_max n m f : 
  Nmax (Nat.max n m) f = Nat.max (Nmax n f) (Nmax m f).
Proof.
  pose proof (Nmax_le_l n m f).
  pose proof (Nmax_le_l m n f).
  bdestruct (n <? m); 
  [replace (Nat.max n m) with m by lia |
  replace (Nat.max n m) with n by lia]; lia.
Qed.

Lemma Nmax_max_r n f g :
  Nmax n (fun k => Nat.max (f k) (g k)) = 
  Nat.max (Nmax n f) (Nmax n g).
Proof.
  induction n; [reflexivity|].
  rewrite 3!Nmax_succ, IHn.
  lia.
Qed.

Lemma Nmax_Nmax_l n f g : 
  Nmax (Nmax n g) f =
  Nmax n (fun k => Nmax (g k) f).
Proof.
  induction n; [reflexivity|].
  now rewrite 2!Nmax_succ, Nmax_max, IHn.
Qed.

Lemma Nmax_le_iff n f m : 
  Nmax n f <= m <-> (forall k, k < n -> f k <= m).
Proof.
  induction n; [cbn; split; intros; lia|].
  rewrite Nmax_succ.
  rewrite max_le_l_iff, IHn.
  split.
  - intros [H ?] k Hk; bdestruct (k =? n); subst; auto with zarith.
  - auto.
Qed.

Lemma Nmax_lt_iff n f m (Hn : m <> 0) : 
  Nmax n f < m <-> (forall k, k < n -> f k < m).
Proof.
  induction n; [cbn; split; intros; lia|].
  rewrite Nmax_succ.
  rewrite max_lt_l_iff, IHn.
  split.
  - intros [H ?] k Hk; bdestruct (k =? n); subst; auto with zarith.
  - auto.
Qed.

Lemma WF_input_func_default m n f : 
  WF_input_func m (Nat.max n (S (Nmax m f))) f.
Proof.
  intros k Hk.
  pose proof (le_Nmax m f k Hk).
  lia.
Qed.

(* FIXME: Move *)
Lemma Nsum_max f n m : 
  big_sum f (Nat.max n m) = 
  Nat.max (big_sum f n) (big_sum f m).
Proof.
  pose proof (Nsum_le_r n m f).
  pose proof (Nsum_le_r m n f).
  bdestruct (m <? n);
  [rewrite Nat.max_l | rewrite Nat.max_r]; lia.
Qed.

Lemma max_n_S_Nmax_WF m n f (Hf : WF_input_func m n f) 
  (Hn : m <> 0) : 
  Nat.max n (S (Nmax m f)) = n.
Proof.
  apply Nat.max_l.
  change (Nmax m f < n).
  apply Nmax_lt_iff; [|auto with zarith].
  specialize (Hf 0); lia.
Qed.

Lemma max_n_S_Nmax_WF_alt m n f (Hf : WF_input_func m n f) 
  (Hn : n <> 0) : 
  Nat.max n (S (Nmax m f)) = n.
Proof.
  apply Nat.max_l.
  change (Nmax m f < n).
  apply Nmax_lt_iff; auto with zarith.
Qed.













Lemma zx_of_big_stack_perms n ns fs 
  (Hfs : forall k, k < n -> permutation (ns k) (fs k)) : 
  zx_of_perm (big_sum ns n) (big_stack_perms n ns fs) ∝
  big_stack ns ns (fun k => zx_of_perm (ns k) (fs k)) n.
Proof.
  induction n; [by_perm_eq_nosimpl; cbn; by_perm_cell|].
  cbn.
  rewrite big_stack_perms_succ.
  rewrite <- stack_zx_of_perm by auto_perm.
  now rewrite IHn by auto_perm.
Qed.

Lemma zx_of_enlarge_to_big_zx_of_permutation_l n f ns (Hf : permutation n f) :
  zx_of_perm (big_sum ns n) (enlarge_permutation n f ns) ∝
  cast _ _ (Nsum_reorder n _ _ Hf) eq_refl
    (big_zx_of_permutation_l n f ns Hf).
Proof.
  unfold big_zx_of_permutation_l.
  now rewrite cast_contract_eq, cast_id.
Qed.


