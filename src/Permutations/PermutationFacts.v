Require Export PermutationDefinitions.
Require Import PermutationAutomation. 
Require Import StrongInduction.
Require Import List.


Local Open Scope nat.
Local Open Scope prg.




(* Local Notation perm_eq n f g := (forall k, k < n -> f k = g k). *)
Local Notation is_perm_rinv n f finv := (perm_eq n (f ∘ finv) idn).
Local Notation is_perm_linv n f finv := (perm_eq n (finv ∘ f) idn).
Local Notation is_perm_inv n f finv := 
  (perm_eq n (f ∘ finv) idn /\ perm_eq n (finv ∘ f) idn).

Lemma perm_linv_injective_of_surjective n f finv finv' : 
  perm_surj n f -> is_perm_linv n f finv -> is_perm_linv n f finv' ->
  perm_eq n finv finv'.
Proof.
  intros Hsurj Hfinv Hfinv' k Hk.
  destruct (Hsurj k Hk) as [k' [Hk' Hfk']].
  rewrite <- Hfk'.
  unfold compose in *.
  rewrite Hfinv, Hfinv'; easy.
Qed.

Lemma perm_bounded_rinv_injective_of_injective n f finv finv' : 
  perm_inj n f -> perm_bdd n finv -> perm_bdd n finv' ->
  is_perm_rinv n f finv -> is_perm_rinv n f finv' ->
  perm_eq n finv finv'.
Proof.
  intros Hinj Hbdd Hbdd' Hfinv Hfinv' k Hk.
  apply Hinj; auto.
  unfold compose in *.
  rewrite Hfinv, Hfinv'; easy.
Qed.

Lemma permutation_inverse_injective n f finv finv' : permutation n f ->
  is_perm_inv n f finv -> is_perm_inv n f finv' ->
  perm_eq n finv finv'.
Proof.
  intros Hperm Hfinv Hfinv'.
  eapply perm_linv_injective_of_surjective.
  + apply permutation_is_surjective, Hperm.
  + destruct (Hfinv); auto.
  + destruct (Hfinv'); auto.
Qed.

(* FIXME: TODO: This is *really* not where this goes! But right now, it needs to. *)
(* Once quantumlib's in, we can put this in automation directly. *)
Ltac perm_eq_by_WF_inv_inj f n :=
  let tryeasylia := try easy; try lia in 
  apply (WF_permutation_inverse_injective f n); [
    tryeasylia; auto with perm_db |
    tryeasylia; auto with WF_perm_db |
    try solve [cleanup_perm; auto] |
    try solve [cleanup_perm; auto]]; tryeasylia.



(* TODO FIXME: Should this really be here? *)
(* Section on swap_perm, swaps two elements. TODO: Do we even want this?
	 We have swap_2_perm and fswap... Also, should swap_perm be defined in 
	 terms of fswap? *)
Lemma swap_perm_same a n :
  swap_perm a a n = idn.
Proof.
  unfold swap_perm.
  apply functional_extensionality; intros k.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite swap_perm_same : perm_cleanup_db.

Lemma swap_perm_comm a b n :
  swap_perm a b n = swap_perm b a n.
Proof.
  apply functional_extensionality; intros k.
  unfold swap_perm.
  bdestructΩ'.
Qed.

Lemma swap_WF_perm a b n : forall k, n <= k -> swap_perm a b n k = k.
Proof.
  intros.
  unfold swap_perm. 
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_WF_perm : WF_perm_db.

Lemma swap_perm_bdd a b n : a < n -> b < n ->
  forall k, k < n -> swap_perm a b n k < n.
Proof.
  intros Ha Hb k Hk.
  unfold swap_perm.
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_perm_bdd : perm_bdd_db.

Lemma swap_perm_inv a b n : a < n -> b < n -> 
  (swap_perm a b n) ∘ (swap_perm a b n) = idn.
Proof.
  intros Ha Hb.
  unfold compose.
  apply functional_extensionality; intros k.
  unfold swap_perm.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite swap_perm_inv : perm_inv_db.

Lemma swap_perm_2_perm a b n : a < n -> b < n ->
  permutation n (swap_perm a b n).
Proof.
  intros Ha Hb.
  perm_by_inverse (swap_perm a b n).
Qed.

#[export] Hint Resolve swap_perm_2_perm : perm_db.

Lemma swap_perm_S_permutation a n (Ha : S a < n) :
  permutation n (swap_perm a (S a) n).
Proof.
  apply swap_perm_2_perm; lia.
Qed.

#[export] Hint Resolve swap_perm_S_permutation : perm_db.

Lemma compose_swap_perm a b c n : a < n -> b < n -> c < n -> 
  b <> c -> a <> c ->
  (swap_perm a b n ∘ swap_perm b c n ∘ swap_perm a b n) = swap_perm a c n.
Proof.
  intros Ha Hb Hc Hbc Hac. 
  apply functional_extensionality; intros k.
  unfold compose, swap_perm.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite compose_swap_perm : perm_cleanup_db.





(* Section on insertion_sort_list *)

Lemma fswap_eq_compose_swap_perm {A} (f : nat -> A) n m o : n < o -> m < o ->
  fswap f n m = f ∘ swap_perm n m o.
Proof.
  intros Hn Hm.
  apply functional_extensionality; intros k.
  unfold compose, fswap, swap_perm.
  bdestruct_all; easy.
Qed.

Lemma fswap_perm_inv_n_permutation f n : permutation (S n) f ->
  permutation n (fswap f (perm_inv (S n) f n) n).
Proof.
  intros Hperm.
  apply fswap_at_boundary_permutation.
  - apply Hperm.
  - apply perm_inv_bdd_S.
  - apply perm_inv_is_rinv_of_permutation; auto.
Qed.

(* Notation perm_list_of_insertion_sort_list l :=
  (map (fun idxk => match idxk with 
    | pair n k => swap_perm n k (S n)
    end) (combine (seq 0 (length l)) l)). *)




Lemma perm_of_swap_list_WF l : swap_list_spec l = true ->
  WF_perm (length l) (perm_of_swap_list l).
Proof.
  induction l.
  - easy.
  - simpl.
    rewrite andb_true_iff.
    intros [Ha Hl].
    intros k Hk.
    unfold compose.
    rewrite IHl; [|easy|lia].
    rewrite swap_WF_perm; easy.
Qed.

Lemma invperm_of_swap_list_WF l : swap_list_spec l = true ->
  WF_perm (length l) (invperm_of_swap_list l).
Proof.
  induction l.
  - easy.
  - simpl.
    rewrite andb_true_iff.
    intros [Ha Hl].
    intros k Hk.
    unfold compose.
    rewrite swap_WF_perm; [|easy].
    rewrite IHl; [easy|easy|lia].
Qed.

#[export] Hint Resolve perm_of_swap_list_WF invperm_of_swap_list_WF : WF_perm_db.

Lemma perm_of_swap_list_bounded l : swap_list_spec l = true ->
  perm_bdd (length l) (perm_of_swap_list l).
Proof. 
  induction l; [easy|].
  simpl.
  rewrite andb_true_iff.
  intros [Ha Hl].
  intros k Hk.
  unfold compose.
  rewrite Nat.ltb_lt in Ha.
  apply swap_perm_bdd; try lia.
  bdestruct (k =? length l).
  - subst; rewrite perm_of_swap_list_WF; try easy; lia.
  - transitivity (length l); [|lia].
    apply IHl; [easy | lia].
Qed.

Lemma invperm_of_swap_list_bounded l : swap_list_spec l = true ->
  perm_bdd (length l) (invperm_of_swap_list l).
Proof.
  induction l; [easy|].
  simpl.
  rewrite andb_true_iff.
  intros [Ha Hl].
  rewrite Nat.ltb_lt in Ha.
  intros k Hk.
  unfold compose.
  bdestruct (swap_perm a (length l) (S (length l)) k =? length l).
  - rewrite H, invperm_of_swap_list_WF; [lia|easy|easy].
  - transitivity (length l); [|lia]. 
    apply IHl; [easy|].
    pose proof (swap_perm_bdd a (length l) (S (length l)) Ha (ltac:(lia)) k Hk).
    lia.
Qed.

#[export] Hint Resolve perm_of_swap_list_bounded invperm_of_swap_list_bounded : perm_bdd_db.

Lemma invperm_linv_perm_of_swap_list l : swap_list_spec l = true ->
  invperm_of_swap_list l ∘ perm_of_swap_list l = idn.
Proof.
  induction l.
  - easy.
  - simpl. 
    rewrite andb_true_iff.
    intros [Ha Hl].
    rewrite Combinators.compose_assoc, 
    <- (Combinators.compose_assoc _ _ _ _ (perm_of_swap_list _)).
    rewrite swap_perm_inv, compose_idn_l.
    + apply (IHl Hl).
    + bdestructΩ (a <? S (length l)).
    + lia.
Qed.

Lemma invperm_rinv_perm_of_swap_list l : swap_list_spec l = true ->
  perm_of_swap_list l ∘ invperm_of_swap_list l = idn.
Proof.
  induction l.
  - easy.
  - simpl. 
    rewrite andb_true_iff.
    intros [Ha Hl].
    rewrite <- Combinators.compose_assoc,
    (Combinators.compose_assoc _ _ _ _ (invperm_of_swap_list _)).
    rewrite (IHl Hl).
    rewrite compose_idn_r.
    rewrite swap_perm_inv; [easy| |lia].
    bdestructΩ (a <? S (length l)).
Qed.

#[export] Hint Rewrite invperm_linv_perm_of_swap_list 
  invperm_rinv_perm_of_swap_list : perm_cleanup_db.


(* FIX ME: Remove; for working reference*)
(* Fixpoint insertion_sort_list n f := 
  match n with 
  | 0 => []
  | S n' => let k := (perm_inv (S n') f n') in
      k :: insertion_sort_list n' (fswap f k n')
  end. *)

Lemma length_insertion_sort_list n f :
  length (insertion_sort_list n f) = n.
Proof.
  revert f;
  induction n;
  intros f.
  - easy.
  - simpl.
    rewrite IHn; easy.
Qed.

Local Opaque perm_inv. 
Lemma insertion_sort_list_is_swap_list n f : 
  swap_list_spec (insertion_sort_list n f) = true.
Proof.
  revert f;
  induction n;
  intros f.
  - easy.
  - simpl.
    rewrite length_insertion_sort_list, IHn.
    pose proof (perm_inv_bdd_S n f n).
    bdestructΩ (perm_inv (S n) f n <? S n).
Qed.

Lemma perm_of_insertion_sort_list_is_rinv n f : permutation n f ->
  forall k, k < n ->
  (f ∘ perm_of_swap_list (insertion_sort_list n f)) k = k.
Proof.
  revert f;
  induction n;
  intros f.
  - intros; exfalso; easy.
  - intros Hperm k Hk.
    simpl.
    rewrite length_insertion_sort_list.
    bdestruct (k =? n).
    + unfold compose.
      rewrite perm_of_swap_list_WF; [ |
        apply insertion_sort_list_is_swap_list |
        rewrite length_insertion_sort_list; lia
      ]. 
      unfold swap_perm.
      bdestructΩ (S n <=? k).
      bdestructΩ (k =? n).
      subst.
      bdestruct (n =? perm_inv (S n) f n).
      1: rewrite H at 1.
      all: rewrite perm_inv_is_rinv_of_permutation; [easy|easy|lia].
    + rewrite <- Combinators.compose_assoc.
      rewrite <- fswap_eq_compose_swap_perm; [|apply perm_inv_bdd_S|lia].
      rewrite IHn; [easy| |lia].
      apply fswap_perm_inv_n_permutation, Hperm.
Qed.
Local Transparent perm_inv. 

Lemma perm_of_insertion_sort_list_WF n f : 
  WF_perm n (perm_of_swap_list (insertion_sort_list n f)).
Proof.
  intros k.
  rewrite <- (length_insertion_sort_list n f) at 1.
  revert k.
  apply perm_of_swap_list_WF.
  apply insertion_sort_list_is_swap_list.
Qed.

Lemma invperm_of_insertion_sort_list_WF n f : 
  WF_perm n (invperm_of_swap_list (insertion_sort_list n f)).
Proof.
  intros k.
  rewrite <- (length_insertion_sort_list n f) at 1.
  revert k.
  apply invperm_of_swap_list_WF.
  apply insertion_sort_list_is_swap_list.
Qed.

#[export] Hint Resolve perm_of_insertion_sort_list_WF invperm_of_swap_list_WF : WF_perm_db.

Lemma perm_of_insertion_sort_list_perm_eq_perm_inv n f : permutation n f ->
  perm_eq n (perm_of_swap_list (insertion_sort_list n f)) (perm_inv n f).
Proof.
  intros Hperm.
  apply (perm_bounded_rinv_injective_of_injective n f).
  - apply permutation_is_injective, Hperm.
  - pose proof (perm_of_swap_list_bounded (insertion_sort_list n f)
      (insertion_sort_list_is_swap_list n f)) as H.
    rewrite (length_insertion_sort_list n f) in H.
    exact H.
  - auto with perm_bdd_db.
  - apply perm_of_insertion_sort_list_is_rinv, Hperm.
  - apply perm_inv_is_rinv_of_permutation, Hperm.
Qed.

Lemma perm_of_insertion_sort_list_eq_make_WF_perm_inv n f : permutation n f ->
  (perm_of_swap_list (insertion_sort_list n f)) = fun k => if n <=?k then k else perm_inv n f k.
Proof.
  intros Hperm.
  apply functional_extensionality; intros k.
  bdestruct (n <=? k).
  - rewrite perm_of_insertion_sort_list_WF; easy.
  - rewrite perm_of_insertion_sort_list_perm_eq_perm_inv; easy.
Qed.

Lemma perm_eq_linv_injective n f finv finv' : permutation n f ->
  is_perm_linv n f finv -> is_perm_linv n f finv' ->
  perm_eq n finv finv'.
Proof.
  intros Hperm Hfinv Hfinv' k Hk.
  destruct (permutation_is_surjective Hperm k Hk) as [k' [Hk' Hfk']].
  unfold compose in *.
  specialize (Hfinv k' Hk').
  specialize (Hfinv' k' Hk').
  rewrite Hfk' in *.
  rewrite Hfinv, Hfinv'.
  easy.
Qed.

Lemma perm_inv_eq_inv n f finv : 
  (forall x : nat, x < n -> f x < n /\ finv x < n /\ finv (f x) = x /\ f (finv x) = x)
  -> perm_eq n (perm_inv n f) finv.
Proof.
  intros Hfinv.
  assert (Hperm: permutation n f) by (exists finv; easy).
  apply (perm_eq_linv_injective n f); [easy| | ]; 
    unfold compose; intros k Hk.
  - rewrite perm_inv_is_linv_of_permutation; easy.
  - apply Hfinv, Hk.
Qed.

Lemma perm_inv_is_inv n f : permutation n f ->
  forall k : nat, k < n -> perm_inv n f k < n /\ f k < n 
    /\ f (perm_inv n f k) = k /\ perm_inv n f (f k) = k.
Proof.
  intros Hperm k Hk.
  repeat split.
  - apply perm_inv_bdd, Hk.
  - destruct Hperm as [? H]; apply H, Hk.
  - rewrite perm_inv_is_rinv_of_permutation; easy.
  - rewrite perm_inv_is_linv_of_permutation; easy.
Qed.

Lemma perm_inv_perm_inv n f : permutation n f ->
  perm_eq n (perm_inv n (perm_inv n f)) f.
Proof.
  intros Hperm k Hk.
  unfold compose.
  rewrite (perm_inv_eq_inv n (perm_inv n f) f); try easy.
  apply perm_inv_is_inv, Hperm.
Qed.

Lemma perm_inv_eq_of_perm_eq' n m f g : perm_eq n f g -> m <= n ->
  perm_eq n (perm_inv m f) (perm_inv m g).
Proof.
  intros Heq Hm.
  induction m; [trivial|].
  intros k Hk.
  simpl.
  rewrite Heq by lia.
  rewrite IHm by lia.
  easy.
Qed.

Lemma perm_inv_eq_of_perm_eq n f g : perm_eq n f g ->
  perm_eq n (perm_inv n f) (perm_inv n g).
Proof.
  intros Heq.
  apply perm_inv_eq_of_perm_eq'; easy.
Qed.

Lemma perm_inv_of_insertion_sort_list_eq n f : permutation n f ->
  perm_eq n f (perm_inv n (perm_of_swap_list (insertion_sort_list n f))).
Proof.
  intros Hperm k Hk.
  rewrite (perm_of_insertion_sort_list_eq_make_WF_perm_inv n f) by easy.
  rewrite (perm_inv_eq_of_perm_eq n _ (perm_inv n f)); [
    | intros; bdestructΩ' | easy].
  rewrite perm_inv_perm_inv; easy.
Qed.

Lemma perm_of_insertion_sort_list_of_perm_inv_eq n f : permutation n f ->
  perm_eq n f (perm_of_swap_list (insertion_sort_list n (perm_inv n f))).
Proof.
  intros Hperm.
  rewrite perm_of_insertion_sort_list_eq_make_WF_perm_inv by (auto with perm_db).
  intros; bdestructΩ'.
  rewrite perm_inv_perm_inv; easy.
Qed.


Lemma insertion_sort_list_S n f : 
  insertion_sort_list (S n) f = 
  (perm_inv (S n) f n) :: (insertion_sort_list n (fswap f (perm_inv (S n) f n) n)).
Proof. easy. Qed.

Lemma perm_of_swap_list_cons a l :
  perm_of_swap_list (a :: l) = swap_perm a (length l) (S (length l)) ∘ perm_of_swap_list l.
Proof. easy. Qed.

Lemma invperm_of_swap_list_cons a l :
  invperm_of_swap_list (a :: l) = invperm_of_swap_list l ∘ swap_perm a (length l) (S (length l)).
Proof. easy. Qed.

Lemma perm_of_insertion_sort_list_S n f : 
  perm_of_swap_list (insertion_sort_list (S n) f) =
  swap_perm (perm_inv (S n) f n) n (S n) ∘ 
    perm_of_swap_list (insertion_sort_list n (fswap f (perm_inv (S n) f n) n)).
Proof. 
  rewrite insertion_sort_list_S, perm_of_swap_list_cons.
  rewrite length_insertion_sort_list.
  easy.
Qed.

Lemma invperm_of_insertion_sort_list_S n f : 
  invperm_of_swap_list (insertion_sort_list (S n) f) =
  invperm_of_swap_list (insertion_sort_list n (fswap f (perm_inv (S n) f n) n))
  ∘ swap_perm (perm_inv (S n) f n) n (S n).
Proof. 
  rewrite insertion_sort_list_S, invperm_of_swap_list_cons.
  rewrite length_insertion_sort_list.
  easy.
Qed.

Lemma perm_of_swap_list_permutation l : swap_list_spec l = true ->
  permutation (length l) (perm_of_swap_list l).
Proof.
  intros Hsw.
  induction l;
  [ simpl; exists idn; easy |].
  simpl.
  apply permutation_compose.
  - apply swap_perm_2_perm; [|lia].
    simpl in Hsw.
    bdestruct (a <? S (length l)); easy.
  - eapply permutation_of_le_permutation_WF.
    2: apply IHl.
    1: lia.
    2: apply perm_of_swap_list_WF.
    all: simpl in Hsw;
    rewrite andb_true_iff in Hsw; easy.
Qed.

Lemma invperm_of_swap_list_permutation l : swap_list_spec l = true ->
  permutation (length l) (invperm_of_swap_list l).
Proof.
  intros Hsw.
  induction l;
  [ simpl; exists idn; easy |].
  simpl.
  apply permutation_compose.
  - eapply permutation_of_le_permutation_WF.
    2: apply IHl.
    1: lia.
    2: apply invperm_of_swap_list_WF.
    all: simpl in Hsw;
    rewrite andb_true_iff in Hsw; easy.
  - apply swap_perm_2_perm; [|lia].
    simpl in Hsw.
    bdestruct (a <? S (length l)); easy.
Qed.

Lemma perm_of_insertion_sort_list_permutation n f: 
  permutation n (perm_of_swap_list (insertion_sort_list n f)).
Proof.
  rewrite <- (length_insertion_sort_list n f) at 1.
  apply perm_of_swap_list_permutation.
  apply insertion_sort_list_is_swap_list.
Qed.

Lemma invperm_of_insertion_sort_list_permutation n f: 
  permutation n (invperm_of_swap_list (insertion_sort_list n f)).
Proof.
  rewrite <- (length_insertion_sort_list n f) at 1.
  apply invperm_of_swap_list_permutation.
  apply insertion_sort_list_is_swap_list.
Qed.

#[export] Hint Resolve perm_of_insertion_sort_list_permutation
    invperm_of_insertion_sort_list_permutation : perm_db.

Lemma invperm_of_insertion_sort_list_eq n f : permutation n f ->
  perm_eq n f (invperm_of_swap_list (insertion_sort_list n f)).
Proof.
  intros Hperm.
  apply (perm_eq_linv_injective n (perm_of_swap_list (insertion_sort_list n f))).
  - auto with perm_db.
  - intros k Hk.
    rewrite perm_of_insertion_sort_list_is_rinv; easy.
  - intros k Hk.
    rewrite invperm_linv_perm_of_swap_list; [easy|].
    apply insertion_sort_list_is_swap_list.
Qed.
  

Lemma permutation_grow_l' n f : permutation (S n) f -> 
  perm_eq (S n) f (swap_perm (f n) n (S n) ∘ 
  perm_of_swap_list (insertion_sort_list n (fswap (perm_inv (S n) f) (f n) n))).
Proof.
  intros Hperm k Hk.
  rewrite (perm_of_insertion_sort_list_of_perm_inv_eq _ _ Hperm) at 1 by auto.
Local Opaque perm_inv.
  simpl.
Local Transparent perm_inv.
  rewrite length_insertion_sort_list, perm_inv_perm_inv by auto.
  easy.
Qed.

Lemma permutation_grow_r' n f : permutation (S n) f -> 
  perm_eq (S n) f ( 
  invperm_of_swap_list (insertion_sort_list n (fswap f (perm_inv (S n) f n) n))
  ∘ swap_perm (perm_inv (S n) f n) n (S n)).
Proof.
  intros Hperm k Hk.
  rewrite (invperm_of_insertion_sort_list_eq _ _ Hperm) at 1 by auto.
Local Opaque perm_inv.
  simpl.
Local Transparent perm_inv.
  rewrite length_insertion_sort_list by auto.
  easy.
Qed.

Lemma permutation_grow_l n f : permutation (S n) f ->
  exists g k, k < S n /\ perm_eq (S n) f (swap_perm k n (S n) ∘ g) /\ permutation n g.
Proof.
  intros Hperm.
  eexists.
  exists (f n).
  split; [apply permutation_is_bounded; [easy | lia] | split].
  pose proof (perm_of_insertion_sort_list_of_perm_inv_eq _ _ Hperm) as H.
  rewrite perm_of_insertion_sort_list_S in H.
  rewrite perm_inv_perm_inv in H by (easy || lia).
  exact H.
  auto with perm_db.
Qed.

Lemma permutation_grow_r n f : permutation (S n) f ->
  exists g k, k < S n /\ perm_eq (S n) f (g ∘ swap_perm k n (S n)) /\ permutation n g.
Proof.
  intros Hperm.
  eexists.
  exists (perm_inv (S n) f n).
  split; [apply permutation_is_bounded; [auto with perm_db | lia] | split].
  pose proof (invperm_of_insertion_sort_list_eq _ _ Hperm) as H.
  rewrite invperm_of_insertion_sort_list_S in H.
  exact H.
  auto with perm_db.
Qed.
  


Local Transparent perm_inv.


(* Section on stack_perms *)
Lemma stack_perms_left {n0 n1} {f g} {k} :
  k < n0 -> stack_perms n0 n1 f g k = f k.
Proof.
  intros Hk.
  unfold stack_perms.
  replace_bool_lia (k <? n0) true.
  easy.
Qed.

Lemma stack_perms_right {n0 n1} {f g} {k} :
  n0 <= k < n0 + n1 -> stack_perms n0 n1 f g k = g (k - n0) + n0.
Proof.
  intros Hk.
  unfold stack_perms.
  replace_bool_lia (k <? n0) false.
  replace_bool_lia (k <? n0 + n1) true.
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
	replace_bool_lia (k <? n0) false. 
	replace_bool_lia (k <? n0 + n1) false.
	easy.
Qed.

Lemma stack_perms_f_idn n0 n1 f :
	stack_perms n0 n1 f idn = fun k => if k <? n0 then f k else k.
Proof. solve_modular_permutation_equalities. Qed. 

Lemma stack_perms_idn_f n0 n1 f : 
	stack_perms n0 n1 idn f = 
	fun k => if (¬ k <? n0) && (k <? n0 + n1) then f (k - n0) + n0 else k.
Proof. solve_modular_permutation_equalities. Qed. 

Lemma stack_perms_idn_idn n0 n1 :
	stack_perms n0 n1 idn idn = idn.
Proof. solve_modular_permutation_equalities. Qed.

#[export] Hint Rewrite stack_perms_idn_idn : perm_cleanup_db.

Lemma stack_perms_compose {n0 n1} {f g} {f' g'} 
	(Hf' : permutation n0 f') (Hg' : permutation n1 g') :
	(stack_perms n0 n1 f g ∘ stack_perms n0 n1 f' g'
	= stack_perms n0 n1 (f ∘ f') (g ∘ g'))%prg.
Proof.
	destruct Hf' as [Hf'inv Hf'].
	destruct Hg' as [Hg'inv Hg'].
	unfold compose.
	(* bdestruct_one. *)
  solve_modular_permutation_equalities.
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
  bdestructΩ'.
  rewrite (Nat.add_comm n0 n1), Nat.add_assoc.
  f_equal; f_equal; f_equal.
  lia.
Qed.

Lemma stack_perms_idn_of_left_right_idn {n0 n1} {f g} 
  (Hf : forall k, k < n0 -> f k = k) (Hg : forall k, k < n1 -> g k = k) :
  stack_perms n0 n1 f g = idn.
Proof.
  solve_modular_permutation_equalities.
  - apply Hf; easy.
  - rewrite Hg; lia.
Qed.







(* Section on rotr / rotl *)
(* FIXME: Decide whether/how to put this back where it goes in PermutationInstances *)
Lemma rotr_WF {n m} : 
	forall k, n <= k -> (rotr n m) k = k.
Proof. intros. unfold rotr. bdestruct_one; lia. Qed.

Lemma rotl_WF {n m} : 
	forall k, n <= k -> (rotl n m) k = k.
Proof. intros. unfold rotl. bdestruct_one; lia. Qed.

#[export] Hint Resolve rotr_WF rotl_WF : WF_perm_db.

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

#[export] Hint Resolve rotr_bdd rotl_bdd : perm_bdd_db.

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

#[export] Hint Resolve rotr_perm rotl_perm : perm_db.


(* This is the start of the actual section *)
Lemma rotr_0_r n : rotr n 0 = idn.
Proof.
	apply functional_extensionality; intros k.
	unfold rotr.
	bdestructΩ'.
	rewrite Nat.mod_small; lia.
Qed.

Lemma rotl_0_r n : rotl n 0 = idn.
Proof.
	apply functional_extensionality; intros k.
	unfold rotl.
	bdestructΩ'.
	rewrite Nat.mod_0_l, Nat.sub_0_r; [|lia].
	replace (k + n) with (k + 1 * n) by lia.
	rewrite Nat.mod_add, Nat.mod_small; lia.
Qed.

Lemma rotr_0_l k : rotr 0 k = idn.
Proof.
	apply functional_extensionality; intros a.
	unfold rotr.
	bdestructΩ'.
Qed.
	
Lemma rotl_0_l k : rotl 0 k = idn.
Proof.
	apply functional_extensionality; intros a.
	unfold rotl.
	bdestructΩ'.
Qed.

#[export] Hint Rewrite rotr_0_r rotl_0_r rotr_0_l rotl_0_l : perm_cleanup_db.

Lemma rotr_rotr n k l :
	((rotr n k) ∘ (rotr n l) = rotr n (k + l))%prg.
Proof.
	apply functional_extensionality; intros a.
	unfold compose, rotr.
	symmetry.
	bdestructΩ'; assert (Hn0 : n <> 0) by lia.
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
	bdestructΩ'.
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
  perm_eq_by_WF_inv_inj (rotr n n) n.
Qed.

#[export] Hint Rewrite rotl_n : perm_cleanup_db.

Lemma rotl_eq_rotl_mod n k : rotl n k = rotl n (k mod n).
Proof. 
  perm_eq_by_WF_inv_inj (rotr n k) n.
  rewrite rotr_eq_rotr_mod, rotl_rotr_inv; easy.
Qed.

Lemma rotr_eq_rotl_sub n k : 
	rotr n k = rotl n (n - k mod n).
Proof.
	rewrite rotr_eq_rotr_mod.
  perm_eq_by_WF_inv_inj (rotl n (k mod n)) n.
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
  perm_eq_by_WF_inv_inj (rotr n k) n.
	destruct n; [cbn; rewrite 2!rotr_0_l, compose_idn_l; easy|].
  rewrite (rotr_eq_rotr_mod _ k), rotr_rotr, <- (rotr_n (S n)).
  f_equal.
  assert (H' : S n <> 0) by easy.
  pose proof (Nat.mod_upper_bound k (S n) H').
  lia.
Qed.




Local Close Scope nat.
Local Close Scope prg.

