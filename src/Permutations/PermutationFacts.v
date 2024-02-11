Require Export PermutationDefinitions.
Require Import PermutationAutomation. 
Require Import StrongInduction.
Require Import List.


Local Open Scope nat.
Local Open Scope prg.










(* Section on general permutation properties *)
(* FIXME: In QuantumLib *)
Lemma permutation_is_surjective {n f} : permutation n f ->
  forall k, k < n -> exists k', k' < n /\ f k' = k.
Proof.
  intros Hf k Hk.
  destruct Hf as [finv Hfinv].
  specialize (Hfinv k Hk).
  exists (finv k).
  intuition.
Qed.

(* FIXME: In QuantumLib *)
Lemma compose_idn_l {T} {f: T -> nat} : (idn ∘ f = f)%prg.
Proof.
	unfold compose.
	apply functional_extensionality; easy.
Qed.

(* FIXME: In QuantumLib *)
Lemma compose_idn_r {T} {f: nat -> T} : (f ∘ idn = f)%prg.
Proof.
	unfold compose.
	apply functional_extensionality; easy.
Qed.

#[export] Hint Rewrite @compose_idn_r @compose_idn_l : perm_cleanup_db.






(* Section on perm_inv *)
(* FIXME: In QuantumLib *)
Lemma perm_inv_bdd_S n f k : 
  perm_inv (S n) f k < S n.
Proof.
  induction n; simpl;
<<<<<<< Updated upstream
<<<<<<< Updated upstream
  [bdestructΩ'|]. 
  bdestruct_one; [|transitivity (S n); [apply IHn|]]. 
=======
  [destruct_if_solve|]. 
  destruct_if; [|transitivity (S n); [apply IHn|]]. 
>>>>>>> Stashed changes
=======
  [destruct_if_solve|]. 
  destruct_if; [|transitivity (S n); [apply IHn|]]. 
>>>>>>> Stashed changes
  all: apply Nat.lt_succ_diag_r.
Qed.

(* FIXME: In QuantumLib *)
Lemma perm_inv_bdd n f k : k < n ->
  perm_inv n f k < n.
Proof.
  induction n.
  - easy.
  - intros. apply perm_inv_bdd_S.
Qed.

Global Hint Resolve perm_inv_bdd_S perm_inv_bdd : perm_bdd_db.

(* FIXME: In QuantumLib *)
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

(* FIXME: In QuantumLib *)
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

(* FIXME: In QuantumLib *)
Lemma perm_inv_is_linv_of_permutation n f : permutation n f ->
  forall k, k < n -> perm_inv n f (f k) = k.
Proof.
  intros Hperm.
  apply perm_inv_is_linv_of_inj, permutation_is_injective, Hperm.
Qed.

(* FIXME: In QuantumLib *)
Lemma perm_inv_is_rinv_of_permutation n f : permutation n f ->
  forall k, k < n -> f (perm_inv n f k) = k.
Proof.
  intros Hperm k Hk.
  apply perm_inv_is_rinv_of_surj, (permutation_is_surjective Hperm _ Hk).
Qed.

(* FIXME: In QuantumLib *)
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

<<<<<<< Updated upstream
<<<<<<< Updated upstream

Local Notation perm_surj n f := (forall k, k < n -> exists k', k' < n /\ f k' = k).
Local Notation perm_bdd  n f := (forall k, k < n -> f k < n).
Local Notation perm_inj  n f := (forall k l, k < n -> l < n -> f k = f l -> k = l).
(* Local Notation WF_perm   n f := (forall k, n <= k -> f k = k). *)


(* FIXME: In QuantumLib *)
=======
=======
>>>>>>> Stashed changes
(* FIXME: Should these exist? *)
Local Notation perm_surj n f := (forall k, k < n -> exists k', k' < n /\ f k' = k).
Local Notation perm_bdd  n f := (forall k, k < n -> f k < n).
Local Notation perm_inj  n f := (forall k l, k < n -> l < n -> f k = f l -> k = l).
Local Notation perm_WF   n f := (forall k, n <= k -> f k = k).


(* TODO: Move this where it belongs *)
<<<<<<< Updated upstream
>>>>>>> Stashed changes
=======
>>>>>>> Stashed changes
Lemma fswap_involutive : forall {A} (f : nat -> A) x y,
  fswap (fswap f x y) x y = f.
Proof.
  intros A f x y.
  unfold fswap.
  apply functional_extensionality.
  intros k.
  bdestruct_all; subst; easy.
Qed.

<<<<<<< Updated upstream
<<<<<<< Updated upstream


=======
>>>>>>> Stashed changes
=======
>>>>>>> Stashed changes
Lemma fswap_injective_if_injective : forall {A} n (f:nat -> A) x y,
  x < n -> y < n ->
  perm_inj n f -> perm_inj n (fswap f x y).
Proof.
  intros A n f x y Hx Hy Hinj k l Hk Hl.
  unfold fswap.
  bdestruct (k =? x); bdestruct (k =? y);
  bdestruct (l =? x); bdestruct (l =? y);
  subst; auto using Hinj.
  all: intros Heq;
    epose proof (Hinj _ _ _ _ Heq); 
    exfalso; lia.
  Unshelve.
  all: assumption.
Qed.

Lemma fswap_injective_iff_injective : forall {A} n (f:nat -> A) x y,
  x < n -> y < n ->
  perm_inj n f <-> perm_inj n (fswap f x y).
Proof.
  intros A n f x y Hx Hy.
  split.
  - apply fswap_injective_if_injective; easy.
  - intros Hinj.
    rewrite <- (fswap_involutive f x y).
    apply fswap_injective_if_injective; easy.
Qed.

Lemma fswap_surjective_if_surjective : forall n f x y, 
  x < n -> y < n -> 
  perm_surj n f -> perm_surj n (fswap f x y).
Proof.
  intros n f x y Hx Hy Hsurj k Hk.
  destruct (Hsurj k Hk) as [k' [Hk' Hfk']].
  bdestruct (k' =? x); [|bdestruct (k' =? y)].
  - exists y.
    split; [assumption|].
    subst.
    rewrite fswap_simpl2.
    easy.
  - exists x.
    split; [assumption|].
    subst.
    rewrite fswap_simpl1.
    easy.
  - exists k'.
    split; [assumption|].
    rewrite fswap_neq; lia.
Qed.

Lemma fswap_surjective_iff_surjective : forall n f x y,
  x < n -> y < n ->
  perm_surj n f <-> perm_surj n (fswap f x y).
Proof.
  intros n f x y Hx Hy.
  split.
  - apply fswap_surjective_if_surjective; easy.
  - intros Hsurj.
    rewrite <- (fswap_involutive f x y).
    apply fswap_surjective_if_surjective; easy.
Qed.

Lemma fswap_bounded_if_bounded : forall n f x y,
  x < n -> y < n ->
  perm_bdd n f -> perm_bdd n (fswap f x y).
Proof.
  intros n f x y Hx Hy Hbdd k Hk.
  unfold fswap.
  bdestruct_all;
  apply Hbdd; 
  easy.
Qed.

Lemma fswap_bounded_iff_bounded : forall n f x y,
  x < n -> y < n ->
  perm_bdd n f <-> perm_bdd n (fswap f x y).
Proof.
  intros n f x y Hx Hy.
  split.
  - apply fswap_bounded_if_bounded; easy.
  - intros Hbdd.
    rewrite <- (fswap_involutive f x y).
    apply fswap_bounded_if_bounded; easy.
Qed.

Lemma surjective_of_eq_boundary_shrink : forall n f,
  perm_surj (S n) f -> f n = n -> perm_surj n f.
Proof.
  intros n f Hsurj Hfn k Hk.
  assert (HkS : k < S n) by lia.
  destruct (Hsurj k HkS) as [k' [Hk' Hfk']].
  bdestruct (k' =? n).
  - exfalso; subst; lia.
  - exists k'.
    split; [lia | assumption].
Qed.

Lemma surjective_of_eq_boundary_grow : forall n f,
  perm_surj n f -> f n = n -> perm_surj (S n) f.
Proof.
  intros n f Hsurj Hfn k Hk.
  bdestruct (k =? n).
  - exists n; lia.
  - assert (H'k : k < n) by lia.
    destruct (Hsurj k H'k) as [k' [Hk' Hfk']].
    exists k'; lia.
Qed.

Lemma fswap_at_boundary_surjective : forall n f n',
  n' < S n -> perm_surj (S n) f -> f n' = n -> 
  perm_surj n (fswap f n' n).
Proof.
  intros n f n' Hn' Hsurj Hfn' k Hk.
  bdestruct (k =? f n).
  - exists n'.
    split.
    + assert (Hneq: n' <> n); [|lia].
      intros Hfalse.
      rewrite Hfalse in Hfn'.
      rewrite Hfn' in H.
      lia.
    + rewrite fswap_simpl1; easy.
  - assert (H'k : k < S n) by lia.
    destruct (Hsurj k H'k) as [k' [Hk' Hfk']].
    assert (Hk'n: k' <> n) by (intros Hfalse; subst; lia).
    assert (Hk'n': k' <> n') by (intros Hfalse; subst; lia).
    exists k'.
    split; [lia|].
    rewrite fswap_neq; lia.
Qed.

Lemma injective_monotone : forall {A} n (f : nat -> A) m, 
  m < n -> perm_inj n f -> perm_inj m f.
Proof.
  intros A n f m Hmn Hinj k l Hk Hl Hfkl.
  apply Hinj; auto; lia.
Qed.

<<<<<<< Updated upstream
<<<<<<< Updated upstream
Lemma injective_and_bounded_grow_of_boundary : forall n f,
=======
Lemma injective_and_bdd_grow_of_boundary : forall n f,
>>>>>>> Stashed changes
=======
Lemma injective_and_bdd_grow_of_boundary : forall n f,
>>>>>>> Stashed changes
  perm_inj n f /\ perm_bdd n f -> f n = n ->
  perm_inj (S n) f /\ perm_bdd (S n) f.
Proof.
  intros n f [Hinj Hbdd] Hfn.
  split.
  - intros k l Hk Hl Hfkl.
    bdestruct (k =? n).
    + subst.
      bdestruct (l =? n); [easy|].
      assert (H'l : l < n) by lia.
      specialize (Hbdd _ H'l).
      lia.
    + assert (H'k : k < n) by lia.
      bdestruct (l =? n).
      * specialize (Hbdd _ H'k). 
        subst. lia.
      * assert (H'l : l < n) by lia.
        apply Hinj; easy.
  - intros k Hk.
    bdestruct (k <? n).
    + specialize (Hbdd _ H). lia.
    + replace k with n by lia.
      lia.
Qed.

<<<<<<< Updated upstream
<<<<<<< Updated upstream
Lemma injective_and_bounded_of_surjective : forall n f,
=======
Lemma injective_and_bdd_of_surjective : forall n f,
>>>>>>> Stashed changes
=======
Lemma injective_and_bdd_of_surjective : forall n f,
>>>>>>> Stashed changes
  perm_surj n f -> perm_inj n f /\ perm_bdd n f.
Proof.
  intros n.
  induction n; [easy|].
  intros f Hsurj.
  assert (HnS : n < S n) by lia.
  destruct (Hsurj n HnS) as [n' [Hn' Hfn']].
  pose proof (fswap_at_boundary_surjective _ _ _ Hn' Hsurj Hfn') as Hswap_surj.
  specialize (IHn (fswap f n' n) Hswap_surj).
  rewrite (fswap_injective_iff_injective _ f n' n); [|easy|easy].
  rewrite (fswap_bounded_iff_bounded _ f n' n); [|easy|easy].
<<<<<<< Updated upstream
<<<<<<< Updated upstream
  apply injective_and_bounded_grow_of_boundary;
=======
  apply injective_and_bdd_grow_of_boundary;
>>>>>>> Stashed changes
=======
  apply injective_and_bdd_grow_of_boundary;
>>>>>>> Stashed changes
  [| rewrite fswap_simpl2; easy].
  easy.
Qed.

<<<<<<< Updated upstream
<<<<<<< Updated upstream
Lemma injective_and_bounded_shrink_of_boundary : forall n f,
=======
Lemma injective_and_bdd_shrink_of_boundary : forall n f,
>>>>>>> Stashed changes
=======
Lemma injective_and_bdd_shrink_of_boundary : forall n f,
>>>>>>> Stashed changes
  perm_inj (S n) f /\ perm_bdd (S n) f -> f n = n -> 
  perm_inj n f /\ perm_bdd n f.
Proof.
  intros n f [Hinj Hbdd] Hfn.
  split.
  - eapply injective_monotone, Hinj; lia.
  - intros k Hk.
    assert (H'k : k < S n) by lia.
    specialize (Hbdd k H'k).
    bdestruct (f k =? n).
    + rewrite <- Hfn in H.
      assert (HnS : n < S n) by lia.
      specialize (Hinj _ _ H'k HnS H).
      lia.
    + lia.
Qed.

<<<<<<< Updated upstream
<<<<<<< Updated upstream
(* Formalization of proof sketch of pigeonhole principle
   from https://math.stackexchange.com/a/910790 *)
Lemma exists_bounded_decidable : forall n P,
  (forall k, k < n -> {P k} + {~ P k}) ->
  {exists j, j < n /\ P j} + {~ exists j, j < n /\ P j}.
Proof.
  intros n P HPdec.
  induction n.
  - right; intros [x [Hlt0 _]]; inversion Hlt0.
  - destruct (HPdec n) as [HPn | HnPn]; [lia| |].
    + left. exists n; split; [lia | assumption].
    + destruct IHn as [Hex | Hnex].
      * intros k Hk; apply HPdec; lia.
      * left. 
        destruct Hex as [j [Hjn HPj]].
        exists j; split; [lia | assumption].
      * right.
        intros [j [Hjn HPj]].
        apply Hnex.
        bdestruct (j =? n).
        -- exfalso; apply HnPn; subst; easy.
        -- exists j; split; [lia | easy].
Qed.

Lemma has_preimage_decidable : forall n f, 
  forall k, k < n ->
  {exists j, j < n /\ f j = k} + {~exists j, j < n /\ f j = k}.
Proof.
  intros n f k Hk.
  apply exists_bounded_decidable.
  intros k' Hk'.
  bdestruct (f k' =? k).
  - left; easy.
  - right; easy.
Qed.

Lemma pigeonhole_S : forall n f, 
  (forall i, i < S n -> f i < n) ->
  exists i j, i < S n /\ j < i /\ f i = f j.
Proof.
  intros n.
  destruct n;
    [intros f Hbdd; specialize (Hbdd 0); lia|].
  induction n; intros f Hbdd.
  (* Base case: *)
  1: {
    exists 1, 0.
    pose (Hbdd 0).
    pose (Hbdd 1). 
    lia.
  }
  destruct (has_preimage_decidable (S (S n)) f (f (S (S n)))) as [Hex | Hnex].
  - apply Hbdd; lia.
  - destruct Hex as [j [Hj Hfj]].
    exists (S (S n)), j.
    repeat split; lia.
  - destruct (IHn (fun k => if f k <? f (S (S n)) then f k else f k - 1)) as
      [i [j [Hi [Hj Hgij]]]].
    + intros i Hi.
      bdestruct (f i <? f (S (S n))).
      * specialize (Hbdd (S (S n))).
        lia.
      * specialize (Hbdd i).
        lia.
    + exists i, j.
      repeat (split; [lia|]).
      assert (Hnex': forall k, k < S (S n) -> f k >= f (S (S n)) -> f k > f (S (S n))). 1:{
        intros k Hk Hge.
        bdestruct (f k =? f (S (S n))).
        - exfalso; apply Hnex; exists k; split; lia.
        - lia.
      }
      bdestruct (f i <? f (S (S n)));
      bdestruct (f j <? f (S (S n)));
      try easy.
      * specialize (Hnex' j); lia.
      * specialize (Hnex' i); lia.
      * pose (Hnex' j).
        pose (Hnex' i Hi H).
        lia.
Qed.

Lemma n_has_preimage_of_injective_and_bounded : forall n f,
  perm_inj (S n) f /\ perm_bdd (S n) f -> exists k, k < S n /\ f k = n.
Proof. 
  intros n f [Hinj Hbdd].
  destruct (has_preimage_decidable (S n) f n) as [Hex | Hnex]; 
    [lia | assumption |].
  (* Now, contradict injectivity using pigeonhole principle *)
  exfalso.
  assert (Hbdd': forall j, j < S n -> f j < n). 1:{
    intros j Hj.
    specialize (Hbdd j Hj).
    bdestruct (f j =? n).
    - exfalso; apply Hnex; exists j; easy.
    - lia.
  }
  destruct (pigeonhole_S n f Hbdd') as [i [j [Hi [Hj Heq]]]].
  absurd (i = j).
  - lia.
  - apply Hinj; lia.
Qed.

Lemma surjective_of_injective_and_bounded : forall n f,
  perm_inj n f /\ perm_bdd n f -> perm_surj n f.
Proof. 
  induction n; [easy|].
  intros f Hinj_bdd.
  destruct (n_has_preimage_of_injective_and_bounded n f Hinj_bdd) as [n' [Hn' Hfn']].
  rewrite (fswap_injective_iff_injective _ _ n n') in Hinj_bdd;
    [|lia|lia].
  rewrite (fswap_bounded_iff_bounded _ _ n n') in Hinj_bdd;
    [|lia|lia].
  rewrite (fswap_surjective_iff_surjective _ _ n n');
    [|lia|easy].
  intros k Hk.
  bdestruct (k =? n).
  - exists n.
    split; [lia|].
    rewrite fswap_simpl1; subst; easy.
  - pose proof (injective_and_bounded_shrink_of_boundary n _ Hinj_bdd) as Hinj_bdd'.
    rewrite fswap_simpl1 in Hinj_bdd'.
    specialize (Hinj_bdd' Hfn').
    destruct (IHn (fswap f n n') Hinj_bdd' k) as [k' [Hk' Hfk']]; [lia|].
    exists k'.
    split; [lia|assumption].
Qed.

(*FIXME: ^ all up to notation has been moved into QuantumLib. *)



(* Section on WF_perm *)
Lemma monotonic_WF_perm n m f : WF_perm n f -> n <= m ->
  WF_perm m f.
=======
=======
>>>>>>> Stashed changes
Lemma surjective_of_inj_and_bdd : forall n f,
  perm_inj n f /\ perm_bdd n f -> perm_surj n f.
Proof.
  induction n; [easy|].
  intros f [Hinj Hbdd].
  rewrite (fswap_surjective_iff_surjective _ _ n (perm_inv (S n) f n));
  [|lia|apply perm_inv_bdd_S].
  rewrite (fswap_injective_iff_injective _ _ n (perm_inv (S n) f n)) in Hinj;
  [|lia|apply perm_inv_bdd_S].
  rewrite (fswap_bounded_iff_bounded _ _ n (perm_inv (S n) f n)) in Hbdd;
  [|lia|apply perm_inv_bdd_S].
  assert (perm_surj n (fswap f n (perm_inv (S n) f n))).
  1 : {
    apply IHn, injective_and_bdd_shrink_of_boundary; [easy|].
    rewrite fswap_simpl1.
    admit.
  }
  apply surjective_of_eq_boundary_grow; [easy|].
  Admitted.






(* Lemma perm_inv_surj_of_surj n f :
  (forall k, k < n -> exists l, l < n /\ f l = k) ->
  forall l, l < n -> exists k, k < n /\ perm_inv n f k = l. *)





(* Section for prelude lemmas that don't directly involve permutations *)
(* TODO: Prove these: *)




Lemma bdd_of_is_inj_is_surj n f :
  perm_inj n f -> perm_surj n f -> perm_bdd n f.
Proof.
  intros Hinj Hsurj k Hk.

  Abort.

Lemma surj_of_is_bdd_is_inj n f : 
  perm_bdd n f -> perm_inj n f -> perm_surj n f.
Proof.
  Abort.

Lemma inj_of_is_surj_is_bdd n f :
  perm_surj n f -> perm_bdd n f -> perm_inj n f. 
Proof.
  Abort. 

(* Lemma surj_of_is_WF_is_inj n f *)




(* Section on perm_WF *)
Lemma monotonic_perm_WF n m f : perm_WF n f -> n <= m ->
  perm_WF m f.
<<<<<<< Updated upstream
>>>>>>> Stashed changes
=======
>>>>>>> Stashed changes
Proof.
  intros HWF Hnm k Hk.
  apply HWF; lia.
Qed.

<<<<<<< Updated upstream
<<<<<<< Updated upstream
Global Hint Resolve monotonic_WF_perm : WF_perm_db.

Lemma compose_WF_perm n f g : WF_perm n f -> WF_perm n g -> 
  WF_perm n (f ∘ g).
=======
=======
>>>>>>> Stashed changes
Global Hint Resolve monotonic_perm_WF : perm_WF_db.

Lemma compose_perm_WF n f g : perm_WF n f -> perm_WF n g -> 
  perm_WF n (f ∘ g).
<<<<<<< Updated upstream
>>>>>>> Stashed changes
=======
>>>>>>> Stashed changes
Proof.
  unfold compose.
  intros Hf Hg k Hk.
  rewrite Hg, Hf; easy.
Qed.

<<<<<<< Updated upstream
<<<<<<< Updated upstream
Global Hint Resolve compose_WF_perm : WF_perm_db.
=======
Global Hint Resolve compose_perm_WF : perm_WF_db.
>>>>>>> Stashed changes
=======
Global Hint Resolve compose_perm_WF : perm_WF_db.
>>>>>>> Stashed changes

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


Lemma permutation_of_le_permutation_WF f m n : (m <= n)%nat -> permutation m f ->
  WF_perm m f -> permutation n f.
Proof.
  intros Hmn [finv_m Hfinv_m] HWF.
  exists (fun k => if m <=? k then k else finv_m k).
  intros k Hk.
  bdestruct (m <=? k).
  - rewrite HWF; bdestructΩ'.
  - specialize (Hfinv_m _ H).
    bdestructΩ'.
Qed.

<<<<<<< Updated upstream
(* FIXME: ^ All this is now in QuantumLib*)


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

Global Hint Resolve swap_WF_perm : WF_perm_db.

Lemma swap_perm_bdd a b n : a < n -> b < n ->
  forall k, k < n -> swap_perm a b n k < n.
Proof.
  intros Ha Hb k Hk.
  unfold swap_perm.
  bdestructΩ'.
Qed.

<<<<<<< Updated upstream
Global Hint Resolve swap_perm_bdd : perm_bdd_db.

Lemma swap_perm_inv a b n : a < n -> b < n -> 
  (swap_perm a b n) ∘ (swap_perm a b n) = idn.
Proof.
=======
=======
>>>>>>> Stashed changes

















(* TODO FIXME: Should this really be here? *)
(* Section on swap_perm, swaps two elements. TODO: Do we even want this?
	 We have swap_2_perm and fswap... Also, should swap_perm be defined in 
	 terms of fswap? *)
Lemma swap_perm_same a n :
  swap_perm a a n = idn.
Proof.
  unfold swap_perm.
  apply functional_extensionality; intros k.
  destruct_if_solve.
Qed.

#[export] Hint Rewrite swap_perm_same : perm_cleanup_db.

Lemma swap_perm_comm a b n :
  swap_perm a b n = swap_perm b a n.
Proof.
  apply functional_extensionality; intros k.
  unfold swap_perm.
  destruct_if_solve.
Qed.

Lemma swap_perm_WF a b n : forall k, n <= k -> swap_perm a b n k = k.
Proof.
  intros.
  unfold swap_perm. 
  destruct_if_solve.
Qed.

Global Hint Resolve swap_perm_WF : perm_WF_db.

Lemma swap_perm_bdd a b n : a < n -> b < n ->
  forall k, k < n -> swap_perm a b n k < n.
<<<<<<< Updated upstream
Proof.
  intros Ha Hb k Hk.
  unfold swap_perm.
  destruct_if_solve.
Qed.

Global Hint Resolve swap_perm_bdd : perm_bdd_db.

Lemma swap_perm_inv a b n : a < n -> b < n -> 
  (swap_perm a b n) ∘ (swap_perm a b n) = idn.
Proof.
>>>>>>> Stashed changes
=======
Proof.
  intros Ha Hb k Hk.
  unfold swap_perm.
  destruct_if_solve.
Qed.

Global Hint Resolve swap_perm_bdd : perm_bdd_db.

Lemma swap_perm_inv a b n : a < n -> b < n -> 
  (swap_perm a b n) ∘ (swap_perm a b n) = idn.
Proof.
>>>>>>> Stashed changes
  intros Ha Hb.
  unfold compose.
  apply functional_extensionality; intros k.
  unfold swap_perm.
<<<<<<< Updated upstream
<<<<<<< Updated upstream
  bdestructΩ'.
=======
  destruct_if_solve.
>>>>>>> Stashed changes
=======
  destruct_if_solve.
>>>>>>> Stashed changes
Qed.

#[export] Hint Rewrite swap_perm_inv : perm_inv_db.

Lemma swap_perm_2_perm a b n : a < n -> b < n ->
  permutation n (swap_perm a b n).
Proof.
  intros Ha Hb.
  perm_by_inverse (swap_perm a b n).
Qed.

Global Hint Resolve swap_perm_2_perm : perm_db.

Lemma swap_perm_S_permutation a n (Ha : S a < n) :
  permutation n (swap_perm a (S a) n).
Proof.
  apply swap_perm_2_perm; lia.
Qed.

Global Hint Resolve swap_perm_S_permutation : perm_db.

Lemma compose_swap_perm a b c n : a < n -> b < n -> c < n -> 
  b <> c -> a <> c ->
  (swap_perm a b n ∘ swap_perm b c n ∘ swap_perm a b n) = swap_perm a c n.
Proof.
  intros Ha Hb Hc Hbc Hac. 
  apply functional_extensionality; intros k.
  unfold compose, swap_perm.
<<<<<<< Updated upstream
<<<<<<< Updated upstream
  bdestructΩ'.
=======
  destruct_if_solve.
>>>>>>> Stashed changes
=======
  destruct_if_solve.
>>>>>>> Stashed changes
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
<<<<<<< Updated upstream
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

Fixpoint swap_list_spec l : bool :=
  match l with 
  | [] => true
  | k :: ks => (k <? S (length ks)) && swap_list_spec ks
  end.

Fixpoint perm_of_swap_list l :=
  match l with
  | [] => idn
  | k :: ks => let n := length ks in
    (swap_perm k n (S n) ∘ (perm_of_swap_list ks))
  end.

Fixpoint invperm_of_swap_list l :=
  match l with 
  | [] => idn
  | k :: ks => let n := length ks in
    ((invperm_of_swap_list ks) ∘ swap_perm k n (S n))
  end.

Local Opaque perm_inv.
Lemma perm_of_swap_list_WF l : swap_list_spec l = true ->
<<<<<<< Updated upstream
  WF_perm (length l) (perm_of_swap_list l).
=======
  perm_WF (length l) (perm_of_swap_list l).
>>>>>>> Stashed changes
Proof.
  induction l.
  - easy.
  - simpl.
    rewrite andb_true_iff.
    intros [Ha Hl].
    intros k Hk.
    unfold compose.
    rewrite IHl; [|easy|lia].
<<<<<<< Updated upstream
    rewrite swap_WF_perm; easy.
Qed.

Lemma invperm_of_swap_list_WF l : swap_list_spec l = true ->
  WF_perm (length l) (invperm_of_swap_list l).
=======
    rewrite swap_perm_WF; easy.
Qed.

Lemma invperm_of_swap_list_WF l : swap_list_spec l = true ->
  perm_WF (length l) (invperm_of_swap_list l).
>>>>>>> Stashed changes
=======
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

Fixpoint swap_list_spec l : bool :=
  match l with 
  | [] => true
  | k :: ks => (k <? S (length ks)) && swap_list_spec ks
  end.

Fixpoint perm_of_swap_list l :=
  match l with
  | [] => idn
  | k :: ks => let n := length ks in
    (swap_perm k n (S n) ∘ (perm_of_swap_list ks))
  end.

Fixpoint invperm_of_swap_list l :=
  match l with 
  | [] => idn
  | k :: ks => let n := length ks in
    ((invperm_of_swap_list ks) ∘ swap_perm k n (S n))
  end.

Local Opaque perm_inv.
Lemma perm_of_swap_list_WF l : swap_list_spec l = true ->
  perm_WF (length l) (perm_of_swap_list l).
>>>>>>> Stashed changes
Proof.
  induction l.
  - easy.
  - simpl.
    rewrite andb_true_iff.
    intros [Ha Hl].
    intros k Hk.
    unfold compose.
<<<<<<< Updated upstream
<<<<<<< Updated upstream
    rewrite swap_WF_perm; [|easy].
    rewrite IHl; [easy|easy|lia].
Qed.

Global Hint Resolve perm_of_swap_list_WF invperm_of_swap_list_WF : WF_perm_db.
=======
    rewrite swap_perm_WF; [|easy].
    rewrite IHl; [easy|easy|lia].
Qed.

Global Hint Resolve perm_of_swap_list_WF invperm_of_swap_list_WF : perm_WF_db.
>>>>>>> Stashed changes

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
=======
    rewrite IHl; [|easy|lia].
    rewrite swap_perm_WF; easy.
Qed.

Lemma invperm_of_swap_list_WF l : swap_list_spec l = true ->
  perm_WF (length l) (invperm_of_swap_list l).
Proof.
  induction l.
  - easy.
  - simpl.
    rewrite andb_true_iff.
    intros [Ha Hl].
    intros k Hk.
    unfold compose.
    rewrite swap_perm_WF; [|easy].
    rewrite IHl; [easy|easy|lia].
Qed.

Global Hint Resolve perm_of_swap_list_WF invperm_of_swap_list_WF : perm_WF_db.

Lemma invperm_linv_perm_of_swap_list l : swap_list_spec l = true ->
  invperm_of_swap_list l ∘ perm_of_swap_list l = idn.
>>>>>>> Stashed changes
Proof.
  induction l.
  - easy.
  - simpl. 
    rewrite andb_true_iff.
    intros [Ha Hl].
<<<<<<< Updated upstream
    rewrite <- Combinators.compose_assoc,
    (Combinators.compose_assoc _ _ _ _ (invperm_of_swap_list _)).
    rewrite (IHl Hl).
    rewrite compose_idn_r.
    rewrite swap_perm_inv; [easy| |lia].
    bdestructΩ (a <? S (length l)).
Qed.

#[export] Hint Rewrite invperm_linv_perm_of_swap_list 
  invperm_rinv_perm_of_swap_list : perm_cleanup_db.


(* FIXME: Remove; for working reference*)
Fixpoint insertion_sort_list n f := 
  match n with 
  | 0 => []
  | S n' => let k := (perm_inv (S n') f n') in
      k :: insertion_sort_list n' (fswap f k n')
  end.

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

Lemma insertion_sort_list_is_swap_list n f : 
  swap_list_spec (insertion_sort_list n f) = true.
=======
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


(* FIXME: Remove; for working reference*)
Fixpoint insertion_sort_list n f := 
  match n with 
  | 0 => []
  | S n' => let k := (perm_inv (S n') f n') in
      k :: insertion_sort_list n' (fswap f k n')
  end.

Lemma length_insertion_sort_list n f :
  length (insertion_sort_list n f) = n.
>>>>>>> Stashed changes
Proof.
  revert f;
  induction n;
  intros f.
  - easy.
  - simpl.
<<<<<<< Updated upstream
=======
    rewrite IHn; easy.
Qed.

Lemma insertion_sort_list_is_swap_list n f : 
  swap_list_spec (insertion_sort_list n f) = true.
Proof.
  revert f;
  induction n;
  intros f.
  - easy.
  - simpl.
>>>>>>> Stashed changes
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

Global Hint Resolve rotr_perm rotl_perm : perm_db.


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

