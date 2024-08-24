(** The definition of and facts about bipermutations (involutive 
  fixed-point-free permutations) that don't involve or require matrices 
**)

(* Require Import ZXCore. *)
Require Import CoreRules.
Import CoreData CoreAutomation.
Import CastRules.
From QuantumLib Require Import Bits.
Require Export QuantumLib.Permutations.
Import QuantumLib.VectorStates Modulus Kronecker.
Require Export BipermAux.
Export Setoid.

Open Scope prg.
Open Scope nat_scope.

(* Section Bipermutations.v *)


(* ORDERING: Bottom to top, outputs first. I.e., 
7  \/ —     3
6  /\ \/    2
5  —  /\ ╲  1
4  —  —  ╱  0
*)

Create HintDb biperm_db.

(* Section Bipermutations. *)

Local Open Scope nat.

Definition bipermutation n f :=
  (forall k : nat, k < n -> f k < n /\ f k <> k /\ f (f k) = k).

Add Parametric Morphism n : (bipermutation n) with signature
  perm_eq n ==> iff as bipermutation_of_perm_eq.
Proof.
  enough (H : forall x y : nat -> nat,
  perm_eq n x y -> bipermutation n x -> bipermutation n y) by 
  (intros; split; apply H; easy).
  intros f g Hfg.
  unfold bipermutation.
  intros Hf k Hk.
  destruct (Hf k Hk) as (? & ? & ?).
  rewrite <- !Hfg by easy.
  easy.
Qed.

Lemma bipermutation_change_dims n m f : n = m ->
  bipermutation m f -> bipermutation n f.
Proof.
  now intros [].
Qed.

Lemma bipermutation_defn n f : 
  bipermutation n f <-> 
  (perm_bounded n f /\ (forall k, k < n -> f k <> k) 
    /\ perm_eq n (f ∘ f) idn).
Proof.
  split.
  - intros Hf; repeat split; intros ? ?; now apply Hf.
  - unfold compose. intros (? & ? & ?) k Hk; auto.
Qed.

Lemma permutation_of_bipermutation {n f} : bipermutation n f -> permutation n f.
Proof.
  intros Hbiperm.
  exists f.
  intros k Hk.
  repeat split.
  all: apply Hbiperm, Hk.
Qed.

#[export] Hint Resolve permutation_of_bipermutation : perm_db biperm_db.

Lemma perm_inv_bipermutation n f (Hf : bipermutation n f) : 
  perm_eq n (perm_inv n f) f.
Proof.
  rewrite <- (compose_idn_r (perm_inv n f)).
  rewrite compose_perm_inv_l by cleanup_perm.
  symmetry.
  exact (fun k Hk => proj2 (proj2 (Hf k Hk))).
Qed.

Lemma bipermutation_defn_alt n f : 
  bipermutation n f <-> 
  (permutation n f /\ (forall k, k < n -> f k <> k) 
    /\ perm_eq n (perm_inv n f) f).
Proof.
  split.
  - intros Hf.
    repeat split.
    + auto with perm_db.
    + now apply bipermutation_defn in Hf.
    + now apply perm_inv_bipermutation.
  - intros (? & ? & Hfinv).
    rewrite bipermutation_defn.
    intuition auto with perm_db.
    rewrite <- Hfinv at 1.
    cleanup_perm_inv.
Qed.

Lemma bipermutation_is_bounded n f : bipermutation n f -> 
  perm_bounded n f.
Proof.
  intros Hf k Hk; now apply Hf.
Qed. 

#[export] Hint Resolve bipermutation_is_bounded : perm_bounded_db.

Lemma bipermutation_involutive {n f} k : bipermutation n f -> k < n ->
  f (f k) = k.
Proof.
  intros Hbiperm Hk.
  apply (Hbiperm k Hk).
Qed.

Lemma bipermutation_dim_ne_1 {n f} (Hf : bipermutation n f) : 
  n <> 1.
Proof.
  intros contra.
  specialize (Hf 0).
  lia.
Qed.

(* #[export] Hint Rewrite @bipermutation_involutive 
  using (solve [auto with biperm_db perm_db perm_bounded_db zarith]) :
  perm_cleanup_db. *)

Lemma bipermutation_eqb_iff {n f} a b : bipermutation n f -> a < n -> b < n ->
  f a =? b = (a =? f b).
Proof.
  intros Hbiperm Ha Hb.
  rewrite <- (bipermutation_involutive b Hbiperm Hb) at 1.
  rewrite (permutation_eqb_iff a (f b) (permutation_of_bipermutation Hbiperm) Ha).
  - easy.
  - apply Hbiperm, Hb.
Qed.

Lemma bipermutation_eq_iff {n f} a b : bipermutation n f -> a < n -> b < n ->
  f a = b <-> a = f b.
Proof.
  intros Hbiperm Ha Hb.
  pose proof (bipermutation_eqb_iff a b Hbiperm Ha Hb) as H.
  revert H.
  bdestructΩ'.
Qed.

Lemma bipermutation_injective {n} {g : nat -> nat} 
  (Hg : bipermutation n g) i j (Hi : i < n) (Hj : j < n) : 
  g i = g j <-> i = j.
Proof.
  rewrite (bipermutation_eq_iff _ _ Hg), (proj2 (proj2 (Hg j Hj)));
  lia + apply Hg; lia.
Qed.

Lemma bipermutation_shift_of_eq_swap n f 
  (Hf : bipermutation n f) (Hfsmall : perm_eq 2 f swap_2_perm) : 
  bipermutation (n - 2) (fun k => f (k + 2) - 2).
Proof.
  intros k Hk.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (Hf (k + 2)).
  assert (2 <= f (k + 2)). 1: {
    enough (~ (f (k + 2) = 0 \/ f (k + 2) = 1)) by lia.
    rewrite 2!(bipermutation_eq_iff _ _ Hf) by lia.
    rewrite 2!Hfsmall by lia.
    cbn; lia.
  }
  repeat split.
  - lia.
  - lia. 
  - rewrite Nat.sub_add by lia; lia.
Qed.

Lemma bipermutation_shrink_of_eq_swap n f 
  (Hf : bipermutation n f) 
  (Hfbig : perm_eq 2 
    (fun k => f ((n - 2) + k)) (fun k => swap_2_perm k + (n - 2))) : 
  bipermutation (n - 2) f.
Proof.
  intros k Hk.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (Hf k ltac:(lia)).
  repeat split; [|easy..].
  enough (~ (f k = n - 2 \/ f k = n - 1)) by lia.
  rewrite 2!(bipermutation_eq_iff _ _ Hf) by lia.
  replace (n - 2) with (n - 2 + 0) by lia.
  replace (n - 1) with (n - 2 + 1) by lia.
  rewrite 2!Hfbig by lia.
  lia.
Qed.


(* TODO: Flip _l and _r here *)
Definition biperm_compose_perm_l n m f g : nat -> nat :=
  (* f is a biperm on n + m, g a perm on n; 
     graphically, we put g on the left of f *)
  fun k => 
  if k <? n then
    (if f (g k) <? n then 
      perm_inv n g (f (g k))
    else 
      f (g k))
  else
    (if k <? n + m then 
      (if f k <? n then 
        perm_inv n g (f k)
      else
        f k)
    else 
      k).

Definition biperm_compose_perm_r n m f g : nat -> nat :=
  (* f is a biperm on n + m, g a perm on m; 
     graphically, we put g on the right of f *)
  fun k => 
  if n + m <=? k then k else
  if k <? n then 
    if f k <? n then f k else
      n + perm_inv m g (f k - n)
  else 
    if f (n + g (k - n)) <? n then 
      f (n + g (k - n))
    else
      n + perm_inv m g (f (n + g (k - n)) - n).

Lemma biperm_compose_perm_l_spec n m f g : 
  perm_eq (n + m) 
  (biperm_compose_perm_l n m f g)
  (stack_perms n m (perm_inv n g) idn ∘ f ∘ stack_perms n m g idn).
Proof.
  rewrite (stack_perms_defn n m g).
  rewrite stack_perms_f_idn.
  intros k Hk.
  unfold biperm_compose_perm_l.
  unfold compose.
  rewrite !(if_dist _ _ _ f).
  bdestruct (k <? n);
  [|rewrite Nat.sub_add by lia];
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_r_spec n m f g 
  (Hf : perm_bounded (n + m) f) (Hg : perm_bounded m g) : 
  perm_eq (n + m) 
  (biperm_compose_perm_r n m f g)
  (stack_perms n m idn (perm_inv m g) ∘ f ∘ stack_perms n m idn g).
Proof.
  rewrite (stack_perms_defn n m idn g).
  rewrite stack_perms_idn_f.
  intros k Hk.
  unfold biperm_compose_perm_r.
  unfold compose.
  rewrite !(if_dist _ _ _ f).
  pose proof (Hf k Hk).
  rewrite (Nat.add_comm n (g (k - n))).
  simplify_bools_lia_one_kernel.
  bdestructΩ'.
  pose proof (Hg (k - n)).
  pose proof (Hf (g (k - n) + n)).
  lia.
Qed.

Lemma biperm_compose_perm_l_WF n m f g :
  WF_Perm (n + m) (biperm_compose_perm_l n m f g).
Proof.
  unfold biperm_compose_perm_l.
  intros k Hk; bdestructΩ'.
Qed.

Lemma biperm_compose_perm_r_WF n m f g :
  WF_Perm (n + m) (biperm_compose_perm_r n m f g).
Proof.
  unfold biperm_compose_perm_r.
  intros k Hk; bdestructΩ'.
Qed.

#[export] Hint Resolve biperm_compose_perm_l_WF
  biperm_compose_perm_r_WF : WF_Perm_db. 

Add Parametric Morphism n m : (biperm_compose_perm_r n m) with signature
  on_predicate_relation_l (fun f => perm_bounded (n + m) f) 
    (perm_eq (n + m)) ==> 
  on_predicate_relation_l (fun f => perm_bounded m f) 
    (perm_eq m) ==> eq as 
    biperm_compose_perm_r_eq_of_perm_eq.
Proof.
  intros f f' [Hfbdd Hf] g g' [Hgbdd Hg].
  eq_by_WF_perm_eq (n + m).
  intros k Hk.
  unfold biperm_compose_perm_r.
  simplify_bools_lia_one_kernel.
  rewrite <- (Hf k Hk).
  pose proof (Hfbdd k Hk).
  bdestruct (k <? n).
  - bdestructΩ'.
    now rewrite <- (perm_inv_eq_of_perm_eq _ _ _ Hg) by lia.
  - rewrite <- Hg by lia.
    pose proof (Hgbdd (k - n)).
    rewrite <- Hf by lia.
    bdestructΩ'.
    pose proof (Hfbdd (n + g (k - n))).
    now rewrite <- (perm_inv_eq_of_perm_eq _ _ _ Hg) by lia.
Qed.

Add Parametric Morphism n m : (biperm_compose_perm_l n m) with signature
  on_predicate_relation_l (fun f => perm_bounded (n + m) f) 
    (perm_eq (n + m)) ==> 
  on_predicate_relation_l (fun f => perm_bounded n f) 
    (perm_eq n) ==> eq as 
    biperm_compose_perm_l_eq_of_perm_eq.
Proof.
  intros f f' [Hfbdd Hf] g g' [Hgbdd Hg].
  eq_by_WF_perm_eq (n + m).
  intros k Hk.
  unfold biperm_compose_perm_l.
  simplify_bools_lia_one_kernel.
  rewrite <- (Hf k Hk).
  pose proof (Hfbdd k Hk).
  bdestruct (k <? n).
  - pose proof (Hgbdd k).
    rewrite <- Hg, <- Hf by lia.
    bdestructΩ'.
    now rewrite <- (perm_inv_eq_of_perm_eq _ _ _ Hg) by lia.
  - bdestructΩ'.
    now apply perm_inv_eq_of_perm_eq.
Qed.

(* TODO: Like the above, but only for the biperm / perm; can we do better? *)

Lemma biperm_compose_perm_l_bounded n m f g 
  (Hf : perm_bounded (n + m) f) (Hg : perm_bounded n g) :
  perm_bounded (n + m) (biperm_compose_perm_l n m f g).
Proof.
  unfold biperm_compose_perm_l.
  intros.
  bdestructΩ'.
  - pose proof (perm_inv_bounded n g (f (g k)) ltac:(easy)).
    lia.
  - apply Hf.
    specialize (Hg k ltac:(easy)); lia.
  - pose proof (perm_inv_bounded n g (f k) ltac:(easy)).
    lia.
  - apply Hf; easy.
Qed.

Lemma biperm_compose_perm_r_bounded n m f g 
  (Hf : perm_bounded (n + m) f) (Hg : perm_bounded m g) :
  perm_bounded (n + m) (biperm_compose_perm_r n m f g).
Proof.
  unfold biperm_compose_perm_r.
  intros.
  bdestructΩ'.
  - apply Nat.add_lt_mono_l.
    apply perm_inv_bounded.
    specialize (Hf k ltac:(easy)).
    apply sub_lt_iff; [lia|].
    apply Hf.
  - apply Nat.add_lt_mono_l.
    pose proof (Hf k) as ?.
    apply perm_inv_bounded.
    apply sub_lt_iff; [lia|].
    apply Hf.
    apply Nat.add_lt_mono_l, Hg.
    lia.
Qed.

#[export] Hint Resolve biperm_compose_perm_l_bounded
  biperm_compose_perm_r_bounded : perm_bounded_db. 



Lemma biperm_compose_perm_r_biperm n m f g 
  (Hf : bipermutation (n + m) f) (Hg : permutation m g) : 
  bipermutation (n + m) (biperm_compose_perm_r n m f g).
Proof.
  intros k Hk.
  pose proof (fun k Hk => proj1 (Hf k Hk)) as Hfbdd.
  pose proof (fun k Hk => proj1 (proj2 (Hf k Hk))) as Hfne.
  pose proof (fun k Hk => proj2 (proj2 (Hf k Hk))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (Hgbdd (k - n)).
  pose proof (Hfbdd (n + g (k - n))).
  split; [auto with perm_bounded_db perm_db | split].
  - unfold biperm_compose_perm_r.
    bdestructΩ'; [apply Hf; easy|].
    intros Hfalse.
    assert (Hginveq : perm_inv m g (f (n + g (k - n)) - n) = k - n) by lia.
    rewrite perm_inv_eq_iff in Hginveq by (easy + lia).
    specialize (Hf (n + g (k - n))); lia.
  - bdestruct (n <=? k).
    + unfold biperm_compose_perm_r.
      do 2 simplify_bools_lia_one_kernel.
      pose proof (perm_inv_bounded m g (f (n + g (k - n)) - n)).
      replace (n + m <=?
      (if f (n + g (k - n)) <? n
       then f (n + g (k - n))
       else n + perm_inv m g (f (n + g (k - n)) - n))) with false by
       (bdestructΩ').
      rewrite !(if_dist _ _ _ f).
      rewrite Hfeq by lia.
      pose proof (Hfeq (n + g (k - n)) ltac:(lia)).
      bdestructΩ'simp.
      * rewrite add_sub'.
        cleanup_perm; lia.
      * rewrite add_sub' in *.
        rewrite perm_inv_is_rinv_of_permutation in * by (easy + lia).
        rewrite Nat.add_sub_assoc, add_sub' in * by lia.
        lia.
      * rewrite add_sub'.
        cleanup_perm.
        rewrite le_plus_minus_r' by lia.
        rewrite Hfeq, add_sub' by lia.
        cleanup_perm; lia.
    + unfold biperm_compose_perm_r.
      pose proof (Hfbdd k ltac:(easy)).
      do 2 simplify_bools_lia_one_kernel.
      pose proof (perm_inv_bounded m g (f k - n)).
      replace (n + m <=? (if f k <? n then f k
        else n + perm_inv m g (f k - n)))
        with false by bdestructΩ'.
      rewrite (if_dist' f).
      rewrite Hfeq by lia.
      bdestructΩ';
      rewrite add_sub' in *; 
      rewrite perm_inv_is_rinv_of_permutation in * by auto with zarith;
      rewrite Nat.add_sub_assoc, add_sub', Hfeq in *; 
      lia.
Qed.

Lemma biperm_compose_perm_l_biperm n m f g 
  (Hf : bipermutation (n + m) f) (Hg : permutation n g) : 
  bipermutation (n + m) (biperm_compose_perm_l n m f g).
Proof.
  intros k Hk.
  pose proof (fun k Hk => proj1 (Hf k Hk)) as Hfbdd.
  pose proof (fun k Hk => proj1 (proj2 (Hf k Hk))) as Hfne.
  pose proof (fun k Hk => proj2 (proj2 (Hf k Hk))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (Hgbdd k).
  split; [auto with perm_bounded_db perm_db | split].
  - unfold biperm_compose_perm_l.
    bdestructΩ';
    rewrite ?perm_inv_eq_iff by (easy + lia);
    [apply Hf; lia|..].
    + pose proof (perm_inv_bounded n g (f k)); lia.
    + apply Hf; lia.
  - bdestruct (n <=? k).
    + unfold biperm_compose_perm_l.
      do 2 simplify_bools_lia_one_kernel.
      pose proof (perm_inv_bounded n g (f k)).
      bdestructΩ'; cleanup_perm;
      rewrite ?perm_inv_is_rinv_of_permutation in * by (easy + lia);
      rewrite ?Hfeq in * by lia; try lia.
      specialize (Hf k); lia.
    + unfold biperm_compose_perm_l.
      pose proof (Hfbdd k ltac:(easy)).
      simplify_bools_lia_one_kernel.
      pose proof (perm_inv_bounded n g (f (g k))).
      rewrite (if_dist' f).
      rewrite Hfeq by lia.
      pose proof (Hfbdd (g k)).
      bdestruct (f (g k) <? n); 
      [|bdestructΩ'; cleanup_perm].
      simplify_bools_lia_one_kernel. 
      cleanup_perm.
      rewrite Hfeq by lia.
      bdestructΩ'; cleanup_perm.
Qed.



Lemma biperm_compose_perm_l_compose n m f g h 
  (Hf : bipermutation (n + m) f)
  (Hg : permutation n g) (Hh : permutation n h) :
  forall k, 
  biperm_compose_perm_l n m (biperm_compose_perm_l n m f g) h k =
  biperm_compose_perm_l n m f (g ∘ h)%prg k.
Proof.
  intros k.
  unfold biperm_compose_perm_l.
  pose proof (fun k Hk => proj1 (Hf k Hk)) as Hfbdd.
  (* pose proof (fun k Hk => proj1 (proj2 (Hf k Hk))) as Hfne. *)
  (* pose proof (fun k Hk => proj2 (proj2 (Hf k Hk))) as Hfeq. *)
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (permutation_is_bounded _ _ Hh) as Hhbdd.
  pose proof (permutation_compose n g h Hg Hh) as Hgh.
  bdestructΩ'; 
  rewrite ?perm_inv_compose; try easy + lia;
  let show_lt := (match goal with
  | |- context[g ?k] => specialize (Hgbdd k); lia
  | |- context[h ?k] => specialize (Hhbdd k); lia
  end; lia) in 
  let do_tac := first 
  [ assumption | 
    apply perm_inv_bounded; lia | show_lt |
    unfold compose in *; lia |
    apply Hgbdd; lia | apply Hhbdd; lia | apply Hfbdd; lia |
    match goal with
    | H : perm_inv _ _ _ >= _ |- _ =>
      apply perm_inv_ge in H
    | |- perm_inv _ _ _ = _ =>
      apply perm_inv_eq_iff
  end]
  in repeat do_tac.
Qed.

Lemma biperm_compose_perm_l_compose_eq (n m : nat) (f g h : nat -> nat) :
  bipermutation (n + m) f ->
  permutation n g ->
  permutation n h ->
  biperm_compose_perm_l n m (biperm_compose_perm_l n m f g) h =
  biperm_compose_perm_l n m f (g ∘ h).
Proof.
  intros.
  apply functional_extensionality.
  now apply biperm_compose_perm_l_compose.
Qed.

Lemma biperm_compose_perm_r_compose n m f g h 
  (Hf : bipermutation (n + m) f)
  (Hg : permutation m g) (Hh : permutation m h) :
  forall k, 
  biperm_compose_perm_r n m (biperm_compose_perm_r n m f g) h k =
  biperm_compose_perm_r n m f (fun x => g (h x)) k.
Proof.
  intros k.
  pose proof (fun k Hk => proj1 (Hf k Hk)) as Hfbdd.
  pose proof (fun k Hk => proj1 (proj2 (Hf k Hk))) as Hfne.
  pose proof (fun k Hk => proj2 (proj2 (Hf k Hk))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (permutation_is_bounded _ _ Hh) as Hhbdd.
  pose proof (permutation_compose m g h Hg Hh) as Hgh.
  unfold Basics.compose in Hgh.
  unfold biperm_compose_perm_r.
  pose proof (Hfbdd k).
  bdestructΩ'; 
  rewrite ?perm_inv_compose; try easy + lia;
  rewrite ?add_sub' in *;
  let show_lt := (match goal with
  | |- context[g ?k] => specialize (Hgbdd k); lia
  | |- context[h ?k] => specialize (Hhbdd k); lia
  end; lia) in 
  let do_tac := first 
  [ assumption | 
    apply perm_inv_bounded | show_lt |
    apply Hgbdd | apply Hhbdd | apply Hfbdd |
    match goal with
    | |- ?n + _ < ?n + _ =>
      apply Nat.add_lt_mono_l
    | |- _ - _ < _ =>
      apply sub_lt_iff; [lia|]
    | |- ?n - ?m = ?k =>
      enough (n = k + m) by lia
    | |- ?n + _ = ?n + _ =>
      apply Nat.add_cancel_l
    | H : _ <= perm_inv _ _ _ |- _ =>
      let e := eval unfold ge in perm_inv_ge in 
      apply e in H
    | H : ?n + _ <= ?n + _ |- _ =>
      apply add_le_cancel_l_iff in H
    | |- perm_inv _ _ _ = _ =>
      apply perm_inv_eq_iff
    | |- ?n <= ?k => 
      bdestruct (n <=? k); [easy|];
      specialize (Hgbdd k ltac:(easy)); lia
  end |
  rewrite (perm_inv_is_rinv_of_permutation _ _ Hgh) |
  lia]
  in repeat do_tac.
Qed.

Lemma biperm_compose_perm_r_compose_eq n m f g h : 
  bipermutation (n + m) f -> permutation m g -> permutation m h ->
  biperm_compose_perm_r n m (biperm_compose_perm_r n m f g) h =
  biperm_compose_perm_r n m f (g ∘ h).
Proof.
  intros Hf Hg Hh.
  apply functional_extensionality.
  unfold compose.
  now apply biperm_compose_perm_r_compose.
Qed.

Lemma biperm_compose_perm_l_r_swap n m f g h : 
  bipermutation (n + m) f -> permutation n g -> permutation m h ->
  forall k,
  biperm_compose_perm_l n m (biperm_compose_perm_r n m f h) g k =
  biperm_compose_perm_r n m (biperm_compose_perm_l n m f g) h k.
Proof.
  intros Hf Hg Hh.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (permutation_is_bounded _ _ Hh) as Hhbdd.
  pose proof (perm_inv_bounded n g) as Hginvbdd.
  pose proof (perm_inv_bounded m h) as Hhinvbdd.
  intros k.
  unfold biperm_compose_perm_l, biperm_compose_perm_r.
  bdestruct (n + m <=? k);
  [now simplify_bools_lia|].
  replace_bool_lia (k <? n + m) true.
  replace_bool_lia (n + h (k - n) <? n) false.
  pose proof (Hgbdd k).
  pose proof (Hhbdd (k - n)).
  bdestruct (k <? n).
  - pose proof (Hginvbdd (f (g k))).
    bdestructΩ'.
  - replace_bool_lia (n + h (k - n) <? n + m) true.
    pose proof (Hginvbdd (f (n + h (k - n)))).
    bdestructΩ'.
Qed.

Lemma biperm_compose_perm_l_r_swap_eq (n m : nat) (f g h : nat -> nat) : 
  bipermutation (n + m) f ->
  permutation n g ->
  permutation m h ->
  biperm_compose_perm_l n m (biperm_compose_perm_r n m f h) g =
  biperm_compose_perm_r n m (biperm_compose_perm_l n m f g) h.
Proof.
  intros.
  apply functional_extensionality.
  now apply biperm_compose_perm_l_r_swap.
Qed.

Lemma biperm_compose_perm_r_lt_small n m f g : 
  forall k, k < n ->
  biperm_compose_perm_r n m f g k < n <-> f k < n.
Proof.
  intros k Hk.
  unfold biperm_compose_perm_r.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_r_lt_big n m f g : 
  forall k, n <= k -> k < n + m ->
  biperm_compose_perm_r n m f g k < n <-> f (n + g (k - n)) < n.
Proof.
  intros k Hkl Hku.
  unfold biperm_compose_perm_r.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_r_ltb_small n m f g : 
  forall k, k < n ->
  biperm_compose_perm_r n m f g k <? n = (f k <? n).
Proof.
  intros k Hk.
  unfold biperm_compose_perm_r.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_r_ltb_big n m f g : 
  forall k, n <= k -> k < n + m ->
  biperm_compose_perm_r n m f g k <? n = (f (n + g (k - n)) <? n).
Proof.
  intros k Hkl Hku.
  unfold biperm_compose_perm_r.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_l_lt_small n m f g : 
  forall k, k < n ->
  biperm_compose_perm_l n m f g k < n <-> f (g k) < n.
Proof.
  intros k Hk.
  unfold biperm_compose_perm_l.
  simplify_bools_lia_one_kernel.
  pose proof (perm_inv_bounded n g (f (g k))).
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_l_lt_big n m f g : 
  forall k, n <= k -> k < n + m ->
  biperm_compose_perm_l n m f g k < n <-> f k < n.
Proof.
  intros k Hkl Hku.
  unfold biperm_compose_perm_l.
  do 2 simplify_bools_lia_one_kernel.
  pose proof (perm_inv_bounded n g (f k)).
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_l_ltb_small n m f g : 
  forall k, k < n ->
  biperm_compose_perm_l n m f g k <? n = (f (g k) <? n).
Proof.
  intros k Hk.
  unfold biperm_compose_perm_l.
  simplify_bools_lia_one_kernel.
  pose proof (perm_inv_bounded n g (f (g k))).
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_l_ltb_big n m f g : 
  forall k, n <= k -> k < n + m ->
  biperm_compose_perm_l n m f g k <? n = (f k <? n).
Proof.
  intros k Hkl Hku.
  unfold biperm_compose_perm_l.
  do 2 simplify_bools_lia_one_kernel.
  pose proof (perm_inv_bounded n g (f k)).
  bdestructΩ'.
Qed.

(*TODO: Improve using the _spec lemma and stack_perms_idn_idn *)
Lemma biperm_compose_perm_r_idn n m f 
  (Hf : perm_bounded (m + n) f) : 
  perm_eq (m + n) (biperm_compose_perm_r m n f idn) f.
Proof.
  intros k Hk.
  pose proof (Hf k Hk).
  unfold biperm_compose_perm_r.
  simplify_bools_lia_one_kernel.
  bdestruct (k <? m).
  - bdestructΩ'. 
    rewrite idn_inv; lia.
  - rewrite Nat.add_sub_assoc, add_sub' by lia.
    bdestructΩ'. 
    rewrite idn_inv; lia.
Qed.

(* TODO : 
Lemma biperm_compose_perm_r_idn n m f 
  (Hf : perm_bounded (m + n) f) : 
  perm_eq (m + n) (biperm_compose_perm_r m n f idn) f.
Proof.
  intros k Hk.
  pose proof (Hf k Hk).
  unfold biperm_compose_perm_r.
  simplify_bools_lia_one_kernel.
  bdestruct (k <? m).
  - bdestructΩ'. 
    rewrite idn_inv; lia.
  - rewrite Nat.add_sub_assoc, add_sub' by lia.
    bdestructΩ'. 
    rewrite idn_inv; lia.
Qed.
*)



(* TODO: Fix this definition to have the right order of arguments *)
Definition stack_biperms (n0 m0 n1 m1 : nat) (f g : nat -> nat) : nat -> nat :=
  fun k => if n0 + n1 + m0 + m1 <=? k then k else
  if k <? n0 then 
    if f k <? n0 then f k else n1 + f k
  else if k - n0 <? n1 then 
    if g (k - n0) <? n1 then n0 + g (k - n0) else n0 + m0 + g (k - n0)
  else if k - (n0 + n1) <? m0 then
    if f (k - n1) <? n0 then f (k - n1) else n1 + f (k - n1)
  else (* n0 + n1 + m0 < k < n0 + n1 + m0 + m1 *)
    if g (k - (n0 + m0)) <? n1 then n0 + g (k - (n0 + m0)) 
      else n0 + m0 + g (k - (n0 + m0)).
(* TODO: stack_biperms_spec : stack_biperms m0 n0 m1 n0 f g =
  stack_perms (m0 + n0 + m1) n1
    (stack_perms m0 (n0 + m1) 
      idn (big_swap_perm n0 m1)      <-- big_swap_perm _may_ need args swapped
    ) idn
  stack_perms (m0 + n0) (m1 + n1) f g ∘
  stack_perms (m0 + n0 + m1) n1
    (stack_perms m0 (n0 + m1) 
      idn (big_swap_perm m1 n0)      <-- big_swap_perm _may_ need args swapped
    ) idn
  *)

Lemma stack_biperms_WF n0 m0 n1 m1 f g :
  WF_Perm (m0 + n0 + (m1 + n1)) (stack_biperms n0 m0 n1 m1 f g).
Proof.
  intros i Hi.
  unfold stack_biperms.
  now simplify_bools_lia_one_kernel.
Qed.

#[export] Hint Resolve stack_biperms_WF : WF_Perm_db.

(* Add Parametric Morphism n0 m0 n1 m1 nm0 nm1 
  (H0 : m0 + n0 = nm0) (H1 : m1 + n1 = nm1)
  : (stack_biperms n0 m0 n1 m1) 
  with signature
  perm_eq nm0 ==> perm_eq nm1 ==> eq
  as stack_biperms_eq_of_perm_eq.
Proof.
  subst nm0 nm1.
  intros f f' Hf g g' Hg.
  eq_by_WF_perm_eq (m0 + n0 + (m1 + n1)).
  intros k Hk.
  unfold stack_biperms.
  simplify_bools_lia_one_kernel.
  repeat (apply f_equal_if_precedent; 
  rewrite ?Nat.ltb_lt, ?Nat.ltb_nlt; intros);
  try reflexivity;
  rewrite ?Hf by lia; 
  try reflexivity;
  rewrite ?Hg by lia;
  reflexivity.
Qed. *)

Lemma stack_biperms_eq_of_perm_eq 
  {nm0 f f'} (Hf : perm_eq nm0 f f') 
  {g g' nm1} (Hg : perm_eq nm1 g g') n0 m0 n1 m1  
  (H0 : m0 + n0 = nm0) (H1 : m1 + n1 = nm1)
  : stack_biperms n0 m0 n1 m1 f g = stack_biperms n0 m0 n1 m1 f' g'.
Proof.
  subst nm0 nm1.
  eq_by_WF_perm_eq (m0 + n0 + (m1 + n1)).
  intros k Hk.
  unfold stack_biperms.
  simplify_bools_lia_one_kernel.
  repeat (apply f_equal_if_precedent; 
  rewrite ?Nat.ltb_lt, ?Nat.ltb_nlt; intros);
  try reflexivity;
  rewrite ?Hf by lia; 
  try reflexivity;
  rewrite ?Hg by lia;
  reflexivity.
Qed.

Lemma stack_biperms_bipermutation {n0 n1 m0 m1} {f g} 
  (Hf : bipermutation (n0 + m0) f) (Hg : bipermutation (n1 + m1) g) :
  bipermutation (n0 + n1 + (m0 + m1)) (stack_biperms n0 m0 n1 m1 f g).
Proof.
  intros k Hk.
  pose proof (fun k Hk => proj1 (Hf k Hk)) as Hfbdd.
  pose proof (fun k Hk => proj1 (Hg k Hk)) as Hgbdd.
  pose proof (fun k Hk => proj1 (proj2 (Hf k Hk))) as Hfne.
  pose proof (fun k Hk => proj1 (proj2 (Hg k Hk))) as Hgne.
  pose proof (fun k Hk => proj2 (proj2 (Hf k Hk))) as Hfeq.
  pose proof (fun k Hk => proj2 (proj2 (Hg k Hk))) as Hgeq.
  split; [|split];
  unfold stack_biperms.
  - bdestructΩ';
    match goal with 
    | |- context[f ?k] => specialize (Hfbdd k)
    | |- context[g ?k] => specialize (Hgbdd k)
    end; lia.
  - bdestructΩ';
    match goal with 
    | |- context[f ?k] => specialize (Hfne k)
    | |- context[g ?k] => specialize (Hgne k)
    end; lia.
  - bdestructΩ';
    rewrite ?add_sub' in *;
    multimatch goal with 
    | |- context[f (f ?k)] => specialize (Hfeq k)
    | |- context[g (g ?k)] => specialize (Hgeq k)
    | |- context[f ?k] => pose proof (Hfbdd k)
    | |- context[g ?k] => pose proof (Hgbdd k)
    end; lia.
Qed.

Lemma stack_biperms_bipermutation_alt {n0 n1 m0 m1} {f g} 
  (Hf : bipermutation (m0 + n0) f) (Hg : bipermutation (m1 + n1) g) :
  bipermutation ((m0 + m1) + (n0 + n1)) (stack_biperms n0 m0 n1 m1 f g).
Proof.
  eapply bipermutation_change_dims;
  [|apply stack_biperms_bipermutation;
    (eapply bipermutation_change_dims; 
    [|eassumption])]; lia.
Qed.

Definition idn_biperm (n : nat) : nat -> nat :=
  fun k => if n + n <=? k then k else
  if k <? n then n + k else k - n.

Lemma idn_biperm_bipermutation n : 
  bipermutation (n + n) (idn_biperm n).
Proof.
  unfold idn_biperm.
  intros k Hk; bdestructΩ'.
Qed.

Definition flip_biperm n m (f : nat -> nat) : nat -> nat :=
  fun k =>
  let outval :=
    if k <? m then f (k + n) else 
    if k <? n + m then f (k - m) else f k 
  in
    if outval <? n then outval + m else 
    if outval <? n + m then outval - n else outval.

Lemma flip_biperm_bipermutation n m f (Hf : bipermutation (n + m) f) : 
  bipermutation (m + n) (flip_biperm n m f).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  split; [|split].
  - unfold flip_biperm.
    bdestructΩ';
    match goal with |- context[ f ?k ] =>
      specialize (Hfbdd k); lia
    end.
  - unfold flip_biperm.
    bdestructΩ';
    match goal with |- context[ f ?k ] =>
      specialize (Hfne k); lia
    end.
  - unfold flip_biperm at 2.
    replace_bool_lia (k <? n + m) true.
    pose proof (Hfbdd (k + n)).
    pose proof (Hfbdd (k - m)).
    replace ((if k <? m then f (k + n) else f (k - m)) <? n + m) with 
      true by bdestructΩ'.
    unfold flip_biperm.
    bdestructΩ';
    rewrite ?Nat.add_sub in *;
    rewrite ?Nat.sub_add in * by lia;
    rewrite ?Hfeq in * by lia;
    lia.
Qed.


Definition contract_biperm k l f :=
  if (k <? l) then 
    contract_perm (contract_perm f l) k
  else 
    contract_perm (contract_perm f k) l.

Add Parametric Morphism n k l (Hk : k < n) 
  (Hl : l < n) (Hkl : k <> l) : (contract_biperm k l) with signature
  perm_eq n ==> 
  perm_eq (n - 2) as contract_biperm_perm_eq_proper.
Proof.
  intros f g Hfg.
  unfold contract_biperm.
  replace (n - 2) with (n - 1 - 1) by lia.
  bdestructΩ'; now rewrite Hfg.
Qed.

Lemma contract_biperm_comm f k l : 
  contract_biperm k l f = contract_biperm l k f.
Proof.
  unfold contract_biperm.
  bdestructΩ'.
  now replace k with l by lia.
Qed.

Lemma contract_biperm_bounded n f 
  (Hf : perm_bounded n f) k l (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_bounded (n - 2) (contract_biperm k l f).
Proof.
  unfold contract_biperm.
  replace (n - 2) with (n - 1 - 1) by lia.
  bdestructΩ';
  repeat apply contract_perm_bounded; lia + auto.
Qed.

Lemma contract_biperm_permutation n f 
  (Hf : permutation n f) k l (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  permutation (n - 2) (contract_biperm k l f).
Proof.
  unfold contract_biperm.
  replace (n - 2) with (n - 1 - 1) by lia.
  bdestructΩ';
  repeat apply contract_perm_permutation; 
  auto with perm_bounded_db zarith.
Qed.

Lemma contract_biperm_inv n f 
  (Hf : permutation n f) k l (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_eq (n - 2) (perm_inv (n - 2) (contract_biperm k l f))
    (contract_biperm (f k) (f l) (perm_inv n f)).
Proof.
  replace (n - 2) with (n - 1 - 1) by lia.
  unfold contract_biperm.
  bdestructΩ'.
  - cleanup_perm_inv.
    replace (contract_perm f l k) with (f k); [easy|].
    unfold contract_perm.
    bdestructΩ'.
  - cleanup_perm_inv.
    replace (contract_perm f l k) with (f k - 1) 
      by (unfold contract_perm; bdestructΩ').
    intros i Hi.
    unfold contract_perm.
    pose proof (permutation_is_injective n f Hf k l).
    rewrite Nat.sub_add by lia.
    rewrite !perm_inv_is_linv_of_permutation by cleanup_perm.
    replace_bool_lia (f k - 1 <? f l) false.
    replace_bool_lia (f l <? f k) true.
    replace_bool_lia (k <? l) true.
    replace_bool_lia (l <? k) false.
    repeat match goal with |- context[ i <? ?a] =>
      bdestruct (i <? a); try lia
    end.
    + bdestructΩ'.
    + replace_bool_lia (i + 1 <? f k) true.
      bdestructΩ'.
    + bdestructΩ'.
  - cleanup_perm_inv.
    erewrite contract_perm_perm_eq_of_perm_eq.
    3: (apply contract_perm_inv; auto).
    2: (pose proof (permutation_is_bounded n f Hf l Hl); 
      unfold contract_perm; bdestructΩ').
    replace (contract_perm f k l) with (f l - 1) by
      (unfold contract_perm; bdestructΩ').
    intros i Hi.
    unfold contract_perm.
    pose proof (permutation_is_injective n f Hf k l).
    rewrite Nat.sub_add by lia.
    rewrite !perm_inv_is_linv_of_permutation by cleanup_perm.
    replace_bool_lia (f l - 1 <? f k) false.
    replace_bool_lia (f k <? f l) true.
    replace_bool_lia (k <? l) false.
    replace_bool_lia (l <? k) true.
    repeat match goal with |- context[ i <? ?a] =>
      bdestruct (i <? a); try lia
    end.
    + bdestructΩ'.
    + replace_bool_lia (i + 1 <? f l) true.
      bdestructΩ'.
    + bdestructΩ'.
  - rewrite contract_perm_inv by auto with perm_db zarith.
    pose proof (permutation_is_injective n f Hf k l).
    replace (contract_perm f k l) with (f l) by
      (unfold contract_perm; bdestructΩ').
    pose proof (permutation_is_bounded n f Hf l Hl).
    pose proof (permutation_is_bounded n f Hf k Hk).
    rewrite (contract_perm_inv n f Hf k) by easy.
    easy.
Qed.

Lemma contract_biperm_bipermutation_iff n f 
  (Hf : bipermutation n f) k (Hk : k < n) : 
  bipermutation (n - 2) (contract_biperm k (f k) f) <->
  (forall a, a < n - 2 -> contract_biperm k (f k) f a <> a).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  rewrite bipermutation_defn_alt.
  assert (Hrw : 
    permutation (n - 2) (contract_biperm k (f k) f)
      <-> True). 
  1: {
    intuition idtac.
    apply contract_biperm_permutation;
      try symmetry; try apply Hf; auto with perm_db.
  }
  rewrite Hrw; clear Hrw.
  rewrite and_True_l.
  symmetry.
  rewrite <- (and_True_r (forall k, _ -> _)) at 1.
  apply and_iff_distr_l.
  intros Hne.
  split; [intros _ | easy].
  rewrite contract_biperm_inv by 
    (try (symmetry; apply Hf); auto with perm_db).
  pose proof (Hfne k Hk).
  pose proof (Hfbdd k Hk).
  rewrite Hfeq by lia.
  rewrite contract_biperm_comm.
  erewrite contract_biperm_perm_eq_proper;
  [|easy..|apply (perm_inv_bipermutation n f Hf)].
  easy.
Qed.


(* Section on n_m_cup_cap, in Bipermutations.v *)
Definition n_m_cup_cap (n m : nat) : nat -> nat :=
  fun k => if n + n + (m + m) <=? k then k else
  if Nat.even k then S k else pred k.

Lemma n_m_cup_cap_comm n m : 
  n_m_cup_cap n m = n_m_cup_cap m n.
Proof.
  unfold n_m_cup_cap.
  now rewrite Nat.add_comm.
Qed.

Lemma n_m_cup_cap_WF n m : 
  WF_Perm (n + n + (m + m)) (n_m_cup_cap n m).
Proof.
  intros k Hk; unfold n_m_cup_cap; bdestructΩ'.
Qed.

Lemma n_m_cup_cap_WF_alt n m : 
  WF_Perm (n + n + (m + m)) (n_m_cup_cap m n).
Proof.
  intros k Hk; unfold n_m_cup_cap; bdestructΩ'.
Qed.

#[export] Hint Resolve n_m_cup_cap_WF n_m_cup_cap_WF_alt : WF_Perm_db.

(* TODO: Redo with the new bipermutation_iff lemmas *)
Lemma n_m_cup_cap_bipermutation (n m : nat) : 
  bipermutation (n + n + (m + m)) (n_m_cup_cap n m).
Proof.
  assert (Hev : Nat.even (n + n + (m + m)) = true) by
    now rewrite 3!Nat.even_add, !eqb_reflx.
  unfold n_m_cup_cap.
  intros k Hk; split; [|split];
  bdestructΩ'.
  - bdestruct (S k =? n + n + (m + m)); [|lia].
    rewrite <- Nat.odd_succ in Heqb.
    replace -> (S k) in Heqb.
    rewrite <- Nat.negb_even in Heqb.
    rewrite Hev in Heqb; easy.
  - destruct k; easy.
  - assert (Heq : S k = n + n + (m + m)) by lia.
    apply (f_equal Nat.odd) in Heq.
    rewrite Nat.odd_succ, Heqb in Heq.
    rewrite <- Nat.negb_even, Hev in Heq.
    easy.
  - rewrite Nat.even_succ, <- Nat.negb_even in *.
    rewrite Heqb in *.
    easy.
  - destruct k; easy.
  - destruct k; [easy|].
    rewrite Nat.even_succ, <- Nat.negb_even in Heqb.
    simpl in *.
    destruct (Nat.even k); easy.
Qed.

Lemma n_m_cup_cap_bipermutation' ncup ncap : 
  bipermutation (ncap + ncap + (ncup + ncup))
  (n_m_cup_cap ncup ncap).
Proof.
  rewrite Nat.add_comm.
  apply n_m_cup_cap_bipermutation.
Qed.

Hint Resolve n_m_cup_cap_bipermutation' : biperm_db biperm_db_alt.

Lemma n_m_cup_cap_bounded n m k : 
  k < n + n + (m + m) ->
  n_m_cup_cap n m k < n + n + (m + m).
Proof.
  intros Hk.
  now apply n_m_cup_cap_bipermutation.
Qed.

Lemma n_m_cup_cap_lt_double_iff m n a k : 
  a <= m + n ->
  n_m_cup_cap m n k < a + a <-> k < a + a.
Proof.
  intros Ha.
  unfold n_m_cup_cap.
  split; bdestructΩ'.
  - destruct k; [easy|].
    simpl.
    apply succ_even_lt_even; [|apply even_add_same].
    now rewrite even_succ_false in Heqb.
  - apply succ_even_lt_even; auto using even_add_same.
Qed.

Lemma n_m_cup_cap_even_plus n m a k : 
  Nat.even a = true -> a + k < n + n + m + m ->
  n_m_cup_cap n m (a + k) = a + n_m_cup_cap n m k.
Proof.
  intros Ha Hak.
  unfold n_m_cup_cap.
  do 2 simplify_bools_lia_one_kernel.
  rewrite Nat.even_add, Ha, eqb_true_l.
  bdestructΩ'; destruct k; [easy|lia].
Qed.

Lemma n_m_cup_cap_double_plus n m a k : 
  a + a + k < n + n + m + m ->
  n_m_cup_cap n m (a + a + k) = a + a + n_m_cup_cap n m k.
Proof.
  apply n_m_cup_cap_even_plus, even_add_same.
Qed.

Lemma n_m_cup_cap_sub_double n m a k : 
  a + a <= k -> k < n + n + m + m ->
  n_m_cup_cap n m (k - (a + a)) = n_m_cup_cap n m k - (a + a).
Proof.
  intros Hak Hk.
  rewrite <- (add_sub' k (a + a)) at 2.
  rewrite <- Nat.add_sub_assoc by lia.
  rewrite n_m_cup_cap_double_plus by lia.
  now rewrite add_sub'.
Qed.


Lemma n_m_cup_cap_ge_double_iff m n a k :
  a <= m + n -> 
  a + a <= n_m_cup_cap m n k <-> a + a <= k.
Proof.
  pose proof (n_m_cup_cap_lt_double_iff m n a k).
  lia.
Qed.

Lemma n_m_cup_cap_ltb_double m n a k :
  a <= m + n -> 
  n_m_cup_cap m n k <? a + a = (k <? a + a).
Proof.
  intros Ha.
  pose proof (n_m_cup_cap_lt_double_iff m n a k Ha).
  bdestructΩ'.
Qed.

Lemma n_m_cup_cap_double_leb m n a k :
  a <= m + n -> 
  a + a <=? n_m_cup_cap m n k = (a + a <=? k).
Proof.
  intros Ha.
  pose proof (n_m_cup_cap_ge_double_iff m n a k Ha).
  bdestructΩ'.
Qed.

Lemma n_m_cup_cap_twice_plus n m a k :
  a * 2 + k < n + n + m + m ->
  n_m_cup_cap n m (a*2 + k) = 
  a*2 + n_m_cup_cap n m k.
Proof.
  replace (a*2) with (a+a) by lia.
  apply n_m_cup_cap_double_plus.
Qed.

Lemma n_m_cup_cap_geb_double m n a k : a <= m + n -> 
  (a + a <=? n_m_cup_cap m n k) = (a + a <=? k).
Proof.
  intros Ha.
  apply eq_iff_eq_true; 
  rewrite !Nat.leb_le.
  now apply n_m_cup_cap_ge_double_iff.
Qed.

(* Lemma n_m_cup_cap_double_sub n m a k (Hk : k < a + a) (Ha : a <= m + n) : 
  n_m_cup_cap m n (a + a - S k) = a + a - n_m_cup_cap m n (k).
Proof.
  rewrite (Nat.div_mod_eq k 2).
  enough (n_m_cup_cap m n (k) + n_m_cup_cap m n (a + a - S k) = a + a) by lia.
  rewrite 2!n_m_cup_cap_eqb.
  do 2 simplify_bools_lia_one_kernel.
  symmetry.

  replace (a + a) with (S k + (a + a - S k)) at 1 by lia.
  Search ((_ - _ ) mod _). *)

Lemma n_m_cup_cap_eqb n m k :
  n_m_cup_cap n m k = 
  if n + n + (m + m) <=? k then k else
  k / 2 * 2 + (1 - (k mod 2)).
Proof.
  unfold n_m_cup_cap.
  bdestruct_one; [easy|].
  rewrite (Nat.div_mod_eq k 2).
  rewrite Nat.even_add, Nat.even_mul.
  cbn [Nat.even orb].
  rewrite eqb_true_l.
  assert (k mod 2 < 2) by show_moddy_lt.
  assert (Hdisj : k mod 2 = 0 \/ k mod 2 = 1) by lia.
  rewrite Nat.mul_comm, mod_add_l, Nat.div_add_l, mod_div, Nat.add_0_r by lia.
  destruct Hdisj; replace -> (k mod 2);
  simpl; lia.
Qed.

Lemma n_m_cup_cap_stack_biperms_decomp ncup ncap :
  n_m_cup_cap ncup ncap = 
  stack_biperms (ncap + ncap) 0 0 (ncup + ncup) 
    (n_m_cup_cap 0 ncap) (n_m_cup_cap ncup 0).
Proof.
  apply functional_extensionality.
  intros k.
  bdestruct (k <? ncap + ncap + (ncup + ncup));
  [|unfold n_m_cup_cap, stack_biperms; 
    now do 2 simplify_bools_lia_one_kernel].
  unfold stack_biperms.
  simplify_bools_lia_one_kernel.
  rewrite Tauto.if_same.
  bdestruct (k <? ncap + ncap).
  - rewrite 2!n_m_cup_cap_eqb.
    bdestructΩ'.
  - rewrite Nat.add_0_r.
    replace k with ((ncap + ncap) + (k - (ncap + ncap))) at 1 by lia.
    rewrite n_m_cup_cap_double_plus by lia.
    f_equal.
    rewrite 2!n_m_cup_cap_eqb.
    bdestructΩ'.
Qed.

Lemma n_m_cup_cap_stack_biperms_decomp_alt ncup ncap :
  n_m_cup_cap ncup ncap = 
  stack_biperms (ncup + ncup) 0 0 (ncap + ncap) 
    (n_m_cup_cap 0 ncup) (n_m_cup_cap ncap 0).
Proof.
  rewrite n_m_cup_cap_comm.
  apply n_m_cup_cap_stack_biperms_decomp.
Qed.

Lemma n_m_cup_cap_plus_plus_decomp n0 n1 m0 m1 :
  n_m_cup_cap (n0 + n1) (m0 + m1) = 
  stack_biperms (n0 + n0) (m0 + m0) (n1 + n1) (m1 + m1)
  (n_m_cup_cap n0 m0) (n_m_cup_cap n1 m1).
Proof.
  apply functional_extensionality; intros k.
  unfold stack_biperms.
  bdestruct (k <? n0 + n0 + n1 + n1 + m0 + m0 + m1 + m1); 
  simplify_bools_lia_one_kernel;
  [|rewrite n_m_cup_cap_eqb; bdestructΩ'].
  rewrite !n_m_cup_cap_ltb_double by lia.
  bdestructΩ'.
  - rewrite 2!n_m_cup_cap_eqb; bdestructΩ'.
  - replace k with (n0 + n0 + (k - (n0 + n0))) at 1 by lia.
    rewrite n_m_cup_cap_double_plus by lia.
    rewrite 2!n_m_cup_cap_eqb; bdestructΩ'.
  - replace k with (n1 + n1 + (k - (n1 + n1))) at 1 by lia.
    rewrite n_m_cup_cap_double_plus by lia.
    rewrite 2!n_m_cup_cap_eqb; bdestructΩ'.
  - replace k with ((n0+m0)+(n0+m0) + (k - (n0 + n0 + (m0 + m0)))) 
      at 1 by lia.
    rewrite n_m_cup_cap_double_plus by lia.
    rewrite 2!n_m_cup_cap_eqb; bdestructΩ'.
Qed.

(* TODO: Change to perm_eq *)
Lemma n_m_cup_cap_absorb_stacked_swap_perm_l padl padr m :
  forall k, k < (padl + 1 + padr) + (padl + 1 + padr) + (m + m) ->
  biperm_compose_perm_r (m + m) ((padl + 1 + padr) + (padl + 1 + padr))
  (n_m_cup_cap m (padl + 1 + padr))
  (stack_perms (padl+padl+2) (padr+padr)
    (stack_perms (padl + padl) 2 idn (swap_perm 0 1 2)) idn) k =
  n_m_cup_cap m (padl + 1 + padr) k.
Proof. Abort. (* TODO: Aborted for performance. Do we want this? *) (*
  intros k Hk.
  unfold biperm_compose_perm_r.
  (* TODO: Try to remove all XXX.XXX references (except, say, Nat); at 
    least for PermutationInstances. They are fragile and should be imported. *)
  pose proof (@PermutationInstances.stack_perms_bounded (padl+padl) 2 idn
    (swap_perm 0 1 2) ltac:(easy) ltac:(unfold swap_perm;intros;bdestructΩ'))
    as Hstbdd.
  pose proof (@PermutationInstances.stack_perms_bounded _ (padr+padr) _ idn
    Hstbdd ltac:(easy)) as Hsbdd.
  assert (Hsperm : permutation (padl + 1 + padr + (padl + 1 + padr))
    (stack_perms (padl+padl+2) (padr+padr)
    (stack_perms (padl + padl) 2 idn (swap_perm 0 1 2)) idn)) by
    (rewrite !double_add; auto with perm_db).
  rewrite !n_m_cup_cap_ltb_double by lia.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
  rewrite n_m_cup_cap_double_plus, add_sub' 
    by (pose proof (Hsbdd (k-(m+m))); lia).
  rewrite !double_add.
  rewrite perm_inv_stack_perms; auto with perm_db.
  2: {
    change 2 with (1 + 1).
    rewrite <- 2!double_add, n_m_cup_cap_lt_double_iff, !double_add;
    specialize (Hsbdd (k - (m + m))); simpl; lia.
  }
  rewrite stack_perms_f_idn.
  rewrite stack_perms_idn_f.
  rewrite <- stack_perms_idn_f at 1.
  rewrite !(if_dist' (n_m_cup_cap m (padl + 1 + padr))).
  rewrite n_m_cup_cap_sub_double by lia.
  pose proof (fun x => n_m_cup_cap_lt_double_iff m (padl+1+padr) x k) 
    as Hltdbl.
  bdestruct (k - (m + m) <? padl + padl + 2).
  - simpl_bools.
    bdestructΩ'simp.
    + unfold stack_perms at 1.
      pose proof (Hltdbl (m + padl + 1)).
      simplify_bools_lia.
      rewrite perm_inv_stack_perms by (lia + auto with perm_db).
      pose proof (Hltdbl (m+padl)).
      rewrite stack_perms_left by lia.
      rewrite idn_inv; 
      pose proof (Hltdbl m); lia.
    + assert (Hdisj: k = (m + padl + (m + padl))
          \/ k = S (m + padl + (m + padl))) by lia; destruct Hdisj; subst.
      * unfold swap_perm at 2.
        simplify_bools_lia.
        unfold n_m_cup_cap.
        rewrite even_succ_add_same, even_add_same.
        simplify_bools_lia.
        rewrite stack_perms_left by lia.
        rewrite perm_inv_stack_perms by lia + auto with perm_db.
        rewrite stack_perms_right by lia.
        rewrite swap_perm_inv by lia.
        unfold swap_perm; bdestructΩ'.
      * unfold swap_perm at 2.
        replace (S (m + padl + (m + padl)) - (m + m) - (padl + padl))
          with 1 by lia.
        simpl.
        unfold n_m_cup_cap.
        rewrite even_succ_add_same, even_add_same.
        simplify_bools_lia.
        rewrite stack_perms_left by lia.
        rewrite perm_inv_stack_perms by lia + auto with perm_db.
        rewrite stack_perms_right by lia.
        rewrite swap_perm_inv by lia.
        unfold swap_perm; bdestructΩ'.
  - rewrite stack_perms_right by 
      (pose proof (Hltdbl (m+padl+1));
      pose proof (Hltdbl (m+padl+1+padr)); lia).
    rewrite idn_inv 
      by (pose proof (Hltdbl (m+padl+1+padr)); lia).
    rewrite Nat.sub_add by (pose proof (Hltdbl (m+padl+1)); lia).
    pose proof (Hltdbl m); lia.
Qed.*)

(* TODO: Change to perm_eq *)
Lemma n_m_cup_cap_absorb_swap_block_perm_l padl padm padr m :
  forall k, k < (padl + 1 + padm + 1 + padr) 
    + (padl + 1 + padm + 1 + padr) + (m + m) ->
  biperm_compose_perm_r (m + m) 
    ((padl + 1 + padm + 1 + padr) + (padl + 1 + padm + 1 + padr))
  (n_m_cup_cap m (padl + 1 + padm + 1 + padr))
  (swap_block_perm (padl + padl) (padm + padm) 2) k =
  n_m_cup_cap m (padl + 1 + padm + 1 + padr) k.
Proof. Abort. (* TODO: Aborted for performance. Do we want this? *) (*
  intros k Hk.
  unfold biperm_compose_perm_r.
  rewrite !double_add.
  rewrite swap_block_perm_inv 
    by (pose proof (n_m_cup_cap_bounded m (padl+1+padm+1+padr) k); lia).
  simplify_bools_lia_one_kernel.
  rewrite !n_m_cup_cap_ltb_double by lia.
  simplify_bools_lia_one_kernel.
  bdestructΩ'.
  rewrite swap_block_perm_sub by easy.
  pose proof (swap_block_perm_bounded (m+m+(padl+padl)) (padm+padm) (padr+padr) 
    2 k ltac:(lia)).
  pose proof (fun k x => n_m_cup_cap_lt_double_iff m (padl+1+padm+1+padr) x k) 
    as Hltdbl.
  rewrite swap_block_perm_inv
    by (pose proof (Hltdbl (m + m + (swap_block_perm 
      (m + m + (padl + padl)) (padm + padm) 2 k - (m + m))) 
      (m + padl+1+padm+1+padr));
      lia).
  rewrite n_m_cup_cap_double_plus, n_m_cup_cap_sub_double by 
    lia + (unfold swap_block_perm; bdestructΩ').
  rewrite add_sub'.
  rewrite swap_block_perm_sub
    by (rewrite n_m_cup_cap_ge_double_iff by lia; 
      unfold swap_block_perm; bdestructΩ').
  unfold swap_block_perm at 1.
  change 2 with (1 + 1).
  rewrite <- !double_add.
  rewrite !n_m_cup_cap_ltb_double by lia.
  unfold swap_block_perm.
  bdestructΩ';
  match goal with 
  |- context [n_m_cup_cap _ _ ?K ] =>
      pose proof (Hltdbl K m);
      try rewrite Nat.add_sub_assoc, add_sub' by lia
  end;
  try easy.
  - rewrite (Nat.add_comm k), <- double_add, n_m_cup_cap_double_plus;
    pose proof (Hltdbl k m); lia.
  - rewrite <- double_add, n_m_cup_cap_sub_double;
    pose proof (Hltdbl k (1+padm)); lia.
Qed.*)

(* Used in the following, currently unused, lemma
Lemma swap_perm_invol' a b n k : a < n -> b < n -> 
  swap_perm a b n (swap_perm a b n k) = k.
Proof.
  intros Ha Hb.
  pose proof (swap_perm_invol a b n Ha Hb) as H.
  apply (f_equal_inv k) in H.
  apply H.
Qed.
*)
Lemma n_m_cup_cap_absorb_tensor_2_idn_swap_perm_l n m 
  a b (Ha : a < n) (Hb : b < n) :
  perm_eq (n + n + m + m)
  (biperm_compose_perm_r (m + m) 
    (n + n)
  (n_m_cup_cap m n)
  (tensor_perms n 2 (swap_perm a b n) idn))
  (n_m_cup_cap m n).
Proof. Abort. (* TODO: Aborted for performance. Do we need this? *) (*
  intros k HK.
  unfold biperm_compose_perm_r.
  simplify_bools_lia_one_kernel.
  replace (n + n) with (n * 2) in * by lia.
  rewrite 2!n_m_cup_cap_ltb_double by lia.
  simplify_bools_lia_one_kernel.
  bdestruct (k <? m + m); [easy|].
  pose proof (tensor_perms_bounded n 2 (swap_perm a b n) idn 
    ltac:(cleanup_perm) ltac:(cleanup_perm) (k - (m + m)) ltac:(lia)).
  rewrite n_m_cup_cap_double_plus by lia.
  rewrite add_sub'.
  rewrite tensor_perms_inv; auto with perm_db;
  [|replace (n*2) with (n + n);
  [apply n_m_cup_cap_lt_double_iff|]; lia].
  unfold tensor_perms at 2.
  simplify_bools_lia_one_kernel.
  pose proof (swap_perm_bounded a b n Ha Hb ((k - (m + m)) / 2)
    ltac:(apply Nat.Div0.div_lt_upper_bound; lia)).
  assert ((k - (m + m)) mod 2 < 2) by show_moddy_lt.
  rewrite n_m_cup_cap_twice_plus by 
    (apply (Nat.lt_le_trans _ ((n - 1)*2 + 2)); [nia | show_pow2_le]).
  rewrite n_m_cup_cap_eqb.
  simplify_bools_lia_one_kernel.
  rewrite mod_div, Nat.mul_0_l, Nat.add_0_l.
  rewrite Nat.mod_small by easy.
  unfold tensor_perms.
  simplify_bools_lia_one_kernel.
  rewrite Nat.div_add_l, (Nat.div_small (1 - _)), Nat.add_0_r by lia.
  rewrite mod_add_l, Nat.mod_small by lia.
  rewrite swap_perm_inv, swap_perm_invol', idn_inv by lia. 
  symmetry.
  replace k with (m + m + (k - (m + m))) at 1 by lia.
  rewrite n_m_cup_cap_double_plus by lia.
  f_equal.
  rewrite n_m_cup_cap_eqb.
  bdestructΩ'.
Qed. *)

Local Arguments Nat.modulo : simpl never.
Local Arguments Nat.div : simpl never.
Local Arguments perm_inv : simpl never.
Local Arguments Nat.sub : simpl nomatch.


Lemma n_m_cup_cap_absorb_tensor_2_idn_perm_l n m f 
  (Hf : permutation n f) :
  perm_eq (n + n + (m + m))
  (biperm_compose_perm_r (m + m) 
    (n + n)
  (n_m_cup_cap m n)
  (tensor_perms n 2 f idn))
  (n_m_cup_cap m n).
Proof.
  rewrite Nat.add_assoc.
  intros k HK.
  unfold biperm_compose_perm_r.
  simplify_bools_lia_one_kernel.
  replace (n + n) with (n * 2) in * by lia.
  rewrite 2!n_m_cup_cap_ltb_double by lia.
  simplify_bools_lia_one_kernel.
  bdestruct (k <? m + m); [easy|].
  pose proof (tensor_perms_bounded n 2 f idn 
    ltac:(cleanup_perm) ltac:(cleanup_perm) (k - (m + m)) ltac:(lia)).
  rewrite n_m_cup_cap_double_plus by lia.
  rewrite add_sub'.
  rewrite tensor_perms_inv; auto with perm_db;
  [|replace (n*2) with (n + n);
  [apply n_m_cup_cap_lt_double_iff|]; lia].
  unfold tensor_perms at 2.
  simplify_bools_lia_one_kernel.
  pose proof (permutation_is_bounded n f Hf ((k - (m + m)) / 2)
    ltac:(apply Nat.Div0.div_lt_upper_bound; lia)).
  assert ((k - (m + m)) mod 2 < 2) by show_moddy_lt.
  rewrite n_m_cup_cap_twice_plus by 
    (apply (Nat.lt_le_trans _ ((n - 1)*2 + 2)); [nia | show_pow2_le]).
  rewrite n_m_cup_cap_eqb.
  simplify_bools_lia_one_kernel.
  rewrite mod_div, Nat.mul_0_l, Nat.add_0_l.
  rewrite Nat.mod_small by easy.
  unfold tensor_perms.
  simplify_bools_lia_one_kernel.
  rewrite Nat.div_add_l, (Nat.div_small (1 - _)), Nat.add_0_r by lia.
  rewrite mod_add_l, Nat.mod_small by lia.
  cleanup_perm; [|apply Nat.Div0.div_lt_upper_bound; lia].
  rewrite idn_inv by lia. 
  symmetry.
  replace k with (m + m + (k - (m + m))) at 1 by lia.
  rewrite n_m_cup_cap_double_plus by lia.
  f_equal.
  rewrite n_m_cup_cap_eqb.
  bdestructΩ'.
Qed.

Lemma n_m_cup_cap_absorb_tensor_2_idn_perm_l_eq n m f
  (Hf : permutation n f) : 
  biperm_compose_perm_r (m + m) (n + n)
    (n_m_cup_cap m n) (tensor_perms n 2 f idn) 
  = n_m_cup_cap m n.
Proof.
  eq_by_WF_perm_eq (m + m + (n + n)).
  rewrite Nat.add_comm.
  now apply n_m_cup_cap_absorb_tensor_2_idn_perm_l.
Qed.

Lemma n_m_cup_cap_absorb_reflect_perm_l n m :
  biperm_compose_perm_r (m + m) (n + n)
    (n_m_cup_cap m n) (reflect_perm (n + n))
  = n_m_cup_cap m n.
Proof.
  eq_by_WF_perm_eq (m + m + (n + n)).
  intros k Hk.
  unfold biperm_compose_perm_r.
  simplify_bools_lia_one_kernel.
  rewrite !n_m_cup_cap_ltb_double by lia.
  simplify_bools_lia_one_kernel.
  bdestructΩ (k <? m + m).
  rewrite n_m_cup_cap_double_plus
    by (pose proof (reflect_perm_bounded (n + n) (k - (m+m))); lia).
  rewrite add_sub'.
  rewrite reflect_perm_inv 
    by (apply n_m_cup_cap_lt_double_iff; auto with zarith perm_bounded_db).
  unfold reflect_perm.
  simplify_bools_lia_one_kernel.
  rewrite n_m_cup_cap_geb_double by lia.
  simplify_bools_lia_one_kernel.
  unfold n_m_cup_cap.
  do 2 simplify_bools_lia_one_kernel.
  rewrite Nat.even_sub, even_add_same, eqb_true_l by lia.
  rewrite Nat.even_succ, <- Nat.negb_even.
  rewrite Nat.even_sub, even_add_same, eqb_true_r by lia.
  rewrite if_negb.
  bdestructΩ'.
  - pose proof (succ_even_lt_even k (m + n + (m + n)) ltac:(easy)
      (even_add_same _)).
    lia.
  - assert (k <> m + m) by (intros Hf; subst; now rewrite even_add_same in *).
    lia. 
Qed.

Lemma n_m_cup_cap_absorb_perm_swap_even_S_l n m a 
  (Ha : Nat.even a = true) :
  biperm_compose_perm_r (m + m) (n + n)
    (n_m_cup_cap m n) (swap_perm a (S a) (n + n))
  = n_m_cup_cap m n.
Proof.
  eq_by_WF_perm_eq (m + m + (n + n)).
  bdestruct (a <? n + n).
  2: {
    rewrite swap_perm_big_eq by lia.
    apply biperm_compose_perm_r_idn, n_m_cup_cap_bipermutation.
  }
  pose proof (succ_even_lt_even a (n + n) Ha (even_add_same n) ltac:(easy)).
  intros k Hk.
  pose proof (n_m_cup_cap_bounded m n k Hk).
  unfold biperm_compose_perm_r.
  rewrite 2!n_m_cup_cap_ltb_double by lia.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ (k <? m + m).
  pose proof (swap_perm_bounded a (S a) (n+n) 
    ltac:(easy) ltac:(easy) (k-(m+m)) ltac:(lia)).
  rewrite n_m_cup_cap_double_plus by lia.
  rewrite add_sub'.
  rewrite swap_perm_inv by (lia + apply n_m_cup_cap_lt_double_iff; lia).
  unfold swap_perm at 2.
  simplify_bools_lia_one_kernel.
  bdestruct (k =? m + m + a);
  simplify_bools_lia_one_kernel;
  [|bdestruct (k =? m + m + S a);
    simplify_bools_lia_one_kernel].
  - unfold n_m_cup_cap.
    rewrite Nat.even_succ, <- Nat.negb_even.
    rewrite Ha.
    do 2 simplify_bools_lia_one_kernel.
    subst.
    rewrite Nat.even_add, even_add_same, Ha.
    unfold swap_perm; bdestructΩ'.
  - unfold n_m_cup_cap.
    rewrite Ha.
    do 2 simplify_bools_lia_one_kernel.
    subst.
    rewrite Nat.even_add, even_add_same.
    rewrite Nat.even_succ, <- Nat.negb_even, Ha.
    unfold swap_perm; bdestructΩ'.
  - unfold swap_perm.
    rewrite n_m_cup_cap_geb_double by lia.
    simplify_bools_lia_one_kernel.
    rewrite n_m_cup_cap_sub_double by lia.
    assert (m + m <= n_m_cup_cap m n k) 
      by (rewrite n_m_cup_cap_ge_double_iff; lia).
    unfold n_m_cup_cap.
    simplify_bools_lia_one_kernel.
    destruct (Nat.even k) eqn:e.
    + bdestruct (S k - (m + m) =? a);
      [subst a; rewrite Nat.even_sub, even_add_same,
        Nat.even_succ, <- Nat.negb_even, e in Ha by lia; easy|].
      bdestructΩ'.
    + destruct k; [easy|].
      rewrite even_succ_false in *.
      simpl.
      bdestruct (k =? (m + m) + S a);
      [subst k; rewrite Nat.even_add, even_add_same, 
        Nat.even_succ, <- Nat.negb_even, Ha in e; easy|].
      pose proof (even_le_even_of_le_succ k (m + m) 
        ltac:(easy) (even_add_same m) ltac:(lia)). 
      bdestructΩ'.
Qed.

Lemma n_m_cup_cap_absorb_perm_swap_0_1_l n m :
  biperm_compose_perm_r (m + m) (n + n)
    (n_m_cup_cap m n) (swap_perm 0 1 (n + n))
  = n_m_cup_cap m n.
Proof.
  eq_by_WF_perm_eq (m + m + (n + n)).
  intros k Hk.
  unfold biperm_compose_perm_r.
  simplify_bools_lia_one_kernel.
  rewrite 2!n_m_cup_cap_ltb_double by lia.
  simplify_bools_lia_one_kernel.
  bdestructΩ'.
  unfold swap_perm at 2.
  simplify_bools_lia_one_kernel.
  bdestruct (k =? m + m);
  simplify_bools_lia_one_kernel;
  [|bdestruct (k =? m + m + 1);
  simplify_bools_lia_one_kernel];
  rewrite n_m_cup_cap_double_plus, add_sub' by lia;
  rewrite swap_perm_inv by (lia + apply n_m_cup_cap_lt_double_iff; lia).
  - unfold n_m_cup_cap.
    do 2 simplify_bools_lia_one_kernel.
    subst.
    rewrite even_add_same.
    unfold swap_perm; bdestructΩ'.
  - unfold n_m_cup_cap.
    do 2 simplify_bools_lia_one_kernel.
    subst.
    rewrite Nat.even_add, even_add_same.
    unfold swap_perm; bdestructΩ'.
  - assert (1 + 1 <= n_m_cup_cap m n (k - (m + m))) 
      by (apply n_m_cup_cap_ge_double_iff; lia).
    unfold swap_perm.
    rewrite n_m_cup_cap_geb_double by lia.
    bdestructΩ'.
    rewrite <- n_m_cup_cap_double_plus by lia.
    f_equal; lia.
Qed.




(* TODO: Move these to earlier in the file, maybe? Maybe better to have them
  concentrated, though, since we can't really use them in this file anyways *)

Create HintDb biperm_db_alt.

#[export] Hint Resolve idn_biperm_bipermutation flip_biperm_bipermutation
  n_m_cup_cap_bipermutation (* remove_swap_bipermutation *)
  stack_biperms_bipermutation
  stack_biperms_bipermutation_alt (* compose_swap_biperm_gen_bipermutation *)
  (* biperm_of_zxbiperm_folio_bipermutation *)
  bipermutation_is_bounded bipermutation_involutive
  (* compose_swap_biperm_bipermutation *) (* compose_cap_biperm_l_bipermutation *)
  (* compose_cup_biperm_l_bipermutation *) 
  biperm_compose_perm_l_biperm biperm_compose_perm_r_biperm
  : biperm_db.

#[export] Hint Resolve idn_biperm_bipermutation flip_biperm_bipermutation
  n_m_cup_cap_bipermutation (* remove_swap_bipermutation *)
  stack_biperms_bipermutation
  stack_biperms_bipermutation_alt (* compose_swap_biperm_gen_bipermutation *)
  (* biperm_of_zxbiperm_folio_bipermutation *)
  bipermutation_is_bounded bipermutation_involutive
  (* compose_swap_biperm_bipermutation *) (* compose_cap_biperm_l_bipermutation *)
  (* compose_cup_biperm_l_bipermutation *) 
  biperm_compose_perm_l_biperm biperm_compose_perm_r_biperm
  : biperm_db_alt.

(* FIXME: Test these replacements *)
Hint Extern 0 (permutation _ _) => auto with perm_db : biperm_db biperm_db_alt.
(*
Hint Extern 0 (permutation _ _) => solve [auto with perm_db] 
  : biperm_db biperm_db_alt.
*)

Hint Extern 0 (_ < _) => auto with perm_bounded_db : biperm_db biperm_db_alt.
(* 
Hint Extern 0 (_ < _) => solve [auto with perm_bounded_db] : biperm_db biperm_db_alt.
*)


Hint Extern 4 (bipermutation (?n + ?m) _) => 
  (* idtac n m; *) rewrite (Nat.add_comm n m); auto with biperm_db_alt : biperm_db.
(*
Hint Extern 4 (bipermutation (?n + ?m) _) => 
  rewrite (Nat.add_comm n m) : biperm_db.
*)

Hint Extern 4 (bipermutation (?n) _) => 
  let k := fresh in 
  evar (k : nat); 
  replace n with k;
  unfold k;
  auto with biperm_db_alt;
  lia : biperm_db.
(*
Hint Extern 4 (bipermutation (?n) _) =>
  is_ground n;
  let k := fresh in 
  evar (k : nat); 
  replace n with k; 
  unfold k;
  [ solve [auto with biperm_db_alt] |];
  [| (lia || cbn; lia)] : biperm_db.
*)

Hint Extern 4 (permutation (?n) _) => 
  let k := fresh in 
  evar (k : nat); 
  replace n with k;
  unfold k;
  auto with biperm_db_alt;
  lia : biperm_db.
(*
Hint Extern 4 (permutation (?n) _) => 
  is_ground n;
  let k := fresh in 
  evar (k : nat); 
  replace n with k;
  unfold k;
  [ solve [auto with biperm_db_alt] |];
  [|(lia || cbn; lia)] : biperm_db.
*)