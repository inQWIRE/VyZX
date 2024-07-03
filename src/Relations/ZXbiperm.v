Require Import ZXCore.
Require Import CoreAutomation.
Require Import CoreRules.
Require Import CastRules.
Require Import PermutationAutomation.
Require Import PermutationFacts.


(*TODO: matrices? *)

Local Open Scope nat.

Fixpoint has_common_below n f g : bool :=
  match n with
  | 0 => false
  | S n' => (f n') && (g n') || has_common_below n' f g
  end.

Notation bipermutation n f :=
  (forall k : nat, k < n -> f k < n /\ f k <> k /\ f (f k) = k).

(* Lemma bipermutation_permutation n f : bipermutation n f -> permutation n f.
Proof.
  intros Hbiperm.
  exists f.
  intros k Hk.
  destruct (Hbiperm k Hk) as [? [? ?]].
  auto.
Qed. *)

Fixpoint compose_biperms_helper cost n m o f g (to_g : bool) val :=
  (* ping pong among [1 ... n 1 ... m 1 ... o] (but 0-indexed) until in terminal region
    terminal region:  ├─────┤         ├─────┤

    f operates on:   [1 ... n 1 ... m]
    g operates on:           [1 ... m 1 ... o]                    *)
  match cost with | O => O | S cost' =>
  if val <? n then val
  else if val <? n + m then 
    if to_g then compose_biperms_helper cost' n m o f g false (n + g (val - n))
    else compose_biperms_helper cost' n m o f g true (f val)
  else if val <? n + m + o then val - m 
  else O
  end.

Definition compose_biperms n m o f g :=
  fun i => 
  if i <? n then 
    compose_biperms_helper (n + o) n m o f g (true) (f i)
  else if i <? n + o then
    compose_biperms_helper (n + o) n m o f g (false) (n + g (m + i - n))
  else i.

Local Notation perm_surj n f := (forall k, k < n -> exists k', k' < n /\ f k' = k).
Local Notation perm_bdd  n f := (forall k, k < n -> f k < n).
Local Notation perm_inj  n f := (forall k l, k < n -> l < n -> f k = f l -> k = l).

Lemma compose_biperms_helper_bounded cost n m o f g (H: 0 < n + o) : forall to_g val,
  compose_biperms_helper cost n m o f g to_g val < n + o.
Proof.
  induction cost; intros; simpl.
  - assumption.
  - bdestructΩ'.
Qed.

Lemma compose_biperms_bounded n m o f g : 
  perm_bdd (n + o) (compose_biperms n m o f g).
Proof.
  intros; unfold compose_biperms.
  bdestructΩ'; apply compose_biperms_helper_bounded; lia.
Qed.

#[export] Hint Resolve compose_biperms_helper_bounded compose_biperms_bounded : perm_bdd_db.

Lemma compose_biperms_WF n m o f g :
  WF_perm (n + o) (compose_biperms n m o f g).
Proof.
  intros k Hk.
  unfold compose_biperms.
  bdestructΩ'.
Qed.

#[export] Hint Resolve compose_biperms_WF : WF_perm_db.

Lemma permutation_of_bipermutation {n f} : bipermutation n f -> permutation n f.
Proof.
  intros Hbiperm.
  exists f.
  intros k Hk.
  repeat split.
  all: apply Hbiperm, Hk.
Qed.

#[export] Hint Resolve permutation_of_bipermutation : perm_db.

Lemma permutation_eqb_iff {n f} a b : permutation n f -> 
  a < n -> b < n ->
  f a =? f b = (a =? b).
Proof.
  intros Hperm Hk Hfk.
  bdestruct_one.
  apply (permutation_is_injective n f Hperm) in H; [bdestruct_one| |]; lia.
  bdestruct_one; subst; easy.
Qed.

Lemma permutation_eq_iff {n f} a b : permutation n f -> 
  a < n -> b < n ->
  f a = f b <-> a = b.
Proof.
  intros Hperm Hk Hfk.
  pose proof (permutation_eqb_iff _ _ Hperm Hk Hfk) as H.
  revert H; bdestructΩ'.
Qed.

Lemma bipermutation_involutive {n f} k : bipermutation n f -> k < n ->
  f (f k) = k.
Proof.
  intros Hbiperm Hk.
  apply (Hbiperm k Hk).
Qed.

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

Local Notation contract_f a b f := 
  (fun k => f (k - ((if a <=? k then 1 else 0) + (if b <=? k then 1 else 0)))).

Local Notation expand_f a b f :=
  (fun k => if k =? a then a else if k =? b then b else 
    f (k + if a <=? k then 1 else 0 + if b <=? k then 1 else 0)).

Local Notation exp_cont_f a b f :=
  (expand_f a b (contract_f a b f)).

Local Notation biperm_grow_r n f := 
  (exp_cont_f (f (S n)) (S n) f ∘ swap_perm (f (S n)) (S n) (S (S n)))%prg.

Local Notation biperm_grow_l n f := 
  (swap_perm (f (S n)) (S n) (S (S n)) ∘ exp_cont_f (f (S n)) (S n) f)%prg.

Lemma swap_perm_fswap a b n : a < n -> b < n -> 
  swap_perm a b n = fswap idn a b.
Proof.
  intros.
  unfold swap_perm, fswap.
  apply functional_extensionality; intros k.
  bdestructΩ'.
Qed.

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

  
  (* if n <=? k then 
    (if n <=? f (n + (g (k - n))) then
      n + perm_inv m g (f (n + (g (k - n))) - n)
    else
      f (n + (g (k - n))))
  else (* k < n *)
    if n <=? f k then
      n + perm_inv m g (f k - n)
    else 
      f k. *)

Lemma biperm_compose_perm_l_WF n m f g :
  WF_perm (n + m) (biperm_compose_perm_l n m f g).
Proof.
  unfold biperm_compose_perm_l.
  intros; bdestructΩ'.
Qed.

Lemma biperm_compose_perm_r_WF n m f g :
  WF_perm (n + m) (biperm_compose_perm_r n m f g).
Proof.
  unfold biperm_compose_perm_r.
  intros; bdestructΩ'.
Qed.


Lemma biperm_compose_perm_l_bdd n m f g 
  (Hf : perm_bdd (n + m) f) (Hg : perm_bdd n g) :
  perm_bdd (n + m) (biperm_compose_perm_l n m f g).
Proof.
  unfold biperm_compose_perm_l.
  intros.
  (* pose proof perm_inv_bdd as PB. *)
  bdestructΩ'.
  - pose proof (perm_inv_bdd n g (f (g k)) ltac:(easy)).
    lia.
  - apply Hf.
    specialize (Hg k ltac:(easy)); lia.
  - pose proof (perm_inv_bdd n g (f k) ltac:(easy)).
    lia.
  - apply Hf; easy.
Qed.

Lemma sub_lt_iff n m p (Hp : 0 < p) : 
  n - m < p <-> n < m + p.
Proof.
  split; lia.
Qed.

Lemma biperm_compose_perm_r_bdd n m f g 
  (Hf : perm_bdd (n + m) f) (Hg : perm_bdd m g) :
  perm_bdd (n + m) (biperm_compose_perm_r n m f g).
Proof.
  unfold biperm_compose_perm_r.
  intros.
  (* pose proof perm_inv_bdd as PB. *)
  bdestructΩ'.
  - apply Nat.add_lt_mono_l.
    apply perm_inv_bdd.
    specialize (Hf k ltac:(easy)).
    apply sub_lt_iff; [lia|].
    apply Hf.
  - apply Nat.add_lt_mono_l.
    pose proof (Hf k) as ?.
    apply perm_inv_bdd.
    apply sub_lt_iff; [lia|].
    apply Hf.
    apply Nat.add_lt_mono_l, Hg.
    lia.
Qed.

(* FIXME: Temp; probably just called something else *)
Lemma permutation_bdd {n f} (Hf : permutation n f) : 
  perm_bdd n f.
Proof.
  destruct Hf as [? Hf]; intros; apply Hf; easy.
Qed.

(* TODO: See if we can improve the hypotheses here 
  (specifically, keep around the equality we rewrite in intro)*)
Lemma perm_inv_eq_iff {n g} (Hg : permutation n g) 
  {k m} (Hk : k < n) (Hm : m < n) :
  perm_inv n g k = m <-> k = g m.
Proof.
  split; 
  [intros <- | intros ->];
  rewrite ?(perm_inv_is_rinv_of_permutation _ g Hg),
    ?(perm_inv_is_linv_of_permutation _ g Hg);
  easy.
Qed.

Lemma perm_inv_ge n g k : 
  n <= perm_inv n g k -> n <= k.
Proof.
  intros H.
  bdestruct (n <=? k); [lia|].
  specialize (perm_inv_bdd n g k); lia.
Qed.

Lemma add_sub' n m : m + n - m = n.
Proof.
  lia.
Qed.

Lemma add_leb_mono_l n m d : 
  (n + m <=? n + d) = (m <=? d).
Proof.
  bdestructΩ'.
Qed.

Lemma add_ltb_mono_l n m d : 
  (n + m <? n + d) = (m <? d).
Proof.
  bdestructΩ'.
Qed.

Lemma geb_0 n : 0 <=? n = true.
Proof.
  bdestructΩ'.
Qed.

Lemma add_le_cancel_l_iff n m d : 
  n + m <= n + d <-> m <= d.
Proof. lia. Qed.

Lemma add_lt_cancel_l_iff n m d : 
  n + m < n + d <-> m < d.
Proof. lia. Qed.

Lemma add_ge_cancel_l_iff n m d : 
  n + m >= n + d <-> m >= d.
Proof. lia. Qed.

Lemma add_gt_cancel_l_iff n m d : 
  n + m > n + d <-> m > d.
Proof. lia. Qed.

Lemma biperm_compose_perm_r_biperm n m f g 
  (Hf : bipermutation (n + m) f) (Hg : permutation m g) : 
  bipermutation (n + m) (biperm_compose_perm_r n m f g).
Proof.
  intros k Hk.
  split; 
    [ apply biperm_compose_perm_r_bdd; 
    apply Hf + apply permutation_bdd + easy; easy 
    | split].
  - unfold biperm_compose_perm_r.
    bdestructΩ'; [apply Hf; easy|].
    intros Hfalse.
    assert (Hkeq : k = n + (k - n)) by lia.
    remember (k - n) as d.
    assert (Hd : d < m) by lia.
    rewrite Hkeq in *.
    rewrite Nat.add_cancel_l in Hfalse.
    rewrite perm_inv_eq_iff in Hfalse; try (easy + lia).
    + assert (key: f (n + g d) = n + g d) by lia;
      (apply Hf in key; try easy; apply Nat.add_lt_mono_l,
        permutation_bdd; easy).
    + apply sub_lt_iff; [lia|].
      apply Hf, Nat.add_lt_mono_l, permutation_bdd; easy.
  - pose proof (fun k Hk => proj1 (Hf k Hk)) as Hfbdd.
    pose proof (fun k Hk => proj1 (proj2 (Hf k Hk))) as Hfne.
    pose proof (fun k Hk => proj2 (proj2 (Hf k Hk))) as Hfeq.
    pose proof (permutation_bdd Hg) as Hgbdd.
    bdestruct (n <=? k).
    + assert (Hkeq : k = n + (k - n)) by lia.
      remember (k - n) as d.
      assert (Hd : d < m) by lia.
      rewrite Hkeq in *.
      unfold biperm_compose_perm_r.
      rewrite add_sub', add_leb_mono_l.
      pose proof (add_ltb_mono_l n d 0) as e;
      rewrite Nat.add_0_r in e; rewrite e; clear e.
      simpl.
      replace_bool_lia (m <=? d) false.
      pose proof (Hfbdd (n + g d)) as e.
      rewrite add_lt_cancel_l_iff in e.
      bdestructΩ';
      let show_lt := (match goal with
      |- context[g ?k] => specialize (Hgbdd k)
      end; lia) in 
      let do_tac := first 
      [ reflexivity | assumption |
        specialize (e ltac:(show_lt)) |
        rewrite (perm_inv_is_rinv_of_permutation _ g Hg) in * |
        rewrite (perm_inv_is_linv_of_permutation _ g Hg) in * |
        rewrite Hfeq in * by (show_lt + easy) |
        apply Hf | apply Hgbdd |
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
        (* | |- perm_inv _ _ _ = _ =>
          apply perm_inv_eq_iff *)
        | |- ?n <= ?k => 
          bdestruct (n <=? k); [easy|];
          specialize (Hgbdd k ltac:(easy)); lia
      end |
      rewrite add_sub' |
      lia | 
      rewrite (perm_inv_is_rinv_of_permutation _ g Hg) in *; [|lia] |
      replace (n + (f (n + g d) - n)) with (f (n + g d)) in * by lia]
      in repeat do_tac; 
      rewrite add_sub' in *.
      rewrite (perm_inv_is_rinv_of_permutation _ g Hg) in *; [|lia].
      replace (n + (f (n + g d) - n)) with (f (n + g d)) in * by lia.
      rewrite Hfeq in *; try lia.
      apply Nat.add_lt_mono_l, Hgbdd; easy.
    + unfold biperm_compose_perm_r.
      pose proof (Hfbdd k ltac:(easy)).
      bdestructΩ';
      let show_lt := (match goal with
      |- context[g ?k] => specialize (Hgbdd k)
      end; lia) in 
      let do_tac := first 
      [ reflexivity | assumption |
        specialize (e ltac:(show_lt)) |
        rewrite (perm_inv_is_rinv_of_permutation _ g Hg) in * |
        rewrite (perm_inv_is_linv_of_permutation _ g Hg) in * |
        rewrite Hfeq in * by (show_lt + easy) |
        apply Hf | apply Hgbdd |
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
      rewrite add_sub' |
      lia | 
      rewrite (perm_inv_is_rinv_of_permutation _ g Hg) in *; [|lia] |
      replace (n + (f k - n)) with (f k) in * by lia]
      in repeat do_tac.
      rewrite add_sub' in *.
      rewrite (perm_inv_is_rinv_of_permutation _ g Hg) in *; [|lia].
      replace (n + (f k - n)) with (f k) in * by lia.
      rewrite Hfeq in *; lia.
Qed.

Lemma biperm_compose_perm_l_biperm n m f g 
  (Hf : bipermutation (n + m) f) (Hg : permutation n g) : 
  bipermutation (n + m) (biperm_compose_perm_l n m f g).
Proof.
  intros k Hk.
  split; 
    [ apply biperm_compose_perm_l_bdd; 
    apply Hf + apply permutation_bdd + easy; easy 
    | split].
  - unfold biperm_compose_perm_l.
    bdestructΩ'; try (apply Hf; easy).
    + intros Hfalse.
      apply (f_equal g) in Hfalse.
      rewrite (perm_inv_is_rinv_of_permutation _ g Hg) in Hfalse by easy.
      apply Hf in Hfalse; [easy|].
      specialize (permutation_bdd Hg k); lia.
    + pose proof (perm_inv_bdd n g (f k)); lia.
  - pose proof (fun k Hk => proj1 (Hf k Hk)) as Hfbdd.
    pose proof (fun k Hk => proj1 (proj2 (Hf k Hk))) as Hfne.
    pose proof (fun k Hk => proj2 (proj2 (Hf k Hk))) as Hfeq.
    pose proof (permutation_bdd Hg) as Hgbdd.
    unfold biperm_compose_perm_l.
    bdestructΩ';
    let show_lt := (match goal with
    |- g ?k < ?val => specialize (Hgbdd k)
    end; lia) in 
    repeat first 
      [ reflexivity | assumption |
        rewrite (perm_inv_is_rinv_of_permutation _ g Hg) in * by easy |
        rewrite (perm_inv_is_linv_of_permutation _ g Hg) in * by easy |
        rewrite Hfeq in * by (show_lt + easy) |
        assert (Hfgk : f (g k) < n) by assumption;
        specialize (perm_inv_bdd n g _ Hfgk); lia |
        match goal with
        | |- ?n <= ?k => 
          bdestruct (n <=? k); [easy|];
          specialize (Hgbdd k ltac:(easy)); lia
        | H : perm_inv _ _ _ >= _ |- _ =>
          apply perm_inv_ge in H; lia
      end |
      lia].
      + specialize (Hgbdd k); lia.
      + specialize (Hgbdd k); lia.
      + enough (f (g k) < n + m) by lia.
        apply Hf.
        specialize (Hgbdd k); lia.
      + specialize (Hfbdd k); lia.
Qed.

Lemma perm_inv_compose {n f g} (Hf : permutation n f) (Hg : permutation n g) : 
  forall k, k < n -> perm_inv n g (perm_inv n f k) =
  perm_inv n (fun x => f (g x)) k.
Proof.
  pose proof (permutation_compose n f g Hf Hg) as e.
  unfold Basics.compose in e.
  apply permutation_inverse_injective with (fun x => f (g x)).
  - easy.
  - unfold Basics.compose.
    split; intros k Hk.
    + rewrite 2!perm_inv_is_rinv_of_permutation; 
      try apply perm_inv_bdd; easy.
    + rewrite 2!perm_inv_is_linv_of_permutation; 
      try apply permutation_bdd; easy.
  - unfold Basics.compose.
    split; intros k Hk.
    + rewrite (perm_inv_is_rinv_of_permutation n (fun x => f (g x))); easy.
    + rewrite (perm_inv_is_linv_of_permutation n (fun x => f (g x))); easy.
Qed.

Lemma biperm_compose_perm_l_compose n m f g h 
  (Hf : bipermutation (n + m) f)
  (Hg : permutation n g) (Hh : permutation n h) :
  forall k, 
  biperm_compose_perm_l n m (biperm_compose_perm_l n m f g) h k =
  biperm_compose_perm_l n m f (fun x => g (h x)) k.
Proof.
  intros k.
  unfold biperm_compose_perm_l.
  pose proof (fun k Hk => proj1 (Hf k Hk)) as Hfbdd.
  (* pose proof (fun k Hk => proj1 (proj2 (Hf k Hk))) as Hfne. *)
  (* pose proof (fun k Hk => proj2 (proj2 (Hf k Hk))) as Hfeq. *)
  pose proof (permutation_bdd Hg) as Hgbdd.
  pose proof (permutation_bdd Hh) as Hhbdd.
  pose proof (permutation_compose n g h Hg Hh) as Hgh.
  bdestructΩ'; 
  rewrite ?perm_inv_compose; try easy + lia;
  let show_lt := (match goal with
  | |- context[g ?k] => specialize (Hgbdd k); lia
  | |- context[h ?k] => specialize (Hhbdd k); lia
  end; lia) in 
  let do_tac := first 
  [ assumption | 
    apply perm_inv_bdd; lia | show_lt |
    apply Hgbdd; lia | apply Hhbdd; lia | apply Hfbdd; lia |
    match goal with
    | H : perm_inv _ _ _ >= _ |- _ =>
      apply perm_inv_ge in H
    | |- perm_inv _ _ _ = _ =>
      apply perm_inv_eq_iff
  end]
  in repeat do_tac.
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
  pose proof (permutation_bdd Hg) as Hgbdd.
  pose proof (permutation_bdd Hh) as Hhbdd.
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
    apply perm_inv_bdd | show_lt |
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

Definition cap_cup_rel : nat -> nat :=
  fun k => if 2 <=? k then k else 
  if k =? 0 then 1 else 0.

Lemma cap_cup_rel_biperm : bipermutation 2 cap_cup_rel.
Proof.
  unfold cap_cup_rel.
  intros k Hk.
  bdestructΩ'.
Qed.

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

Definition n_m_cup_cap (n m : nat) : nat -> nat :=
  fun k => if n + n + (m + m) <=? k then k else
  if Nat.even k then S k else pred k.

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

Definition idn_biperm (n : nat) : nat -> nat :=
  fun k => if n + n <=? k then k else
  if k <? n then n + k else k - n.

Lemma idn_biperm_bipermutation n : 
  bipermutation (n + n) (idn_biperm n).
Proof.
  unfold idn_biperm.
  intros k Hk; bdestructΩ'.
Qed.

Definition realize_biperm_data (lperm rperm : nat -> nat) 
  (nid ncup ncap : nat) :=
  biperm_compose_perm_l (nid + (ncup + ncup)) (nid + (ncap + ncap))
    (biperm_compose_perm_r (nid + (ncup + ncup)) (nid + (ncap + ncap))
    (stack_biperms nid nid (ncup + ncup) (ncap + ncap) 
      (idn_biperm nid) (n_m_cup_cap ncup ncap))
    rperm)
    lperm.

Lemma realize_biperm_data_bipermutation {lperm rperm} {nid ncup ncap} 
  (Hlperm : permutation (nid + (ncup + ncup)) lperm)
  (Hrperm : permutation (nid + (ncap + ncap)) rperm) :
  bipermutation (nid + (ncup + ncup) + (nid + (ncap + ncap)))
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  unfold realize_biperm_data.
  apply biperm_compose_perm_l_biperm; [|easy].
  apply biperm_compose_perm_r_biperm; [|easy].
  apply stack_biperms_bipermutation.
  - apply idn_biperm_bipermutation.
  - apply n_m_cup_cap_bipermutation.
Qed.

Section Foliation.

Inductive ZX_elem : forall (n m : nat), Set :=
  | ElemEmpty : ZX_elem 0 0
  | ElemCap : ZX_elem 0 2 (* FIXME: Fix for cap-cup switch*)
  | ElemCup : ZX_elem 2 0
  | ElemSwap : ZX_elem 2 2
  | ElemWire : ZX_elem 1 1
  | ElemBox : ZX_elem 1 1
  | ElemX (n m : nat) (a : R) : ZX_elem n m
  | ElemZ (n m : nat) (a : R) : ZX_elem n m.

Inductive ZX_sheet : forall (n m : nat), Set :=
  | SheetElement {n m} (padl : nat)
    (zx : ZX_elem n m) (padr : nat) : 
    ZX_sheet (padl + n + padr) (padl + m + padr).

Inductive ZX_folio : forall (n m : nat), Set :=
  | FolioNil (n : nat) : ZX_folio n n
  | FolioCons {n m o} (st : ZX_sheet n m) 
    (fs : ZX_folio m o) : ZX_folio n o.

Definition zx_of_elem {n m} (zx : ZX_elem n m) : ZX n m :=
  match zx with
  | ElemEmpty => Empty
  | ElemCap => Cap
  | ElemCup => Cup
  | ElemSwap => Swap
  | ElemWire => Wire
  | ElemBox => Box
  | ElemX n m a => X_Spider n m a
  | ElemZ n m a => Z_Spider n m a
  end.

Definition zx_of_sheet {n m} (zx : ZX_sheet n m) : ZX n m :=
  match zx with
  | SheetElement padl elem_zx padr =>
    n_wire padl ↕ zx_of_elem elem_zx ↕ n_wire padr
  end.

Fixpoint zx_of_folio {n m} (zxs : ZX_folio n m) : ZX n m :=
  match zxs with
  | FolioNil n => n_wire n
  | FolioCons st fs => zx_of_sheet st ⟷ zx_of_folio fs
  end.

Fixpoint compose_zx_folio {n m o} (fs : ZX_folio n m) (gs : ZX_folio m o) 
  : ZX_folio n o :=
  match fs with
  | FolioNil k => fun gs => gs
  | FolioCons st fs' => fun gs => FolioCons st (compose_zx_folio fs' gs)
  end gs.

Definition cast_zx_sheet {n m n' m'} (Hn : n = n') (Hm : m = m') 
  (st : ZX_sheet n m) : ZX_sheet n' m'.
  case Hn, Hm.
  exact st.
Defined.

Lemma cast_zx_sheet_id {n m} (Hn : n = n) (Hm : m = m) zx : 
  cast_zx_sheet Hn Hm zx = zx.
Proof.
  rewrite (UIP_nat _ _ Hm eq_refl), (UIP_nat _ _ Hn eq_refl).
  easy.
Qed.

Lemma add_assoc_four {a b c d} : a + b + c + d = a + (b + c + d).
Proof.
  now rewrite 2!Nat.add_assoc.
Qed.

Lemma add_assoc_three {a b c} : a + (b + c) = a + b + c.
Proof.
  now rewrite Nat.add_assoc.
Qed.

Definition pad_stack_l {n m} (padl : nat) (st : ZX_sheet n m) : 
  ZX_sheet (padl + n) (padl + m) :=
  match st with
  | SheetElement padl' zx_elem padr => 
    cast_zx_sheet add_assoc_four add_assoc_four 
      (SheetElement (padl + padl') zx_elem padr)
  end.

Definition pad_stack_r {n m} (padr : nat) (st : ZX_sheet n m) : 
  ZX_sheet (n + padr) (m + padr) :=
  match st with
  | SheetElement padl zx_elem padr' => 
    cast_zx_sheet add_assoc_three add_assoc_three
      (SheetElement padl zx_elem (padr' + padr))
  end.

Fixpoint pad_folio_l {n m} (padl : nat) (fs : ZX_folio n m) : 
  ZX_folio (padl + n) (padl + m) := 
  match fs with
  | FolioNil n' => FolioNil (padl + n')
  | FolioCons st fs => 
    FolioCons (pad_stack_l padl st) (pad_folio_l padl fs)
  end.

Fixpoint pad_folio_r {n m} (padr : nat) (fs : ZX_folio n m) : 
  ZX_folio (n + padr) (m + padr) := 
  match fs with
  | FolioNil n' => FolioNil (n' + padr)
  | FolioCons st fs => 
    FolioCons (pad_stack_r padr st) (pad_folio_r padr fs)
  end.

Local Notation "'&' z" := 
  (FolioCons (SheetElement 0 z 0) (FolioNil _)) (at level 30).

Fixpoint ZX_folio_of_zx {n m} (zx : ZX n m) : ZX_folio n m :=
  match zx with
  | Empty => & ElemEmpty
  | Cap => & ElemCap
  | Cup => & ElemCup
  | Swap => & ElemSwap
  | Wire => & ElemWire
  | Box => & ElemBox
  | X_Spider n m a => 
      FolioCons (cast_zx_sheet (Nat.add_0_r n) (Nat.add_0_r m) 
        (SheetElement 0 (ElemX n m a) 0)) (FolioNil m)
  | Z_Spider n m a => 
    FolioCons (cast_zx_sheet (Nat.add_0_r n) (Nat.add_0_r m) 
      (SheetElement 0 (ElemZ n m a) 0)) (FolioNil m)
  | @Stack n0 m0 n1 m1 zx0 zx1 =>
    compose_zx_folio 
      (pad_folio_r n1 (ZX_folio_of_zx zx0))
      (pad_folio_l m0 (ZX_folio_of_zx zx1))
  | Compose zx0 zx1 => 
    compose_zx_folio (ZX_folio_of_zx zx0) (ZX_folio_of_zx zx1)
  end.

Lemma zx_of_sheet_cast {n m n' m'} (Hn : n = n') (Hm : m = m') zx :
  zx_of_sheet (cast_zx_sheet Hn Hm zx) = 
  cast _ _ (eq_sym Hn) (eq_sym Hm) (zx_of_sheet zx).
Proof.
  subst; easy.
Qed.

Tactic Notation "clean_eqns" tactic(tac) :=
  unshelve (tac); [reflexivity + lia..|].

Lemma zx_of_folio_pad_l {n m} (zx : ZX_folio n m) padl : 
  zx_of_folio (pad_folio_l padl zx) ∝ n_wire padl ↕ zx_of_folio zx.
Proof.
  induction zx as [n' | n' m' o' [padl' elem padr'] zx]; simpl.
  - now rewrite n_wire_stack.
  - rewrite zx_of_sheet_cast; simpl.
    rewrite IHzx.
    rewrite <- n_wire_stack.
    clean_eqns
    rewrite 2!stack_assoc, 2!cast_contract, cast_stack_distribute,
      stack_assoc_back, cast_contract, 2!cast_id.
    now rewrite stack_nwire_distribute_l.
Qed.

Lemma zx_of_folio_pad_r {n m} (zx : ZX_folio n m) padr : 
  zx_of_folio (pad_folio_r padr zx) ∝ zx_of_folio zx ↕ n_wire padr.
Proof.
  induction zx as [n' | n' m' o' [padl' elem padr'] zx]; simpl.
  - now rewrite n_wire_stack.
  - rewrite zx_of_sheet_cast; simpl.
    rewrite IHzx.
    rewrite <- n_wire_stack.
    clean_eqns rewrite stack_assoc_back, cast_contract, cast_id.
    now rewrite stack_nwire_distribute_r.
Qed.

Lemma zx_of_compose_zx_folio {n m o} (zx0 : ZX_folio n m) (zx1 : ZX_folio m o) :
  zx_of_folio (compose_zx_folio zx0 zx1) ∝
  zx_of_folio zx0 ⟷ zx_of_folio zx1.
Proof.
  induction zx0; simpl.
  - now rewrite nwire_removal_l.
  - now rewrite IHzx0, ComposeRules.compose_assoc.
Qed.


Lemma zx_of_folio_of_zx_prop {n m} (zx : ZX n m) : 
  zx_of_folio (ZX_folio_of_zx zx) ∝ zx.
Proof.
  induction zx; 
  [ let simpls := 
      (cbn [ZX_folio_of_zx zx_of_folio 
        zx_of_sheet zx_of_elem]) in
    simpls; 
    rewrite ?zx_of_sheet_cast;
    simpls;
    (clean_eqns rewrite ?nwire_removal_r,
    ?stack_empty_l, ?stack_empty_r, ?cast_contract);
    apply cast_id + reflexivity
    ..| |]; simpl.
  - rewrite zx_of_compose_zx_folio.
    rewrite zx_of_folio_pad_l, zx_of_folio_pad_r.
    rewrite <- stack_compose_distr,
      nwire_removal_l, nwire_removal_r.
    apply stack_compat; easy.
  - rewrite zx_of_compose_zx_folio.
    apply compose_compat; easy.
Qed.

Lemma zx_foliation_ind (P : forall {n m}, ZX n m -> Prop) 
  (Pcompat : forall {n m} (zx0 zx1 : ZX n m), zx1 ∝ zx0 -> P zx1 -> P zx0)
  (Pbase : forall n, P (n_wire n)) 
  (Pind_Empty : forall padl padr m (zx : ZX _ m), 
    P zx -> P (n_wire padl ↕ ⦰ ↕ n_wire padr ⟷ zx))
  (Pind_Cap : forall padl padr m (zx : ZX _ m), 
    P zx -> P (n_wire padl ↕ Cap ↕ n_wire padr ⟷ zx))
  (Pind_Cup : forall padl padr m (zx : ZX _ m), 
    P zx -> P (n_wire padl ↕ Cup ↕ n_wire padr ⟷ zx))
  (Pind_Swap : forall padl padr m (zx : ZX _ m), 
    P zx -> P (n_wire padl ↕ Swap ↕ n_wire padr ⟷ zx)) 
  (Pind_Wire : forall padl padr m (zx : ZX _ m), 
    P zx -> P (n_wire padl ↕ Wire ↕ n_wire padr ⟷ zx)) 
  (Pind_Box : forall padl padr m (zx : ZX _ m), 
    P zx -> P (n_wire padl ↕ Box ↕ n_wire padr ⟷ zx))  
  (Pind_X : forall padl padr n' m' a m (zx : ZX _ m), 
    P zx -> P (n_wire padl ↕ X_Spider n' m' a ↕ n_wire padr ⟷ zx)) 
  (Pind_Z : forall padl padr n' m' a m (zx : ZX _ m), 
    P zx -> P (n_wire padl ↕ Z_Spider n' m' a ↕ n_wire padr ⟷ zx)) : 
    forall {n m} (zx : ZX n m), P zx.
Proof.
  intros n m zx.
  apply (Pcompat n m zx (zx_of_folio (ZX_folio_of_zx zx))
    (zx_of_folio_of_zx_prop zx)).
  generalize (ZX_folio_of_zx zx).
  clear zx.
  intros zxf.
  induction zxf as [n|n m o [n' m' padl [] padr]]; simpl; auto.
Qed.

Definition compose_cap_biperm_l_prefun (padl : nat) (g : nat -> nat) :=
  fun k => 
  if k =? padl then S padl else if S padl =? k then padl else
  if padl =? g k then g (S padl) else
  if S padl =? g k then g (padl) else g k.

Definition compose_cap_biperm_l (padl : nat) (g : nat -> nat) :=
  fun k => 
    let outf := compose_cap_biperm_l_prefun padl g
      (if padl <=? k then 2 + k else k) in
    if S padl <? outf then outf - 2 else outf.

Lemma sub_eq_iff {a b m} : b <= a ->
  a - b = m <-> a = b + m.
Proof.
  lia.
Qed.

Lemma bipermutation_injective {n} {g : nat -> nat} 
  (Hg : bipermutation n g) i j (Hi : i < n) (Hj : j < n) : 
  g i = g j <-> i = j.
Proof.
  rewrite (bipermutation_eq_iff _ _ Hg), (proj2 (proj2 (Hg j Hj)));
  lia + apply Hg; lia.
Qed.

Lemma compose_cap_biperm_l_prefun_bipermutation (padl padr m : nat) {g} 
  (Hg : bipermutation (padl + 2 + padr + m) g) :
  bipermutation (padl + 2 + padr + m) (compose_cap_biperm_l_prefun padl g).
Proof.
  pose proof (fun i Hi => proj1 (Hg i Hi)) as Hgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hg i Hi))) as Hgne.
  pose proof (fun i Hi => proj2 (proj2 (Hg i Hi))) as Hgeq.
  intros i Hi; split; [|split]; unfold compose_cap_biperm_l_prefun.
  - bdestructΩ';
    match goal with 
    | |- context[ g ?i ] => specialize (Hgbdd i); lia
    end.
  - bdestructΩ'; 
    match goal with 
    | |- context[ g ?i ] => pose proof (Hgne i ltac:(lia)); try lia
    end;
    rewrite (bipermutation_eq_iff _ _ Hg); lia.
  - pose proof (Hgeq i Hi).
    bdestructΩ';
    repeat first [
      match goal with
    | H : g ?i = g ?j |- _ => 
      apply (bipermutation_injective Hg 
        i j ltac:(lia) ltac:(lia)) in H
    | H : g ?i = ?i |- _ => 
      specialize (Hgne i ltac:(lia)); lia
    | H : ?i = g ?i |- _ => 
      specialize (Hgne i ltac:(lia)); lia
    end |
    rewrite !Hgeq in * by lia; lia]; try lia;
    repeat first [
      match goal with
    (* | H : g ?i = ?j |- _ => 
      rewrite (bipermutation_eq_iff _ _ Hg) in H by lia; try lia *)
    | H : ?i = g ?j |- _ => 
      rewrite <- (bipermutation_eq_iff _ _ Hg) in H by lia; try lia
    end].
Qed.

Lemma remove_swap_bipermutation {n} {f : nat -> nat} (Hf : bipermutation n f) 
  a (Ha : S a < n) (Hab : f a = S a) : 
  bipermutation (n - 2) 
  (fun k => 
    let outf := f (if a <=? k then 2 + k else k) in
    if S a <? outf then outf - 2 else outf).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  assert (Ha' : f (S a) = a) by (rewrite <- Hab, Hfeq; lia).
  cbn zeta.
  intros i Hi; split; [|split].
  - bdestructΩ';
    match goal with 
    | |- context[f ?i] => specialize (Hfbdd i ltac:(lia))
    end; try lia.
    + bdestruct (f (2 + i) =? S a); [|lia].
      rewrite (bipermutation_eq_iff (2 + i) (S a) Hf) in *; lia.
    + bdestruct (f i =? S a); [|bdestruct (f i =? a); [|lia]];
      [rewrite (bipermutation_eq_iff i (S a) Hf) in *; lia|].
      rewrite (bipermutation_eq_iff i a Hf) in *; lia.
  - bdestructΩ';
    match goal with 
    | |- context[f ?i] => specialize (Hfne i ltac:(lia))
    | |- _ - _ <> _ => rewrite sub_eq_iff by lia
    end; try lia.
    intros Hfalse.
    assert (Hdisj: i = S a \/ i = a) by lia.
    destruct Hdisj; subst.
    + rewrite (bipermutation_eq_iff (2 + S a) (S a) Hf) in *; lia.
    + rewrite (bipermutation_eq_iff (2 + a) (a) Hf) in *; lia.
  - bdestructΩ';
    repeat first [match goal with
    | |- context[_ + (_ - _)] => 
      rewrite Nat.add_sub_assoc, add_sub' in * by lia
    end 
    | rewrite Hfeq in * by lia
    | rewrite sub_eq_iff by lia]; try lia.
    + assert (Hdisj: f (2 + i) = S a \/ f (2 + i) = a) by lia.
      destruct Hdisj as [Hrw | Hrw]; rewrite Hrw in *.
      * rewrite (bipermutation_eq_iff (2 + i) (S a) Hf), 
        Ha', Hrw in * by lia. 
        rewrite (bipermutation_eq_iff _ _ Hf); lia.
      * rewrite (bipermutation_eq_iff (2 + i) a Hf), Hab, Hrw in * by lia. 
        rewrite (bipermutation_eq_iff (2 + a) (S a) Hf), Ha'; lia.
    + assert (Hdisj: f (2 + i) = S a \/ f (2 + i) = a) by lia.
      destruct Hdisj as [Hrw | Hrw]; rewrite Hrw in *.
      * rewrite (bipermutation_eq_iff (2 + i) (S a) Hf), Ha' in *; lia.
      * rewrite (bipermutation_eq_iff (2 + i) a Hf), Hab in *; lia.
    + assert (Hdisj: f i = S a \/ f i = a) by lia.
      destruct Hdisj as [Hrw | Hrw]; rewrite Hrw in *.
      * rewrite (bipermutation_eq_iff i (S a) Hf), Ha' in *; lia.
      * rewrite (bipermutation_eq_iff i a Hf), Hab in *; lia.
    + assert (Hdisj: f i = S a \/ f i = a) by lia.
      destruct Hdisj as [Hrw | Hrw]; rewrite Hrw in *.
      * rewrite (bipermutation_eq_iff i (S a) Hf), Ha' in *; lia.
      * rewrite (bipermutation_eq_iff i a Hf), Hab in *; lia.
Qed.

(* Lemma compose_cap_biperm_l_bipermutation_old (padl padr m : nat) {g} 
  (Hg : bipermutation (padl + 2 + padr + m) g) :
  bipermutation (padl + 0 + padr + m) (compose_cap_biperm_l padl g).
Proof.
  replace (padl + 0 + padr + m) with (padl + 2 + padr + m - 2) by lia.
  apply remove_swap_bipermutation; 
  [apply compose_cap_biperm_l_prefun_bipermutation; easy | lia | ].
  unfold compose_cap_biperm_l_prefun.
  bdestructΩ'.
Qed. *)

Lemma compose_cap_biperm_l_bipermutation (padl padr m : nat) {g} 
  (Hg : bipermutation (padl + 2 + padr + m) g) :
  bipermutation (padl + 0 + padr + m) 
    (compose_cap_biperm_l (m + padl) g).
Proof.
  replace (padl + 0 + padr + m) with (m + padl + 2 + padr + 0 - 2) by lia.
  (* replace (padl + 0 + padr + m) with (padl + 2 + padr + m - 2) by lia. *)
  apply remove_swap_bipermutation;
  [ | lia | ].
  - apply compose_cap_biperm_l_prefun_bipermutation.
    replace (m + padl + 2 + padr + 0) with (padl + 2 + padr + m) by lia.
    easy.
  - unfold compose_cap_biperm_l_prefun.
    bdestructΩ'.
Qed.

Definition compose_cup_biperm_l (padl : nat) (g : nat -> nat) :=
  fun k => 
  if padl =? k then S padl else if S padl =? k then padl else
  if k <? padl then 
    if g k <? padl then g k else 2 + g k
  else 
    if g (k - 2) <? padl then g (k - 2) else 2 + g (k - 2).


(* Lemma compose_cup_biperm_l_bipermutation_old (padl padr m : nat) {g} 
  (Hg : bipermutation (padl + 0 + padr + m) g) :
  bipermutation (padl + 2 + padr + m) (compose_cup_biperm_l padl g).
Proof.
  pose proof (fun i Hi => proj1 (Hg i Hi)) as Hgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hg i Hi))) as Hgne.
  pose proof (fun i Hi => proj2 (proj2 (Hg i Hi))) as Hgeq.
  intros i Hi; split; [|split]; unfold compose_cup_biperm_l.
  - bdestructΩ';
    match goal with
    | |- context[g ?i] => specialize (Hgbdd i); lia
    end.
  - bdestructΩ';
    match goal with
    | |- context[g ?i] => specialize (Hgne i); lia
    end.
  - bdestructΩ'; 
    rewrite ?add_sub', ?Hgeq in *; lia.
Qed. *)

Lemma compose_cup_biperm_l_bipermutation (padl padr m : nat) {g} 
  (Hg : bipermutation (padl + 0 + padr + m) g) :
  bipermutation (padl + 2 + padr + m) (compose_cup_biperm_l (m + padl) g).
Proof.
  pose proof (fun i Hi => proj1 (Hg i Hi)) as Hgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hg i Hi))) as Hgne.
  pose proof (fun i Hi => proj2 (proj2 (Hg i Hi))) as Hgeq.
  intros i Hi; split; [|split]; unfold compose_cup_biperm_l.
  - bdestructΩ';
    match goal with
    | |- context[g ?i] => specialize (Hgbdd i); lia
    end.
  - bdestructΩ';
    match goal with
    | |- context[g ?i] => specialize (Hgne i); lia
    end.
  - bdestructΩ'; 
    rewrite ?add_sub', ?Hgeq in *; lia.
Qed.

(* Definition compose_swap_biperm_l_old (padl padr m : nat) (g : nat -> nat) :=
  biperm_compose_perm_l (padl + 2 + padr) m 
    g (swap_perm padl (S padl) (padl + 2 + padr)). *)

Definition compose_swap_biperm_l (padl padr m : nat) (g : nat -> nat) :=
  biperm_compose_perm_r m (padl + 2 + padr)
    g (swap_perm padl (S padl) (padl + 2 + padr)).

Lemma compose_swap_biperm_l_bipermutation (padl padr m : nat) {g} 
  (Hg : bipermutation (padl + 2 + padr + m) g) :
  bipermutation (padl + 2 + padr + m) (compose_swap_biperm_l padl padr m g).
Proof.
  rewrite Nat.add_comm in *.
  apply biperm_compose_perm_r_biperm; [easy|].
  apply swap_perm_S_permutation; lia.
Qed.

Fixpoint biperm_of_zx_folio {n m} (zx : ZX_folio n m) : nat -> nat :=
  match zx with
  | FolioNil n' => idn_biperm n'
  | FolioCons (SheetElement padl zx_elem padr) fs => match zx_elem with
    | ElemEmpty => biperm_of_zx_folio fs
    | ElemCap =>
        compose_cap_biperm_l (m + padl) (biperm_of_zx_folio fs)
    | ElemCup => 
        compose_cup_biperm_l (m + padl) (biperm_of_zx_folio fs)
    | ElemSwap => 
        compose_swap_biperm_l padl padr m (biperm_of_zx_folio fs)
    | ElemWire => biperm_of_zx_folio fs
    | ElemBox => id
    | ElemX n' m' a => id
    | ElemZ n' m' a => id
    end
  end.

Inductive ZXbiperm_elem : forall {n m} (zx : ZX_elem n m), Prop :=
  | BipermEmpty : ZXbiperm_elem ElemEmpty
  | BipermCap : ZXbiperm_elem ElemCap
  | BipermCup : ZXbiperm_elem ElemCup
  | BipermSwap : ZXbiperm_elem ElemSwap
  | BipermWire : ZXbiperm_elem ElemWire.

Inductive ZXbiperm_sheet : forall {n m} (zx : ZX_sheet n m), Prop :=
  | BipermSheet {n m} padl {zx : ZX_elem n m} 
    (H : ZXbiperm_elem zx) padr : 
    ZXbiperm_sheet (SheetElement padl zx padr).

Inductive ZXbiperm_folio : forall {n m} (zx : ZX_folio n m), Prop :=
  | BipermNil (n : nat) : ZXbiperm_folio (FolioNil n)
  | BipermCons {n m o} {zx : ZX_sheet n m} (Hzx : ZXbiperm_sheet zx)
      {fs : ZX_folio m o} (Hfs : ZXbiperm_folio fs) : 
      ZXbiperm_folio (FolioCons zx fs).

Lemma biperm_of_zxbiperm_folio_bipermutation 
  {n m} {zx : ZX_folio n m} (H : ZXbiperm_folio zx) :
  bipermutation (n + m) (biperm_of_zx_folio zx).
Proof.
  induction H as [n|n m o ? [n' m' padl ? [] padr]]; [apply idn_biperm_bipermutation|..]; simpl.
  - easy.
  - apply compose_cap_biperm_l_bipermutation; easy.
  - apply compose_cup_biperm_l_bipermutation; easy.
  - apply compose_swap_biperm_l_bipermutation; easy.
  - easy.
Qed. 

Definition number_preserved (i : nat) (f : nat -> nat) (bound : nat) :=
  forallb (fun k => eqb (Nat.testbit i k) 
    (Nat.testbit i (f k))) (seq 0 bound).
  (* forallb (fun k => 
  eqb (nth k (nat_to_binlist bound i) false) 
    (nth (f k) (nat_to_binlist bound i) false)) (seq 0 bound). *)







(* Notation flip_biperm f bound := 
  (fun k => pred (bound) - f (pred (bound) - k)). *)
    

Definition matrix_of_biperm (n m : nat) (f : nat -> nat) : Matrix (2^m) (2^n) :=
  fun i j =>
  (* if 2^m <=? i then C0 else if 2^n <=? j then C0 else *)
  if number_preserved (j * 2^m + i) 
  (f) (n + m) then C1 else C0.
                      (* this order works experimentally... :/ *)

(* Fixpoint is_ZX_folio {n m : nat} (zx : ZX n m) : bool :=
  match zx with
  | zx0 ↕ zx1 => is_ZX_folio zx0 && is_ZX_folio zx1
  | zx0 ⟷ zx1 => is_ZX_folio zx0 && is_ZX_folio zx1 *)

(* Definition is_ZX_folio_dec {n m : nat} (zx : ZX n m) :
  {fol & zx ∝ zx_of_folio fol} + {True}.
Proof.
  induction zx.0 *)

(* Definition biperm_of_zx_folio *)

Definition matrix_of_zx_folio_biperm {n m} (zx : ZX_folio n m) : 
  Matrix (2^m) (2^n) :=
  matrix_of_biperm n m (biperm_of_zx_folio zx).

Lemma pow_pos (n m : nat) : n <> 0 -> 0 < n ^ m.
Proof.
  induction m; simpl; lia.
Qed.

Lemma n_le_pow_2_n (n : nat) : n <= 2 ^ n.
Proof. 
  induction n; simpl; [lia|].
  pose proof (pow_pos 2 n).
  lia.
Qed.

Lemma testbit_add_pow2_small (i j s n : nat) (Hs : s < n) : 
  Nat.testbit (i + 2^n * j) s = Nat.testbit i s.
Proof.
  rewrite 2!Nat.testbit_eqb.
  replace n with (s + (n - s)) by lia.
  rewrite Nat.pow_add_r, <- Nat.mul_assoc, Nat.mul_comm, Nat.div_add by
    (apply Nat.pow_nonzero; lia).
  destruct (n - s) eqn:e; [lia|].
  cbn [Nat.pow].
  rewrite <- Nat.mul_assoc, Nat.mul_comm, Nat.mod_add by lia.
  easy.
Qed.

Lemma testbit_add_pow2_large (i j s n : nat) (Hs : n <= s) (Hi : i < 2^n) : 
  Nat.testbit (i + 2^n * j) s = Nat.testbit j (s - n).
Proof.
  replace s with (s-n + n) at 1 by lia.
  generalize (s - n) as d.
  intros d.
  rewrite 2!Nat.testbit_eqb.
  do 2 f_equal.
  rewrite Nat.pow_add_r, (Nat.mul_comm _ (2^_)), Nat.mul_comm,
    <- Nat.div_div, Nat.div_add by
    (apply Nat.pow_nonzero; lia).
  rewrite (Nat.div_small i) by easy.
  easy.
Qed.

Lemma testbit_add_pow2_split i j n (Hi : i < 2^n) : 
  forall s, 
  Nat.testbit (j * 2 ^ n + i) s =
  if s <? n then Nat.testbit i s else Nat.testbit j (s - n).
Proof.
  intros.
  rewrite Nat.add_comm, Nat.mul_comm.
  bdestruct (s <? n).
  - apply testbit_add_pow2_small; easy.
  - apply testbit_add_pow2_large; easy.
Qed.


Lemma and_andb {P P'} {b b'} : 
  reflect P b -> reflect P' b' -> 
  reflect (P /\ P') (b && b').
Proof.
  intros H H'; apply reflect_iff in H, H'.
  apply iff_reflect.
  rewrite andb_true_iff.
  now rewrite H, H'.
Qed.

Require Import Setoid.

Lemma Forall_forallb {A} (f : A -> bool) (P : A -> Prop)
  (Hf : forall a, P a <-> f a = true) : 
  forall l, Forall P l <-> forallb f l = true.
Proof.
  intros l.
  induction l; [repeat constructor|].
  simpl.
  rewrite andb_true_iff.
  rewrite Forall_cons_iff.
  apply Morphisms_Prop.and_iff_morphism; easy.
Qed.

Lemma eq_eqb_iff (b c : bool) : 
  b = c <-> eqb b c = true.
Proof.
  destruct b, c ; easy.
Qed.

Lemma Forall_seq {start len : nat} f : 
  Forall f (seq start len) <-> forall k, k < len -> f (start + k).
Proof.
  revert start;
  induction len; intros start;
  [split; constructor + lia|].
  simpl.
  rewrite Forall_cons_iff.
  split.
  - intros [Hfk H].
    rewrite IHlen in H.
    intros k Hk.
    destruct k.
    + rewrite Nat.add_0_r; easy.
    + specialize (H k).
      rewrite Nat.add_succ_r.
      apply H. 
      lia.
  - intros H.
    rewrite IHlen; split. 
    + specialize (H 0).
      rewrite Nat.add_0_r in H.
      apply H; lia.
    + intros k Hk; specialize (H (S k)).
      rewrite Nat.add_succ_r in H.
      apply H.
      lia.
Qed.

Lemma Forall_seq0 {len : nat} f : 
  Forall f (seq 0 len) <-> forall k, k < len -> f k.
Proof.
  apply (@Forall_seq 0 len f).
Qed.

Lemma number_preserved_iff_all_lt_eq ji nm f : 
  number_preserved ji f nm = true <->
  forall s, s < nm -> 
  Nat.testbit ji s = Nat.testbit ji (f s).
Proof.
  unfold number_preserved.
  rewrite <- Forall_forallb.
  2: (intros a; apply eq_eqb_iff). 
  rewrite Forall_seq.
  easy.
Qed.

Lemma forall_iff {A} (f g : A -> Prop) : 
  (forall a, (f a <-> g a)) ->
  ((forall a, f a) <-> (forall a, g a)).
Proof.
  intros ?; split; intros; apply H; auto.
Qed.

Lemma impl_iff (P Q Q' : Prop) : 
  ((P -> Q) <-> (P -> Q')) <->
  (P -> (Q <-> Q')).
Proof.
  split;
  intros ?; split; intros; apply H; auto.
Qed.

Lemma number_preserved_iff j i n m (Hi : i < 2^n) f : 
  number_preserved (j * 2^n + i) f (n + m) = true <->
  forall s, s < (n + m) -> 
  if s <? n then
    if (f s) <? n then 
      Nat.testbit i s = Nat.testbit i (f s)
    else 
      Nat.testbit i s = Nat.testbit j (f s - n)
  else 
    if (f s) <? n then 
      Nat.testbit j (s - n) = Nat.testbit i (f s)
    else 
      Nat.testbit j (s - n) = Nat.testbit j (f s - n).
Proof.
  rewrite number_preserved_iff_all_lt_eq.
  apply forall_iff.
  intros s. 
  rewrite impl_iff.
  intros Hs.
  rewrite 2!testbit_add_pow2_split by easy.
  bdestructΩ'; easy.
Qed.

Lemma mod_2_pow_S i n : 
  i mod 2^(S n) = 2^n * (Nat.b2n (Nat.testbit i n)) + (i mod (2^n)).
Proof.
  enough (Hmod : i mod 2^(S n) = 
    (2^n * (Nat.b2n (Nat.testbit i n)) + (i mod (2^n))) mod 2^(S n)).
  - rewrite (Nat.mod_small (_ + _)) in Hmod; [easy|].
    simpl.
    pose proof (Nat.mod_upper_bound i (2^n) 
      ltac:(apply Nat.pow_nonzero; lia)).
    destruct (Nat.testbit i n); simpl; lia.
  - rewrite Nat.pow_succ_r by lia.
    symmetry.
    rewrite (Nat.mul_comm 2 (2^n)).
    rewrite 2!Nat.Div0.mod_mul_r.
    rewrite Nat.mul_comm, (Nat.add_comm (_ * _)).
    pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
    rewrite Nat.mod_add, Nat.mod_mod, Nat.div_add by easy.
    rewrite Nat.div_small by (now apply Nat.mod_upper_bound).
    do 2 f_equal.
    rewrite Nat.testbit_eqb.
    bdestructΩ'; simpl Nat.b2n.
    simpl Nat.add.
    rewrite Nat.mod_0_l by easy.
    pose proof (Nat.mod_upper_bound (i / 2 ^ n) 2 ltac:(lia)).
    lia.
Qed.

Lemma mod_pow2_eq_closed_down i j n m : n <= m -> 
  i mod 2^m = j mod 2^m -> i mod 2^n = j mod 2^n.
Proof.
  intros Hnm Heq.
  replace m with (n + (m - n)) in * by lia.
  generalize dependent (m - n).
  intros k _.
  rewrite Nat.pow_add_r, 2!Nat.Div0.mod_mul_r.
  intros H.
  apply (f_equal (fun k => k mod 2^n)) in H.
  revert H.
  rewrite 2!(Nat.mul_comm (2^n)).
  rewrite 2!Nat.Div0.mod_add, 2!Nat.Div0.mod_mod.
  easy.
Qed.

Lemma bits_inj_upto i j n : 
  (forall s, s < n -> Nat.testbit i s = Nat.testbit j s) <->
  i mod 2^n = j mod 2^n.
Proof.
  split.
  - intros Heq.
    induction n;
    [now rewrite 2!Nat.mod_1_r|].
    rewrite 2!mod_2_pow_S.
    f_equal; [|apply IHn; intros k Hk; apply Heq; lia].
    rewrite Heq by lia.
    easy.
  - intros Heq s Hs.
    rewrite 2!Nat.testbit_eqb.
    rewrite (Nat.div_mod i (2^(S s)) ltac:(apply Nat.pow_nonzero; lia)).
    rewrite (Nat.div_mod j (2^(S s)) ltac:(apply Nat.pow_nonzero; lia)).
    rewrite (mod_pow2_eq_closed_down i j (S s) n ltac:(lia) Heq).
    rewrite 2!(Nat.mul_comm (2^ S s)), 2!(Nat.add_comm (_*_)).
    rewrite Nat.pow_succ_r by lia.
    rewrite 2!Nat.mul_assoc.
    rewrite 2!Nat.div_add by (apply Nat.pow_nonzero; lia).
    rewrite 2!Nat.Div0.mod_add.
    easy.
Qed.

Lemma lt_pow2_S_log2 i : i < 2 ^ S (Nat.log2 i).
Proof.
  destruct i; [cbn; lia|].
  apply Nat.log2_spec; lia.
Qed.

Lemma bits_inj_upto_small i j n (Hi : i < 2^n) (Hj : j < 2^n) : 
  (forall s, s < n -> Nat.testbit i s = Nat.testbit j s) <->
  i = j.
Proof.
  split; [|intros ->; easy].
  intros H; apply bits_inj_upto in H.
  assert (H2n : 2^n <> 0) by (apply Nat.pow_nonzero; lia).
  rewrite (Nat.div_mod i (2^n) H2n), (Nat.div_mod j (2^n) H2n).
  rewrite 2!Nat.div_small, Nat.mul_0_r by lia.
  easy.
Qed.

Lemma bits_inj i j : 
  (forall s, Nat.testbit i s = Nat.testbit j s) <-> i = j.
Proof.
  split; [|intros ->; easy].
  set (ub := 2^ max (S (Nat.log2 i)) (S (Nat.log2 j))).
  assert (Hi : i < ub) by 
    (enough (i < 2 ^ (S (Nat.log2 i))) by
    (pose proof (Nat.pow_le_mono_r 2 (S (Nat.log2 i)) _ 
      ltac:(easy) (Nat.le_max_l _ (S (Nat.log2 j)))); lia);
    apply lt_pow2_S_log2).
  assert (Hj : j < ub) by 
    (enough (j < 2 ^ (S (Nat.log2 j))) by
    (pose proof (Nat.pow_le_mono_r 2 (S (Nat.log2 j)) _ 
      ltac:(easy) (Nat.le_max_r (S (Nat.log2 i)) _)); lia);
    apply lt_pow2_S_log2).
  intros s.
  apply (bits_inj_upto_small i j _ Hi Hj).
  intros; easy.
Qed.

Lemma number_preserved_eq_of_eq_on (ij n : nat) f g : 
  (forall i, i < n -> f i = g i) ->
  number_preserved ij f n = number_preserved ij g n.
Proof.
  intros Hfg.
  apply eq_iff_eq_true.
  rewrite 2!number_preserved_iff_all_lt_eq.
  apply forall_iff; intros s; apply impl_iff; intros Hs.
  setoid_rewrite Hfg; easy.
Qed.

Lemma number_preserved_idn (n : nat) {i j} (Hi : i < 2^n) (Hj : j < 2^n) : 
  number_preserved (j * 2 ^ n + i) (idn_biperm n) (n + n) = (i =? j).
Proof.
  rewrite eq_iff_eq_true.
  rewrite number_preserved_iff by easy.
  unfold idn_biperm.
  rewrite Nat.eqb_eq.
  split.
  - intros H.
    apply (bits_inj_upto_small i j n Hi Hj).
    intros s Hs.
    specialize (H s ltac:(lia)).
    revert H.
    bdestructΩ'.
    now rewrite add_sub'.
  - intros -> s Hs.
    bdestructΩ'; 
    now rewrite add_sub'.
Qed.

(* Lemma number_preserved_idn_flipped (n : nat) {i j} (Hi : i < 2^n) (Hj : j < 2^n) : 
  number_preserved (j * 2 ^ n + i) 
  (flip_biperm (idn_biperm n) (n + n)) (n + n) = (i =? j).
Proof.
  rewrite <- (number_preserved_idn n Hi Hj).
  apply number_preserved_eq_of_eq_on.
  clear i j Hi Hj.
  intros i Hi.
  unfold idn_biperm.
  bdestructΩ'.
Qed. *)

Add Parametric Relation {n m} : (Matrix n m) (@mat_equiv n m) 
  reflexivity proved by ltac:(easy)
  symmetry proved by ltac:(intros A B H i j Hi Hj; 
    symmetry; apply H; easy)
  transitivity proved by ltac:(intros A B C H H' i j Hi Hj;
    transitivity (B i j); [apply H | apply H']; easy)
  as mat_equiv_setoid.

Add Parametric Morphism {n m} : (@scale n m) 
  with signature 
  eq ==> (@mat_equiv n m) ==> mat_equiv
  as scale_mat_equiv_proper.
Proof.
  unfold scale.
  intros x A B H i j Hi Hj.
  rewrite (H i j Hi Hj).
  easy.
Qed.

Lemma mat_equiv_prop_symm {n m} (A B : Matrix n m) : 
  (exists c : C, mat_equiv A (c .* B) /\ c <> 0%R)
  <-> exists c : C, mat_equiv B (c .* A) /\ c <> 0%R.
Proof.
  split;
  intros (c & Heq & Hc);
  prop_exists_nonzero (/ c); auto;
  now rewrite Heq, Mscale_assoc, Cmult_comm, Cinv_r, Mscale_1_l.
Qed.

(* Lemma matrix_of_biperm_split_cap  *)

Open Scope matrix_scope.

(* Lemma matrix_of_folio_compose_cap_biperm_l padl padr m f 
  (Hf : bipermutation (padl + 2 + padr + m) f) : 
  mat_equiv (matrix_of_biperm (padl + 0 + padr) m 
    (compose_cap_biperm_l padl f))
  (if f padl =? S padl 
  then 2%R .* matrix_of_biperm (padl + 2 + padr) m f
  else matrix_of_biperm (padl + 2 + padr) m f). *)

Lemma kron_I_r {n m p} (A : Matrix n m) :
  mat_equiv (A ⊗ I p)
  (fun i j => if i mod p =? j mod p then A (i / p) (j / p) else C0).
Proof.
  intros i j Hi Hj.
  unfold kron, I.
  pose proof (Nat.mod_upper_bound i p ltac:(lia)).
  bdestructΩ'; lca.
Qed.

Lemma kron_I_l {n m p} (A : Matrix n m) :
  mat_equiv (I p ⊗ A)
  (fun i j => if i / n =? j / m then A (i mod n) (j mod m) else C0).
Proof.
  intros i j Hi Hj.
  unfold kron, I.
  rewrite Nat.mul_comm in Hi.
  pose proof (Nat.Div0.div_lt_upper_bound _ _ _ Hi).
  bdestructΩ'; lca.
Qed.

Lemma testbit_make_gap i m k s : 
  Nat.testbit (i mod 2^m + (i/2^m) * 2^k * (2^m)) s =
  if s <? m then Nat.testbit i s else 
  if s <? k + m then false else
  Nat.testbit i (s - k).
Proof.
  rewrite Nat.add_comm.
  rewrite testbit_add_pow2_split by 
    (apply Nat.mod_upper_bound, Nat.pow_nonzero; easy).
  bdestructΩ'.
  - apply (proj2 (bits_inj_upto _ _ m) (Nat.Div0.mod_mod i _) s H).
  - rewrite Nat.testbit_eqb.
    replace k with ((k - (s-m) - 1 + 1) + (s-m)) by lia.
    rewrite 2!Nat.pow_add_r, Nat.mul_assoc, Nat.div_mul by
      (now apply Nat.pow_nonzero).
    change (2^1) with 2.
    now rewrite Nat.mul_assoc, Nat.Div0.mod_mul.
  - replace (s - m) with (s - m - k + k) by lia.
    rewrite Nat.mul_pow2_bits_add, Nat.div_pow2_bits.
    f_equal; lia.
Qed.

Lemma testbit_make_2_gap i m s : 
  Nat.testbit (i mod 2^m + (i/2^m) * 4 * (2^m)) s =
  if s <? m then Nat.testbit i s else 
  if s <? 2 + m then false else
  Nat.testbit i (s - 2).
Proof.
  change 4 with (2^2); apply testbit_make_gap.
Qed.

Lemma testbit_make_2_gap' i m s : 
  Nat.testbit ((i/2^m) * 4 * (2^m) + i mod 2^m) s =
  if s <? m then Nat.testbit i s else 
  if s <? 2 + m then false else
  Nat.testbit i (s - 2).
Proof.
  rewrite Nat.add_comm; apply testbit_make_2_gap.
Qed.

(* Lemma number_preserved_compose_cap_l {padl padr m} {i j} {f} 
  (Hf : bipermutation (padl + 2 + padr + m) f) 
  (Hi : i < 2 ^ m) (Hj : j < 2 ^ (padl + 0 + padr)) :
  number_preserved (j * 2 ^ m + i) (compose_cap_biperm_l (m + padl) f) 
    (padl + 0 + padr + m) = 
  number_preserved (((j mod 2^padl) + (j/2^padl)*4 * (2^padl)) * 2 ^ m + i)
    (compose_cap_biperm_l_prefun (m + padl) f) 
    (padl + 2 + padr + m).
Proof.
  apply eq_iff_eq_true.
  rewrite 2!number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_add_pow2_split; [|easy..].
  setoid_rewrite testbit_make_2_gap.
  split.
  - intros H.
    intros s Hs.
    bdestruct (s <? m + padl).
    + specialize (H s ltac:(lia)).
      revert H.
      (* assert (m + padl <> f s). *)
      unfold compose_cap_biperm_l, compose_cap_biperm_l_prefun.
      bdestructΩ'; try ((intros -> + idtac); easy + (f_equal; lia)).
      
      ); try (f_equal; lia).

    bdestruct (s <? m).
    bdestructΩ'.
    rewrite 2!(Nat.eqb_sym padl), 2!(Nat.eqb_sym (S padl)).
    bdestruct (pred (padl + 2 + padr + m) - s =? padl); 
    [|bdestruct (pred (padl + 2 + padr + m) - s =? S padl)].
    + replace s with (pred (padl + 2 + padr + m) - padl) by lia.
      replace (pred (padl + 2 + padr + m) - padl) with 
        (1 + padr + m) by lia.
      replace (pred (padl + 2 + padr + m) - S padl) with 
        (padr + m) by lia.
      rewrite 2!testbit_add_pow2_split by easy.
      bdestructΩ'.
      rewrite 2!Nat.add_sub.
      rewrite 2!Nat.testbit_eqb.
      change 4 with (2^1*2^1) at 1.
      rewrite Nat.mul_assoc, <- Nat.mul_assoc, <- Nat.pow_add_r.
      rewrite Nat.div_add by (apply Nat.pow_nonzero; easy).
      rewrite Nat.div_small by (pose proof (Nat.mod_upper_bound 
        j (2^padr) (Nat.pow_nonzero 2 _ ltac:(lia))); simpl; lia).
      rewrite Nat.div_add by (apply Nat.pow_nonzero; easy).
      rewrite (Nat.div_small (_ mod _)) by 
        (apply Nat.mod_upper_bound, Nat.pow_nonzero; easy).
      change (2^1) with 2.
      change (4) with (2*2).
      rewrite Nat.mul_assoc.
      rewrite 2!Nat.Div0.mod_add.
      easy.
    + 


        j (2^padr) (Nat.pow_nonzero 2 _ ltac:(lia))); simpl; lia).
      rewrite (Nat.div_mod j (2^(padl))) at 1 3 by
        (apply Nat.pow_nonzero; easy).
      rewrite (Nat.mul_comm (2^_)), (Nat.add_comm (_*(2^_))), Nat.div_add by
        (apply Nat.pow_nonzero; easy).
      rewrite (Nat.div_small (_ mod _)) by 
        (apply Nat.mod_upper_bound, Nat.pow_nonzero; easy).
      rewrite Nat.div_add
    
    replace s with (pred (padl + 2 + padr + m) - 
      (pred (padl + 2 + padr + m) - s)) at 1 by lia.
    assert (Hsubs : pred (padl + 2 + padr + m) - s 
      < padl + 2 + padr + m) by lia.
    revert Hsubs.
    generalize (pred (padl + 2 + padr + m) - s) as a.
    clear s Hs.
    intros s Hs.
    

    unfold compose_cap_biperm_l_prefun.
    rewrite 2!(Nat.eqb_sym _ s).
    bdestructΩ'.

  unfold compose_cap_biperm_l, compose_cap_biperm_l_prefun.
  split; [admit|intros].
  bdestruct (padl <=? s). *)

Add Parametric Morphism {n m o} : (@Mmult m n o) 
  with signature
  @mat_equiv m n ==> @mat_equiv n o ==> @mat_equiv m o
  as Mmult_proper.
Proof.
  intros A A' HA B B' HB.
  unfold Mmult.
  intros i j Hi Hj.
  apply big_sum_eq_bounded.
  intros k Hk.
  now rewrite HA, HB.
Qed.

Add Parametric Morphism {n m o p} : (@kron m n o p) 
  with signature
  @mat_equiv m n ==> @mat_equiv o p ==> 
  @mat_equiv (m*o) (n*p)
  as kron_proper.
Proof.
  intros A A' HA B B' HB.
  unfold kron.
  intros i j Hi Hj.
  rewrite HA, HB; 
  [easy|..];
  apply Nat.mod_upper_bound + apply Nat.Div0.div_lt_upper_bound; lia.
Qed.

Lemma cap_semantics i j : 
  ⟦ ⊂ ⟧ i j =
  if j =? 0 then if i =? 0 then C1 else if i =? 3 then C1 else C0 else C0.
Proof.
  simpl.
  do 5 (try destruct i);
  destruct j; cbn; easy + destruct j; easy.
Qed.

Lemma cup_semantics i j : 
  ⟦ ⊃ ⟧ i j =
  if i =? 0 then if j =? 0 then C1 else if j =? 3 then C1 else C0 else C0.
Proof.
  simpl.
  do 5 (try destruct j);
  destruct i; cbn; easy + destruct i; easy.
Qed.

Lemma orb_if {A} b c (v v' : A) : 
  (if (b || c) then v else v') =
  if b then v else if c then v else v'.
Proof.
  bdestructΩ'.
Qed.

Lemma f_equal_if {A} (b c : bool) (u v x y : A) : 
  b = c -> u = v -> x = y ->
  (if b then u else x) = (if c then v else y).
Proof.
  intros; subst; easy.
Qed.

Lemma div_mul_not_exact a b : b <> 0 -> 
  (a / b) * b = a - (a mod b).
Proof.
  intros Hb.
  rewrite (Nat.div_mod a b Hb) at 1 2.
  rewrite Nat.add_sub.
  rewrite (Nat.mul_comm b (a/b)), Nat.add_comm, Nat.div_add by easy.
  rewrite Nat.div_small by (apply Nat.mod_upper_bound; easy).
  easy.
Qed.

Section BigSumLemmas.

Local Open Scope group_scope.

Context {G} {H : Monoid G} {H0 : Group G} {H1 : Comm_Group G}
  {H2 : @Ring G H H0 H1}.

Lemma Gopp0 : - 0 = 0.
Proof.
  rewrite <- (Gplus_0_l (- 0)).
  apply H0.
Qed.

Lemma big_sum_opp (f : nat -> G) n : 
  - big_sum f n = big_sum (fun k => - f k) n.
Proof.
  induction n; simpl.
  - apply Gopp0.
  - rewrite Gopp_plus_distr.
    now rewrite Gplus_comm, IHn.
Qed.

Lemma big_sum_if_or 
  (ifl ifr : nat -> bool)
  (f : nat -> G) (n : nat) : 
  big_sum (fun k => if ifl k || ifr k then f k else 0) n =
  big_sum (fun k => if ifl k then f k else 0) n + 
  big_sum (fun k => if ifr k then f k else 0) n - 
  big_sum (fun k => if ifl k && ifr k then f k else 0) n.
Proof.
  unfold Gminus.
  rewrite big_sum_opp.
  rewrite <- 2!big_sum_plus.
  apply big_sum_eq_bounded.
  intros.
  bdestructΩ'; rewrite <- Gplus_assoc, ?Gopp_r, 
    ?Gopp0, ?Gplus_0_r, ?Gplus_0_l; easy.
Qed.

Lemma big_sum_if_eq (f : nat -> G) n k : 
  big_sum (fun x => if x =? k then f x else 0) n =
  if k <? n then f k else 0.
Proof.
  induction n; [easy|]. 
  simpl.
  rewrite IHn.
  bdestructΩ'; now rewrite ?Gplus_0_l, ?Gplus_0_r.
Qed.

Lemma big_sum_if_eq' (f : nat -> G) n k : 
  big_sum (fun x => if k =? x then f x else 0) n =
  if k <? n then f k else 0.
Proof.
  induction n; [easy|]. 
  simpl.
  rewrite IHn.
  bdestructΩ'; now rewrite ?Gplus_0_l, ?Gplus_0_r.
Qed.

Lemma big_sum_if_or_eq_ne (f : nat -> G) n k l : k <> l ->
  big_sum (fun x => if (x =? k) || (x =? l) then f x else 0) n =
  (if k <? n then f k else 0) +
  (if l <? n then f l else 0).
Proof.
  intros Hkl.
  induction n; [symmetry; apply Gplus_0_l|]. 
  simpl.
  rewrite IHn.
  bdestructΩ'; rewrite 2?Gplus_0_l, 2?Gplus_0_r; easy + apply Gplus_comm.
Qed.

Lemma if_mult (b c : bool) (u v : G) : 
  (if b then u else 0) * (if c then v else 0) =
  if b && c then u * v else 0.
Proof.
  bdestructΩ'; now rewrite ?Gmult_0_l, ?Gmult_0_r.
Qed.

End BigSumLemmas.

Lemma number_preserved_compose_cap_l_eq_1 {padl padr m} {i j} {f} 
  (Hf : bipermutation (padl + 2 + padr + m) f) 
  (Hi : i < 2 ^ m) (Hj : j < 2 ^ (padl + 0 + padr)) 
  (Hfpadl : f (m + padl) = S (m + padl)) : 
  number_preserved (j * 2 ^ m + i)
    (compose_cap_biperm_l (m + padl) f) (padl + 0 + padr + m) = 
  number_preserved
    ((j / 2 ^ padl * 4 * 2 ^ padl + j mod 2 ^ padl) * 2 ^ m + i) 
    f (padl + 2 + padr + m).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  assert (HfSpadl : f (S (m + padl)) = m + padl) by
    (rewrite <- Hfpadl, Hfeq; lia).
  
  apply eq_iff_eq_true.
  rewrite 2!number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_add_pow2_split; [|easy..].
  setoid_rewrite testbit_make_2_gap'.
  split.
  - intros H.
    intros s Hs.
    bdestruct (s <? m + padl); 
    [|
    replace_bool_lia (s <? m) false;
    replace_bool_lia (s - m <? padl) false;
    bdestruct (s - m =? padl); [|bdestruct (s - m =? S padl)]].
    + specialize (H s ltac:(lia)).
      revert H.
      bdestruct (s <? m).
      * intros ->.
        unfold compose_cap_biperm_l, compose_cap_biperm_l_prefun.
        rewrite ?(Nat.eqb_sym (m + padl)), ?(Nat.eqb_sym (S (m + padl))).
        replace_bool_lia (m + padl <=? s) false.
        replace_bool_lia (s =? S (m + padl)) false.
        replace_bool_lia (s =? m + padl) false.
        rewrite 2!(bipermutation_eqb_iff s _ Hf) by lia.
        rewrite Hfpadl, HfSpadl by lia.
        replace_bool_lia (s =? S (m + padl)) false.
        replace_bool_lia (s =? m + padl) false.
        bdestructΩ';
        try (f_equal; lia).
        assert (Hor: f s = S (m + padl) \/ f s = m + padl) by lia.
        destruct Hor as [Hor | Hor]; rewrite Hor in *;
        match goal with
        | H : f _ = _ |- _ =>
            apply (f_equal f) in H; rewrite Hfeq in H; lia
        end.
      * replace_bool_lia (s - m <? padl) true.
        unfold compose_cap_biperm_l, compose_cap_biperm_l_prefun.
        replace_bool_lia (m + padl <=? s) false.
        replace_bool_lia (S (m + padl) =? s) false.
        replace_bool_lia (s =? m + padl) false.
        rewrite <- 2!(bipermutation_eqb_iff _ s Hf) by lia.
        rewrite Hfpadl, HfSpadl by lia.
        replace_bool_lia (S (m + padl) =? s) false.
        replace_bool_lia (m + padl =? s) false.
        bdestructΩ';
        match goal with
        | _ => intros ->; f_equal; lia
        | _ => idtac
        end.
        assert (Hor: f s = S (m + padl) \/ f s = m + padl) by lia.
        destruct Hor as [Hor | Hor]; rewrite Hor in *;
        match goal with
        | H : f _ = _ |- _ =>
            apply (f_equal f) in H; rewrite Hfeq in H; lia
        end.
    + replace -> (s - m).
      replace s with (m + padl) by lia.
      rewrite Hfpadl.
      bdestructΩ'.
    + replace -> (s - m).
      replace s with (S (m + padl)) by lia.
      rewrite HfSpadl.
      bdestructΩ'.
    + replace_bool_lia (s - m <? 2 + padl) false.
      specialize (H (s - 2) ltac:(lia)).
      revert H.
      replace_bool_lia (s - 2 <? m) false.
      replace (s - 2 - m) with (s - m - 2) by lia.
      intros ->.
      unfold compose_cap_biperm_l, compose_cap_biperm_l_prefun.
      rewrite Nat.add_sub_assoc, add_sub' by lia.
      replace_bool_lia (m + padl <=? s - 2) true.
      rewrite <- 2!(bipermutation_eqb_iff _ _ Hf) by lia.
      rewrite Hfpadl, HfSpadl by lia.
      replace_bool_lia (s =? m + padl) false.
      replace_bool_lia (S (m + padl) =? s) false.
      replace_bool_lia (m + padl =? s) false.
      bdestructΩ'; try (f_equal; lia).
      assert (Hor: f s = S (m + padl) \/ f s = m + padl) by lia.
      rewrite 2!(bipermutation_eq_iff s _ Hf) in Hor by lia.
      lia.
  - intros H.
    intros s Hs.
    bdestruct (s <? m + padl); 
    [ specialize (H s ltac:(lia));
      revert H;
      bdestruct (s <? m)
    | ].
    + intros ->.
      unfold compose_cap_biperm_l, compose_cap_biperm_l_prefun.
      rewrite ?(Nat.eqb_sym (m + padl)), ?(Nat.eqb_sym (S (m + padl))).
      replace_bool_lia (m + padl <=? s) false.
      replace_bool_lia (s =? S (m + padl)) false.
      replace_bool_lia (s =? m + padl) false.
      rewrite 2!(bipermutation_eqb_iff s _ Hf) by lia.
      rewrite Hfpadl, HfSpadl by lia.
      replace_bool_lia (s =? S (m + padl)) false.
      replace_bool_lia (s =? m + padl) false.
      bdestructΩ';
      try (f_equal; lia).
      assert (Hor: f s = S (m + padl) \/ f s = m + padl) by lia.
      destruct Hor as [Hor | Hor]; rewrite Hor in *;
      match goal with
      | H : f _ = _ |- _ =>
          apply (f_equal f) in H; rewrite Hfeq in H; lia
      end.
    + replace_bool_lia (s - m <? padl) true.
      unfold compose_cap_biperm_l, compose_cap_biperm_l_prefun.
      replace_bool_lia (m + padl <=? s) false.
      replace_bool_lia (S (m + padl) =? s) false.
      replace_bool_lia (s =? m + padl) false.
      rewrite <- 2!(bipermutation_eqb_iff _ s Hf) by lia.
      rewrite Hfpadl, HfSpadl by lia.
      replace_bool_lia (S (m + padl) =? s) false.
      replace_bool_lia (m + padl =? s) false.
      bdestructΩ';
      match goal with
      | _ => intros ->; f_equal; lia
      | _ => idtac
      end.
      assert (Hor: f s = S (m + padl) \/ f s = m + padl) by lia.
      destruct Hor as [Hor | Hor]; rewrite Hor in *;
      match goal with
      | H : f _ = _ |- _ =>
          apply (f_equal f) in H; rewrite Hfeq in H; lia
      end.
    + specialize (H (s + 2) ltac:(lia)).
      revert H.
      replace_bool_lia (s <? m) false.
      replace_bool_lia (s + 2 <? m) false.
      replace_bool_lia (s + 2 - m <? padl) false.
      replace_bool_lia (s + 2 - m <? 2 + padl) false.
      replace (s + 2 - m - 2) with (s - m) by lia.
      intros ->.
      unfold compose_cap_biperm_l. 
      replace_bool_lia (m + padl <=? s) true.
      unfold compose_cap_biperm_l_prefun.
      rewrite <- 2!(bipermutation_eqb_iff _ (2 + s) Hf) by lia.
      rewrite Hfpadl, HfSpadl by lia.
      rewrite !(Nat.eqb_sym _ (2 + s)).
      replace_bool_lia (2 + s =? S (m + padl)) false.
      replace_bool_lia (2 + s =? m + padl) false.
      rewrite (Nat.add_comm 2 s).
      assert (f (s + 2) <> m + padl) by 
      (rewrite (bipermutation_eq_iff _ _ Hf), Hfpadl; lia).
      assert (f (s + 2) <> S (m + padl)) by 
      (rewrite (bipermutation_eq_iff _ _ Hf), HfSpadl; lia).
      bdestructΩ'; f_equal; lia.
Qed.

Lemma mod_div a b : a mod b / b = 0.
Proof.
  destruct b; [easy|].
  apply Nat.div_small, Nat.mod_upper_bound; easy.
Qed.

Lemma number_preserved_compose_cap_l_eq_helper {padl} {j} s :
  Nat.testbit ((j / 2 ^ padl * 4 + 3) * 2 ^ padl + j mod 2 ^ padl) s =
  if (s =? padl) || (s =? S padl) then true else
  Nat.testbit (j / 2 ^ padl * 4 * 2 ^ padl + j mod 2 ^ padl) s.
Proof.
  pose proof (fun k => Nat.pow_nonzero 2 k ltac:(easy)).
  bdestruct (s =? padl); bdestruct (s =? S padl); [lia|..]; simpl; 
  [subst..| bdestruct (s <? padl)]; rewrite !Nat.testbit_eqb.
  - rewrite Nat.add_comm, Nat.div_add by easy. 
    rewrite mod_div, Nat.add_0_l.
    change 4 with (2*2).
    rewrite Nat.mul_assoc, Nat.add_comm, Nat.Div0.mod_add.
    easy.
  - rewrite Nat.pow_succ_r by lia.
    rewrite (Nat.mul_comm 2 _), <- Nat.Div0.div_div.
    rewrite Nat.add_comm, Nat.div_add by easy.
    rewrite mod_div, Nat.add_0_l.
    change 4 with (2*2).
    rewrite Nat.mul_assoc, Nat.add_comm, Nat.div_add, Nat.Div0.mod_add;
    easy.
  - replace padl with (S (pred (padl - s)) + s) by lia.
    generalize (pred (padl - s)).
    intros p.
    rewrite Nat.add_comm, Nat.pow_add_r, Nat.mul_assoc, Nat.div_add by easy.
    rewrite Nat.pow_succ_r, (Nat.mul_comm 2 _), Nat.mul_assoc by lia.
    rewrite Nat.Div0.mod_add.
    rewrite Nat.add_comm, !Nat.mul_assoc, Nat.div_add, 
      Nat.Div0.mod_add by easy.
    easy.
  - replace s with (padl + (2 + (s - padl - 2))) by lia.
    generalize (s - padl - 2).
    intros p.
    rewrite Nat.pow_add_r, <- Nat.Div0.div_div.
    rewrite Nat.add_comm, Nat.div_add, mod_div, Nat.add_0_l by easy.
    rewrite Nat.pow_add_r, <- Nat.Div0.div_div.
    rewrite Nat.add_comm, Nat.div_add, Nat.add_0_l by easy.
    rewrite <- Nat.Div0.div_div.
    rewrite Nat.add_comm, Nat.div_add, mod_div, Nat.add_0_l by easy.
    rewrite <- Nat.Div0.div_div.
    rewrite Nat.div_mul; easy.
Qed. 

Lemma neq_iff_neq_true b c : 
  b <> c <-> (b = true <-> ~ (c = true)).
Proof.
  destruct b, c; split; easy + intros []; auto.
  discriminate H0.
  easy.
Qed.

Lemma neq_iff_impls b c : 
  b <> c <-> 
  ((b = true -> ~ (c = true)) /\
   (c = true -> ~ (b = true)) /\
   (b = false -> ~ (c = false))).
Proof.
  destruct b, c; split; easy + intros (? & ? & ?); auto.
Qed.

Lemma number_preserved_compose_cap_l_neq_parts {padl padr m} {i j} {f} 
  (Hf : bipermutation (padl + 2 + padr + m) f) 
  (Hi : i < 2 ^ m) (Hj : j < 2 ^ (padl + 0 + padr)) 
  (Hfpadl : f (m + padl) <> S (m + padl)) : 
  (number_preserved
    ((j / 2 ^ padl * 4 * 2 ^ padl + j mod 2 ^ padl) * 2 ^ m + i) 
    f (padl + 2 + padr + m) = true ->
  number_preserved
    (((j / 2 ^ padl * 4 + 3) * 2 ^ padl + j mod 2 ^ padl) * 2 ^ m + i) 
    f (padl + 2 + padr + m) = false) /\
  (number_preserved
    (((j / 2 ^ padl * 4 + 3) * 2 ^ padl + j mod 2 ^ padl) * 2 ^ m + i) 
    f (padl + 2 + padr + m) = true ->
  number_preserved
    ((j / 2 ^ padl * 4 * 2 ^ padl + j mod 2 ^ padl) * 2 ^ m + i) 
    f (padl + 2 + padr + m) = false).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  assert (HfSpadl : f (S (m + padl)) <> m + padl) by
    (intros Hfalse; rewrite <- Hfalse, Hfeq in Hfpadl; lia).
  rewrite <- 2!not_true_iff_false.
  setoid_rewrite number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_add_pow2_split; [|easy..].
  setoid_rewrite number_preserved_compose_cap_l_eq_helper.
  setoid_rewrite testbit_make_2_gap'.
  split.
  - intros H.
    intros Hfalse.
    pose proof (H (m + padl) ltac:(lia)) as Hs.
    pose proof (Hfalse (m + padl) ltac:(lia)) as Hfs.
    revert Hs Hfs.
    replace_bool_lia (m + padl <? m) false.
    rewrite add_sub'.
    replace_bool_lia (padl <? padl) false.
    replace_bool_lia (padl <? 2 + padl) true.
    rewrite Nat.eqb_refl.
    simpl.
    specialize (Hfne (m + padl) ltac:(lia)).
    bdestructΩ'; congruence.
  - intros H.
    intros Hfalse.
    pose proof (H (m + padl) ltac:(lia)) as Hs.
    pose proof (Hfalse (m + padl) ltac:(lia)) as Hfs.
    revert Hs Hfs.
    replace_bool_lia (m + padl <? m) false.
    rewrite add_sub'.
    replace_bool_lia (padl <? padl) false.
    replace_bool_lia (padl <? 2 + padl) true.
    rewrite Nat.eqb_refl.
    simpl.
    specialize (Hfne (m + padl) ltac:(lia)).
    bdestructΩ'; congruence.
Qed.

Lemma forallb_seq (f : nat -> bool) n m : 
  forallb f (seq m n) = true <->
  (forall s, s < n -> f (s + m) = true).
Proof.
  revert m;
  induction n; intros m; [easy|].
  simpl.
  rewrite andb_true_iff, IHn.
  split.
  - intros [Hm Hlt].
    intros s.
    destruct s; [easy|].
    setoid_rewrite Nat.add_succ_r in Hlt.
    intros.
    apply Hlt; lia.
  - intros Hlt; split.
    + apply (Hlt 0 ltac:(lia)).
    + intros s Hs. 
      rewrite Nat.add_succ_r.
      apply (Hlt (S s)).
      lia.
Qed.

Lemma forallb_seq0 (f : nat -> bool) n : 
  forallb f (seq 0 n) = true <->
  (forall s, s < n -> f s = true).
Proof.
  rewrite forallb_seq.
  now setoid_rewrite Nat.add_0_r.
Qed.

(* Lemma number_preserved_compose_cap_l_neq {padl padr m} {i j} {f} 
  (Hf : bipermutation (padl + 2 + padr + m) f) 
  (Hi : i < 2 ^ m) (Hj : j < 2 ^ (padl + 0 + padr)) 
  (Hpadl : padl <> 0)
  (Hfpadl : f (m + padl) <> S (m + padl)) : 
  number_preserved (j * 2 ^ m + i)
    (compose_cap_biperm_l (m + padl) f) (padl + 0 + padr + m) =
  let val := (j / 2 ^ padl * 4 * 2 ^ padl + j mod 2 ^ padl) * 2 ^ m + i in  
  forallb (fun k => 
    if k =? m + padl then true else if k =? S (m + padl) then true
    else if k =? f (m + padl) then
      eqb (Nat.testbit val (f (m + padl))) 
        (Nat.testbit val (f (S m + padl)))
    else if k =? f (S (m + padl)) then
      eqb (Nat.testbit val (f (m + padl))) 
        (Nat.testbit val (f (S m + padl)))
    else 
      eqb (Nat.testbit val k)
        (Nat.testbit val (f k))) 
        (seq 0 (padl + 2 + padr + m)).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  assert (HfSpadl : f (S (m + padl)) <> m + padl) by
    (intros Hfalse; rewrite <- Hfalse, Hfeq in Hfpadl; lia).
  apply eq_iff_eq_true.
  rewrite number_preserved_iff_all_lt_eq.
  rewrite forallb_seq0.
  setoid_rewrite testbit_add_pow2_split; [|easy..].
  setoid_rewrite testbit_make_2_gap'.
  split.
  - intros H.
    intros s Hs.
    bdestruct (s =? m + padl); [easy|].
    bdestruct (s =? S (m + padl)); [easy|].
    bdestruct (s =? f (m + padl)); [|bdestruct (s =? S (m + padl))].
    + rewrite <- eq_eqb_iff. 
      bdestruct (f (m + padl) - m <? padl); 
      [|bdestruct (f (m + padl) - m <? 2 + padl)].
      * specialize (H (f (m + padl)) ltac:(lia)).
        revert H.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? f (m + padl)) false.
        unfold compose_cap_biperm_l_prefun.
        rewrite !Hfeq by lia.
        rewrite !(Nat.eqb_sym (f (m + padl)) _).
        replace_bool_lia (S (m + padl) =? f (m + padl)) false.
        replace_bool_lia (m + padl =? f (m + padl)) false.
        replace_bool_lia (S (m + padl) =? m + padl) false.
        rewrite Nat.eqb_refl.
        simpl in *.
        (* replace_bool_lia (f (m + padl) <? m) true. *)
        specialize (Hfne (S (m + padl)) ltac:(lia)).
        bdestructΩ'; try (intros ->; f_equal; lia).
      * lia.
      * bdestructΩ'; try (f_equal; lia).
        destruct padl.
        --rewrite ?Nat.add_0_r in *.
          assert (f m = m \/)
          bdestructΩ'.
          admit.
          assert (f ())
        bdestruct (replace_bool_lia (f (m + padl) <? m) false.
        assert (Hor : f (m+padl)=m+padl \/ f (m+padl)=S(m+padl)) by lia.
        rewrite 2!(bipermutation_eq_iff _ _ Hf) in * by lia.
        
        replace (f (S (m + padl)) = S (m +padl) ) by lia.


    + specialize (H (f (m + padl)) ltac:(lia)).
      revert H.
      unfold compose_cap_biperm_l.
      replace_bool_lia (m + padl <=? f (m + padl)) false.
      unfold compose_cap_biperm_l_prefun.
      rewrite !Hfeq by lia.
      rewrite !(Nat.eqb_sym (f (m + padl)) _).
      replace_bool_lia (S (m + padl) =? f (m + padl)) false.
      replace_bool_lia (m + padl =? f (m + padl)) false.
      replace_bool_lia (S (m + padl) =? m + padl) false.
      rewrite Nat.eqb_refl.
      simpl in *.
      replace_bool_lia (f (m + padl) <? m) true.
      bdestructΩ'.
    ; [easy|].
    bdestructΩ'; rewrite <- eq_eqb_iff, ?testbit_add_pow2_split by easy.
    + specialize (H (f (m + padl)) ltac:(lia)).
      revert H.
      unfold compose_cap_biperm_l.
      replace_bool_lia (m + padl <=? f (m + padl)) false.
      unfold compose_cap_biperm_l_prefun.
      rewrite !Hfeq by lia.
      rewrite !(Nat.eqb_sym (f (m + padl)) _).
      replace_bool_lia (S (m + padl) =? f (m + padl)) false.
      replace_bool_lia (m + padl =? f (m + padl)) false.
      replace_bool_lia (S (m + padl) =? m + padl) false.
      rewrite Nat.eqb_refl.
      simpl in *.
      replace_bool_lia (f (m + padl) <? m) true.
      bdestructΩ'.
    + specialize (H (f (m + padl)) ltac:(lia)).
      revert H.
      unfold compose_cap_biperm_l.
      replace_bool_lia (m + padl <=? f (m + padl)) false.
      unfold compose_cap_biperm_l_prefun.
      rewrite !Hfeq by lia.
      rewrite !(Nat.eqb_sym (f (m + padl)) _).
      replace_bool_lia (S (m + padl) =? f (m + padl)) false.
      replace_bool_lia (m + padl =? f (m + padl)) false.
      replace_bool_lia (S (m + padl) =? m + padl) false.
      rewrite Nat.eqb_refl.
      simpl in *.
      replace_bool_lia (f (m + padl) <? m) true.
      bdestructΩ'.
    + bdestruct (s <? m); bdestruct (f s <? m).
      * specialize (H s ltac:(lia)).
        revert H.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s) false. 
        unfold compose_cap_biperm_l_prefun. 
        rewrite <-2!(bipermutation_eqb_iff _ s Hf) by lia.
        replace_bool_lia (f (S (m + padl)) =? s) false.
        replace_bool_lia (f (m + padl) =? s) false.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        bdestructΩ'.
      * 
        specialize (H (f s))
      (* assert (padl + padr + m <> 0) by lia. *)
      bdestruct (s <? m + padl); bdestruct (f s <? m + padl).
      * specialize (H s ltac:(lia)).
        revert H.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s) false. 
        unfold compose_cap_biperm_l_prefun. 
        rewrite <-2!(bipermutation_eqb_iff _ s Hf) by lia.
        replace_bool_lia (f (S (m + padl)) =? s) false.
        replace_bool_lia (f (m + padl) =? s) false.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        bdestructΩ'.
      * 
        specialize (H (f (f s + 2)) ltac:(pose (Hfbdd (f s + 2)); 
        pose (Hfbdd s); lia)).
        revert H.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s) false. 
        unfold compose_cap_biperm_l_prefun. 
        rewrite <-2!(bipermutation_eqb_iff _ s Hf) by lia.
        replace_bool_lia (f (S (m + padl)) =? s) false.
        replace_bool_lia (f (m + padl) =? s) false.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        rewrite <-2!(bipermutation_eq_iff s _ Hf) in * by lia.

        bdestructΩ'.
        
        specialize (H (f s - 2) ltac:(pose (Hfbdd s); lia)).
        revert H.
        replace_bool_lia (f s - 2 <? m) false.
        solve [bdestructΩ']
        
        rewrite 2!testbit_add_pow2_split by easy.
      (* bdestructΩ'. *)
      specialize (H (f (m + padl)) ltac:(lia)).
      revert H.
      unfold compose_cap_biperm_l.
      replace_bool_lia (m + padl <=? f (m + padl)) false.
      unfold compose_cap_biperm_l_prefun.
      rewrite !Hfeq by lia.
      rewrite !(Nat.eqb_sym (f (m + padl)) _).
      replace_bool_lia (S (m + padl) =? f (m + padl)) false.
      replace_bool_lia (m + padl =? f (m + padl)) false.
      replace_bool_lia (S (m + padl) =? m + padl) false.
      rewrite Nat.eqb_refl.
      simpl in *.
      replace_bool_lia (f (m + padl) <? m) true.
      bdestructΩ'.
      

        ++unfold compose_cap_biperm_l_prefun.
          rewrite !Hfeq by lia.
          rewrite !(Nat.eqb_sym (f (m + padl)) _).
          replace_bool_lia (S (m + padl) =? f (m + padl)) false.
          replace_bool_lia (m + padl =? f (m + padl)) false.
          replace_bool_lia (S (m + padl) =? m + padl) false.
          rewrite Nat.eqb_refl.
          simpl in *.
          replace_bool_lia (S (m + padl) <? f (S (m + padl))) false.
          bdestructΩ'.
          now rewrite eq_eqb_iff.
        ++
      ltac:(specialize (Hfbdd (m + padl) ltac:(lia)); lia)).
  do 4 setoid_rewrite orb_true_iff.
  setoid_rewrite <- eq_eqb_iff.
  setoid_rewrite Nat.eqb_eq.
  unfold 
  Forall_forallb
  setoid_rewrite testbit_add_pow2_split; [|easy..].
  setoid_rewrite testbit_make_2_gap'.
  apply forall_iff; intros s; apply impl_iff; intros Hs.
    
    

    


Lemma number_preserved_compose_cap_l_eq_12 {padl padr m} {i j} {f} 
  (Hf : bipermutation (padl + 2 + padr + m) f) 
  (Hi : i < 2 ^ m) (Hj : j < 2 ^ (padl + 0 + padr)) 
  (Hfpadl : f (m + padl) = S (m + padl)) : 
  number_preserved
    (((j / 2 ^ padl * 4 + 3) * 2 ^ padl + j mod 2 ^ padl) * 2 ^ m + i) 
    f (padl + 2 + padr + m) =
  number_preserved
    ((j / 2 ^ padl * 4 * 2 ^ padl + j mod 2 ^ padl) * 2 ^ m + i) 
    f (padl + 2 + padr + m).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  assert (HfSpadl : f (S (m + padl)) = m + padl) by
    (rewrite <- Hfpadl, Hfeq; lia).
  
  apply eq_iff_eq_true.
  rewrite 2!number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_add_pow2_split; [|easy..].
  setoid_rewrite testbit_make_2_gap'.
  apply forall_iff; intros s; apply impl_iff; intros Hs.
  bdestructΩ'.



      replace -> (s - m).
      replace s with (m + padl) by lia.
      rewrite Nat.leb_refl.
      rewrite <- 2!(bipermutation_eqb_iff _ _ Hf) by lia.
      rewrite Hfpadl, HfSpadl by lia.
      replace_bool_lia (m + padl =? 2 + (m + padl)) false.
      replace_bool_lia (S (m + padl) =? 2 + (m + padl)) false.
      (* replace_bool_lia (s =? m + padl) false.
      replace_bool_lia (S (m + padl) =? s) false.
      replace_bool_lia (m + padl =? s) false. *)
      
      bdestructΩ'.
    + replace -> (s - m).
      replace s with (S (m + padl)) by lia.
      rewrite HfSpadl.
      bdestructΩ'.
    + replace_bool_lia (s - m <? 2 + padl) false.
      specialize (H (s - 2) ltac:(lia)).
      revert H.
      replace_bool_lia (s - 2 <? m) false.
      replace (s - 2 - m) with (s - m - 2) by lia.
      intros ->.
      unfold compose_cap_biperm_l, compose_cap_biperm_l_prefun.
      rewrite Nat.add_sub_assoc, add_sub' by lia.
      replace_bool_lia (m + padl <=? s - 2) true.
      rewrite <- 2!(bipermutation_eqb_iff _ _ Hf) by lia.
      rewrite Hfpadl, HfSpadl by lia.
      replace_bool_lia (s =? m + padl) false.
      replace_bool_lia (S (m + padl) =? s) false.
      replace_bool_lia (m + padl =? s) false.
      bdestructΩ'; try (f_equal; lia).
      assert (Hor: f s = S (m + padl) \/ f s = m + padl) by lia.
      rewrite 2!(bipermutation_eq_iff s _ Hf) in Hor by lia.
      lia.
      
      replace_bool_lia (s <? 2 + padl) true.


      

      bdestruct (m + padl <=?)
      rewrite ?(Nat.eqb_sym (m + padl)), ?(Nat.eqb_sym (S (m + padl))).
      
        
        bdestructΩ'
      
        
        apply (f_equal f) in H8; rewrite Hfeq in H8; lia.
        Admitted.
        (* admit.


        try (rewrite Hfeq in *; lia).
        --rewrite Hfeq in *; lia. 
        
      revert H.
      (* assert (m + padl <> f s). *)
      unfold compose_cap_biperm_l, compose_cap_biperm_l_prefun.
      bdestructΩ'; try ((intros -> + idtac); easy + (f_equal; lia)).
      
      ); try (f_equal; lia).

    bdestruct (s <? m).
    bdestructΩ'.
    rewrite 2!(Nat.eqb_sym padl), 2!(Nat.eqb_sym (S padl)).
    bdestruct (pred (padl + 2 + padr + m) - s =? padl); 
    [|bdestruct (pred (padl + 2 + padr + m) - s =? S padl)].
    + replace s with (pred (padl + 2 + padr + m) - padl) by lia.
      replace (pred (padl + 2 + padr + m) - padl) with 
        (1 + padr + m) by lia.
      replace (pred (padl + 2 + padr + m) - S padl) with 
        (padr + m) by lia.
      rewrite 2!testbit_add_pow2_split by easy.
      bdestructΩ'.
      rewrite 2!Nat.add_sub.
      rewrite 2!Nat.testbit_eqb.
      change 4 with (2^1*2^1) at 1.
      rewrite Nat.mul_assoc, <- Nat.mul_assoc, <- Nat.pow_add_r.
      rewrite Nat.div_add by (apply Nat.pow_nonzero; easy).
      rewrite Nat.div_small by (pose proof (Nat.mod_upper_bound 
        j (2^padr) (Nat.pow_nonzero 2 _ ltac:(lia))); simpl; lia).
      rewrite Nat.div_add by (apply Nat.pow_nonzero; easy).
      rewrite (Nat.div_small (_ mod _)) by 
        (apply Nat.mod_upper_bound, Nat.pow_nonzero; easy).
      change (2^1) with 2.
      change (4) with (2*2).
      rewrite Nat.mul_assoc.
      rewrite 2!Nat.Div0.mod_add.
      easy.
    + 


        j (2^padr) (Nat.pow_nonzero 2 _ ltac:(lia))); simpl; lia).
      rewrite (Nat.div_mod j (2^(padl))) at 1 3 by *)
  

  


(* number_preserved (j * 2 ^ m + i)
    (compose_cap_biperm_l padl f) (padl + 0 + padr + m) *)

(* number_preserved
  ((j / 2 ^ padr * 4 * 2 ^ padr + j mod 2 ^ padr) * 2 ^ m + i) 
  f (padl + 2 + padr + m) *)
(* number_preserved
  (((j / 2 ^ padr * 4 + 3) * 2 ^ padr + j mod 2 ^ padr) * 2 ^ m + i) 
  f (padl + 2 + padr + m) *)

(* Goal True.
set (f := SheetElement 2 (ElemCap) 0).
let t := eval unfold f in (f) in 
let val := eval cbn in (biperm_of_zx_folio (FolioCons f (FolioNil _)))
in pose val.
pose (fun k => number_preserved k n 6) as pres.
Eval cbn in (map (fun pp => (pp, (map Nat.b2n (nat_to_binlist 6 pp), pres pp))) (seq 0 (2^6))).

Eval cbv in n. *)

Lemma matrix_of_compose_cap_biperm_l padl padr m f 
  (Hf : bipermutation (padl + 2 + padr + m) f) : 
  mat_equiv (matrix_of_biperm (padl + 0 + padr) m 
  (compose_cap_biperm_l (m + padl) f))
  (matrix_of_biperm (padl + 2 + padr) m f 
  × ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^padr))).
Proof.
  rewrite !Nat.pow_add_r.
  rewrite kron_I_l, kron_I_r.
  intros i j Hi Hj.
  unfold Mmult.
  rewrite (big_sum_eq_bounded _
  (fun k => (matrix_of_biperm (padl + 2 + padr) m f i k * if 
    (k =? (j / 2 ^ padr) * 4 * 2 ^ padr + j mod 2 ^ padr) ||
    (k =? ((j / 2 ^ padr) * 4 + 3) * 2 ^ padr + j mod 2 ^ padr)
    then C1 else 0%R)%C)).
  2: {
    intros k Hk.
    rewrite <- andb_if.
    rewrite Nat.pow_0_r, Nat.mod_1_r, Nat.div_1_r.
      (* Nat.Div0.div_div, Nat.mul_comm, <- Nat.Div0.div_div. *)
    rewrite cap_semantics.
    rewrite Nat.eqb_refl.
    rewrite <- orb_if, <- andb_if.
    f_equal.
    apply f_equal_if; [|easy..].
    rewrite <- andb_assoc, 2!andb_orb_distrib_r.
    f_equal.
    - apply eq_iff_eq_true.
      rewrite !andb_true_iff, !Nat.eqb_eq.
      split.
      + intros (Hmodpadr & Hlow & Hmid).
        rewrite (Nat.div_mod k (2^padr)) by (apply Nat.pow_nonzero; easy).
        f_equal; [|easy].
        rewrite <- Hlow.
        change 4 with (2^2).
        rewrite div_mul_not_exact by easy.
        lia.
      + intros ->.
        repeat split.
        * now rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.Div0.mod_mod.
        * rewrite Nat.add_comm, Nat.div_add, (Nat.div_small (_ mod _)) 
          by (try apply Nat.mod_upper_bound; apply Nat.pow_nonzero; easy).
          rewrite Nat.add_0_l.
          now rewrite Nat.div_mul by easy.
        * rewrite Nat.add_comm, Nat.div_add by (now apply Nat.pow_nonzero).
          rewrite Nat.Div0.mod_add.
          now rewrite Nat.div_small 
            by (apply Nat.mod_upper_bound, Nat.pow_nonzero; easy).
    - apply eq_iff_eq_true.
      rewrite !andb_true_iff, !Nat.eqb_eq.
      split.
      + intros (Hmodpadr & Hlow & Hmid).
        rewrite (Nat.div_mod k (2^padr)) by (apply Nat.pow_nonzero; easy).
        f_equal; [|easy].
        rewrite Nat.mul_comm.
        f_equal.
        rewrite (Nat.div_mod (k / 2 ^ padr) (2^2) ltac:(easy)).
        rewrite Nat.mul_comm.
        f_equal; [f_equal; easy| easy].
      + intros ->.
        repeat split.
        * now rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.Div0.mod_mod.
        * rewrite Nat.add_comm, Nat.div_add, (Nat.div_small (_ mod _)) 
          by (try apply Nat.mod_upper_bound; apply Nat.pow_nonzero; easy).
          rewrite Nat.add_0_l, Nat.add_comm, Nat.div_add by easy.
          easy.
        * rewrite Nat.add_comm, Nat.div_add by (now apply Nat.pow_nonzero).
          rewrite (Nat.add_comm _ 3), Nat.add_assoc, Nat.Div0.mod_add.
          now rewrite Nat.div_small 
            by (apply Nat.mod_upper_bound, Nat.pow_nonzero; easy).
  }
  unfold matrix_of_biperm.
  erewrite big_sum_eq_bounded.
  2: {
    intros k Hk.
    rewrite (if_mult (H2:=C_is_ring)).
    rewrite Cmult_1_l.
    rewrite andb_comm, andb_if.
    (* change (if number_preserved (k * 2 ^ m + i) f (padl + 2 + padr + m)
    then C1 else 0%G) 
    with (id (fun x => if number_preserved (x * 2 ^ m + i) f 
    (padl + 2 + padr + m) then C1 else 0%G) k). *)
    reflexivity.
  }
  rewrite big_sum_if_or_eq_ne by lia.
  rewrite 2!big_sum_if_eq. (id (fun x : nat =>
    if number_preserved (x * 2 ^ m + i) f
    (padl + 2 + padr + m) then C1
    else 0%G)) ((2 ^ padl * 2 ^ 2 * 2 ^ padr))).



        Search ((_ / _) * _).
    Search ( (if _ then _ else _) = (if _ then _ else _)).
    replace 
    Search (if _ then (if _ then _ else _) else _).
    rewrite 
  }
  erewrite Mmult_proper.
  2: reflexivity.
  2: {
    eapply kron_proper.
    apply kron_I_l.
  }

  (* change Nat.mul with Init.Nat.mul. 2 (_ + 2)). *)
  rewrite kron_I_r.
  setoid_rewrite kron_I_l.
  pose proof (kron_I_r (p:=2^padr) (⟦⊂⟧)).
  (* rewrite <-  *)
  (* change (2^0) with 1 in *.
  rewrite Nat.mul_1_l in H. *)

  (* rewrite Nat.add_0_r. *)
  restore_dims.
  rewrite H.
  rewrite kron_I_r.
  unfold matrix_of_biperm.
  unfold compose_cap_biperm_l.
  compose_cup_biperm_l
  unfold number_preserved.


Lemma number_preserved_compose_cap_l_flipped {padl padr m} {i j} {f} 
  (Hf : bipermutation (padl + 2 + padr + m) f) 
  (Hi : i < 2 ^ m) (Hj : j < 2 ^ (padl + 0 + padr)) :
  number_preserved (j * 2 ^ m + i)
    (flip_biperm (compose_cap_biperm_l padl f) (padl + 0 + padr + m)) 
    (padl + 0 + padr + m) = 
  number_preserved (((j mod 2^padr) + (j/2^padr)*4 * (2^padr)) * 2 ^ m + i)
    (flip_biperm (compose_cap_biperm_l_prefun padl f) (padl + 2 + padr + m)) 
    (padl + 2 + padr + m).
Proof.
  apply eq_iff_eq_true.
  rewrite 2!number_preserved_iff_all_lt_eq.
  split.
  - intros H.
    intros s Hs.

    rewrite 2!testbit_add_pow2_split by easy.
    bdestruct (s <? m).
    unfold compose_cap_biperm_l_prefun.
    bdestructΩ'.
    rewrite 2!(Nat.eqb_sym padl), 2!(Nat.eqb_sym (S padl)).
    bdestruct (pred (padl + 2 + padr + m) - s =? padl); 
    [|bdestruct (pred (padl + 2 + padr + m) - s =? S padl)].
    + replace s with (pred (padl + 2 + padr + m) - padl) by lia.
      replace (pred (padl + 2 + padr + m) - padl) with 
        (1 + padr + m) by lia.
      replace (pred (padl + 2 + padr + m) - S padl) with 
        (padr + m) by lia.
      rewrite 2!testbit_add_pow2_split by easy.
      bdestructΩ'.
      rewrite 2!Nat.add_sub.
      rewrite 2!Nat.testbit_eqb.
      change 4 with (2^1*2^1) at 1.
      rewrite Nat.mul_assoc, <- Nat.mul_assoc, <- Nat.pow_add_r.
      rewrite Nat.div_add by (apply Nat.pow_nonzero; easy).
      rewrite Nat.div_small by (pose proof (Nat.mod_upper_bound 
        j (2^padr) (Nat.pow_nonzero 2 _ ltac:(lia))); simpl; lia).
      rewrite Nat.div_add by (apply Nat.pow_nonzero; easy).
      rewrite (Nat.div_small (_ mod _)) by 
        (apply Nat.mod_upper_bound, Nat.pow_nonzero; easy).
      change (2^1) with 2.
      change (4) with (2*2).
      rewrite Nat.mul_assoc.
      rewrite 2!Nat.Div0.mod_add.
      easy.
    + 


        j (2^padr) (Nat.pow_nonzero 2 _ ltac:(lia))); simpl; lia).
      rewrite (Nat.div_mod j (2^(padl))) at 1 3 by
        (apply Nat.pow_nonzero; easy).
      rewrite (Nat.mul_comm (2^_)), (Nat.add_comm (_*(2^_))), Nat.div_add by
        (apply Nat.pow_nonzero; easy).
      rewrite (Nat.div_small (_ mod _)) by 
        (apply Nat.mod_upper_bound, Nat.pow_nonzero; easy).
      rewrite Nat.div_add
    
    replace s with (pred (padl + 2 + padr + m) - 
      (pred (padl + 2 + padr + m) - s)) at 1 by lia.
    assert (Hsubs : pred (padl + 2 + padr + m) - s 
      < padl + 2 + padr + m) by lia.
    revert Hsubs.
    generalize (pred (padl + 2 + padr + m) - s) as a.
    clear s Hs.
    intros s Hs.
    

    unfold compose_cap_biperm_l_prefun.
    rewrite 2!(Nat.eqb_sym _ s).
    bdestructΩ'.

  unfold compose_cap_biperm_l, compose_cap_biperm_l_prefun.
  split; [admit|intros].
  bdestruct (padl <=? s).



  (* if f padl =? S padl then 
  number_preserved ((4 * j/(2^padr) ) * 2^m + i)
    f (padl + 2 + padr + m). *)

  

Lemma matrix_of_compose_cap_biperm_l padl padr m f 
  (Hf : bipermutation (padl + 2 + padr + m) f) : 
  mat_equiv (matrix_of_biperm (padl + 0 + padr) m 
  (compose_cap_biperm_l padl f))
  (matrix_of_biperm (padl + 2 + padr) m f × (I (2^padl) ⊗ ⟦⊃⟧ ⊗ I (2^padr))).
Proof.
  intros i j Hi Hj.
  simpl.
  unfold matrix_of_biperm.
  unfold compose_cap_biperm_l.

  

Lemma biperm_of_zxbiperm_folio_bipermutation_semantics_correct 
  {n m} {zx : ZX_folio n m} (H : ZXbiperm_folio zx) :
  exists c : C, 
  mat_equiv (matrix_of_zx_folio_biperm zx) (c .* ⟦ zx_of_folio zx ⟧) 
  /\ c <> 0%R.
Proof.
  unfold matrix_of_zx_folio_biperm.
  induction H.
  - simpl.
    rewrite n_wire_semantics.
    prop_exists_nonzero R1.
    rewrite Mscale_1_l.
    intros i j Hi Hj.
    unfold matrix_of_biperm, I.
    rewrite number_preserved_idn by easy.
    bdestructΩ'.
  - induction Hzx as [n m padl zx Hzx padr].
    induction Hzx.
    + simpl. 
      rewrite kron_1_r, 2!n_wire_semantics.
      revert fs H IHZXbiperm_folio. 
      rewrite (Nat.add_0_r padl).
      rewrite id_kron.
      rewrite <- Nat.pow_add_r.
      intros.
      rewrite Mmult_1_r by auto with wf_db.
      easy.
    + simpl.
      rewrite  
      revert fs H IHZXbiperm_folio. 
      rewrite Nat.add_0_r.
    destruct zx as [n m padl zx padr].
    simpl.
    destruct zx; simpl in Hzx. try .

    

  bipermutation (n + m) (biperm_of_zx_folio zx).


try apply cap_cup_rel_biperm.
  - intros k Hk.
    repeat (destruct k; try lia); cbn; lia.
  - apply stack_biperms_bipermutation; assumption.
  - apply compose_biperms_bipermutation; assumption.
Qed.


Lemma zx_folio_rect (P : forall n m, ZX_folio n m -> Type)
  (Pnil : forall n, P (FolioNil n)) 

Lemma zx_foliate_rect

  simpl.

  Search (⦰ ↕ _).
  . [reflexivity|..].

Definition biperm_of_zx {n m} {zx : ZX n m} 


Inductive ZXbiperm_elem : forall (n m : nat), Set :=
  | ElemEmpty : ZXbiperm_elem 0 0
  | ElemCap : ZXbiperm_elem 0 2 (* FIXME: Fix for cap-cup switch*)
  | ElemCup : ZXbiperm_elem 2 0
  | ElemSwap : ZXbiperm_elem 2 2
  | ElemWire : ZXbiperm_elem 1 1.

(* Inductive ZXbiperm_stack : forall (n m : nat), Set :=
  | StackNil : ZXbiperm_stack O O
  | StackCons {n m ns ms : nat} {zx : ZX n m} (H : ZXbiperm_elem zx) 
    (st : ZXbiperm_stack ns ms) : ZXbiperm_stack (n + ns) (m + ms). *)

Inductive ZXbiperm_sheet : forall (n m : nat), Set :=
  | SheetElement {n m} (padl : nat)
    (zx : ZXbiperm_elem n m) (padr : nat) : 
    ZXbiperm_sheet (padl + n + padr) (padl + m + padr).

Inductive ZXbiperm_folio : forall (n m : nat), Set :=
  | FolioNil (n : nat) : ZXbiperm_folio n n
  | FolioCons {n m o} (st : ZXbiperm_sheet n m) 
    (fs : ZXbiperm_folio m o) : ZXbiperm_folio n o.

Definition zx_of_biperm_elem {n m} (zx : ZXbiperm_elem n m) : ZX n m :=
  match zx with
  | ElemEmpty => Empty
  | ElemCap => Cap
  | ElemCup => Cup
  | ElemSwap => Swap
  | ElemWire => Wire
  end.

Definition zx_of_biperm_sheet {n m} (zx : ZXbiperm_sheet n m) : ZX n m :=
  match zx with
  | SheetElement padl elem_zx padr =>
    n_wire padl ↕ zx_of_biperm_elem elem_zx ↕ n_wire padr
  end.

Fixpoint zx_of_biperm_folio {n m} (zxs : ZXbiperm_folio n m) : ZX n m :=
  match zxs with
  | FolioNil n => n_wire n
  | FolioCons st fs => zx_of_biperm_sheet st ⟷ zx_of_biperm_folio fs
  end.

Definition compose_zx_folio {n m o} (fs : ZXbiperm_folio n m) 

Fixpoint ZXbiperm_folio_of_zx

Definition biperm_of_zx {n m} {zx : ZX n m} 


(* NEW TESTS, post inversion *)

Definition matrix_of_zx_folio {n m : nat} (zx : ZX_folio n m) : 
  Matrix (2^m) (2^n) :=
  matrix_of_biperm n m (biperm_of_zx_folio zx).

Definition matrix_of_zx_biperm_by_folio {n m : nat} (zx : ZX n m) : 
  Matrix (2^m) (2^n) :=
  matrix_of_biperm n m (biperm_of_zx_folio (ZX_folio_of_zx zx)).

(* Definition matrix_of_zx_biperm {n m : nat} (zx : ZX n m) : Matrix (2^m) (2^n) :=
  matrix_of_biperm n m (biperm_of_zx zx). *)

Ltac by_cell_nosimpl :=
  intros i j Hi Hj; try solve_end;
  repeat
  (destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
    try solve_end); clear Hi;
  repeat
  (destruct j as [| j]; [  | apply <- Nat.succ_lt_mono in Hj ];
    try solve_end); clear Hj.

Ltac by_cell_Csimpl :=
  intros i j Hi Hj; try solve_end;
  repeat
  (destruct i as [| i]; simpl; Csimpl; [  | apply <- Nat.succ_lt_mono in Hi ];
    try solve_end); clear Hi;
  repeat
  (destruct j as [| j]; simpl; Csimpl; [  | apply <- Nat.succ_lt_mono in Hj ];
    try solve_end); clear Hj.

Notation zxbiperm_correct zx := 
  (mat_equiv (⟦ zx ⟧) (matrix_of_zx_biperm_by_folio zx)).

Goal zxbiperm_correct —.
by_cell_nosimpl. 
all: cbn. 
all: lca.
Qed.

Goal zxbiperm_correct (— ⟷ —).
by_cell_nosimpl.
all: cbn.
all: lca.
Qed.

Goal zxbiperm_correct ⨉.
by_cell_nosimpl.
all: cbn.
all: reflexivity.
Qed.

Goal zxbiperm_correct (⨉ ⟷ ⨉).
by_cell_nosimpl.
all: cbn.
all: lca.
Qed.

Goal zxbiperm_correct (⨉ ⟷ (— ↕ —)).
unfold matrix_of_zx_biperm_by_folio; cbn; 
  rewrite ?cast_zx_sheet_id; cbn.
by_cell_nosimpl.
all: cbn.
all: lca.
Qed.

Goal zxbiperm_correct ((⨉ ↕ —) ⟷ (— ↕ ⨉)).
unfold matrix_of_zx_biperm_by_folio; cbn; 
  rewrite ?cast_zx_sheet_id; cbn.
(* unfold kron, I, swap, Mmult. *)
by_cell_nosimpl.
all: cbn.
all: lca. 
Qed.

Goal zxbiperm_correct ((⊃ ↕ —) ⟷ (— ↕ ⊂)).
(* Admitted. for performance *)
cbn.
unfold kron, Mmult, big_sum.
intros i j Hi Hj.
rewrite Cplus_0_l.
unfold I.
rewrite !Nat.mod_1_r, !Nat.div_1_r.
simpl (1 mod 2).
change (1 <? 2) with true.
simpl (1 / 2).
simpl (0 / 2).
simpl (0 mod 2).
change (0 <? 2) with true.
(* revert i j Hi Hj. *)

(* by_cell_nosimpl. *)
unfold matrix_of_zx_biperm_by_folio; cbn; 
rewrite ?cast_zx_sheet_id; cbn.
repeat (destruct i; try lia);
simpl;
Csimpl;
repeat (destruct j; try lia);
simpl; 
Csimpl; reflexivity.
(* simpl. *)
(* revert i j Hi Hj. *)
(* by_cell_nosimpl.
all: cbn.
all: lca.  *)
Qed.

Goal zxbiperm_correct ((— ↕ ⊂) ⟷ (⊃ ↕ —)).
cbn.
unfold kron.
unfold matrix_of_zx_biperm_by_folio; cbn; 
rewrite ?cast_zx_sheet_id; cbn.
by_cell_nosimpl.
all: cbn.
all: lca. 
Qed.

(* Goal zxbiperm_correct ((— ↕ ⊂) ⟷ (— ↕ ⨉) ⟷ (⊃ ↕ —)).
cbn.
unfold kron.
unfold matrix_of_zx_biperm_by_folio; cbn; 
rewrite ?cast_zx_sheet_id; cbn.
by_cell_nosimpl.
all: cbn.
all: lca. 
Qed. *)

Goal zxbiperm_correct ((— ↕ ⊂ ↕ ⊂) 
  ⟷ (⊃ ↕ ⊃ ↕ —)).
Proof.
  Admitted. (* for performance *)
  (* cbn.
  unfold kron.
  unfold Mmult, I, list2D_to_matrix.
  by_cell_nosimpl.
  all: cbn.
  all: lca. *)
(* Qed. *)

Goal zxbiperm_correct ((— ↕ ⊂) ⟷
  (⨉ ↕ —) ⟷
  (⊃ ↕ —)).
Proof.
  Admitted. (* for performance *)
  (* cbn.
  unfold kron.
  unfold Mmult.
  by_cell_nosimpl.
  all: cbn.
  all: lca. *)
(* Qed. *)



(* HYPOTHESIS: for semantics, A[i,j] = 1 if the bits are preserved by 
   the bipermutation. Ok, what does that mean? (i,j) should have n + m 
   bits, and we then simply check if bit k equals bit f k for all k. *)
(* CORRECTION: The above is *mostly* correct; the actual equation differs
   is A[i,j] = 2^k if [same] and 0 otherwise, where k is the number of 
   closed loops *)

Definition number_preserved (i : nat) (f : nat -> nat) (bound : nat) :=
  forallb (fun k => eqb (Nat.testbit i k) (Nat.testbit i (f k))) (seq 0 bound).

Definition matrix_of_biperm (n m : nat) (f : nat -> nat) : Matrix (2^m) (2^n) :=
  fun i j =>
  if number_preserved (j * 2^m + i) f (n + m) then C1 else C0.
                      (* this order works experimentally... :/ *)

Fixpoint biperm_of_zx {n m} (zx : ZX n m) : nat -> nat :=
  match zx with
  | ⦰ => fun k => k
  | ⊂ => fun k => cap_cup_rel k
  | ⊃ => fun k => cap_cup_rel k
  | ⨉ => fun k =>
    if 4 <=? k then k else
    if k =? 0 then 3 else if k =? 1 then 2 else
    if k =? 2 then 1 else if k =? 3 then 0 else k (* <- this clause is redundant *)
  | — => fun k => cap_cup_rel k
  | □ => idn
  | X_Spider n m _ => idn
  | Z_Spider n m _ => idn
  | @Stack n0 m0 n1 m1 zx0 zx1 => 
    stack_biperms n0 m0 n1 m1 (biperm_of_zx zx0) (biperm_of_zx zx1)
  | @Compose n m o zx0 zx1 =>
    compose_biperms n m o (biperm_of_zx zx0) (biperm_of_zx zx1)
  end.

Inductive ZXbiperm : forall {n m} (zx : ZX n m), Prop :=
  | BipermEmpty : ZXbiperm ⦰
  | BipermCap : ZXbiperm ⊂
  | BipermCup : ZXbiperm ⊃
  | BipermSwap : ZXbiperm ⨉
  | BipermWire : ZXbiperm —
  | BipermStack {n0 m0 n1 m1} {zx0 : ZX n0 m0} {zx1 : ZX n1 m1} : 
    ZXbiperm zx0 -> ZXbiperm zx1 -> ZXbiperm (zx0 ↕ zx1)
  | BipermCompose {n m o} {zx0 : ZX n m} {zx1 : ZX m o} :
    ZXbiperm zx0 -> ZXbiperm zx1 -> ZXbiperm (zx0 ⟷ zx1). 

Lemma compose_biperms_bipermutation {n m o} {f g : nat -> nat}
  (Hf : bipermutation (n + m) f) (Hg : bipermutation (m + o) g) : 
  bipermutation (n + o) (compose_biperms n m o f g).
Admitted.

Lemma biperm_of_zxbiperm_bipermutation {n m} {zx : ZX n m} (H : ZXbiperm zx) :
  bipermutation (n + m) (biperm_of_zx zx).
Proof.
  induction H; [easy|..]; try apply cap_cup_rel_biperm.
  - intros k Hk.
    repeat (destruct k; try lia); cbn; lia.
  - apply stack_biperms_bipermutation; assumption.
  - apply compose_biperms_bipermutation; assumption.
Qed.


Section SemanticsLemmas.

Open Scope R_scope.

Lemma zxbiperm_semantics_real {n m} {zx : ZX n m}
  (H : ZXbiperm zx) (i j : nat) : 
  snd (⟦ zx ⟧ i j) = 0.
Proof.
  revert i j.
  induction H; intros i j; simpl; try lra.
  - unfold I; bdestructΩ'; simpl; lra.
  - destruct i; [|destruct i; [|destruct i; [|destruct i; [|destruct i]]]]; 
    (destruct j; [|destruct j]); cbn; lra.
  - destruct j; [|destruct j; [|destruct j; [|destruct j; [|destruct j]]]]; 
    (destruct i; [|destruct i]); cbn; lra.
  - unfold swap.
    destruct i; [|destruct i; [|destruct i; [|destruct i; [|destruct i]]]]; cbn;
    repeat (destruct j; cbn; try lra).
  - unfold I; bdestructΩ'; simpl; lra.
  - rewrite IHZXbiperm1, IHZXbiperm2; lra.
  - unfold Mmult.
    apply big_sum_snd_0.
    intros ?.
    cbn.
    rewrite IHZXbiperm1, IHZXbiperm2; lra.
Qed.

Lemma zxbiperm_semantics_nonneg {n m} {zx : ZX n m}
  (H : ZXbiperm zx) (i j : nat) : 
  0 <= (fst (⟦ zx ⟧ i j)).
Proof.
  revert i j.
  induction H; intros i j; simpl; try lra.
  - unfold I; bdestructΩ'; simpl; lra.
  - destruct i; [|destruct i; [|destruct i; [|destruct i; [|destruct i]]]]; 
    (destruct j; [|destruct j]); cbn; lra.
  - destruct j; [|destruct j; [|destruct j; [|destruct j; [|destruct j]]]]; 
    (destruct i; [|destruct i]); cbn; lra.
  - unfold swap.
    destruct i; [|destruct i; [|destruct i; [|destruct i; [|destruct i]]]]; cbn;
    repeat (destruct j; cbn; try lra).
  - unfold I; bdestructΩ'; simpl; lra.
  - rewrite !zxbiperm_semantics_real by easy.
    rewrite Rmult_0_l, Rminus_0_r.
    apply Rmult_le_pos; auto.
  - apply big_sum_ge_0.
    intros x.
    cbn.
    rewrite !zxbiperm_semantics_real by easy.
    rewrite Rmult_0_l, Rminus_0_r.
    apply Rmult_le_pos; auto.
Qed.

Lemma Re_big_sum (n : nat) (f : nat -> C) : 
  fst (Σ (fun i => f i) n) = big_sum (fun i => fst (f i)) n.
Proof.
  induction n; [easy|].
  simpl; f_equal; easy.
Qed. 

Lemma Im_big_sum (n : nat) (f : nat -> C) : 
  snd (Σ (fun i => f i) n) = big_sum (fun i => snd (f i)) n.
Proof.
  induction n; [easy|].
  simpl; f_equal; easy.
Qed. 

Lemma big_sum_ge_0_on (n : nat) (f : nat -> R) : 
  (forall k, (k < n)%nat -> 0 <= f k) ->
  0 <= big_sum f n.
Proof.
  induction n; [simpl; lra|].
  intros Hf.
  specialize (IHn ltac:(intros;apply Hf;lia)).
  simpl.
  specialize (Hf n ltac:(lia)).
  lra.
Qed.

Lemma nonneg_big_sum_le (n : nat) (f : nat -> R) a : 
  (forall k, (k < n)%nat -> 0 <= f k) ->
  big_sum f n <= a ->
  forall k, (k < n)%nat -> f k <= a.
Proof.
  intros Hfge0 Hle.
  induction n; [easy|].
  specialize (IHn ltac:(intros; apply Hfge0; lia)
    ltac:(simpl in Hle; specialize (Hfge0 n ltac:(lia)); lra)).
  simpl in Hle.
  pose proof (big_sum_ge_0_on n f ltac:(intros; apply Hfge0; lia)).
  intros k Hk.
  bdestruct (k =? n).
  - subst; lra.
  - apply IHn; lia.
Qed.

Lemma unitary_conj_trans_real {n} {A : Matrix n n} (HA : WF_Unitary A) i j :
  snd ((A †%M × A) i j) = 0.
Proof.
  destruct HA as [_ Heq].
  apply (f_equal_inv i) in Heq.
  apply (f_equal_inv j) in Heq.
  rewrite Heq.
  unfold I.
  bdestructΩ'.
Qed.

Lemma Re_Cpow (c : C) (Hc : snd c = 0) n : 
  fst (Cpow c n) = pow (fst c) n.
Proof.
  induction n; [easy|].
  simpl; rewrite Hc, IHn.
  lra.
Qed.

Lemma Cmult_conj_nonneg (c : C) : 
  0 <= fst (c ^* * c)%C.
Proof.
  rewrite <- Cmod_sqr, Re_Cpow by easy.
  apply pow2_ge_0.
Qed.

Lemma unitary_conj_trans_nonneg {n} {A : Matrix n n} 
  (HA : WF_Unitary A) i j :
  0 <= fst ((A †%M × A) i j).
Proof.
  rewrite (proj2 HA).
  unfold I; bdestructΩ'; simpl; lra.
Qed.

Lemma nonneg_big_sum_ge_any n (f : nat -> R) k (Hk : (k < n)%nat) : 
  (forall i, (i < n)%nat -> 0 <= f i) ->
  f k <= big_sum f n.
Proof.
  intros Hle.
  induction n; [easy|].
  bdestruct (k =? n).
  - subst.
    simpl.
    pose proof (big_sum_ge_0_on n f ltac:(intros;apply Hle;lia)).
    lra.
  - pose proof (Hle n ltac:(lia)).
    simpl.
    apply Rle_trans with (big_sum f n).
    + apply IHn; [lia | intros; apply Hle; lia].
    + lra.
Qed.

Lemma big_sum_real n (f : nat -> C)
  (Hf : forall i, (i < n)%nat -> snd (f i) = 0) :
  Σ f n = big_sum (fun i => fst (f i)) n.
Proof.
  rewrite (big_sum_eq_bounded _ (fun i => RtoC (fst (f i)))).
  - apply c_proj_eq.
    + rewrite Rsum_big_sum; easy.
    + rewrite Im_big_sum.
      simpl.
      clear Hf.
      induction n; [easy|].
      simpl; lra.
  - intros i Hi.
    apply c_proj_eq; [easy|]. 
    apply Hf; easy.
Qed.

Lemma Cmod_real_nonneg_sum_ge_any n (f : nat -> C) k (Hk : (k < n)%nat) 
  (Hf_re : forall i, (i < n)%nat -> snd (f i) = 0) 
  (Hf_nonneg : forall i, (i < n)%nat -> 0 <= fst (f i)):
  Cmod (f k) <= Cmod (big_sum (fun i => f i) n).
Proof.
  rewrite big_sum_real by easy.
  rewrite 2!Cmod_real; try apply Hf_re; 
  try apply Rle_ge;
  try apply (Hf_nonneg k Hk); try easy.
  - simpl.
    apply (nonneg_big_sum_ge_any n (fun i => fst (f i))); easy.
  - apply big_sum_ge_0_on.
    easy.
Qed.

Lemma Rmult_le_impl_le_disj_nonneg (x y z w : R) 
  (Hz : 0 <= z) (Hw : 0 <= w) : 
  x * y <= z * w -> x <= z \/ y <= w.
Proof.
  destruct (Rle_or_lt x z), (Rle_or_lt y w); 
  [left + right; easy..|].
  assert (Hx : 0 < x) by lra.
  assert (Hy : 0 < y) by lra.
  intros Hfasle.
  destruct Hz, Hw; enough (z * w < x * y) by lra;
  [|subst; rewrite ?Rmult_0_l, ?Rmult_0_r; 
    apply Rmult_lt_0_compat; easy..].
  pose proof (Rmult_lt_compat_r w z x) as Ht1.
  pose proof (Rmult_lt_compat_l x w y) as Ht2.
  lra.
Qed.

Lemma Rle_pow_le_nonneg (x y : R) (Hx : 0 <= x) (Hy : 0 <= y) n :
  x ^ (S n) <= y ^ (S n) -> x <= y.
Proof.
  induction n; [rewrite !pow_1; easy|].
  change (?z ^ S ?m) with (z * z ^ m).
  intros H.
  apply Rmult_le_impl_le_disj_nonneg in H; 
  [|easy|apply pow_le; easy].
  destruct H; auto.
Qed.

Lemma Cmod_ge_0 (c : C) : 0 <= Cmod c.
Proof.
  apply sqrt_pos.
Qed.

Lemma R1_eq_1 : R1 = 1.
Proof. easy. Qed.

Lemma sqrt_eq_iff_eq_sqr (r s : R) (Hs : 0 < s) : 
  sqrt r = s <-> r = pow s 2.
Proof.
  split.
  - destruct (Rcase_abs r) as [Hr | Hr];
    [rewrite sqrt_neg_0; lra|].
    intros H.
    apply (f_equal (fun i => pow i 2)) in H.
    rewrite pow2_sqrt in H; lra.
  - intros ->.
    rewrite sqrt_pow2; lra.
Qed.

Lemma sqrt_eq_1_iff_eq_1 (r : R) :
  sqrt r = 1 <-> r = 1.
Proof.
  rewrite sqrt_eq_iff_eq_sqr by lra.
  now rewrite pow1.
Qed.

Lemma subnormal_matrix_le_1 {n m : nat} (A : Matrix n m) {i j} 
  (Hi : (i < n)%nat) (Hj : (j < m)%nat) 
  (Hnorm : forall i, (i < m)%nat -> norm (get_vec i A) <= 1) :
  Cmod (A i j) <= 1.
Proof.
  apply Rle_pow_le_nonneg with 1%nat; try lra; [apply Cmod_ge_0|].
  rewrite pow1.
  specialize (Hnorm j Hj).
  revert Hnorm.
  unfold get_vec, norm, inner_product. 
  autounfold with U_db.
  rewrite Nat.eqb_refl. 
  rewrite (big_sum_eq_bounded _ (fun k => RtoC (Cmod (A k j) ^ 2)))
  by (intros; rewrite <- Cmod_sqr, RtoC_pow; easy).
  rewrite Rsum_big_sum.
  intros H.
  rewrite <- sqrt_1 in H.
  apply sqrt_le_0 in H; 
  [|apply big_sum_ge_0_on;intros;apply pow2_ge_0|lra].
  refine (Rle_trans _ _ _ _ H).
  apply (nonneg_big_sum_ge_any n (fun k => Cmod (A k j) ^ 2) i); [easy|].
  intros; apply pow2_ge_0.
Qed.

Lemma normal_matrix_le_1 {n m : nat} (A : Matrix n m) {i j} 
  (Hi : (i < n)%nat) (Hj : (j < m)%nat) 
  (Hnorm : forall i, (i < m)%nat -> norm (get_vec i A) = 1) :
  Cmod (A i j) <= 1.
Proof.
  apply subnormal_matrix_le_1; [easy..|].
  intros.
  rewrite Hnorm; easy + lra.
Qed.

Require QuantumLib.Eigenvectors.

Lemma unitary_abs_le_1 {n} {A : Matrix n n} (HA: WF_Unitary A) :
  forall i j, 
  Cmod (A i j) <= 1.
Proof.
  intros i j.
  bdestruct (i <? n); bdestruct (j <? n); 
  [|rewrite (proj1 HA); [rewrite ?Cmod_0; lra | auto]..].
  apply normal_matrix_le_1; [easy..|].
  apply (proj1 (Eigenvectors.unit_is_orthonormal A) HA).
Qed.

Definition is_integral (r : C) : Prop := exists k, r = INR k.

Definition is_integral_matrix {n m} (A : Matrix n m) : Prop :=
  forall i j, (i < n)%nat -> (j < m)%nat ->
  is_integral (A i j).

Lemma is_integral_plus {r s : C} : is_integral r -> is_integral s ->
  is_integral (r + s).
Proof.
  intros [nr Hnr] [ns Hns].
  exists (Nat.add nr ns).
  rewrite plus_INR, RtoC_plus; f_equal; easy.
Qed.

Lemma is_integral_mult {r s : C} : is_integral r -> is_integral s ->
  is_integral (r * s).
Proof.
  intros [nr Hnr] [ns Hns].
  exists (Nat.mul nr ns).
  rewrite mult_INR, RtoC_mult; f_equal; easy.
Qed.

Lemma is_integral_big_sum n (f : nat -> C) 
  (Hf : forall i, (i < n)%nat -> is_integral (f i)) :
  is_integral (Σ f n).
Proof.
  induction n; [exists O; easy|].
  simpl.
  specialize (IHn ltac:(intros; apply Hf; lia)).
  specialize (Hf n ltac:(lia)).
  apply is_integral_plus; easy.
Qed.

Lemma Mmult_integral_matrix {n m o} {A : Matrix n m} {B : Matrix m o} 
  (HA : is_integral_matrix A) (HB : is_integral_matrix B) : 
  is_integral_matrix (A × B).
Proof.
  intros i j Hi Hj.
  apply is_integral_big_sum.
  intros k Hk.
  apply is_integral_mult; auto.
Qed.

Lemma kron_integral_matrix {n m o p} {A : Matrix n m} {B : Matrix o p} 
  (HA : is_integral_matrix A) (HB : is_integral_matrix B) :
  is_integral_matrix (A ⊗ B).
Proof.
  intros i j Hi Hj.
  unfold kron.
  apply is_integral_mult.
  - apply HA;
    apply Nat.div_lt_upper_bound; 
    lia.
  - apply HB;
    apply Nat.mod_upper_bound; 
    lia.
Qed.

Lemma is_integral_0 : is_integral 0.
Proof. exists O; easy. Qed.

Lemma is_integral_C1 : is_integral C1.
Proof. exists (S O); easy. Qed.

Lemma zxbiperm_integral_matrix {n m} {zx : ZX n m} (H : ZXbiperm zx) :
  is_integral_matrix (⟦ zx ⟧).
Proof.
  induction H.
  6: rewrite 2Nat.pow_add_r; apply kron_integral_matrix; easy.
  6: apply Mmult_integral_matrix; easy.
  all: by_cell; first [apply is_integral_0 | apply is_integral_C1].
Qed.

Definition is_binary_matrix {n m} (A : Matrix n m) : Prop :=
  forall i j, (i < n)%nat -> (j < m)%nat -> 
  A i j = 0 \/ A i j = 1.

Lemma kron_binary_matrix {n m o p} {A : Matrix n m} {B : Matrix o p}
  (HA : is_binary_matrix A) (HB : is_binary_matrix B) : 
  is_binary_matrix (A ⊗ B).
Proof.
  intros i j Hi Hj.
  unfold kron.
  specialize (HA (i / o) (j / p))%nat.
  do 2 (specialize (HA ltac:(apply Nat.div_lt_upper_bound;lia))).
  specialize (HB (i mod o) (j mod p))%nat.
  do 2 (specialize (HB ltac:(apply Nat.mod_upper_bound;lia))).
  revert HA HB.
  intros [-> | ->] [-> | ->]; Csimpl; auto. 
Qed.

Goal is_binary_matrix (⟦ ⊂ ⟷ ⊃ ⟧).
by_cell.
cbn.

(* Lemma zxbiperm_binary_matrix {n m} {zx : ZX n m} (H : ZXbiperm zx) :
  is_binary_matrix (⟦ zx ⟧).
Proof.
  induction H;
  [by_cell; left + right; reflexivity.. | |].
  - rewrite 2!Nat.pow_add_r.
    apply kron_binary_matrix; easy.
  - intros i j Hi Hj.
    cbn.
    unfold Mmult. *)


Definition matrix_of_zx_biperm {n m : nat} (zx : ZX n m) : Matrix (2^m) (2^n) :=
  matrix_of_biperm n m (biperm_of_zx zx).

Ltac by_cell_nosimpl :=
  intros i j Hi Hj; try solve_end;
  repeat
  (destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
    try solve_end); clear Hi;
  repeat
  (destruct j as [| j]; [  | apply <- Nat.succ_lt_mono in Hj ];
    try solve_end); clear Hj.

Ltac by_cell_Csimpl :=
  intros i j Hi Hj; try solve_end;
  repeat
  (destruct i as [| i]; simpl; Csimpl; [  | apply <- Nat.succ_lt_mono in Hi ];
    try solve_end); clear Hi;
  repeat
  (destruct j as [| j]; simpl; Csimpl; [  | apply <- Nat.succ_lt_mono in Hj ];
    try solve_end); clear Hj.

Notation zxbiperm_correct zx := 
  (mat_equiv (⟦ zx ⟧) (matrix_of_zx_biperm zx)).

Goal zxbiperm_correct —.
by_cell_nosimpl. 
all: cbn. 
all: lca.
Qed.

Goal zxbiperm_correct (— ⟷ —).
by_cell_nosimpl.
all: cbn.
all: lca.
Qed.

Goal zxbiperm_correct ⨉.
by_cell_nosimpl.
all: cbn.
all: reflexivity.
Qed.

Goal zxbiperm_correct (⨉ ⟷ ⨉).
by_cell_nosimpl.
all: cbn.
all: lca.
Qed.

Goal zxbiperm_correct (⨉ ⟷ (— ↕ —)).
by_cell_nosimpl.
all: cbn.
all: lca.
Qed.

Goal zxbiperm_correct ((⨉ ↕ —) ⟷ (— ↕ ⨉)).
cbn.
unfold kron, I, swap, Mmult.
by_cell_nosimpl.
all: cbn.
all: lca. 
Qed.

Goal zxbiperm_correct ((⊃ ↕ —) ⟷ (— ↕ ⊂)).
Admitted. (* for performance *)
(* cbn.
unfold kron, Mmult, big_sum.
intros i j Hi Hj.
rewrite Cplus_0_l.
unfold I.
rewrite !Nat.mod_1_r, !Nat.div_1_r.
simpl (1 mod 2).
change (1 <? 2) with true.
simpl (1 / 2).
simpl (0 / 2).
simpl (0 mod 2).
change (0 <? 2) with true.
(* revert i j Hi Hj. *)

(* by_cell_nosimpl. *)
repeat (destruct i; try lia);
simpl;
Csimpl;
repeat (destruct j; try lia);
simpl; 
Csimpl; reflexivity. *)
(* simpl. *)
(* revert i j Hi Hj. *)
(* by_cell_nosimpl.
all: cbn.
all: lca.  *)
(* Qed. *)

Goal zxbiperm_correct ((— ↕ ⊂) ⟷ (⊃ ↕ —)).
cbn.
unfold kron.
by_cell_nosimpl.
all: cbn.
all: lca. 
Qed.

Goal zxbiperm_correct ((— ↕ ⊂ ↕ ⊂) 
  ⟷ (⊃ ↕ ⊃ ↕ —)).
Proof.
  Admitted. (* for performance *)
  (* cbn.
  unfold kron.
  unfold Mmult, I, list2D_to_matrix.
  by_cell_nosimpl.
  all: cbn.
  all: lca. *)
(* Qed. *)

Goal zxbiperm_correct ((— ↕ ⊂) ⟷
  (⨉ ↕ —) ⟷
  (⊃ ↕ —)).
Proof.
  Admitted. (* for performance *)
  (* cbn.
  unfold kron.
  unfold Mmult.
  by_cell_nosimpl.
  all: cbn.
  all: lca. *)
(* Qed. *)
  

(* 
  Goal zxbiperm_correct ((— ↕ ⊂ ↕ ⊂ ↕ ⊂) 
    ⟷ (⊃ ↕ ⊃ ↕ ⊃ ↕ —)).
  cbn.
  unfold kron.
  unfold Mmult.
  by_cell_nosimpl.

  cbn [Nat.div Nat.modulo Nat.div_mod fst snd].
  lca.
  rewrite !Nat.div_1_r, !Nat.div_0_l, Nat.mod_1_r, Nat.mod_0_l by easy.

  setoid_rewrite Nat.div_1_r.



  all: cbn.
  all: lca. 

  Goal zxbiperm_correct ((— ↕ ⊂ ↕ ⊂ ↕ ⊂ ↕ ⊂ ↕ ⊂) 
    ⟷ (⊃ ↕ ⊃ ↕ ⊃ ↕ ⊃ ↕ ⊃ ↕ —)).
  cbn [ZX_semantics].
    unfold kron.
    cbn [Nat.pow].
    by_cell_nosimpl.
    





  all: match goal with
  |- _ ?i ?j = ?RHS => (* idtac i j; *)
    set (d := nat_to_binlist 4 (i * 2^2 + j));
    let v := eval cbv in (nat_to_binlist 4 (i * 2^2 + j)) in 
    assert (H : d = v) by easy;
    try change (C0 = RHS);
    try change (C1 = RHS);
    try reflexivity;
    revert H
  end.
  unfold matrix_of_zx_biperm.
  cbn [biperm_of_zx].
  unfold matrix_of_biperm.
  cbn [Nat.mul Nat.pow Nat.add].
  unfold number_preserved.
  cbn [seq].
  forallb  
*)

Fixpoint pre_compose_bipermutations (cost : nat) (n m o : nat) 
  (f g : nat -> nat) : nat -> nat :=
  (* like compose_bipermutations, but not explicitly overlapping 
     f and g. Ping-pong among
     [1 ... n 1 ... m 1 ... m 1 ... o] (but 0-indexed) until in 
     terminal region:
      ├─────┤                 ├─────┤
     The domains are
  f : ├─────────────┤ ├─────────────┤ : g
     Swap as appropriate: if the ouput lands 
     in here: ├─────┤ it is moved in the recursive
     call to here:    ├─────┤ and visa versa.
     Designed to enable meaningful induction on cost. *)
  fun k => 
    match cost with
    | O => 
      if n + m + (m + o) <=? k then k else
      if k <? n + m then 
        f k
      else 
        (n + m) + g (k - (n + m))
    | S cost' => 
    if n + m + (m + o) <=? k then k else
    if k <? n + m then 
      if f k <? n then f k else
      pre_compose_bipermutations cost' n m o f g (m + f k)
    else 
      if g (k - (n + m)) <? m then 
        pre_compose_bipermutations cost' n m o f g (n + g (k - (n + m)))
      else n + m + g (k - (n + m))
    end. 

Definition pre_compose_bipermutations_elab (cost : nat) (n m o : nat) 
  (f g : nat -> nat) : nat -> nat * list nat :=
  (fix precompelab (cost : nat) :=  (* List pre_compose_bipermutations, but stores all intermediate results *)
  fun k => 
    match cost with
    | O => 
      if n + m + (m + o) <=? k then (k, []) else
      if k <? n + m then 
        (f k, [k])
      else 
        ((n + m) + g (k - (n + m)), [k])
    | S cost' => 
    if n + m + (m + o) <=? k then (k, []) else
    if k <? n + m then 
      if f k <? n then (f k, [k]) else
      (fst (precompelab cost' (m + f k)),
       k :: f k :: snd (precompelab cost' (m + f k)))
    else 
      if g (k - (n + m)) <? m then 
      (fst (precompelab cost' (n + g (k - (n + m)))),
       k :: g (k - (n + m)) :: snd (precompelab cost' (n + g (k - (n + m)))))
      else (n + m + g (k - (n + m)), [k])
    end) cost.

Lemma pre_compose_bipermutations_eq_elab cost n m o f g k : 
  fst (pre_compose_bipermutations_elab cost n m o f g k) =
  pre_compose_bipermutations cost n m o f g k.
Proof.
  revert k;
  induction cost; intros k; simpl; bdestructΩ';
  rewrite IHcost; reflexivity.
Qed.

Lemma Nodup_snd_pre_compose_bipermutations_elab cost n m o f g k : 
  NoDup (snd (pre_compose_bipermutations_elab cost n m o f g k)).
Proof.
  revert k;
  induction cost; intros k.
  - simpl. bdestructΩ'; simpl; repeat easy + constructor.
  - simpl. bdestructΩ'; simpl; repeat easy + constructor + apply IHcost.


Lemma pre_compose_bipermutations_WF (cost : nat) (n m o : nat) 
  (f g : nat -> nat) : 
  WF_perm (n + m + (m + o)) 
    (pre_compose_bipermutations cost n m o f g).
Proof.
  unfold pre_compose_bipermutations.
  intros k Hk. 
  destruct cost; 
  replace_bool_lia (n + m + (m + o) <=? k) true; 
  easy.
Qed.

Lemma pre_compose_bipermutations_bdd {n m o : nat}
  {f g : nat -> nat} (Hf : perm_bdd (n + m) f)
  (Hg : perm_bdd (m + o) g) (cost : nat) : 
  perm_bdd (n + m + (m + o)) 
    (pre_compose_bipermutations cost n m o f g).
Proof.
  induction cost.
  - simpl; intros; bdestructΩ';
    match goal with 
    | |- context[f ?k] => specialize (Hf k)
    | |- context[g ?k] => specialize (Hg k)
    end; lia.
  - simpl.
    intros k Hk.
    bdestructΩ'; try apply IHcost;
    match goal with 
    | |- context[f ?k] => specialize (Hf k)
    | |- context[g ?k] => specialize (Hg k)
    end; lia.
Qed.

Lemma pre_compose_bipermutations_bipermutation {n m o : nat}
  {f g : nat -> nat} (Hf : bipermutation (n + m) f)
  (Hg : bipermutation (m + o) g) (cost : nat) :
  bipermutation (n + m + (m + o)) 
    (pre_compose_bipermutations cost n m o f g).
Proof.
  induction cost.
  - intros k Hk.
    simpl.
    bdestructΩ';
    match goal with 
    | |- context[f ?k] => specialize (Hf k ltac:(lia))
    | |- context[g ?k] => specialize (Hg k ltac:(lia))
    end; rewrite ?add_sub'; lia.
  - intros k Hk.
    split; [|split].
    + apply pre_compose_bipermutations_bdd; 
      apply Hf + apply Hg + easy.
    + simpl.
      bdestructΩ'; try apply IHcost; try apply Hf. try lia.
  cbn.




Lemma biperm_grow_r_bipermutation_SS n f : bipermutation (S (S n)) f ->
  bipermutation (S (S n)) (biperm_grow_r n f).
Proof.
  intros Hbiperm k Hk.
  pose proof (Hbiperm n ltac:(lia)) as Hfn.
  assert (HfSnlt : f (S n) < S (S n)) by (apply Hbiperm; lia).
  assert (HfSnne : f (S n) <> S n) by (apply Hbiperm; lia).
  rewrite swap_perm_fswap by lia.
  unfold compose.
  split.
  1 : {
    bdestruct (k =? S n); bdestruct (k =? f (S n)); try lia; subst;
    rewrite 1?fswap_simpl1, 1?fswap_simpl2, 1?fswap_neq, 1?Nat.eqb_refl by lia;
    bdestructΩ';
    apply Hbiperm; lia.
  }
  bdestruct (k =? S n); [|bdestruct (k =? f (S n))].
  - subst k.
    rewrite (fswap_simpl2 nat idn (f (S n)) (S n)).
    rewrite (Nat.eqb_refl (f (S n))).
    rewrite (fswap_simpl1 nat idn (f (S n)) (S n)).
    split; [easy|].
    replace_bool_lia (S n =? f (S n)) false.
    rewrite Nat.eqb_refl; easy.
  - (* k = f n *)
    subst k.
    rewrite (fswap_simpl1 nat idn (f (S n)) (S n)).
    replace_bool_lia ((S n) =? f (S n)) false.
    rewrite Nat.eqb_refl.
    rewrite (fswap_simpl2 nat idn (f (S n)) (S n)).
    split; [lia|].
    rewrite Nat.eqb_refl.
    easy.
  - rewrite fswap_neq by lia.
    replace_bool_lia (k =? f (S n)) false.
    replace_bool_lia (k =? S n) false.
    replace_bool_lia (S n <=? k) false.
    bdestruct (k =? n).
    + subst.
      replace_bool_lia (f (S n) <=? n) true.
      replace_bool_lia (f (S n) <=? n + 1) true.
      replace_bool_lia (S n <=? n + 1) true.
      bdestruct (f (S n) =? 0).
      1: {
        rewrite H1; simpl.
        rewrite (bipermutation_eq_iff _ _ Hbiperm) in H1 by lia.
        rewrite <- H1.
        split; [lia|].
        rewrite fswap_simpl2.
      }
      rewrite (fswap_neq idn (f (S n)) (S n) (f (f (S n) - (1 + 1)))).
      2,3:  unfold not; 
        erewrite <- (bipermutation_eq_iff _ _ Hbiperm) by lia;
        rewrite 1?(bipermutation_involutive _ Hbiperm) by lia;
        rewrite 1?(permutation_eq_iff _ _ (permutation_of_bipermutation Hbiperm)) by lia;
        try lia.
      ].
      replace_bool_lia (S n <=? n + (if f (S n) <=? n then 1 else 0 + 0)) (f (S n) <=? n).
      replace_bool_lia (f (S n) <=? n) true.

    bdestruct (n <=? k). 1:{
      replace k with (S n) by lia.
      replace_bool_lia (f n <=? S n) true.
      replace_bool_lia (f n <=? S n + 1) true.
      replace_bool_lia (n <=? S n + 1) true.
}




    replace_bool_lia (f n <=? f n) true.
    replace_bool_lia (f n <=? f n + 1) true.
  unfold swap_perm.
  replace_bool_lia (S n <=? k) false.
  bdestruct (k =? n).
  - replace_bool_lia (k =? f n) false.
    subst k.
    replace_bool_lia (f n <=? f n) true.
    replace (n <=? f n) with false by (bdestruct_all; specialize (Hbiperm n); lia).
    pose proof (Hbiperm n ltac:(lia)) as Hfn.
    replace (S n <=? f (f n - (1 + 0))) with false by
      (bdestructΩ'; pose (Hbiperm (f n - 1)); simpl in *; lia);
    rewrite (bipermutation_eq_iff (f n - (1 + 0)) _ Hbiperm) by lia.
    rewrite (permutation_eqb_iff (f n) n (permutation_of_bipermutation Hbiperm));
      [ | apply Hbiperm; lia | lia].
    replace_bool_lia (f n =? n) false.
    bdestruct (S n <=? f (f n)).
    1: specialize (Hbiperm n Hk); lia.
    rewrite (bipermutation_involutive n Hbiperm Hk).
    rewrite Nat.eqb_refl, (bipermutation_involutive n Hbiperm Hk).
    easy.
  - bdestruct (k =? f n).
    + replace_bool_lia (f n =? n) false.
      replace_bool_lia (f n =? f n) true.
      bdestruct (S n <=? f n).
      1: specialize (Hbiperm n (ltac:(lia))); lia.
      easy.
    + bdestruct (S n <=? f k).
      1: specialize (Hbiperm k Hk); lia.
      rewrite (permutation_eqb_iff k n (permutation_of_bipermutation Hbiperm)) by lia.
      replace_bool_lia (k =? n) false.
      rewrite <- (bipermutation_involutive n Hbiperm) at 1 by lia.
      rewrite (permutation_eqb_iff k (f n) (permutation_of_bipermutation Hbiperm));
        [| lia | apply Hbiperm; lia].
      replace_bool_lia (k =? f n) false.
      eapply (bipermutation_involutive k Hbiperm Hk).
Qed.

Local Notation perm_eq n f g := (forall k, k < n -> f k = g k).

Lemma biperm_grow_r_eq_biprem_grow_l n f : bipermutation (S n) f ->
  perm_eq (S n) (biperm_grow_l n f) (biperm_grow_r n f).
Proof.
  intros Hbiperm k Hk; unfold compose.
  bdestruct (f n =? n);
  [rewrite H, swap_perm_same; easy |].
  bdestruct (k =? n).
  - subst k.
    unfold swap_perm.
    rewrite 2!Nat.eqb_refl.
    bdestruct (S n <=? f n).
    1: specialize (Hbiperm n ltac:(lia)); lia.
    replace_bool_lia (S n <=? n) false.
    bdestruct (n =? f n).
    + easy.
    + rewrite (bipermutation_involutive n Hbiperm); lia.
  - unfold swap_perm.
    bdestruct (S n <=? f k).
    1: specialize (Hbiperm k Hk); lia.
    bdestruct (S n <=? k); [lia|].
    rewrite (permutation_eqb_iff k n (permutation_of_bipermutation Hbiperm)) by lia.
    rewrite (bipermutation_eqb_iff k n Hbiperm) by lia.
    bdestruct_all; easy.
Qed.

Lemma bipermutation_S_of_fix n f : bipermutation (S n) f -> f n = n ->
  bipermutation n f.
Proof.
  intros Hbiperm Hfn.
  intros k Hk.
  split; [| apply Hbiperm; lia].
  enough (f k < S n /\ f k <> n) by lia.
  split.
  - apply Hbiperm; lia.
  - (* unfold not.  *)
    rewrite (bipermutation_eq_iff k n Hbiperm); lia.
Qed.

Lemma biperm_grow_r_bipermutation n f : bipermutation (S n) f ->
  bipermutation n (biperm_grow_r n f).
Proof.
  intros Hbiperm.
  apply bipermutation_S_of_fix.
  1: apply biperm_grow_r_bipermutation_S, Hbiperm.
  unfold compose, swap_perm.
  bdestructΩ'.
  rewrite (bipermutation_involutive n Hbiperm); lia.
Qed.

Lemma grow_bipermutation_r n f : bipermutation (S n) f ->
  f = (biperm_grow_r n f ∘ swap_perm (f n) n (S n))%prg.
Proof.
  intros Hbiperm.
  rewrite Combinators.compose_assoc, swap_perm_inv, compose_idn_r.
  - easy.
  - apply Hbiperm; lia.
  - lia.
Qed.

Lemma grow_bipermutation_l n f : bipermutation (S n) f ->
  f = (swap_perm (f n) n (S n) ∘ biperm_grow_l n f)%prg.
Proof.
  intros Hbiperm.
  rewrite <- Combinators.compose_assoc, swap_perm_inv, compose_idn_l.
  - easy.
  - apply Hbiperm; lia.
  - lia.
Qed.


Lemma compose_biperms_0_0_r_eq n f g : bipermutation n f ->
  perm_eq n (compose_biperms n 0 0 f g) f.
Proof.
  intros Hbiperm.
  intros k Hk.
  unfold compose_biperms; bdestructΩ'.
  - induction n.
    + easy.
    + simpl.
      bdestructΩ'.
      specialize (Hbiperm k H); lia.
Qed. 

Lemma compose_biperms_compose_swap_r_eq n m o f g a b : bipermutation (n + m) f ->
  bipermutation (m + o) g -> a < m + o -> b < m + o ->
  compose_biperms n m o f (g ∘ swap_perm a b (m + o)) =
  compose_biperms n m o f g

Lemma compose_biperms_S_0_r_eq n m f g : bipermutation n f -> bipermutation (S m) g ->
  perm_eq (n + (S m)) (compose_biperms n (S m) 0 f g)



Lemma compose_biperms_bipermutation_0_r n m f g : bipermutation (n + m) f ->
  bipermutation m g -> bipermutation (n + 0) (compose_biperms n m 0 f g).
Proof.
  intros Hf Hg.
  intros k Hk; split.
  apply compose_biperms_bounded; easy.
  revert k Hk.
  replace (n + 0) with n in * by lia.
  induction m.
  - replace (n + 0) with n in * by lia.
    intros k Hk.
    rewrite (compose_biperms_0_0_r_eq _ _ _ Hf k Hk).
    rewrite compose_biperms_0_0_r_eq; [| easy | apply Hf; easy].
    erewrite bipermutation_involutive by eassumption.
    easy.
  - intros k Hk.
    simpl.





Lemma compose_biperms_bipermutation n m o f g : bipermutation (n + m) f ->
  bipermutation (m + o) g -> bipermutation (n + o) (compose_biperms n m o f g).
Proof.
  intros Hf Hg.
  intros k Hk; split.
  apply compose_biperms_bounded; easy.
  revert k Hk.
  induction o.
  - intros k Hk.
    unfold compose_biperms.
    bdestructΩ'; split; try lia.


  split; [auto with perm_bdd_db|].
  unfold compose_biperms.
  remember (n + o) as c.
  assert (n + o)
  Admitted.




  

Notation rel_eq n f g := 
  (forall i j, i < n -> j < n -> f i j = g i j).

Definition stack_rels2 n0 m0 n1 m1 f g : rel :=
  fun i j => 
    if (i <? n0) then (
      (j <? n0) && (f i j) ||
      (n0 + n1 <=? j) && (j <? n0 + n1 + m0) && (f i (j - n1))
    ) else
    if (i <? n0 + n1) then (
      (n0 <=? j) && (j <? n0 + n1) && (g (i - n0) (j - n0)) ||
      (n0 + n1 + m0 <=? j) && (j <? n0 + n1 + m0 + m1) && (g (i - n0) (j - (n0 + m0)))
    ) else
    if (i <? n0 + n1 + m0) then (
      (j <? n0) && (f (i - n1) j) ||
      (n0 + n1 <=? j) && (j <? n0 + n1 + m0) && (f (i - n1) (j - n1))
    ) else
    if (i <? n0 + n1 + m0 + m1) then (
      (n0 <=? j) && (j <? n0 + n1) && (g (i - (n0 + m0)) (j - n0)) ||
      (n0 + n1 + m0 <=? j) && (j <? n0 + n1 + m0 + m1) && (g (i - (n0 + m0)) (j - (n0 + m0)))
    ) else false.

Fixpoint rel_of_zx {n m} (zx : ZX n m) : rel :=
  let conn i j a b := (i =? a) && (j =? b) || (i =? b) && (j =? a) in
  match zx with
  | ⦰ => fun i j => false
  | ⊂ => fun i j => conn i j 0 1
  | ⊃ => fun i j => conn i j 0 1
  | ⨉ => fun i j =>
    conn i j 0 2 || conn i j 1 3
  | — => fun i j => conn i j 0 1
  | □ => fun i j => conn i j 0 1
  | X_Spider n m _ => 
    fun i j => (i <? n) && (n <=? j) && (j <? n + m) 
      || (j <? n) && (n <=? i) && (i <? n + m)
  | Z_Spider n m _ => 
    fun i j => (i <? n) && (n <=? j) && (j <? n + m) 
      || (j <? n) && (n <=? i) && (i <? n + m)
  | @Stack n0 m0 n1 m1 zx0 zx1 => 
    let f := rel_of_zx zx0 in
    let g := rel_of_zx zx1 in (* Note this is backwards! *)
    stack_rels2 n1 m1 n0 m0 g f
  | @Compose n m o zx0 zx1 =>
    let f := rel_of_zx zx0 in
    let g := rel_of_zx zx1 in
    compose_rels n m o f g
  end. *)