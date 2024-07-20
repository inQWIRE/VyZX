Require Import PermutationAutomation.

Section AuxiliaryLemmas.

Import Bits Bool.

Section nat_lemmas.

Import Nat.

Local Open Scope nat.

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

Lemma sub_lt_iff n m p (Hp : 0 <> p) : 
  n - m < p <-> n < m + p.
Proof.
  split; lia.
Qed.

Lemma add_assoc_four {a b c d} : a + b + c + d = a + (b + c + d).
Proof.
  now rewrite 2!Nat.add_assoc.
Qed.

Lemma add_assoc_three {a b c} : a + (b + c) = a + b + c.
Proof.
  now rewrite Nat.add_assoc.
Qed.

Lemma sub_eq_iff {a b m} : b <= a ->
  a - b = m <-> a = b + m.
Proof.
  lia.
Qed.

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

Lemma add_sub_four (n m o : nat) : 
  n + m - o - n = m - o.
Proof. lia. Qed.

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

Lemma mod_div a b : a mod b / b = 0.
Proof.
  destruct b; [easy|].
  apply Nat.div_small, Nat.mod_upper_bound; easy.
Qed.

Lemma mod_add_l a b c : (a * b + c) mod b = c mod b.
Proof.
  rewrite Nat.add_comm.
  apply Nat.Div0.mod_add.
Qed.

Lemma min_ltb n m : min n m = if n <? m then n else m.
Proof.
  bdestructΩ'.
Qed.

Lemma eqb_iff_div_mod_eqb a i j : 
  i =? j =
  (i mod a =? j mod a) && (i / a =? j / a).
Proof.
  apply eq_iff_eq_true.
  rewrite andb_true_iff, !Nat.eqb_eq.
  split; [intros ->; easy|].
  intros.
  rewrite (Nat.div_mod_eq i a), (Nat.div_mod_eq j a).
  lia.
Qed.

Lemma eqb_div_mod_pow_2_iff a i j k l : 
  i mod 2 ^ a + 2 ^ a * j =? k mod 2 ^ a + 2 ^ a * l  =
  ((i mod 2 ^ a =? k mod 2 ^ a) && 
  (j =? l)).
Proof.
  apply eq_iff_eq_true.
  rewrite andb_true_iff, !Nat.eqb_eq.
  split; try lia.
  rewrite 2!(Nat.mul_comm (2^a)).
  intros H.
  generalize (f_equal (fun x => x mod 2^a) H).
  rewrite 2!Nat.Div0.mod_add, !Nat.Div0.mod_mod.
  intros; split; [easy|].
  generalize (f_equal (fun x => x / 2^a) H).
  now rewrite 2!Nat.div_add, !Nat.div_small by 
    (show_nonzero + show_moddy_lt).
Qed.

Lemma succ_even_lt_even a b : Nat.even a = true -> 
  Nat.even b = true ->
  a < b -> S a < b.
Proof.
  intros Ha Hb Hab.
  enough (S a <> b) by lia.
  intros Hf.
  apply (f_equal Nat.even) in Hf.
  rewrite Nat.even_succ in Hf.
  rewrite <- Nat.negb_even in Hf.
  rewrite Ha, Hb in Hf.
  easy.
Qed.

Lemma succ_odd_lt_odd a b : Nat.odd a = true -> 
  Nat.odd b = true ->
  a < b -> S a < b.
Proof.
  intros Ha Hb Hab.
  enough (S a <> b) by lia.
  intros Hf.
  apply (f_equal Nat.even) in Hf.
  rewrite Nat.even_succ in Hf.
  rewrite <- Nat.negb_odd in Hf.
  rewrite Ha, Hb in Hf.
  easy.
Qed.

Lemma even_add_same n : Nat.even (n + n) = true.
Proof.
  now rewrite Nat.even_add, eqb_reflx.
Qed.

Lemma even_succ_false n : 
  Nat.even (S n) = false <-> Nat.even n = true.
Proof.
  rewrite Nat.even_succ, <- Nat.negb_even. 
  now destruct (Nat.even n).
Qed.

Lemma even_succ_add_same n : Nat.even (S (n + n)) = false.
Proof.
  now rewrite even_succ_false, even_add_same.
Qed.

Lemma odd_succ_false n : 
  Nat.odd (S n) = false <-> Nat.odd n = true.
Proof.
  rewrite Nat.odd_succ, <- Nat.negb_odd. 
  now destruct (Nat.odd n).
Qed.

Lemma double_add n m : n + m + (n + m) = n + n + (m + m).
Proof.
  lia.
Qed.

Lemma sub_leb_eq n m p : 
  n - m <=? p = (n <=? m + p).
Proof.
  bdestructΩ'.
Qed.

Lemma sub_ltb_eq_nonzero n m p : p <> 0 ->
  n - m <? p = (n <? m + p).
Proof.
  intros.
  bdestructΩ'.
Qed.

Lemma sub_ltb_eq_le n m p : m <= n ->
  n - m <? p = (n <? m + p).
Proof.
  intros.
  bdestructΩ'.
Qed.

Lemma sum_ne_pows_2_lt_pow_2_S n k l : 
  k < n -> l < n -> k <> l -> 
  2^k + 2^l < 2 ^ n.
Proof.
  intros.
  bdestruct (2^k + 2^l <? 2^n); [easy|].
  destruct n; [easy|].
  simpl in *; rewrite Nat.add_0_r in *.
  pose proof (Nat.pow_le_mono_r 2 k n).
  pose proof (Nat.pow_le_mono_r 2 l n).
  assert (Heq: 2^k = 2^l) by lia.
  apply (f_equal Nat.log2) in Heq.
  rewrite 2!Nat.log2_pow2 in Heq; lia.
Qed.

Lemma sub_S_sub_S n k : k < n -> 
  n - S (n - S k) = k.
Proof.
  lia.
Qed.

Section testbit_lemmas.

Lemma testbit_add_pow2_small (i j s n : nat) (Hs : s < n) : 
  Nat.testbit (i + 2^n * j) s = Nat.testbit i s.
Proof.
  rewrite 2!Nat.testbit_eqb.
  replace n with (s + (n - s)) by lia.
  rewrite Nat.pow_add_r, <- Nat.mul_assoc, Nat.mul_comm, Nat.div_add by
    (apply Nat.pow_nonzero; lia).
  destruct (n - s) eqn:e; [lia|].
  cbn [Nat.pow].
  rewrite <- Nat.mul_assoc, Nat.mul_comm, Nat.Div0.mod_add by lia.
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
    <- Nat.Div0.div_div, Nat.div_add by
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
    rewrite Nat.Div0.mod_add, Nat.Div0.mod_mod, Nat.div_add by easy.
    rewrite Nat.div_small by (now apply Nat.mod_upper_bound).
    do 2 f_equal.
    rewrite Nat.testbit_eqb.
    bdestructΩ'; simpl Nat.b2n.
    simpl Nat.add.
    rewrite Nat.Div0.mod_0_l.
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

Lemma testbit_mod_pow2 i n m : 
  Nat.testbit (i mod 2^n) m = 
  if m <? n then Nat.testbit i m else false.
Proof.
  pose proof (Nat.pow_nonzero) as Hnz.
  bdestruct (m <? n).
  - rewrite Nat.mod_pow2_bits_low; easy.
  - rewrite Nat.mod_pow2_bits_high; easy.
Qed.

Lemma testbit_div_pow2 i n m : 
  Nat.testbit (i / 2^n) m = 
  Nat.testbit i (n + m).
Proof.
  rewrite Nat.add_comm.
  apply Nat.div_pow2_bits.
Qed.

Lemma testbit_mul_pow2 i n m : 
  Nat.testbit (i * 2^n) m = 
  if m <? n then false else
  Nat.testbit i (m - n).
Proof.
  bdestructΩ'.
  - now rewrite Nat.mul_pow2_bits_low.
  - now rewrite Nat.mul_pow2_bits_high.
Qed.

Lemma testbit_remove_gap i m k s : 
  Nat.testbit (i mod 2^m + (i/2^m / 2^k) * (2^m)) s =
  if s <? m then Nat.testbit i s else 
  Nat.testbit i (s + k).
Proof.
  rewrite Nat.add_comm.
  rewrite testbit_add_pow2_split by
  (apply Nat.mod_upper_bound, Nat.pow_nonzero; lia).
  bdestruct (s <? m).
  - rewrite testbit_mod_pow2; bdestructΩ'.
  - rewrite !testbit_div_pow2.
    bdestructΩ'; f_equal; lia.
Qed.

Lemma testbit_remove_2_gap i m s : 
  Nat.testbit (i mod 2^m + (i/2^m / 4) * (2^m)) s =
  if s <? m then Nat.testbit i s else 
  Nat.testbit i (s + 2).
Proof.
  change 4 with (2^2).
  apply testbit_remove_gap.
Qed.

Lemma testbit_remove_2_gap' i m s : 
  Nat.testbit ((i/2^m / 4) * (2^m) + i mod 2^m) s =
  if s <? m then Nat.testbit i s else
  Nat.testbit i (s + 2).
Proof.
  rewrite Nat.add_comm; apply testbit_remove_2_gap.
Qed.

Lemma nat_lt_pow2_funbool_to_nat_ind (P : nat -> Prop) n
  (H : forall f, P (funbool_to_nat n f)) : 
  forall i, i < 2 ^ n -> P i.
Proof.
  intros i Hi.
  rewrite <- (nat_to_funbool_inverse n i Hi).
  apply H.
Qed.

Lemma div_add' n m p : 
  (n + m) / p = 
  n / p + m / p + (n mod p + m mod p) / p.
Proof.
  rewrite (Nat.div_mod_eq n p) at 1.
  rewrite (Nat.div_mod_eq m p) at 1.
  bdestruct (p =? 0); [now subst|].
  symmetry.
  rewrite Nat.add_comm.
  rewrite <- Nat.div_add by easy.
  f_equal.
  lia.
Qed.

Lemma sum_eq_lxor_of_bits_disj_l n m : 
  (forall k, Nat.testbit n k = true -> Nat.testbit m k = false) ->
  n + m = Nat.lxor n m.
Proof.
  intros Hnm.
  apply bits_inj.
  intros s.
  rewrite lxor_spec.
  revert n m Hnm.
  induction s; 
  intros n m Hnm;
  [apply Nat.odd_add|].
  simpl.
  rewrite !div2_div.
  rewrite div_add'.
  rewrite <- !bit0_mod.
  rewrite (div_small (_ + _)), Nat.add_0_r by 
    (generalize (Hnm 0); 
    destruct (testbit n 0), (testbit m 0); 
    simpl; lia).
  apply IHs.
  intros k.
  rewrite 2!div2_bits; auto.
Qed.

Lemma testbit_add_disjoint_pow2_l k n : 
  Nat.testbit n k = false ->
  forall i,
  Nat.testbit (2^k + n) i = (i =? k) || testbit n i.
Proof.
  intros Hn i.
  rewrite sum_eq_lxor_of_bits_disj_l, lxor_spec, pow2_bits_eqb, eqb_sym.
  - bdestructΩ'.
    now rewrite Hn.
  - intros s.
    rewrite pow2_bits_eqb.
    bdestructΩ'.
Qed.

Lemma testbit_sum_pows_2_ne k l : k <> l -> forall i, 
  Nat.testbit (2 ^ k + 2 ^ l) i = (i =? k) || (i =? l).
Proof.
  intros Hkl i.
  rewrite testbit_add_disjoint_pow2_l;
  rewrite pow2_bits_eqb; bdestructΩ'.
Qed.

Lemma testbit_add_disjoint m n : 
  (forall k, Nat.testbit n k = true -> Nat.testbit m k = false) ->
  forall i,
  Nat.testbit (n + m) i = testbit n i || testbit m i.
Proof.
  intros Hn i.
  rewrite sum_eq_lxor_of_bits_disj_l, lxor_spec by easy.
  generalize (Hn i).
  destruct (testbit n i), (testbit m i); lia + auto.
Qed.

Lemma testbit_b2n b k : 
  testbit (b2n b) k = b && (k =? 0).
Proof.
  destruct b, k; easy + apply Nat.bits_0.
Qed.

Lemma testbit_decomp n k : 
  n = (n / 2 ^ (S k)) * 2 ^ (S k) + 
    b2n (testbit n k) * 2 ^ k + (n mod 2^k).
Proof.
  apply bits_inj.
  intros s.
  rewrite Nat.pow_succ_r, Nat.mul_assoc, <- Nat.mul_add_distr_r by lia.
  rewrite testbit_add_pow2_split by show_moddy_lt.
  change 2 with (2^1) at 4.
  rewrite testbit_add_pow2_split by (destruct (testbit n k); simpl; lia).
  rewrite testbit_b2n.
  rewrite <- Nat.pow_succ_r by lia.
  rewrite testbit_div_pow2, testbit_mod_pow2.
  bdestructΩ'; rewrite ?andb_true_r; f_equal; lia.
Qed.

End testbit_lemmas.

End nat_lemmas.

Import Setoid.

Section bool_lemmas.

Lemma eqb_true_l b : eqb true b = b.
Proof. now destruct b. Qed.

Lemma eqb_true_r b : eqb b true = b.
Proof. now destruct b. Qed.

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

End bool_lemmas.

Section Assorted_lemmas.

Lemma if_true {A} b (u v : A) : 
  b = true ->
  (if b then u else v) = u.
Proof.
  bdestructΩ'.
Qed.

Lemma if_false {A} b (u v : A) : 
  b = false ->
  (if b then u else v) = v.
Proof.
  bdestructΩ'.
Qed.

Lemma if_dist' {A B} (f : A -> B) (b : bool) (x y : A) : 
  f (if b then x else y) = if b then f x else f y.
Proof.
  now destruct b.
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

Lemma f_equal_if_precedent {A} b c (v1 v2 u1 u2 : A) : 
  b = c -> 
  (b = true -> c = true -> v1 = v2) ->
  (b = false -> c = false -> u1 = u2) ->
  (if b then v1 else u1) = (if c then v2 else u2).
Proof.
  intros ->.
  destruct c; auto.
Qed.

Lemma f_equal_if_precedent_same {A} b (v1 v2 u1 u2 : A) : 
  (b = true -> v1 = v2) ->
  (b = false -> u1 = u2) ->
  (if b then v1 else u1) = (if b then v2 else u2).
Proof.
  intros.
  apply f_equal_if_precedent; auto.
Qed.

Lemma and_same (P : Prop) : P /\ P <-> P.
Proof. split; try intros []; auto. Qed.

Local Open Scope nat_scope.

Lemma and_andb {P P'} {b b'} : 
  reflect P b -> reflect P' b' -> 
  reflect (P /\ P') (b && b').
Proof.
  intros H H'; apply reflect_iff in H, H'.
  apply iff_reflect.
  rewrite andb_true_iff.
  now rewrite H, H'.
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

Import Setoid.

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

Lemma forall_lt_sum_split n m (P : nat -> Prop) : 
  (forall k, k < n + m -> P k) <->
  (forall k, k < n -> P k) /\ (forall k, k < m -> P (n + k)).
Proof.
  split; [intros H; split; intros; apply H; lia|].
  intros [Hlow Hhigh].
  intros.
  bdestruct (k <? n);
  [now apply Hlow|].
  generalize (Hhigh (k - n) ltac:(lia)).
  rewrite Nat.add_sub_assoc, add_sub' by lia.
  easy.
Qed.


End Assorted_lemmas.

Section BigSumLemmas.

Local Open Scope nat.
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

Lemma big_sum_split n i (v : nat -> G) (Hi : (i < n)) :
  big_sum v n = (big_sum v i) + v i + (big_sum (shift v (i + 1)) (n - 1 - i)).
Proof.
  intros.
  induction n; [lia|].
  bdestruct (i =? n).
  - subst.
    replace (S n - 1 - n)%nat with O by lia.
    rewrite <- big_sum_extend_r. 
    simpl. 
    solve_monoid.
  - specialize (IHn ltac:(lia)).
    replace (S n - 1 - i)%nat with (S (n - 1 - i))%nat by lia.
    rewrite <- !big_sum_extend_r.
    rewrite IHn.
    unfold shift; simpl.
    replace (n - 1 - i + (i + 1))%nat with n by lia.
    now rewrite Gplus_assoc.
Qed.

Lemma big_sum_eq_up_to_fswap n (v : nat -> G) f x y (Hx : x < n) (Hy : y < n) :
  big_sum (fun i => v (f i)) n = 
  big_sum (fun i => v (fswap f x y i)) n.
Proof.
  bdestruct (x =? y);
  [apply big_sum_eq_bounded; unfold fswap; intros;
    bdestructΩ'|].
  bdestruct (x <? y).
  - rewrite 2 (big_sum_split n y) by auto.
    rewrite 2 (big_sum_split y x) by auto.
    rewrite fswap_simpl1, fswap_simpl2.
    apply f_equal_gen; try apply f_equal;
    [|apply big_sum_eq_bounded; unfold fswap, shift; intros;
      bdestructΩ'].
    rewrite <- !Gplus_assoc.
    apply f_equal_gen; try apply f_equal;
    [apply big_sum_eq_bounded; unfold fswap; intros;
      bdestructΩ'|].
    rewrite Gplus_comm, (Gplus_comm _ (v (f y))), Gplus_assoc.
    do 2 f_equal.
    apply big_sum_eq_bounded; unfold fswap, shift; intros;
    bdestructΩ'.
  - rewrite 2 (big_sum_split n x) by auto.
    rewrite 2 (big_sum_split x y) by lia.
    rewrite fswap_simpl1, fswap_simpl2.
    apply f_equal_gen; try apply f_equal;
    [|apply big_sum_eq_bounded; unfold fswap, shift; intros;
      bdestructΩ'].
    rewrite <- !Gplus_assoc.
    apply f_equal_gen; try apply f_equal;
    [apply big_sum_eq_bounded; unfold fswap; intros;
      bdestructΩ'|].
    rewrite Gplus_comm, (Gplus_comm _ (v (f x))), Gplus_assoc.
    do 2 f_equal.
    apply big_sum_eq_bounded; unfold fswap, shift; intros;
    bdestructΩ'.
Qed.


Lemma big_sum_reorder n (v : nat -> G) f (Hf : permutation n f) :
  big_sum v n = big_sum (fun i => v (f i)) n.
Proof.
  intros.
  generalize dependent f.
  induction n.
  reflexivity.
  intros f [g Hg].
  destruct (Hg n) as [_ [H1' [_ H2']]]; try lia.
  symmetry.
  rewrite (big_sum_eq_up_to_fswap _ v _ (g n) n) by auto.
  repeat rewrite <- big_sum_extend_r.
  rewrite fswap_simpl2.
  rewrite H2'.
  specialize (IHn (fswap f (g n) n)).
  rewrite <- IHn; [easy|].
  apply fswap_at_boundary_permutation; auto.
  exists g. auto.
Qed.

Lemma big_sum_product_div_mod_split n m (f : nat -> G) : 
  big_sum f (n * m) = 
  big_sum (fun i => big_sum (fun j => f (j + i * n)%nat) n) m.
Proof.
  rewrite big_sum_double_sum.
  apply big_sum_eq_bounded.
  intros k Hk.
  f_equal.
  rewrite (Nat.div_mod_eq k n) at 1.
  lia.
Qed.

End BigSumLemmas.


Section C_lemmas.


Local Open Scope C_scope.

Lemma big_sum_if_eq_C (f : nat -> C) n k :
  Σ (fun x => if x =? k then f x else 0%R) n =
  (if k <? n then f k else 0%R).
Proof. 
  apply (@big_sum_if_eq C).
Qed.

Lemma big_sum_if_eq_C' (f : nat -> C) n k :
  Σ (fun x => if k =? x then f x else 0%R) n =
  (if k <? n then f k else 0%R).
Proof. 
  apply (@big_sum_if_eq' C).
Qed.

Lemma add_if_exclusive_join_C (b c : bool) (v : C) : 
  (b = true -> c = false) -> (c = true -> b = false) -> 
  ((if b then v else 0%R) + (if c then v else 0%R) = 
  if b || c then v else 0%R)%C.
Proof.
  destruct b, c; simpl; intros; lca.
Qed.

Lemma Cmult_if_l (b : bool) (c d : C) : 
  (if b then c else 0%R) * d = 
  if b then c * d else 0%R.
Proof.
  destruct b; now Csimpl.
Qed.

Lemma Cmult_if_r (b : bool) (c d : C) : 
  d * (if b then c else 0%R) = 
  if b then d * c else 0%R.
Proof.
  destruct b; now Csimpl.
Qed.

Lemma Cmult_if_andb (b c : bool) (x y : C) : 
  (if b then x else 0%R) * (if c then y else 0%R) = 
  if b && c then x * y else 0%R.
Proof.
  destruct b,c; now Csimpl.
Qed.

Lemma Cmult_if_1_l (b : bool) (d : C) : 
  (if b then C1 else 0%R) * d = 
  if b then d else 0%R.
Proof.
  destruct b; now Csimpl.
Qed.

Lemma Cmult_if_1_r (b : bool) (d : C) : 
  d * (if b then C1 else 0%R) = 
  if b then d else 0%R.
Proof.
  destruct b; now Csimpl.
Qed.

Lemma Cmult_if_if_1_l (b c : bool) (x : C) : 
  (if b then C1 else 0%R) * (if c then x else 0%R) = 
  if b && c then x else 0%R.
Proof.
  destruct b; now Csimpl.
Qed.

Lemma Cmult_if_if_1_r (b c : bool) (x : C) : 
  (if b then x else 0%R) * (if c then C1 else 0%R) = 
  if b && c then x else 0%R.
Proof.
  destruct b,c; now Csimpl.
Qed.

Lemma Cdiv_mult_r (c d : C) : d <> 0%R ->
  c / d * d = c.
Proof.
  intros.
  C_field_simplify; trivial.
Qed.

Lemma Cdiv_mult_l (c d : C) : d <> 0%R ->
  d * c / d = c.
Proof.
  intros.
  C_field_simplify; trivial.
Qed.

Lemma Cdiv_mult_l' (c d : C) : d <> 0%R ->
  d * (c / d) = c.
Proof.
  intros.
  C_field_simplify; trivial.
Qed.

Lemma Cdiv_nonzero (c d : C) : c <> 0%R -> d <> 0%R ->
  c / d <> 0%R.
Proof.
  intros Hc Hd Hf; apply Hc.
  apply (f_equal (Cmult d)) in Hf.
  rewrite Cdiv_mult_l' in Hf; [|easy].
  revert Hf.
  now Csimpl.
Qed.

Lemma C1_nonzero : C1 <> 0%R.
Proof.
  unfold C1.
  intros H; inversion H.
  lra.
Qed.

Lemma C2_nonzero : C2 <> 0%R.
Proof.
  unfold C2.
  intros H; inversion H.
  lra.
Qed.

End C_lemmas.

Local Notation "A ⩧ B" := (mat_equiv A B) (at level 70) : matrix_scope.

Section matrix_lemmas.

#[global] Add Parametric Relation {n m} : (Matrix n m) (@mat_equiv n m) 
  reflexivity proved by ltac:(easy)
  symmetry proved by ltac:(intros A B H i j Hi Hj; 
    symmetry; apply H; easy)
  transitivity proved by ltac:(intros A B C H H' i j Hi Hj;
    transitivity (B i j); [apply H | apply H']; easy)
  as mat_equiv_setoid.

#[global] Add Parametric Morphism {n m} : (@scale n m) 
  with signature 
  eq ==> (@mat_equiv n m) ==> mat_equiv
  as scale_mat_equiv_proper.
Proof.
  unfold scale.
  intros x A B H i j Hi Hj.
  rewrite (H i j Hi Hj).
  easy.
Qed.

#[global] Add Parametric Morphism {n m o} : (@Mmult m n o) 
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

#[global] Add Parametric Morphism {n m o p} : (@kron m n o p) 
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

#[global] Add Parametric Morphism n m : (@Matrix.transpose n m) 
  with signature
  @mat_equiv n m ==> @mat_equiv m n
  as transpose_proper.
Proof.
  unfold mat_equiv.
  intros A B H i j Hi Hj.
  now apply H.
Qed.

Local Open Scope nat.
Local Open Scope matrix_scope.


Lemma transpose_proper_inv {n m} (A B : Matrix n m) : 
  A ⊤ ⩧ B ⊤ -> A ⩧ B.
Proof.
  intros H i j Hi Hj;
  now apply H.
Qed.

Lemma mat_equiv_prop_symm {n m} (A B : Matrix n m) : 
  (exists c : C, mat_equiv A (c .* B) /\ c <> 0%R)
  <-> exists c : C, mat_equiv B (c .* A) /\ c <> 0%R.
Proof.
  split;
  intros (c & Heq & Hc);
  Proportional.prop_exists_nonzero (/ c); auto;
  now rewrite Heq, Mscale_assoc, Cmult_comm, Cinv_r, Mscale_1_l.
Qed.

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

Lemma kron_transpose' [m n o p] (A : Matrix m n) (B : Matrix o p) :
  forall mo' mp',
  @Matrix.transpose mo' mp' (A ⊗ B) = 
  (@Matrix.transpose m n A) ⊗ (@Matrix.transpose o p B).
Proof.
  intros.
  apply kron_transpose.
Qed.

Lemma kron_1_l_mat_equiv {m n} (A : Matrix m n) : 
  I 1 ⊗ A ⩧ A.
Proof.
  intros i j Hi Hj.
  unfold kron.
  rewrite !Nat.div_small, !Nat.mod_small by lia.
  apply Cmult_1_l.
Qed.

Lemma matrix_times_basis_eq_lt {m n : nat} (A : Matrix m n) (i j : nat) :
  j < n -> (A × basis_vector n j) i 0 = A i j.
Proof.
  intros Hj.
  unfold Mmult.
  rewrite (big_sum_eq_bounded _ (fun k => if k =? j then A i j else 0%R)%C).
  2: {
    intros k Hk.
    unfold basis_vector.
    bdestructΩ'; lca.
  }
  rewrite big_sum_if_eq_C.
  bdestructΩ'.
Qed.

Lemma matrix_times_basis_mat_equiv {m n : nat} (A : Matrix m n) (j : nat) :
  j < n -> mat_equiv (A × basis_vector n j) 
  (get_vec j A).
Proof.
  intros Hj i z Hi Hz.
  replace z with 0 by lia.
  rewrite matrix_times_basis_eq_lt by easy.
  unfold get_vec.
  bdestructΩ'.
Qed.

Lemma matrix_conj_basis_eq_lt {m n : nat} (A : Matrix m n) (i j : nat) :
  i < m -> j < n -> ((basis_vector m i)⊤ × A × basis_vector n j) 0 0 = A i j.
Proof.
  intros Hi Hj.
  rewrite matrix_times_basis_mat_equiv by lia.
  unfold get_vec.
  bdestructΩ'.
  unfold Mmult, Matrix.transpose.
  rewrite (big_sum_eq_bounded _ (fun k => if k =? i then A i j else 0%R)%C).
  2: {
    intros k Hk.
    unfold basis_vector.
    bdestructΩ'; lca.
  }
  rewrite big_sum_if_eq_C.
  bdestructΩ'.
Qed.

Lemma mat_equiv_of_all_basis_conj {m n : nat} (A B : Matrix m n) 
  (H : forall (i j : nat), i < m -> j < n -> 
  ((basis_vector m i) ⊤ × A × basis_vector n j) 0 0 =
  ((basis_vector m i) ⊤ × B × basis_vector n j) 0 0) :
  mat_equiv A B.
Proof.
  intros i j Hi Hj.
  specialize (H i j Hi Hj).
  now rewrite 2!matrix_conj_basis_eq_lt in H by easy.
Qed.

Lemma basis_trans_basis {n} i j : 
  ((basis_vector n i) ⊤ × basis_vector n j) 0 0 =
  if (i =? j) && (i <? n) then C1 else 0%R.
Proof.
  unfold Mmult, basis_vector, Matrix.transpose.
  bdestructΩ'simp.
  - erewrite big_sum_eq_bounded.
    2: {
      intros k Hk.
      simpl_bools.
      rewrite Cmult_if_if_1_l.
      replace_bool_lia ((k =? j) && (k =? j)) (k =? j).
      reflexivity.
    }
    rewrite big_sum_if_eq_C.
    bdestructΩ'.
  - rewrite big_sum_0_bounded; [easy|].
    intros; bdestructΩ'simp.
  - rewrite big_sum_0_bounded; [easy|].
    intros; bdestructΩ'simp.
Qed.

Section QuantumLib_lemmas.

Lemma swap_equiv i j : 
  swap i j = 
  if ((i =? 0) && (j =? 0)) 
  || ((i =? 1) && (j =? 2))
  || ((i =? 2) && (j =? 1))
  || ((i =? 3) && (j =? 3)) then C1 else C0.
Proof.
  do 4 (try (destruct i); try destruct j; try easy).
Qed.

Lemma kron_f_to_vec {n m p q} (A : Matrix (2^n) (2^m)) 
  (B : Matrix (2^p) (2^q)) f : 
  @mat_equiv _ 1 (A ⊗ B × f_to_vec (m + q) f)
  ((A × f_to_vec m f (* : Matrix _ 1 *)) ⊗ 
  (B × f_to_vec q (fun k => f (m + k)) (* : Matrix _ 1) *))).
Proof.
  rewrite <- kron_mixed_product.
  rewrite f_to_vec_merge.
  Morphisms.f_equiv.
  apply f_to_vec_eq.
  intros; bdestructΩ'; f_equal; lia.
Qed.

Lemma f_to_vec_split' n m f : 
  mat_equiv (f_to_vec (n + m) f)
  (f_to_vec n f ⊗ f_to_vec m (fun k => f (n + k))).
Proof.
  intros i j Hi Hj.
  rewrite f_to_vec_merge.
  erewrite f_to_vec_eq; [reflexivity|].
  intros; simpl; bdestructΩ'; f_equal; lia.
Qed.

Lemma f_to_vec_split'_eq n m f : 
  (f_to_vec (n + m) f) =
  (f_to_vec n f ⊗ f_to_vec m (fun k => f (n + k))).
Proof.
  apply mat_equiv_eq; [..|apply f_to_vec_split']; auto with wf_db.
Qed.

Lemma f_to_vec_1_eq f : 
  f_to_vec 1 f = if f 0 then ∣1⟩ else ∣0⟩.
Proof.
  cbn.
  unfold ket.
  rewrite kron_1_l by (destruct (f 0); auto with wf_db).
  now destruct (f 0).
Qed.

Lemma f_to_vec_1_mult_r f (A : Matrix (2^1) (2^1)) : 
  A × f_to_vec 1 f = (fun x j => if j =? 0 then A x (Nat.b2n (f 0)) else 0%R).
Proof.
  cbn.
  rewrite kron_1_l by auto with wf_db.
  apply functional_extensionality; intros i.
  apply functional_extensionality; intros j.
  unfold Mmult.
  simpl.
  destruct (f 0);
  unfold ket;
  simpl;
  now destruct j; simpl; Csimpl.
Qed.

Lemma f_to_vec_1_mult_r_decomp f (A : Matrix (2^1) (2^1))  : 
  A × f_to_vec 1 f ⩧
  A 0 (Nat.b2n (f 0)) .* ∣0⟩ .+ 
  A 1 (Nat.b2n (f 0)) .* ∣1⟩.
Proof.
  rewrite f_to_vec_1_mult_r.
  intros i j Hi Hj.
  replace j with 0 by lia.
  simpl.
  autounfold with U_db.
  do 2 (try destruct i); [..| simpl in *; lia]; 
  now Csimpl.
Qed.

Lemma f_to_vec_1_mult_r_decomp_eq f (A : Matrix (2^1) (2^1))  : 
  WF_Matrix A -> 
  A × f_to_vec 1 f =
  A 0 (Nat.b2n (f 0)) .* ∣0⟩ .+ 
  A 1 (Nat.b2n (f 0)) .* ∣1⟩.
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  apply f_to_vec_1_mult_r_decomp.
Qed.

Lemma qubit0_f_to_vec : ∣0⟩ = f_to_vec 1 (fun x => false).
Proof. now rewrite f_to_vec_1_eq. Qed.

Lemma qubit1_f_to_vec : ∣1⟩ = f_to_vec 1 (fun x => x =? 0).
Proof. now rewrite f_to_vec_1_eq. Qed.

Lemma ket_f_to_vec b : ∣ Nat.b2n b ⟩ = f_to_vec 1 (fun x => b).
Proof.
  destruct b; [apply qubit1_f_to_vec | apply qubit0_f_to_vec].
Qed.

Lemma f_to_vec_1_mult_r_decomp_eq' f (A : Matrix (2^1) (2^1))  : 
  WF_Matrix A -> 
  A × f_to_vec 1 f =
  A 0 (Nat.b2n (f 0)) .* f_to_vec 1 (fun x => false) .+ 
  A 1 (Nat.b2n (f 0)) .* f_to_vec 1 (fun x => x=?0).
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  rewrite f_to_vec_1_mult_r_decomp.
  rewrite 2!f_to_vec_1_eq.
  easy.
Qed.

Lemma f_to_vec_1_mult_l_decomp f (A : Matrix (2^1) (2^1))  : 
  (f_to_vec 1 f) ⊤ × A ⩧
  A (Nat.b2n (f 0)) 0 .* (∣0⟩ ⊤) .+ 
  A (Nat.b2n (f 0)) 1 .* (∣1⟩ ⊤).
Proof.
  rewrite <- (transpose_involutive _ _ A).
  rewrite <- Mmult_transpose, <- Mscale_trans.
  intros i j Hi Hj.
  apply (f_to_vec_1_mult_r_decomp f (A ⊤)); easy.
Qed.

Lemma f_to_vec_1_mult_l_decomp_eq f (A : Matrix (2^1) (2^1))  : 
  WF_Matrix A -> 
  (f_to_vec 1 f) ⊤ × A =
  A (Nat.b2n (f 0)) 0 .* (∣0⟩ ⊤) .+ 
  A (Nat.b2n (f 0)) 1 .* (∣1⟩ ⊤).
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  apply f_to_vec_1_mult_l_decomp.
Qed.

Lemma f_to_vec_1_mult_l_decomp_eq' f (A : Matrix (2^1) (2^1))  : 
  WF_Matrix A -> 
  (f_to_vec 1 f) ⊤ × A =
  A (Nat.b2n (f 0)) 0 .* ((f_to_vec 1 (fun x => false)) ⊤) .+ 
  A (Nat.b2n (f 0)) 1 .* ((f_to_vec 1 (fun x => x =? 0)) ⊤).
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  rewrite f_to_vec_1_mult_l_decomp_eq by easy.
  now rewrite qubit0_f_to_vec, qubit1_f_to_vec.
Qed.

Lemma funbool_to_nat_add_pow2_join n f g m : 
  funbool_to_nat n f * 2 ^ m + funbool_to_nat m g = 
  funbool_to_nat (n + m) (fun k => if k <? n then f k else g (k - n)).
Proof.
  apply bits_inj.
  intros s.
  rewrite testbit_add_pow2_split by apply funbool_to_nat_bound.
  rewrite 3!testbit_funbool_to_nat.
  bdestructΩ'; f_equal; lia.
Qed.

Lemma funbool_to_nat_div_pow2 n m f : 
  funbool_to_nat n f / 2 ^ m = funbool_to_nat (n - m) f.
Proof.
  apply bits_inj.
  intros s.
  rewrite testbit_div_pow2, 2!testbit_funbool_to_nat.
  bdestructΩ'; f_equal; lia.
Qed.

Lemma funbool_to_nat_mod_pow2 n m f : 
  (funbool_to_nat n f) mod 2 ^ m = 
  funbool_to_nat (min n m) (fun k => f (n + k - (min n m))).
Proof.
  apply bits_inj.
  intros s.
  rewrite testbit_mod_pow2, 2!testbit_funbool_to_nat.
  rewrite min_ltb.
  bdestructΩ'; f_equal; lia.
Qed.

Lemma funbool_to_nat_eq_iff n f g  :
  (forall k, k < n -> f k = g k) <-> funbool_to_nat n f = funbool_to_nat n g.
Proof.
  split; 
  [apply funbool_to_nat_eq|].
  intros H k Hk.
  apply (f_equal (fun f => Nat.testbit f (n - S k))) in H.
  revert H.
  rewrite 2!testbit_funbool_to_nat.
  simplify_bools_lia.
  now replace (n - S (n - S k)) with k by lia.
Qed.

(* For setoid_rewrite *)
Lemma nat_to_funbool_eq' n j k :
  nat_to_funbool n j k = 
  if k <=? n - 1 then Nat.testbit j (n - S k) else false.
Proof.
  now rewrite nat_to_funbool_eq.
Qed.

End QuantumLib_lemmas.

End matrix_lemmas.

End AuxiliaryLemmas.
