Require Import QuantumLib.Permutations.
Require Import PermutationAutomation.



(* We're about to show the correctness of zxperm semantics (i.e., 
   matrix of (perm_of_zx zx) is ⟦ zx ⟧ for zx a ZXperm), but first, 
   we need a tremendous amount of machinery to show that stack_permutation
   behaves like the kronecker product. [The rest of the proof of
   correctness is a third length of just correctness of stacking.]*)

Local Open Scope nat.
  
Lemma testbit_binlist {n : nat} {k : list bool} :
  Nat.testbit (binlist_to_nat k) n = nth n k false.
Proof.
  revert k;
  induction n;
  intros k.
  - cbn.
    destruct k; [easy|].  
    destruct b; cbn;
    rewrite Nat.add_0_r.
    2: rewrite <- Nat.negb_even;
      symmetry; apply negb_sym; cbn.
    1: rewrite Nat.odd_succ.
    all: rewrite Nat.even_add;
      apply eqb_reflx.
  - destruct k.
    + rewrite Nat.testbit_0_l; easy.
    + simpl. 
      destruct b;
      simpl Nat.b2n.
      * rewrite Nat.add_1_l.
        rewrite Nat.add_0_r, double_mult.
        rewrite div2_S_double.
        apply IHn.
      * rewrite Nat.add_0_l, Nat.add_0_r, double_mult.
        rewrite Nat.div2_double.
        apply IHn.
Qed.

Lemma binlist_mod {k : list bool} {n0 : nat} :
  (binlist_to_nat k) mod (2^n0) = binlist_to_nat (firstn n0 k).
Proof.
  apply Nat.bits_inj.
  intros n.
  rewrite testbit_binlist.
  bdestruct (n <? n0).
  - rewrite Nat.mod_pow2_bits_low.
    rewrite testbit_binlist.
    rewrite nth_firstn.
    easy.
    1,2: exact H.
  - rewrite Nat.mod_pow2_bits_high; [|easy].
    rewrite nth_overflow; [easy|].
    transitivity n0; [|easy].
    apply firstn_le_length.
Qed.

Lemma nth_skipn {T:Type} {n0 n : nat} {k : list T} {d : T} : 
  nth n (skipn n0 k) d = nth (n0 + n) k d.
Proof.
  bdestruct (n0 <? length k).
  - replace (nth _ k d) with 
      (nth (n0+n) (firstn n0 k ++ skipn n0 k) d) 
      by (rewrite (firstn_skipn n0 k); easy).
    replace (n0 + n) with (length (firstn n0 k) + n).
    + rewrite app_nth2_plus.
      easy. 
    + rewrite firstn_length_le; lia.
  - rewrite skipn_all2; [|easy].
    rewrite 2!nth_overflow; cbn; try easy; try lia.
Qed.

Lemma binlist_div {k : list bool} {n0 : nat} :
  (binlist_to_nat k) / (2^n0) = binlist_to_nat (skipn n0 k).
Proof.
  apply Nat.bits_inj.
  intros n.
  rewrite Nat.div_pow2_bits.
  rewrite 2!testbit_binlist.
  rewrite nth_skipn.
  rewrite Nat.add_comm.
  easy. 
Qed.

Lemma funbool_to_nat_div {n0 n1 : nat} {f}:
  (funbool_to_nat (n0 + n1) f) / (2^n1) = funbool_to_nat n0 f.
Proof.
  destruct n1.
  - rewrite Nat.pow_0_r, Nat.div_1_r, Nat.add_0_r.
    easy.
  - rewrite (funbool_to_nat_shift _ _ n0); [|lia].
    replace (n0 + S n1 - n0) with (S n1) by lia.
    rewrite Nat.mul_comm.
    rewrite Nat.div_add_l; [|apply Nat.pow_nonzero; easy].
    rewrite Nat.div_small; [easy|].
    apply funbool_to_nat_bound.
Qed.

Lemma funbool_to_nat_mod {n0 n1 : nat} {f}:
  (funbool_to_nat (n0 + n1) f) mod (2^n1) = funbool_to_nat n1 (shift f n0).
Proof.
  destruct n1.
  - rewrite Nat.pow_0_r, Nat.mod_1_r.
    easy.
  - rewrite (funbool_to_nat_shift _ _ n0); [|lia].
    replace (n0 + S n1 - n0) with (S n1) by lia.
    rewrite Nat.add_comm, Nat.mul_comm, Nat.mod_add;
    [|apply Nat.pow_nonzero; easy].
    rewrite Nat.mod_small; [|apply funbool_to_nat_bound].
    easy.
Qed.

Lemma testbit_funbool_to_nat {n0 n} {f} :
  Nat.testbit (funbool_to_nat n0 f) n = if n <? n0 then f (n0 - (S n)) else false.
Proof.
  unfold funbool_to_nat.
  rewrite testbit_binlist.
  gen n0 f;
  induction n; intros n0 f.
  - induction n0.
    + cbn. easy.
    + replace (0 <? S n0) with true by easy.
      cbn.
      rewrite Nat.sub_0_r.
      easy.
  - induction n0.
    + cbn. easy.
    + cbn. rewrite IHn. easy.
Qed.

Lemma list_to_funbool_eq {k : list bool} {n0} :
  (list_to_funbool n0 k) = fun n => if n <=? (n0 - 1) then nth (n0 - S n) k false else false.
Proof.
  gen n0;
  induction k; intros n0.
  - apply functional_extensionality; intros n.
    destruct (n0 - S n); rewrite Tauto.if_same; easy.
  - destruct n0.
    1: apply functional_extensionality; intros n; destruct n; try easy.
      simpl. rewrite IHk.
      unfold update. easy.
    simpl list_to_funbool. 
    rewrite IHk.
    apply functional_extensionality.
    intros n.
    unfold update.
    rewrite Nat.sub_0_r.
    replace (S n0 - 1) with n0 by lia.
    bdestruct (n <=? n0).
    + bdestruct (n =? n0).
      * subst.
        replace (S n0 - S n0) with 0 by lia.
        easy.
      * bdestruct (n <=? n0 - 1); [|lia].
        destruct (S n0 - S n) as [|n'] eqn:Hn'; [lia|].
        simpl nth.
        replace (n0 - S n) with n' by lia.
        easy.
    + bdestruct (n =? n0); subst; try lia.
      bdestruct (n <=? n0 - 1); subst; try lia.
Qed.

Lemma list_to_funbool_eq' {k : list bool} {n0 n} :
  list_to_funbool n0 k n = if n <=? (n0 - 1) then nth (n0 - S n) k false else false.
Proof.
  rewrite list_to_funbool_eq. easy.
Qed.

Lemma nth_nat_to_binlist {len n} : forall k,
  nth k (nat_to_binlist len n) false = Nat.testbit n k.
Proof.
  intros k.
  rewrite <- testbit_binlist, nat_to_binlist_inverse.
  easy.
Qed.

Lemma nat_to_funbool_eq {n j} :
  nat_to_funbool n j = fun k => if k <=? n - 1 then Nat.testbit j (n - S k) else false.
Proof.
  apply functional_extensionality; intros k.
  unfold nat_to_funbool.
  rewrite list_to_funbool_eq', nth_nat_to_binlist.
  easy.
Qed.

Lemma nat_to_funbool_mod {n1 j} {k} (n0:nat) : k < n1 ->
  nat_to_funbool n1 (j mod 2 ^ n1) k = nat_to_funbool (n0 + n1) j (k + n0).
Proof.
  intros Hk.
  rewrite 2!nat_to_funbool_eq.
  bdest_lia_replace (k <=? n1 - 1) true.
  bdest_lia_replace (k + n0 <=? n0 + n1 - 1) true.
  rewrite Nat.mod_pow2_bits_low; [|lia].
  f_equal.
  lia.
Qed.

Lemma nat_to_funbool_div {n0 n1 j} {k} : k < n0 -> 
  nat_to_funbool n0 (j / 2 ^ n1) k = nat_to_funbool (n0 + n1) j k.
Proof.
  intros Hk.
  rewrite 2!nat_to_funbool_eq.
  bdest_lia_replace (k <=? n0 - 1) true.
  bdest_lia_replace (k <=? n0 + n1 - 1) true.
  rewrite Nat.div_pow2_bits.
  f_equal.
  lia.
Qed.

Lemma div_mod_inj {a b} (c:nat) : c > 0 ->
  (a mod c) = (b mod c) /\ (a / c) = (b / c) -> a = b.
Proof.
  intros Hc.
  intros [Hmod Hdiv].
  rewrite (Nat.div_mod_eq a c).
  rewrite (Nat.div_mod_eq b c).
  rewrite Hmod, Hdiv.
  easy.
Qed.

Lemma eqb_iff {b c : bool} :
  b = c <-> ((b = true) <-> (c = true)).
Proof.
  destruct b; destruct c; split;
  intros; try split; auto; lia.
Qed.

Local Close Scope nat.