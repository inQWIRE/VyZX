(* Require Import ZXCore. *)
Require Import CoreRules.
Import CoreData CoreAutomation.
Import CastRules.
From QuantumLib Require Import Bits.
Require Export QuantumLib.Permutations.
Import QuantumLib.VectorStates Modulus Kronecker.

Open Scope nat_scope.

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

#[export] Hint Resolve swap_perm_permutation_alt | 10 : perm_db.

#[export] Hint Extern 100 (WF_Matrix _) => 
  apply WF_Matrix_dim_change : wf_db.

Section VyZX_lemmas.

Import CoreData.

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

Lemma swap_cup : swap × (⟦ ⊂ ⟧) = (⟦ ⊂ ⟧).
Proof.
  change (2*2) with (2^2).
  apply mat_equiv_eq; [auto with wf_db..|].
  by_cell; cbn; lca.
Qed.

Lemma cap_times_cup : 
  (⟦ ⊃ ⟧) × (⟦ ⊂ ⟧) = 2%R .* I (2^0).
Proof.
  apply mat_equiv_eq; [auto with wf_db..].
  unfold scale.
  by_cell; cbv; lca.
Qed.

Lemma cap_cup_yank_eq : 
  I (2 ^ 1) ⊗ (⟦ ⊃ ⟧) × 
  ((⟦ ⊂ ⟧) ⊗ I (2 ^ 1)) = I (2^1).
Proof.
  apply mat_equiv_eq; [auto with wf_db..].
  rewrite kron_I_l, kron_I_r.
  by_cell; cbv; lca.
Qed.

Lemma cap_cap_cup_yank_eq : 
  (⟦ ⊃ ⟧) ⊗ (⟦ ⊃ ⟧) × 
  (I (2 ^ 1) ⊗ (⟦ ⊂ ⟧) ⊗ I (2 ^ 1)) = (⟦ ⊃ ⟧).
Proof.
  apply mat_equiv_eq; [auto using WF_Matrix_dim_change with wf_db..].
  rewrite kron_I_l, kron_I_r.
  by_cell; cbv; lca.
Qed.

Lemma cap_cup_yank_eq_alt : 
  (⟦ ⊃ ⟧) ⊗ I (2 ^ 1) × 
  (I (2 ^ 1) ⊗ (⟦ ⊂ ⟧)) = I (2^1).
Proof.
  apply mat_equiv_eq; [auto with wf_db..].
  rewrite kron_I_l, kron_I_r.
  by_cell; cbv; lca.
Qed.

End VyZX_lemmas.

Section ZXpermLemmas.

Local Open Scope matrix_scope.
Local Open Scope nat_scope.




Definition swap_middle_bits_perm_alt padl padm padr a :=
  fun k =>
  (k / (2^(padr + a + padm + a))) mod (2^padl) * 2 ^ (padr + a + padm + a) +
  (k / (2^(padr))) mod (2^a) * 2 ^ (padr + a + padm) + 
  (k / (2^(padr + a))) mod (2^padm) * 2 ^ (padr + a) +
  (k / (2^(padr + a + padm))) mod (2^a) * 2 ^ padr + 
  k mod (2^padr).


Definition swap_middle_bits_perm padl padm padr a :=
  fun k => 
  funbool_to_nat (padl + a + padm + a + padr)
  (fun i => 
    if i <? padr then nat_to_funbool (padl + a + padm + a + padr) k i
    else if i <? padr + a then nat_to_funbool (padl + a + padm + a + padr) k (i + (padm + a))
    else if i <? padr + a + padm then nat_to_funbool (padl + a + padm + a + padr) k i
    else if i <? padr + a + padm + a then nat_to_funbool (padl + a + padm + a + padr) k (i - (padm + a))
    else nat_to_funbool (padl + a + padm + a + padr) k i).


Lemma swap_middle_bits_perm_eq padl padm padr a : 
  perm_eq (2^(padl + a + padm + a + padr)) 
  (swap_middle_bits_perm padl padm padr a)
  (qubit_perm_to_nat_perm (padl + a + padm + a + padr) 
  (swap_block_perm padr padm a)).
Proof.
  rewrite qubit_perm_to_nat_perm_defn.
  intros k Hk.
  unfold swap_middle_bits_perm.
  apply funbool_to_nat_eq.
  intros j Hj.
  unfold swap_block_perm, Basics.compose.
  bdestruct_all; f_equal; lia.
Qed.

Lemma swap_middle_bits_permutation padl padm padr a : 
  permutation (2 ^ padl * 2 ^ a * 2 ^ padm * 2 ^ a * 2 ^ padr)
  (swap_middle_bits_perm padl padm padr a).
Proof.
  unify_pows_two.
  rewrite swap_middle_bits_perm_eq.
  auto with perm_db.
Qed.

Lemma swap_middle_bits_perm_eq_alt padl padm padr a k :
  swap_middle_bits_perm padr padm padl a k = 
  swap_middle_bits_perm_alt padl padm padr a k.
Proof.
  apply bits_inj.
  unfold swap_middle_bits_perm, swap_middle_bits_perm_alt.
  replace (padr + a + padm + a) with (a + padm + a + padr) by lia.
  replace (padr + a + padm) with (padm + a + padr) by lia.
  replace (padr + a) with (a + padr) by lia.
  rewrite !Nat.pow_add_r.
  intros s.
  rewrite testbit_funbool_to_nat.
  rewrite !Nat.mul_assoc, <- !Nat.mul_add_distr_r.
  rewrite !testbit_add_pow2_split by 
    apply Nat.mod_upper_bound, pow2_nonzero.
  rewrite !testbit_mod_pow2, <- !Nat.pow_add_r, !testbit_div_pow2.
  rewrite !nat_to_funbool_eq.
  bdestructΩ'; f_equal; lia.
Qed.

Lemma swap_middle_bits_perm_perm_eq_alt padl padm padr a :
  perm_eq (2 ^ padl * 2 ^ a * 2 ^ padm * 2 ^ a * 2 ^ padr)
  (swap_middle_bits_perm padr padm padl a)
  (swap_middle_bits_perm_alt padl padm padr a).
Proof.
  intros k _; apply swap_middle_bits_perm_eq_alt.
Qed.

Lemma swap_middle_bits_alt_permutation padl padm padr a : 
  permutation (2 ^ padl * 2 ^ a * 2 ^ padm * 2 ^ a * 2 ^ padr)
  (swap_middle_bits_perm_alt padl padm padr a).
Proof.
  rewrite <- swap_middle_bits_perm_perm_eq_alt.
  eapply permutation_change_dims;
  [|apply swap_middle_bits_permutation].
  lia.
Qed.

End ZXpermLemmas.

#[export] Hint Resolve swap_middle_bits_perm
  swap_middle_bits_perm_alt : perm_db.


Create HintDb biperm_db.

(* Section Bipermutations. *)

Local Open Scope nat.

Definition bipermutation n f :=
  (forall k : nat, k < n -> f k < n /\ f k <> k /\ f (f k) = k).

(* Local Notation perm_surj n f := (forall k, k < n -> exists k', k' < n /\ f k' = k).
Local Notation perm_bounded  n f := (forall k, k < n -> f k < n).
Local Notation perm_inj  n f := (forall k l, k < n -> l < n -> f k = f l -> k = l). *)

Lemma permutation_of_bipermutation {n f} : bipermutation n f -> permutation n f.
Proof.
  intros Hbiperm.
  exists f.
  intros k Hk.
  repeat split.
  all: apply Hbiperm, Hk.
Qed.

#[export] Hint Resolve permutation_of_bipermutation : perm_db biperm_db.

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

Lemma biperm_compose_perm_l_bounded n m f g 
  (Hf : perm_bounded (n + m) f) (Hg : perm_bounded n g) :
  perm_bounded (n + m) (biperm_compose_perm_l n m f g).
Proof.
  unfold biperm_compose_perm_l.
  intros.
  (* pose proof perm_inv_bounded as PB. *)
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
  (* pose proof perm_inv_bounded as PB. *)
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



Section Foliation.

Import CoreRules.

Inductive ZX_elem : forall (n m : nat), Set :=
  | ElemEmpty : ZX_elem 0 0
  | ElemCap : ZX_elem 2 0
  | ElemCup : ZX_elem 0 2
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

Lemma add_assoc_three {a b c : nat} : 
  (a + (b + c) = a + b + c)%nat. 
Proof. lia. Qed.

Lemma add_assoc_four {a b c d} : 
  (a + b + c + d = a + (b + c + d))%nat.
Proof. lia. Qed.

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

Import ZXpermAutomation.

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

End Foliation.

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



Definition number_preserved (i : nat) (f : nat -> nat) (bound : nat) :=
  forallb (fun k => eqb (Nat.testbit i k) 
    (Nat.testbit i (f k))) (seq 0 bound).

Definition matrix_of_biperm (n m : nat) (f : nat -> nat) : Matrix (2^m) (2^n) :=
  fun i j =>
  if 2^m <=? i then C0 else if 2^n <=? j then C0 else
  if number_preserved (j * 2^m + i) 
  (f) (n + m) then C1 else C0.
  (* this order works experimentally... :/ *)

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

Lemma number_preserved_funbool_to_nat f g n 
  (Hf : perm_bounded n f) : 
  number_preserved (funbool_to_nat n g) f n =
  forallb (fun k => eqb (g (n - S k)) (g (n - S (f k)))) (seq 0 n).
Proof.
  apply eq_iff_eq_true.
  rewrite forallb_seq0, number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_funbool_to_nat.
  setoid_rewrite <- eq_eqb_iff.
  apply forall_iff; intros s; apply impl_iff.
  intros Hs.
  replace_bool_lia (s <? n) true.
  specialize (Hf s Hs).
  replace_bool_lia (f s <? n) true.
  easy.
Qed.



Open Scope matrix_scope.

Lemma matrix_of_biperm_WF n m f : 
  WF_Matrix (matrix_of_biperm n m f).
Proof.
  unfold matrix_of_biperm.
  intros i j.
  bdestructΩ'.
Qed.

Hint Resolve matrix_of_biperm_WF : wf_db.

Lemma matrix_of_biperm_funbool_conj f g h n m :
  ((f_to_vec m g) ⊤ × matrix_of_biperm n m f × f_to_vec n h) 0 0 = 
  (if number_preserved (funbool_to_nat (n + m)
    (fun k => if k <? n then h k else g (k - n)))
    f (n + m) then 1%R else 0%R).
Proof.
  rewrite 2!basis_f_to_vec.
  rewrite matrix_conj_basis_eq_lt by apply funbool_to_nat_bound.
  unfold matrix_of_biperm.
  rewrite funbool_to_nat_add_pow2_join.
  pose proof (funbool_to_nat_bound m g).
  pose proof (funbool_to_nat_bound n h).
  bdestructΩ'.
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

Lemma matrix_of_biperm_transpose n m f (Hf : bipermutation (n + m) f) : 
  (matrix_of_biperm m n f) ⊤ ≡
  (matrix_of_biperm n m (flip_biperm n m f)).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  intros i j Hi Hj.
  unfold Matrix.transpose.
  unfold matrix_of_biperm.
  do 2 simplify_bools_lia_one_kernel.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite 2!number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_add_pow2_split; [|easy..].
  split.
  - intros H s Hs.
    unfold flip_biperm.
    simplify_bools_lia_one_kernel.
    bdestruct (s <? m).
    + generalize (H (s + n) ltac:(lia)).
      pose proof (Hfbdd (s + n) ltac:(lia)).
      do 2 simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub.
      intros ->.
      bdestructΩ'.
      f_equal; lia.
    + generalize (H (s - m) ltac:(lia)).
      simplify_bools_lia_one_kernel.
      intros ->.
      pose proof (Hfbdd (s - m) ltac:(lia)).
      simplify_bools_lia_one_kernel.
      bdestructΩ'; f_equal; lia.
  - intros H s Hs.
    bdestruct (s <? n).
    + generalize (H (s + m) ltac:(lia)).
      pose proof (Hfbdd (s) ltac:(lia)).
      unfold flip_biperm.
      do 2 simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub.
      intros ->.
      bdestructΩ'.
      f_equal; lia.
    + generalize (H (s - n) ltac:(lia)).
      simplify_bools_lia_one_kernel.
      intros ->.
      pose proof (Hfbdd (s) ltac:(lia)).
      unfold flip_biperm.
      simplify_bools_lia_one_kernel.
      rewrite Nat.sub_add by lia.
      bdestructΩ'; f_equal; lia.
Qed.

Lemma matrix_of_biperm_transpose_eq n m f (Hf : bipermutation (n + m) f) : 
  (matrix_of_biperm m n f) ⊤ =
  (matrix_of_biperm n m (flip_biperm n m f)).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  now apply matrix_of_biperm_transpose.
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


Lemma number_preserved_compose_cap_l_neq {padl padr m} {i j} {f} 
  (* (Hpadr : padr <> 0) *)
  (Hf : bipermutation (padl + 2 + padr + m) f) 
  (Hi : i < 2 ^ m) (Hj : j < 2 ^ (padl + 0 + padr)) 
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
  assert (HSmpne : f (S (m + padl)) <> S (m + padl)) by (apply Hfne; lia).
  assert (Hmpne : f (m + padl) <> (m + padl)) by (apply Hfne; lia).
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
    bdestruct (s =? f (m + padl)); [|bdestruct (s =? f (S (m + padl)))].
    + rewrite <- eq_eqb_iff.
      pose proof (Hfbdd s ltac:(easy)).
      replace <- (f (m + padl)).
      specialize (H (if (s <? m + padl) then s else s - 2) ltac:(bdestructΩ')).
      revert H.
      assert (f s = m + padl) by 
      (apply (bipermutation_eq_iff _ _ Hf); easy + lia).
      assert (f (S (m + padl)) <> m + padl) by lia.
      assert (f (S (m + padl)) <> S (m + padl)) by (apply Hfne; lia).
      bdestruct (s <? m); [|
      replace_bool_lia (s - m <? padl) (s <? m + padl);
      bdestruct (s <? m + padl)].
      * replace_bool_lia (s <? m + padl) true.
        replace_bool_lia (s <? m) true.
        intros ->.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s) false.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (m + padl =? f s) true.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        simpl.
        bdestruct (S (m + padl) <? f (S (m + padl))).
        1 :{
          replace_bool_lia (f (S (m + padl)) <? m) false.
          replace_bool_lia (f (S (m + padl)) - m <? padl) false.
          replace_bool_lia (f (S (m + padl)) - 2 <? m) false.
          bdestructΩ'; f_equal; lia.
        }
        bdestruct (f (S (m + padl)) <? m); [easy|].
        bdestruct (f (S (m + padl)) - m <? padl); [easy|].
        bdestructΩ'.
      * replace_bool_lia (s <? m) false.
        intros ->.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s) false.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (m + padl =? f s) true.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        bdestruct (S (m + padl) <? f (S (m + padl))).
        1 :{
          simpl.
          replace_bool_lia (f (S (m + padl)) <? m) false.
          replace_bool_lia (f (S (m + padl)) - m <? padl) false.
          replace_bool_lia (f (S (m + padl)) - 2 <? m) false.
          bdestructΩ'; f_equal; lia.
        }
        simpl.
        bdestructΩ'.
      * replace_bool_lia (s - 2 <? m) false.
        replace_bool_lia (s - m <? 2 + padl) false.
        replace (s - 2 - m) with (s - m - 2) by lia.
        intros ->.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s - 2) true.
        rewrite Nat.add_sub_assoc, add_sub' by lia.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (m + padl =? f s) true.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        simpl.
        bdestructΩ'.
        f_equal; lia.
    + rewrite <- eq_eqb_iff.
      pose proof (Hfbdd s ltac:(easy)).
      rewrite !(testbit_add_pow2_split i) by lia.
      simpl.
      replace <- (f (S (m + padl))).
      rewrite 2!testbit_make_2_gap'.
      specialize (H (if (s <? m + padl) then s else s - 2) ltac:(bdestructΩ')).
      revert H.
      assert (f s = S (m + padl)) by 
        (apply (bipermutation_eq_iff _ _ Hf); easy + lia).

      bdestruct (s <? m); [|
      replace_bool_lia (s - m <? padl) (s <? m + padl);
      bdestruct (s <? m + padl)].
      * replace_bool_lia (s <? m + padl) true.
        replace_bool_lia (s <? m) true.
        intros ->.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s) false.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        replace_bool_lia (m + padl =? f s) false.
        replace_bool_lia (S (m + padl) =? f s) true.
        simpl.
        bdestruct (S (m + padl) <? f (m + padl)).
        1 :{
          replace_bool_lia (f (m + padl) <? m) false.
          replace_bool_lia (f (m + padl) - m <? padl) false.
          replace_bool_lia (f (m + padl) - 2 <? m) false.
          bdestructΩ'; f_equal; lia.
        }
        bdestruct (f (m + padl) <? m); [easy|].
        bdestruct (f (m + padl) - m <? padl); [easy|].
        bdestructΩ'.
      * replace_bool_lia (s <? m) false.
        intros ->.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s) false.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (S (m + padl) =? f s) true.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        replace_bool_lia (m + padl =? f s) false.
        bdestruct (S (m + padl) <? f (m + padl)).
        1 :{
          simpl.
          replace_bool_lia (f (m + padl) <? m) false.
          replace_bool_lia (f (m + padl) - m <? padl) false.
          replace_bool_lia (f (m + padl) - 2 <? m) false.
          bdestructΩ'; f_equal; lia.
        }
        simpl.
        bdestructΩ'.
      * replace_bool_lia (s - 2 <? m) false.
        replace_bool_lia (s - m <? 2 + padl) false.
        replace (s - 2 - m) with (s - m - 2) by lia.
        intros ->.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s - 2) true.
        rewrite Nat.add_sub_assoc, add_sub' by lia.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (m + padl =? f s) false.
        replace_bool_lia (S (m + padl) =? f s) true.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        simpl.
        bdestructΩ'.
        f_equal; lia.
    + rewrite <- eq_eqb_iff.
      pose proof (Hfbdd s ltac:(easy)).
      assert (f s <> S (m + padl)) by 
        (rewrite (bipermutation_eq_iff _ _ Hf); easy + lia).
      assert (f s <> (m + padl)) by 
        (rewrite (bipermutation_eq_iff _ _ Hf); easy + lia).
      rewrite !(testbit_add_pow2_split i) by lia.
      rewrite 2!testbit_make_2_gap'.
      specialize (H (if (s <? m + padl) then s else s - 2) ltac:(bdestructΩ')).
      revert H.
      bdestruct (s <? m); [|
      replace_bool_lia (s - m <? padl) (s <? m + padl);
      bdestruct (s <? m + padl)];
      [ replace_bool_lia (s <? m + padl) true; 
        replace_bool_lia (s <? m) true
      | replace_bool_lia (s <? m) false
      | replace_bool_lia (s - 2 <? m) false;
        replace_bool_lia (s - m <? 2 + padl) false;
        replace (s - 2 - m) with (s - m - 2) by lia
      ]; intros ->;
        unfold compose_cap_biperm_l;
        [replace_bool_lia (m + padl <=? s) false |
        replace_bool_lia (m + padl <=? s) false |
        replace_bool_lia (m + padl <=? s - 2) true];
        unfold compose_cap_biperm_l_prefun;
        [| | replace (2 + (s - 2)) with s by lia];
        replace_bool_lia (s =? m + padl) false;
        replace_bool_lia (S (m + padl) =? s) false;
        replace_bool_lia (m + padl =? f s) false;
        replace_bool_lia (S (m + padl) =? f s) false;
        simpl;
        (bdestruct (S (m + padl) <? f s); 
        [replace_bool_lia (f s <? m) false;
        replace_bool_lia (f s - m <? padl) false;
        replace_bool_lia (f s - 2 <? m) false;
        bdestructΩ'; f_equal; try lia|]);
        (bdestruct (f s <? m); [easy|]);
        (bdestruct (f s - m <? padl); [easy|]);
        lia.
  - intros H.
    intros s Hs.
    do 2 setoid_rewrite (fun j => testbit_add_pow2_split i j m Hi) in H.
    do 2 setoid_rewrite testbit_make_2_gap' in H.
    unfold compose_cap_biperm_l.
    bdestruct (s <? m); [|bdestruct (m + padl <=? s)].
    + specialize (H s ltac:(lia)).
      revert H.
      replace_bool_lia (s <? m) true.
      replace_bool_lia (s =? m + padl) false.
      replace_bool_lia (s =? S (m + padl)) false.
      simpl.
      bdestruct (s =? f (m + padl)); 
      [ replace <- (f (m + padl))
      | bdestruct (s =? f (S (m + padl)));
      [ replace <- (f (S (m + padl))) | ]];
      rewrite <- eq_eqb_iff.
      * replace_bool_lia (s <? m) true.
        intros ->.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s) false.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        assert (f s = m + padl) by 
          (apply (bipermutation_eq_iff _ _ Hf); easy + lia).
        replace_bool_lia (m + padl =? f s) true.
        bdestructΩ'; f_equal; lia.
      * replace_bool_lia (s <? m) true.
        intros <-.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s) false.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        assert (f s = S (m + padl)) by 
          (apply (bipermutation_eq_iff _ _ Hf); easy + lia).
        replace_bool_lia (m + padl =? f s) false.
        replace_bool_lia (S (m + padl) =? f s) true.
        bdestructΩ'; f_equal; lia.
      * intros ->.
        unfold compose_cap_biperm_l.
        replace_bool_lia (m + padl <=? s) false.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        assert (f s <> S (m + padl)) by 
          (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
        assert (f s <> m + padl) by 
          (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
        replace_bool_lia (m + padl =? f s) false.
        replace_bool_lia (S (m + padl) =? f s) false.
        bdestructΩ'; f_equal; lia.
    + specialize (H (2 + s) ltac:(lia)).
      revert H.
      replace_bool_lia (2 + s =? m + padl) false.
      replace_bool_lia (2 +s =? S (m + padl)) false.
      change (S m + padl) with (S (m + padl)).
      bdestruct (2 + s =? f (m + padl)); 
      [ replace <- (f (m + padl))
      | bdestruct (2 + s =? f (S (m + padl)));
      [ replace <- (f (S (m + padl))) | ]];
      rewrite <- eq_eqb_iff;
      (replace_bool_lia (2 + s <? m) false;
      replace_bool_lia (2 + s - m <? padl) false;
      replace_bool_lia (2 + s - m <? 2 + padl) false;
      replace (2 + s - m - 2) with (s - m) by lia).
      * intros ->.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (2 + s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? 2 + s) false.
        assert (f (2 + s) = m + padl) by 
          (apply (bipermutation_eq_iff _ _ Hf); easy + lia).
        replace_bool_lia (m + padl =? f (2 + s)) true.
        bdestructΩ'; f_equal; lia.
      * intros <-.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (2 + s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? 2 + s) false.
        assert (f (2 + s) = S (m + padl)) by 
          (apply (bipermutation_eq_iff _ _ Hf); easy + lia).
        replace_bool_lia (m + padl =? f (2 + s)) false.
        replace_bool_lia (S (m + padl) =? f (2 + s)) true.
        bdestructΩ'; f_equal; lia.
      * intros ->.
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia ((2 + s) =? m + padl) false.
        replace_bool_lia (S (m + padl) =? (2 + s)) false.
        assert (f (2 + s) <> S (m + padl)) by 
          (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
        assert (f (2 + s) <> m + padl) by 
          (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
        replace_bool_lia (m + padl =? f (2 + s)) false.
        replace_bool_lia (S (m + padl) =? f (2 + s)) false.
        bdestructΩ'; f_equal; lia.
    + specialize (H s ltac:(lia)).
      revert H.
      replace_bool_lia (s <? m) false.
      replace_bool_lia (s =? m + padl) false.
      replace_bool_lia (s =? S (m + padl)) false.
      replace_bool_lia (s - m <? padl) true.
      simpl.
      bdestruct (s =? f (m + padl)); 
      [ replace <- (f (m + padl))
      | bdestruct (s =? f (S (m + padl)));
      [ replace <- (f (S (m + padl))) | ]];
      rewrite <- eq_eqb_iff;
      replace_bool_lia (s <? m) false;
      replace_bool_lia (s - m <? padl) true;
      [intros -> | intros <- | intros ->].
      * assert (f s = m + padl) by 
          (apply (bipermutation_eq_iff _ _ Hf); easy + lia).
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        replace_bool_lia (m + padl =? f s) true.
        bdestructΩ'; f_equal; lia.
      * assert (f s = S (m + padl)) by 
          (apply (bipermutation_eq_iff _ _ Hf); easy + lia).
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        replace_bool_lia (m + padl =? f s) false.
        replace_bool_lia (S (m + padl) =? f s) true.
        bdestructΩ'; f_equal; lia.
      * 
        unfold compose_cap_biperm_l_prefun.
        replace_bool_lia (s =? m + padl) false.
        replace_bool_lia (S (m + padl) =? s) false.
        assert (f s <> S (m + padl)) by 
          (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
        assert (f s <> m + padl) by 
          (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
        replace_bool_lia (m + padl =? f s) false.
        replace_bool_lia (S (m + padl) =? f s) false.
        bdestructΩ'; f_equal; lia.
Qed.

Lemma number_preserved_compose_cap_l_either_impl_ne padl padr m f i j  
  (Hf : bipermutation (padl + 2 + padr + m) f) 
  (Hi : i < 2 ^ m) (Hj : j < 2 ^ (padl + 0 + padr))
  (Hfpadl : f (m + padl) <> S (m + padl)) : 
  number_preserved
    ((j / 2 ^ padl * 4 * 2 ^ padl + j mod 2 ^ padl) * 2 ^ m + i) f
    (padl + 2 + padr + m)
  || number_preserved
      (((j / 2 ^ padl * 4 + 3) * 2 ^ padl + j mod 2 ^ padl) *
        2 ^ m + i) f (padl + 2 + padr + m) = true -> 
  number_preserved (j * 2 ^ m + i)
    (compose_cap_biperm_l (m + padl) f) (padl + 0 + padr + m) = true.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  assert (HfSpadl : f (S (m + padl)) <> m + padl) by
    (intros Hfalse; rewrite <- Hfalse, Hfeq in Hfpadl; lia).
  assert (HSmpne : f (S (m + padl)) <> S (m + padl)) by (apply Hfne; lia).
  assert (Hmpne : f (m + padl) <> (m + padl)) by (apply Hfne; lia).
  rewrite orb_true_iff.
  intros [Hl | Hr].
  - rewrite number_preserved_compose_cap_l_neq by easy.
    cbn zeta.
    rewrite forallb_seq0.
    intros s Hs.
    bdestruct (s =? m + padl); [easy|].
    bdestruct (s =? S (m + padl)); [easy|].
    rewrite number_preserved_iff_all_lt_eq in Hl.
    rewrite <- 3!Hl by lia.
    rewrite eqb_reflx.
    rewrite !(testbit_add_pow2_split i _ _ Hi).
    rewrite add_sub'.
    replace (S m + padl - m) with (S padl) by lia.
    rewrite !testbit_make_2_gap'.
    simpl.
    replace_bool_lia (m + padl <? m) false.
    replace_bool_lia (padl <? padl) false.
    replace_bool_lia (padl <? S (S padl)) true.
    replace_bool_lia (S padl <? padl) false.
    bdestructΩ'.
  - rewrite number_preserved_iff_all_lt_eq in Hr.
    setoid_rewrite (testbit_add_pow2_split i _ _ Hi) in Hr.
    setoid_rewrite number_preserved_compose_cap_l_eq_helper in Hr.
    setoid_rewrite testbit_make_2_gap' in Hr.
    pose proof (Hr (m + padl) ltac:(lia)) as Hmp.
    revert Hmp.
    replace_bool_lia (m + padl <? m) false.
    rewrite add_sub'.
    rewrite Nat.eqb_refl.
    simpl.
    intros Hmp.
    
    pose proof (Hr (S (m + padl)) ltac:(lia)) as HSmp.
    revert HSmp.
    replace_bool_lia (S (m + padl) <? m) false.
    replace_bool_lia ((S (m + padl) - m =? padl)) false.
    replace_bool_lia (S (m + padl) - m =? S padl) true.
    simpl.
    intros HSmp.
    rewrite number_preserved_compose_cap_l_neq by easy.

    cbn zeta.
    rewrite forallb_seq0.
    intros s Hs.
    rewrite !(testbit_add_pow2_split i _ _ Hi).
    rewrite !testbit_make_2_gap'.
    simpl.
    bdestruct (s =? m + padl); [easy|].
    bdestruct (s =? S (m + padl)); [easy|].
    bdestruct (s =? f (m + padl)); 
    [|bdestruct (s =? f (S (m + padl)))]; rewrite <- eq_eqb_iff.
    + rewrite Hmp in HSmp at 1.
      revert HSmp.
      repeat (bdestruct_one; subst;
      try (intros ->); try (intros <-); try lia; try reflexivity).
    + rewrite Hmp in HSmp at 1.
      revert HSmp.
      repeat (bdestruct_one; subst;
      try (intros ->); try (intros <-); try lia; try reflexivity).
    + assert (f s <> S (m + padl)) by 
        (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
      assert (f s <> m + padl) by 
        (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
      specialize (Hr s ltac:(lia)).
      revert Hr.
      replace_bool_lia (s - m =? S padl) false.
      repeat (bdestruct_one; subst; simpl;
      try (intros ->); try (intros <-); try lia; try reflexivity).
Qed.

Lemma number_preserved_compose_cap_l_impl_either_ne padl padr m f i j  
  (Hf : bipermutation (padl + 2 + padr + m) f) 
  (Hi : i < 2 ^ m) (Hj : j < 2 ^ (padl + 0 + padr))
  (Hfpadl : f (m + padl) <> S (m + padl)) : 
  number_preserved (j * 2 ^ m + i)
  (compose_cap_biperm_l (m + padl) f) (padl + 0 + padr + m) = true ->
  number_preserved
    ((j / 2 ^ padl * 4 * 2 ^ padl + j mod 2 ^ padl) * 2 ^ m + i) f
    (padl + 2 + padr + m)
  || number_preserved
      (((j / 2 ^ padl * 4 + 3) * 2 ^ padl + j mod 2 ^ padl) *
        2 ^ m + i) f (padl + 2 + padr + m) = true.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  assert (HfSpadl : f (S (m + padl)) <> m + padl) by
    (intros Hfalse; rewrite <- Hfalse, Hfeq in Hfpadl; lia).
  assert (HSmpne : f (S (m + padl)) <> S (m + padl)) by (apply Hfne; lia).
  assert (Hmpne : f (m + padl) <> (m + padl)) by (apply Hfne; lia).
  intros H.
  pose proof H as H'.
  rewrite number_preserved_compose_cap_l_neq in H by easy.
  cbn zeta in H.
  rewrite forallb_seq0 in H.
  rewrite orb_true_iff.
  rewrite number_preserved_iff_all_lt_eq in H'.
  
  pose proof (H (f (m + padl)) ltac:(apply Hfbdd; lia)) as HfmpS.
  revert HfmpS.
  replace_bool_lia (f (m + padl) =? m + padl) false.
  replace_bool_lia (f (m + padl) =? S (m + padl)) false.
  rewrite Nat.eqb_refl, <- eq_eqb_iff.
  intros HfmpS.

  destruct (
  Nat.testbit ((j / 2 ^ padl * 4 * 2 ^ padl + j mod 2 ^ padl) * 2 ^ m + i)
  (f (m + padl))
  ) eqn:e.
  pose proof ( HfmpS) as e'.
  1: { right.
  rewrite number_preserved_iff_all_lt_eq.
  intros s Hs.
  rewrite !(testbit_add_pow2_split _ _ _ Hi) in *.
  rewrite !number_preserved_compose_cap_l_eq_helper.
  rewrite !testbit_make_2_gap' in *.
  bdestruct (f (m + padl) =? s); [|
  bdestruct (f (S (m + padl)) =? s); [bdestruct (s <? m)|]].
  + repeat (bdestruct_one; subst; simpl; 
    try rewrite Hfeq in * by lia;
    try (intros ->); try (intros <-); try lia; try reflexivity);
    revert e; bdestructΩ'.
  + replace <- s.
    rewrite Hfeq by lia.
    replace_bool_lia (S (m + padl) <? m) false.
    replace_bool_lia (S (m + padl) - m =? padl) false.
    replace_bool_lia (S (m + padl) - m =? S padl) true.
    simpl in *.
    revert e'. 
    bdestructΩ'.
  + replace_bool_lia (s - m =? padl) false.
    replace_bool_lia (s - m =? S padl) false.
    simpl.
    replace <- s.
    rewrite Hfeq by lia.
    simpl in e'.
    revert e'.
    bdestructΩ'.
  + assert (f s <> S (m + padl)) by 
      (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
    assert (f s <> m + padl) by 
      (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
    bdestruct (s <? m); [
    | bdestruct (s - m =? padl) ; [
    | bdestruct (s - m =? S padl)]].
    * specialize (H s ltac:(lia)).
      revert H.
      replace_bool_lia (s =? f (m + padl)) false.
      replace_bool_lia (s =? f (S (m + padl))) false.
      replace_bool_lia (s =? (m + padl)) false.
      replace_bool_lia (s =? (S (m + padl))) false.
      rewrite <-eq_eqb_iff.
      rewrite !(testbit_add_pow2_split _ _ _ Hi) in *.
      rewrite !testbit_make_2_gap' in *.
      replace_bool_lia (s <? m) true.
      intros ->.
      bdestructΩ'. 
    * simpl.
      replace s with (m + padl) in * by lia.
      revert e.
      bdestructΩ'.
    * simpl.
      replace s with (S (m + padl)) in * by lia.
      simpl in *.
      revert e';
      bdestructΩ'.
    * simpl. 
      specialize (H s ltac:(lia)).
      revert H.
      replace_bool_lia (s =? f (m + padl)) false.
      replace_bool_lia (s =? f (S (m + padl))) false.
      replace_bool_lia (s =? (m + padl)) false.
      replace_bool_lia (s =? (S (m + padl))) false.
      rewrite !(testbit_add_pow2_split _ _ _ Hi) in *.
      rewrite !testbit_make_2_gap' in *.
      rewrite <- eq_eqb_iff.
      replace_bool_lia (s <? m) false.
      bdestructΩ'.
  } 
  left.
  rewrite number_preserved_iff_all_lt_eq.
  intros s Hs.
  pose proof HfmpS as e'.
  bdestruct (f (m + padl) =? s); [|
  bdestruct (f (S (m + padl)) =? s); [bdestruct (s <? m)|]].
  + subst s.
    rewrite Hfeq by lia.
    rewrite !(testbit_add_pow2_split _ _ _ Hi) in *.
    rewrite !testbit_make_2_gap' in *.
    repeat (bdestruct_one; subst; simpl; 
    try rewrite Hfeq in * by lia;
    try (intros ->); try (intros <-); try lia; try reflexivity);
    revert e; bdestructΩ'.
  + replace <- s.
    rewrite Hfeq by lia.
    rewrite !(testbit_add_pow2_split _ _ _ Hi) in *.
    rewrite !testbit_make_2_gap' in *.
    replace_bool_lia (S (m + padl) <? m) false.
    change (S m + padl) with (S (m + padl)) in *.
    revert e'. 
    bdestructΩ'.
  + rewrite !(testbit_add_pow2_split _ _ _ Hi) in *.
    rewrite !testbit_make_2_gap' in *.
    simpl.
    replace <- s.
    rewrite Hfeq by lia.
    simpl in e'.
    revert e'.
    bdestructΩ'.
  + assert (f s <> S (m + padl)) by 
      (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
    assert (f s <> m + padl) by 
      (intros K; apply (bipermutation_eq_iff _ _ Hf) in K; easy + lia).
    bdestruct (s =? (m + padl)); 
      [|bdestruct (s =? (S (m + padl)))].
    * simpl.
      subst s.
      rewrite e.
      rewrite !(testbit_add_pow2_split _ _ _ Hi).
      rewrite !testbit_make_2_gap'.
      bdestructΩ'.
    * simpl in *.
      subst s.
      rewrite <- e'.
      rewrite !(testbit_add_pow2_split _ _ _ Hi).
      rewrite !testbit_make_2_gap'.
      bdestructΩ'.
    * specialize (H s ltac:(lia)).
      revert H.
      bdestructΩ'.
      rewrite <-eq_eqb_iff.
      easy.
Qed.

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
  setoid_rewrite number_preserved_compose_cap_l_eq_helper.
  setoid_rewrite testbit_make_2_gap'.
  apply forall_iff; intros s; apply impl_iff; intros Hs.
  pose proof (bipermutation_eq_iff s (m + padl) Hf ltac:(lia) ltac:(lia)).
  pose proof (bipermutation_eq_iff s (S (m + padl)) Hf ltac:(lia) ltac:(lia)).
  bdestruct (s <? m).
  - bdestruct (f s <? m); [easy|].
    replace_bool_lia (f s - m =? padl) false.
    replace_bool_lia (f s - m =? S padl) false.
    simpl.
    easy.
  - replace_bool_lia (s - m =? padl) (f s =? S (m + padl)).
    replace_bool_lia (s - m =? S padl) (f s =? m + padl).
    repeat (bdestruct_one; subst; simpl;
    try (intros ->); try (intros <-); try lia; try reflexivity).
Qed.

Lemma matrix_of_compose_cap_biperm_l padl padr m f 
  (Hf : bipermutation (padl + 2 + padr + m) f)
  (* (Hne : f (m + padl) <> S (m + padl)) *) : 
  mat_equiv (
    (if (f (m + padl) =? S (m + padl)) then 2%R else 1%R) .*
  (matrix_of_biperm (padr + 0 + padl) m
  (compose_cap_biperm_l (m + padl) f)))
  ((matrix_of_biperm (padr + 2 + padl) m f 
  × ((I (2^padr) ⊗ ⟦⊂⟧) ⊗ I (2^padl)))).
Proof.
  rewrite !Nat.pow_add_r.
  rewrite kron_I_l, kron_I_r.
  intros i j Hi Hj.
  unfold Mmult.
  rewrite (big_sum_eq_bounded _
  (fun k => (matrix_of_biperm (padr + 2 + padl) m f i k * if 
    (k =? (j / 2 ^ padl) * 4 * 2 ^ padl + j mod 2 ^ padl) ||
    (k =? ((j / 2 ^ padl) * 4 + 3) * 2 ^ padl + j mod 2 ^ padl)
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
        rewrite (Nat.div_mod k (2^padl)) by (apply Nat.pow_nonzero; easy).
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
        rewrite (Nat.div_mod k (2^padl)) by (apply Nat.pow_nonzero; easy).
        f_equal; [|easy].
        rewrite Nat.mul_comm.
        f_equal.
        rewrite (Nat.div_mod (k / 2 ^ padl) (2^2) ltac:(easy)).
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
    simplify_bools_lia.
    rewrite !Nat.pow_add_r.
    simplify_bools_lia_one_kernel.
    rewrite Cmult_if_if_1_l. 
    rewrite andb_comm, andb_if.
    reflexivity.
  }
  rewrite (@big_sum_if_or_eq_ne C C_is_monoid C_is_group C_is_comm_group) by lia.
  assert ((j / 2 ^ padl * 4 + 3) * 2 ^ padl + j mod 2 ^ padl <
    2 ^ padr * 2 ^ 2 * 2 ^ padl).
  1: {
    replace (2 ^ padr * 2 ^ 2 * 2 ^ padl) with 
    ((2 ^ padr * 2 ^ 2 - 1) * 2 ^ padl + 2 ^ padl).
    2: {
      rewrite <- (Nat.mul_1_l (2^padl)) at 2.
      rewrite <- Nat.mul_add_distr_r.
      f_equal.
      cbn.
      lia.
    }
    pose proof (Nat.mod_upper_bound j (2^padl) ltac:(lia)).
    enough ((j / 2 ^ padl * 4 + 3) * 2 ^ padl <=
      (2 ^ padr * 2 ^ 2 - 1) * 2 ^ padl) by lia.
    apply Nat.mul_le_mono_r.
    cbn.
    rewrite <- !Nat.pow_add_r, Nat.add_0_r in Hj.
    assert (j / 2 ^ padl < 2 ^ padr) by 
    (apply Nat.Div0.div_lt_upper_bound; 
      rewrite <- Nat.pow_add_r, Nat.add_comm; lia).
    lia.
  } 
  replace_bool_lia (j / 2 ^ padl * 4 * 2 ^ padl + j mod 2 ^ padl <?
    2 ^ padr * 2 ^ 2 * 2 ^ padl) true.
  replace_bool_lia ((j / 2 ^ padl * 4 + 3) * 2 ^ padl + j mod 2 ^ padl <?
  2 ^ padr * 2 ^ 2 * 2 ^ padl) true.
  rewrite <- 2!Nat.pow_add_r in Hj.
  replace (padr + 0 + padl) with (padl + 0 + padr) in * by lia.
  replace (padr + 2 + padl) with (padl + 2 + padr) in * by lia.
  unfold scale.
  bdestruct (f (m + padl) =? S (m + padl)).
  - rewrite number_preserved_compose_cap_l_eq_12 by easy.
    rewrite <- number_preserved_compose_cap_l_eq_1 by easy.
    bdestructΩ'; lca.    
  - rewrite add_if_exclusive_join_C by 
      (apply (number_preserved_compose_cap_l_neq_parts Hf Hi Hj ltac:(easy))).
    Csimpl.
    simplify_bools_lia.
    apply f_equal_if; [|easy..].
    apply eq_iff_eq_true.
    split.
    + apply number_preserved_compose_cap_l_impl_either_ne; easy.
    + apply number_preserved_compose_cap_l_either_impl_ne; easy.
Qed.

Lemma number_preserved_compose_cup_l padl padr m f 
  (Hf : bipermutation (padl + 0 + padr + m) f) i 
  (Hi : i < 2 ^ m) j :
  number_preserved (j * 2^m + i) 
    (compose_cup_biperm_l (m + padl) f) (padl + 2 + padr + m) =
  number_preserved (((j / 2^padl / 4) * 2^padl + (j mod 2^padl))*2^m + i) 
    f (padl + 0 + padr + m) &&
  eqb (Nat.testbit j padl) (Nat.testbit j (S padl)).
Proof.
  rewrite eq_iff_eq_true.
  rewrite andb_true_iff, <- eq_eqb_iff.
  rewrite 2!number_preserved_iff_all_lt_eq.
  setoid_rewrite (testbit_add_pow2_split _ _ _ Hi).
  setoid_rewrite testbit_remove_2_gap'.
  split.
  - intros H.
    split.
    + intros s Hs.
      bdestruct (s <? m + padl).
      * specialize (H s ltac:(lia)).
        revert H.
        unfold compose_cup_biperm_l.
        bdestructΩ'; intros ->; f_equal; lia.
      * specialize (H (s + 2) ltac:(lia)).
        revert H.
        replace_bool_lia (s <? m) false.
        replace_bool_lia (s - m <? padl) false.
        replace (s + 2 - m) with (s - m + 2) by lia.
        unfold compose_cup_biperm_l.
        rewrite Nat.add_sub.
        bdestructΩ'; intros ->; f_equal; lia.
    + specialize (H (m + padl) ltac:(lia)). 
      revert H. 
      unfold compose_cup_biperm_l.
      rewrite add_sub'.
      bdestructΩ'; intros ->; f_equal; lia.
  - intros [H Hpad].
    intros s Hs.
    bdestruct (s <? m + padl); 
    [|bdestruct (s =? m + padl); 
    [|bdestruct (s =? S (m + padl))]].
    + specialize (H s ltac:(lia)).
      revert H.
      unfold compose_cup_biperm_l.
      bdestructΩ'; intros ->; f_equal; lia.
    + subst.
      unfold compose_cup_biperm_l.
      rewrite add_sub'.
      bdestructΩ'; rewrite Hpad; f_equal; lia.
    + subst.
      unfold compose_cup_biperm_l.
      bdestructΩ'; rewrite add_sub', Hpad; f_equal; lia.
    + specialize (H (s - 2) ltac:(lia)).
      revert H.
      unfold compose_cup_biperm_l.
      replace (s - 2 - m + 2) with (s - m) by lia.
      bdestructΩ';
      intros ->; f_equal; lia.
Qed.

Lemma matrix_of_compose_cup_biperm_l padl padr m f 
  (Hf : bipermutation (padl + 0 + padr + m) f)
   : 
  mat_equiv (matrix_of_biperm (padr + 2 + padl) m
  (compose_cup_biperm_l (m + padl) f))
  ((matrix_of_biperm (padr + 0 + padl) m f 
  × ((I (2^padr) ⊗ ⟦⊃⟧) ⊗ I (2^padl)))).
Proof.
  rewrite !Nat.pow_add_r.
  pose proof (Nat.pow_nonzero) as Hnz.
  rewrite kron_I_l, kron_I_r.
  intros i j Hi Hj.
  unfold Mmult.
  rewrite (big_sum_eq_bounded _
  (fun k => if 
    (k =? (j / 2 ^ padl) / 2 ^ 2 * 2 ^ padl + j mod 2 ^ padl) 
      && eqb (Nat.testbit j padl) (Nat.testbit j (S padl))
  then (matrix_of_biperm (padl + 0 + padr) m f i k) else C0)).
  2: {
    intros k Hk.
    rewrite <- andb_if.
    rewrite cup_semantics.
    rewrite <- orb_if, <- 2!andb_if.
    rewrite (if_dist _ _ _ (fun x => 
      Cmult (matrix_of_biperm _ _ _ _ _) x)).
    rewrite Cmult_0_r, Cmult_1_r.
    apply f_equal_if; [|easy + f_equal; lia..].
    rewrite Nat.pow_0_r, Nat.mod_1_r, Nat.eqb_refl, andb_true_r.
    rewrite Nat.div_1_r.
    f_equal.
    - apply eq_iff_eq_true.
      rewrite andb_true_iff.
      rewrite !Nat.eqb_eq.
      split.
      + intros [Hkmod Hkdiv].
        rewrite (Nat.div_mod k (2^padl)) by (apply Hnz;lia).
        lia. 
      + intros ->.
        rewrite Nat.add_comm.
        rewrite Nat.Div0.mod_add, Nat.Div0.mod_mod.
        split; [easy|].
        rewrite Nat.div_add by (apply Hnz;lia).
        rewrite Nat.div_small by (apply Nat.mod_upper_bound, Hnz;lia).
        lia.
    - apply eq_iff_eq_true.
      rewrite orb_true_iff, !Nat.eqb_eq.
      rewrite <- eq_eqb_iff.
      rewrite 2!Nat.testbit_eqb.
      change (2^2) with (2*2).
      rewrite Nat.Div0.mod_mul_r.
      rewrite Nat.Div0.div_div.
      pose proof (Nat.mod_upper_bound (j / 2 ^ padl) 2 ltac:(easy)).
      pose proof (Nat.mod_upper_bound (j / (2 ^ padl * 2)) 2 ltac:(easy)).
      assert (Hrw: (j / 2 ^ padl) mod 2 +
      2 * ((j / (2 ^ padl * 2)) mod 2) = 0 <-> 
      (j / 2 ^ padl) mod 2 = 0 /\ ((j / (2 ^ padl * 2)) mod 2) = 0) by lia.
      rewrite Hrw; clear Hrw.
      assert (Hrw: (j / 2 ^ padl) mod 2 +
      2 * ((j / (2 ^ padl * 2)) mod 2) = 3 <-> 
      (j / 2 ^ padl) mod 2 = 1 /\ ((j / (2 ^ padl * 2)) mod 2) = 1) by lia.
      rewrite Hrw; clear Hrw.
      rewrite eq_iff_eq_true, 2!Nat.eqb_eq.
      rewrite Nat.pow_succ_r by lia.
      rewrite Nat.mul_comm in *.
      generalize dependent ((j / 2^padl) mod 2).
      intros n Hn.
      generalize dependent (j / (2 * 2^padl) mod 2).
      intros n' Hn'.
      lia.
  } 
  rewrite (big_sum_eq_bounded _
  (fun k => if 
    (k =? (j / 2 ^ padl) / 2 ^ 2 * 2 ^ padl + j mod 2 ^ padl) 
    then if eqb (Nat.testbit j padl) (Nat.testbit j (S padl)) 
      && number_preserved (k * 2^m + i) f (padl + 0 + padr + m)
    then C1 else C0 else C0)).
  2: {
    unfold matrix_of_biperm.
    intros k Hk.
    replace_bool_lia (2^m <=? i) false.
    rewrite !Nat.pow_add_r.
    replace_bool_lia (2^padl*2^0*2^padr <=? k) false.
    rewrite <- !andb_if, andb_assoc.
    easy.
  }
  unfold matrix_of_biperm.
  rewrite (big_sum_if_eq_C).
  replace (j / 2 ^ padl / 2 ^ 2 * 2 ^ padl +
  j mod 2 ^ padl <?
  2 ^ padr * 2 ^ 0 * 2 ^ padl) with true.
  - replace (padr + 2 + padl) with (padl + 2 + padr) by lia.
    rewrite number_preserved_compose_cup_l by easy.
    rewrite !Nat.pow_add_r.
    replace_bool_lia (2^m <=? i) false.
    replace_bool_lia (2^padl*2^2*2^padr <=? j) false.
    now rewrite andb_comm.
  - symmetry. 
    rewrite Nat.ltb_lt. 
    assert (j / 2 ^ padl / 2 ^ 2 * 2 ^ padl <= (2 ^ padr - 1) * 2 ^ padl).
    1: {
      apply Nat.mul_le_mono_r.
      enough (j / 2 ^ padl / 2 ^ 2 < 2 ^ padr) by lia.
      do 2 apply Nat.Div0.div_lt_upper_bound. lia.
    }
    pose proof (Nat.mod_upper_bound j (2 ^ padl) ltac:(apply Hnz;lia)).
    rewrite Nat.pow_0_r, Nat.mul_1_r.
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l in *.
    enough (2 ^ padr * 2 ^ padl - 2 ^ padl + 2 ^ padl <= 2 ^ padr * 2 ^ padl) by lia.
    pose proof (Hnz 2 padl).
    pose proof (Hnz 2 padr).
    nia.
Qed.










Definition compose_swap_biperm_gen a b (f : nat -> nat) : nat -> nat :=
  fun k => 
    let inval := if k =? a then b else if k =? b then a else k in
    if f inval =? a then b
    else if f inval =? b then a
    else f inval.

Lemma compose_swap_biperm_gen_bipermutation {m a b} {f : nat -> nat} 
  (Hf : bipermutation m f) (Ha : a < m) (Hb : b < m) : 
  bipermutation m (compose_swap_biperm_gen a b f).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  intros k Hk; repeat split; unfold compose_swap_biperm_gen.
  - bdestructΩ'; apply Hfbdd; lia.
  - pose proof (Hfne k).
    pose proof (Hfne a).
    pose proof (Hfne b).
    bdestructΩ'.
  - pose proof (Hfeq k).
    pose proof (Hfeq a).
    pose proof (Hfeq b).
    bdestructΩ'.
Qed.

Definition compose_swap_biperm a (f : nat -> nat) : nat -> nat :=
  fun k => 
    let inval := if k =? a then S a else if k =? S a then a else k in
    if f inval =? a then S a
    else if f inval =? S a then a
    else f inval.

Lemma compose_swap_biperm_bipermutation {m a} {f : nat -> nat} 
  (Hf : bipermutation m f) (Ha : S a < m) : 
  bipermutation m (compose_swap_biperm a f).
Proof.
  apply compose_swap_biperm_gen_bipermutation; easy + lia.
Qed.

Lemma matrix_of_compose_swap_biperm {padl padr m f}
  (Hf : bipermutation (padl + 2 + padr + m) f) : 
  mat_equiv (matrix_of_biperm (padl + 2 + padr) m
  (compose_swap_biperm (m + padl) f))
  ((matrix_of_biperm (padl + 2 + padr) m f 
  × perm_to_matrix (padl + 2 + padr) 
    (swap_perm padr (S padr) (padl + 2 + padr)))).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (compose_swap_biperm_bipermutation 
    (a:=m+padl) Hf ltac:(lia)) as Hfg.
  pose proof (fun i Hi => proj1 (Hfg i Hi)) as Hfgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hfg i Hi))) as Hfgne.
  pose proof (fun i Hi => proj2 (proj2 (Hfg i Hi))) as Hfgeq.
  pose proof (swap_perm_S_permutation padr (padl + 2 + padr) ltac:(lia))
    as Hswapperm.


  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite matrix_of_biperm_funbool_conj.

  rewrite 2!Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits by auto with perm_db.
  rewrite <- Mmult_assoc.
  rewrite matrix_of_biperm_funbool_conj.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true; rewrite 2!number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_funbool_to_nat.
  split.
  - intros H s Hs.
    pose proof (H s Hs) as HHs.
    revert HHs.
    simplify_bools_lia_one_kernel.
    match goal with
    |- context [?n + ?m - S ?x <? ?n] => 
      replace_bool_lia (n + m - S x <? n) (m <=? x)
    end.
    match goal with
    |- context [f ?x <? ?n] => 
      pose proof (Hfbdd x);
      replace_bool_lia (f x <? n) true
    end.
    do 2 match goal with
    |- context [?n + ?m - S ?x <? ?n] => 
      replace_bool_lia (n + m - S x <? n) (m <=? x)
    end.
    unfold compose_swap_biperm.
    bdestruct (s =? m + padl);
    [|bdestruct (s =? S (m + padl))].
    + pose proof (Hfne (S (m + padl))).
      do 2 simplify_bools_lia_one_kernel.
      pose proof (Hfbdd (S (m + padl))).
      replace ((if f (S (m + padl)) =? m + padl
       then S (m + padl)
       else f (S (m + padl))) <? padl + 2 + padr + m) with true by bdestructΩ'.
      unfold swap_perm.
      do 2 simplify_bools_lia_one_kernel.
      replace (padl + 2 + padr + m - S s) with (S padr) by lia.
      do 2 match goal with 
      |- context[ ?p + ?m - ?x - ?p ] => 
        replace (p + m - x - p) with (m - x) by lia
      end.
      replace <- (m + padl).
      pose proof (bipermutation_eq_iff s (S s) Hf).
      bdestruct (f s =? S s).
      * replace -> (f s).
        replace_bool_lia (f (S s) =? s) true.
        replace (padl + 2 + padr + m - S (S s)) with padr by lia.
        replace (padr - (padl + 2 + padr)) with 0 by lia.
        bdestructΩ'.
      * intros _. 
        do 2 simplify_bools_lia_one_kernel.
        generalize (H (S s) ltac:(lia)).
        do 2 simplify_bools_lia_one_kernel.
        unfold compose_swap_biperm.
        do 2 simplify_bools_lia_one_kernel.
        pose proof (Hfne (m + padl)).
        subst s.
        do 4 simplify_bools_lia_one_kernel.
        rewrite Tauto.if_same.
        replace (padl+2+padr+m-S(S(m+padl))) with padr by lia.
        replace_bool_lia (padl+2+padr+m-S(f(m+padl))<?padl+2+padr)
          (m <=? f (m + padl)).
        match goal with 
        |- context[ ?p + ?m - ?x - ?p ] => 
          replace (p + m - x - p) with (m - x) by lia
        end.
        easy.
    + pose proof (Hfne (m + padl)).
      do 2 simplify_bools_lia_one_kernel.
      pose proof (Hfbdd (m + padl)).
      
      unfold swap_perm.
      do 2 simplify_bools_lia_one_kernel.
      subst.
      replace (padl + 2 + padr + m - S (S (m + padl))) with (padr) by lia.
      do 2 match goal with 
      |- context[ ?p + ?m - ?x - ?p ] => 
        replace (p + m - x - p) with (m - x) by lia
      end.
      match goal with 
      |- context[ ?p <=? ?p + ?m - S ?x] => 
        replace_bool_lia (p <=? p + m - S x) (x <? m)
      end.
      pose proof (bipermutation_eq_iff (m + padl) (S (m + padl)) Hf).
      bdestruct (f (m + padl) =? S (m + padl)).
      * do 5 simplify_bools_lia_one_kernel.
        replace (padl + 2 + padr + m - S (m + padl)) with (S padr) by lia.
        intros <-.
        bdestructΩ'.
      * intros _. 
        do 1 simplify_bools_lia_one_kernel.
        generalize (H (m + padl) ltac:(lia)).
        do 2 simplify_bools_lia_one_kernel.
        unfold compose_swap_biperm.
        do 2 simplify_bools_lia_one_kernel.
        pose proof (Hfne (S (m + padl))).
        do 3 simplify_bools_lia_one_kernel.
        replace (padl+2+padr+m-S(m+padl)) with (S padr) by lia.
        intros ->.
        bdestructΩ'; f_equal; lia.
    + pose proof (bipermutation_eq_iff s (S (m + padl)) Hf ltac:(lia)ltac:(lia)).
      pose proof (bipermutation_eq_iff s (S (m + padl)) Hf ltac:(lia)ltac:(lia)).
      bdestruct (f s =? m + padl);
      [|bdestruct (f s =? S (m + padl))].
      * do 3 simplify_bools_lia_one_kernel.
        unfold swap_perm.
        do 5 simplify_bools_lia_one_kernel.
        replace (padl + 2 + padr + m - S (S (m + padl))) with (padr) by lia.
        intros <-.
        bdestructΩ'.
      * do 3 simplify_bools_lia_one_kernel.
        unfold swap_perm.
        do 4 simplify_bools_lia_one_kernel.
        replace (padl + 2 + padr + m - S (m + padl)) with (S padr) by lia.
        (* intros <-. *)
        bdestructΩ'.
      * do 1 simplify_bools_lia_one_kernel.
        unfold swap_perm.
        do 4 simplify_bools_lia_one_kernel.
        do 2 match goal with 
        |- context[ ?p + ?m - ?x - ?p ] => 
          replace (p + m - x - p) with (m - x) by lia
        end.
        bdestructΩ'.
  - intros H s Hs.
    pose proof (H s Hs) as HHs.
    revert HHs.
    
    do 2 match goal with 
    |- context[ ?p + ?m - ?x - ?p ] => 
      replace (p + m - x - p) with (m - x) by lia
    end.
    simplify_bools_lia_one_kernel.
    match goal with
    |- context [?n + ?m - S ?x <? ?n] => 
      replace_bool_lia (n + m - S x <? n) (m <=? x)
    end.
    match goal with
    |- context [f ?x <? ?n] => 
      pose proof (Hfbdd x);
      replace_bool_lia (f x <? n) true
    end.
    do 2 match goal with
    |- context [?n + ?m - S ?x <? ?n] => 
      replace_bool_lia (n + m - S x <? n) (m <=? x)
    end.
    unfold compose_swap_biperm.
    bdestruct (s =? m + padl);
    [|bdestruct (s =? S (m + padl))].
    + pose proof (Hfne (S (m + padl))).
      do 2 simplify_bools_lia_one_kernel.
      pose proof (Hfbdd (S (m + padl))).
      replace ((if f (S (m + padl)) =? m + padl
       then S (m + padl)
       else f (S (m + padl))) <? padl + 2 + padr + m) with true by bdestructΩ'.
      
      unfold swap_perm.
      do 3 simplify_bools_lia_one_kernel.
      replace (padl + 2 + padr + m - S s) with (S padr) by lia.
      match goal with 
      |- context[ ?p + ?m - ?x - ?p ] => 
        replace (p + m - x - p) with (m - x) by lia
      end.
      replace <- (m + padl).
      pose proof (bipermutation_eq_iff s (S s) Hf).
      bdestruct (f s =? S s).
      * replace -> (f s).
        replace_bool_lia (f (S s) =? s) true.
        replace (padl + 2 + padr + m - S (S s)) with padr by lia.
        bdestructΩ'.
      * intros _. 
        do 1 simplify_bools_lia_one_kernel.
        generalize (H (S s) ltac:(lia)).
        do 2 simplify_bools_lia_one_kernel.
        unfold swap_perm.
        do 3 simplify_bools_lia_one_kernel.
        match goal with 
        |- context[ ?p + ?m - ?x - ?p ] => 
          replace (p + m - x - p) with (m - x) by lia
        end.
        pose proof (Hfne (m + padl)).
        subst s.
        do 2 simplify_bools_lia_one_kernel.
        rewrite Tauto.if_same.
        intros ->.
        bdestructΩ'.
    + pose proof (Hfne (m + padl)).
      do 2 simplify_bools_lia_one_kernel.
      pose proof (Hfbdd (m + padl)).
      
      unfold swap_perm.
      do 2 simplify_bools_lia_one_kernel.
      subst.
      replace (padl + 2 + padr + m - S (S (m + padl))) with (padr) by lia.
      match goal with 
      |- context[ ?p + ?m - ?x - ?p ] => 
        replace (p + m - x - p) with (m - x) by lia
      end.
      match goal with 
      |- context[ ?p <=? ?p + ?m - S ?x] => 
        replace_bool_lia (p <=? p + m - S x) (x <? m)
      end.
      pose proof (bipermutation_eq_iff (m + padl) (S (m + padl)) Hf).
      bdestruct (f (m + padl) =? S (m + padl)).
      * do 5 simplify_bools_lia_one_kernel.
        replace (padl + 2 + padr + m - S (m + padl)) with (S padr) by lia.
        intros <-.
        bdestructΩ'.
      * intros _. 
        do 1 simplify_bools_lia_one_kernel.
        generalize (H (m + padl) ltac:(lia)).
        do 2 simplify_bools_lia_one_kernel.
        unfold swap_perm.
        do 5 simplify_bools_lia_one_kernel.
        intros ->.
        pose proof (Hfne (S (m + padl))).
        do 1 simplify_bools_lia_one_kernel.
        replace (padl+2+padr+m-S(m+padl)) with (S padr) by lia.
        match goal with 
        |- context[ ?p + ?m - ?x - ?p ] => 
          replace (p + m - x - p) with (m - x) by lia
        end.
        bdestructΩ'.
    + pose proof (bipermutation_eq_iff s (S (m + padl)) Hf ltac:(lia)ltac:(lia)).
      pose proof (bipermutation_eq_iff s (S (m + padl)) Hf ltac:(lia)ltac:(lia)).
      bdestruct (f s =? m + padl);
      [|bdestruct (f s =? S (m + padl))].
      * do 3 simplify_bools_lia_one_kernel.
        unfold swap_perm.
        do 5 simplify_bools_lia_one_kernel.
        replace (padl + 2 + padr + m - S (S (m + padl))) with (padr) by lia.
        intros <-.
        bdestructΩ'.
      * do 3 simplify_bools_lia_one_kernel.
        unfold swap_perm.
        do 4 simplify_bools_lia_one_kernel.
        replace (padl + 2 + padr + m - S (m + padl)) with (S padr) by lia.
        (* intros <-. *)
        bdestructΩ'.
      * do 1 simplify_bools_lia_one_kernel.
        unfold swap_perm.
        do 4 simplify_bools_lia_one_kernel.
        match goal with 
        |- context[ ?p + ?m - ?x - ?p ] => 
          replace (p + m - x - p) with (m - x) by lia
        end.
        bdestructΩ'.
Qed.

Lemma matrix_of_compose_swap_biperm_corrected {padl padr m f}
  (Hf : bipermutation (padl + 2 + padr + m) f) : 
  mat_equiv (matrix_of_biperm (padl + 2 + padr) m
  (compose_swap_biperm (m + padr) f))
  ((matrix_of_biperm (padl + 2 + padr) m f 
  × perm_to_matrix (padl + 2 + padr) 
    (swap_perm padl (S padl) (padl + 2 + padr)))).
Proof.
  replace (padl + 2 + padr) with (padr + 2 + padl) in * by lia.
  apply matrix_of_compose_swap_biperm.
  easy.
Qed.


Lemma matrix_of_compose_cap_biperm_l_corrected padl padr m f 
  (Hf : bipermutation (padl + 2 + padr + m) f) : 
  mat_equiv ((matrix_of_biperm (padl + 0 + padr) m
  (compose_cap_biperm_l (m + padr) f)))
  ((if f (m + padr) =? S (m + padr) then / 2%R else 1%R)
  .* (matrix_of_biperm (padl + 2 + padr) m f
      × (I (2 ^ padl) ⊗ (⟦ ⊂ ⟧) ⊗ I (2 ^ padr)))).
Proof.
  rewrite <- matrix_of_compose_cap_biperm_l by 
    (replace (padr+2+padl) with (padl+2+padr) by lia; easy).
  bdestructΩ'; [|now Msimpl].
  rewrite Mscale_assoc.
  replace (/ C2 * C2)%C with (C1) by lca.
  now Msimpl.
Qed.

Lemma matrix_of_compose_cup_biperm_l_corrected padl padr m f 
  (Hf : bipermutation (padl + 0 + padr + m) f)
  (* (Hne : f (m + padl) <> S (m + padl)) *) : 
  mat_equiv (matrix_of_biperm (padl + 2 + padr) m
  (compose_cup_biperm_l (m + padr) f))
  ((matrix_of_biperm (padl + 0 + padr) m f 
  × ((I (2^padl) ⊗ ⟦⊃⟧) ⊗ I (2^padr)))).
Proof.
  now rewrite <- matrix_of_compose_cup_biperm_l by
    (replace (padr+0+padl) with (padl+0+padr) by lia; easy).
Qed.

Fixpoint biperm_of_zx_folio {n m} (zx : ZX_folio n m) : nat -> nat :=
  match zx with
  | FolioNil n' => idn_biperm n'
  | FolioCons (SheetElement padl zx_elem padr) fs => match zx_elem with
    | ElemEmpty => biperm_of_zx_folio fs
    | ElemCap =>
        compose_cup_biperm_l (m + padr) (biperm_of_zx_folio fs)
    | ElemCup => 
        compose_cap_biperm_l (m + padr) (biperm_of_zx_folio fs)
    | ElemSwap => 
        compose_swap_biperm (m + padr) (biperm_of_zx_folio fs)
    | ElemWire => biperm_of_zx_folio fs
    | ElemBox => idn
    | ElemX n' m' a => idn
    | ElemZ n' m' a => idn
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
  induction H as [n|n m o ? [n' m' padl ? [] padr]]; 
    [apply idn_biperm_bipermutation|..]; simpl.
  - easy.
  - replace (padl+2+padr) with (padr+2+padl) by lia.
    apply compose_cup_biperm_l_bipermutation.
    replace (padr+0+padl) with (padl+0+padr) by lia.
    easy.
  - replace (padl+0+padr) with (padr+0+padl) by lia.
    apply compose_cap_biperm_l_bipermutation.
    replace (padr+2+padl) with (padl+2+padr) by lia.
    easy.
  - apply compose_swap_biperm_bipermutation; easy + lia.
  - easy.
Qed. 

Definition matrix_of_zx_folio_biperm {n m} (zx : ZX_folio n m) : 
  Matrix (2^m) (2^n) :=
  matrix_of_biperm n m (biperm_of_zx_folio zx).

Lemma mat_equiv_prop_symm {n m} (A B : Matrix n m) : 
  (exists c : C, A ≡ c .* B /\ c <> 0%R) ->
  (exists c : C, B ≡ c .* A /\ c <> 0%R).
Proof.
  intros (c & HA & Hc).
  Proportional.prop_exists_nonzero (/ c); auto.
  rewrite HA.
  distribute_scale.
  now rewrite Cinv_l, Mscale_1_l by easy.
Qed.

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
    Proportional.prop_exists_nonzero R1.
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
    + apply mat_equiv_prop_symm in IHZXbiperm_folio.
      destruct IHZXbiperm_folio as (c & Hequiv & Hc).
      apply mat_equiv_prop_symm.
      exists c; split; [|easy].
      simpl.
      rewrite Hequiv.
      rewrite 2!n_wire_semantics.
      rewrite matrix_of_compose_cup_biperm_l_corrected 
        by now apply biperm_of_zxbiperm_folio_bipermutation.
      rewrite Mscale_mult_dist_l.
      easy.
    + simpl.
      apply mat_equiv_prop_symm in IHZXbiperm_folio.
      destruct IHZXbiperm_folio as (c & Hequiv & Hc).
      exists (if biperm_of_zx_folio fs (o + padr) =? S (o + padr) 
        then / 2%R * / c else 1%R / c)%C.
      rewrite Hequiv.
      split; 
      [| bdestructΩ';
      [rewrite <- Cinv_mult_distr by (easy + apply C2_nonzero);
        apply nonzero_div_nonzero, Cmult_neq_0; easy + apply C2_nonzero | 
        apply Cdiv_nonzero; easy + apply C1_nonzero]].
      rewrite !n_wire_semantics.
      rewrite Mscale_mult_dist_l.
      rewrite Mscale_assoc.
      rewrite matrix_of_compose_cap_biperm_l_corrected
        by now apply biperm_of_zxbiperm_folio_bipermutation.
      rewrite (if_dist _ _ _ (fun x => Cmult x c)).
      fold (Cdiv (/C2) c).
      rewrite 2!Cdiv_mult_r by easy.
      easy.
    + simpl.
      destruct IHZXbiperm_folio as (c & Hequiv & Hc).
      exists c; split; [|apply Hc].
      rewrite matrix_of_compose_swap_biperm_corrected, Hequiv
        by now apply biperm_of_zxbiperm_folio_bipermutation.
      rewrite Mscale_mult_dist_l.
      rewrite 2!n_wire_semantics.
      rewrite perm_to_matrix_swap_perm_S by lia.
      now replace (padl + 2 + padr - S (S padl)) with padr by lia.
    + simpl.
      destruct IHZXbiperm_folio as (c & Hequiv & Hc).
      exists c; split; [|apply Hc].
      rewrite 2!n_wire_semantics, id_kron.
      restore_dims.
      rewrite id_kron.
      replace (2 ^ padl * 2 * 2 ^ padr) with (2 ^ (padl + 1 + padr)) by
        (rewrite !Nat.pow_add_r; simpl; lia).
      rewrite Mmult_1_r_mat_eq.
      apply Hequiv.
Qed.


(* ORDERING: Bottom to top, outputs first. I.e., 
7  \/ —     3
6  /\ \/    2
5  —  /\ ╲  1
4  —  —  ╱  0
*)

Lemma matrix22_pullthrough_id_l {padl padr} {f}
  (Hf : bipermutation (padl + 1 + padr + (padl + 1 + padr)) f)
  (Hfpad : f padr = padl + 1 + padr + padr) (A : Matrix 2 2) (HA : WF_Matrix A) :
  @mat_equiv (2^padl*2*2^padr) (2^padl*2*2^padr)
  (I (2^padl) ⊗ A ⊗ I (2^padr) ×
    matrix_of_biperm (padl + 1 + padr) (padl + 1 + padr) f)
  (@Mmult (2^padl*2*2^padr) (2^padl*2*2^padr) _
    (matrix_of_biperm (padl + 1 + padr) (padl + 1 + padr) f)
    (I (2^padl) ⊗ A ⊗ I (2^padr))).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  replace (2^padl * 2 * 2^padr) with (2^(padl+1+padr)) in * by 
    (now rewrite !Nat.pow_add_r).
  rewrite !basis_f_to_vec_alt by easy.
  rewrite !Mmult_assoc, !f_to_vec_split'_eq.
  rewrite !(fun x y => kron_transpose' _ _ x y).
  rewrite !(fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z) by
    (now rewrite ?Nat.pow_add_r; simpl;lia).
  rewrite <- !Mmult_assoc.
  rewrite !(fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z) by
    (now rewrite ?Nat.pow_add_r; simpl;lia).
  rewrite !Mmult_1_r, !Mmult_1_l by auto with wf_db.
  rewrite f_to_vec_1_mult_r_decomp_eq, f_to_vec_1_mult_l_decomp_eq by easy.
  gridify.
  rewrite !Mscale_kron_dist_r, !Mscale_kron_dist_l, !Mscale_mult_dist_l.
  replace (2^padl * 2 * 2^padr) with (2^(padl+1+padr)) in * by 
    (now rewrite !Nat.pow_add_r).
  rewrite !Mscale_mult_dist_r, !ket_f_to_vec.
  replace (2^(padl+1+padr)) with (2^padl * 2 * 2^padr) in * by 
    (now rewrite !Nat.pow_add_r).
  rewrite <- !kron_transpose, qubit0_f_to_vec, qubit1_f_to_vec.
  restore_dims.
  rewrite !f_to_vec_merge.
  restore_dims.
  rewrite !f_to_vec_merge.
  unfold Mplus, scale.
  replace (2^padl * 2 * 2^padr) with (2^(padl+1+padr)) in * by 
    (now rewrite !Nat.pow_add_r).
  rewrite 4!matrix_of_biperm_funbool_conj. 
  rewrite 2!Nat.add_assoc in Hfpad.
  destruct (nat_to_funbool (padl + 1 + padr) i (padl + 0)) eqn:Hpadli;
  destruct (nat_to_funbool (padl + 1 + padr) j (padl + 0)) eqn:Hpadlj.
  - simpl.
    repeat match goal with 
    | |- context[ Cmult (A 0 _) (if ?b then _ else _) ] => 
      replace b with false
    | |- context[ Cmult (A _ 0) (if ?b then _ else _) ] => 
      replace b with false
    end. 
    + Csimpl.
      f_equal.
      apply f_equal_if; [|easy..].
      apply eq_iff_eq_true.
      rewrite 2!number_preserved_iff_all_lt_eq.
      apply forall_iff; intros s.
      apply impl_iff; intros Hs.
      rewrite 4!testbit_funbool_to_nat.
      simplify_bools_lia_one_kernel.
      solve [Morphisms.f_equiv; bdestructΩ'].
    + symmetry.
      rewrite <- not_true_iff_false.
      rewrite number_preserved_iff_all_lt_eq.
      intros Hfalse.
      specialize (Hfalse (padl + 1 + padr + padr) ltac:(
        lia)).
      revert Hfalse.
      rewrite 2!testbit_funbool_to_nat.
      rewrite <- Hfpad.
      rewrite Hfeq by lia.
      bdestructΩ'.
    + symmetry.
      rewrite <- not_true_iff_false.
      rewrite number_preserved_iff_all_lt_eq.
      intros Hfalse.
      specialize (Hfalse (padl + 1 + padr + padr) ltac:(
        lia)).
      revert Hfalse.
      rewrite 2!testbit_funbool_to_nat.
      rewrite <- Hfpad.
      rewrite Hfeq by lia.
      bdestructΩ'.
  - simpl.
    repeat match goal with 
    | |- context[ Cmult (A 0 _) (if ?b then _ else _) ] => 
      replace b with false
    | |- context[ Cmult (A _ 1) (if ?b then _ else _) ] => 
      replace b with false
    end. 
    + Csimpl.
      f_equal.
      apply f_equal_if; [|easy..].
      apply eq_iff_eq_true.
      rewrite 2!number_preserved_iff_all_lt_eq.
      setoid_rewrite testbit_funbool_to_nat.
      split.
      * intros Hfalse s Hs.
        pose proof (Hfalse s Hs) as Hfs; revert Hfs.
        simplify_bools_lia_one_kernel.
        pose proof (bipermutation_eq_iff s 
          (padl + 1 + padr + padr) Hf ltac:(lia) ltac:(lia)) as Hssum.
        rewrite <- Hfpad, Hfeq, Hfpad in Hssum by lia.
        pose proof (bipermutation_eq_iff s padr Hf 
          ltac:(lia) ltac:(lia)) as Hspadr.
        rewrite Hfpad in Hspadr.
        bdestructΩ'simp.
      * intros Hfalse s Hs.
        pose proof (Hfalse s Hs) as Hfs; revert Hfs.
        simplify_bools_lia_one_kernel.
        pose proof (bipermutation_eq_iff s 
          (padl + 1 + padr + padr) Hf ltac:(lia) ltac:(lia)) as Hssum.
        rewrite <- Hfpad, Hfeq, Hfpad in Hssum by lia.
        pose proof (bipermutation_eq_iff s padr Hf 
          ltac:(lia) ltac:(lia)) as Hspadr.
        rewrite Hfpad in Hspadr.
        bdestructΩ'simp.
    + symmetry.
      rewrite <- not_true_iff_false.
      rewrite number_preserved_iff_all_lt_eq.
      intros Hfalse.
      specialize (Hfalse (padl + 1 + padr + padr) ltac:(
        lia)).
      revert Hfalse.
      rewrite 2!testbit_funbool_to_nat.
      rewrite <- Hfpad.
      rewrite Hfeq by lia.
      bdestructΩ'.
    + symmetry.
      rewrite <- not_true_iff_false.
      rewrite number_preserved_iff_all_lt_eq.
      intros Hfalse.
      specialize (Hfalse (padl + 1 + padr + padr) ltac:(
        lia)).
      revert Hfalse.
      rewrite 2!testbit_funbool_to_nat.
      rewrite <- Hfpad.
      rewrite Hfeq by lia.
      bdestructΩ'.
  - simpl.
    repeat match goal with 
    | |- context[ Cmult (A 1 _) (if ?b then _ else _) ] => 
      replace b with false
    | |- context[ Cmult (A _ 0) (if ?b then _ else _) ] => 
      replace b with false
    end. 
    + Csimpl.
      f_equal.
      apply f_equal_if; [|easy..].
      apply eq_iff_eq_true.
      rewrite 2!number_preserved_iff_all_lt_eq.
      setoid_rewrite testbit_funbool_to_nat.
      split.
      * intros Hfalse s Hs.
        pose proof (Hfalse s Hs) as Hfs; revert Hfs.
        simplify_bools_lia_one_kernel.
        pose proof (bipermutation_eq_iff s 
          (padl + 1 + padr + padr) Hf ltac:(lia) ltac:(lia)) as Hssum.
        rewrite <- Hfpad, Hfeq, Hfpad in Hssum by lia.
        pose proof (bipermutation_eq_iff s padr Hf 
          ltac:(lia) ltac:(lia)) as Hspadr.
        rewrite Hfpad in Hspadr.
        bdestructΩ'simp.
      * intros Hfalse s Hs.
        pose proof (Hfalse s Hs) as Hfs; revert Hfs.
        simplify_bools_lia_one_kernel.
        pose proof (bipermutation_eq_iff s 
          (padl + 1 + padr + padr) Hf ltac:(lia) ltac:(lia)) as Hssum.
        rewrite <- Hfpad, Hfeq, Hfpad in Hssum by lia.
        pose proof (bipermutation_eq_iff s padr Hf 
          ltac:(lia) ltac:(lia)) as Hspadr.
        rewrite Hfpad in Hspadr.
        bdestructΩ'simp.
    + symmetry.
      rewrite <- not_true_iff_false.
      rewrite number_preserved_iff_all_lt_eq.
      intros Hfalse.
      specialize (Hfalse (padl + 1 + padr + padr) ltac:(
        lia)).
      revert Hfalse.
      rewrite 2!testbit_funbool_to_nat.
      rewrite <- Hfpad.
      rewrite Hfeq by lia.
      bdestructΩ'.
    + symmetry.
      rewrite <- not_true_iff_false.
      rewrite number_preserved_iff_all_lt_eq.
      intros Hfalse.
      specialize (Hfalse (padl + 1 + padr + padr) ltac:(
        lia)).
      revert Hfalse.
      rewrite 2!testbit_funbool_to_nat.
      rewrite <- Hfpad.
      rewrite Hfeq by lia.
      bdestructΩ'.
  - simpl.
    repeat match goal with 
    | |- context[ Cmult (A 1 _) (if ?b then _ else _) ] => 
      replace b with false
    | |- context[ Cmult (A _ 1) (if ?b then _ else _) ] => 
      replace b with false
    end. 
    + now Csimpl.
    + symmetry.
      rewrite <- not_true_iff_false.
      rewrite number_preserved_iff_all_lt_eq.
      intros Hfalse.
      specialize (Hfalse (padl + 1 + padr + padr) ltac:(
        lia)).
      revert Hfalse.
      rewrite 2!testbit_funbool_to_nat.
      rewrite <- Hfpad.
      rewrite Hfeq by lia.
      bdestructΩ'.
    + symmetry.
      rewrite <- not_true_iff_false.
      rewrite number_preserved_iff_all_lt_eq.
      intros Hfalse.
      specialize (Hfalse (padl + 1 + padr + padr) ltac:(
        lia)).
      revert Hfalse.
      rewrite 2!testbit_funbool_to_nat.
      rewrite <- Hfpad.
      rewrite Hfeq by lia.
      bdestructΩ'.
Qed.

Lemma make_gap_lt_helper_alt {padl a padr k} 
  (Hk : k < 2 ^ (padl + a + padr)) : 
  k / 2 ^ padr / 2 ^ a * 2 ^ padr * 2 ^ a 
    + k mod 2 ^ a < 2 ^ (padl + a + padr).
Proof.
  show_moddy_lt.
Qed.

Lemma make_gap_lt_helper {padl a padr k} 
  (Hk : k < 2 ^ (padl + a + padr)) : 
  k / 2 ^ padr / 2 ^ a * 2 ^ a * 2 ^ padr 
    + k mod 2 ^ padr < 2 ^ (padl + a + padr).
Proof.
  show_moddy_lt.
Qed.

Lemma matrix_of_biperm_split_middle_id {padl a padr} {f}
  (Hf : bipermutation (padl + a + padr + (padl + a + padr)) f) 
  (Hfpad : forall b, b < a -> f (padr + b) = padl + a + padr + (padr + b)) 
  k l (Hk : k < 2 ^ (padl + a + padr)) (Hl : l < 2 ^ (padl + a + padr)) :
  matrix_of_biperm (padl + a + padr) (padl + a + padr) f k l = 
  if ((k / 2 ^ padr) mod 2 ^ a =? (l / 2 ^ padr) mod 2 ^ a) then
  matrix_of_biperm (padl + a + padr) (padl + a + padr) f 
  (k / 2 ^ padr / 2 ^ a * 2 ^ a * 2 ^ padr + k mod 2 ^ padr) 
  (l / 2 ^ padr / 2 ^ a * 2 ^ a * 2 ^ padr + l mod 2 ^ padr)
  else 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (fun i j Hi Hj => 
    proj1 (bipermutation_injective Hf i j Hi Hj)) as Hfinj.
  unfold matrix_of_biperm.
  do 2 simplify_bools_lia_one_kernel.
  let r := get_strict_upper_bound (k) 
  in idtac r.
  let r := get_div_by_pow_2 (2 ^ (padl + a + padr)) padr in
  idtac r.
  do 2 simplify_bools_moddy_lia_one_kernel.
  rewrite <- andb_if.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite andb_true_iff.
  rewrite 2!number_preserved_iff_all_lt_eq.
  assert (Hfpad' : forall b, b < padl + a + padr + (padl + a + padr) ->
    padr <= f b -> f b - padr < a -> b = padl + a + padr + f b).
  1: {
    intros b Hb ? Hfbsub.
    specialize (Hfpad _ Hfbsub).
    replace (padr + (f b - padr)) with (f b) in Hfpad by lia.
    now rewrite Hfeq in Hfpad by lia.
  }
  assert (Hfpad'' : forall b, b < padl + a + padr + (padl + a + padr) ->
    padl + a + padr + padr <= f b -> 
    f b - (padl + a + padr + padr) < a -> 
    b = f b - (padl + a + padr)).
  1: {
    intros b Hb ? Hfbsub.
    specialize (Hfpad _ Hfbsub).
    rewrite (bipermutation_eq_iff _ _ Hf) in Hfpad by lia.
    pose proof (Hfeq b).
    replace (padr + (f b - (padl + a + padr + padr))) with
      (f b - (padl + a + padr)) in * by lia.
    rewrite Hfpad.
    rewrite <- (Hfeq b) at 1; [f_equal|]; lia.
  }
  assert (Hfpad''' : forall b, b < padl + a + padr + (padl + a + padr) ->
    padl + a + padr + padr <= b -> 
    b - (padl + a + padr + padr) < a -> 
    f b = b - (padl + a + padr)).
  1: {
    intros b Hb ? Hfbsub.
    specialize (Hfpad _ Hfbsub).
    rewrite (bipermutation_eq_iff _ _ Hf) in Hfpad by lia.
    replace (padr + (b - (padl + a + padr + padr))) with
      (b - (padl + a + padr)) in * by lia.
    rewrite Hfpad.
    apply (bipermutation_injective Hf); lia.
  }
  split.
  - intros Hall.
    split.
    + rewrite Nat.eqb_eq.
      apply bits_inj_upto.
      intros s Hs.
      rewrite !testbit_div_pow2.
      specialize (Hall (padr + s) ltac:(lia)).
      revert Hall.
      rewrite 2!testbit_add_pow2_split by easy.
      rewrite (Hfpad s Hs).
      simplify_bools_lia.
      intros ->.
      f_equal; lia.
    + intros s Hs.
      pose proof (make_gap_lt_helper Hk).
      generalize (Hall s Hs).
      rewrite !testbit_add_pow2_split by
        (apply Nat.mod_upper_bound, pow2_nonzero || lia).
      rewrite !testbit_mod_pow2, !testbit_mul_pow2, !testbit_div_pow2.
      repeat (bdestruct_one; subst; try reflexivity);
      try (replace (padr + (a + (s - padr - a))) with s by lia);
      try (replace (padr + (a + (f s - padr - a))) with (f s) by lia);
      try (try (intros -> || intros <-); f_equal; lia).
      all: tryif pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
        rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs by lia then lia 
        else idtac.
      all : tryif 
        pose proof (Hfpad (f s - (padl + a + padr) - padr) 
        ltac:(lia)) as Hffs;
        match type of Hffs with
        | _ = ?RHS => replace RHS with (f s) in Hffs by lia; 
          apply Hfinj in Hffs
        end then lia else idtac.
      all: tryif pose proof (Hfpad (s - padr) ltac:(lia)) as Hffs then
        rewrite Nat.add_sub_assoc, add_sub' in Hffs by lia; lia 
        else idtac.
      all: tryif pose proof (Hfpad''' s ltac:(lia) 
        ltac:(lia) ltac:(lia)) then 
        lia else idtac.
      replace (padr + (a + (s - (padl + a + padr) - padr - a))) with 
        (s - (padl + a + padr)) by lia.
      intros ->.
      f_equal; lia.
  - rewrite Nat.eqb_eq.
    intros [Hmid Hout].
    intros s Hs.
    specialize (Hout s Hs).
    revert Hout.
    pose proof (make_gap_lt_helper Hk).
    assert (Hmid' : forall i, 
      Nat.testbit ((k / 2 ^ padr) mod 2 ^ a) i =
      Nat.testbit ((l / 2 ^ padr) mod 2 ^ a) i) by (now rewrite Hmid).
    setoid_rewrite testbit_mod_pow2 in Hmid'.
    setoid_rewrite testbit_div_pow2 in Hmid'.
    rewrite !testbit_add_pow2_split by
      (apply Nat.mod_upper_bound, pow2_nonzero || lia).
    rewrite !testbit_mod_pow2, !testbit_mul_pow2, !testbit_div_pow2.
    repeat (bdestruct_one; subst; try reflexivity);
    try (replace (padr + (a + (s - padr - a))) with s by lia);
    try (replace (padr + (a + (f s - padr - a))) with (f s) by lia);
    try (try (intros -> || intros <-); f_equal; lia).
    all: tryif pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
      rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs by lia then try lia 
      else idtac.
    all : tryif 
      pose proof (Hfpad (f s - (padl + a + padr) - padr) 
      ltac:(lia)) as Hffs;
      match type of Hffs with
      | _ = ?RHS => replace RHS with (f s) in Hffs by lia; 
        apply Hfinj in Hffs
      end then try lia else idtac.
    all: tryif pose proof (Hfpad (s - padr) ltac:(lia)) as Hffs then
      rewrite Nat.add_sub_assoc, add_sub' in Hffs by lia; lia 
      else idtac.
    all: tryif pose proof (Hfpad''' s ltac:(lia) 
      ltac:(lia) ltac:(lia)) then 
      try lia else idtac.
    + specialize (Hmid' (s - padr)).
      revert Hmid'.
      simplify_bools_lia.
      rewrite Nat.add_sub_assoc, add_sub' by lia.
      intros -> _.
      f_equal; lia.
    + specialize (Hmid' (f s - padr)).
      revert Hmid'.
      simplify_bools_lia.
      rewrite Nat.add_sub_assoc, add_sub' by lia.
      intros -> _.
      f_equal; lia.
    + replace (padr + (a + (s - (padl + a + padr) - padr - a))) with 
        (s - (padl + a + padr)) by lia.
      intros ->.
      f_equal; lia.
Qed.

Lemma make_gap_lt_helper_two {padl a padr i j} 
  (Hi : i < 2 ^ (padl + a + padr)) : 
  i / 2 ^ padr / 2 ^ a * 2 ^ a * 2 ^ padr +
  (j / 2 ^ padr) mod 2 ^ a * 2 ^ padr + i mod 2 ^ padr <
  2 ^ (padl + a + padr).
Proof.
  show_moddy_lt.
Qed.

Lemma matrix_kk_pullthrough_id_l {padl a padr} {f}
  (Hf : bipermutation (padl + a + padr + (padl + a + padr)) f)
  (Hfpad : forall b, b < a -> f (padr + b) = padl + a + padr + (padr + b)) 
  (A : Matrix (2^a) (2^a)) (HA : WF_Matrix A) :
  @mat_equiv (2^padl*2^a*2^padr) (2^padl*2^a*2^padr)
  (I (2^padl) ⊗ A ⊗ I (2^padr) ×
    matrix_of_biperm (padl + a + padr) (padl + a + padr) f)
  (@Mmult (2^padl*2^a*2^padr) (2^padl*2^a*2^padr) _
    (matrix_of_biperm (padl + a + padr) (padl + a + padr) f)
    (I (2^padl) ⊗ A ⊗ I (2^padr))).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  intros i j Hi Hj.
  replace (2^padl * 2^a * 2^padr) with (2^(padl+a+padr)) in * by 
    (now rewrite !Nat.pow_add_r).
  (* rewrite <- (nat_to_funbool_inverse _ _ Hi).
  rewrite <- (nat_to_funbool_inverse _ _ Hj). *)
  (* generalize (nat_to_funbool (padl + a + padr) i).
  generalize (nat_to_funbool (padl + a + padr) j). *)
  (* intros g h. *)
  unfold Mmult, kron.
  rewrite (big_sum_eq_bounded _ 
    (fun k => if (k / 2 ^ padr / 2 ^ a =? i / 2 ^ padr / 2 ^ a) &&
      (k mod 2 ^ padr =? i mod 2 ^ padr) then 
      (A ((i / 2 ^ padr) mod 2 ^ a) ((k / 2 ^ padr) mod 2 ^ a) *
      matrix_of_biperm (padl + a + padr) (padl + a + padr) f 
      (i / 2^padr / 2^a * 2^a * 2^padr + 
       ((k / 2^padr) mod 2^a) * 2^padr + 
       i mod 2^padr)%nat j)%C
      else 0%R)).
  2: {
    intros k Hk.
    unfold I.
    pose proof (Nat.mod_upper_bound i (2^padr) 
      (Nat.pow_nonzero 2 padr ltac:(lia))).
    pose proof (Nat.mod_upper_bound k (2^padr) 
      (Nat.pow_nonzero 2 padr ltac:(lia))).
    replace (padl + a + padr) with (padr + a + padl) in * by lia.
    rewrite !Nat.pow_add_r, <- Nat.mul_assoc in *.
    pose proof (Nat.Div0.div_lt_upper_bound _ _ _
      (Nat.Div0.div_lt_upper_bound _ _ _ Hi)).
    pose proof (Nat.Div0.div_lt_upper_bound _ _ _
      (Nat.Div0.div_lt_upper_bound _ _ _ Hk)).
    do 2 simplify_bools_lia_one_kernel.
    bdestructΩ'simp.
    Csimpl.
    do 2 f_equal.
    rewrite (fun H => Nat.div_mod k (2^padr) (Nat.pow_nonzero _ _ H)) 
      at 1 by lia.
    f_equal; [|easy].
    rewrite Nat.mul_comm, Nat.mul_assoc, <- Nat.mul_add_distr_r.
    f_equal.
    rewrite (fun H => Nat.div_mod (k/2^padr) (2^a) (Nat.pow_nonzero _ _ H)) 
      at 1 by lia.
    rewrite Nat.mul_comm.
    do 2 f_equal.
    easy.
  } 
  rewrite (big_sum_eq_bounded (fun k => Cmult _ _) 
    (fun k => if (k / 2 ^ padr / 2 ^ a =? j / 2 ^ padr / 2 ^ a) &&
      (k mod 2 ^ padr =? j mod 2 ^ padr) then 
      (A ((k / 2 ^ padr) mod 2 ^ a) ((j / 2 ^ padr) mod 2 ^ a) *
      matrix_of_biperm (padl + a + padr) (padl + a + padr) f i
      (j / 2^padr / 2^a * 2^a * 2^padr + 
       ((k / 2^padr) mod 2^a) * 2^padr + 
       j mod 2^padr)%nat)%C
      else 0%R)).
  2: {
    intros k Hk.
    unfold I.
    pose proof (Nat.mod_upper_bound j (2^padr) 
      (Nat.pow_nonzero 2 padr ltac:(lia))).
    pose proof (Nat.mod_upper_bound k (2^padr) 
      (Nat.pow_nonzero 2 padr ltac:(lia))).
    replace (padl + a + padr) with (padr + a + padl) in * by lia.
    rewrite !Nat.pow_add_r, <- Nat.mul_assoc in *.
    pose proof (Nat.Div0.div_lt_upper_bound _ _ _
      (Nat.Div0.div_lt_upper_bound _ _ _ Hi)).
    pose proof (Nat.Div0.div_lt_upper_bound _ _ _
      (Nat.Div0.div_lt_upper_bound _ _ _ Hk)).
    do 2 simplify_bools_lia_one_kernel.
    bdestructΩ'simp.
    Csimpl.
    rewrite Cmult_comm.
    do 2 f_equal.
    rewrite (fun H => Nat.div_mod k (2^padr) (Nat.pow_nonzero _ _ H)) 
      at 1 by lia.
    f_equal; [|easy].
    rewrite Nat.mul_comm, Nat.mul_assoc, <- Nat.mul_add_distr_r.
    f_equal.
    rewrite (fun H => Nat.div_mod (k/2^padr) (2^a) (Nat.pow_nonzero _ _ H)) 
      at 1 by lia.
    rewrite Nat.mul_comm.
    do 2 f_equal.
    easy.
  }
  rewrite (big_sum_eq_bounded _ 
    (fun k => if 
      (k =? i / 2 ^ padr / 2 ^ a * 2 ^ a * 2 ^ padr + 
        ((j / 2 ^ padr) mod 2 ^ a) * 2 ^ padr + 
        i mod 2 ^ padr) 
      then 
      (matrix_of_biperm (padl + a + padr) (padl + a + padr) f
      (i / 2 ^ padr / 2 ^ a * 2 ^ a * 2 ^ padr + i mod 2 ^ padr)%nat
      (j / 2 ^ padr / 2 ^ a * 2 ^ a * 2 ^ padr + j mod 2 ^ padr)%nat) * 
        A ((i / 2 ^ padr) mod 2 ^ a) ((j / 2 ^ padr) mod 2 ^ a)
      else 0%R)%C).
  2: {
    intros k Hk.
    rewrite (matrix_of_biperm_split_middle_id Hf Hfpad) by 
      (show_moddy_lt).
    rewrite Cmult_comm.
    rewrite (if_dist' (fun x => Cmult x (A _ _))).
    Csimpl.
    rewrite <- andb_if.
    rewrite (Nat.add_comm), <- Nat.mul_add_distr_r, !Nat.div_add, mod_div
      by (apply pow2_nonzero).
    simpl.
    rewrite Nat.add_comm, !Nat.Div0.mod_add, Nat.Div0.mod_mod.
    rewrite Nat.div_add, Nat.Div0.mod_mod, mod_div by (apply pow2_nonzero).
      simpl.
    apply f_equal_if_precedent; [| | easy].
    - apply eq_iff_eq_true.
      rewrite !andb_true_iff, !Nat.eqb_eq.
      rewrite !and_assoc.
      split.
      + intros (Hhigh & Hlow & Hmid).
        rewrite (Nat.div_mod k (2^padr) (pow2_nonzero padr)).
        f_equal; [|easy].
        rewrite Nat.mul_comm, <- Nat.mul_add_distr_r.
        f_equal.
        rewrite (Nat.div_mod (k/2^padr) (2^a) (pow2_nonzero a)).
        f_equal; [|easy].
        rewrite Nat.mul_comm.
        f_equal.
        easy.
      + rewrite <- Nat.mul_add_distr_r.
        intros ->.
        rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.div_add by
          (apply pow2_nonzero).
        rewrite (Nat.add_comm (_*(_^_))), Nat.add_assoc, Nat.div_add by
          (apply pow2_nonzero).
        rewrite mod_div; simpl.
        rewrite Nat.Div0.mod_add, !Nat.Div0.mod_mod by
          (apply pow2_nonzero).
        now rewrite mod_div.
    - rewrite !andb_true_iff, !Nat.eqb_eq.
      now intros [_ ->].
  } 
  rewrite (big_sum_eq_bounded (fun _ => if (_:bool) then Cmult (A _ _) _ else _)
    (fun k => if 
      (k =? j / 2 ^ padr / 2 ^ a * 2 ^ a * 2 ^ padr + 
        ((i / 2 ^ padr) mod 2 ^ a) * 2 ^ padr + 
        j mod 2 ^ padr) 
      then 
      (matrix_of_biperm (padl + a + padr) (padl + a + padr) f
      (i / 2 ^ padr / 2 ^ a * 2 ^ a * 2 ^ padr + i mod 2 ^ padr)%nat
      (j / 2 ^ padr / 2 ^ a * 2 ^ a * 2 ^ padr + j mod 2 ^ padr)%nat) * 
        A ((i / 2 ^ padr) mod 2 ^ a) ((j / 2 ^ padr) mod 2 ^ a)
      else 0%R)%C).
  2: {
    intros k Hk.
    rewrite (matrix_of_biperm_split_middle_id Hf Hfpad) by show_moddy_lt.
    rewrite Cmult_comm.
    rewrite (if_dist' (fun x => Cmult x (A _ _))).
    Csimpl.
    rewrite <- andb_if.
    rewrite (Nat.add_comm), <- Nat.mul_add_distr_r, !Nat.div_add, mod_div
      by (apply pow2_nonzero).
    simpl.
    rewrite Nat.add_comm, !Nat.Div0.mod_add, Nat.Div0.mod_mod.
    rewrite Nat.div_add, Nat.Div0.mod_mod, mod_div by (apply pow2_nonzero).
      simpl.
    apply f_equal_if_precedent; [| | easy].
    - apply eq_iff_eq_true.
      rewrite !andb_true_iff, !Nat.eqb_eq.
      rewrite !and_assoc.
      split.
      + intros (Hhigh & Hlow & Hmid).
        rewrite (Nat.div_mod k (2^padr) (pow2_nonzero padr)).
        f_equal; [|easy].
        rewrite Nat.mul_comm, <- Nat.mul_add_distr_r.
        f_equal.
        rewrite (Nat.div_mod (k/2^padr) (2^a) (pow2_nonzero a)).
        f_equal; [|easy].
        rewrite Nat.mul_comm.
        f_equal.
        easy.
      + rewrite <- Nat.mul_add_distr_r.
        intros ->.
        rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.div_add by
          (apply pow2_nonzero).
        rewrite (Nat.add_comm (_*(_^_))), Nat.add_assoc, Nat.div_add by
          (apply pow2_nonzero).
        rewrite mod_div; simpl.
        rewrite Nat.Div0.mod_add, !Nat.Div0.mod_mod by
          (apply pow2_nonzero).
        now rewrite mod_div.
    - rewrite !andb_true_iff, !Nat.eqb_eq.
      now intros [_ ->].
  }
  rewrite 2!big_sum_if_eq_C. 
  pose proof (@make_gap_lt_helper_two padl a padr i j Hi).
  pose proof (@make_gap_lt_helper_two padl a padr j i Hj).
  simplify_bools_lia.
  easy.
Qed.

Lemma make_two_gaps_lt_helper padl padm padr a k 
  (Hk : k < 2 ^ (padl + a + padm + a + padr)) :
  k / 2 ^ padr / 2 ^ a / 2 ^ padm / 2 ^ a 
    * 2 ^ a * 2 ^ padm * 2 ^ a * 2 ^ padr + 
   ((k / 2 ^ padr / 2 ^ a) mod 2^padm) * 2 ^ a * 2 ^ padr + 
   k mod 2 ^ padr < 2 ^ (padl + a + padm + a + padr).
Proof.
  show_moddy_lt.
  (* pose proof (pow2_nonzero) as H.
  enough (Hle: k / 2 ^ padr / 2 ^ a / 2 ^ padm / 2 ^ a 
    * 2 ^ a * 2 ^ padm * 2 ^ a * 2 ^ padr + 
    ((k / 2 ^ padr / 2 ^ a) mod 2^padm) * 2 ^ a * 2 ^ padr + 
    k mod 2 ^ padr <=
    2 ^ padr * 2 ^ a * 2 ^ padm * 2 ^ a * (2 ^ padl - 1) + 
    2 ^ padr * 2 ^ a * (2 ^ padm - 1) + 
    (2 ^ padr - 1)) by
  (rewrite !Nat.pow_add_r, !Nat.mul_sub_distr_l in *;
    generalize (H a) (H padr) (H padm) (H padl);
    intros; nia).
  apply Nat.add_le_mono; 
  [|pose proof (Nat.mod_upper_bound k _ (H padr)); lia].
  rewrite <- !Nat.mul_add_distr_r.
  rewrite (Nat.mul_comm (2^padr) (2^a)).
  rewrite <- !(Nat.mul_assoc (2^a*2^padr)), 2!(Nat.mul_comm (2^a*2^padr)).
  rewrite <- Nat.mul_assoc, <- Nat.mul_add_distr_r.
  apply Nat.mul_le_mono_r.
  apply Nat.add_le_mono;
  [|pose proof (Nat.mod_upper_bound (k/2^padr/2^a) _ (H padm)); lia].
  rewrite <- Nat.mul_assoc, (Nat.mul_comm (2^a) (2^padm)).
  rewrite (Nat.mul_comm (2^padm*2^a)).
  apply Nat.mul_le_mono_r.
  rewrite !Nat.Div0.div_div, !Nat.mul_assoc.
  replace (padl+a+padm+a+padr) with (padr+a+padm+a+padl) in Hk by lia.
  rewrite !Nat.pow_add_r in Hk.
  pose proof (Nat.Div0.div_lt_upper_bound _ _ _ Hk).
  lia. *)
Qed.

Lemma matrix_of_biperm_split_right_id {padl padm padr a m} {f}
  (Hf : bipermutation (m + (padl + a + padm + a + padr)) f)
  (Hfpad : forall b, b < a ->
    f (padr + b) = padr + a + padm + b)
  k l (Hk : k < 2 ^ (padl + a + padm + a + padr)) 
  (Hl : l < 2 ^ m) :
  matrix_of_biperm m (padl + a + padm + a + padr) f k l = 
  if ((k / 2 ^ padr) mod 2 ^ a =? 
    (k / 2 ^ padr / 2 ^ a / 2 ^ padm) mod 2 ^ a) then
  matrix_of_biperm m (padl + a + padm + a + padr) f
  (k / 2 ^ padr / 2 ^ a / 2 ^ padm / 2 ^ a 
    * 2 ^ a * 2 ^ padm * 2 ^ a * 2 ^ padr + 
   ((k / 2 ^ padr / 2 ^ a) mod 2^padm) * 2 ^ a * 2 ^ padr + 
   k mod 2 ^ padr) l
  else 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (fun i j Hi Hj => 
    proj1 (bipermutation_injective Hf i j Hi Hj)) as Hfinj.
  unfold matrix_of_biperm.
  do 2 simplify_bools_lia_one_kernel.
  simplify_bools_moddy_lia_one_kernel.
  rewrite <- andb_if.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite andb_true_iff.
  rewrite 2!number_preserved_iff_all_lt_eq.
  assert (Hfpad' : forall b, b < padl + a + padm + a + padr + m ->
    padr <= f b -> f b - padr < a -> b = f b + padm + a).
  1: {
    intros b Hb ? Hfbsub.
    specialize (Hfpad _ Hfbsub).
    replace (padr + (f b - padr)) with (f b) in Hfpad by lia.
    rewrite Hfeq in Hfpad; lia.
  }
  assert (Hfpadr : forall b, padr + a + padm <= b ->
    b < padr + a + padm + a ->
    f b = b - (padm + a)).
  1: {
    intros b Hbl Hbu.
    specialize (Hfpad (b - (padr + a + padm)) ltac:(lia)).
    rewrite 2!Nat.add_sub_assoc, add_sub' in Hfpad by lia.
    rewrite (bipermutation_eq_iff _ _ Hf) in Hfpad by lia.
    lia.
  }
  assert (Hfpadr' : forall b, b < padl + a + padm + a + padr + m ->
    padr + a + padm <= f b ->
    f b < padr + a + padm + a ->
    b = f b - (padm + a)).
  1: {
    intros b Hb Hfbl Hfbu.
    specialize (Hfpad (f b - (padr + a + padm)) ltac:(lia)).
    rewrite 2!Nat.add_sub_assoc, add_sub' in Hfpad by lia.
    apply Hfinj in Hfpad; lia. 
  }
  rewrite Nat.eqb_eq.
  setoid_rewrite testbit_add_pow2_split; 
    [|try apply make_two_gaps_lt_helper; easy..].
  setoid_rewrite <- Nat.mul_assoc.
  setoid_rewrite <- (Nat.mul_add_distr_r).
  rewrite <- Nat.pow_add_r.
  setoid_rewrite testbit_add_pow2_split;
  [| pose proof (Nat.mod_upper_bound k _ (pow2_nonzero padr));
    pose proof (pow2_nonzero a); rewrite Nat.pow_add_r; nia..].
  setoid_rewrite <- Nat.mul_assoc.
  rewrite <- Nat.pow_add_r.
  setoid_rewrite testbit_add_pow2_split;
  [| pose proof (Nat.mod_upper_bound (k/2^padr/2^a) _ (pow2_nonzero padm));
    pose proof (pow2_nonzero a); rewrite Nat.pow_add_r; nia..].
  repeat setoid_rewrite testbit_mod_pow2.
  repeat setoid_rewrite testbit_div_pow2.
  split.
  - intros Hall.
    split.
    + apply bits_inj_upto.
      intros s Hs.
      rewrite !testbit_div_pow2.
      specialize (Hall (padr + s) ltac:(lia)).
      revert Hall.
      simplify_bools_lia_one_kernel.
      rewrite (Hfpad s Hs).
      intros ->.
      simplify_bools_lia_one_kernel.
      now rewrite !Nat.add_assoc.
    + intros s Hs.
      specialize (Hall s Hs).
      revert Hall.
      
      repeat (bdestruct_one; subst; try reflexivity);
      try (replace (padr + (a + (s - (a + padr)))) with s by lia);
      try (replace (padr + (a + (f s - (a + padr)))) with (f s) by lia);
      try (try (intros -> || intros <-); f_equal; lia).
      all: tryif pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
        rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs by lia then lia 
        else idtac.
      all: tryif pose proof (Hfpad (s - padr) ltac:(lia)) as Hffs;
        rewrite Nat.add_sub_assoc, add_sub' in Hffs by lia then lia 
        else idtac.
      all: tryif pose proof (Hfpadr (f s) ltac:(lia) ltac:(lia)) as Hffs then
        rewrite Hfeq in Hffs; lia else idtac.
      all: tryif pose proof (Hfpadr (s) ltac:(lia) ltac:(lia)) as Hffs then
        lia else idtac.
      intros Hrw.
      transitivity (Nat.testbit k s);
      [| rewrite Hrw]; f_equal; lia.
  - intros [Hmid Hout].
    assert (Hmid' : forall i, 
      Nat.testbit ((k / 2 ^ padr) mod 2 ^ a) i =
      Nat.testbit ((k / 2 ^ padr / 2 ^ a / 2 ^ padm) mod 2 ^ a) i) 
      by (now rewrite Hmid).
    
    setoid_rewrite testbit_mod_pow2 in Hmid'.
    repeat setoid_rewrite testbit_div_pow2 in Hmid'.
    intros s Hs.
    specialize (Hout s Hs).
    revert Hout.
    
    repeat (bdestruct_one; subst; try reflexivity);
    try (replace (padr + (a + (s - (a + padr)))) with s by lia);
    try (replace (padr + (a + (f s - (a + padr)))) with (f s) by lia);
    try (try (intros -> || intros <-); f_equal; lia).
    all: tryif pose proof (Hfpad (s - padr) ltac:(lia)) as Hffs;
      rewrite Nat.add_sub_assoc, add_sub' in Hffs by lia then 
      try lia 
      else idtac.
    all: tryif pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
      rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs by lia then try lia 
      else idtac.
    all: tryif pose proof (Hfpadr (f s) ltac:(lia) ltac:(lia)) as Hffs then
      rewrite Hfeq in Hffs; lia else idtac.
    all: tryif pose proof (Hfpadr (s) ltac:(lia) ltac:(lia)) as Hffs then
      lia else idtac.
    3: intros Hrw; etransitivity; [etransitivity; [|exact Hrw]|];
      f_equal; lia.
    + generalize (Hmid' (s - padr)); simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub_assoc, add_sub' by lia.
      intros -> _; f_equal; lia.
    + generalize (Hmid' (f s - padr)); simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub_assoc, add_sub' by lia.
      intros -> _; f_equal; lia.
Qed.

(* FIXME: (re?)move *)
Lemma add_sub_four a b c : (c <= c -> a + b - c - a = b - c)%nat.
Proof. lia. Qed.

Lemma matrix_kk_id_l_l_swap_block_perm_l {padl padm padr a m} {f}
  (Hf : bipermutation (m + (padl + a + padm + a + padr)) f)
  (Hfpad : forall b, b < a ->
    f (padr + b) = padr + a + padm + b) :
  perm_to_matrix (padl + a + padm + a + padr) (swap_block_perm padl padm a) ×
  matrix_of_biperm m (padl + a + padm + a + padr) f ≡
  matrix_of_biperm m (padl + a + padm + a + padr) f.
Proof.
  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite <- (transpose_involutive _ _ 
    (perm_to_matrix _ (swap_block_perm _ _ _))).
  rewrite <- !Mmult_assoc, <- Mmult_transpose.
  rewrite (perm_to_matrix_transpose_eq
    (swap_block_perm_permutation padl padm padr a)).
  rewrite (perm_to_matrix_eq_of_perm_eq (padl + a + padm + a + padr) 
    (perm_inv (padl + a + padm + a + padr) (swap_block_perm padl padm a)) 
    (swap_block_perm padl padm a)
    (swap_block_perm_inv padl padm padr a)).
  rewrite !basis_f_to_vec_alt by easy.
  rewrite perm_to_matrix_permutes_qubits by 
    auto with perm_db.
  rewrite !matrix_of_biperm_funbool_conj.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true;
  rewrite 2!number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_funbool_to_nat.
  repeat setoid_rewrite nat_to_funbool_eq'.
  unfold swap_block_perm.


  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (fun i j Hi Hj => 
    proj1 (bipermutation_injective Hf i j Hi Hj)) as Hfinj.
  assert (Hfpad' : forall b, b < padl + a + padm + a + padr + m ->
    padr <= f b -> f b - padr < a -> b = f b + padm + a).
  1: {
    intros b Hb ? Hfbsub.
    specialize (Hfpad _ Hfbsub).
    replace (padr + (f b - padr)) with (f b) in Hfpad by lia.
    rewrite Hfeq in Hfpad; lia.
  }
  assert (Hfpadr : forall b, padr + a + padm <= b ->
    b < padr + a + padm + a ->
    f b = b - (padm + a)).
  1: {
    intros b Hbl Hbu.
    specialize (Hfpad (b - (padr + a + padm)) ltac:(lia)).
    rewrite 2!Nat.add_sub_assoc, add_sub' in Hfpad by lia.
    rewrite (bipermutation_eq_iff _ _ Hf) in Hfpad by lia.
    lia.
  }
  assert (Hfpadr' : forall b, b < padl + a + padm + a + padr + m ->
    padr + a + padm <= f b ->
    f b < padr + a + padm + a ->
    b = f b - (padm + a)).
  1: {
    intros b Hb Hfbl Hfbu.
    specialize (Hfpad (f b - (padr + a + padm)) ltac:(lia)).
    rewrite 2!Nat.add_sub_assoc, add_sub' in Hfpad by lia.
    apply Hfinj in Hfpad; lia. 
  }

  split.
  - intros H s Hs.
    pose proof (Hfbdd s Hs).
    do 4 simplify_bools_lia_one_kernel.    
    bdestruct ((padl + a + padm + a + padr) <=? s); 
    [|simplify_bools_lia_one_kernel;
      bdestruct ((a + padm + a + padr) <=? s);
    [|bdestruct ((padr + a + padm) <=? s);
    [|bdestruct ((padr + a) <=? s);
    [|bdestruct ((padr) <=? s)]]]].
    + generalize (H s Hs).
      clear H.
      do 4 simplify_bools_lia_one_kernel.
      intros ->.
      repeat (bdestruct_one; subst; try reflexivity); 
      try (f_equal; lia).
      * pose proof (Hfpadr (f s) ltac:(lia) ltac:(lia)) as Hffs;
        rewrite Hfeq in Hffs; lia.
      * pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
        rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs; lia .
    + generalize (H s Hs).
      clear H.
      do 5 simplify_bools_lia_one_kernel.
      intros ->.
      repeat (bdestruct_one; subst; try reflexivity); 
      try (try (intros -> || intros <-); f_equal; lia).
      * pose proof (Hfpadr (f s) ltac:(lia) ltac:(lia)) as Hffs;
        rewrite Hfeq in Hffs; lia.
      * pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
        rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs; lia.
    + generalize (H (s - (a + padm)) ltac:(lia)).
      do 5 simplify_bools_lia_one_kernel.
      
      pose proof (Hfbdd (s - (a + padm)) ltac:(lia)).
      simplify_bools_lia_one_kernel.
      clear H.
      pose proof (Hfpad (s - (a + padm) - padr) ltac:(lia)) as Hffss;
      rewrite Nat.add_sub_assoc, add_sub' in Hffss by lia;
      rewrite Hffss.
      replace (padr + a + padm + (s - (a + padm) - padr)) with s
        by lia.
      simplify_bools_lia_one_kernel.
      rewrite !add_sub_four in * by lia.
      replace (padl + a + padm + a + padr - S (s - (a + padm)) - (a + padm)) 
        with (padl + a + padm + a + padr - S s) by lia.
      do 5 simplify_bools_lia_one_kernel.
      intros ->.
      pose proof (Hfpadr s ltac:(lia) ltac:(lia)) as Hffs.
      bdestructΩ'.
      f_equal; lia.
    + generalize (H s Hs).
      clear H.
      do 6 simplify_bools_lia_one_kernel.
      intros ->.
      pose proof (Hfbdd s Hs).
      simplify_bools_lia_one_kernel.
      repeat (bdestruct_one; subst; try reflexivity); 
      try (try (intros -> || intros <-); f_equal; lia).
      * pose proof (Hfpadr (f s) ltac:(lia) ltac:(lia)) as Hffs;
        rewrite Hfeq in Hffs; lia.
      * pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
        rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs; lia .
    + generalize (H (s + (a + padm)) ltac:(lia)).
      do 5 simplify_bools_lia_one_kernel.
      pose proof (Hfbdd (s + (a + padm)) ltac:(lia)).
      simplify_bools_lia_one_kernel.
      clear H.
      pose proof (Hfpad (s - padr) ltac:(lia)) as Hffss;
      rewrite Nat.add_sub_assoc, add_sub' in Hffss by lia;
      rewrite Hffss.
      pose proof (Hfpadr (s + (a + padm)) ltac:(lia) ltac:(lia)) as Hffs.
      intros Hrw; etransitivity; [etransitivity; [|exact Hrw]|];
      [do 2 f_equal; lia|].
      rewrite Hffs.
      do 7 simplify_bools_lia_one_kernel.
      do 2 f_equal; lia.
    + generalize (H s Hs).
      clear H.
      do 8 simplify_bools_lia_one_kernel.
      intros ->.
      repeat (bdestruct_one; subst; try reflexivity); 
      try (try (intros -> || intros <-); f_equal; lia).
      * pose proof (Hfpadr (f s) ltac:(lia) ltac:(lia)) as Hffs;
        rewrite Hfeq in Hffs; lia.
      * pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
        rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs; lia .
  - intros H s Hs.
    simplify_bools_lia_one_kernel.
    pose proof (Hfbdd s Hs).
    simplify_bools_lia_one_kernel.  
    bdestruct ((padl + a + padm + a + padr) <=? s); 
    [|simplify_bools_lia_one_kernel;
      bdestruct ((a + padm + a + padr) <=? s);
    [|simplify_bools_lia_one_kernel;
      bdestruct ((padr + a + padm) <=? s);
    [|simplify_bools_lia_one_kernel;
      bdestruct ((padr + a) <=? s);
    [|simplify_bools_lia_one_kernel;
      bdestruct ((padr) <=? s)]]]].
    + generalize (H s Hs).
      clear H.
      do 5 simplify_bools_lia_one_kernel.
      intros ->.
      repeat (bdestruct_one; subst; try reflexivity); 
      try (f_equal; lia).
      * pose proof (Hfpadr (f s) ltac:(lia) ltac:(lia)) as Hffs;
        rewrite Hfeq in Hffs; lia.
      * pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
        rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs; lia.
    + generalize (H s Hs).
      clear H.
      do 7 simplify_bools_lia_one_kernel.
      intros ->.
      repeat (bdestruct_one; subst; try reflexivity); 
      try (try (intros -> || intros <-); f_equal; lia).
      * pose proof (Hfpadr (f s) ltac:(lia) ltac:(lia)) as Hffs;
        rewrite Hfeq in Hffs; lia.
      * pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
        rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs; lia.
    + generalize (H (s - (a + padm)) ltac:(lia)).
      do 6 simplify_bools_lia_one_kernel.
      
      pose proof (Hfbdd (s - (a + padm)) ltac:(lia)).
      simplify_bools_lia_one_kernel.
      clear H.
      pose proof (Hfpad (s - (a + padm) - padr) ltac:(lia)) as Hffss;
      rewrite Nat.add_sub_assoc, add_sub' in Hffss by lia;
      rewrite Hffss.
      replace (padr + a + padm + (s - (a + padm) - padr)) with s
        by lia.
      simplify_bools_lia_one_kernel.
      rewrite !add_sub_four in * by lia.
      replace (padl + a + padm + a + padr - S (s - (a + padm))) 
        with (padl + a + padm + a + padr - S s + (a + padm)) by lia.
      intros ->.
      pose proof (Hfpadr s ltac:(lia) ltac:(lia)) as Hffs.
      simplify_bools_lia.
      do 2 f_equal; lia.
    + generalize (H s Hs).
      clear H.
      do 7 simplify_bools_lia_one_kernel.
      intros ->.
      repeat (bdestruct_one; subst; try reflexivity); 
      try (try (intros -> || intros <-); f_equal; lia).
      * pose proof (Hfpadr (f s) ltac:(lia) ltac:(lia)) as Hffs;
        rewrite Hfeq in Hffs; lia.
      * pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
        rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs; lia .
    + generalize (H (s + (a + padm)) ltac:(lia)).
      do 6 simplify_bools_lia_one_kernel.
      pose proof (Hfbdd (s + (a + padm)) ltac:(lia)).
      simplify_bools_lia_one_kernel.
      clear H.
      pose proof (Hfpad (s - padr) ltac:(lia)) as Hffss;
      rewrite Nat.add_sub_assoc, add_sub' in Hffss by lia;
      rewrite Hffss.
      pose proof (Hfpadr (s + (a + padm)) ltac:(lia) ltac:(lia)) as Hffs.
      intros Hrw; etransitivity; [etransitivity; [|exact Hrw]|];
      [do 2 f_equal; lia|].
      rewrite Hffs.
      do 5 simplify_bools_lia_one_kernel.
      do 2 f_equal; lia.
    + generalize (H s Hs).
      clear H.
      do 7 simplify_bools_lia_one_kernel.
      intros ->.
      repeat (bdestruct_one; subst; try reflexivity); 
      try (try (intros -> || intros <-); f_equal; lia).
      * pose proof (Hfpadr (f s) ltac:(lia) ltac:(lia)) as Hffs;
        rewrite Hfeq in Hffs; lia.
      * pose proof (Hfpad (f s - padr) ltac:(lia)) as Hffs;
        rewrite Nat.add_sub_assoc, add_sub', Hfeq in Hffs; lia.
Qed.
 


Lemma matrix_kk_pullthrough_id_l_l {padl padm padr a m} {f}
  (Hf : bipermutation (m + (padl + a + padm + a + padr)) f)
  (Hfpad : forall b, b < a ->
    f (padr + b) = padr + a + padm + b)
  (A : Matrix (2^a) (2^a)) (HA : WF_Matrix A) :
  @mat_equiv (2^padl*2^a*2^padm*2^a*2^padr) (2^m)
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _
    (I (2^padl) ⊗ A ⊗ I (2^padm * 2^a * 2^padr))
    (matrix_of_biperm m (padl + a + padm + a + padr) f))
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _
    (I (2^padl * 2^a * 2^padm) ⊗ A ⊤ ⊗ I (2^padr))
    (matrix_of_biperm m (padl + a + padm + a + padr) f)).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  intros i j Hi Hj.
  replace (2^padl * 2^a * 2^padr) with (2^(padl+a+padr)) in * by 
    (now rewrite !Nat.pow_add_r).
  unfold Mmult, kron.
  erewrite (big_sum_eq_bounded).
  2: {
    intros k Hk.
    rewrite (matrix_of_biperm_split_right_id Hf) 
      by (easy + rewrite !Nat.pow_add_r; easy).
    unfold I.
    rewrite !Nat.Div0.div_div.
    pose proof (Nat.Div0.div_lt_upper_bound i 
      (2^padm*2^a*2^padr*2^a) (2^padl) ltac:(lia)).
    simplify_bools_lia_one_kernel.
    rewrite Cmult_if_1_l, Cmult_if_if_1_r.
    rewrite Cmult_if_andb.
    rewrite matrix_of_biperm_split_right_id
      by easy + show_moddy_lt.
    pose proof (Nat.mod_upper_bound i (2^padm * 2^a * 2^padr)) as H'.
    simplify_bools_lia_one_kernel.
    clear H'.
    rewrite Cmult_if_r.
    eapply (f_equal_if_precedent_same _ _ 
    (
    A ((i / 2 ^ (padm + a + padr)) mod 2 ^ a)
   ((k / 2 ^ (padm + a + padr)) mod 2 ^ a) *
 matrix_of_biperm m (padl + a + padm + a + padr) f
   ((k / 2 ^ (padr + a + padm + a) * 2 ^ a * 2 ^ padm +
     (k / 2 ^ (padr + a)) mod 2 ^ padm) * 
    2 ^ a * 2 ^ padr + k mod 2 ^ padr)%nat j)%C
    _ (RtoC 0%R));
    [|reflexivity].
    rewrite <- !Nat.pow_add_r, !Nat.add_assoc.
    intros Htemp.
    rewrite <- !Nat.mul_add_distr_r.
    rewrite !Nat.div_add_l by apply pow2_nonzero.
    rewrite !mod_div, !Nat.Div0.div_0_l, !Nat.add_0_r.
    rewrite !Nat.div_add_l by apply pow2_nonzero.
    rewrite !mod_div, !Nat.Div0.div_0_l, !Nat.add_0_r.
    rewrite !Nat.Div0.mod_mul, Nat.eqb_refl.
    rewrite !mod_add_l, !Nat.Div0.mod_mod.
    reflexivity.
  } 
  symmetry.
  erewrite (big_sum_eq_bounded).
  2: {
    intros k Hk.
    rewrite (matrix_of_biperm_split_right_id Hf) 
      by (easy + rewrite !Nat.pow_add_r; easy).
    unfold I.
    rewrite !Nat.Div0.div_div.
    pose proof (Nat.Div0.div_lt_upper_bound i 
      (2^padr*2^a) (2^padl*2^padm*2^a) ltac:(lia)).
    simplify_bools_lia_one_kernel.
    rewrite Cmult_if_1_l, Cmult_if_if_1_r.
    rewrite Cmult_if_andb.
    rewrite matrix_of_biperm_split_right_id
      by easy + show_moddy_lt.
    pose proof (Nat.mod_upper_bound i (2^padr)) as H'.
    simplify_bools_lia_one_kernel.
    clear H'.
    rewrite Cmult_if_r.
    eapply (f_equal_if_precedent_same _ _ 
      ((A ((k / 2 ^ padr) mod 2 ^ a)
        ((i / 2 ^ padr) mod 2 ^ a) *
      matrix_of_biperm m (padl + a + padm + a + padr) f
      ((k / 2 ^ (padr + a + padm + a) * 2 ^ a * 2 ^ padm +
        (k / 2 ^ (padr + a)) mod 2 ^ padm) * 
      2 ^ a * 2 ^ padr + k mod 2 ^ padr)%nat j)%C)%C
      _ (RtoC 0%R));
    [|reflexivity].
    rewrite <- !Nat.pow_add_r.
    intros Htemp.
    rewrite <- !Nat.mul_add_distr_r.
    rewrite !Nat.div_add_l by apply pow2_nonzero.
    rewrite !mod_div, !Nat.Div0.div_0_l, !Nat.add_0_r.
    rewrite !Nat.div_add_l by apply pow2_nonzero.
    rewrite !mod_div, !Nat.Div0.div_0_l, !Nat.add_0_r.
    rewrite !Nat.Div0.mod_mul, Nat.eqb_refl.
    rewrite !mod_add_l, !Nat.Div0.mod_mod.
    unfold Matrix.transpose.
    reflexivity.
  }
  rewrite (Nat.mul_comm _ (2^padr)).
  rewrite big_sum_product_div_mod_split.
  erewrite big_sum_eq_bounded.
  2: {
    intros k Hk.
    erewrite big_sum_eq_bounded.
    2: {
      intros l Hl.
      rewrite <- 2!Nat.Div0.div_div, Nat.div_add,
        Nat.Div0.mod_add
        by apply pow2_nonzero.
      rewrite andb_comm, andb_assoc, andb_comm.
      rewrite andb_if.
      rewrite <- Nat.mul_assoc, <- Nat.Div0.div_div, Nat.div_add
        by apply pow2_nonzero.
      rewrite !Nat.pow_add_r, <- !Nat.mul_assoc, 
        <- !Nat.Div0.div_div, Nat.div_add
        by apply pow2_nonzero.
      rewrite (Nat.mod_small l), (Nat.div_small l) by easy.
      simpl.
      reflexivity.
    }
    rewrite big_sum_if_eq_C'.
    pose proof (Nat.mod_upper_bound i _ (pow2_nonzero padr)).
    simplify_bools_lia_one_kernel.
    reflexivity.
  }
  rewrite (Nat.mul_comm _ (2^a)).
  rewrite big_sum_product_div_mod_split.
  erewrite big_sum_eq_bounded.
  2: {
    intros k Hk.
    erewrite big_sum_eq_bounded.
    2: {
      intros l Hl.
      rewrite Nat.div_add, Nat.Div0.mod_add
        by apply pow2_nonzero.
      rewrite andb_if.
      rewrite (Nat.mod_small l), (Nat.div_small l) by easy.
      simpl.
      reflexivity.
    } 
    rewrite big_sum_if_eq_C.
    pose proof (Nat.mod_upper_bound (k/2^padm) _ (pow2_nonzero a)).
    simplify_bools_lia_one_kernel.
    reflexivity.
  } 
  rewrite big_sum_if_eq_C'.
  replace (i / 2 ^ padr / 2 ^ a <? 2 ^ padl * 2 ^ a * 2 ^ padm)
    with true by (symmetry; rewrite Nat.ltb_lt; show_moddy_lt).
  rewrite big_sum_product_div_mod_split.
  erewrite big_sum_eq_bounded.
  2: {
    intros k Hk.
    erewrite big_sum_eq_bounded.
    2: {
      intros l Hl.
      rewrite <- 2!Nat.Div0.div_div, Nat.div_add,
        Nat.Div0.mod_add
        by apply pow2_nonzero.
      replace (2 ^ padm * 2 ^ a * 2 ^ padr * 2 ^ a) 
        with (2 ^ padr * (2 ^ a * (2 ^ padm * 2 ^ a))) by lia.
      rewrite <- !Nat.Div0.div_div.
      rewrite Nat.div_add
        by apply pow2_nonzero.
      rewrite !Nat.pow_add_r.
      replace (2 ^ padm * 2 ^ a * 2 ^ padr) 
        with (2 ^ padr * (2 ^ a * 2 ^ padm)) by lia.
      rewrite <- Nat.mul_assoc, (Nat.Div0.mod_mul_r (_+_)).
      rewrite Nat.div_add, Nat.Div0.mod_mul_r, Nat.Div0.mod_add
        by apply pow2_nonzero.
      rewrite eqb_div_mod_pow_2_iff.
      rewrite <- Nat.mul_assoc, <- !Nat.Div0.div_div, !Nat.div_add
        by apply pow2_nonzero.
      rewrite (Nat.mod_small l), (Nat.div_small l) by easy.
      simpl.
      rewrite andb_assoc, (andb_comm _ (_=?l)), <- !andb_assoc.
      rewrite andb_if.
      reflexivity.
    }
    rewrite big_sum_if_eq_C'.
    pose proof (Nat.mod_upper_bound i _ (pow2_nonzero padr)).
    simplify_bools_lia_one_kernel.
    reflexivity.
  }
  rewrite big_sum_product_div_mod_split.
  erewrite big_sum_eq_bounded.
  2: {
    intros k Hk.
    erewrite big_sum_eq_bounded.
    2: {
      intros l Hl.
      rewrite Nat.div_add, Nat.Div0.mod_add
        by apply pow2_nonzero.
      rewrite (Nat.Div0.mod_mul_r (_+_)), Nat.Div0.mod_mul_r.
      rewrite eqb_div_mod_pow_2_iff.
      rewrite Nat.div_add, Nat.Div0.mod_add
        by apply pow2_nonzero.
      rewrite (Nat.mod_small l), (Nat.div_small l) by easy.
      simpl.
      rewrite !andb_assoc, (andb_comm _ (_ =? l)), <- !andb_assoc.
      rewrite andb_if.
      reflexivity.
    } 
    rewrite big_sum_if_eq_C'.
    pose proof (Nat.mod_upper_bound (i/2^padr) _ (pow2_nonzero a)).
    simplify_bools_lia_one_kernel.
    rewrite andb_assoc, andb_comm, andb_assoc.
    rewrite <- eqb_div_mod_pow_2_iff.
    rewrite (Nat.add_comm ((k/2^padm) mod 2^a)).
    rewrite <- Nat.div_mod_eq.
    rewrite andb_comm, <- eqb_div_mod_pow_2_iff.
    rewrite (Nat.add_comm (k mod 2^padm)).
    rewrite <- Nat.div_mod_eq.
    reflexivity.
  }
  rewrite big_sum_if_eq_C'.
  match goal with
  |- context[if ?b then _ else _] =>
    replace b with true by (symmetry; 
    rewrite Nat.ltb_lt; show_moddy_lt)
  end.
  rewrite (Nat.mul_comm (2^padm)), Nat.div_add, mod_div by show_nonzero.
  simpl.
  rewrite (Nat.mul_comm (2^a) (_ / _)), !Nat.Div0.mod_add,
    Nat.div_add, mod_div, !Nat.Div0.mod_mod by show_nonzero.
  simpl.
  rewrite !Nat.Div0.div_div.
  do 7 f_equal.
  lia.
Qed.

Lemma matrix_kk_pullthrough_id_r_r {padl padm padr a m} {f}
  (Hf : bipermutation (m + (padl + a + padm + a + padr)) f)
  (Hfpad : forall b, b < a ->
    f (m + padr + b) = m + padr + a + padm + b)
  (A : Matrix (2^a) (2^a)) (HA : WF_Matrix A) :
  @eq (Matrix (2^m) (2^padl*2^a*2^padm*2^a*2^padr))
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _
    (matrix_of_biperm (padl + a + padm + a + padr) m f)
    (I (2^padl) ⊗ A ⊗ I (2^padm * 2^a * 2^padr)))
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _
    (matrix_of_biperm (padl + a + padm + a + padr) m f)
    (I (2^padl * 2^a * 2^padm) ⊗ A ⊤ ⊗ I (2^padr))).
Proof.
  apply transpose_matrices.
  apply mat_equiv_eq; [auto_wf..|].
  rewrite !Mmult_transpose, !(fun x y => kron_transpose' _ _ x y).
  rewrite !id_transpose_eq.
  rewrite <- !Nat.pow_add_r.
  rewrite matrix_of_biperm_transpose by easy.
  rewrite !Nat.pow_add_r.
  apply matrix_kk_pullthrough_id_l_l; [..|auto with wf_db].
  - rewrite Nat.add_comm.
    now apply flip_biperm_bipermutation.
  - intros b Hb.
    unfold flip_biperm.
    simplify_bools_lia.
    replace (padr + b + m) with (m + padr + b) by lia.
    rewrite Hfpad by lia.
    bdestructΩ'.
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

Lemma n_m_cup_cap_bounded n m k : 
  k < n + n + (m + m) ->
  n_m_cup_cap n m k < n + n + (m + m).
Proof.
  intros Hk.
  now apply n_m_cup_cap_bipermutation.
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

Lemma n_m_cup_cap_absorb_stacked_swap_perm_l padl padr m :
  forall k, k < (padl + 1 + padr) + (padl + 1 + padr) + (m + m) ->
  biperm_compose_perm_r (m + m) ((padl + 1 + padr) + (padl + 1 + padr))
  (n_m_cup_cap m (padl + 1 + padr))
  (stack_perms (padl+padl+2) (padr+padr)
    (stack_perms (padl + padl) 2 idn (swap_perm 0 1 2)) idn) k =
  n_m_cup_cap m (padl + 1 + padr) k.
Proof.
  intros k Hk.
  unfold biperm_compose_perm_r.
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
Qed.

Lemma n_m_cup_cap_absorb_swap_block_perm_l padl padm padr m :
  forall k, k < (padl + 1 + padm + 1 + padr) 
    + (padl + 1 + padm + 1 + padr) + (m + m) ->
  biperm_compose_perm_r (m + m) 
    ((padl + 1 + padm + 1 + padr) + (padl + 1 + padm + 1 + padr))
  (n_m_cup_cap m (padl + 1 + padm + 1 + padr))
  (swap_block_perm (padl + padl) (padm + padm) 2) k =
  n_m_cup_cap m (padl + 1 + padm + 1 + padr) k.
Proof.
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


Lemma matrix_of_biperm_compose_perm_l n m f g
  (Hf : bipermutation (m + n) f)
  (Hg : permutation n g) : 
  matrix_of_biperm n m (biperm_compose_perm_r m n f g) ≡
  matrix_of_biperm n m f × 
  perm_to_matrix n (reflect_perm n ∘ perm_inv n g ∘ reflect_perm n)%prg.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (biperm_compose_perm_r_biperm _ _ f g Hf Hg) as Hfg.
  rewrite (Nat.add_comm m n) in *.
  pose proof (fun i Hi => proj1 (Hfg i Hi)) as Hfgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hfg i Hi))) as Hfgne.
  pose proof (fun i Hi => proj2 (proj2 (Hfg i Hi))) as Hfgeq.
  pose proof (perm_inv_permutation n g Hg) as Hginv.
  pose proof (perm_inv_bounded n g) as Hginvbdd.
  pose proof (perm_inv_is_linv_of_permutation n g Hg) as Hglinv.
  pose proof (perm_inv_is_rinv_of_permutation n g Hg) as Hgrinv.
  pose proof (permutation_compose _ _ _ 
    (permutation_compose _ _ _ (reflect_perm_permutation n) Hginv)
    (reflect_perm_permutation n)) as Hgreflperm.
  pose proof (permutation_is_bounded _ _ Hgreflperm) as Hgreflbdd.
  unfold Basics.compose in *.

  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite matrix_of_biperm_funbool_conj.
  rewrite 2!Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits by easy.
  rewrite <- Mmult_assoc.
  rewrite matrix_of_biperm_funbool_conj.
  apply f_equal_if; [|easy..].
  rewrite <- 2!funbool_to_nat_add_pow2_join.
  rewrite (Nat.add_comm n m).
  apply eq_iff_eq_true; 
  rewrite 2!number_preserved_iff by apply funbool_to_nat_bound. 
  rewrite (Nat.add_comm m n).
  rewrite !nat_to_funbool_inverse by easy.
  do 3 setoid_rewrite testbit_funbool_to_nat.
  etransitivity.
  1: {
    apply forall_iff; intros s.
    apply impl_iff; intros Hs.
    instantiate (1 := (if s <? m then if f s <? m then _ else _ 
      else if f (m + g (s - m)) <? m then _ else _)).
    bdestruct (s <? m).
    - rewrite biperm_compose_perm_r_ltb_small by easy.
      bdestruct (f s <? m); unfold biperm_compose_perm_r; simplify_bools_lia;
      rewrite ?add_sub'; reflexivity.
    - rewrite biperm_compose_perm_r_ltb_big by lia.
      bdestruct (f (m + g (s - m)) <? m); unfold biperm_compose_perm_r; 
      simplify_bools_lia; rewrite ?add_sub'; reflexivity.
  }
  etransitivity.
  2: {
    symmetry.
    apply forall_iff; intros s.
    apply impl_iff; intros Hs.
    instantiate (1 := (if s <? m then if f s <? m then _ else _ 
      else if f s <? m then _ else _)).
    bdestruct (s <? m).
    - rewrite nat_to_funbool_eq.
      bdestruct (f s <? m); [reflexivity|].
      pose proof (Hfbdd s Hs).
      unfold reflect_perm.
      simplify_bools_lia.
      match goal with
      |- context[ n - S (n - S ?k) ] => 
        replace (n - S (n - S k)) with k by lia
      end.
      pose proof (Hginvbdd (f s - m) ltac:(lia)).
      do 2 simplify_bools_lia_one_kernel.
      match goal with
      |- context[ n - S (n - S ?k) ] => 
        replace (n - S (n - S k)) with k by lia
      end.
      reflexivity.
    - rewrite 2!nat_to_funbool_eq'.
      unfold reflect_perm.
      simplify_bools_lia.
      pose proof (Hfbdd s Hs).
      do 2 match goal with
      |- context[ n - S (n - S ?k) ] => 
        replace (n - S (n - S k)) with k by lia
      end.
      pose proof (Hginvbdd (s - m)).
      pose proof (Hginvbdd (f s - m)).
      do 5 simplify_bools_lia_one_kernel.
      do 2 match goal with
      |- context[ n - S (n - S ?k) ] => 
        replace (n - S (n - S k)) with k by lia
      end.
      reflexivity.
  } 
  split.
  - intros H s Hs.
    pose proof (Hfbdd s Hs).
    bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'.
    + generalize (H (f s) (Hfbdd s Hs)).
      bdestructΩ'; rewrite ?Hfeq in * by lia; try lia.
      easy.
    + generalize (H (perm_inv n g (s - m) + m) 
      ltac:(pose (Hginvbdd (s - m)); lia)).
      simplify_bools_lia.
      rewrite Nat.add_sub.
      rewrite Hgrinv by lia.
      rewrite Nat.add_sub_assoc, add_sub' by lia.
      now simplify_bools_lia_one_kernel.
  - intros H s Hs.
    pose proof (Hfbdd s Hs).
    bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'.
    + pose proof (Hgbdd (s - m) ltac:(lia)).
      pose proof (Hfbdd (m + g (s - m)) ltac:(lia)).
      generalize (H (f (m + g (s - m))) ltac:(easy)).
      bdestructΩ'; rewrite ?Hfeq in * by lia; try lia.
      rewrite add_sub', Hglinv by lia.
      easy.
    + pose proof (Hgbdd (s - m) ltac:(lia)).
      generalize (H (m + g (s - m)) ltac:(lia)).
      simplify_bools_lia.
      rewrite add_sub'.
      now rewrite Hglinv by lia.
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

Lemma matrix_of_biperm_compose_perm_r n m f g
  (Hf : bipermutation (m + n) f)
  (Hg : permutation m g) : 
  matrix_of_biperm n m (biperm_compose_perm_l m n f g) ≡
  perm_to_matrix m (reflect_perm m ∘ g ∘ reflect_perm m)%prg ×
  matrix_of_biperm n m f.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (biperm_compose_perm_l_biperm _ _ f g Hf Hg) as Hfg.
  rewrite (Nat.add_comm m n) in *.
  pose proof (fun i Hi => proj1 (Hfg i Hi)) as Hfgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hfg i Hi))) as Hfgne.
  pose proof (fun i Hi => proj2 (proj2 (Hfg i Hi))) as Hfgeq.
  pose proof (perm_inv_permutation m g Hg) as Hginv.
  pose proof (perm_inv_bounded m g) as Hginvbdd.
  pose proof (perm_inv_is_linv_of_permutation m g Hg) as Hglinv.
  pose proof (perm_inv_is_rinv_of_permutation m g Hg) as Hgrinv.
  pose proof (permutation_compose _ _ _ 
    (permutation_compose _ _ _ (reflect_perm_permutation m) Hg)
    (reflect_perm_permutation m)) as Hgreflperm.
  pose proof (permutation_is_bounded _ _ Hgreflperm) as Hgreflbdd.
  unfold Basics.compose in *.

  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite matrix_of_biperm_funbool_conj.
  rewrite <- Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits_l by easy.
  erewrite f_to_vec_eq.
  2: {
    intros k Hk.
    rewrite perm_inv_compose_alt by 
      (try apply permutation_compose; auto with perm_db).
    rewrite perm_inv_compose_alt by auto with perm_db perm_bounded_db.
    rewrite (reflect_perm_inv m k) by easy.
    rewrite reflect_perm_inv by auto with perm_db perm_bounded_db.
    reflexivity.
  }
  rewrite matrix_of_biperm_funbool_conj.
  apply f_equal_if; [|easy..].
  rewrite <- funbool_to_nat_add_pow2_join.
  rewrite <- (funbool_to_nat_add_pow2_join _ _ (
    fun x => nat_to_funbool m i (reflect_perm m 
      (perm_inv m g (reflect_perm m x)))
  )).
  rewrite (Nat.add_comm n m).
  apply eq_iff_eq_true; 
  rewrite 2!number_preserved_iff by apply funbool_to_nat_bound. 
  rewrite (Nat.add_comm m n).
  rewrite !nat_to_funbool_inverse by easy.
  do 3 setoid_rewrite testbit_funbool_to_nat.
  etransitivity.
  1: {
    apply forall_iff; intros s.
    apply impl_iff; intros Hs.
    instantiate (1 := (if s <? m then if f (g s) <? m then _ else _ 
      else if f s <? m then _ else _)).
    bdestruct (s <? m).
    - rewrite biperm_compose_perm_l_ltb_small by easy.
      bdestruct (f (g s) <? m); unfold biperm_compose_perm_l; simplify_bools_lia;
      reflexivity.
    - rewrite biperm_compose_perm_l_ltb_big by lia.
      bdestruct (f s <? m); unfold biperm_compose_perm_l; 
      simplify_bools_lia; reflexivity.
  }
  etransitivity.
  2: {
    symmetry.
    apply forall_iff; intros s.
    apply impl_iff; intros Hs.
    instantiate (1 := (if s <? m then if f s <? m then _ else _ 
      else if f s <? m then _ else _)).
    bdestruct (s <? m).
    - rewrite nat_to_funbool_eq.
      unfold reflect_perm.
      do 2 simplify_bools_lia_one_kernel.
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      pose proof (Hginvbdd s ltac:(lia)).
      do 2 simplify_bools_lia_one_kernel.
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      bdestruct (f s <? m); [|reflexivity].
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      pose proof (Hginvbdd (f s)) ltac:(lia).
      do 2 simplify_bools_lia_one_kernel.
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      reflexivity.
    - rewrite nat_to_funbool_eq'.
      bdestruct (f s <? m); [|reflexivity].
      unfold reflect_perm.
      simplify_bools_lia.
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      pose proof (Hginvbdd (f s)).
      do 2 simplify_bools_lia_one_kernel.
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      reflexivity.
  } 
  split.
  - intros H s Hs.
    pose proof (Hfbdd s Hs).
    bdestruct (s <? m).
    + pose proof (Hginvbdd s ltac:(lia)).
      generalize (H (perm_inv m g s) ltac:(lia)).
      rewrite Hgrinv by lia.
      bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'. 
  - intros H s Hs.
    pose proof (Hfbdd s Hs).
    bdestruct (s <? m).
    + pose proof (Hgbdd s ltac:(lia)).
      generalize (H (g s) ltac:(lia)).
      rewrite Hglinv by lia.
      bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'.
Qed.



Lemma matrix_of_biperm_pow_2_l n m f 
  (Hf : bipermutation (n + m) f) k : 
  matrix_of_biperm n m f 0 (2^k) = 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  unfold matrix_of_biperm.
  simplify_bools_moddy_lia_one_kernel.
  bdestruct_one; [easy|].
  apply if_false.
  rewrite <- Nat.pow_add_r, Nat.add_0_r.
  rewrite <- not_true_iff_false.
  rewrite number_preserved_iff_all_lt_eq.
  intros Hcontra.
  bdestruct (k <? n); 
  [|pose proof (Nat.pow_le_mono_r 2 n k); lia].
  specialize (Hcontra (k + m) ltac:(lia)).
  rewrite 2!Nat.pow2_bits_eqb in Hcontra.
  pose proof (Hfne (k + m) ltac:(lia)).
  revert Hcontra.
  bdestructΩ'.
Qed.

Lemma matrix_of_biperm_pow_2_r n m f 
  (Hf : bipermutation (n + m) f) k : 
  matrix_of_biperm n m f (2^k) 0 = 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  unfold matrix_of_biperm.
  simplify_bools_moddy_lia_one_kernel.
  bdestruct_one; [easy|].
  apply if_false.
  rewrite <- not_true_iff_false.
  rewrite number_preserved_iff_all_lt_eq.
  intros Hcontra.
  bdestruct (k <? m); 
  [|pose proof (Nat.pow_le_mono_r 2 m k); lia].
  specialize (Hcontra (k) ltac:(lia)).
  rewrite 2!Nat.pow2_bits_eqb in Hcontra.
  pose proof (Hfne (k) ltac:(lia)).
  revert Hcontra.
  bdestructΩ'.
Qed.



Lemma matrix_of_biperm_sum_pows_2_l_l n m f 
  (Hf : bipermutation (n + m) f) k l : k < n -> l < n ->
  matrix_of_biperm n m f 0 (2^k + 2^l) =
  if f (m + k) =? m + l then C1 else 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  intros Hk Hl.
  bdestruct (k =? l).
  1:{
    replace (2 ^ k + 2 ^ l) with (2 ^ (S k)) by (cbn; subst; lia).
    rewrite matrix_of_biperm_pow_2_l by easy. 
    pose proof (Hfne (m + l)); bdestructΩ'.
  }
  unfold matrix_of_biperm.
  simplify_bools_moddy_lia_one_kernel.
  bdestruct_one.
  - pose proof (Nat.pow_le_mono_r 2 k (n - 1) ltac:(lia) ltac:(lia)).
    pose proof (Nat.pow_le_mono_r 2 l (n - 1) ltac:(lia) ltac:(lia)).
    destruct n; [easy|].
    simpl in *.
    rewrite Nat.sub_0_r, Nat.add_0_r in *.
    assert (Hkl : 2 ^ k = 2 ^ l) by lia.
    apply (f_equal (Nat.log2)) in Hkl.
    rewrite 2!Nat.log2_pow2 in Hkl by lia.
    pose proof (Hfne k).
    bdestructΩ'.
  - apply f_equal_if; [|easy..].
    apply eq_iff_eq_true.
    rewrite (Nat.add_comm n m), number_preserved_iff by show_nonzero.
    rewrite Nat.eqb_eq.
    split.
    + intros Hall.
      generalize (Hall (m + k) ltac:(lia)).
      simplify_bools_lia.
      rewrite add_sub'.
      rewrite !testbit_sum_pows_2_ne by easy.
      rewrite Nat.bits_0.
      pose proof (Hfne (m + k) ltac:(lia)).
      bdestructΩ'simp.
    + intros Hfmk.
      pose proof (proj1 (bipermutation_eq_iff (m+k) (m+l) Hf
        ltac:(lia) ltac:(lia)) ltac:(lia)) as Hfml.
      intros s Hs.
      rewrite !testbit_sum_pows_2_ne by easy.
      rewrite !Nat.bits_0.
      bdestruct (s <? m); bdestruct (f s <? m);
      [pose proof (bipermutation_eq_iff s (m+l) Hf ltac:(lia) ltac:(lia)); 
        pose proof (bipermutation_eq_iff (m+k) s Hf ltac:(lia) ltac:(lia));
      bdestructΩ'..|].
      replace_bool_lia (f s - m =? k) (f s =? m + k).
      replace_bool_lia (f s - m =? l) (f s =? m + l).
      rewrite 2!(bipermutation_eqb_iff _ _ Hf) by lia.
      rewrite Hfmk, <- Hfml.
      bdestructΩ'.
Qed.



Lemma matrix_of_biperm_sum_pows_2_r_r n m f 
  (Hf : bipermutation (n + m) f) k l : k < m -> l < m ->
  matrix_of_biperm n m f (2^k + 2^l) 0 =
  if f k =? l then C1 else 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  intros Hk Hl.
  bdestruct (k =? l).
  1:{
    replace (2 ^ k + 2 ^ l) with (2 ^ (S k)) by (cbn; subst; lia).
    rewrite matrix_of_biperm_pow_2_r by easy. 
    pose proof (Hfne k); bdestructΩ'.
  }
  unfold matrix_of_biperm.
  simplify_bools_moddy_lia_one_kernel.
  pose proof (sum_ne_pows_2_lt_pow_2_S m k l).
  simplify_bools_lia_one_kernel.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite (Nat.add_comm n m), number_preserved_iff_all_lt_eq.
  rewrite Nat.eqb_eq.
  split.
  - intros Hall.
    generalize (Hall k ltac:(lia)).
    simplify_bools_lia.
    rewrite !testbit_sum_pows_2_ne by easy.
    pose proof (Hfne (k) ltac:(lia)).
    bdestructΩ'simp.
  - intros Hfmk.
    pose proof (proj1 (bipermutation_eq_iff (k) (l) Hf
      ltac:(lia) ltac:(lia)) ltac:(lia)) as Hfml.
    intros s Hs.
    rewrite !testbit_sum_pows_2_ne by easy.
    rewrite 2!(bipermutation_eqb_iff _ _ Hf) by lia.
    bdestructΩ'.
Qed.

Lemma matrix_of_biperm_sum_pows_2_l_r n m f 
  (Hf : bipermutation (n + m) f) k l : k < m -> l < n ->
  matrix_of_biperm n m f (2^k) (2^l) =
  if f k =? m + l then C1 else 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  intros Hk Hl.
  unfold matrix_of_biperm.
  pose proof (Nat.pow_lt_mono_r 2 k m ltac:(lia) ltac:(lia)).
  pose proof (Nat.pow_lt_mono_r 2 l n ltac:(lia) ltac:(lia)).
  do 2 simplify_bools_lia_one_kernel.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite (Nat.add_comm n m), number_preserved_iff by easy.
  rewrite Nat.eqb_eq.
  split.
  - intros Hall.
    generalize (Hall k ltac:(lia)).
    simplify_bools_lia.
    rewrite !Nat.pow2_bits_eqb.
    pose proof (Hfne (k) ltac:(lia)).
    bdestructΩ'simp.
  - intros Hfmk.
    pose proof (proj1 (bipermutation_eq_iff (k) (m+l) Hf
      ltac:(lia) ltac:(lia)) ltac:(lia)) as Hfml.
    intros s Hs.
    rewrite !Nat.pow2_bits_eqb by easy.
    pose proof (bipermutation_eq_iff s (m+l) Hf ltac:(lia) ltac:(lia)).
    pose proof (bipermutation_eq_iff k s Hf ltac:(lia) ltac:(lia)).
    bdestructΩ'.
Qed.

Lemma matrix_of_biperm_inj n m f g 
  (Hf : bipermutation (n + m) f) (Hg : bipermutation (n + m) g) : 
  matrix_of_biperm n m f ≡ matrix_of_biperm n m g ->
  perm_eq (n + m) f g.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (fun i Hi => proj1 (Hg i Hi)) as Hgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hg i Hi))) as Hgne.
  pose proof (fun i Hi => proj2 (proj2 (Hg i Hi))) as Hgeq.
  intros Hequiv k Hk.
  bdestruct (k <? m); bdestruct (f k <? m).
  - pose proof (Hfne k Hk).
    generalize (Hequiv (2^k + 2^(f k)) 0 
      ltac:(apply sum_ne_pows_2_lt_pow_2_S; lia) ltac:(show_nonzero)).
    rewrite 2!matrix_of_biperm_sum_pows_2_r_r by easy.
    simplify_bools_lia_one_kernel.
    bdestructΩ'.
    pose proof C1_nonzero. congruence.
  - pose proof (Hfbdd k Hk).
    generalize (Hequiv (2^k) (2^(f k - m))
      ltac:(apply Nat.pow_lt_mono_r; lia) 
      ltac:(apply Nat.pow_lt_mono_r; lia)).
    rewrite 2!matrix_of_biperm_sum_pows_2_l_r by easy + lia.
    bdestructΩ'.
    pose proof C1_nonzero; congruence.
  - pose proof (Hfbdd k Hk).
    generalize (Hequiv (2^(f k)) (2^(k - m))
      ltac:(apply Nat.pow_lt_mono_r; lia) 
      ltac:(apply Nat.pow_lt_mono_r; lia)).
    rewrite 2!matrix_of_biperm_sum_pows_2_l_r by easy + lia.
    replace (m + (k - m)) with k by lia.
    rewrite Hfeq by lia.
    rewrite (bipermutation_eqb_iff _ _ Hg) by lia.
    bdestructΩ'; 
    pose proof C1_nonzero; congruence.
  - pose proof (Hfne k Hk).
    pose proof (Hfbdd k Hk).
    generalize (Hequiv 0 (2^(k-m) + 2^(f k - m))
      ltac:(show_nonzero) ltac:(apply sum_ne_pows_2_lt_pow_2_S; lia)).
    rewrite 2!matrix_of_biperm_sum_pows_2_l_l by easy + lia.
    replace (m + (k - m)) with k by lia.
    replace (m + (f k - m)) with (f k) by lia.
    bdestructΩ'.
    pose proof C1_nonzero. 
    congruence.
Qed.

(* Create HintDb biperm_db. *)
Create HintDb biperm_db_alt.



Hint Resolve idn_biperm_bipermutation flip_biperm_bipermutation
  n_m_cup_cap_bipermutation remove_swap_bipermutation
  stack_biperms_bipermutation compose_swap_biperm_gen_bipermutation
  biperm_of_zxbiperm_folio_bipermutation
  bipermutation_is_bounded bipermutation_involutive
  compose_swap_biperm_bipermutation compose_cap_biperm_l_bipermutation
  compose_cup_biperm_l_bipermutation 
  biperm_compose_perm_l_biperm biperm_compose_perm_r_biperm
  : biperm_db.

Hint Resolve idn_biperm_bipermutation flip_biperm_bipermutation
  n_m_cup_cap_bipermutation remove_swap_bipermutation
  stack_biperms_bipermutation compose_swap_biperm_gen_bipermutation
  biperm_of_zxbiperm_folio_bipermutation
  bipermutation_is_bounded bipermutation_involutive
  compose_swap_biperm_bipermutation compose_cap_biperm_l_bipermutation
  compose_cup_biperm_l_bipermutation 
  biperm_compose_perm_l_biperm biperm_compose_perm_r_biperm
  : biperm_db_alt.

Hint Extern 0 (permutation _ _) => auto with perm_db : biperm_db biperm_db_alt.

Hint Extern 0 (_ < _) => auto with perm_bounded_db : biperm_db biperm_db_alt.

Hint Extern 4 (bipermutation (?n + ?m) _) => 
  (* idtac n m; *) rewrite (Nat.add_comm n m); auto with biperm_db_alt : biperm_db.

Hint Extern 4 (bipermutation (?n) _) => 
  let k := fresh in 
  evar (k : nat); 
  replace n with k;
  unfold k;
  auto with biperm_db_alt;
  lia : biperm_db.

Hint Extern 4 (permutation (?n) _) => 
  let k := fresh in 
  evar (k : nat); 
  replace n with k;
  unfold k;
  auto with biperm_db_alt;
  lia : biperm_db.






Lemma n_m_cup_cap_bipermutation' ncup ncap : 
  bipermutation (ncap + ncap + (ncup + ncup))
  (n_m_cup_cap ncup ncap).
Proof.
  auto with biperm_db.
Qed.

Hint Resolve n_m_cup_cap_bipermutation' : biperm_db biperm_db_alt.


Lemma number_preserved_iff' i j n m (Hi : i < 2 ^ n) f : 
  number_preserved (j * 2 ^ n + i) f (m + n) = true <->
  (forall s : nat,
  s < m + n ->
  if s <? n
  then if f s <? n
    then Nat.testbit i s = Nat.testbit i (f s)
    else Nat.testbit i s = Nat.testbit j (f s - n)
  else if f s <? n
    then Nat.testbit j (s - n) = Nat.testbit i (f s)
    else Nat.testbit j (s - n) = Nat.testbit j (f s - n)).
Proof.
  rewrite (Nat.add_comm m n).
  now apply number_preserved_iff.
Qed.


Lemma matrix_of_stack_biperms n0 m0 n1 m1 f g 
  (Hf : bipermutation (n0 + m0) f)
  (Hg : bipermutation (n1 + m1) g) : 
  matrix_of_biperm (n0 + n1) (m0 + m1) (stack_biperms m0 n0 m1 n1 f g) =
  matrix_of_biperm n1 m1 g ⊗ matrix_of_biperm n0 m0 f.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (fun i Hi => proj1 (Hg i Hi)) as Hgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hg i Hi))) as Hgne.
  pose proof (fun i Hi => proj2 (proj2 (Hg i Hi))) as Hgeq.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold kron.
  unfold matrix_of_biperm.
  do 6 simplify_bools_moddy_lia_one_kernel.
  rewrite Cmult_if_if_1_l.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true;
  rewrite andb_true_iff.
  rewrite !number_preserved_iff' by show_moddy_lt.
  split.
  - intros H.
    split.
    + intros s Hs.
      rewrite !testbit_div_pow2.
      bdestruct (s <? m1).
      * generalize (H (m0 + s) ltac:(lia)).
        simplify_bools_lia_one_kernel.
        unfold stack_biperms.
        rewrite add_sub'.
        do 3 simplify_bools_lia_one_kernel.
        pose proof (Hgbdd s ltac:(lia)).
        bdestructΩ'; intros ->; f_equal; lia.
      * generalize (H (m0 + n0 + s) ltac:(lia)).
        simplify_bools_lia_one_kernel.
        unfold stack_biperms.
        rewrite add_sub'.
        do 4 simplify_bools_lia_one_kernel.
        replace (m0 + n0 + s - (m0 + m1)) with (n0 + s - m1) by lia.
        rewrite Nat.add_sub_assoc by lia.
        bdestructΩ'; intros ->; f_equal; lia.
    + intros s Hs.
      rewrite !testbit_mod_pow2.
      bdestruct (s <? m0).
      * generalize (H (s) ltac:(lia)).
        simplify_bools_lia_one_kernel.
        unfold stack_biperms.
        do 2 simplify_bools_lia_one_kernel.
        pose proof (Hfbdd s ltac:(lia)).
        bdestructΩ'; intros ->; f_equal; lia.
      * simplify_bools_lia_one_kernel.
        generalize (H (m1+s) ltac:(lia)).
        simplify_bools_lia_one_kernel.
        unfold stack_biperms.
        do 4 simplify_bools_lia_one_kernel.
        rewrite add_sub'.
        replace (m1 + s - (m0 + m1)) with (s - m0) by lia.
        pose proof (Hfbdd s).
        bdestructΩ'; intros ->; f_equal; lia.
  - intros [Hhigh Hlow].
    intros s Hs.
    bdestruct (s <? m0 + m1);
    [bdestruct (s <? m0) | bdestruct (s <? m0 + m1 + n0)].
    + generalize (Hlow s ltac:(lia)).
      rewrite !testbit_mod_pow2.
      simplify_bools_lia_one_kernel.
      pose proof (Hfbdd s).
      bdestruct_one; intros ->; 
      unfold stack_biperms; bdestructΩ'; f_equal; lia.
    + generalize (Hhigh (s - m0) ltac:(lia)).
      rewrite !testbit_div_pow2.
      simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub_assoc, add_sub' by lia.
      pose proof (Hgbdd (s - m0)).
      bdestruct_one; intros ->; 
      unfold stack_biperms; bdestructΩ'; f_equal; lia.
    + generalize (Hlow (s - m1) ltac:(lia)).
      rewrite !testbit_mod_pow2.
      do 2 simplify_bools_lia_one_kernel.
      replace (s - m1 - m0) with (s - (m0 + m1)) by lia.
      pose proof (Hfbdd (s - m1)).
      bdestruct_one; intros ->; 
      unfold stack_biperms; bdestructΩ'; f_equal; lia.
    + generalize (Hhigh (s - (n0 + m0)) ltac:(lia)).
      rewrite !testbit_div_pow2.
      simplify_bools_lia_one_kernel.
      replace (n0 + (s - (n0 + m0) - m1)) with (s - (m0 + m1)) by lia.
      pose proof (Hgbdd (s - (m0 + n0))).
      bdestruct_one; intros ->;
      unfold stack_biperms; bdestructΩ';
      rewrite ?(Nat.add_comm n0 m0) in *; f_equal; lia.
Qed.

Lemma matrix_of_idn_biperm n : 
  matrix_of_biperm n n (idn_biperm n) = I (2 ^ n).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold matrix_of_biperm, I.
  simplify_bools_lia.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite Nat.eqb_eq, <- bits_inj_upto_small by eauto.
  rewrite number_preserved_iff by easy.
  split.
  - intros H s Hs.
    generalize (H s ltac:(lia)).
    unfold idn_biperm.
    simplify_bools_lia.
    intros ->; f_equal; lia.
  - intros H s Hs.
    unfold idn_biperm.
    simplify_bools_lia.
    bdestructΩ'; rewrite H; f_equal; lia.
Qed.

Definition realize_biperm_data (lperm rperm : nat -> nat) 
  (nid ncup ncap : nat) :=
  biperm_compose_perm_l (ncap + ncap + nid) (ncup + ncup + nid)
    (biperm_compose_perm_r (ncap + ncap + nid) (ncup + ncup + nid)
    (stack_biperms  nid nid (ncap + ncap) (ncup + ncup)
      (idn_biperm nid) (n_m_cup_cap ncup ncap))
    (reflect_perm (ncup + ncup + nid) ∘ 
      perm_inv (ncup + ncup + nid) lperm ∘
      reflect_perm (ncup + ncup + nid))%prg)
    (reflect_perm (ncap + ncap + nid) ∘ 
      rperm ∘
      reflect_perm (ncap + ncap + nid))%prg.

Lemma realize_biperm_data_bipermutation {lperm rperm} {nid ncup ncap} 
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  bipermutation ((ncup + ncup + nid) + (ncap + ncap + nid))
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  unfold realize_biperm_data.
  rewrite Nat.add_comm.
  apply biperm_compose_perm_l_biperm; [|auto with perm_db].
  apply biperm_compose_perm_r_biperm; [|auto with perm_db].
  auto with biperm_db.
Qed.

Lemma matrix_of_realize_biperm_data {lperm rperm} {nid ncup ncap} 
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid)
    (realize_biperm_data lperm rperm nid ncup ncap) =
  perm_to_matrix (ncap + ncap + nid) rperm × 
  (matrix_of_biperm (ncup + ncup) (ncap + ncap) (n_m_cup_cap ncup ncap)
    ⊗ I (2^nid)) ×
    perm_to_matrix (ncup + ncup + nid) lperm.
Proof.
  apply mat_equiv_eq; auto with wf_db.
  unfold realize_biperm_data.
  rewrite matrix_of_biperm_compose_perm_r by auto with biperm_db.
  rewrite matrix_of_biperm_compose_perm_l by auto with biperm_db.
  rewrite 2!(Nat.add_comm _ nid) in *.
  rewrite matrix_of_stack_biperms by auto with biperm_db.
  rewrite matrix_of_idn_biperm.
  rewrite <- Mmult_assoc.
  repeat apply mmult_mat_equiv_morph; try easy.
  - apply perm_to_matrix_perm_eq.
    intros k Hk.
    unfold Basics.compose.
    now rewrite 2!reflect_perm_invol.
  - apply perm_to_matrix_perm_eq.
    intros k Hk.
    unfold Basics.compose.
    rewrite 2!perm_inv_compose_alt by auto with perm_db perm_bounded_db.
    rewrite !reflect_perm_inv by auto with perm_bounded_db.
    rewrite 2!reflect_perm_invol.
    now apply perm_inv_perm_inv.
Qed.

Record NF_biperm := {
  lperm' : nat -> nat;
  rperm' : nat -> nat;
  nid' : nat;
  ncup' : nat;
  ncap' : nat
}.

Definition uncurry_NF_biperm 
  {A : (nat -> nat) -> (nat -> nat) -> nat -> nat -> nat -> Type} 
  (f : forall lperm rperm nid ncup ncap, A lperm rperm nid ncup ncap) :
  forall bp : NF_biperm, 
  A bp.(lperm') bp.(rperm') bp.(nid') bp.(ncup') bp.(ncap') :=
  fun bp => 
  f bp.(lperm') bp.(rperm') bp.(nid') bp.(ncup') bp.(ncap').

Definition curry_NF_biperm {A : NF_biperm -> Type} 
  (f : forall bp : NF_biperm, A bp) :
  forall lperm rperm nid ncup ncap, 
    A (Build_NF_biperm lperm rperm nid ncup ncap) :=
  fun lperm rperm nid ncup ncap => 
  f (Build_NF_biperm lperm rperm nid ncup ncap).

Lemma curry_uncurry_NF_biperm {A} f : 
  forall lperm rperm nid ncup ncap, 
  curry_NF_biperm (@uncurry_NF_biperm A f) 
    lperm rperm nid ncup ncap = f lperm rperm nid ncup ncap.
Proof.
  reflexivity.
Qed.

Lemma uncurry_curry_NF_biperm {A} f : 
  forall bp,
  uncurry_NF_biperm (@curry_NF_biperm (fun _ => A) f) bp = 
    f bp.
Proof.
  intros [];
  reflexivity.
Qed.

Lemma curry_uncurry_NF_biperm_eq {A} f :  
  curry_NF_biperm (@uncurry_NF_biperm A f) = f.
Proof.
  do 5 (apply functional_extensionality_dep; intros).
  apply curry_uncurry_NF_biperm.
Qed.

Lemma uncurry_curry_NF_biperm_eq {A} f :  
  uncurry_NF_biperm (@curry_NF_biperm (fun _ => A) f) = f.
Proof.
  apply functional_extensionality_dep; intros;
  apply uncurry_curry_NF_biperm.
Qed.

Definition WF_NF_biperm (b : NF_biperm) :=
  permutation (b.(ncup') + b.(ncup') + b.(nid')) b.(lperm') /\
  permutation (b.(ncap') + b.(ncap') + b.(nid')) b.(rperm').

(* TODO: Move to permaux *)
Lemma max_ltb n m : 
  Nat.max n m = if n <? m then m else n.
Proof. bdestructΩ'. Qed.

Lemma n_m_cup_cap_twice_plus n m a k :
  a * 2 + k < n + n + m + m ->
  n_m_cup_cap n m (a*2 + k) = 
  a*2 + n_m_cup_cap n m k.
Proof.
  replace (a*2) with (a+a) by lia.
  apply n_m_cup_cap_double_plus.
Qed.

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

Local Arguments Nat.sub : simpl never.
Local Arguments Nat.div : simpl never.
Local Arguments Nat.divmod : simpl never.
Local Arguments Nat.modulo : simpl never.
Local Arguments perm_inv : simpl never.


Lemma swap_perm_invol' a b n k : a < n -> b < n -> 
  swap_perm a b n (swap_perm a b n k) = k.
Proof.
  intros Ha Hb.
  pose proof (swap_perm_invol a b n Ha Hb) as H.
  apply (f_equal_inv k) in H.
  apply H.
Qed.

Lemma n_m_cup_cap_absorb_tensor_2_idn_swap_perm_l n m 
  a b (Ha : a < n) (Hb : b < n) :
  perm_eq (n + n + m + m)
  (biperm_compose_perm_r (m + m) 
    (n + n)
  (n_m_cup_cap m n)
  (tensor_perms n 2 (swap_perm a b n) idn))
  (n_m_cup_cap m n).
Proof.
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
Qed.  


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

Definition realize_NF_biperm : NF_biperm -> nat -> nat :=
  uncurry_NF_biperm realize_biperm_data.

Lemma realize_NF_biperm_constructor lperm rperm nid ncup ncap : 
  realize_NF_biperm {|lperm':=lperm; rperm':=rperm; 
    nid':=nid; ncup':=ncup; ncap':=ncap|} = 
  realize_biperm_data lperm rperm nid ncup ncap.
Proof. easy. Qed.



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

Lemma n_m_cup_cap_comm n m : 
  n_m_cup_cap n m = n_m_cup_cap m n.
Proof.
  unfold n_m_cup_cap.
  now rewrite Nat.add_comm.
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

Lemma matrix_of_biperm_0_0 f : 
  matrix_of_biperm 0 0 f = I 1.
Proof.
  apply mat_equiv_eq; auto with wf_db.
  simpl.
  intros [] [] Hi Hj; (easy + lia).
Qed.

Lemma matrix_of_biperm_n_m_cup_cap_0_l ncap : 
  matrix_of_biperm 0 (ncap + ncap) (n_m_cup_cap 0 ncap) =
  (ncap ⨂ ⟦⊂⟧).
Proof.
  induction ncap; [simpl; now rewrite matrix_of_biperm_0_0|].
  rewrite n_m_cup_cap_comm.
  change 0 with (0 + 0) at 5.
  replace (S ncap + S ncap) with ((1 + 1) + (ncap + ncap)) by lia.
  replace (S ncap) with (1 + ncap) by lia.
  rewrite n_m_cup_cap_plus_plus_decomp.
  rewrite 2!(n_m_cup_cap_comm _ 0).
  pose proof (matrix_of_stack_biperms (0+0) (1+1) (0+0) (ncap + ncap)
    (n_m_cup_cap 0 1) (n_m_cup_cap 0 ncap)
    ltac:(auto with biperm_db)
    ltac:(auto with biperm_db)) as Hrw.
  change 0 with (0 + 0 + (0 + 0)) at 6.
  rewrite Hrw.
  clear Hrw.
  change (1 + ncap) with (S ncap).
  cbn [kron_n].
  f_equal;
  [rewrite <- Nat.pow_mul_r; f_equal; lia..|apply IHncap |].
  apply mat_equiv_eq; auto with wf_db.
  by_cell; reflexivity.
Qed.

Lemma matrix_of_biperm_n_m_cup_cap_0_r ncup : 
  matrix_of_biperm (ncup + ncup) 0 (n_m_cup_cap ncup 0) =
  (ncup ⨂ ⟦⊃⟧).
Proof.
  induction ncup; [simpl; now rewrite matrix_of_biperm_0_0|].
  rewrite n_m_cup_cap_comm.
  change 0 with (0 + 0) at 5.
  replace (S ncup + S ncup) with ((1 + 1) + (ncup + ncup)) by lia.
  replace (S ncup) with (1 + ncup) by lia.
  rewrite n_m_cup_cap_plus_plus_decomp.
  (* rewrite 2!(n_m_cup_cap_comm 0 _). *)
  pose proof (matrix_of_stack_biperms (1+1) (0+0) (ncup + ncup) (0+0)
    (n_m_cup_cap 0 1) (n_m_cup_cap 0 ncup)
    ltac:(auto with biperm_db)
    ltac:(auto with biperm_db)) as Hrw.
  change 0 with (0 + 0 + (0 + 0)) at 8.
  rewrite Hrw.
  clear Hrw.
  change (1 + ncup) with (S ncup).
  cbn [kron_n].
  f_equal;
  [rewrite <- Nat.pow_mul_r; f_equal; lia..|
    rewrite n_m_cup_cap_comm; apply IHncup |].
  apply mat_equiv_eq; auto with wf_db.
  by_cell; reflexivity.
Qed.

Lemma matrix_of_biperm_n_m_cup_cap_split ncup ncap : 
  matrix_of_biperm (ncup + ncup) (ncap + ncap) (n_m_cup_cap ncup ncap) =
  matrix_of_biperm 0 (ncap + ncap) (n_m_cup_cap 0 ncap) ×
  matrix_of_biperm (ncup + ncup) 0 (n_m_cup_cap ncup 0).
Proof.
  rewrite n_m_cup_cap_stack_biperms_decomp.
  pose proof (matrix_of_stack_biperms 0 (ncap + ncap) (ncup + ncup) 0
    (n_m_cup_cap 0 ncap) (n_m_cup_cap ncup 0) 
    ltac:(auto with biperm_db)
    ltac:(auto with biperm_db)) as Hrw.
  rewrite Nat.add_0_r, Nat.add_0_l in Hrw.
  rewrite Hrw.
  clear Hrw.
  rewrite kron_split_antidiag by auto with wf_db.
  change (2^0) with 1.
  now rewrite kron_1_l, kron_1_r by (change 1 with (2^0); auto with wf_db).
Qed.

Lemma matrix_of_biperm_n_m_cup_cap ncup ncap : 
  matrix_of_biperm (ncup + ncup) (ncap + ncap) (n_m_cup_cap ncup ncap) =
  @Mmult (2^(ncap + ncap)) (2^0) (2^(ncup + ncup)) 
    (ncap ⨂ ⟦⊂⟧) (ncup ⨂ ⟦⊃⟧).
Proof.
  rewrite matrix_of_biperm_n_m_cup_cap_split.
  now rewrite 
    matrix_of_biperm_n_m_cup_cap_0_l,
    matrix_of_biperm_n_m_cup_cap_0_r.
Qed.

Lemma matrix_of_biperm_eq_of_perm_eq {n m f g}
  (H : perm_eq (n + m) f g) : 
  matrix_of_biperm n m f = matrix_of_biperm n m g.
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold matrix_of_biperm.
  do 2 simplify_bools_lia_one_kernel.
  now rewrite (number_preserved_eq_of_eq_on _ _ _ _ H).
Qed.

Local Open Scope prg.

Lemma matrix_of_biperm_compose_perm_l_eq n m f g 
  (Hf : bipermutation (m + n) f)
  (Hg : permutation n g) : 
  matrix_of_biperm n m (biperm_compose_perm_r m n f g) = 
  matrix_of_biperm n m f × 
    perm_to_matrix n (reflect_perm n ∘ perm_inv' n g ∘ reflect_perm n).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  rewrite matrix_of_biperm_compose_perm_l by easy.
  Morphisms.f_equiv.
  apply perm_to_matrix_eq_of_perm_eq.
  apply perm_eq_compose_proper;
  cleanup_perm.
Qed.

Lemma matrix_of_biperm_compose_perm_r_eq n m f g 
  (Hf : bipermutation (m + n) f)
  (Hg : permutation m g) : 
  matrix_of_biperm n m (biperm_compose_perm_l m n f g) = 
  perm_to_matrix m (reflect_perm m ∘ g ∘ reflect_perm m) 
    × matrix_of_biperm n m f.
Proof.
  apply mat_equiv_eq; auto with wf_db.
  now apply matrix_of_biperm_compose_perm_r.
Qed.

Lemma matrix_of_biperm_Mmult_perm_r_eq n m f g 
  (Hf : bipermutation (m + n) f)
  (Hg : permutation n g) : 
  matrix_of_biperm n m f × perm_to_matrix n g = 
  matrix_of_biperm n m 
    (biperm_compose_perm_r m n f 
      (reflect_perm n ∘ perm_inv' n g ∘ reflect_perm n)).
Proof.
  rewrite matrix_of_biperm_compose_perm_l_eq by auto with perm_db.
  f_equal.
  rewrite !perm_inv'_compose by auto with perm_db.
  apply perm_to_matrix_eq_of_perm_eq.
  rewrite !compose_assoc.
  cleanup_perm.
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

Lemma n_m_cup_cap_absorb_reflect_perm_l n m :
  biperm_compose_perm_r (m + m) (n + n)
    (n_m_cup_cap m n) (reflect_perm (n + n))
  = n_m_cup_cap m n.
Proof.
  eq_by_WF_perm_eq (m + m + (n + n)).
  intros k Hk.
  (* rewrite n_m_cup_cap_eqb. *)
  (* simplify_bools_lia_one_kernel. *)
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
  (* rewrite 2!n_m_cup_cap_eqb. *)
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

Lemma biperm_NF_absorb_tensor_2_idn_perm_l lperm rperm nid ncup ncap f
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  (Hf : permutation ncup f) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data (lperm ∘ tensor_perms ncup 2 f idn)
      rperm nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  replace (tensor_perms ncup 2 f idn) with 
    (stack_perms (ncup + ncup) nid (tensor_perms ncup 2 f idn) idn) 
    by cleanup_perm.
  rewrite 2!matrix_of_realize_biperm_data by auto with perm_db.
  rewrite perm_to_matrix_compose by auto with perm_db.
  rewrite <- Mmult_assoc.
  f_equal.
  rewrite Mmult_assoc.
  f_equal.
  rewrite perm_to_matrix_of_stack_perms, 
    perm_to_matrix_idn by auto with perm_db.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_r by auto with wf_db.
  f_equal.
  rewrite matrix_of_biperm_Mmult_perm_r_eq by auto with biperm_db.
  rewrite <- 2!biperm_compose_perm_r_compose_eq by auto with biperm_db.
  rewrite n_m_cup_cap_comm.
  rewrite n_m_cup_cap_absorb_reflect_perm_l.
  assert (H2cup : ncup + ncup = ncup * 2) by lia. 
  rewrite H2cup.
  rewrite tensor_perms_inv' by auto with perm_db.
  rewrite <- H2cup.
  rewrite idn_inv'.
  rewrite n_m_cup_cap_absorb_tensor_2_idn_perm_l_eq by auto with perm_db.
  now rewrite n_m_cup_cap_absorb_reflect_perm_l.
Qed.

Lemma biperm_NF_absorb_tensor_2_idn_perm_l' lperm rperm nid ncup ncap f
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  (Hf : permutation ncup f) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data (lperm ∘ 
      stack_perms (ncup + ncup) nid (tensor_perms ncup 2 f idn) idn)
      rperm nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  rewrite stack_perms_WF_idn by cleanup_perm.
  now apply biperm_NF_absorb_tensor_2_idn_perm_l.
Qed.

Lemma biperm_NF_absorb_l_perm_r_perm_inv' lperm rperm nid ncup ncap f
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  (Hf : permutation nid f) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data 
      (lperm ∘ stack_perms (ncup + ncup) nid idn f)
      (stack_perms (ncap + ncap) nid idn (perm_inv' nid f) ∘ rperm) 
      nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  rewrite 2!matrix_of_realize_biperm_data by auto with perm_db.
  rewrite !perm_to_matrix_compose by auto with perm_db.
  rewrite <- Mmult_assoc.
  f_equal.
  rewrite !Mmult_assoc.
  f_equal.
  rewrite !perm_to_matrix_of_stack_perms, 
    !perm_to_matrix_idn by auto with perm_db.
  restore_dims.
  rewrite 2!kron_mixed_product, !Mmult_1_l, Mmult_1_r by auto with wf_db.
  f_equal.
  rewrite <- perm_to_matrix_transpose_eq' by auto.
  apply perm_mat_transpose_linv; auto with perm_db.
Qed.

Lemma biperm_NF_absorb_l_r_perm_invs lperm rperm nid ncup ncap f g
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  (Hf : permutation nid f) (Hg : permutation nid g) 
  (Hfg : perm_eq nid (f ∘ g) idn) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data 
      (lperm ∘ stack_perms (ncup + ncup) nid idn f)
      (stack_perms (ncap + ncap) nid idn g ∘ rperm) 
      nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  rewrite 2!matrix_of_realize_biperm_data by auto with perm_db.
  rewrite !perm_to_matrix_compose by auto with perm_db.
  rewrite <- Mmult_assoc.
  f_equal.
  rewrite !Mmult_assoc.
  f_equal.
  rewrite !perm_to_matrix_of_stack_perms, 
    !perm_to_matrix_idn by auto with perm_db.
  restore_dims.
  rewrite 2!kron_mixed_product, !Mmult_1_l, Mmult_1_r by auto with wf_db.
  f_equal.
  rewrite <- perm_to_matrix_compose, 
    (perm_to_matrix_eq_of_perm_eq _ _ _ Hfg) by auto with perm_db.
  apply perm_to_matrix_idn.
Qed.

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
    apply biperm_compose_perm_r_idn; auto with biperm_db.
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

(* #[export] Hint Extern 20 (permutation ?n (swap_perm ?a ?b ?n')) =>
  apply (fun H => proj1 (permutation_change_dims n' n H _));
  []
  solve [auto with zarith *)

(* #[export] Hint Extern 100 (permutation ?n ?f) => 
  is_ground n;
  lazymatch f with 
  | compose _ _ => 
    idtac "hit compose:";
    print_goal;
    apply permutation_compose
  | stack_perms ?k ?l => 
    replace n with (k + l) by lia;
    apply stack_perms_permutation
  | _ => 
    idtac "hit WF";
    print_goal; 
    eapply permutation_of_le_permutation_WF;
    print_goal;
    fail;
    solve [auto with perm_db WF_Perm_db zarith]
  end : perm_db. *)



Lemma biperm_NF_absorb_swap_0_1_perm_l lperm rperm nid ncup ncap f g
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  (Hf : permutation nid f) (Hg : permutation nid g) 
  (Hfg : perm_eq nid (f ∘ g) idn) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data (lperm ∘ 
      stack_perms (ncup + ncup) nid (swap_perm 0 1 (ncup + ncup)) idn)
      rperm nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  bdestruct (ncup =? 0);
  [now rewrite swap_perm_big_eq, stack_perms_idn_idn, compose_idn_r by lia|].
  assert (permutation (ncup + ncup) (swap_perm 0 1 (ncup + ncup))) 
    by (auto with perm_db zarith).
  rewrite 2!matrix_of_realize_biperm_data by auto with perm_db.
  rewrite !perm_to_matrix_compose by auto with perm_db.
  rewrite <- Mmult_assoc.
  f_equal.
  rewrite !Mmult_assoc.
  f_equal.
  rewrite !perm_to_matrix_of_stack_perms, 
    !perm_to_matrix_idn by auto with perm_db.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_l by auto with wf_db.
  f_equal.
  rewrite matrix_of_biperm_Mmult_perm_r_eq by auto with biperm_db.
  rewrite swap_perm_inv' by lia.
  rewrite swap_perm_conj_reflect_eq by lia.
  rewrite swap_perm_comm.
  replace (ncup + ncup - 1) with (S (ncup + ncup - 2)) by lia.
  now rewrite n_m_cup_cap_comm, n_m_cup_cap_absorb_perm_swap_even_S_l by
    (now rewrite Nat.even_sub, even_add_same by lia).
Qed.



Lemma biperm_NF_absorb_swap_even_S_perm_l lperm rperm nid ncup ncap a
  (Ha : Nat.even a = true)
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data (lperm ∘ 
      swap_perm a (S a) (ncup + ncup))
      rperm nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  assert (permutation (ncup + ncup) (swap_perm a (S a) (ncup + ncup)))
    by (apply swap_perm_even_S_even_permutation; easy + apply even_add_same).
  replace (swap_perm a (S a) (ncup + ncup)) with
    (stack_perms (ncup + ncup) nid (swap_perm a (S a) (ncup + ncup)) idn)
    by cleanup_perm.
  
  bdestruct (ncup + ncup <=? a);
  [now rewrite swap_perm_big_eq, stack_perms_idn_idn, compose_idn_r by lia|].
  pose proof (succ_even_lt_even a (ncup + ncup) 
    Ha (even_add_same _) ltac:(easy)).
  rewrite 2!matrix_of_realize_biperm_data by auto with perm_db.
  rewrite !perm_to_matrix_compose by auto with perm_db.
  rewrite <- Mmult_assoc.
  f_equal.
  rewrite !Mmult_assoc.
  f_equal.
  rewrite !perm_to_matrix_of_stack_perms, 
    !perm_to_matrix_idn by auto with perm_db.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_l by auto with wf_db.
  f_equal.
  rewrite matrix_of_biperm_Mmult_perm_r_eq by auto with biperm_db.
  
  rewrite swap_perm_inv' by lia.
  rewrite swap_perm_conj_reflect_eq by lia.
  rewrite swap_perm_comm.
  replace (ncup + ncup - S a) with (S (ncup + ncup - S (S a))) by lia.
  now rewrite n_m_cup_cap_comm, n_m_cup_cap_absorb_perm_swap_even_S_l by
    (now rewrite Nat.even_sub, even_add_same, Nat.even_succ_succ, Ha by lia).
Qed.

Lemma biperm_NF_absorb_swap_even_S_perm_l' lperm rperm nid ncup ncap a
  (Ha : Nat.even a = true)
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data (lperm ∘ 
      stack_perms (ncup + ncup) nid (swap_perm a (S a) (ncup + ncup)) idn)
      rperm nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  rewrite stack_perms_WF_idn by cleanup_perm.
  now apply biperm_NF_absorb_swap_even_S_perm_l.
Qed.





(* Computes normal form for the bipermutation given by composing to
  the bipermutation whose normal form is (lperm, nid, ncup, ncap, rperm)
  a cap (⊂) at position padl (so S padl < nid + ncup). There are 3 cases:
  - Both legs of the cap end up in the cups. 2 subcases:
    + If the legs end up at the same cup, we simply contract lperm along
      both legs and decrement ncup
    + If the legs up at different cups we permute lperm with swap_block_perm
      so that the legs end up at the first and second cup. Then, we 
      contract lperm along both legs and decrement ncup (note we don't 
      need to worry about swapping at the destination caps, though for 
      maximal 'visual' clarity we could swap so that the legs of the cap
      end up adjacent, i.e. at indices 1 and 2 / 2nd and 3rd from the top)
  - Both legs of the cap end up in the ids. In this case, we 'WLOG' swap 
    after lperm / before rperm symmetrically so that the legs end up at
    the first two ids, then contract lperm along both legs of the cap and
    increment ncap
  - One leg of the cap lands in the ids while one lands in the cups. In 
    this case, we permute with swap_block_perm to make one leg land at the
    last cup, then 'WLOG' swap after lperm / before rperm symmetrically 
    so that the other leg lands at the first id. Then, we simply contract
    lperm along both legs. (This ensures the other input to the target cup
    ends up at the first id, as is correct.)
*)





(* This implements that spec but without any contraction. 
  It preserves underlying permutation *)
(* Definition prep_compose_cap_NF_l_old (lperm rperm : nat -> nat) 
  (nid ncup ncap padl : nat) :=
  if (lperm padl <? ncup + ncup) && (lperm (S padl) <? ncup + ncup) then
    (* First case, both in cups *)
    if lperm padl / 2 =? lperm (S padl) / 2 then
      let cup := lperm padl / 2 in 
      (* First subcase, same cup *)
      let lperm_alt := lperm ∘ tensor_perms ncup 2 (swap_perm 0 cup ncup) idn in
      let lperm_alt_1 := 
        if lperm padl <? lperm (S padl) then lperm_alt 
        else lperm_alt ∘ swap_perm 0 1 (ncup + ncup) (* Ensure first goes to first *)
        in
      (* let lperm' := contract_perm (contract_perm lperm (S padl)) padl in *)
      Build_NF_biperm lperm_alt_1 rperm nid (ncup(*  - 1 *)) ncap
    else 
      (* Second subcase, different cups *)
      let cup1 := lperm padl / 2 in let cup2 := lperm (S padl) / 2 in
      let lperm_alt := 
        lperm ∘ tensor_perms ncup 2 (swap_perm 0 cup1 ncup) idn
          ∘ tensor_perms ncup 2 (swap_perm 1 cup2 ncup) idn in
      let lperm_alt_1 :=
        if Nat.even (lperm padl) then 
        lperm_alt ∘ swap_perm 0 1 (ncup + ncup)
        else lperm_alt
        in
      let lperm_alt_2 :=
        if Nat.even (lperm (S padl)) then 
        lperm_alt_1 ∘ swap_perm 2 3 (ncup + ncup)
        else lperm_alt_1
        in
      (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
      Build_NF_biperm lperm_alt_2 rperm nid (ncup(*  - 1 *)) ncap
  else if (lperm padl <? ncup + ncup) (* && (lperm (S padl) <? ncup + ncup) *) then
    (* Third case, first orientation (first leg in cup) *)
    let cup1 := lperm padl / 2 in let id2 := lperm (S padl) - (ncup + ncup) in
    let lperm_alt := 
      lperm ∘ stack_perms (ncup + ncup) nid 
        (tensor_perms ncup 2 (swap_perm cup1 (ncup - 1) ncup) idn)
        idn in
    let lperm_alt_1 := 
      if Nat.even (lperm padl) then lperm_alt else
      lperm_alt ∘ swap_perm (ncup + ncup - 2) (ncup + ncup - 1) (ncup + ncup)
      in
    let lperm_alt_1' :=
      lperm_alt_1 ∘ stack_perms (ncup + ncup) nid idn (swap_perm 0 id2 nid) in
    let rperm' := 
      stack_perms (ncap + ncap) nid idn (swap_perm 0 id2 nid) ∘ rperm in
    (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
    Build_NF_biperm lperm_alt_1' rperm' nid (ncup(*  - 1 *)) ncap
  else if (* (lperm padl <? ncup + ncup) && *) (lperm (S padl) <? ncup + ncup) then
    (* Third case, second orientation (second leg in cup) *)
    let id1 := lperm padl - (ncup + ncup) in let cup2 := lperm (S padl) / 2 in
    let lperm_alt := 
      lperm ∘ stack_perms (ncup + ncup) nid 
        (tensor_perms ncup 2 (swap_perm cup2 (ncup - 1) ncup) idn)
        idn in
    let lperm_alt_1 := 
      if Nat.even (lperm padl) then lperm_alt else
      lperm_alt ∘ swap_perm (ncup + ncup - 2) (ncup + ncup - 1) (ncup + ncup)
      in
    let lperm_alt_1' :=
      lperm_alt_1 ∘ stack_perms (ncup + ncup) nid idn (swap_perm 0 id1 nid) in
    let rperm' := 
      stack_perms (ncap + ncap) nid idn (swap_perm 0 id1 nid) ∘ rperm in
    (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
    Build_NF_biperm lperm_alt_1' rperm' nid (ncup(*  - 1 *)) ncap
  else (* if (lperm padl <? ncup + ncup) && (lperm (S padl) <? ncup + ncup) then *)
    (* Second case, both legs in ids *)
    let id1 := lperm padl - (ncup + ncup) in 
    let id2 := lperm (S padl) - (ncup + ncup) in
    let id2' := swap_perm 0 id1 nid id2 in
    let lperm_alt :=
      lperm ∘ stack_perms (ncup + ncup) nid idn
        (swap_perm 0 id1 nid ∘ swap_perm 1 id2' nid) in
    let rperm' := 
      stack_perms (ncap + ncap) nid idn 
        (swap_perm 1 id2' nid ∘ swap_perm 0 id1 nid) 
      ∘ rperm in
    (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
    Build_NF_biperm lperm_alt rperm' nid ncup (ncap(*  + 1 *)). *)



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

Definition prep_compose_cap_NF_l (lperm_init rperm : nat -> nat) 
  (nid ncup ncap padl : nat) :=
  let lperm := perm_inv (ncup + ncup + nid) lperm_init in
  if (lperm padl <? ncup + ncup) && (lperm (S padl) <? ncup + ncup) then
    (* First case, both in cups *)
    if lperm padl / 2 =? lperm (S padl) / 2 then
      let cup := lperm padl / 2 in 
      (* First subcase, same cup *)
      let lperm_alt := lperm_init ∘ tensor_perms ncup 2 (swap_perm 0 cup ncup) idn in
      let lperm_alt_1 := 
        if lperm padl <? lperm (S padl) then lperm_alt 
        else lperm_alt ∘ swap_perm 0 1 (ncup + ncup) (* Ensure first goes to first *)
        in
      (* let lperm' := contract_perm (contract_perm lperm (S padl)) padl in *)
      Build_NF_biperm lperm_alt_1 rperm nid (ncup(*  - 1 *)) ncap
    else 
      (* Second subcase, different cups *)
      let cup1 := lperm padl / 2 in let cup2 := lperm (S padl) / 2 in
      let lperm_alt := 
          lperm_init ∘ 
          tensor_perms ncup 2 (swap_2_to_2_perm 0 1 cup1 cup2 ncup) idn in
      let lperm_alt_1 :=
        if Nat.even (lperm padl) then 
        lperm_alt ∘ swap_perm 0 1 (ncup + ncup)
        else lperm_alt
        in
      let lperm_alt_2 :=
        if Nat.even (lperm (S padl)) then 
        lperm_alt_1
        else lperm_alt_1 ∘ swap_perm 2 3 (ncup + ncup)
        in
      (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
      Build_NF_biperm lperm_alt_2 rperm nid (ncup(*  - 1 *)) ncap
  else if (lperm padl <? ncup + ncup) (* && (lperm (S padl) <? ncup + ncup) *) then
    (* Third case, first orientation (first leg in cup) *)
    let cup1 := lperm padl / 2 in let id2 := lperm (S padl) - (ncup + ncup) in
    let lperm_alt := 
      lperm_init ∘ stack_perms (ncup + ncup) nid 
        (tensor_perms ncup 2 (swap_perm cup1 (ncup - 1) ncup) idn)
        idn in
    let lperm_alt_1 := 
      if Nat.even (lperm padl) then 
      lperm_alt ∘ swap_perm (ncup + ncup - 2) (ncup + ncup - 1) (ncup + ncup)  
      else lperm_alt in
    let lperm_alt_1' :=
      lperm_alt_1 ∘ stack_perms (ncup + ncup) nid idn (swap_perm 0 id2 nid) in
    let rperm' := 
      stack_perms (ncap + ncap) nid idn (swap_perm 0 id2 nid) ∘ rperm in
    (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
    Build_NF_biperm lperm_alt_1' rperm' nid (ncup(*  - 1 *)) ncap
  else if (* (lperm padl <? ncup + ncup) && *) (lperm (S padl) <? ncup + ncup) then
    (* Third case, second orientation (second leg in cup) *)
    let id1 := lperm padl - (ncup + ncup) in let cup2 := lperm (S padl) / 2 in
    let lperm_alt := 
      lperm_init ∘ stack_perms (ncup + ncup) nid 
        (tensor_perms ncup 2 (swap_perm cup2 (ncup - 1) ncup) idn)
        idn in
    let lperm_alt_1 := 
      if Nat.even (lperm (S padl)) then 
      lperm_alt ∘ swap_perm (ncup + ncup - 2) (ncup + ncup - 1) (ncup + ncup) 
      else lperm_alt
      in
    let lperm_alt_1' :=
      lperm_alt_1 ∘ stack_perms (ncup + ncup) nid idn (swap_perm 0 id1 nid) in
    let rperm' := 
      stack_perms (ncap + ncap) nid idn (swap_perm 0 id1 nid) ∘ rperm in
    (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
    Build_NF_biperm lperm_alt_1' rperm' nid (ncup(*  - 1 *)) ncap
  else (* if (lperm padl <? ncup + ncup) && (lperm (S padl) <? ncup + ncup) then *)
    (* Second case, both legs in ids *)
    let id1 := lperm padl - (ncup + ncup) in 
    let id2 := lperm (S padl) - (ncup + ncup) in
    let id2' := swap_perm 0 id1 nid id2 in
    let lperm_alt :=
      lperm_init ∘ stack_perms (ncup + ncup) nid idn
        (swap_2_to_2_perm 0 1 id1 id2 nid)
        (* (swap_perm 0 id1 nid ∘ swap_perm 1 id2' nid) *) in
    let rperm' := 
      stack_perms (ncap + ncap) nid idn 
        (perm_inv nid (swap_2_to_2_perm 0 1 id1 id2 nid))
        (* (swap_perm 1 id2' nid ∘ swap_perm 0 id1 nid)  *)
      ∘ rperm in
    (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
    Build_NF_biperm lperm_alt rperm' nid ncup (ncap(*  + 1 *)).





Lemma prep_compose_cap_NF_l_case_2 lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm padl)  
  (HSpadl :  ncup + ncup <= perm_inv (ncup + ncup + nid) lperm (S padl)) 
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup) = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup + 1) = S padl.
Proof.
  pose proof (perm_inv_bounded (ncup+ncup+nid) lperm) as Hlinvbdd.
  pose proof (Hlinvbdd (padl) ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  pattern (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup))
    false.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup))
    false.
  simpl.
  assert (perm_inv (ncup + ncup + nid) lperm padl <> 
    perm_inv (ncup + ncup + nid) lperm (S padl))
    by (intros Hfalse; 
    apply (ltac:(lia) : (padl <> S padl));
    apply (permutation_is_injective (ncup + ncup + nid)
    (perm_inv (ncup + ncup + nid) lperm)); auto with perm_db zarith).
  unfold Pred; clear Pred.
  unfold compose.
  rewrite 2!stack_perms_right by lia.
  rewrite Nat.sub_diag, add_sub'.
  rewrite swap_2_to_2_perm_first, swap_2_to_2_perm_second by lia.
  split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
Qed.

Lemma prep_compose_cap_NF_l_case_3_2 lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm padl)  
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup - 1) = S padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup) = padl.
Proof.
  pose proof (perm_inv_bounded (ncup+ncup+nid) lperm) as Hlinvbdd.
  pose proof (Hlinvbdd (padl) ltac:(lia)).
  pattern (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup))
    false.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup))
    true.
  simpl.
  rewrite !even_eqb.
  bdestructΩ'; unfold Pred; clear Pred.
  - unfold compose at 1 4.
    rewrite stack_perms_left, stack_perms_right by lia.
    rewrite Nat.sub_diag.
    rewrite swap_perm_left, Nat.sub_add by lia.
    unfold compose at 1 3.
    rewrite swap_perm_right, swap_perm_neither by lia.
    unfold compose, tensor_perms.
    rewrite stack_perms_left, stack_perms_right by lia.
    simplify_bools_lia_one_kernel.
    replace (ncup + ncup - 2) with ((ncup - 1)*2) by lia.
    rewrite Nat.div_mul, Nat.Div0.mod_mul by lia.
    rewrite swap_perm_right by lia.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose at 1 3.
    rewrite stack_perms_left, stack_perms_right by lia.
    rewrite Nat.sub_diag.
    rewrite swap_perm_left, Nat.sub_add by lia.
    unfold compose, tensor_perms.
    rewrite stack_perms_left, stack_perms_right by lia.
    simplify_bools_lia_one_kernel.
    replace (ncup + ncup - 1) with ((ncup - 1)*2 + 1) by lia.
    rewrite Nat.div_add_l, mod_add_l by lia.
    rewrite Nat.add_0_r.
    rewrite swap_perm_right by lia.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.mod_upper_bound 
      (perm_inv (ncup + ncup + nid) lperm (S padl)) 2 ltac:(lia)).
    change (1 mod 2) with 1.
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
Qed.


Lemma prep_compose_cap_NF_l_case_3_1 lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm (S padl))  
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup - 1) = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup) = S padl.
Proof.
  pose proof (perm_inv_bounded (ncup+ncup+nid) lperm) as Hlinvbdd.
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  pattern (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup))
    true.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup))
    false.
  simpl.
  rewrite !even_eqb.
  bdestructΩ'; unfold Pred; clear Pred.
  - unfold compose at 1 4.
    rewrite stack_perms_left, stack_perms_right by lia.
    rewrite Nat.sub_diag.
    rewrite swap_perm_left, Nat.sub_add by lia.
    unfold compose at 1 3.
    rewrite swap_perm_right, swap_perm_neither by lia.
    unfold compose, tensor_perms.
    rewrite stack_perms_left, stack_perms_right by lia.
    simplify_bools_lia_one_kernel.
    replace (ncup + ncup - 2) with ((ncup - 1)*2) by lia.
    rewrite Nat.div_mul, Nat.Div0.mod_mul by lia.
    rewrite swap_perm_right by lia.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose at 1 3.
    rewrite stack_perms_left, stack_perms_right by lia.
    rewrite Nat.sub_diag.
    rewrite swap_perm_left, Nat.sub_add by lia.
    unfold compose, tensor_perms.
    rewrite stack_perms_left, stack_perms_right by lia.
    simplify_bools_lia_one_kernel.
    replace (ncup + ncup - 1) with ((ncup - 1)*2 + 1) by lia.
    rewrite Nat.div_add_l, mod_add_l by lia.
    rewrite Nat.add_0_r.
    rewrite swap_perm_right by lia.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound 
      (perm_inv (ncup + ncup + nid) lperm (padl)) 2 ltac:(lia)).
    change (1 mod 2) with 1.
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
Qed.

Lemma prep_compose_cap_NF_l_case_1_2 lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hdiff : perm_inv (ncup + ncup + nid) lperm padl / 2 <> 
    perm_inv (ncup + ncup + nid) lperm (S padl) / 2) 
  (Hlperm : permutation (ncup + ncup + nid) lperm):
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 1 = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 2 = S padl.
Proof.
  pattern (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  replace ((perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup) 
    && (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup)) 
    with true by bdestructΩ'.
  simplify_bools_lia_one_kernel.
  pose proof (diff_divs_lower_bound 
    (perm_inv (ncup + ncup + nid) lperm padl)
    (perm_inv (ncup + ncup + nid) lperm (S padl))
    2 (ncup + ncup) ltac:(easy) ltac:(easy) ltac:(easy)).
  rewrite !even_eqb.
  bdestructΩ'; unfold Pred; clear Pred.
  - unfold compose at 1 3.
    rewrite swap_perm_right, swap_perm_neither by lia.
    unfold compose, tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (0 / 2) with 0.
    change (2 / 2) with 1.
    rewrite swap_2_to_2_perm_first, swap_2_to_2_perm_second by lia.
    change (2 mod 2) with 0.
    change (0 mod 2) with 0.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose, tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (1 / 2) with 0.
    change (2 / 2) with 1.
    rewrite swap_2_to_2_perm_first, swap_2_to_2_perm_second by lia.
    change (2 mod 2) with 0.
    change (1 mod 2) with 1.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose at 1 4.
    rewrite swap_perm_neither, swap_perm_left by lia.
    unfold compose at 1 3.
    rewrite swap_perm_right, swap_perm_neither by lia.
    unfold compose, tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (0 / 2) with 0.
    change (3 / 2) with 1.
    rewrite swap_2_to_2_perm_first, swap_2_to_2_perm_second by lia.
    change (3 mod 2) with 1.
    change (0 mod 2) with 0.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose at 1 3.
    rewrite swap_perm_neither, swap_perm_left by lia.
    unfold compose, tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (1 / 2) with 0.
    change (3 / 2) with 1.
    rewrite swap_2_to_2_perm_first, swap_2_to_2_perm_second by lia.
    change (3 mod 2) with 1.
    change (1 mod 2) with 1.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
Qed.

Lemma prep_compose_cap_NF_l_case_1_1 lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hsame : perm_inv (ncup + ncup + nid) lperm padl / 2 = 
    perm_inv (ncup + ncup + nid) lperm (S padl) / 2) 
  (Hlperm : permutation (ncup + ncup + nid) lperm):
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 0 = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 1 = S padl.
Proof.
  pattern (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  replace ((perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup) 
    && (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup)) 
    with true by bdestructΩ'.
  simplify_bools_lia_one_kernel.
  bdestructΩ'; unfold Pred; clear Pred.
  - unfold compose.
    unfold tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (0 / 2) with 0.
    change (1 / 2) with 0.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound (perm_inv 
      (ncup + ncup + nid) lperm (S padl)) 2 ltac:(lia)).
    assert (Hpadmod2 : perm_inv (ncup + ncup + nid) 
      lperm (padl) mod 2 = 0) by lia.
    assert (HSpadmod2 : perm_inv (ncup + ncup + nid) 
      lperm (S padl) mod 2 = 1) by lia.
    rewrite 2!Nat.mod_small by lia.
    unfold swap_perm.
    simplify_bools_lia_one_kernel.
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose at 1 3.
    unfold swap_perm at 2 4; simpl.
    do 2 simplify_bools_lia_one_kernel.
    unfold compose, tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (0 / 2) with 0.
    change (1 / 2) with 0.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    assert (perm_inv (ncup + ncup + nid) lperm padl <> 
      perm_inv (ncup + ncup + nid) lperm (S padl)) by
      (intros Hfalse; generalize (f_equal lperm Hfalse); 
      cleanup_perm; lia).
    pose proof (Nat.mod_upper_bound (perm_inv 
      (ncup + ncup + nid) lperm (padl)) 2 ltac:(lia)).
    assert (Hpadmod2 : perm_inv (ncup + ncup + nid) 
      lperm (padl) mod 2 = 1) by lia.
    assert (HSpadmod2 : perm_inv (ncup + ncup + nid) 
      lperm (S padl) mod 2 = 0) by lia.
    rewrite 2!Nat.mod_small by lia.
    unfold swap_perm.
    simplify_bools_lia_one_kernel.
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
Qed.

Lemma realize_biperm_data_WF lperm rperm nid ncup ncap :
  WF_Perm (ncup + ncup + nid + (ncap + ncap + nid))
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  unfold realize_biperm_data.
  rewrite Nat.add_comm.
  apply biperm_compose_perm_l_WF.
Qed.

#[export] Hint Resolve realize_biperm_data_WF : WF_Perm_db.

Lemma prep_compose_cap_NF_l_correct lperm rperm nid ncup ncap padl 
  (Hpadl : S padl < ncup + ncup + nid)
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  realize_NF_biperm 
    (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) =
  realize_biperm_data lperm rperm nid ncup ncap.
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).

  (* rewrite matrix_of_realize_biperm_data by auto. *)
  unfold prep_compose_cap_NF_l.
  pose proof (stack_perms_WF_idn (ncup + ncup) nid) as mkWF.
  rewrite <- (mkWF (tensor_perms ncup 2 (swap_perm 0 (perm_inv 
    (ncup + ncup + nid) lperm padl / 2) ncup) idn)) by cleanup_perm.
  rewrite <- (mkWF (tensor_perms ncup 2 (swap_2_to_2_perm 0 1
       (perm_inv (ncup + ncup + nid) lperm padl / 2)
       (perm_inv (ncup + ncup + nid) lperm (S padl) / 2) ncup) idn)) 
       by cleanup_perm.
  rewrite <- (mkWF (swap_perm 0 1 (ncup + ncup))) by cleanup_perm.
  rewrite <- (mkWF (swap_perm 2 3 (ncup + ncup))) by cleanup_perm.
  rewrite <- (mkWF (swap_perm (ncup + ncup - 2) (ncup + ncup - 1)
    (ncup + ncup))) by cleanup_perm.
  bdestruct (perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup);
    [assert (perm_inv (ncup + ncup + nid) lperm padl / 2 < ncup)   
    by (apply Nat.Div0.div_lt_upper_bound; lia)|];
  (bdestruct (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup); 
    [assert (perm_inv (ncup + ncup + nid) lperm (S padl) / 2 < ncup) 
    by (apply Nat.Div0.div_lt_upper_bound; lia)|]);
  cbn [andb];
  [bdestruct (perm_inv (ncup + ncup + nid) lperm padl / 2 
    =? perm_inv (ncup + ncup + nid) lperm (S padl) / 2)|..];
  rewrite realize_NF_biperm_constructor.
  - apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|].
    apply matrix_of_biperm_inj; 
      [apply realize_biperm_data_bipermutation; auto 6 with perm_db zarith;
      bdestruct_one; auto 6 with perm_db zarith..|].
    bdestruct (perm_inv (ncup + ncup + nid) lperm padl <? 
      perm_inv (ncup + ncup + nid) lperm (S padl)).
    + now rewrite biperm_NF_absorb_tensor_2_idn_perm_l' by 
        auto with perm_db zarith.
    + rewrite biperm_NF_absorb_swap_even_S_perm_l'
        by (auto with perm_db zarith).
      now rewrite biperm_NF_absorb_tensor_2_idn_perm_l' by 
        auto with perm_db zarith.
  - apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
      [auto with WF_Perm_db..|].
    apply matrix_of_biperm_inj;
    [apply realize_biperm_data_bipermutation; 
      bdestructΩ'; auto 10 with perm_db zarith..|].
    destruct 
      (Nat.even (perm_inv (ncup + ncup + nid) lperm (S padl))) eqn:HSpadle, 
      (Nat.even (perm_inv (ncup + ncup + nid) lperm padl)) eqn:Hpadle;
    rewrite 2?biperm_NF_absorb_swap_even_S_perm_l'
        by (auto 10 with perm_db zarith);
    now rewrite 2?biperm_NF_absorb_tensor_2_idn_perm_l'
        by (auto with perm_db zarith).
  - replace (ncup + ncup - 1) with (S (ncup + ncup - 2)) by lia.
    apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|]. 
    apply matrix_of_biperm_inj;
      [apply realize_biperm_data_bipermutation; auto 10 with perm_db zarith..|];
      [bdestructΩ'; auto 10 with perm_db zarith|..]. 
    destruct (Nat.even (perm_inv (ncup + ncup + nid) lperm padl)) eqn:Hpadle;
    rewrite biperm_NF_absorb_l_r_perm_invs
      by (auto 10 with perm_db zarith; cleanup_perm);
    [rewrite biperm_NF_absorb_swap_even_S_perm_l'
      by ((now rewrite Nat.even_sub, even_add_same by lia) 
        + auto 10 with perm_db zarith)|];
    now rewrite 2?biperm_NF_absorb_tensor_2_idn_perm_l'
        by (auto with perm_db zarith).
  - replace (ncup + ncup - 1) with (S (ncup + ncup - 2)) by lia.
    (* rewrite <- (stack_perms_WF_idn _ nid (swap_perm (ncup + ncup - 2) 
      (S (ncup + ncup - 2)) (ncup + ncup))) by cleanup_perm. *)
    apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|]. 
    apply matrix_of_biperm_inj;
      [apply realize_biperm_data_bipermutation; auto 10 with perm_db zarith..|];
      [bdestructΩ'; auto 10 with perm_db zarith|..].
    destruct (Nat.even (perm_inv (ncup + ncup + nid) lperm (S padl))) eqn:Hpadle;
    rewrite biperm_NF_absorb_l_r_perm_invs
      by (auto 10 with perm_db zarith; cleanup_perm);
    [rewrite biperm_NF_absorb_swap_even_S_perm_l'
        by ((now rewrite Nat.even_sub, even_add_same by lia) 
          + auto 10 with perm_db zarith)|];
    now rewrite 2?biperm_NF_absorb_tensor_2_idn_perm_l'
        by (auto with perm_db zarith).
  - apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|]. 
    apply matrix_of_biperm_inj;
      [apply realize_biperm_data_bipermutation; auto 10 with perm_db zarith..|].
    rewrite biperm_NF_absorb_l_r_perm_invs;
    [easy|auto with perm_db zarith..].
    apply perm_inv_rinv_of_permutation.
    auto with perm_db zarith.
Qed.



(* Lemma prep_compose_cap_NF_l_correct_old lperm rperm nid ncup ncap padl 
  (Hpadl : S padl < ncup + ncup + nid)
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  realize_NF_biperm 
    (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) =
  realize_biperm_data lperm rperm nid ncup ncap.
Proof.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).

  (* rewrite matrix_of_realize_biperm_data by auto. *)
  unfold prep_compose_cap_NF_l.
  replace (tensor_perms ncup 2 (swap_perm 0 (lperm padl / 2) ncup) idn) with 
      (stack_perms (ncup + ncup) nid (tensor_perms ncup 2 
      (swap_perm 0 (lperm padl / 2) ncup) idn) idn) 
      by cleanup_perm.
  replace (tensor_perms ncup 2 (swap_perm 1 (lperm (S padl) / 2) ncup) idn) with 
    (stack_perms (ncup + ncup) nid (tensor_perms ncup 2 
    (swap_perm 1 (lperm (S padl) / 2) ncup) idn) idn) 
    by cleanup_perm.
  replace (swap_perm 0 1 (ncup + ncup)) with 
    (stack_perms (ncup + ncup) nid (swap_perm 0 1 (ncup + ncup)) idn) 
    by cleanup_perm.
  replace (swap_perm 2 3 (ncup + ncup)) with 
    (stack_perms (ncup + ncup) nid (swap_perm 2 3 (ncup + ncup)) idn) 
    by cleanup_perm.
  
  bdestruct (lperm padl <? ncup + ncup);
    [assert (lperm padl / 2 < ncup)   
    by (apply Nat.Div0.div_lt_upper_bound; lia)|];
  (bdestruct (lperm (S padl) <? ncup + ncup); 
    [assert (lperm (S padl) / 2 < ncup) 
    by (apply Nat.Div0.div_lt_upper_bound; lia)|]);
  cbn [andb];
  [bdestruct (lperm padl / 2 =? lperm (S padl) / 2)|..];
  rewrite realize_NF_biperm_constructor.
  - apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|].
    apply matrix_of_biperm_inj; 
      [apply realize_biperm_data_bipermutation; auto 6 with perm_db zarith;
      bdestruct_one; auto 6 with perm_db zarith..|].
    bdestruct (lperm padl <? lperm (S padl)).
    + now rewrite biperm_NF_absorb_tensor_2_idn_perm_l' by 
        auto with perm_db zarith.
    + rewrite biperm_NF_absorb_swap_even_S_perm_l'
        by (auto with perm_db zarith).
      now rewrite biperm_NF_absorb_tensor_2_idn_perm_l' by 
        auto with perm_db zarith.
  - apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
      [auto with WF_Perm_db..|].
    apply matrix_of_biperm_inj;
    [apply realize_biperm_data_bipermutation; 
      bdestructΩ'; auto 10 with perm_db zarith..|].
    destruct (Nat.even (lperm (S padl))) eqn:HSpadle, 
      (Nat.even (lperm padl)) eqn:Hpadle;
    rewrite 2?biperm_NF_absorb_swap_even_S_perm_l'
        by (auto 10 with perm_db zarith);
    now rewrite 2?biperm_NF_absorb_tensor_2_idn_perm_l'
        by (auto with perm_db zarith).
  - replace (ncup + ncup - 1) with (S (ncup + ncup - 2)) by lia.
    rewrite <- (stack_perms_WF_idn _ nid (swap_perm (ncup + ncup - 2) 
      (S (ncup + ncup - 2)) (ncup + ncup))) by cleanup_perm.
    apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|]. 
    apply matrix_of_biperm_inj;
      [apply realize_biperm_data_bipermutation; auto 10 with perm_db zarith..|];
      [bdestructΩ'; auto 10 with perm_db zarith|..]. 
    destruct (Nat.even (lperm padl)) eqn:Hpadle;
    rewrite biperm_NF_absorb_l_r_perm_invs
      by (auto 10 with perm_db zarith; cleanup_perm);
    [|rewrite biperm_NF_absorb_swap_even_S_perm_l'
        by ((now rewrite Nat.even_sub, even_add_same by lia) 
          + auto 10 with perm_db zarith)];
    now rewrite 2?biperm_NF_absorb_tensor_2_idn_perm_l'
        by (auto with perm_db zarith).
  - replace (ncup + ncup - 1) with (S (ncup + ncup - 2)) by lia.
    rewrite <- (stack_perms_WF_idn _ nid (swap_perm (ncup + ncup - 2) 
      (S (ncup + ncup - 2)) (ncup + ncup))) by cleanup_perm.
    apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|]. 
    apply matrix_of_biperm_inj;
      [apply realize_biperm_data_bipermutation; auto 10 with perm_db zarith..|];
      [bdestructΩ'; auto 10 with perm_db zarith|..]. 
    destruct (Nat.even (lperm padl)) eqn:Hpadle;
    rewrite biperm_NF_absorb_l_r_perm_invs
      by (auto 10 with perm_db zarith; cleanup_perm);
    [|rewrite biperm_NF_absorb_swap_even_S_perm_l'
        by ((now rewrite Nat.even_sub, even_add_same by lia) 
          + auto 10 with perm_db zarith)];
    now rewrite 2?biperm_NF_absorb_tensor_2_idn_perm_l'
        by (auto with perm_db zarith).
  - apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|]. 
    apply matrix_of_biperm_inj;
      [apply realize_biperm_data_bipermutation; auto 10 with perm_db zarith..|].
    rewrite biperm_NF_absorb_l_r_perm_invs;
    [easy|auto with perm_db zarith..].
    rewrite compose_assoc, <- (compose_assoc (swap_perm 0 _ _)).
    cleanup_perm.
Qed. *)

Lemma perm_to_matrix_cap_straight_pullthrough_r {n f} (Hf : permutation n f) 
  padl (Hpadl : S padl < n) (Hfpadl : f padl = padl) 
  (HfSpadl : f (S padl) = S padl) :
  @Mmult (2^n) (2^n) (2^(n-2)) (perm_to_matrix n f)
  ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl)))) =
  @Mmult (2^n) (2^(n-2)) (2^(n-2))
  ((I (2^ padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm f (S padl)) padl)).
Proof.
  pose proof (permutation_is_bounded _ _ Hf) as Hfbdd.
  pose proof (Hfbdd padl ltac:(lia)).
  pose proof (Hfbdd (S padl) Hpadl).
  apply mat_equiv_eq; auto with wf_db.
  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite <- Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits_l by easy.
  rewrite 3!Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits by
    (replace (n-2) with ((n - 1) - 1) by lia;
      apply contract_perm_bounded; try lia;
      auto with perm_db).
  replace (f_to_vec n) with
    (f_to_vec (padl + 2 + (n - (2 + padl)))) by (f_equal; lia).
  replace (f_to_vec (n-2)) with 
    (f_to_vec (padl + 0 + (n - (2 + padl)))) by (f_equal; lia).
  rewrite !f_to_vec_split'_eq.
  rewrite !(fun x y => kron_transpose' _ _ x y).

  rewrite !(fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z) by
    (now rewrite <- ?Nat.pow_add_r; lia + (f_equal; lia)).
  unfold kron.
  rewrite !Nat.mod_1_r, !Nat.Div0.div_0_l.
  rewrite Cmult_comm.
  symmetry.
  rewrite Cmult_comm, !Cmult_assoc.
  f_equal.
  - rewrite !basis_f_to_vec, <- !Mmult_assoc.
    rewrite !matrix_conj_basis_eq_lt by apply funbool_to_nat_bound.
    unfold I.
    do 4 match goal with
    |- context [funbool_to_nat ?k ?f <? 2 ^ ?k] => 
      replace (funbool_to_nat k f <? 2 ^ k) with true by
      (pose proof (funbool_to_nat_bound k f); bdestructΩ')
    end.
    rewrite 2!Cmult_if_if_1_l, 4!andb_true_r.
    apply f_equal_if; [|easy..].
    apply eq_iff_eq_true.
    rewrite 2!andb_true_iff, !Nat.eqb_eq, <- !funbool_to_nat_eq_iff.
    split.
    + intros [Hhigh Hlow].
      split.
      * intros k Hk.
        bdestruct (perm_inv n f (padl + 2 + k) <? padl).
        --generalize (Hlow (perm_inv n f (padl + 2 + k)) ltac:(easy)).
          intros ->.
          f_equal.
          unfold contract_perm.
          do 2 simplify_bools_lia_one_kernel.
          rewrite perm_inv_is_rinv_of_permutation, Hfpadl, HfSpadl 
            by easy + lia.
          bdestructΩ'.
        --assert (perm_inv n f (padl + 2 + k) <> padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          assert (perm_inv n f (padl + 2 + k) <> S padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          pose proof (perm_inv_bounded n f (padl + 2 + k)).
          generalize (Hhigh (perm_inv n f (padl + 2 + k) - (padl + 2)) 
            ltac:(lia)).
          rewrite Nat.add_sub_assoc, add_sub' by lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 4 simplify_bools_lia_one_kernel.
          replace (padl + 0 + (perm_inv n f (padl + 2 + k) 
            - (padl + 2)) + 1 + 1) with
            (perm_inv n f (padl + 2 + k)) by lia.
          rewrite perm_inv_is_rinv_of_permutation by easy + lia.
          bdestructΩ'.
      * intros k Hk.
        bdestruct (perm_inv n f k <? padl).
        --generalize (Hlow (perm_inv n f k) ltac:(easy)).
          intros ->.
          f_equal.
          unfold contract_perm.
          do 2 simplify_bools_lia_one_kernel.
          rewrite perm_inv_is_rinv_of_permutation, Hfpadl, HfSpadl 
            by easy + lia.
          bdestructΩ'.
        --assert (perm_inv n f k <> padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          assert (perm_inv n f k <> S padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          pose proof (perm_inv_bounded n f k).
          generalize (Hhigh (perm_inv n f k - (padl + 2)) 
            ltac:(lia)).
          rewrite Nat.add_sub_assoc, add_sub' by lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 4 simplify_bools_lia_one_kernel.
          replace (padl + 0 + (perm_inv n f k
            - (padl + 2)) + 1 + 1) with
            (perm_inv n f k) by lia.
          rewrite perm_inv_is_rinv_of_permutation by easy + lia.
          bdestructΩ'.
    + intros [Hhigh Hlow].
      split.
      * intros k Hk.
        bdestruct (f (padl + 2 + k) <? padl).
        --generalize (Hlow (f (padl + 2 + k)) ltac:(easy)).
          rewrite perm_inv_is_linv_of_permutation by easy + lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 4 simplify_bools_lia_one_kernel.
          replace (padl+0+k+1+1) with (padl+2+k) by lia.
          bdestructΩ'.
        --assert (f (padl + 2 + k) <> padl) by 
            (pose proof (permutation_is_injective n f Hf 
              padl (padl + 2 + k)); lia).
          assert (f (padl + 2 + k) <> S padl) by 
            (pose proof (permutation_is_injective n f Hf 
              (S padl) (padl + 2 + k)); lia).
          pose proof (Hfbdd (padl + 2 + k) ltac:(lia)).
          generalize (Hhigh (f (padl + 2 + k) - (padl + 2)) ltac:(lia)).
          rewrite Nat.add_sub_assoc, add_sub' by lia.
          rewrite perm_inv_is_linv_of_permutation by easy + lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 4 simplify_bools_lia_one_kernel.
          replace (padl + 0 + k + 1 + 1) with (padl + 2 + k) by lia.
          bdestructΩ'.
      * intros k HK.
        bdestruct (f k <? padl).
        --generalize (Hlow (f k) ltac:(easy)).
          rewrite perm_inv_is_linv_of_permutation by easy + lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 5 simplify_bools_lia_one_kernel.
          bdestructΩ'.
        --assert (f k <> padl) by 
            (pose proof (permutation_is_injective n f Hf padl k); lia).
          assert (f k <> S padl) by 
            (pose proof (permutation_is_injective n f Hf (S padl) k); lia).
          pose proof (Hfbdd k ltac:(lia)).
          generalize (Hhigh (f k - (padl + 2)) ltac:(lia)).
          rewrite Nat.add_sub_assoc, add_sub' by lia.
          rewrite perm_inv_is_linv_of_permutation by easy + lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 5 simplify_bools_lia_one_kernel.
          bdestructΩ'.
  - set (s := ⟦⊂⟧).
    unfold Mmult;
    simpl.
    replace (padl + 0) with (f padl) by lia. 
    replace (padl + 1) with (f (S padl)) by lia. 
    rewrite 2!perm_inv_is_linv_of_permutation by easy + lia.
    now rewrite Hfpadl, HfSpadl.
Qed.

Local Open Scope prg.







Lemma perm_to_matrix_cap_pullthrough_r {n f} (Hf : permutation n f) 
  padl (Hpadl : S padl < n) (HfSpadl : f (S padl) = S (f padl)) :
  @Mmult (2^n) (2^n) (2^(n-2)) (perm_to_matrix n f)
  ((I (2^ f padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + f padl)))) =
  @Mmult (2^n) (2^(n-2)) (2^(n-2))
  ((I (2^ padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm f (S padl)) padl)).
Proof.
  pose proof (permutation_is_bounded _ _ Hf) as Hfbdd.
  pose proof (Hfbdd padl ltac:(lia)).
  pose proof (Hfbdd (S padl) Hpadl).
  pose proof (perm_inv_bounded n f) as Hfinvbdd.
  
  pose proof (Hfinvbdd padl ltac:(lia)).
  pose proof (Hfinvbdd (S padl) Hpadl).
  
  replace (perm_to_matrix n f) with 
   (perm_to_matrix n (
    stack_perms (2 + f padl) (n - (2 + f padl))
      (rotr (2 + f padl) (f padl)) idn ∘
    stack_perms (2 + f padl) (n - (2 + f padl))
      (rotl (2 + f padl) (f padl)) idn
    ∘ f ∘
    stack_perms (2 + padl) (n - (2 + padl))
      (rotr (2 + padl) padl) idn ∘
    stack_perms (2 + padl) (n - (2 + padl))
      (rotl (2 + padl) padl) idn)) by
    (f_equal; cleanup_perm; rewrite compose_assoc; cleanup_perm).
  pose proof (fun g => proj1 (permutation_change_dims 
    (2 + f padl + (n - (2 + f padl))) n ltac:(lia) g)) as Hch1.
  pose proof (fun g => proj1 (permutation_change_dims 
    (2 + padl + (n - (2 + padl))) n ltac:(lia) g)) as Hch2.
  rewrite perm_to_matrix_compose by 
    (do 3 (try (apply compose_perm_bounded; [|auto with perm_db]));
    auto with perm_db).
  replace (perm_to_matrix n) with 
    (perm_to_matrix (2 + padl + (n - (2 + padl))))
     by (f_equal; lia).
  rewrite perm_to_matrix_of_stack_perms by auto with perm_db.
  rewrite <- rotr_inv', <- perm_to_matrix_transpose_eq'
    by auto with perm_db.
  rewrite Nat.add_comm.
  rewrite perm_to_matrix_rotr_eq_kron_comm.
  restore_dims.
  replace (@transpose (2 ^ (padl + 2)) (2 ^ (padl + 2)))
  with (@transpose (2^2 * 2 ^ (padl)) (2^(padl) * 2^2))
    by (f_equal; show_pow2_le).
  rewrite kron_comm_transpose, perm_to_matrix_idn.
  rewrite !compose_assoc.
  rewrite (Nat.add_comm (padl) 2).
  replace (perm_to_matrix (2 + padl + (n - (2 + padl)))) with
    (perm_to_matrix n (* (2 + f padl + (n - (2 + f padl))) *))
    by (f_equal; lia).
    
  rewrite perm_to_matrix_compose by auto with perm_db.
  replace (perm_to_matrix n) with
    (perm_to_matrix (2 + f padl + (n - (2 + f padl))))
    by (f_equal; lia).
  rewrite perm_to_matrix_of_stack_perms by auto with perm_db.
  rewrite (Nat.add_comm 2 (f padl)).
  rewrite perm_to_matrix_rotr_eq_kron_comm, 
    perm_to_matrix_idn.
  rewrite !Mmult_assoc.
  restore_dims.
  rewrite Mmult_assoc.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite Mmult_1_r, kron_comm_commutes_l by auto with wf_db.
  rewrite kron_comm_1_l.
  restore_dims.
  rewrite Mmult_1_r by auto with wf_db.
  rewrite (Nat.add_comm (f padl) 2).
  replace (perm_to_matrix (2 + padl + (n - (2 + padl)))) with
    (perm_to_matrix n) by (f_equal; lia).
  assert (Hpeq : perm_eq 2 
    ((stack_perms (2 + f padl) (n - (2 + f padl))
    (rotl (2 + f padl) (f padl)) idn ∘ (f
     ∘ stack_perms (2 + padl) (n - (2 + padl))
         (rotr (2 + padl) padl) idn))) idn).
  1:{
    rewrite <- compose_assoc.
    intros k Hk.
    rewrite rotr_add_r_eq.
      unfold compose at 1.
      rewrite stack_perms_left by lia.
      rewrite rotl_eq_rotr_sub, Nat.mod_small, Nat.add_sub by lia.
      unfold compose at 1.
      replace_bool_lia (2 + padl <=? k) false.
      replace_bool_lia (k <? 2) true.
      rewrite stack_perms_left by (destruct k as [|[]]; simpl; lia).
      rewrite rotr_add_l_eq.
      destruct k; [|replace k with 0 by lia];
      simpl Nat.add; bdestructΩ'.
  }
  pose proof ((fun G => perm_eq_of_small_eq_idn 2 n 
    _ ltac:(lia) G Hpeq) ltac:(auto with perm_db)) as Hrw.
  replace (perm_to_matrix (2 + f padl + (n - (2 + f padl))))
    with (perm_to_matrix n) by (f_equal; lia).
  rewrite (perm_to_matrix_eq_of_perm_eq _ _ _ Hrw).
  replace (perm_to_matrix n) 
    with (perm_to_matrix (2 + (n - 2))) by (f_equal; lia).
  rewrite perm_to_matrix_of_stack_perms; [|auto with perm_db|
  apply perm_shift_permutation_of_small_eq_idn; auto with perm_db zarith].
  rewrite kron_assoc, id_kron, 
    <- (Nat.pow_add_r 2 (f padl)) by auto with wf_db.
  replace (f padl + (n - (2 + f padl))) with (n - 2) by lia.
  rewrite perm_to_matrix_idn.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite <- Mmult_1_comm, Mmult_1_comm by auto with wf_db.
  rewrite <- kron_mixed_product.
  replace (I (2 ^ (n - 2))) with (I (2 ^ (padl + (n - (2 + padl)))))
    by (do 2 f_equal; lia).
  rewrite (Nat.pow_add_r 2 (padl)), <- id_kron.
  restore_dims.
  rewrite <- kron_assoc by auto with wf_db.
  restore_dims.
  rewrite <- Mmult_assoc.
  rewrite kron_mixed_product.
  rewrite kron_comm_commutes_l, kron_comm_1_r by auto with wf_db.
  restore_dims.
  rewrite 2!Mmult_1_r by auto with wf_db.
  rewrite kron_1_l by auto with wf_db.
  restore_dims.
  f_equal.
  apply perm_to_matrix_eq_of_perm_eq.
  intros k Hk.
  rewrite <- compose_assoc.
  rewrite rotl_eq_rotr_sub, Nat.mod_small, Nat.add_sub by lia.
  unfold compose at 1.
  unfold contract_perm at 1.
  replace (contract_perm f (S padl) padl) with (f padl) 
    by (unfold contract_perm; bdestructΩ').
  Local Arguments Nat.add : simpl never.
  bdestruct (k <? padl).
  - rewrite stack_perms_left by lia.
    rewrite rotr_add_r_eq.
    do 2 simplify_bools_lia_one_kernel.
    rewrite Nat.add_sub.
    assert (f k <> f padl) by (intros Heq; 
      apply (permutation_is_injective n f Hf) in Heq; lia).
    assert (f k <> f (S padl) ) by (intros Heq; 
      apply (permutation_is_injective n f Hf) in Heq; lia).
    unfold compose.
    bdestruct (f k <? f padl).
    + rewrite stack_perms_left by lia.
      rewrite rotr_add_l_eq.
      do 2 simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub.
      unfold contract_perm.
      bdestructΩ'.
    + pose proof (Hfbdd k ltac:(lia)).
      rewrite stack_perms_right by lia.
      unfold contract_perm; bdestructΩ'.
  - rewrite stack_perms_right by lia.
    rewrite Nat.sub_add by lia.
    unfold compose.
    assert (f (k + 2) <> f padl) by (intros Heq; 
      apply (permutation_is_injective n f Hf) in Heq; lia).
    assert (f (k + 2) <> f (S padl) ) by (intros Heq; 
      apply (permutation_is_injective n f Hf) in Heq; lia).
    bdestruct (f (k + 2) <? f padl).
    + rewrite stack_perms_left by lia.
      rewrite rotr_add_l_eq.
      do 2 simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub.
      unfold contract_perm at 1.
      simplify_bools_lia_one_kernel.
      unfold contract_perm.
      replace (k + 1 + 1) with (k + 2) by lia.
      bdestructΩ'.
    + pose proof (Hfbdd (k + 2) ltac:(lia)).
      rewrite stack_perms_right by lia.
      rewrite Nat.sub_add by lia.
      unfold contract_perm.
      replace (k + 1 + 1) with (k + 2) by lia.
      bdestructΩ'.
Qed.

Local Arguments Nat.add : simpl nomatch.

Lemma perm_to_matrix_cap_pullthrough_r_gen {n f} (Hf : permutation n f) 
  padl (Hpadl : S padl < n)
  (HfSpadl : perm_inv n f (S padl) = S (perm_inv n f padl)) :
  @Mmult (2^n) (2^n) (2^(n-2)) (perm_to_matrix n f)
  ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl)))) =
  @Mmult (2^n) (2^(n-2)) (2^(n-2))
  ((I (2^ perm_inv n  f padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + perm_inv n f padl))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm 
    f (S (perm_inv n f padl))) (perm_inv n f padl))).
Proof.
  pose proof (permutation_is_bounded n f Hf) as Hfbdd. 
  pose proof (Hfbdd padl ltac:(lia)).
  pose proof (perm_inv_bounded n f) as Hfinvbdd.
  replace ((2 ^ padl)) with ((2 ^ (f (perm_inv n f padl)))) by cleanup_perm.
  replace ((2 ^ (n - (2 + padl)))) with 
    ((2 ^ (n - (2 + f (perm_inv n f padl))))) by cleanup_perm.
  
  apply perm_to_matrix_cap_pullthrough_r; [auto |..].
  - pose proof (Hfinvbdd (S padl) Hpadl). 
    lia.
  - rewrite <- HfSpadl.
    cleanup_perm.
Qed.

Lemma perm_to_matrix_cap_pullthrough_r_gen_alt {n f} (Hf : permutation n f) 
  padl padl_in (Hpadl : S padl < n) (Hpadl_in : S padl_in < n)
  (Hfpadl : f padl_in = padl)
  (HfSpadl : f (S padl_in) = S padl) :
  @Mmult (2^n) (2^n) (2^(n-2)) (perm_to_matrix n f)
  ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl)))) =
  @Mmult (2^n) (2^(n-2)) (2^(n-2))
  ((I (2^ padl_in) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl_in))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm 
    f (S padl_in)) padl_in)).
Proof.
  replace (S padl_in) with (perm_inv n f (S padl)) by
    (rewrite perm_inv_eq_iff; cleanup_perm).
  replace padl_in with (perm_inv n f padl) by
    (rewrite perm_inv_eq_iff; cleanup_perm).
  assert (Hkey : perm_inv n f (S padl) = S (perm_inv n f padl)). 
  1: {
    rewrite <- HfSpadl.
    cleanup_perm.
    f_equal.
    symmetry.
    rewrite perm_inv_eq_iff; cleanup_perm.
  }
  rewrite perm_to_matrix_cap_pullthrough_r_gen; [|easy..].
  f_equal.
  now rewrite Hkey.
Qed.




Lemma perm_to_matrix_cap_pullthrough_r_gen_alt_swapped 
  {n f} (Hf : permutation n f) 
  padl padl_in (Hpadl : S padl < n) (Hpadl_in : S padl_in < n)
  (Hfpadl : f padl_in = S padl)
  (HfSpadl : f (S padl_in) = padl) :
  @Mmult (2^n) (2^n) (2^(n-2)) (perm_to_matrix n f)
  ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl)))) =
  @Mmult (2^n) (2^(n-2)) (2^(n-2))
  ((I (2^ padl_in) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl_in))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm 
    f (S padl_in)) padl_in)).
Proof.
  replace (perm_to_matrix n f) with 
    (perm_to_matrix n 
      (swap_perm padl (S padl) n ∘ swap_perm padl (S padl) n ∘ f))
    by (f_equal; cleanup_perm).
  rewrite compose_assoc.
  rewrite perm_to_matrix_compose by auto with perm_db.
  restore_dims.
  rewrite perm_to_matrix_swap_perm_S by easy.
  rewrite Mmult_assoc.
  change (2*2) with (2^2).
  rewrite (fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z) by
    (rewrite <- ?Nat.pow_add_r; f_equal; lia).
  rewrite kron_mixed_product.
  rewrite 2!Mmult_1_l by auto with wf_db.
  change (2^2) with (2*2).
  rewrite swap_cup.
  pose proof ((fun H => @perm_to_matrix_cap_pullthrough_r_gen_alt n
    (swap_perm padl (S padl) n ∘ f) H padl padl_in)
    ltac:(auto with perm_db)
    ltac:(lia) ltac:(lia)
    ltac:(unfold compose; rewrite Hfpadl, swap_perm_right; lia)
    ltac:(unfold compose; rewrite HfSpadl, swap_perm_left; lia)) as e.
  restore_dims in e.
  restore_dims.
  rewrite e.
  f_equal.
  apply perm_to_matrix_eq_of_perm_eq.
  intros k Hk.
  unfold contract_perm at 1 3.
  assert (HcSp : contract_perm (swap_perm padl (S padl) n ∘ f) 
    (S padl_in) padl_in = padl) by
    (unfold contract_perm, compose;
    rewrite Hfpadl, HfSpadl, swap_perm_left, swap_perm_right by lia;
    bdestructΩ').
  assert (Hcp : contract_perm (f) (S padl_in) padl_in = padl) by
    (unfold contract_perm; 
    rewrite Hfpadl, HfSpadl;
    bdestructΩ').
  rewrite HcSp, Hcp.
  bdestruct (k <? padl_in).
  - unfold contract_perm.
    simplify_bools_lia_one_kernel.
    unfold compose.
    rewrite HfSpadl, swap_perm_left by lia.
    assert (f k <> padl) by (intros HF; 
      rewrite <- HfSpadl in HF;
      generalize (f_equal (perm_inv n f) HF);
      cleanup_perm; lia).
    assert (f k <> S padl) by (intros HF; 
      rewrite <- Hfpadl in HF;
      generalize (f_equal (perm_inv n f) HF);
      cleanup_perm; lia).
    rewrite swap_perm_neither by lia.
    bdestructΩ'.
  - assert (f (k + 1 + 1) <> S padl) by (intros HF; 
      rewrite <- Hfpadl in HF;
      generalize (f_equal (perm_inv n f) HF);
      cleanup_perm; lia).
    assert (f (k + 1 + 1) <> padl) by (intros HF; 
      rewrite <- HfSpadl in HF;
      generalize (f_equal (perm_inv n f) HF);
      cleanup_perm; lia).
    unfold contract_perm.
    simplify_bools_lia_one_kernel.
    unfold compose.
    rewrite HfSpadl.
    rewrite swap_perm_left, swap_perm_neither by lia.
    bdestructΩ'.
Qed.

Lemma lperm_prep_compose_cap_NF_l_permutation lperm rperm nid ncup ncap padl 
  (Hpadl : S padl < ncup + ncup + nid) 
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  permutation (ncup + ncup + nid) 
  (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  (* pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd. *)
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  pose proof (stack_perms_WF_idn (ncup + ncup) nid) as mkWF.
  rewrite <- (mkWF (tensor_perms ncup 2 (swap_perm 0 (perm_inv 
    (ncup + ncup + nid) lperm padl / 2) ncup) idn)) by cleanup_perm.
  rewrite <- (mkWF (tensor_perms ncup 2 (swap_2_to_2_perm 0 1
       (perm_inv (ncup + ncup + nid) lperm padl / 2)
       (perm_inv (ncup + ncup + nid) lperm (S padl) / 2) ncup) idn)) 
       by cleanup_perm.
  rewrite <- (mkWF (swap_perm 0 1 (ncup + ncup))) by cleanup_perm.
  rewrite <- (mkWF (swap_perm 2 3 (ncup + ncup))) by cleanup_perm.
  rewrite <- (mkWF (swap_perm (ncup + ncup - 2) (ncup + ncup - 1)
    (ncup + ncup))) by cleanup_perm.
  bdestruct (perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup);
    [assert (perm_inv (ncup + ncup + nid) lperm padl / 2 < ncup)   
    by (apply Nat.Div0.div_lt_upper_bound; lia)|];
  (bdestruct (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup); 
    [assert (perm_inv (ncup + ncup + nid) lperm (S padl) / 2 < ncup) 
    by (apply Nat.Div0.div_lt_upper_bound; lia)|]);
  cbn [andb];
  bdestructΩ'; auto 10 with perm_db zarith.
Qed.

#[export] Hint Resolve lperm_prep_compose_cap_NF_l_permutation : perm_db.

Lemma prep_compose_cap_NF_l_case_2_pull lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm padl)  
  (HSpadl :  ncup + ncup <= perm_inv (ncup + ncup + nid) lperm (S padl)) 
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  (* lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup) = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup + 1) = S padl. *)
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2))
    (perm_to_matrix (ncup + ncup + nid) 
    (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)))
    ((I (2^padl) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - (2 + padl)))) =
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2)) (2^(ncup+ncup+nid-2))
  ((I (2 ^ (ncup + ncup)) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (nid - 2))) 
  (perm_to_matrix (ncup + ncup + nid - 2) 
    (contract_perm (contract_perm 
      (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl))
      (ncup + ncup + 1)) (ncup + ncup))).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  rewrite (fun H => perm_to_matrix_cap_pullthrough_r_gen_alt H _ (ncup + ncup));
  [|auto with perm_db|lia|lia|
  replace (S (ncup + ncup)) with (ncup + ncup + 1) by lia;
  now apply prep_compose_cap_NF_l_case_2..].
  do 2 f_equal; repeat (f_equal; try lia).
Qed.

Lemma prep_compose_cap_NF_l_case_3_2_pull lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm padl)  
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  (* lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup - 1) = S padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup) = padl. *)
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2))
    (perm_to_matrix (ncup + ncup + nid) 
    (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)))
    ((I (2^padl) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - (2 + padl)))) =
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2)) (2^(ncup+ncup+nid-2))
  ((I (2 ^ (ncup + ncup - 1)) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (nid - 1))) 
  (perm_to_matrix (ncup + ncup + nid - 2) 
    (contract_perm (contract_perm 
      (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl))
      (ncup + ncup)) (ncup + ncup - 1))).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  rewrite (fun H => perm_to_matrix_cap_pullthrough_r_gen_alt_swapped 
    H _ (ncup + ncup - 1));
  [|auto with perm_db|lia|lia|
  replace (S (ncup + ncup - 1)) with (ncup + ncup) by lia;
  now apply prep_compose_cap_NF_l_case_3_2..].
  do 2 f_equal; repeat (f_equal; try lia).
Qed.

Lemma prep_compose_cap_NF_l_case_3_1_pull lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm (S padl))  
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  (* lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup - 1) = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup) = S padl. *)
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2))
    (perm_to_matrix (ncup + ncup + nid) 
    (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)))
    ((I (2^padl) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - (2 + padl)))) =
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2)) (2^(ncup+ncup+nid-2))
  ((I (2 ^ (ncup + ncup - 1)) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (nid - 1))) 
  (perm_to_matrix (ncup + ncup + nid - 2) 
    (contract_perm (contract_perm 
      (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl))
      (ncup + ncup)) (ncup + ncup - 1))).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  rewrite (fun H => perm_to_matrix_cap_pullthrough_r_gen_alt
    H _ (ncup + ncup - 1));
  [|auto with perm_db|lia|lia|
  replace (S (ncup + ncup - 1)) with (ncup + ncup) by lia;
  now apply prep_compose_cap_NF_l_case_3_1..].
  do 2 f_equal; repeat (f_equal; try lia).
Qed.


Lemma prep_compose_cap_NF_l_case_1_2_pull lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hdiff : perm_inv (ncup + ncup + nid) lperm padl / 2 <> 
    perm_inv (ncup + ncup + nid) lperm (S padl) / 2) 
  (Hlperm : permutation (ncup + ncup + nid) lperm):
  (* lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 1 = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 2 = S padl. *)
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2))
    (perm_to_matrix (ncup + ncup + nid) 
    (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)))
    ((I (2^padl) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - (2 + padl)))) =
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2)) (2^(ncup+ncup+nid-2))
  ((I (2 ^ 1) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - 3))) 
  (perm_to_matrix (ncup + ncup + nid - 2) 
    (contract_perm (contract_perm 
      (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl))
      2) 1)).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  pose proof (diff_divs_lower_bound 
    (perm_inv (ncup + ncup + nid) lperm padl)
    (perm_inv (ncup + ncup + nid) lperm (S padl))
    2 (ncup + ncup) ltac:(easy) ltac:(easy) ltac:(easy)).
  rewrite (fun H => perm_to_matrix_cap_pullthrough_r_gen_alt
    H _ (1));
  [|auto with perm_db|lia|lia|
  now apply prep_compose_cap_NF_l_case_1_2..].
  do 2 f_equal; repeat (f_equal; try lia).
Qed.


Lemma prep_compose_cap_NF_l_case_1_1_pull lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hsame : perm_inv (ncup + ncup + nid) lperm padl / 2 = 
    perm_inv (ncup + ncup + nid) lperm (S padl) / 2) 
  (Hlperm : permutation (ncup + ncup + nid) lperm):
  (* lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 0 = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 1 = S padl. *)
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2))
    (perm_to_matrix (ncup + ncup + nid) 
    (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)))
    ((I (2^padl) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - (2 + padl)))) =
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2)) (2^(ncup+ncup+nid-2))
  ((I (2 ^ 0) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - 2))) 
  (perm_to_matrix (ncup + ncup + nid - 2) 
    (contract_perm (contract_perm 
      (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl))
      1) 0)).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  (* pose proof (diff_divs_lower_bound 
    (perm_inv (ncup + ncup + nid) lperm padl)
    (perm_inv (ncup + ncup + nid) lperm (S padl))
    2 (ncup + ncup) ltac:(easy) ltac:(easy) ltac:(easy)). *)
  rewrite (fun H => perm_to_matrix_cap_pullthrough_r_gen_alt
    H _ 0);
  [|auto with perm_db|lia|lia|
  now apply prep_compose_cap_NF_l_case_1_1..].
  easy.
Qed.






Lemma n_m_cup_cap_times_cup_r n m (Hn : n <> 0) : 
  matrix_of_biperm (n + n) (m + m) (n_m_cup_cap n m) 
  × (⟦ ⊂ ⟧ ⊗ I (2 ^ (n + n - 2))) = 2%R .*
  matrix_of_biperm ((n - 1) + (n - 1)) (m + m) (n_m_cup_cap (n-1) m).
Proof.
  rewrite n_m_cup_cap_comm.
  replace (n_m_cup_cap m n) with 
    (n_m_cup_cap (m + 0) ((n - 1) + 1)) by (f_equal; lia).
  rewrite n_m_cup_cap_plus_plus_decomp.
  replace (matrix_of_biperm (n + n) (m + m)) with
    (matrix_of_biperm ((n-1 + (n-1)) + (1 + 1)) ((m + m) + (0 + 0)))
    by (f_equal; lia).
  rewrite matrix_of_stack_biperms by auto with biperm_db.
  restore_dims.
  rewrite kron_mixed_product' by (f_equal; lia).
  rewrite n_m_cup_cap_comm.
  rewrite matrix_of_biperm_n_m_cup_cap_0_r.
  rewrite kron_n_1 by auto with wf_db.
  restore_dims.
  rewrite cap_times_cup, Mmult_1_r by auto with wf_db.
  rewrite Mscale_kron_dist_l.
  rewrite kron_1_l by auto with wf_db.
  restore_dims.
  now rewrite n_m_cup_cap_comm.
Qed.

Lemma n_m_cup_cap_times_up_cup_r n m (Hn : 1 < n) : 
  matrix_of_biperm (n + n) (m + m) (n_m_cup_cap n m) 
  × ((I (2 ^ 1) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (n + n - 3))) =
  matrix_of_biperm ((n - 1) + (n - 1)) (m + m) (n_m_cup_cap (n-1) m).
Proof.
  rewrite n_m_cup_cap_comm.
  replace (n_m_cup_cap m n) with 
    (n_m_cup_cap (m + 0) ((n - 2) + 2)) by (f_equal; lia).
  rewrite n_m_cup_cap_plus_plus_decomp.
  replace (matrix_of_biperm (n + n) (m + m)) with
    (matrix_of_biperm ((n-2 + (n-2)) + (2 + 2)) ((m + m) + (0 + 0)))
    by (f_equal; lia).
  rewrite matrix_of_stack_biperms by auto with biperm_db.
  replace (I (2 ^ (n + n - 3))) with (I (2^1 * 2^(n + n - 4))) by 
    (rewrite <- Nat.pow_add_r; do 2 f_equal; lia).
  rewrite <- id_kron.
  restore_dims.
  rewrite <- kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product' by (reflexivity + f_equal; lia).
  rewrite n_m_cup_cap_comm.
  rewrite matrix_of_biperm_n_m_cup_cap_0_r.
  rewrite kron_n_S.
  rewrite kron_n_1 by auto with wf_db.
  restore_dims.
  rewrite cap_cap_cup_yank_eq, Mmult_1_r by auto with wf_db.
  rewrite <- (kron_n_1 (⟦⊃⟧)) by auto with wf_db.
  rewrite <- matrix_of_biperm_n_m_cup_cap_0_r.
  restore_dims.
  rewrite <- matrix_of_stack_biperms by auto with biperm_db.
  replace (stack_biperms (m + m) (n-2+(n-2)) 0 (1 + 1)) 
    with (stack_biperms (m + m) (n-2+(n-2)) (0+0) (1+1)) 
    by (f_equal; lia).
  rewrite (n_m_cup_cap_comm 1 0).
  rewrite <- n_m_cup_cap_plus_plus_decomp.
  rewrite Nat.add_0_r.
  rewrite <- double_add.
  replace (n-2+1) with (n-1) by lia.
  f_equal.
  rewrite n_m_cup_cap_comm.
  f_equal; lia.
Qed.

Lemma n_m_cup_cap_yank_one_r n m p (Hn : n <> 0) (Hp : p <> 0) : 
  matrix_of_biperm (n + n) (m + m) (n_m_cup_cap n m) ⊗ I (2 ^ p)
  × ((I (2 ^ (n + n - 1)) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (p - 1))) =
  matrix_of_biperm ((n - 1) + (n - 1)) (m + m) (n_m_cup_cap (n-1) m) ⊗ I (2^p).
Proof.
  rewrite n_m_cup_cap_comm.
  replace (n_m_cup_cap m n) with 
    (n_m_cup_cap (0 + m) (1 + (n - 1))) by (f_equal; lia).
  rewrite n_m_cup_cap_plus_plus_decomp.
  replace (matrix_of_biperm (n + n) (m + m)) with
    (matrix_of_biperm ((1 + 1) + (n-1 + (n-1))) ((0 + 0) + (m + m)))
    by (f_equal; lia).
  rewrite matrix_of_stack_biperms by auto with biperm_db.
  replace (2^ (n+n-1)) with (2 ^ (n-1+(n-1)) * (2^1)) by 
    (rewrite <- Nat.pow_add_r; f_equal; lia).
  rewrite <- id_kron.
  restore_dims.
  rewrite 3!kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product' by 
    (rewrite <-?Nat.pow_add_r;f_equal;lia).
  rewrite Mmult_1_r by auto with wf_db.
  restore_dims.
  f_equal; [rewrite <-?Nat.pow_add_r;f_equal;lia..
  |now rewrite n_m_cup_cap_comm|].
  replace (2 ^ p) with (2 ^ 1 * 2 ^ (p - 1)) 
    by (rewrite <- Nat.pow_add_r; f_equal; lia).
  rewrite <- id_kron.
  rewrite <- 2!kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_r by auto with wf_db.
  rewrite n_m_cup_cap_comm.
  rewrite matrix_of_biperm_n_m_cup_cap_0_r.
  rewrite kron_n_1 by auto with wf_db.
  f_equal.
  apply cap_cup_yank_eq_alt.
Qed.
  

Definition contract_lperm_NF (b : NF_biperm) v : NF_biperm :=
  {|
    lperm' := contract_perm (lperm' b) v;
    rperm' := rperm' b;
    nid'   := nid' b;
    ncup'  := ncup' b;
    ncap'  := ncap' b;
  |}.

Definition dec_ncup_NF (b : NF_biperm) : NF_biperm :=
  {|
    lperm' := lperm' b;
    rperm' := rperm' b;
    nid'   := nid' b;
    ncup'  := ncup' b - 1;
    ncap'  := ncap' b;
  |}.

Definition dec_dec_nid_NF (b : NF_biperm) : NF_biperm :=
  {|
    lperm' := lperm' b;
    rperm' := rperm' b;
    nid'   := nid' b - 2;
    ncup'  := ncup' b;
    ncap'  := ncap' b;
  |}.


Definition incr_ncap_NF (b : NF_biperm) : NF_biperm :=
  {|
    lperm' := lperm' b;
    rperm' := rperm' b;
    nid'   := nid' b;
    ncup'  := ncup' b;
    ncap'  := 1 + ncap' b;
  |}.

Definition compose_cap_NF_l (lperm_init rperm : nat -> nat) 
  (nid ncup ncap padl : nat) :=
  let lperm := perm_inv (ncup + ncup + nid) lperm_init in
  if (lperm padl <? ncup + ncup) && (lperm (S padl) <? ncup + ncup) then
    (* First case, both in cups *)
    if lperm padl / 2 =? lperm (S padl) / 2 then
      (* First subcase, same cup *)
      dec_ncup_NF (contract_lperm_NF (contract_lperm_NF 
        (prep_compose_cap_NF_l lperm_init rperm nid ncup ncap padl)
        1) 0)
    else 
      (* Second subcase, different cups *)
    dec_ncup_NF (contract_lperm_NF (contract_lperm_NF 
      (prep_compose_cap_NF_l lperm_init rperm nid ncup ncap padl)
      2) 1)
  else if (lperm padl <? ncup + ncup) (* && (lperm (S padl) <? ncup + ncup) *) then
    (* Third case, first orientation (first leg in cup) *)
    dec_ncup_NF (contract_lperm_NF (contract_lperm_NF 
      (prep_compose_cap_NF_l lperm_init rperm nid ncup ncap padl)
      (ncup + ncup)) (ncup + ncup - 1))
  else if (* (lperm padl <? ncup + ncup) && *) (lperm (S padl) <? ncup + ncup) then
    (* Third case, second orientation (second leg in cup) *)
    dec_ncup_NF (contract_lperm_NF (contract_lperm_NF 
      (prep_compose_cap_NF_l lperm_init rperm nid ncup ncap padl)
      (ncup + ncup)) (ncup + ncup - 1))
  else (* if (lperm padl <? ncup + ncup) && (lperm (S padl) <? ncup + ncup) then *)
    (* Second case, both legs in ids *)
    incr_ncap_NF (dec_dec_nid_NF (contract_lperm_NF (contract_lperm_NF 
      (prep_compose_cap_NF_l lperm_init rperm nid ncup ncap padl)
      (ncup + ncup + 1)) (ncup + ncup))).

Lemma dec_contract_contract_WF (b : NF_biperm) (Hb : WF_NF_biperm b) 
  v v' (Hv : v < ncup' b + ncup' b + nid' b) 
  (Hv' : v' < ncup' b + ncup' b + nid' b - 1) 
  (Hncup' : ncup' b <> 0) : 
  WF_NF_biperm (dec_ncup_NF (contract_lperm_NF (contract_lperm_NF b v) v')).
Proof.
  unfold WF_NF_biperm in *. simpl. 
  split; [|easy].
  replace (ncup' b - 1 + (ncup' b - 1) + nid' b) with 
    (ncup' b + ncup' b + nid' b - 1 - 1) by lia.
  apply contract_perm_permutation; [|easy].
  apply contract_perm_permutation; easy.
Qed.

Lemma incr_dec_dec_contract_contract_WF (b : NF_biperm) (Hb : WF_NF_biperm b) 
  v v' (Hv : v < ncup' b + ncup' b + nid' b) 
  (Hv' : v' < ncup' b + ncup' b + nid' b - 1) 
  (Hnid' : 1 < nid' b) : 
  WF_NF_biperm (
    incr_ncap_NF (dec_dec_nid_NF 
      (contract_lperm_NF (contract_lperm_NF b v) v'))).
Proof.
  unfold WF_NF_biperm in *. simpl.
  split.
  - replace (ncup' b + ncup' b + (nid' b - 2)) with 
      (ncup' b + ncup' b + nid' b - 1 - 1) by lia.
    apply contract_perm_permutation; [|easy].
    apply contract_perm_permutation; easy.
  - replace (S (ncap' b + S (ncap' b) + (nid' b - 2))) with 
      (ncap' b + ncap' b + nid' b) by lia.
    easy.
Qed.

Lemma nid_prep_compose_cap_NF_l lperm rperm nid ncup ncap padl : 
  nid' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) = nid.
Proof.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ nid').
  simpl.
  now rewrite !Tauto.if_same.
Qed.

Lemma ncup_prep_compose_cap_NF_l lperm rperm nid ncup ncap padl : 
  ncup' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) = ncup.
Proof.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ ncup').
  simpl.
  now rewrite !Tauto.if_same.
Qed.

Lemma ncap_prep_compose_cap_NF_l lperm rperm nid ncup ncap padl : 
  ncap' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) = ncap.
Proof.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ ncap').
  simpl.
  now rewrite !Tauto.if_same.
Qed.

Lemma rperm_prep_compose_cap_NF_l_permutation lperm rperm nid ncup ncap padl 
  (Hpadl : S padl < ncup + ncup + nid)
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) : 
  permutation (ncap + ncap + nid) 
  (rperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  unfold prep_compose_cap_NF_l; 
  rewrite !(if_dist _ _ _ rperm'); simpl.
  bdestructΩ'; auto with perm_db zarith.
Qed.

#[export] Hint Resolve rperm_prep_compose_cap_NF_l_permutation : perm_db.

Lemma compose_cap_NF_l_WF (lperm rperm : nat -> nat) 
  (nid ncup ncap padl : nat) (Hpadl : S padl < ncup + ncup + nid)
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  WF_NF_biperm (compose_cap_NF_l lperm rperm nid ncup ncap padl).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  unfold compose_cap_NF_l.
  bdestruct (perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup);
    [assert (perm_inv (ncup + ncup + nid) lperm padl / 2 < ncup)   
    by (apply Nat.Div0.div_lt_upper_bound; lia)|];
  (bdestruct (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup); 
    [assert (perm_inv (ncup + ncup + nid) lperm (S padl) / 2 < ncup) 
    by (apply Nat.Div0.div_lt_upper_bound; lia)|]);
  cbn [andb];
  [bdestruct (perm_inv (ncup + ncup + nid) lperm padl / 2 
    =? perm_inv (ncup + ncup + nid) lperm (S padl) / 2)|..].
  - apply dec_contract_contract_WF; [split|..];
    rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
      auto with perm_db zarith.
  - apply dec_contract_contract_WF; [split|..];
    rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
      auto with perm_db zarith.
  - apply dec_contract_contract_WF; [split|..];
    rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
      auto with perm_db zarith.
  - apply dec_contract_contract_WF; [split|..];
    rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
      auto with perm_db zarith.
  - apply incr_dec_dec_contract_contract_WF; [split|..];
    rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
      auto with perm_db zarith.
Qed.

Lemma prep_compose_cap_NF_l_WF (lperm rperm : nat -> nat) 
  (nid ncup ncap padl : nat) (Hpadl : S padl < ncup + ncup + nid)
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  WF_NF_biperm (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl).
Proof.
  split;
  rewrite ?nid_prep_compose_cap_NF_l, 
    ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
    auto with perm_db zarith.
Qed.

Lemma matrix_of_realize_biperm_data' {lperm rperm : nat -> nat} 
  {nid ncup ncap : nat} insize outsize : 
  insize = ncup + ncup + nid ->
  outsize = ncap + ncap + nid ->
  permutation insize lperm ->
  permutation outsize rperm ->
  matrix_of_biperm insize outsize
    (realize_biperm_data lperm rperm nid ncup ncap) =
  perm_to_matrix (ncap + ncap + nid) rperm
  × (matrix_of_biperm (ncup + ncup) (ncap + ncap) (n_m_cup_cap ncup ncap)
    ⊗ I (2 ^ nid)) × perm_to_matrix (ncup + ncup + nid) lperm.
Proof.
  intros -> ->.
  apply matrix_of_realize_biperm_data.
Qed.

Lemma matrix_of_realize_NF_biperm' insize outsize (b : NF_biperm) : 
  insize = ncup' b + ncup' b + nid' b ->
  outsize = ncap' b + ncap' b + nid' b ->
  WF_NF_biperm b ->
  matrix_of_biperm insize outsize
    (realize_NF_biperm b) =
  perm_to_matrix (ncap' b + ncap' b + nid' b) (rperm' b)
  × (matrix_of_biperm (ncup' b + ncup' b) (ncap' b + ncap' b) 
    (n_m_cup_cap (ncup' b) (ncap' b))
    ⊗ I (2 ^ nid' b)) × perm_to_matrix (ncup' b + ncup' b + nid' b) (lperm' b).
Proof.
  intros -> ->.
  intros [].
  now apply matrix_of_realize_biperm_data.
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

#[global] Add Parametric Relation n m : (Matrix n m) (@mat_prop n m) 
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

#[global] Add Parametric Morphism n m o : (@Mmult n m o) with signature
  mat_prop n m ==> mat_prop m o ==> mat_prop n o as Mmult_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB) C D (cCD & HCD & HcCD).
  Proportional.prop_exists_nonzero (cAB * cCD)%C.
  2: now apply Cmult_neq_0.
  rewrite HAB, HCD.
  now rewrite Mscale_mult_dist_l, Mscale_mult_dist_r, Mscale_assoc.
Qed.

#[global] Add Parametric Morphism n m o p : (@kron n m o p) with signature
  mat_prop n m ==> mat_prop o p ==> mat_prop (n*o) (m*p) as kron_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB) C D (cCD & HCD & HcCD).
  Proportional.prop_exists_nonzero (cAB * cCD)%C.
  2: now apply Cmult_neq_0.
  rewrite HAB, HCD.
  now rewrite Mscale_kron_dist_l, Mscale_kron_dist_r, Mscale_assoc.
Qed.

#[global] Add Parametric Morphism n m c : (@scale n m c) with signature
  mat_prop n m ==> mat_prop n m as Mscale_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB).
  Proportional.prop_exists_nonzero (cAB)%C.
  2: easy.
  rewrite HAB.
  now rewrite 2!Mscale_assoc, Cmult_comm.
Qed.

#[global] Add Parametric Morphism n m : (@transpose n m) with signature
  mat_prop n m ==> mat_prop m n as transpose_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB).
  Proportional.prop_exists_nonzero (cAB)%C.
  2: easy.
  rewrite HAB.
  now rewrite Mscale_trans.
Qed.

#[global] Add Parametric Morphism n m k : (@kron_n k n m) with signature
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


Lemma compose_cap_NF_l_correct {lperm rperm} {nid ncup ncap} 
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  padl (Hpadl : S padl < ncup + ncup + nid) : 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid)
    (realize_biperm_data lperm rperm nid ncup ncap)
  × ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^(ncup + ncup + nid - (2 + padl)))) 
  [∝]
  matrix_of_biperm (ncup + ncup + nid - 2) (ncap + ncap + nid)
    (realize_NF_biperm 
      (compose_cap_NF_l lperm rperm nid ncup ncap padl)).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  set (cval := if 
  (perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup) && 
  (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup) &&
  (perm_inv (ncup + ncup + nid) lperm padl / 2 
    =? perm_inv (ncup + ncup + nid) lperm (S padl) / 2)
  then 2%R else 1%R
  ).
  exists cval.
  split; [|unfold cval; match goal with 
  |- context[if ?b then _ else _] => destruct b end; 
  auto using C2_nonzero, C1_nonzero].
  rewrite <- (prep_compose_cap_NF_l_correct lperm rperm nid ncup ncap padl)
    by easy.
  rewrite (matrix_of_realize_NF_biperm' (ncup+ncup+nid) (ncap+ncap+nid));
  [|now rewrite ?nid_prep_compose_cap_NF_l, 
    ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l..|
    now apply prep_compose_cap_NF_l_WF].
  rewrite (matrix_of_realize_NF_biperm' (ncup+ncup+nid-2) (ncap+ncap+nid));
  [| 
    unfold compose_cap_NF_l;
    rewrite !(if_dist NF_biperm nat);
    simpl; rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
    bdestructΩ'..
  | now apply compose_cap_NF_l_WF].
  
  rewrite nid_prep_compose_cap_NF_l, 
    ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
  pattern (compose_cap_NF_l lperm rperm nid ncup ncap padl).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold compose_cap_NF_l.
  bdestruct (perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup);
    [assert (perm_inv (ncup + ncup + nid) lperm padl / 2 < ncup)   
    by (apply Nat.Div0.div_lt_upper_bound; lia)|];
  (bdestruct (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup); 
    [assert (perm_inv (ncup + ncup + nid) lperm (S padl) / 2 < ncup) 
    by (apply Nat.Div0.div_lt_upper_bound; lia)|]);
  cbn [andb];
  [bdestruct (perm_inv (ncup + ncup + nid) lperm padl / 2 
    =? perm_inv (ncup + ncup + nid) lperm (S padl) / 2)|..].
  - unfold Pred.
    cbn -[ZX_semantics].
    rewrite 2!Mmult_assoc.
    rewrite prep_compose_cap_NF_l_case_1_1_pull by easy.

    rewrite nid_prep_compose_cap_NF_l, 
      ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
    restore_dims.
    rewrite <- Mscale_mult_dist_l, <- Mscale_mult_dist_r.
    rewrite Mmult_assoc.
    restore_dims.
    f_equal; [f_equal; lia|].
    rewrite kron_1_l by auto with wf_db.
    restore_dims.
    replace (2^(ncup + ncup) * 2 ^ nid) with (2^2 * 2 ^ (ncup+ncup+nid-2)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- Mmult_assoc.
    restore_dims.
    f_equal; [rewrite <- ?Nat.pow_add_r; f_equal; lia.. | | f_equal; lia].
    replace (2^(ncup+ncup+nid-2)) with (2^(ncup+ncup-2)*(2^nid)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- id_kron, <- kron_assoc by auto with wf_db.
    restore_dims.
    rewrite kron_mixed_product' by (rewrite <- ?Nat.pow_add_r; f_equal; lia).
    rewrite Mmult_1_l by auto with wf_db.
    rewrite <- Mscale_kron_dist_l.
    f_equal; [rewrite <- !Nat.pow_add_r; f_equal; lia|].
    apply n_m_cup_cap_times_cup_r; lia.
  - unfold Pred.
    cbn -[ZX_semantics].
    rewrite 2!Mmult_assoc.
    rewrite prep_compose_cap_NF_l_case_1_2_pull by easy.
    rewrite nid_prep_compose_cap_NF_l, 
      ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
    restore_dims.
    rewrite Mscale_1_l.
    rewrite Mmult_assoc.
    restore_dims.
    f_equal; [f_equal; lia|].
    replace (2^(ncup + ncup) * 2 ^ nid) with (2^1*2^2*2^(ncup+ncup+nid-3)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- Mmult_assoc.
    restore_dims.
    f_equal; [rewrite <- ?Nat.pow_add_r; f_equal; lia.. | | f_equal; lia].
    replace (2^(ncup+ncup+nid-3)) with (2^(ncup+ncup-3)*(2^nid)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- id_kron, <- kron_assoc by auto with wf_db.
    restore_dims.
    rewrite kron_mixed_product' by (rewrite <- ?Nat.pow_add_r; f_equal; lia).
    rewrite Mmult_1_l by auto with wf_db.
    f_equal; [rewrite <- !Nat.pow_add_r; f_equal; lia|].
    apply n_m_cup_cap_times_up_cup_r; lia.
  - unfold Pred.
    cbn -[ZX_semantics].
    rewrite Mscale_1_l.
    rewrite 2!Mmult_assoc.
    rewrite prep_compose_cap_NF_l_case_3_1_pull by easy.
    rewrite nid_prep_compose_cap_NF_l, 
      ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
    restore_dims.
    rewrite Mmult_assoc.
    restore_dims.
    f_equal; [f_equal; lia|].
    replace (2^(ncup + ncup) * 2 ^ nid) with (2^(ncup+ncup-1)*2^2*2^(nid-1)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- Mmult_assoc.
    restore_dims.
    f_equal; [rewrite <- ?Nat.pow_add_r; f_equal; lia.. | | f_equal; lia].
    apply n_m_cup_cap_yank_one_r; lia.
  - unfold Pred.
    cbn -[ZX_semantics].
    rewrite Mscale_1_l.
    rewrite 2!Mmult_assoc.
    rewrite prep_compose_cap_NF_l_case_3_2_pull by easy.
    rewrite nid_prep_compose_cap_NF_l, 
      ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
    restore_dims.
    rewrite Mmult_assoc.
    restore_dims.
    f_equal; [f_equal; lia|].
    replace (2^(ncup + ncup) * 2 ^ nid) with (2^(ncup+ncup-1)*2^2*2^(nid-1)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- Mmult_assoc.
    restore_dims.
    f_equal; [rewrite <- ?Nat.pow_add_r; f_equal; lia.. | | f_equal; lia].
    apply n_m_cup_cap_yank_one_r; lia.
  - unfold Pred.
    cbn -[ZX_semantics Nat.add].
    rewrite Mscale_1_l.
    rewrite 2!Mmult_assoc.
    rewrite prep_compose_cap_NF_l_case_2_pull by easy.
    rewrite nid_prep_compose_cap_NF_l, 
      ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
    restore_dims.
    rewrite Mmult_assoc.
    f_equal; [f_equal; lia..|].
    rewrite kron_assoc by auto with wf_db.
    replace (2^(ncup + ncup) * 2 ^ nid) with (2^(ncup+ncup)*2^2*2^(nid-2)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- Mmult_assoc.
    restore_dims.
    f_equal; [rewrite <- ?Nat.pow_add_r; f_equal; lia.. | | f_equal; lia].
    replace (2 ^ nid) with (2 ^ 2 * 2 ^ (nid - 2))
      by (rewrite <- Nat.pow_add_r; f_equal; lia).
    rewrite <- id_kron.
    rewrite <- !kron_assoc by auto with wf_db.
    restore_dims.
    rewrite kron_mixed_product, Mmult_1_r by auto with wf_db.
    f_equal; [rewrite <- Nat.pow_add_r; f_equal; lia..|].
    rewrite kron_mixed_product, Mmult_1_r, Mmult_1_l by auto with wf_db.
    replace (n_m_cup_cap ncup (1 + ncap)) with 
      (n_m_cup_cap (0 + ncup) (1 + ncap)) by (f_equal; lia).
    rewrite (n_m_cup_cap_comm (_ + _)), n_m_cup_cap_plus_plus_decomp.
    replace (matrix_of_biperm (ncup + ncup) (1 + ncap + (1 + ncap)))
      with (matrix_of_biperm ((0 + 0) + (ncup + ncup)) ((1 + 1) + (ncap + ncap)))
      by (f_equal; lia).
    rewrite matrix_of_stack_biperms by auto with biperm_db.
    f_equal; [now rewrite n_m_cup_cap_comm|].
    rewrite matrix_of_biperm_n_m_cup_cap_0_l.
    now rewrite kron_n_1 by auto with wf_db.
Qed.

Fixpoint compose_n_caps_NF_l (b : NF_biperm) (num_caps : nat) :=
  match num_caps with 
  | 0 => b
  | S k => 
    uncurry_NF_biperm compose_cap_NF_l (compose_n_caps_NF_l b k) 0
  end.

Lemma ncup_ncup_nid_uncurry_compose_cap_NF_l (b : NF_biperm) 
  (Hb : WF_NF_biperm b) n (Hn : S n < ncup' b + ncup' b + nid' b) : 
  ncup' (uncurry_NF_biperm compose_cap_NF_l b n) + 
  ncup' (uncurry_NF_biperm compose_cap_NF_l b n) + 
  nid' (uncurry_NF_biperm compose_cap_NF_l b n) = 
  ncup' b + ncup' b + nid' b - 2.
Proof.
  destruct Hb.
  unfold uncurry_NF_biperm.
  unfold compose_cap_NF_l.
  rewrite !(if_dist NF_biperm nat).
  simpl.
  rewrite !Tauto.if_same.
  rewrite ncup_prep_compose_cap_NF_l, nid_prep_compose_cap_NF_l.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (S n) 
    < ncup' b + ncup' b + nid' b) by auto with perm_bounded_db.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (n) 
    < ncup' b + ncup' b + nid' b) by auto with perm_bounded_db.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (n) 
    <> perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (S n))
    by (intros Hfalse; 
    apply (permutation_is_injective (ncup' b + ncup' b + nid' b)) in Hfalse;
    auto with perm_db zarith).
  bdestructΩ'.
Qed.

Lemma ncap_ncap_nid_uncurry_compose_cap_NF_l (b : NF_biperm) 
  (Hb : WF_NF_biperm b) n (Hn : S n < ncup' b + ncup' b + nid' b) : 
  ncap' (uncurry_NF_biperm compose_cap_NF_l b n) + 
  ncap' (uncurry_NF_biperm compose_cap_NF_l b n) + 
  nid' (uncurry_NF_biperm compose_cap_NF_l b n) = 
  ncap' b + ncap' b + nid' b.
Proof.
  destruct Hb.
  unfold uncurry_NF_biperm.
  unfold compose_cap_NF_l.
  rewrite !(if_dist NF_biperm nat).
  simpl.
  rewrite !Tauto.if_same.
  rewrite ncap_prep_compose_cap_NF_l, nid_prep_compose_cap_NF_l.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (S n) 
    < ncup' b + ncup' b + nid' b) by auto with perm_bounded_db.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (n) 
    < ncup' b + ncup' b + nid' b) by auto with perm_bounded_db.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (n) 
    <> perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (S n))
    by (intros Hfalse; 
    apply (permutation_is_injective (ncup' b + ncup' b + nid' b)) in Hfalse;
    auto with perm_db zarith).
  bdestructΩ'.
Qed.

Lemma ncup_ncup_nid_ncap_ncap_nid_WF_compose_n_caps_NF_l (b : NF_biperm) 
  (Hb : WF_NF_biperm b) (num_caps : nat) 
  (Hnum_caps : num_caps + num_caps <= ncup' b + ncup' b + nid' b) :
  ncap' (compose_n_caps_NF_l b num_caps) + 
  ncap' (compose_n_caps_NF_l b num_caps) + 
  nid' (compose_n_caps_NF_l b num_caps) = 
  ncap' b + ncap' b + nid' b /\
  ncup' (compose_n_caps_NF_l b num_caps) + 
  ncup' (compose_n_caps_NF_l b num_caps) + 
  nid' (compose_n_caps_NF_l b num_caps) = 
  ncup' b + ncup' b + nid' b - (num_caps + num_caps)
  /\ WF_NF_biperm (compose_n_caps_NF_l b num_caps).
Proof.
  induction num_caps.
  - simpl; split; [|split]; [lia.. | easy].
  - simpl.
    destruct (IHnum_caps ltac:(lia)) as [Hcups HWF].
    rewrite ncup_ncup_nid_uncurry_compose_cap_NF_l, 
      ncap_ncap_nid_uncurry_compose_cap_NF_l by (easy + lia).
    repeat split; try lia;
    (apply compose_cap_NF_l_WF; [lia|apply HWF..]).
Qed.


Lemma compose_n_caps_NF_l_WF (b : NF_biperm) (num_caps : nat)
  (Hnum_caps : num_caps + num_caps <= ncup' b + ncup' b + nid' b) 
  (Hb : WF_NF_biperm b) :
  WF_NF_biperm (compose_n_caps_NF_l b num_caps).
Proof.
  now apply ncup_ncup_nid_ncap_ncap_nid_WF_compose_n_caps_NF_l.
Qed.

Lemma ncup_ncup_nid_compose_n_caps_NF_l (b : NF_biperm) (num_caps : nat)
  (Hnum_caps : num_caps + num_caps <= ncup' b + ncup' b + nid' b) 
  (Hb : WF_NF_biperm b) :
  ncup' (compose_n_caps_NF_l b num_caps) +
  ncup' (compose_n_caps_NF_l b num_caps) +
  nid' (compose_n_caps_NF_l b num_caps) = 
  ncup' b + ncup' b + nid' b - (num_caps + num_caps).
Proof.
  now apply ncup_ncup_nid_ncap_ncap_nid_WF_compose_n_caps_NF_l.
Qed.

Lemma ncap_ncap_nid_compose_n_caps_NF_l (b : NF_biperm) (num_caps : nat)
  (Hnum_caps : num_caps + num_caps <= ncup' b + ncup' b + nid' b) 
  (Hb : WF_NF_biperm b) :
  ncap' (compose_n_caps_NF_l b num_caps) +
  ncap' (compose_n_caps_NF_l b num_caps) +
  nid' (compose_n_caps_NF_l b num_caps) = 
  ncap' b + ncap' b + nid' b.
Proof.
  now apply ncup_ncup_nid_ncap_ncap_nid_WF_compose_n_caps_NF_l.
Qed.

Definition matrix_of_NF_biperm (b : NF_biperm) := 
  matrix_of_biperm (ncup' b + ncup' b + nid' b) 
    (ncap' b + ncap' b + nid' b) (realize_NF_biperm b).

Lemma matrix_of_NF_biperm_WF b : 
  WF_Matrix (matrix_of_NF_biperm b).
Proof.
  apply matrix_of_biperm_WF.
Qed.

#[export] Hint Resolve matrix_of_NF_biperm_WF : wf_db.

Lemma uncurry_compose_cap_NF_l_correct (b : NF_biperm) 
  (Hb : WF_NF_biperm b) (padl : nat) 
  (Hpadl : S padl < ncup' b + ncup' b + nid' b) : 
  (@Mmult _ _ (ncup' b + ncup' b + nid' b - 2)
  (matrix_of_NF_biperm b)
  (I (2 ^ padl) ⊗ (⟦ ⊂ ⟧)
    ⊗ I (2 ^ (ncup' b + ncup' b + nid' b - (2 + padl)))))
  [∝@ (2^(ncap' b + ncap' b + nid' b))
    (2^(ncup' b + ncup' b + nid' b - 2))] 
    matrix_of_NF_biperm (uncurry_NF_biperm compose_cap_NF_l b padl).
Proof.
  unfold matrix_of_NF_biperm.
  rewrite ncup_ncup_nid_uncurry_compose_cap_NF_l,
    ncap_ncap_nid_uncurry_compose_cap_NF_l by easy.
  unfold uncurry_NF_biperm.
  apply compose_cap_NF_l_correct; easy + apply Hb.
Qed.

(* Lemma uncurry_compose_cap_NF_l_correct_alt (b : NF_biperm) 
  (Hb : WF_NF_biperm b) (padl : nat) 
  (Hpadl : S padl < ncup' b + ncup' b + nid' b) : 
  (@Mmult _ _ (ncup' b + ncup' b + nid' b - 2)
  (matrix_of_NF_biperm b)
  (I (2 ^ padl) ⊗ (⟦ ⊂ ⟧)
    ⊗ I (2 ^ (ncup' b + ncup' b + nid' b - (2 + padl)))))
  [∝@ (2^(ncap' b + ncap' b + nid' b))
    (2^(ncup' b + ncup' b + nid' b - 2))] 
    matrix_of_NF_biperm (uncurry_NF_biperm compose_cap_NF_l b padl).
Proof.
  unfold matrix_of_NF_biperm.
  rewrite ncup_ncup_nid_uncurry_compose_cap_NF_l,
    ncap_ncap_nid_uncurry_compose_cap_NF_l by easy.
  unfold uncurry_NF_biperm.
  apply compose_cap_NF_l_correct; easy + apply Hb.
Qed. *)

Ltac restore_dims_prop :=
  match goal with 
  |- context[?A [∝] ?B] =>
    let B' := restore_dims_rec B in 
    let A' := restore_dims_rec A in 
    replace A with A' by (unify_matrix_dims restore_dims_tac);
    replace B with B' by (unify_matrix_dims restore_dims_tac)
  end. 

Local Notation NF_insize b := (ncup' b + ncup' b + nid' b).
Local Notation NF_outsize b := (ncap' b + ncap' b + nid' b).

Lemma compose_n_caps_NF_l_correct (b : NF_biperm) 
  (Hb : WF_NF_biperm b) (num_caps : nat) 
  (Hnum_caps : num_caps + num_caps <= ncup' b + ncup' b + nid' b) :
  @Mmult (2^(ncap' b + ncap' b + nid' b) )
    (2^((ncup' b + ncup' b + nid' b))) 
    (2^((ncup' b + ncup' b + nid' b - (num_caps + num_caps)))) 
    (matrix_of_NF_biperm b)
    ((matrix_of_biperm 0 (num_caps + num_caps) (n_m_cup_cap num_caps 0)
    ⊗ (I (2 ^ (ncup' b + ncup' b + nid' b - (num_caps + num_caps))))))
  [∝]
  matrix_of_NF_biperm (compose_n_caps_NF_l b num_caps).
Proof.
  induction num_caps.
  - simpl.
    rewrite matrix_of_biperm_0_0.
    rewrite id_kron.
    restore_dims.
    now rewrite Mmult_1_r by auto with wf_db.
  - cbn [compose_n_caps_NF_l]. 
    rewrite <- uncurry_compose_cap_NF_l_correct by
      ((apply compose_n_caps_NF_l_WF + 
        rewrite ncup_ncup_nid_compose_n_caps_NF_l); easy + lia).
    progress restore_dims.
    rewrite ncup_ncup_nid_compose_n_caps_NF_l, 
      ncap_ncap_nid_compose_n_caps_NF_l by easy + lia.
    rewrite <- IHnum_caps by lia.
    rewrite Mmult_assoc.
    rewrite kron_assoc by auto with wf_db.
    restore_dims.
    rewrite kron_mixed_product' by restore_dims_tac.
    rewrite Mmult_1_l, Mmult_1_r by auto with wf_db.
    restore_dims.
    replace (2 ^ (ncup' b + ncup' b + nid' b - 
      (num_caps + num_caps) - (2 + 0))) 
      with (2 ^ (ncup' b + ncup' b + nid' b - 
      (S num_caps + S num_caps))) by restore_dims_tac.
    rewrite !Nat.mul_1_l.
    apply Mmult_mat_prop_proper; [easy|].
    restore_dims.
    rewrite <- kron_assoc by auto with wf_db.
    now rewrite 2!(n_m_cup_cap_comm _ 0), 2!matrix_of_biperm_n_m_cup_cap_0_l.
Qed.

Definition compose_n_cups_NF_l (b : NF_biperm) (num_cups : nat) : NF_biperm :=
  {|
    lperm' := stack_perms (num_cups + num_cups) (NF_insize b) idn (lperm' b);
    rperm' := rperm' b;
    nid' := nid' b;
    ncup' := num_cups + ncup' b;
    ncap' := ncap' b;
  |}.

Lemma compose_n_cups_NF_l_WF b k (Hb : WF_NF_biperm b) : 
  WF_NF_biperm (compose_n_cups_NF_l b k).
Proof.
  split; [|apply Hb].
  simpl.
  rewrite double_add, <- Nat.add_assoc.
  destruct Hb.
  auto with perm_db.
Qed.

Lemma NF_insize_compose_n_cups_NF_l b k : 
  NF_insize (compose_n_cups_NF_l b k) = k + k + NF_insize b.
Proof.
  simpl; lia.
Qed.

Lemma NF_outsize_compose_n_cups_NF_l b k : 
  NF_outsize (compose_n_cups_NF_l b k) = NF_outsize b.
Proof.
  easy.
Qed.

Lemma matrix_of_WF_NF_biperm (b : NF_biperm) (Hb : WF_NF_biperm b) : 
  matrix_of_NF_biperm b = 
  perm_to_matrix (NF_outsize b) (rperm' b) ×
  (matrix_of_biperm (ncup' b + ncup' b) (ncap' b + ncap' b)
   (n_m_cup_cap (ncup' b) (ncap' b)) ⊗ I (2 ^ (nid' b))) ×
  perm_to_matrix (NF_insize b) (lperm' b).
Proof.
  now rewrite <- matrix_of_realize_NF_biperm'.
Qed.

Lemma matrix_of_stack_biperms' (n0 m0 n1 m1 n01 m01 : nat) (f g : nat -> nat)
  (Hf : bipermutation (n0 + m0) f)
  (Hg : bipermutation (n1 + m1) g)
  (Hn01 : n0 + n1 = n01) (Hm01 : m01 = m0 + m1) :
  matrix_of_biperm n01 m01 (stack_biperms m0 n0 m1 n1 f g) =
  matrix_of_biperm n1 m1 g ⊗ matrix_of_biperm n0 m0 f.
Proof.
  subst.
  now apply matrix_of_stack_biperms.
Qed.





Lemma compose_n_cups_NF_l_correct (b : NF_biperm) 
  (Hb : WF_NF_biperm b) (num_cups : nat) : 
  matrix_of_NF_biperm b × 
  (matrix_of_biperm (num_cups + num_cups) 0 (n_m_cup_cap num_cups 0)
  ⊗ I (2 ^ (NF_insize b))) =
  matrix_of_NF_biperm (compose_n_cups_NF_l b num_cups).
Proof.
  rewrite 2!matrix_of_WF_NF_biperm by 
    (try apply compose_n_cups_NF_l_WF; easy).
  rewrite !Mmult_assoc.
  f_equal.
  simpl.
  rewrite <- (kron_1_l _ _ (perm_to_matrix _ (lperm' b))) by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_l, Mmult_1_r by 
    auto using WF_Matrix_dim_change with wf_db.
  rewrite perm_to_matrix_of_stack_perms' 
    by (apply Hb + lia + auto with perm_db).
  restore_dims.
  rewrite (kron_split_diag (perm_to_matrix _ _) (perm_to_matrix _ _)), 
    (kron_split_diag _ (perm_to_matrix _ _)) by auto with wf_db.
  restore_dims.
  rewrite double_add.
  rewrite (Nat.pow_add_r 2 _ (ncup' b + ncup' b)), 
    (Nat.pow_add_r 2 (ncup' b + ncup' b)), !Nat.mul_assoc, !Nat.mul_1_l.
  rewrite <- !Mmult_assoc.
  f_equal.
  restore_dims.
  rewrite perm_to_matrix_idn, id_kron.
  restore_dims.
  rewrite Mmult_1_r by auto with wf_db.
  rewrite <- id_kron, <- kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product' by restore_dims_tac.
  rewrite Mmult_1_r by auto with wf_db.
  restore_dims.
  f_equal; [restore_dims_tac|].
  rewrite <- (kron_1_l _ _ (matrix_of_biperm _ _ (n_m_cup_cap (ncup' b) _)))
    by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product.
  restore_dims.
  rewrite Mmult_1_l, Mmult_1_r by auto with wf_db.
  rewrite <- matrix_of_stack_biperms by auto with biperm_db.
  change (stack_biperms ?n0 ?n1 0) with (stack_biperms n0 n1 (0 + 0)).
  rewrite (n_m_cup_cap_comm (ncup' b)), (n_m_cup_cap_comm num_cups).
  rewrite <- n_m_cup_cap_plus_plus_decomp.
  rewrite 2!Nat.add_0_r.
  now rewrite n_m_cup_cap_comm, (Nat.add_comm (_ + _)), 
    (Nat.add_comm num_cups (ncup' b)).
Qed.

Definition compose_perm_l_NF_biperm 
  (g : nat -> nat) (f : NF_biperm) : NF_biperm :=
  {|
    lperm' := g ∘ lperm' f;
    rperm' := rperm' f;
    ncup' := ncup' f;
    ncap' := ncap' f;
    nid' := nid' f
  |}.

(* Definition compose_perm_r_NF_biperm 
  (f : NF_biperm) (g : nat -> nat) : NF_biperm :=
  {|
    lperm' := lperm' f;
    rperm' := rperm' f ∘ g;
    ncup' := ncup' f;
    ncap' := ncap' f;
    nid' := nid' f
  |}. *)

Lemma compose_perm_l_NF_biperm_WF f g 
  (Hf : WF_NF_biperm f) (Hg : permutation (NF_insize f) g) :
  WF_NF_biperm (compose_perm_l_NF_biperm g f).
Proof.
  split; [|apply Hf].
  apply permutation_compose; [apply Hg|apply Hf].
Qed.

Lemma matrix_of_compose_perm_l_NF_biperm f g 
  (Hf : WF_NF_biperm f) (Hg : permutation (NF_insize f) g) :
  matrix_of_NF_biperm (compose_perm_l_NF_biperm g f) = 
  matrix_of_NF_biperm f × perm_to_matrix (NF_insize f) g.
Proof.
  rewrite matrix_of_WF_NF_biperm by now apply compose_perm_l_NF_biperm_WF.
  rewrite matrix_of_WF_NF_biperm by easy.
  cbn.
  pose proof Hf as [].
  rewrite perm_to_matrix_compose by auto with perm_db.
  now rewrite <- Mmult_assoc.
Qed.

Definition compose_NF_biperms (g f : NF_biperm) :=
  compose_perm_l_NF_biperm (lperm' g)
  (compose_n_cups_NF_l (
    compose_n_caps_NF_l (compose_perm_l_NF_biperm (rperm' g) f
    ) (ncap' g)
  ) (ncup' g)).

Lemma compose_NF_biperms_WF_step_1(f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) : 
  WF_NF_biperm (compose_perm_l_NF_biperm (rperm' g) f).
Proof.
  apply compose_perm_l_NF_biperm_WF; (apply Hf + rewrite Hfg; apply Hg).
Qed.

Lemma compose_NF_biperms_WF_step_2 (f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) : 
  WF_NF_biperm (compose_n_caps_NF_l (
      compose_perm_l_NF_biperm (rperm' g) f
      ) (ncap' g)
    ).
Proof. 
  apply compose_n_caps_NF_l_WF;
  [cbn; lia|].
  now apply compose_NF_biperms_WF_step_1.
Qed.

Lemma compose_NF_biperms_WF_step_3 (f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) : 
  WF_NF_biperm (compose_n_cups_NF_l (
    compose_n_caps_NF_l (
      compose_perm_l_NF_biperm (rperm' g) f
      ) (ncap' g)
    ) (ncup' g)).
Proof. 
  now apply compose_n_cups_NF_l_WF, compose_NF_biperms_WF_step_2.
Qed.

Lemma compose_NF_biperms_WF_step_4  (f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) : 
  permutation (NF_insize (compose_n_cups_NF_l
    (compose_n_caps_NF_l (compose_perm_l_NF_biperm (rperm' g) f) 
    (ncap' g)) (ncup' g))) 
  (lperm' g).
Proof.
  rewrite NF_insize_compose_n_cups_NF_l.
  rewrite ncup_ncup_nid_compose_n_caps_NF_l by 
    ((now apply compose_NF_biperms_WF_step_1) + cbn; lia).
  eapply permutation_change_dims; [|apply Hg].
  cbn.
  lia.
Qed.

Lemma compose_NF_biperms_WF (f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) : 
  WF_NF_biperm (compose_NF_biperms g f).
Proof.
  unfold compose_NF_biperms.
  apply compose_perm_l_NF_biperm_WF.
  - now apply compose_NF_biperms_WF_step_3.
  - now apply compose_NF_biperms_WF_step_4.
Qed.

Lemma compose_NF_biperms_correct (f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) :
  matrix_of_NF_biperm (compose_NF_biperms g f) [∝]
  @Mmult (2^(NF_outsize f)) (2^(NF_insize f)) (2^(NF_insize g))
   (matrix_of_NF_biperm f) (matrix_of_NF_biperm g).
Proof.
  unfold compose_NF_biperms.
  rewrite matrix_of_compose_perm_l_NF_biperm by 
    (now apply compose_NF_biperms_WF_step_3 + 
     apply compose_NF_biperms_WF_step_4).
  
  rewrite NF_insize_compose_n_cups_NF_l,
    ncup_ncup_nid_compose_n_caps_NF_l by 
    ((now apply compose_NF_biperms_WF_step_1) + cbn; lia).
  cbn.
  rewrite <- compose_n_cups_NF_l_correct by 
    ((now apply compose_NF_biperms_WF_step_2)).
  rewrite <- compose_n_caps_NF_l_correct by
    ((now apply compose_NF_biperms_WF_step_1) + cbn; lia).
  rewrite matrix_of_compose_perm_l_NF_biperm by 
    (apply Hf + rewrite Hfg; apply Hg).
  rewrite ncup_ncup_nid_compose_n_caps_NF_l, 
    ncap_ncap_nid_compose_n_caps_NF_l by 
    ((now apply compose_NF_biperms_WF_step_1) + cbn; lia).
  cbn.
  rewrite double_add, <- (Nat.add_assoc (_ + _)).
  rewrite ncup_ncup_nid_compose_n_caps_NF_l by 
    ((now apply compose_NF_biperms_WF_step_1) + cbn; lia).
  cbn.
  rewrite Hfg, add_sub'.
  rewrite !Mmult_assoc.
  apply Mmult_mat_prop_proper; [easy|].
  rewrite matrix_of_WF_NF_biperm by easy.
  rewrite Mmult_assoc.
  apply Mmult_mat_prop_proper; [easy|].
  rewrite <- Mmult_assoc.
  apply Mmult_mat_prop_proper; [|easy].
  restore_dims_prop.
  rewrite kron_mixed_product, Mmult_1_r by auto_wf.
  rewrite matrix_of_biperm_n_m_cup_cap_split, n_m_cup_cap_comm.
  easy.
Qed.

















































































































































(* Residual proofs: *)



(* Given a NF biperm and two inputs a and b, given another NF biperm 
   with the same underlying relation such that the given inputs end up
   adjacent. Specifically, the following holds:
          Initial State                   Resulting State
    - Both inputs end in the cups,    - a, b get mapped to 0, 1, respectively
      and at the same cup
    - Both inputs end in the cups,    - a, b get mapped to 1, 2, respectively
      in different cups
    - a ends in the cups, b the ids   - a, b get mapped to the last cup and
                                        first id, ncup + ncup - 1 and 
                                        ncup + ncup, respectively
    - b ends in the ids, a the cups   - symemtric of the previous
    - Both inputs end in the ids      - a, b get mapped to ncup + ncup and
                                        1 + ncup + ncup, respectively  *)
Definition make_ins_adj_NF (lperm rperm : nat -> nat) 
  (nid ncup ncap : nat) (a b : nat) (* a, b < ncup + ncup + nid *)



Lemma compose_cap_NF_l_correct {lperm rperm} {nid ncup ncap} 
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  padl padr : ncup + ncup + nid = padl + 2 + padr ->
  matrix_of_biperm (ncup + ncup + nid - 2) (ncap + ncap + nid)
    (realize_NF_biperm 
      (compose_cap_NF_l lperm rperm nid ncup ncap padl padr)) ≡
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid)
    (realize_biperm_data lperm rperm nid ncup ncap)
  × ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^padr)).
Proof.
  intros Hdims.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).

  rewrite matrix_of_realize_biperm_data by auto.
  unfold compose_cap_NF_l.
  bdestruct (lperm padl <? ncup + ncup);
  bdestruct (lperm (S padl) <? ncup + ncup); cbn [andb];
  [bdestruct (lperm padl / 2 =? lperm (S padl) / 2)|..].

  rewrite !(if_dist _ _ _ realize_NF_biperm).
  unfold realize_NF_biperm, uncurry_NF_biperm.
  cbn beta.









Ltac is_C0 x :=
  assert (x = C0) by lca.

Ltac is_C1 x :=
  assert (x = C1) by lca.

Ltac print_Cval x :=
  tryif is_C0 x then idtac "0" else
  tryif is_C1 x then idtac "1" else idtac "X".

Ltac print_LHS_mat :=
  intros;
   (let i := fresh "i" in
	let j := fresh "j" in
    let Hi := fresh "Hi" in
    let Hj := fresh "Hj" in
    intros i j Hi Hj; try solve_end;
     repeat
      (destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
        try solve_end); clear Hi;
     repeat
      (destruct j as [| j]; [  | apply <- Nat.succ_lt_mono in Hj ];
        try solve_end); clear Hj);
  match goal with |- ?x = ?y => simpl x end;
  match goal with
  | |- ?x = _ ?i ?j => idtac i; idtac j; print_Cval x; idtac ""
  end.

Ltac print_LHS_matU :=
  intros;
    (let i := fresh "i" in
  let j := fresh "j" in
    let Hi := fresh "Hi" in
    let Hj := fresh "Hj" in
    intros i j Hi Hj; try solve_end;
      repeat
      (destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
        try solve_end); clear Hi;
      repeat
      (destruct j as [| j]; [  | apply <- Nat.succ_lt_mono in Hj ];
        try solve_end); clear Hj);
  match goal with |- ?x = ?y ?i ?j => autounfold with U_db; simpl; 
    match goal with
    | |- ?x = _ => idtac i; idtac j; print_Cval x; idtac ""
    end
  end.






Lemma swap_block_perm_cap_pullthrough_r padl padm padr
  @Mmult _ _ _
  (perm_to_matrix (padl + 2 + padm + 2 + padr)56 f)
  ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2 ^ (padm + 2 + padr)) ) =
  @Mmult _ _ _
  ((I (2^ padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm f (S padl)) padl)).





  Lemma perm_to_matrix_times_cap_r {n f} (Hf : permutation n f) 
  padl (Hpadl : S padl < n) (Hfpadl : S (f padl) = f (S padl)) :
  @Mmult (2^n) (2^n) (2^(n-2)) (perm_to_matrix n f)
  ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl)))) =
  @Mmult (2^n) (2^(n-2)) (2^(n-2))
  ((I (2^ f padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + f padl))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm f (S padl)) padl)).
Proof.
  pose proof (permutation_is_bounded _ _ Hf) as Hfbdd.
  pose proof (Hfbdd padl ltac:(lia)).
  pose proof (Hfbdd (S padl) Hpadl).
  apply mat_equiv_eq; auto with wf_db.
  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite <- Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits_l by easy.
  rewrite 3!Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits by
    (replace (n-2) with ((n - 1) - 1) by lia;
      apply contract_perm_permutation; try lia;
      auto with perm_db).
  rewrite (f_equal_inv _ (f_to_vec n) 
    (f_to_vec (padl + 2 + (n - (2 + padl)))) ltac:(f_equal; lia)) at 1.
  rewrite (f_equal_inv _ (f_to_vec n) 
    (f_to_vec (f padl + 2 + (n - (2 + f padl)))) ltac:(f_equal; lia)) at 1.
  rewrite (f_equal_inv _ (f_to_vec (n-2)) 
    (f_to_vec (padl + 0 + (n - (2 + padl)))) ltac:(f_equal; lia)) at 1.
  rewrite (f_equal_inv _ (f_to_vec (n-2)) 
    (f_to_vec (f padl + 0 + (n - (2 + f padl)))) ltac:(f_equal; lia)) at 1.
  rewrite !f_to_vec_split'_eq.
  rewrite !(fun x y => kron_transpose' _ _ x y).

  rewrite !(fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z) by
    (now rewrite <- ?Nat.pow_add_r; lia + (f_equal; lia)).
  unfold kron.
  rewrite !Nat.mod_1_r, !Nat.Div0.div_0_l.
  rewrite Cmult_comm.
  symmetry.
  rewrite Cmult_comm, !Cmult_assoc.
  f_equal.
  - rewrite !basis_f_to_vec, <- !Mmult_assoc.
    rewrite !matrix_conj_basis_eq_lt by apply funbool_to_nat_bound.
    unfold I.
    do 4 match goal with
    |- context [funbool_to_nat ?k ?f <? 2 ^ ?k] => 
      replace (funbool_to_nat k f <? 2 ^ k) with true by
      (pose proof (funbool_to_nat_bound k f); bdestructΩ')
    end.
    rewrite 2!Cmult_if_if_1_l, 4!andb_true_r.
    apply f_equal_if; [|easy..].
    apply eq_iff_eq_true.
    rewrite 2!andb_true_iff, !Nat.eqb_eq, <- !funbool_to_nat_eq_iff.
    split.
    + intros [Hhigh Hlow].
      split.
      * intros k Hk.
        bdestruct (perm_inv n f (padl + 2 + k) <? f padl).
        --generalize (Hlow (perm_inv n f (padl + 2 + k)) ltac:(easy)).
          intros ->.
          f_equal.
          unfold contract_perm.
          do 2 simplify_bools_lia_one_kernel.
          rewrite perm_inv_is_rinv_of_permutation
            by easy + lia.
          bdestructΩ'.
        --assert (perm_inv n f (padl + 2 + k) <> padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          assert (perm_inv n f (padl + 2 + k) <> S padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          pose proof (perm_inv_bounded n f (padl + 2 + k)).
          generalize (Hhigh (perm_inv n f (padl + 2 + k) - (padl + 2)) 
            ltac:(lia)).
          rewrite Nat.add_sub_assoc, add_sub' by lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 4 simplify_bools_lia_one_kernel.
          replace (padl + 0 + (perm_inv n f (padl + 2 + k) 
            - (padl + 2)) + 1 + 1) with
            (perm_inv n f (padl + 2 + k)) by lia.
          rewrite perm_inv_is_rinv_of_permutation by easy + lia.
          bdestructΩ'.
      * intros k Hk.
        bdestruct (perm_inv n f k <? padl).
        --generalize (Hlow (perm_inv n f k) ltac:(easy)).
          intros ->.
          f_equal.
          unfold contract_perm.
          do 2 simplify_bools_lia_one_kernel.
          rewrite perm_inv_is_rinv_of_permutation, Hfpadl, HfSpadl 
            by easy + lia.
          bdestructΩ'.
        --assert (perm_inv n f k <> padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          assert (perm_inv n f k <> S padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          pose proof (perm_inv_bounded n f k).
          generalize (Hhigh (perm_inv n f k - (padl + 2)) 
            ltac:(lia)).
          rewrite Nat.add_sub_assoc, add_sub' by lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 4 simplify_bools_lia_one_kernel.
          replace (padl + 0 + (perm_inv n f k
            - (padl + 2)) + 1 + 1) with
            (perm_inv n f k) by lia.
          rewrite perm_inv_is_rinv_of_permutation by easy + lia.
          bdestructΩ'.
    
    
    + intros [Hhigh Hlow].
      split.
      * intros k Hk.
        bdestruct (perm_inv n f (padl + 2 + k) <? f padl).
        --generalize (Hlow (perm_inv n f (padl + 2 + k)) ltac:(easy)).
          intros ->.
          f_equal.
          unfold contract_perm.
          do 2 simplify_bools_lia_one_kernel.
          rewrite perm_inv_is_rinv_of_permutation by easy + lia.
          assert (perm_inv n f (padl + 2 + k) <> padl). 1:{
            rewrite perm_inv_eq_iff by easy + lia.
          }



    
          



  rewrite !(fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z).
  rewrite => kron_mixed_product'.

    )..|].
  





Definition input_swaps n m f :=
  concat (map 
  (fun i => if (m <=? f (m + i)) && (f (m + i) <? m + i) then
    [(f (m + i) - m, i)] else nil)
  (seq 0 n)).

Definition output_swaps (n m : nat) f :=
  concat (map 
  (fun j => if (f j) <? j then
    [(f j, j)] else nil)
  (seq 0 m)).



Definition swap_pair_permutation ain bin aout bout : nat -> nat :=
  fun k => 
  if k =? ain then aout else
  if k =? bin then bout else
  if k <?
  

Fixpoint biperm_of_input_swaps n m (l : list (nat * nat)) :=
  match l with
  | [] => 

  biperm_of_zx_folio


Proposition input_output_swaps_decomp : 
.



(* Lemma permutation_swap_left_ind (P : nat -> (nat -> nat) -> Prop) 
  (Pproper : forall n f g, permutation n f -> permutation n g -> 
    (forall k, k < n -> f k = g k) -> (P n f <-> P n g)) 
  (Pidentity : forall n, P n idn) 
  (Pswap : forall a n f, permutation n f -> P n f -> a < n -> 
    P n (swap_perm )) : 
    forall n f, permutation n f -> P n f. *)


(* Lemma matrix_of_compose_swap_biperm_l padl padr m f 
  (Hf : bipermutation (padl + 2 + padr + m) f)
  (* (Hne : f (m + padl) <> S (m + padl)) *) : 
  mat_equiv (matrix_of_biperm (padr + 2 + padl) m
  (compose_swap_biperm_l' m padl f))
  ((matrix_of_biperm (padr + 0 + padl) m f 
  × perm_to_matrix).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (biperm_compose_perm_r_biperm _ _ f g Hf Hg) as Hfg.
  pose proof (fun i Hi => proj1 (Hfg i Hi)) as Hfgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hfg i Hi))) as Hfgne.
  pose proof (fun i Hi => proj2 (proj2 (Hfg i Hi))) as Hfgeq.

  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite matrix_of_biperm_funbool_conj.

  rewrite 2!Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits by easy.
  rewrite <- Mmult_assoc.
  rewrite matrix_of_biperm_funbool_conj.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true; rewrite 2!number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_funbool_to_nat.
  split.
  - intros H s Hs.
    replace_bool_lia (s <? n + m) true.
    pose proof (Hfbdd s ltac:(lia)).
    replace_bool_lia (f s <? n + m) true.
    replace_bool_lia (n + m - S s <? n) (m <=? s).
    replace_bool_lia (n + m - S (f s) <? n) (m <=? f s).
    bdestruct (m <=? s).
    + pose proof (perm_inv_bounded n g) as Hginvbdd. *)




(* Lemma matrix_of_biperm_compose_perm_r n m f g
  (Hf : bipermutation (m + n) f)
  (Hg : permutation n g) 
  (* (Hne : f (m + padl) <> S (m + padl)) *) : 
  mat_equiv (matrix_of_biperm n m
  (biperm_compose_perm_r m n f g))
  (matrix_of_biperm n m f ×
    perm_to_matrix n g).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (biperm_compose_perm_r_biperm _ _ f g Hf Hg) as Hfg.
  pose proof (fun i Hi => proj1 (Hfg i Hi)) as Hfgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hfg i Hi))) as Hfgne.
  pose proof (fun i Hi => proj2 (proj2 (Hfg i Hi))) as Hfgeq.



  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite matrix_of_biperm_funbool_conj.

  rewrite 2!Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits by easy.
  rewrite <- Mmult_assoc.
  rewrite matrix_of_biperm_funbool_conj.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true; rewrite 2!number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_funbool_to_nat.
  split.
  - intros H s Hs.
    replace_bool_lia (s <? n + m) true.
    pose proof (Hfbdd s ltac:(lia)).
    replace_bool_lia (f s <? n + m) true.
    replace_bool_lia (n + m - S s <? n) (m <=? s).
    replace_bool_lia (n + m - S (f s) <? n) (m <=? f s).
    bdestruct (m <=? s).
    + pose proof (perm_inv_bounded n g) as Hginvbdd.

    
      specialize (H (m + perm_inv n g (n + m - S s))
        ltac:(specialize (Hginvbdd (n + m - S s) ltac:(lia)); lia)).
      revert H.
      pose proof (Hgbdd (n + m - S s) ltac:(lia)).
      pose proof (Hfgbdd (n + m - S (g (n + m - S s))) ltac:(lia)). 
      replace (n + m - S (n + m - S (g (n + m - S s)))) with 
        (g (n + m - S s)) by lia.
      do 3 simplify_bools_lia_one_kernel.
      intros ->.
      unfold biperm_compose_perm_r.
      do 2 simplify_bools_lia_one_kernel.

      bdestructΩ'.

      repeat (bdestruct_one;
      [| lia]).
      repeat (first [bdestruct_one; [lia |] | bdestruct_one; [lia |]]).
      
      revert H.
      replace_bool_lia (s <? n + m) true.
      replace_bool_lia (n + m - S s <? n) (true).


    bdestructΩ'.
    specialize (H ())
  intros Hs.
  apply forall_iff; intros s.
  rewrite impl_iff; intros Hs.
  
  unfold biperm_compose_perm_l.
  bdestructΩ'. *)




(* Lemma matrix_of_biperm_compose_perm_l n m f g
  (Hf : bipermutation (n + m) f)
  (Hg : permutation n g) 
  (* (Hne : f (m + padl) <> S (m + padl)) *) : 
  mat_equiv (matrix_of_biperm n m
  (biperm_compose_perm_r n m f g))
  (matrix_of_biperm n m f ×
    perm_to_matrix n g).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (biperm_compose_perm_l_biperm _ _ f g Hf Hg) as Hfg.
  pose proof (fun i Hi => proj1 (Hfg i Hi)) as Hfgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hfg i Hi))) as Hfgne.
  pose proof (fun i Hi => proj2 (proj2 (Hfg i Hi))) as Hfgeq.

  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite matrix_of_biperm_funbool_conj.
  rewrite 2!Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits by easy.
  rewrite <- Mmult_assoc.
  rewrite matrix_of_biperm_funbool_conj.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true; rewrite 2!number_preserved_iff_all_lt_eq setoid_rewrite testbit_funbool_to_nat.
  split.
  - intros H s Hs.
    replace_bool_lia (s <? n + m) true.
    pose proof (Hfbdd s Hs).
    replace_bool_lia (f s <? n + m) true.
    replace_bool_lia (n + m - S s <? n) (m <=? s).
    replace_bool_lia (n + m - S (f s) <? n) (m <=? f s).
    bdestruct (m <=? s).
    + specialize (H (n + m - S (g (n + m - S s))) ltac:(lia)).
      revert H.
      pose proof (Hgbdd (n + m - S s) ltac:(lia)).
      pose proof (Hfgbdd (n + m - S (g (n + m - S s))) ltac:(lia)). 
      replace (n + m - S (n + m - S (g (n + m - S s)))) with 
        (g (n + m - S s)) by lia.
      do 3 simplify_bools_lia_one_kernel.
      intros ->.
      match goal with
      |- context [n + m - S ?x <? n] => 
        replace_bool_lia (n + m - S x <? n) (m <=? x)
      end.
      evar (x : nat).
      replace (biperm_compose_perm_l n m f g (n+m-S(g(n+m-S s)))) with x.
      2: {
        symmetry.
        unfold biperm_compose_perm_l.
        
        match goal with
        |- context [n + m - S ?x <? n] => 
          replace_bool_lia (n + m - S x <? n) (m <=? x)
        end.
      }
      
      (* specialize  *)
      unfold biperm_compose_perm_l.
      bdestructΩ'.

      repeat (bdestruct_one;
      [| lia]).
      repeat (first [bdestruct_one; [lia |] | bdestruct_one; [lia |]]).
      
      revert H.
      replace_bool_lia (s <? n + m) true.
      replace_bool_lia (n + m - S s <? n) (true).


    bdestructΩ'.
    specialize (H ())
  intros Hs.
  apply forall_iff; intros s.
  rewrite impl_iff; intros Hs.
  
  unfold biperm_compose_perm_l.
  bdestructΩ'. *)



(* Lemma matrix_of_biperm_compose_perm_r n m f g
  (Hf : bipermutation (m + n) f)
  (Hg : permutation n g) 
  (* (Hne : f (m + padl) <> S (m + padl)) *) : 
  mat_equiv (matrix_of_biperm n m
  (biperm_compose_perm_r m n f g))
  (matrix_of_biperm n m f ×
    perm_to_matrix n g).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (biperm_compose_perm_r_biperm _ _ f g Hf Hg) as Hfg.
  pose proof (fun i Hi => proj1 (Hfg i Hi)) as Hfgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hfg i Hi))) as Hfgne.
  pose proof (fun i Hi => proj2 (proj2 (Hfg i Hi))) as Hfgeq.



  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite matrix_of_biperm_funbool_conj.

  rewrite 2!Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits by easy.
  rewrite <- Mmult_assoc.
  rewrite matrix_of_biperm_funbool_conj.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true; rewrite 2!number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_funbool_to_nat.
  split.
  - intros H s Hs.
    replace_bool_lia (s <? n + m) true.
    pose proof (Hfbdd s ltac:(lia)).
    replace_bool_lia (f s <? n + m) true.
    replace_bool_lia (n + m - S s <? n) (m <=? s).
    replace_bool_lia (n + m - S (f s) <? n) (m <=? f s).
    bdestruct (m <=? s).
    + specialize (H (n + m - S (g (n + m - S s))) ltac:(lia)).
      revert H.
      pose proof (Hgbdd (n + m - S s) ltac:(lia)).
      pose proof (Hfgbdd (n + m - S (g (n + m - S s))) ltac:(lia)). 
      replace (n + m - S (n + m - S (g (n + m - S s)))) with 
        (g (n + m - S s)) by lia.
      do 3 simplify_bools_lia_one_kernel.
      intros ->.
      unfold biperm_compose_perm_r.
      do 2 simplify_bools_lia_one_kernel.
      bdestructΩ'.

      repeat (bdestruct_one;
      [| lia]).
      repeat (first [bdestruct_one; [lia |] | bdestruct_one; [lia |]]).
      
      revert H.
      replace_bool_lia (s <? n + m) true.
      replace_bool_lia (n + m - S s <? n) (true).


    bdestructΩ'.
    specialize (H ())
  intros Hs.
  apply forall_iff; intros s.
  rewrite impl_iff; intros Hs.
  
  unfold biperm_compose_perm_l.
  bdestructΩ'. *)




(* Lemma matrix_of_compose_swap_biperm_l padl padr m f 
  (Hf : bipermutation (padl + 0 + padr + m) f)
  (* (Hne : f (m + padl) <> S (m + padl)) *) : 
  mat_equiv (matrix_of_biperm (padr + 2 + padl) m
  (compose_swap_biperm_l (m + padl) f))
  ((matrix_of_biperm (padr + 0 + padl) m f 
  × ((I (2^padr) ⊗ ⟦⨉⟧) ⊗ I (2^padl)))).
Proof.
  
  rewrite !Nat.pow_add_r.
  (* restore_dims. *)
  (* rewrite <- Nat.mul_assoc. *)

  pose proof (Nat.pow_nonzero) as Hnz.
  rewrite kron_I_l, kron_I_r.
  intros i j Hi Hj.
  unfold Mmult.
  rewrite (big_sum_eq_bounded _
  (fun k => if 
    (k =? (j / 2 ^ padl) / 2 ^ 2 * 2 ^ padl + j mod 2 ^ padl) 
      && eqb (Nat.testbit j padl) (Nat.testbit j (S padl))
  then (matrix_of_biperm (padl + 0 + padr) m f i k) else C0)).
  2: {
    intros k Hk.
    rewrite <- andb_if.
    rewrite cup_semantics.
    rewrite <- orb_if, <- 2!andb_if.
    rewrite (if_dist _ _ _ (fun x => 
      Cmult (matrix_of_biperm _ _ _ _ _) x)).
    rewrite Cmult_0_r, Cmult_1_r.
    apply f_equal_if; [|easy + f_equal; lia..].
    rewrite Nat.pow_0_r, Nat.mod_1_r, Nat.eqb_refl, andb_true_r.
    rewrite Nat.div_1_r.
    f_equal.
    - apply eq_iff_eq_true.
      rewrite andb_true_iff.
      rewrite !Nat.eqb_eq.
      split.
      + intros [Hkmod Hkdiv].
        rewrite (Nat.div_mod k (2^padl)) by (apply Hnz;lia).
        lia. 
      + intros ->.
        rewrite Nat.add_comm.
        rewrite Nat.Div0.mod_add, Nat.Div0.mod_mod.
        split; [easy|].
        rewrite Nat.div_add by (apply Hnz;lia).
        rewrite Nat.div_small by (apply Nat.mod_upper_bound, Hnz;lia).
        lia.
    - apply eq_iff_eq_true.
      rewrite orb_true_iff, !Nat.eqb_eq.
      rewrite <- eq_eqb_iff.
      rewrite 2!Nat.testbit_eqb.
      change (2^2) with (2*2).
      rewrite Nat.Div0.mod_mul_r.
      rewrite Nat.Div0.div_div.
      pose proof (Nat.mod_upper_bound (j / 2 ^ padl) 2 ltac:(easy)).
      pose proof (Nat.mod_upper_bound (j / (2 ^ padl * 2)) 2 ltac:(easy)).
      assert (Hrw: (j / 2 ^ padl) mod 2 +
      2 * ((j / (2 ^ padl * 2)) mod 2) = 0 <-> 
      (j / 2 ^ padl) mod 2 = 0 /\ ((j / (2 ^ padl * 2)) mod 2) = 0) by lia.
      rewrite Hrw; clear Hrw.
      assert (Hrw: (j / 2 ^ padl) mod 2 +
      2 * ((j / (2 ^ padl * 2)) mod 2) = 3 <-> 
      (j / 2 ^ padl) mod 2 = 1 /\ ((j / (2 ^ padl * 2)) mod 2) = 1) by lia.
      rewrite Hrw; clear Hrw.
      rewrite eq_iff_eq_true, 2!Nat.eqb_eq.
      rewrite Nat.pow_succ_r by lia.
      rewrite Nat.mul_comm in *.
      generalize dependent ((j / 2^padl) mod 2).
      intros n Hn.
      generalize dependent (j / (2 * 2^padl) mod 2).
      intros n' Hn'.
      lia.
  } 
  rewrite (big_sum_eq_bounded _
  (fun k => if 
    (k =? (j / 2 ^ padl) / 2 ^ 2 * 2 ^ padl + j mod 2 ^ padl) 
    then if eqb (Nat.testbit j padl) (Nat.testbit j (S padl)) 
      && number_preserved (k * 2^m + i) f (padl + 0 + padr + m)
    then C1 else C0 else C0)).
  2: {
    unfold matrix_of_biperm.
    intros k Hk.
    rewrite <- !andb_if, andb_assoc.
    easy.
  } *)



(* Lemma matrix_of_compose_cap_biperm_l padl padr m f 
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
  erewrite mmult_mat_equiv_morph.
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
  unfold number_preserved. *)


(* Lemma number_preserved_compose_cap_l_flipped {padl padr m} {i j} {f} 
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
  bdestruct (padl <=? s). *)











(* Lemma bipermutation_permutation n f : bipermutation n f -> permutation n f.
Proof.
  intros Hbiperm.
  exists f.
  intros k Hk.
  destruct (Hbiperm k Hk) as [? [? ?]].
  auto.
Qed. *)

Fixpoint has_common_below n f g : bool :=
  match n with
  | 0 => false
  | S n' => (f n') && (g n') || has_common_below n' f g
  end.

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



Lemma compose_biperms_helper_bounded cost n m o f g (H: 0 < n + o) : forall to_g val,
  compose_biperms_helper cost n m o f g to_g val < n + o.
Proof.
  induction cost; intros; simpl.
  - assumption.
  - bdestructΩ'.
Qed.

Lemma compose_biperms_bounded n m o f g : 
  perm_bounded (n + o) (compose_biperms n m o f g).
Proof.
  intros; unfold compose_biperms.
  bdestructΩ'; apply compose_biperms_helper_bounded; lia.
Qed.

#[export] Hint Resolve compose_biperms_helper_bounded compose_biperms_bounded : perm_bounded_db.

Lemma compose_biperms_WF n m o f g :
  WF_Perm (n + o) (compose_biperms n m o f g).
Proof.
  intros k Hk.
  unfold compose_biperms.
  bdestructΩ'.
Qed.

#[export] Hint Resolve compose_biperms_WF : WF_Perm_db.


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
(* CORRECTION: The above is *mostly* correct; the actual equation
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

 




















Require QuantumLib.Eigenvectors.



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
  WF_Perm (n + m + (m + o)) 
    (pre_compose_bipermutations cost n m o f g).
Proof.
  unfold pre_compose_bipermutations.
  intros k Hk. 
  destruct cost; 
  replace_bool_lia (n + m + (m + o) <=? k) true; 
  easy.
Qed.

Lemma pre_compose_bipermutations_bounded {n m o : nat}
  {f g : nat -> nat} (Hf : perm_bounded (n + m) f)
  (Hg : perm_bounded (m + o) g) (cost : nat) : 
  perm_bounded (n + m + (m + o)) 
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
    + apply pre_compose_bipermutations_bounded; 
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


  split; [auto with perm_bounded_db|].
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
  end.