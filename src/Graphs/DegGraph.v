Require Import CoreRules. 
Require Import ZXpermFacts.
Require Import BipermAux. 
From QuantumLib Require Import Modulus. 
Import Setoid. 


Import ComposeRules.
Import Modulus. 
Open Scope ZX_scope.
Open Scope prg.
Open Scope nat_scope.

Require Import BigPerm.





(* More general theory: *)


Lemma Nsum_alt_1_sub_1_eq n d (Hn : n <> 0) : 
  big_sum (fun k => if k mod 2 =? 0 then 1 else (n - 1)) (2 * d)
  = d * n.
Proof.
  change (fun k => if k mod 2 =? 0 then 1 else n - 1) with 
    (fun k => (fun (kdiv2 kmod2 : nat) => if kmod2 =? 0 then 1 else n - 1)
      (k / 2) (k mod 2)). 
  rewrite <- big_sum_double_sum.
  rewrite Nsum_constant.
  cbn [big_sum Gplus nat_is_monoid Nat.eqb].
  f_equal; cbn; lia.
Qed.

Lemma Nsum_alt_1_sub_1_eq_total n m (Hn : n <> 0) : 
  big_sum (fun k => if k mod 2 =? 0 then 1 else (n - 1)) m
  = m / 2 * n + (if m mod 2 =? 0 then 0 else 1).
Proof.
  rewrite (Nat.div_mod_eq m 2) at 1.
  rewrite big_sum_sum.
  cbn [Gplus nat_is_monoid].
  rewrite Nsum_alt_1_sub_1_eq by auto.
  f_equal.
  pose proof (Nat.mod_upper_bound m 2 ltac:(lia)).
  bdestruct (m mod 2 =? 0).
  - replace -> (m mod 2).
    reflexivity.
  - replace (m mod 2) with 1 by lia.
    cbn [big_sum].
    rewrite Nat.add_0_r, Nat.mul_comm, Nat.Div0.mod_mul.
    reflexivity.
Qed.

Lemma Nsum_alt_1_sub_1_eq_diag n : 
  big_sum (fun k => if k mod 2 =? 0 then 1 else (n - 1)) (2 * n)
  = n * n.
Proof.
  bdestruct (n =? 0); [subst; reflexivity|].
  now apply Nsum_alt_1_sub_1_eq.
Qed.


Lemma Nsum_index_alt_1_sub_1_eq n d k (Hk : k < d * n) : 
  Nsum_index (2 * d) (fun k => if k mod 2 =? 0 then 1 else (n - 1)) k
  = k / n * 2 + (if k mod n =? 0 then 0 else 1).
Proof.
  revert n Hk; induction d; [lia|]; intros n Hk.
  assert (Hn : n <> 0) by lia.
  assert (HSd : 2 * S d = S (S (2 * d))) by lia.
  rewrite HSd.
  cbn [Nsum_index big_sum Gplus nat_is_monoid].
  pose proof (Nsum_alt_1_sub_1_eq n (S d) Hn) as Hsum.
  rewrite HSd in Hsum.
  cbn [big_sum Gplus nat_is_monoid] in Hsum.
  rewrite mod_2_succ in Hsum.
  rewrite (Nat.mul_comm 2 d) in *.
  rewrite Nat.Div0.mod_mul in *.
  change (1 - 0) with 1 in Hsum.
  cbn [Nat.eqb] in *.
  pose proof Hsum as Hsum'.
  rewrite <- Nat.add_assoc in Hsum'.
  replace (S d * n) with (d * n + n) in Hsum' by lia.
  pose proof (prf_add_cancel_r Hsum' ltac:(lia)) as Hsumn.
  rewrite Hsumn.
  bdestruct (d * n <=? k).
  - replace (k / n) with d by 
      (symmetry; rewrite Kronecker.div_eq_iff by lia; lia).
    bdestruct_one.
    + rewrite if_false; [lia|].
      rewrite Nat.eqb_neq.
      replace k with (d * n + (k - (d * n))) by lia.
      rewrite mod_add_l, Nat.mod_small by lia.
      lia.
    + rewrite if_true; [lia|].
      rewrite Nat.eqb_eq.
      replace k with (d * n) by lia.
      now rewrite Nat.Div0.mod_mul.
  - replace_bool_lia (d * n + 1 <=? k) false.
    now rewrite IHd by lia.
Qed.

Lemma Nsum_offset_alt_1_sub_1_eq n d k (Hk : k < d * n) : 
  Nsum_offset (2 * d) (fun k => if k mod 2 =? 0 then 1 else (n - 1)) k
  = if k mod n =? 0 then 0 else (k mod n - 1).
Proof.
  assert (Hn : n <> 0) by lia.
  pose proof (Nsum_alt_1_sub_1_eq n d Hn) as Hsum.
  unfold Nsum_offset.
  rewrite Nsum_index_alt_1_sub_1_eq by auto.
  rewrite big_sum_sum.
  cbn [Gplus nat_is_monoid].
  rewrite Nat.mul_comm.
  rewrite Nsum_alt_1_sub_1_eq by auto.
  pose proof (Nat.div_mod_eq k n).
  bdestruct (k mod n =? 0);
  cbn [big_sum Gplus nat_is_monoid].
  - lia.
  - rewrite Nat.add_0_r, (Nat.mul_comm 2), Nat.Div0.mod_mul.
    cbn.
    lia.
Qed.



Lemma alt_1_sub_1_perm_eq n d : 
  perm_eq (2 * d) (fun k => if k mod 2 =? 0 then 1 else n - 1)
  ((fun k => if k <? d then 1 else (n - 1)) ∘ kron_comm_perm 2 d).
Proof.
  rewrite kron_comm_perm_defn.
  intros k Hk.
  unfold compose.
  pose proof (Nat.mod_upper_bound k 2 ltac:(lia)).
  bdestruct (k mod 2 =? 0).
  - replace -> (k mod 2). 
    now simplify_bools_moddy_lia_one_kernel.
  - replace (k mod 2) with 1 by lia.
    now simplify_bools_lia_one_kernel.
Qed.

Lemma alt_1_sub_1_kron_comm_perm_eq n d : 
  perm_eq (2 * d) ((fun k => if k mod 2 =? 0 then 1 else n - 1) ∘ 
  kron_comm_perm d 2)
  (fun k => if k <? d then 1 else (n - 1)).
Proof.
  rewrite alt_1_sub_1_perm_eq.
  rewrite Combinators.compose_assoc, kron_comm_perm_pseudo_invol.
  reflexivity.
Qed.

Lemma big_stack_stack_kron_nat_r_prf0 (ns0 ns1 : nat -> nat) n : 
  big_sum (fun k => if k mod 2 =? 0 
    then ns0 (k / 2) else ns1 (k / 2)) (n * 2) =
  big_sum ((fun k => if k <? n then ns0 k else ns1 (k - n))
    ∘ kron_comm_perm 2 n) (2 * n).
Proof.
  rewrite <- Nsum_reorder by auto_perm.
  replace (2 * n) with (n + n) by lia.
  rewrite Nsum_if_lt.
  rewrite <- big_stack_stack_prf.
  apply Nsum_plus.
Qed.

Lemma big_stack_stack_kron_nat_r_prf1 (ms0 ms1 : nat -> nat) n : 
  big_sum ((fun k => if k mod 2 =? 0 
    then ms0 (k / 2) else ms1 (k / 2)) ∘ kron_comm_perm n 2) (n * 2) =
  big_sum (fun k => if k <? n then ms0 k else ms1 (k - n)) (2 * n).
Proof.
  rewrite <- Nsum_reorder by auto_perm.
  rewrite big_stack_stack_kron_nat_r_prf0.
  now rewrite <- Nsum_reorder by auto_perm.
Qed.



Lemma kron_comm_perm_n_2_alts_if_mod2_0_r f g n : 
  perm_eq (n * 2) 
    ((fun k => if k mod 2 =? 0 then f k else g k) ∘ kron_comm_perm n 2)
    (fun k => if k <? n then f (kron_comm_perm n 2 k) 
      else g (kron_comm_perm n 2 k)).
Proof.
  rewrite kron_comm_perm_defn.
  intros k Hk.
  unfold compose.
  rewrite mod_add_l, Nat.mod_small by show_moddy_lt.
  pose proof (Nat.div_small_iff k n ltac:(lia)).
  rewrite kron_comm_perm_defn by auto.
  replace_bool_lia (k / n =? 0) (k <? n).
  reflexivity.
Qed.


  
Lemma kron_comm_perm_n_2_alts_div2_if_mod2_0_r f g n : 
  perm_eq (n * 2) 
    ((fun k => if k mod 2 =? 0 then f (k / 2) else g (k / 2)) 
      ∘ kron_comm_perm n 2)
    (fun k => if k <? n then f k else g (k - n)).
Proof.
  rewrite kron_comm_perm_n_2_alts_if_mod2_0_r.
  intros k Hk.
  rewrite kron_comm_perm_div_r by auto.
  bdestruct (k <? n).
  - now rewrite Nat.mod_small.
  - now rewrite mod_n_to_2n by lia.
Qed.

Lemma big_stack_stack_enlarge_kron_natural_r ns0 ns1 ms0 ms1 
  (zxs0 : forall k, ZX (ns0 k) (ms0 k)) 
  (zxs1 : forall k, ZX (ns1 k) (ms1 k)) n :
  big_stack (fun k => if k mod 2 =? 0 then ns0 (k / 2) else ns1 (k / 2))
    (fun k => if k mod 2 =? 0 then ms0 (k / 2) else ms1 (k / 2))
    (fun k => 
      if k mod 2 =? 0 as a return 
        ZX (if a then ns0 (k / 2) else ns1 (k / 2))
        (if a then ms0 (k / 2) else ms1 (k / 2))
      then zxs0 (k / 2) else zxs1 (k / 2)) (n * 2) ⟷ 
  big_zx_of_permutation_r (n * 2) (kron_comm_perm n 2) _
    (kron_comm_perm_permutation n 2) ∝
  cast _ _ 
    (big_stack_stack_kron_nat_r_prf0 ns0 ns1 n)
    (big_stack_stack_kron_nat_r_prf1 ms0 ms1 n)
  (
    big_zx_of_permutation_l (2 * n) (kron_comm_perm 2 n) _ 
    (kron_comm_perm_permutation 2 n) ⟷
    big_stack (fun k => if k <? n then ns0 k else ns1 (k - n))
      (fun k => if k <? n then ms0 k else ms1 (k - n))
      (fun k => 
      if k <? n as a return 
        ZX (if a then ns0 k else ns1 (k - n))
        (if a then ms0 k else ms1 (k - n))
      then zxs0 k else zxs1 (k - n)) (2 * n)
  ).
Proof.
  rewrite big_zx_of_permutation_r_natural.
  rewrite cast_compose_distribute.
  unshelve (eapply compose_simplify_casted).
  1: {
    apply big_stack_stack_kron_nat_r_prf1.
  }
  - unfold big_zx_of_permutation_r, big_zx_of_permutation_l.
    rewrite 2!cast_contract_eq.
    rewrite cast_zx_of_perm_natural_l.
    symmetry.
    rewrite cast_zx_of_perm_natural_l.
    apply cast_simplify.
    erewrite zx_of_perm_eq_of_perm_eq; [reflexivity|].
    rewrite Nat.mul_comm.
    erewrite enlarge_permutation_perm_eq_to_eq; [reflexivity|..].
    + rewrite kron_comm_perm_inv'_alt. 
      split; auto_perm.
    + rewrite Nat.mul_comm. 
      now rewrite kron_comm_perm_n_2_alts_div2_if_mod2_0_r.
  - rewrite (big_stack_rebound (Nat.mul_comm 2 n)), 2!cast_contract_eq.
    apply big_stack_simplify_casted_abs.
    + now rewrite kron_comm_perm_n_2_alts_div2_if_mod2_0_r.
    + now rewrite kron_comm_perm_n_2_alts_div2_if_mod2_0_r.
    + intros k ? ? Hk.
      apply ZX_prop_by_mat_prop.
      simpl_cast_semantics.
      clear prfn prfm.
      assert ((kron_comm_perm n 2 k mod 2 =? 0) = (k <? n)). 1: {
        apply eq_iff_eq_true.
        rewrite Nat.eqb_eq, Nat.ltb_lt.
        rewrite kron_comm_perm_mod_r by lia.
        apply Nat.div_small_iff; lia.
      }
      unfold compose.
      bdestruct_all.
      * now rewrite kron_comm_perm_div_r, Nat.mod_small by lia.
      * now rewrite kron_comm_perm_div_r, mod_n_to_2n by lia.
Qed.


(* Specific to this graph semantic: *)

Definition wire_to_ordered_edge n k : nat * nat :=
  let i := k / (n - 1) in 
  let j := k mod (n - 1) in 
  if j <? i 
  then (i, j)
  else (i, S j).

Definition ordered_edge_to_wire n ij : nat :=
  if snd ij <? fst ij 
  then fst ij * (n - 1) + snd ij 
  else (fst ij) * (n - 1) + (snd ij - 1).

Lemma wire_to_ordered_edge_to_wire n k (Hk : k < n * (n - 1)) : 
  ordered_edge_to_wire n (wire_to_ordered_edge n k) = k.
Proof.
  unfold wire_to_ordered_edge, ordered_edge_to_wire.
  pose proof (Nat.div_mod_eq k (n - 1)).
  bdestruct_one; cbn; simplify_bools_lia_one_kernel;
  lia.
Qed.

Lemma ordered_edge_to_wire_to_ordered_edge n ij 
  (Hi : fst ij < n) (Hj : snd ij < n) (Hij : fst ij <> snd ij) : 
  wire_to_ordered_edge n (ordered_edge_to_wire n ij) = ij.
Proof.
  unfold ordered_edge_to_wire, wire_to_ordered_edge.
  bdestruct_one;
  rewrite mod_add_l, Nat.div_add_l, Nat.div_small, Nat.mod_small by lia; 
  simplify_bools_lia_one_kernel; 
  destruct ij; 
  cbn [fst snd] in *; f_equal; lia.
Qed.

Lemma wire_to_ordered_edge_spec n k (Hk : k < n * (n - 1)) : 
  fst (wire_to_ordered_edge n k) < n /\
  snd (wire_to_ordered_edge n k) < n /\
  fst (wire_to_ordered_edge n k) <> snd (wire_to_ordered_edge n k). 
Proof.
  assert (2 <= n) by lia.
  unfold wire_to_ordered_edge.
  assert (k / (n - 1) < n) by show_moddy_lt.
  pose proof (Nat.mod_upper_bound k (n - 1) ltac:(lia)).
  bdestruct_one; 
  cbn [fst snd]; lia.
Qed.

Lemma ordered_edge_to_wire_bounded n ij 
  (Hi : fst ij < n) (Hj : snd ij < n) (Hij : fst ij <> snd ij) : 
  ordered_edge_to_wire n ij < n * (n - 1).
Proof.
  unfold ordered_edge_to_wire.
  bdestruct_one; show_moddy_lt.
Qed.

Definition block_to_pairs_perm n := 
  fun k => if n * (n - 1) <=? k then k else
  let ij := wire_to_ordered_edge n k in 
  if fst ij <? snd ij 
  then (* We are the input *)
    (edge_to_idx n ij) * 2 
  else (* We are the output *)
    (edge_to_idx n (snd ij, fst ij)) * 2 + 1.

Definition pairs_to_block_perm n := 
  fun k => if n * (n - 1) <=? k then k else
  let idx := k / 2 in 
  let side := k mod 2 in 
  let ij := idx_to_edge n idx in 
  if side =? 0 then 
    ordered_edge_to_wire n ij
  else
    ordered_edge_to_wire n (snd ij, fst ij).


Lemma block_to_pairs_WF n : 
  WF_Perm (n * (n - 1)) (block_to_pairs_perm n).
Proof.
  intros k Hk.
  unfold block_to_pairs_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma pairs_to_block_WF n : 
  WF_Perm (n * (n - 1)) (pairs_to_block_perm n).
Proof.
  intros k Hk.
  unfold pairs_to_block_perm.
  now simplify_bools_lia_one_kernel.
Qed.

#[export] Hint Resolve block_to_pairs_WF pairs_to_block_WF : WF_Perm_db.


Lemma block_to_pairs_defn n : 
  perm_eq (n * (n - 1)) 
    (block_to_pairs_perm n) 
    (fun k => let ij := wire_to_ordered_edge n k in 
    if fst ij <? snd ij 
    then (edge_to_idx n ij) * 2 
    else (edge_to_idx n (snd ij, fst ij)) * 2 + 1).
Proof.
  intros k Hk.
  unfold block_to_pairs_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma pairs_to_block_defn n : 
  perm_eq (n * (n - 1)) 
    (pairs_to_block_perm n) 
    (fun k => let idx := k / 2 in let side := k mod 2 in 
    let ij := idx_to_edge n idx in 
    if side =? 0 then ordered_edge_to_wire n ij
    else ordered_edge_to_wire n (snd ij, fst ij)).
Proof.
  intros k Hk.
  unfold pairs_to_block_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma block_to_pairs_perm_bounded n : 
  perm_bounded (n * (n - 1))
    (block_to_pairs_perm n).
Proof.
  intros k Hk.
  rewrite block_to_pairs_defn by lia.
  unfold wire_to_ordered_edge.
  assert (k / (n - 1) < n) by show_moddy_lt.
  pose proof (Nat.mod_upper_bound k (n - 1) ltac:(lia)).
  bdestruct_one;
  cbn [fst snd]; simplify_bools_lia_one_kernel.
  - pose proof (edge_to_idx_bounded n (k mod (n - 1), k / (n - 1))
      ltac:(cbn [fst snd]; lia) ltac:(cbn [fst snd]; lia)).
    rewrite <- triangle_number_exact.
    apply (Nat.le_lt_trans _ ((n * (n - 1) / 2 - 1) * 2 + 1)); [|nia].
    apply Nat.add_le_mono_r.
    apply Nat.mul_le_mono_r.
    lia.
  - pose proof (edge_to_idx_bounded n (k / (n - 1), S (k mod (n - 1)))
      ltac:(cbn [fst snd]; lia) ltac:(cbn [fst snd]; lia)).
    rewrite <- triangle_number_exact.
    lia.
Qed.

Lemma pairs_to_block_perm_bounded n : 
  perm_bounded (n * (n - 1))
    (pairs_to_block_perm n).
Proof.
  intros k Hk.
  rewrite pairs_to_block_defn by lia.
  cbn zeta.
  pose proof (idx_to_edge_spec n (k / 2) 
    ltac:(apply Nat.Div0.div_lt_upper_bound; 
      rewrite Nat.mul_comm, triangle_number_exact; lia)).
  bdestruct_one;
  apply ordered_edge_to_wire_bounded; 
  cbn [fst snd]; lia.
Qed.

#[export] Hint Resolve pairs_to_block_perm_bounded
  block_to_pairs_perm_bounded : perm_bounded_db.


Lemma pairs_to_block_to_pairs_inv n : 
  block_to_pairs_perm n ∘ pairs_to_block_perm n = idn.
Proof.
  eq_by_WF_perm_eq (n * (n - 1)).
  rewrite block_to_pairs_defn, pairs_to_block_defn.
  intros k Hk.
  assert (k / 2 < n * (n - 1) / 2) by 
    (apply Nat.Div0.div_lt_upper_bound; 
    rewrite Nat.mul_comm, triangle_number_exact; lia).
  pose proof (idx_to_edge_spec n (k / 2) ltac:(auto)).
  unfold compose.
  bdestruct (k mod 2 =? 0);
  rewrite ordered_edge_to_wire_to_ordered_edge by (cbn [fst snd]; lia);
  cbn [fst snd];
  bdestructΩ'.
  - rewrite idx_to_edge_to_idx by auto.
    pose proof (Nat.div_mod_eq k 2); lia.
  - rewrite <- surjective_pairing.
    rewrite idx_to_edge_to_idx by auto.
    pose proof (Nat.mod_upper_bound k 2).
    pose proof (Nat.div_mod_eq k 2); lia.
Qed.


Lemma pairs_to_block_permutation n : 
  permutation (n * (n - 1)) (pairs_to_block_perm n).
Proof.
  apply permutation_iff_surjective.
  apply surjective_of_injective_and_bounded.
  split; [|auto_perm].
  intros k l Hk Hl.
  intros Heq.
  apply (f_equal (block_to_pairs_perm n)) in Heq.
  pose proof (equal_f (pairs_to_block_to_pairs_inv n) k).
  pose proof (equal_f (pairs_to_block_to_pairs_inv n) l).
  unfold compose in *.
  congruence.
Qed.

#[export] Hint Resolve pairs_to_block_permutation : perm_db.

Lemma pairs_to_block_perm_inv n : 
  perm_eq (n * (n - 1)) 
    (perm_inv (n * (n - 1)) (pairs_to_block_perm n))
    (block_to_pairs_perm n).
Proof.
  rewrite <- (compose_idn_l (perm_inv _ _)).
  rewrite compose_perm_inv_r by auto_perm.
  now rewrite pairs_to_block_to_pairs_inv.
Qed.

Lemma block_to_pairs_permutation n : 
  permutation (n * (n - 1)) (block_to_pairs_perm n).
Proof.
  rewrite <- pairs_to_block_perm_inv.
  auto_perm.
Qed.

#[export] Hint Resolve block_to_pairs_permutation : perm_db.

Lemma block_to_pairs_perm_inv n : 
  perm_eq (n * (n - 1)) 
    (perm_inv (n * (n - 1)) (block_to_pairs_perm n))
    (pairs_to_block_perm n).
Proof.
  rewrite perm_inv_perm_eq_iff by auto_perm.
  now rewrite pairs_to_block_perm_inv.
Qed.

Lemma block_to_pairs_to_block_inv n : 
  pairs_to_block_perm n ∘ block_to_pairs_perm n = idn.
Proof.
  eq_by_WF_perm_eq (n * (n - 1)).
  rewrite <- block_to_pairs_perm_inv.
  auto_perm.
Qed.

(* FIXME: Move *)
Lemma pairs_to_block_perm_inv' n : 
  perm_inv' (n * (n - 1)) (pairs_to_block_perm n) = 
  block_to_pairs_perm n.
Proof.
  eq_by_WF_perm_eq (n * (n - 1)).
  rewrite perm_inv'_eq.
  apply pairs_to_block_perm_inv.
Qed.

Lemma block_to_pairs_perm_inv' n : 
  perm_inv' (n * (n - 1)) (block_to_pairs_perm n) = 
  pairs_to_block_perm n.
Proof.
  eq_by_WF_perm_eq (n * (n - 1)).
  rewrite perm_inv'_eq.
  apply block_to_pairs_perm_inv.
Qed.






Definition pairs_perm n f := 
  fun k => if n * (n - 1) / 2 <=? k then k else
  let ij := idx_to_edge n k in
  if f (fst ij) <? f (snd ij) then
    edge_to_idx n (f (fst ij), f (snd ij))
  else 
    edge_to_idx n (f (snd ij), f (fst ij)).

Lemma pairs_perm_WF n f : 
  WF_Perm (n * (n - 1) / 2) (pairs_perm n f).
Proof.
  intros k Hk;
  unfold pairs_perm;
  now simplify_bools_lia_one_kernel.
Qed.

#[export] Hint Resolve pairs_perm_WF : WF_Perm_db.

Lemma pairs_perm_defn n f : 
  perm_eq (n * (n - 1) / 2) (pairs_perm n f) 
  (fun k => let ij := idx_to_edge n k in
    if f (fst ij) <? f (snd ij) 
    then edge_to_idx n (f (fst ij), f (snd ij))
    else edge_to_idx n (f (snd ij), f (fst ij))).
Proof.
  intros k Hk;
  unfold pairs_perm;
  now simplify_bools_lia_one_kernel.
Qed.

Add Parametric Morphism n : (pairs_perm n) with signature
  perm_eq n ==> eq as pairs_perm_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  eq_by_WF_perm_eq _.
  rewrite 2!pairs_perm_defn.
  intros k Hk.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  now rewrite 2!Hfg by lia.
Qed.

Lemma pairs_perm_bounded n f (Hf : permutation n f) : 
  perm_bounded (n * (n - 1) / 2) (pairs_perm n f).
Proof.
  intros k Hk.
  rewrite pairs_perm_defn by auto.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  assert (f (fst (idx_to_edge n k)) <> f (snd (idx_to_edge n k)))
    by (intros Heq; apply (permutation_is_injective n f Hf) in Heq; lia).
  bdestruct_one; apply edge_to_idx_bounded; cbn [fst snd]; auto_perm.
Qed.

#[export] Hint Resolve pairs_perm_bounded : perm_bounded_db.

Lemma pairs_perm_compose n f g (Hf : permutation n f) (Hg : permutation n g) :
  pairs_perm n f ∘ pairs_perm n g = pairs_perm n (f ∘ g).
Proof.
  eq_by_WF_perm_eq (n * (n - 1) / 2).
  rewrite 3!pairs_perm_defn.
  intros k Hk.
  cbv delta [compose] beta.
  pose proof (idx_to_edge_spec n k Hk).
  assert (Hne : g (fst (idx_to_edge n k)) <> g (snd (idx_to_edge n k)))
    by (intros Heq; apply (permutation_is_injective n g Hg) in Heq; lia).
  set (ij := idx_to_edge n k) in *.
  cbn zeta.
  bdestruct (g (fst ij) <? g (snd ij)).
  - rewrite edge_to_idx_to_edge; cbn [fst snd]; auto_perm.
  - rewrite edge_to_idx_to_edge; cbn [fst snd]; auto_perm.
    assert (f (g (fst ij)) <> f (g (snd ij)))
    by (intros Heq; apply (permutation_is_injective n f Hf) in Heq; auto_perm).
    bdestruct_all; reflexivity + lia.
Qed.

Lemma pairs_perm_idn n : 
  pairs_perm n idn = idn.
Proof.
  eq_by_WF_perm_eq (n * (n - 1) / 2).
  rewrite pairs_perm_defn.
  intros k Hk.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  rewrite <- surjective_pairing, idx_to_edge_to_idx by lia.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite pairs_perm_compose 
  pairs_perm_idn
  using solve [auto_perm] : perm_cleanup_db.

Lemma pairs_perm_permutation n f (Hf : permutation n f) : 
  permutation (n * (n - 1) / 2) (pairs_perm n f).
Proof.
  rewrite permutation_defn.
  exists (pairs_perm n (perm_inv n f)).
  repeat split; [auto_perm..| |];
  rewrite pairs_perm_compose by auto_perm;
  [rewrite perm_inv_rinv_of_permutation by auto|
  rewrite perm_inv_linv_of_permutation by auto];
  now rewrite pairs_perm_idn.
Qed.

#[export] Hint Resolve pairs_perm_permutation : perm_db.

Lemma pairs_perm_inv n f (Hf : permutation n f) : 
  perm_eq (n * (n - 1) / 2) (perm_inv (n * (n - 1) / 2) (pairs_perm n f))
  (pairs_perm n (perm_inv n f)).
Proof.
  perm_eq_by_inv_inj (pairs_perm n f) (n * (n - 1) / 2).
Qed.

#[export] Hint Rewrite pairs_perm_inv
  using solve [auto_perm] : perm_inv_db.

Lemma pairs_perm_inv' n f (Hf : permutation n f) : 
  perm_inv' (n * (n - 1) / 2) (pairs_perm n f) = 
  pairs_perm n (perm_inv' n f).
Proof.
  eq_by_WF_perm_eq _.
  rewrite 2!perm_inv'_eq, pairs_perm_inv; auto_perm.
Qed.

#[export] Hint Rewrite pairs_perm_inv'
  using solve [auto_perm] : perm_inv_db.


(* Definition pairs_perm_r n f := 
  fun k => if n * (n - 1) / 2 <=? k then k else
  let ij := idx_to_edge n k in
  if fst ij <? f (snd ij) then
    edge_to_idx n (fst ij, f (snd ij))
  else 
    edge_to_idx n (f (snd ij), fst ij).

Lemma pairs_perm_r_WF n f : 
  WF_Perm (n * (n - 1) / 2) (pairs_perm_r n f).
Proof.
  intros k Hk;
  unfold pairs_perm_r;
  now simplify_bools_lia_one_kernel.
Qed.

#[export] Hint Resolve pairs_perm_r_WF : WF_Perm_db.

Lemma pairs_perm_r_defn n f : 
  perm_eq (n * (n - 1) / 2) (pairs_perm_r n f) 
  (fun k => let ij := idx_to_edge n k in
    if f (fst ij) <? snd ij 
    then edge_to_idx n (f (fst ij), snd ij)
    else edge_to_idx n (snd ij, f (fst ij))).
Proof.
  intros k Hk;
  unfold pairs_perm_r;
  now simplify_bools_lia_one_kernel.
Qed.

Add Parametric Morphism n : (pairs_perm_r n) with signature
  perm_eq n ==> eq as pairs_perm_r_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  eq_by_WF_perm_eq _.
  rewrite 2!pairs_perm_r_defn.
  intros k Hk.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  now rewrite Hfg by lia.
Qed.

Lemma pairs_perm_r_bounded n f (Hf : permutation n f) : 
  perm_bounded (n * (n - 1) / 2) (pairs_perm_r n f).
Proof.
  intros k Hk.
  rewrite pairs_perm_r_defn by auto.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  (* assert (f (fst (idx_to_edge n k)) <> f (snd (idx_to_edge n k)))
    by (intros Heq; apply (permutation_is_injective n f Hf) in Heq; lia). *)
  bdestruct_one; apply edge_to_idx_bounded; cbn [fst snd]; auto_perm.
Qed.

#[export] Hint Resolve pairs_perm_bounded : perm_bounded_db.

Lemma pairs_perm_compose n f g (Hf : permutation n f) (Hg : permutation n g) :
  pairs_perm n f ∘ pairs_perm n g = pairs_perm n (f ∘ g).
Proof.
  eq_by_WF_perm_eq (n * (n - 1) / 2).
  rewrite 3!pairs_perm_defn.
  intros k Hk.
  cbv delta [compose] beta.
  pose proof (idx_to_edge_spec n k Hk).
  assert (Hne : g (fst (idx_to_edge n k)) <> g (snd (idx_to_edge n k)))
    by (intros Heq; apply (permutation_is_injective n g Hg) in Heq; lia).
  set (ij := idx_to_edge n k) in *.
  cbn zeta.
  bdestruct (g (fst ij) <? g (snd ij)).
  - rewrite edge_to_idx_to_edge; cbn [fst snd]; auto_perm.
  - rewrite edge_to_idx_to_edge; cbn [fst snd]; auto_perm.
    assert (f (g (fst ij)) <> f (g (snd ij)))
    by (intros Heq; apply (permutation_is_injective n f Hf) in Heq; auto_perm).
    bdestruct_all; reflexivity + lia.
Qed.

Lemma pairs_perm_idn n : 
  pairs_perm n idn = idn.
Proof.
  eq_by_WF_perm_eq (n * (n - 1) / 2).
  rewrite pairs_perm_defn.
  intros k Hk.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  rewrite <- surjective_pairing, idx_to_edge_to_idx by lia.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite pairs_perm_compose 
  pairs_perm_idn
  using solve [auto_perm] : perm_cleanup_db.

Lemma pairs_perm_permutation n f (Hf : permutation n f) : 
  permutation (n * (n - 1) / 2) (pairs_perm n f).
Proof.
  rewrite permutation_defn.
  exists (pairs_perm n (perm_inv n f)).
  repeat split; [auto_perm..| |];
  rewrite pairs_perm_compose by auto_perm;
  [rewrite perm_inv_rinv_of_permutation by auto|
  rewrite perm_inv_linv_of_permutation by auto];
  now rewrite pairs_perm_idn.
Qed.

#[export] Hint Resolve pairs_perm_permutation : perm_db.

Lemma pairs_perm_inv n f (Hf : permutation n f) : 
  perm_eq (n * (n - 1) / 2) (perm_inv (n * (n - 1) / 2) (pairs_perm n f))
  (pairs_perm n (perm_inv n f)).
Proof.
  perm_eq_by_inv_inj (pairs_perm n f) (n * (n - 1) / 2).
Qed.

#[export] Hint Rewrite pairs_perm_inv
  using solve [auto_perm] : perm_inv_db.

Lemma pairs_perm_inv' n f (Hf : permutation n f) : 
  perm_inv' (n * (n - 1) / 2) (pairs_perm n f) = 
  pairs_perm n (perm_inv' n f).
Proof.
  eq_by_WF_perm_eq _.
  rewrite 2!perm_inv'_eq, pairs_perm_inv; auto_perm.
Qed.

#[export] Hint Rewrite pairs_perm_inv'
  using solve [auto_perm] : perm_inv_db. *)





Definition reps_to_front_perm n :=
  fun k => if n * n <=? k then k else
  if k mod n =? 0 (* is in front of its section *) 
  then k / n 
  else k + n - S (k / n).

Definition reps_from_front_perm n :=
  fun k => if n * n <=? k then k else
  if k <? n (* k / m =? 0 *)
  then n * (k mod n) 
  else k - (n - S ((k - n) / (n - 1))).

Lemma reps_to_front_perm_WF n : WF_Perm (n * n) (reps_to_front_perm n).
Proof. intros k Hk. unfold reps_to_front_perm. bdestructΩ'. Qed.

Lemma reps_from_front_perm_WF n : WF_Perm (n * n) (reps_from_front_perm n).
Proof. intros k Hk. unfold reps_from_front_perm. bdestructΩ'. Qed.

#[export] Hint Resolve reps_to_front_perm_WF 
  reps_from_front_perm_WF : WF_Perm_db. 

Lemma reps_to_front_perm_defn n : 
  perm_eq (n * n)
    (reps_to_front_perm n)
    (fun k => if k mod n =? 0 then k / n else k + n - S (k / n)).
Proof.
  intros k Hk.
  unfold reps_to_front_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma reps_from_front_perm_defn n : 
  perm_eq (n * n)
    (reps_from_front_perm n)
    (fun k => if k <? n then n * (k mod n) else k - (n - S ((k - n) / (n - 1)))).
Proof.
  intros k Hk.
  unfold reps_from_front_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma reps_to_front_perm_bounded n : 
  perm_bounded (n * n) (reps_to_front_perm n).
Proof.
  intros k Hk.
  rewrite reps_to_front_perm_defn by auto.
  bdestruct_one.
  - show_moddy_lt.
  - bdestruct (k <? n * (n - 1)); [lia|].
    enough (k / n >= (n - 1)) by lia.
    apply Nat.div_le_lower_bound; lia.
Qed.

Lemma reps_from_front_perm_bounded n : 
  perm_bounded (n * n) (reps_from_front_perm n).
Proof.
  intros k Hk.
  rewrite reps_from_front_perm_defn by auto.
  bdestruct_one.
  - show_moddy_lt.
  - lia.
Qed.

#[export] Hint Resolve reps_to_front_perm_bounded
  reps_from_front_perm_bounded : perm_bounded_db.





Lemma block_to_pairs_perm_succ n : 
  perm_eq (S n * (S n - 1))
    (block_to_pairs_perm (S n))
    (stack_perms (n * 2) (n * (n - 1))
    (kron_comm_perm n 2) 
    (block_to_pairs_perm n)
    ∘ stack_perms n (n * n) idn 
      ((enlarge_permutation (2 * n) (kron_comm_perm n 2)
      (fun k => if k mod 2 =? 0 then 1 else (n - 1))))).
Proof.
  pose proof (Nsum_alt_1_sub_1_eq_diag n) as Haltsum.
  rewrite 2!block_to_pairs_defn, kron_comm_perm_defn at 1.
  etransitivity;
  [|symmetry; apply compose_perm_eq_proper_l;
  [eapply perm_eq_dim_change_if_nonzero;
  [apply (stack_perms_defn (n * 2) (n * (n - 1)))|nia]|
  split; [|
  eapply perm_eq_dim_change_if_nonzero;
  [rewrite <- Haltsum, enlarge_permutation_defn, Haltsum;
    apply (stack_perms_defn n (n * n))|lia]];
  rewrite <- Haltsum; auto_perm]].
  intros k Hk.
  assert (Hn : n <> 0) by lia.
  change ((?f ∘ ?g) k) with ((f ∘ idn) (g k)).
  cbv beta.
  bdestruct (k <? n).
  - cbv delta [compose] beta. 
    replace_bool_lia (k <? n * 2) true.
    unfold wire_to_ordered_edge.
    rewrite 2!Nat.mod_small, 2!Nat.div_small by lia.
    cbn [Nat.ltb Nat.leb fst snd].
    simplify_bools_lia_one_kernel.
    rewrite edge_to_idx_succ by (cbn; lia).
    cbn [fst snd].
    rewrite Nat.eqb_refl.
    lia.
  - rewrite kron_comm_perm_inv'_alt.
    rewrite Nsum_index_alt_1_sub_1_eq, Nsum_offset_alt_1_sub_1_eq by lia.
    assert (k - n < n * n) by lia.
    assert ((k - n) / n * 2 + (if (k - n) mod n =? 0 then 0 else 1) < 2 * n) 
      by (bdestruct_one; show_moddy_lt).
    erewrite (big_sum_eq_bounded);
    [|eapply perm_eq_mono; [|apply alt_1_sub_1_kron_comm_perm_eq]; 
      apply Nat.lt_le_incl, kron_comm_perm_bounded; auto].
    rewrite kron_comm_perm_defn by auto.
    rewrite mod_add_l, Nat.div_add_l by lia.
    rewrite (Nat.mod_small (if _ : bool then _ else _)) by (bdestructΩ').
    rewrite (Nat.div_small (if _ : bool then _ else _)) by (bdestructΩ').
    rewrite div_sub_n_r, Nat.add_0_r in *.
    rewrite mod_sub_n_r in * by lia.
    assert (k / n < S n) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (k / n <> 0) by (rewrite Nat.div_small_iff; lia).
    bdestruct (k mod n =? 0).
    + rewrite Nat.add_0_l, Nat.add_0_r.
      erewrite (big_sum_eq_bounded _ (fun _ => 1)) 
        by (intros ? ?; bdestructΩ').
      rewrite Nsum_1.
      cbv delta [compose] beta.
      replace_bool_lia (k / n - 1 + n <? n * 2) true.
      rewrite mod_add_n_r, div_add_n_r by auto. 
      rewrite Nat.mod_small, (Nat.div_small (_ - _)) by lia.
      cbv delta [wire_to_ordered_edge] beta.
      replace (S n - 1) with n by lia.
      replace -> (k mod n).
      cbn zeta.
      replace_bool_lia (0 <? k / n) true.
      cbn [fst snd Nat.ltb Nat.leb].
      rewrite edge_to_idx_succ by (cbn; lia).
      reflexivity.
    + rewrite Nat.mul_1_l.
      rewrite (big_sum_if_lt n _ (fun _ => 1) (fun _ => n - 1)).
      rewrite Nsum_1, Nsum_constant.
      change ((?x + ?y)%G) with (x + y).
      cbv delta [compose] beta.
      replace (n + (k / n - 1) * (n - 1) + 
        (k mod n - 1) + n) with 
        ((k / n - 1) * (n - 1) + 
        (k mod n - 1) + n * 2) by lia.
      replace ((k / n - 1) * (n - 1) + 
        (k mod n - 1) + n * 2 <? n * 2) with false 
        by (generalize ((k / n - 1) * (n - 1)); intros; bdestructΩ').
      rewrite Nat.add_sub.
      cbv delta [wire_to_ordered_edge] beta.
      pose proof (Nat.mod_upper_bound k n Hn).
      replace (S n - 1) with n by lia.
      rewrite Nat.div_add_l, mod_add_l, (Nat.mod_small (_ - _)), 
        (Nat.div_small (_ - _)), Nat.add_0_r by lia.
      lazy zeta.
      replace_bool_lia (k mod n - 1 <? k / n - 1) (k mod n <? k / n).
      bdestruct_one; cbn [fst snd]; do 2 simplify_bools_lia_one_kernel; 
      rewrite edge_to_idx_succ by (cbn; lia);
      cbn [fst snd]; simplify_bools_lia_one_kernel; [lia|].
      replace (S (k mod n - 1)) with (k mod n - 0) by lia.
      lia.
Qed.



Lemma pairs_to_block_perm_pullthrough_l n f (Hf : permutation n f) : 
  tensor_perms n (n - 1) f idn ∘ pairs_to_block_perm n =
  big_stack_perms n (fun _ => (n - 1)) (fun k => contract_perm 
  (perm_inv n f) k) ∘ 
  pairs_to_block_perm n ∘ 
  tensor_perms (n * (n - 1) / 2) 2
    (pairs_perm n f) idn ∘
  big_stack_perms (n * (n - 1) / 2) (fun _ => 2)
    (fun k => let ij := idx_to_edge n k in 
    if f (snd ij) <? f (fst ij) then 
    swap_2_perm else idn).
Proof.
  pose proof (triangle_number_exact n) as Htri.
  pose proof (Nsum_constant (n - 1) n) as Hsum.
  pose proof (Nsum_constant 2 (n * (n - 1) / 2)) as Hsum2.
  eq_by_WF_perm_eq (n * (n - 1));
  [rewrite !Combinators.compose_assoc; 
    apply compose_WF_Perm; [rewrite <- Hsum; auto_perm|];
    apply compose_WF_Perm; [auto_perm|];
    apply compose_WF_Perm; [auto_perm|];
    rewrite <- Htri, <- Hsum2 at 1; auto_perm|].
  rewrite tensor_perms_defn, pairs_to_block_defn at 1.
  symmetry.
  assert (Hstack2 : permutation (n * (n - 1))
    (big_stack_perms (n * (n - 1) / 2) (fun _ => 2)
    (fun k => let ij := idx_to_edge n k in
     if f (snd ij) <? f (fst ij) then swap_2_perm else idn))).
  1: {
    eapply permutation_change_dims;
    [|apply big_stack_perms_permutation;
      intros k Hk; cbn zeta; bdestruct_one; auto_perm].
    lia.
    }
  rewrite big_stack_perms_constant_alt, pairs_to_block_defn.
  rewrite <- Htri at 1.
  rewrite <- Htri in Hstack2 at 1.
  rewrite tensor_perms_defn at 1.
  rewrite big_stack_perms_constant_alt.
  rewrite Htri.
  intros k Hk.
  unfold compose.
  rewrite mod_add_l, Nat.Div0.mod_mod, Nat.div_add_l, 
    mod_div, Nat.add_0_r by lia.
  assert (Hk' : k / 2 < n * (n - 1) / 2) 
    by (apply Nat.Div0.div_lt_upper_bound; lia).
  pose proof (idx_to_edge_spec _ _ Hk').
  set (ij := idx_to_edge n (k / 2)) in *.
  assert (f (fst ij) <> f (snd ij))
    by (intros Heq; apply (permutation_is_injective n f Hf) in Heq; lia).
  bdestruct (f (fst ij) <? f (snd ij)).
  - replace_bool_lia (f (snd ij) <? f (fst ij)) false.
    rewrite (Nat.mul_comm (k / 2) 2).
    rewrite <- (Nat.div_mod_eq k 2). 
    rewrite pairs_perm_defn by auto.
    fold ij.
    cbn zeta.
    (* unfold ordered_edge_to_wire. *)
    replace_bool_lia (f (fst ij) <? f (snd ij)) true.
    rewrite edge_to_idx_to_edge by (cbn [fst snd]; auto_perm).
    unfold ordered_edge_to_wire.
    cbn [fst snd].
    replace_bool_lia (f (fst ij) <? f (snd ij)) true.
    replace_bool_lia (f (snd ij) <? f (fst ij)) false.
    replace_bool_lia (snd ij <? fst ij) false.
    replace_bool_lia (fst ij <? snd ij) true.
    bdestruct (k mod 2 =? 0).
    + pose proof (permutation_is_bounded n f Hf) as Hfbdd.
      pose proof (Hfbdd (fst ij) ltac:(lia)).
      pose proof (Hfbdd (snd ij) ltac:(lia)).
      rewrite 2!mod_add_l, 2!Nat.div_add_l, 
        2!(Nat.div_small (_ - _)), 2!(Nat.mod_small (_ - _)), 
        2!Nat.add_0_r by lia.
      unfold contract_perm.
      rewrite Nat.sub_add by lia.
      rewrite 2!perm_inv_is_linv_of_permutation by auto_perm.
      bdestruct_all; lia.
    + pose proof (permutation_is_bounded n f Hf) as Hfbdd.
      pose proof (Hfbdd (fst ij) ltac:(lia)).
      pose proof (Hfbdd (snd ij) ltac:(lia)).
      rewrite 2!mod_add_l, 2!Nat.div_add_l,
        2!Nat.div_small, 2!Nat.mod_small, 
        2!Nat.add_0_r by lia.
      unfold contract_perm.
      rewrite 2!perm_inv_is_linv_of_permutation by auto_perm.
      bdestruct_all; lia.
  - replace_bool_lia (f (snd ij) <? f (fst ij)) true.
    rewrite mod_add_l, Nat.div_add_l by lia.
    rewrite <- even_eqb.
    pose proof (Nat.mod_upper_bound k 2 ltac:(lia)).
    rewrite (Nat.div_small (swap_2_perm _)), Nat.add_0_r by auto_perm.
     
    rewrite pairs_perm_defn by auto.
    fold ij.
    cbn zeta.
    (* unfold ordered_edge_to_wire. *)
    replace_bool_lia (f (fst ij) <? f (snd ij)) false.
    rewrite edge_to_idx_to_edge by (cbn [fst snd]; auto_perm).
    unfold ordered_edge_to_wire.
    cbn [fst snd].
    replace_bool_lia (f (fst ij) <? f (snd ij)) false.
    replace_bool_lia (f (snd ij) <? f (fst ij)) true.
    replace_bool_lia (snd ij <? fst ij) false.
    replace_bool_lia (fst ij <? snd ij) true.
    bdestruct (k mod 2 =? 0).
    + replace (k mod 2) with 0 by auto.
      change (swap_2_perm 0) with 1.
      cbn [Nat.even].
      pose proof (permutation_is_bounded n f Hf) as Hfbdd.
      pose proof (Hfbdd (fst ij) ltac:(lia)).
      pose proof (Hfbdd (snd ij) ltac:(lia)).
      rewrite 2!mod_add_l, 2!Nat.div_add_l, 
        2!(Nat.div_small), 2!(Nat.mod_small), 
        2!Nat.add_0_r by lia.
      unfold contract_perm.
      rewrite 2!perm_inv_is_linv_of_permutation by auto_perm.
      bdestruct_all; lia.
    + replace (k mod 2) with 1 by lia.
      change (swap_2_perm 1) with 0.
      cbn [Nat.even].
      pose proof (permutation_is_bounded n f Hf) as Hfbdd.
      pose proof (Hfbdd (fst ij) ltac:(lia)).
      pose proof (Hfbdd (snd ij) ltac:(lia)).
      rewrite 2!mod_add_l, 2!Nat.div_add_l,
        2!Nat.div_small, 2!Nat.mod_small, 
        2!Nat.add_0_r by lia.
      unfold contract_perm.
      rewrite Nat.sub_add by lia.
      rewrite 2!perm_inv_is_linv_of_permutation by auto_perm.
      bdestruct_all; lia.
Qed.

(* Notation "'ZXif' b 'then' zx0 'else' zx1" :=
  (if b as a ) *)






Lemma ZX_complete_stack_prf_1 n : 
  n = big_sum (fun _ => 1) n.
Proof.
  rewrite big_sum_constant, times_n_nat; lia.
Qed.

Lemma ZX_complete_stack_prf_2 n : 
  n * (n - 1) = big_sum (fun _ => n - 1) n.
Proof.
  rewrite big_sum_constant, times_n_nat; lia.
Qed.

Definition ZX_complete_stack n (αs : nat -> R) (color : nat -> bool) : 
  ZX n (n * (n - 1)) := 
  cast _ _ (ZX_complete_stack_prf_1 n) (ZX_complete_stack_prf_2 n) 
    (big_stack (fun _ => 1) (fun _ => n - 1)
      (fun k => b2ZX (color k) 1 (n - 1) (αs k)) n).

Definition ZX_complete_perm n : ZX (n * (n - 1)) ((n * (n - 1) / 2) * 2) :=
  cast _ _ eq_refl (triangle_number_exact n)
    (zx_of_perm (n * (n - 1)) (pairs_to_block_perm n)).

Lemma ZX_complete_connections_prf_1 n : 
  ((n * (n - 1) / 2) * 2) = big_sum (fun _ => 2) (n * (n - 1) / 2).
Proof.
  rewrite big_sum_constant, times_n_nat; lia.
Qed.

Lemma ZX_complete_connections_prf_2 n : 
  0 = big_sum (fun _ => 0) (n * (n - 1) / 2).
Proof.
  now rewrite big_sum_0.
Qed.

Definition ZX_complete_connections n (deg : nat * nat -> nat) 
  (color : nat -> bool) : ZX ((n * (n - 1) / 2) * 2) 0 :=
  cast _ _ (ZX_complete_connections_prf_1 n)
    (ZX_complete_connections_prf_2 n)
    (big_stack (fun _ => 2) (fun _ => 0)
      (fun k => 
        let ij := idx_to_edge n k in 
        (b2ZX (color (fst ij)) 1 (deg ij) 0) ↕
        (b2ZX (color (snd ij)) 1 (deg ij) 0) ⟷
        n_cup (deg ij)
        )
      (n * (n - 1) / 2)).



Definition ZX_connections_stack n (deg : nat * nat -> nat)
  (color : nat -> bool) : 
  ZX ((n * (n - 1) / 2) * 2) (big_sum (
    Nat.double ∘ deg ∘ (fun k => idx_to_edge n k)) 
    (n * (n - 1) / 2)) :=
  cast _ _ (ZX_complete_connections_prf_1 n)
    eq_refl
    (big_stack (fun _ => 2) (Nat.double ∘ deg ∘ 
      (fun k => idx_to_edge n k))
      (fun k => 
        let ij := idx_to_edge n k in 
        (b2ZX (color (fst ij)) 1 (deg ij) 0) ↕
        (b2ZX (color (snd ij)) 1 (deg ij) 0))
      (n * (n - 1) / 2)).

Definition ZX_caps_stack n (deg : nat * nat -> nat) :  
  ZX (big_sum (Nat.double ∘ deg ∘ (idx_to_edge n)) 
    (n * (n - 1) / 2)) 0 :=
  cast _ _ eq_refl (ZX_complete_connections_prf_2 n)
    (big_stack (Nat.double ∘ deg ∘ (idx_to_edge n))
      (fun _ => 0)
      (fun k => 
        n_cup (deg (idx_to_edge n k)))
      (n * (n - 1) / 2)).


Definition ZX_complete_form n color αs deg : ZX n 0 :=
  ZX_complete_stack n αs color ⟷ 
  ZX_complete_perm n ⟷ ZX_complete_connections n deg color.


Lemma ZX_connections_stack_alt_prf n deg : 
  big_sum (Nat.double ∘ deg ∘ idx_to_edge n) (n * (n - 1) / 2) =
  big_sum (fun k => deg (idx_to_edge n (k / 2))) (n * (n - 1)).
Proof.
  rewrite Combinators.compose_assoc.
  unfold Nat.double.
  unfold compose at 1.
  rewrite big_stack_stack_prf.
  rewrite triangle_number_exact.
  apply big_sum_eq_bounded.
  intros k Hk.
  now rewrite Tauto.if_same.
Qed.

Lemma ZX_connections_stack_alt n color deg : 
  ZX_connections_stack n deg color ∝ 
  cast _ _ 
  (eq_trans (triangle_number_exact _) (eq_sym (Nsum_1 _)))
  (ZX_connections_stack_alt_prf n deg)
  (big_stack (fun _ => 1)
  (fun k => deg (idx_to_edge n (k / 2)))
  (fun k => 
    let ij := idx_to_edge n (k / 2) in 
   if k mod 2 =? 0 
   then (if color (fst ij) then X 1 (deg ij) 0 else Z 1 (deg ij) 0)
   else (if color (snd ij) then X 1 (deg ij) 0 else Z 1 (deg ij) 0))  
  (n * (n - 1)) ).
Proof.
  unfold ZX_connections_stack.
  change (Nat.double ∘ deg ∘ (fun k => idx_to_edge n k))
    with (fun k => (deg ∘ idx_to_edge n) k + (deg ∘ idx_to_edge n) k).
  etransitivity.
  1: {
    apply cast_mor.
    apply (big_stack_stack (fun _=>1) (fun _=>1)
      (deg ∘ idx_to_edge n) (deg ∘ idx_to_edge n)
      (fun k => if color (fst (idx_to_edge n k))
      then X 1 (deg (idx_to_edge n k)) 0
      else Z 1 (deg (idx_to_edge n k)) 0)
      (fun k => if color (snd (idx_to_edge n k))
      then X 1 (deg (idx_to_edge n k)) 0
      else Z 1 (deg (idx_to_edge n k)) 0)).
  }
  rewrite cast_contract_eq.
  prop_exists_nonzero 1%R.
  rewrite Mscale_1_l.
  simpl_cast_semantics.
  rewrite 2!big_stack_semantics.
  f_equal;
  [apply functional_extensionality_dep; intros k..|apply triangle_number_exact];
  [now rewrite Tauto.if_same..|].
  now destruct (k mod 2 =? 0).
Qed.






Lemma ZX_complete_connections_split n color deg : 
  ZX_complete_connections n deg color ∝ 
  ZX_connections_stack n deg color ⟷ ZX_caps_stack n deg.
Proof.
  unfold ZX_connections_stack, ZX_caps_stack.
  rewrite cast_compose_eq_mid_join.
  rewrite big_stack_compose.
  now apply cast_simplify.
Qed.

Lemma ZX_complete_form_pullthrough_1 n color αs deg : 
  ZX_complete_form n color αs deg ∝ 
  ZX_complete_stack n αs color ⟷
  cast _ _ (eq_sym (Nsum_1 _)) 
  (ZX_connections_stack_alt_prf n deg)
  (big_stack (fun _ => 1)
  ((fun k => deg (idx_to_edge n (k / 2)))
   ∘ perm_inv' (n * (n - 1)) (pairs_to_block_perm n))
  (fun k =>
   (fun k0 : nat =>
    if k0 mod 2 =? 0
    then
     if color (fst (idx_to_edge n (k0 / 2)))
     then X 1 (deg (idx_to_edge n (k0 / 2))) 0
     else Z 1 (deg (idx_to_edge n (k0 / 2))) 0
    else
     if color (snd (idx_to_edge n (k0 / 2)))
     then X 1 (deg (idx_to_edge n (k0 / 2))) 0
     else Z 1 (deg (idx_to_edge n (k0 / 2))) 0)
     (perm_inv' (n * (n - 1)) (pairs_to_block_perm n) k))
  (n * (n - 1))
⟷ big_zx_of_permutation_l (n * (n - 1))
    (perm_inv' (n * (n - 1)) (pairs_to_block_perm n))
    (fun k : nat => deg (idx_to_edge n (k / 2)))
    (perm_inv'_permutation (n * (n - 1)) 
       (pairs_to_block_perm n) (pairs_to_block_permutation n)))
  ⟷ ZX_caps_stack n deg.
Proof.
  unfold ZX_complete_form.
  rewrite compose_assoc.
  rewrite ZX_complete_connections_split.
  rewrite <- (compose_assoc (ZX_complete_perm n)).
  rewrite <- compose_assoc.
  apply compose_simplify; [|reflexivity].
  apply compose_simplify; [reflexivity|].
  unfold ZX_complete_perm.
  rewrite ZX_connections_stack_alt.
  unshelve rewrite zx_of_perm_to_big_zx_of_permutation_l;
  [auto_perm|].
  rewrite cast_contract_eq.
  rewrite cast_compose_eq_mid_join.
  unfold compose.
  apply cast_simplify.
  apply (big_zx_of_permutation_l_natural (n * (n - 1)) (fun _ => 1)).
Qed.




(* Lemma idx_to_edge_decomp_div2_case1 n k k' 
  (Hk : k < n) (Hk' : k' < n - 1) 
  (Hmod : (k * (n - 1) + k') mod 2 = 0) : 
  idx_to_edge n ((k * (n - 1) + k') / 2) = 
  if k <=? k'
  then wire_to_ordered_edge n (k * (n - 1) + k') 
  else (snd (wire_to_ordered_edge n (k * (n - 1) + k')), 
    fst (wire_to_ordered_edge n (k * (n - 1) + k'))).
Proof.
  assert (Hlt : k * (n - 1) + k' < n * (n - 1)) by show_moddy_lt.
  assert (Hlt' : (k * (n - 1) + k') / 2 < n * (n - 1) / 2) 
    by (apply Nat.Div0.div_lt_upper_bound; 
    rewrite (Nat.mul_comm 2), (triangle_number_exact n); lia).
  bdestructΩ'.
  unfold idx_to_edge.
  unfold wire_to_ordered_edge
  apply (edge_to_idx_inj n);
  [now apply idx_to_edge_spec..| | |];
  [unfold wire_to_ordered_edge;
  rewrite mod_add_l, Nat.div_add_l, 
    Nat.div_small, Nat.mod_small by lia; bdestructΩ';
  cbn [fst snd]; try lia.. |].
  rewrite idx_to_edge_to_idx by auto.
  cbv delta [wire_to_ordered_edge] beta.
  rewrite mod_add_l, Nat.div_add_l, 
    (Nat.div_small k'), Nat.mod_small, Nat.add_0_r by lia.
  cbn zeta.
  bdestruct (k <=? k').
  - replace_bool_lia (k' <? k) false.
    unfold edge_to_idx.
    cbn [fst snd].
    match goal with 
    | H : _ <= _ |- _ => 
      destruct (le_ex_diff_r _ _ H) as (d & Hd);
      clear H
    end.
    subst k'.
    replace (k * (n - 1) + (k + d)) with (k * n + d) in * by nia.
    replace (S (k + d) - S k) with d by lia.
    rewrite Nsum_reflect_perm by auto.
    rewrite <- (Nat.mul_cancel_r _ _ 2 ltac:(easy)).
    rewrite Nat.mul_add_distr_r, Nat.mul_sub_distr_r.
    rewrite <- triangle_number', triangle_number, triangle_number_exact.
    pose proof (Nat.div_mod_eq (k * n + d) 2).
    rewrite div_mul_not_exact, Hmod, Nat.sub_0_r by lia.
    
    rewrite triangle_number_exact
    induction k, (fun a : nat => a) using Nat.measure_induction.
    

    rewrite Nsum_reflect_perm.
  


  unfold idx_to_edge.

  ordered_edge_to_wire
*)

Lemma ZX_complete_form_pullthrough_2 n color αs deg : 
  ZX_complete_form n color αs deg ∝ 
  cast _ _ 
    (ZX_complete_stack_prf_1 n)
    (big_stack_mult_prf _ _ _)
    (big_stack (fun _ => 1) (fun k => big_sum (fun i =>
      ((fun k0 => deg (idx_to_edge n (k0 / 2)))
        ∘ perm_inv' (n * (n - 1)) (pairs_to_block_perm n))
        (k * (n - 1) + i)) (n - 1)) 
      (fun k => (b2ZX (color k) 1 _ (αs k))) n)
  ⟷ cast _ _
    eq_refl
    (ZX_connections_stack_alt_prf n deg)
    (big_zx_of_permutation_l (n * (n - 1))
      (perm_inv' (n * (n - 1)) (pairs_to_block_perm n))
      (fun k => deg (idx_to_edge n (k / 2)))
      (perm_inv'_permutation _ _ (pairs_to_block_permutation n)))
  ⟷ ZX_caps_stack n deg.
Proof.
  rewrite ZX_complete_form_pullthrough_1.
  rewrite big_stack_mult.
  unfold ZX_complete_stack.
  rewrite cast_compose_distribute.
  rewrite <- compose_assoc, cast_contract_eq.
  rewrite (big_stack_resize_unbounded 
    (fun _ => Nsum_1 (n - 1)) (fun k => eq_refl)).
  rewrite cast_contract_eq.
  rewrite cast_compose_eq_mid_join.
  rewrite big_stack_compose.
  rewrite (big_stack_simplify _ _ _ 
    (fun k => (b2ZX (color k) 1 _ (αs k)))).
  2: {
    intros k Hk.
    rewrite cast_compose_r, cast_b2ZX.
    rewrite b2ZX_spider_big_fusion_0'; [|easy|].
    2: {
      intros k' Hk'.
      unfold compose.
      rewrite b2ZX_if_color_dist.
      apply b2ZX_simplify; [|easy].
      assert (Hlt : k * (n - 1) + k' < n * (n - 1)) by show_moddy_lt.
      assert (Hlt' : (k * (n - 1) + k') / 2 < n * (n - 1) / 2) 
        by (apply Nat.Div0.div_lt_upper_bound; 
        rewrite (Nat.mul_comm 2), (triangle_number_exact n); lia).
      rewrite perm_inv'_eq by auto.
      rewrite pairs_to_block_perm_inv by auto.
      rewrite block_to_pairs_defn by auto.
      cbv delta [wire_to_ordered_edge] beta.
      rewrite mod_add_l, Nat.div_add_l, (Nat.div_small k'), 
        (Nat.mod_small k'), Nat.add_0_r by lia.
      cbn zeta.
      bdestruct (k' <? k).
      - cbn [fst snd].
        replace_bool_lia (k <? k') false.
        rewrite mod_add_l, if_false by reflexivity.
        rewrite Nat.div_add_l, Nat.add_0_r by lia.
        rewrite edge_to_idx_to_edge by (cbn; lia).
        reflexivity.
      - cbn [fst snd].
        replace_bool_lia (k <? S k') true.
        rewrite Nat.Div0.mod_mul.
        cbn [Nat.eqb].
        rewrite Nat.div_mul by lia.
        rewrite edge_to_idx_to_edge by (cbn; lia).
        reflexivity.
    }
    reflexivity.
  }
  apply compose_simplify; [|reflexivity].
  apply compose_simplify; [|reflexivity].
  cast_irrelevance.
Qed.



Definition ZX_large_stack n (color : nat -> bool) αs deg :=
  cast _ _ 
    (ZX_complete_stack_prf_1 n)
    (big_stack_mult_prf _ _ _)
    (big_stack (fun _ => 1) (fun k => big_sum (fun i =>
      ((fun k0 => deg (idx_to_edge n (k0 / 2)))
        ∘ (block_to_pairs_perm n))
        (k * (n - 1) + i)) (n - 1)) 
      (fun k => (b2ZX (color k) 1 _ (αs k))) n).

Definition ZX_large_perm n deg :=
  cast _ _
    eq_refl
    (ZX_connections_stack_alt_prf n deg)
    (big_zx_of_permutation_l (n * (n - 1))
      (block_to_pairs_perm n)
      (fun k => deg (idx_to_edge n (k / 2)))
      (block_to_pairs_permutation n)).



Definition ZX_large_form n color αs deg : ZX n 0 :=
  ZX_large_stack n color αs deg ⟷ 
  ZX_large_perm n deg ⟷
  ZX_caps_stack n deg.



Lemma ZX_complete_large_form_equiv n color αs deg : 
  ZX_complete_form n color αs deg ∝
  ZX_large_form n color αs deg.
Proof.
  rewrite ZX_complete_form_pullthrough_2.
  apply compose_simplify; [|reflexivity].
  unfold ZX_large_stack, ZX_large_perm.
  unshelve (eapply compose_simplify_casted);
  [now rewrite pairs_to_block_perm_inv'|..].
  - rewrite cast_contract_eq.
    apply big_stack_simplify_casted_casted_abs;
    [reflexivity|now rewrite pairs_to_block_perm_inv'|].
    intros k ? ? Hk.
    now rewrite cast_b2ZX.
  - unfold big_zx_of_permutation_l.
    rewrite !cast_contract_eq.
    apply cast_simplify.
    now rewrite pairs_to_block_perm_inv'.
Qed.


Lemma ZX_complete_stack_zx_of_perm_passthrough n αs color 
  f (Hf : permutation n f) : 
  zx_of_perm n f ⟷ ZX_complete_stack n αs color ∝
  ZX_complete_stack n 
    (αs ∘ (perm_inv' n f)) (color ∘ (perm_inv' n f)) ⟷
  cast _ _ (eq_trans (ZX_complete_stack_prf_2 n)
    (Nsum_reorder n _ _ (perm_inv'_permutation n f Hf))) 
  (ZX_complete_stack_prf_2 n)
    (big_zx_of_permutation_l n (perm_inv' n f)
      (fun _ => n - 1) 
      (perm_inv'_permutation n f Hf)).
Proof.
  rewrite (zx_of_perm_to_big_zx_of_permutation_l n f Hf).
  unfold ZX_complete_stack.
  rewrite cast_compose_eq_mid_join.
  erewrite cast_mor by
  (apply (big_zx_of_permutation_l_natural n (fun _ => 1))).
  unfold compose.
  rewrite (cast_compose_mid _ 
  (ZX_complete_stack_prf_2 n) (ZX_complete_stack_prf_2 n)).
  rewrite cast_compose_distribute.
  rewrite 2!cast_contract_eq.
  apply compose_simplify; cast_irrelevance.
Qed.















Lemma ZX_complete_form_zx_of_perm_absorbtion n color αs deg 
  f (Hf : permutation n f) 
  (Hdeg : forall k l, k < n -> l < n -> deg (k, l) = deg (l, k)) : 
  zx_of_perm n f ⟷ ZX_complete_form n color αs deg ∝
  ZX_complete_form n (color ∘ perm_inv' n f) (αs ∘ perm_inv' n f) 
    (fun ij => deg (perm_inv' n f (fst ij), perm_inv' n f (snd ij))).
Proof.
  unfold ZX_complete_form at 1.
  rewrite <- 2!compose_assoc.
  rewrite (ZX_complete_stack_zx_of_perm_passthrough _ _ _ _ Hf).
  unfold ZX_complete_perm.
  rewrite (compose_assoc (ZX_complete_stack _ _ _)).
  unfold big_zx_of_permutation_l.
  rewrite enlarge_permutation_constant.
  rewrite perm_inv'_perm_inv' by auto.
  rewrite cast_contract_eq.
  rewrite cast_zx_of_perm.
  rewrite cast_compose_r, cast_id.
  rewrite compose_zx_of_perm by auto_perm.
  pose proof (triangle_number_exact n) as Htri.
  rewrite pairs_to_block_perm_pullthrough_l by auto.
  pose proof (fun f => proj1 (permutation_change_dims _ _ 
    (Nsum_constant 2 (n * (n - 1) / 2)) f)).
  pose proof (fun f => proj1 (permutation_change_dims _ _ 
    (Htri) f)).
  pose proof (fun f => proj1 (permutation_change_dims _ _ 
    (Nsum_constant (n - 1) n) f)).
  assert (permutation (n * (n - 1))
    (big_stack_perms n (fun _ => n - 1) 
    (fun k => contract_perm (perm_inv n f) k))) by auto_perm.
  assert (forall n (b : bool) f g, permutation n f -> permutation n g ->
    permutation n (if b then f else g)) by (intros; now destruct b).
  assert (permutation (n * (n - 1))
    (big_stack_perms (n * (n - 1) / 2) (fun _ => 2)
    (fun k => let ij := idx_to_edge n k in
    if f (snd ij) <? f (fst ij) then swap_2_perm else idn))) by auto_perm.
  rewrite <- 3!compose_zx_of_perm by auto_perm. 
  let H := constr:(eq_sym (Nsum_constant (n - 1) n)) in 
  rewrite <- (cast_zx_of_perm _ _ _ H H).
  rewrite zx_of_big_stack_perms by auto_perm.
  assert (Hrw : pairs_perm n f = perm_inv' (n * (n - 1) / 2) 
    (perm_inv' (n * (n - 1) / 2) (pairs_perm n f))) 
    by cleanup_perm_inv.
  rewrite Hrw.
  rewrite <- enlarge_permutation_constant.
  let H := constr:(eq_sym (eq_trans (Nsum_constant 2 (n * (n - 1) / 2)) Htri)) in 
  rewrite <- 2!(cast_zx_of_perm _ _ (_ _ _) H H).
  unshelve (rewrite zx_of_enlarge_to_big_zx_of_permutation_l);
  [auto_perm|].
  rewrite zx_of_big_stack_perms by auto_perm.
  rewrite !cast_compose_distribute, !cast_contract_eq.
  rewrite !compose_assoc.
  unfold ZX_complete_connections.
  rewrite cast_compose_eq_mid_join.
  rewrite big_stack_compose.
  rewrite cast_compose_eq_mid_join.
  rewrite <- !compose_assoc.
  unfold ZX_complete_form.
  rewrite (cast_compose_mid _ Htri Htri).
  apply compose_simplify.
  - rewrite cast_compose_distribute, cast_contract_eq.
    apply compose_simplify; [|unfold ZX_complete_perm; cast_irrelevance].
    unfold ZX_complete_stack.
    rewrite cast_compose_eq_mid_join.
    rewrite big_stack_compose.
    rewrite cast_contract_eq.
    apply cast_simplify.
    apply big_stack_simplify.
    intros k Hk.
    apply b2ZX_zxperm_absorbtion_right; auto_zxperm.
  - rewrite big_zx_of_permutation_l_natural.
    unfold compose.
    let H := constr:(big_sum_0 (fun _ => 0) 
      (n * (n - 1) / 2) (fun _ => eq_refl)) in 
    rewrite (@proportional_of_perm_eq _ _ _ (cast _ _ H H (n_wire 0)))
      by ((rewrite (big_sum_0 (fun _ => 0)) at 1; easy) +
        unfold big_zx_of_permutation_l; auto_zxperm).
    rewrite cast_n_wire, nwire_removal_r.
    unfold ZX_complete_connections.
    rewrite cast_contract_eq.
    apply cast_simplify.
    apply big_stack_simplify.
    intros k Hk.
    rewrite pairs_perm_inv' by auto.
    pattern (idx_to_edge n (pairs_perm n (perm_inv' n f) k)).
    match goal with |- ?p ?k => set (P := p) end.
    rewrite pairs_perm_defn by auto.
    pose proof (idx_to_edge_spec n k Hk) as Hspec.
    set (ij := idx_to_edge n k) in *.
    cbn zeta.
    assert (perm_inv' n f (fst ij) <> perm_inv' n f (snd ij))
      by (clear -Hspec Hf; 
      intros Heq; apply (permutation_is_injective n (perm_inv' n f)) in Heq; 
        lia + auto_perm).
    assert (Hbdd : perm_bounded n (perm_inv' n f)) by auto_perm.
    pose proof (Hbdd (fst ij) ltac:(lia)).
    pose proof (Hbdd (snd ij) ltac:(lia)).
    bdestruct_one;
    rewrite edge_to_idx_to_edge by (cbn [fst snd]; lia);
    unfold P;
    cbn [fst snd]; 
    rewrite 2!perm_inv'_eq, 2!perm_inv_is_rinv_of_permutation by auto_perm.
    + replace_bool_lia (snd ij <? fst ij) false.
      rewrite zx_of_perm_idn, nwire_removal_l.
      easy.
    + replace_bool_lia (fst ij <? snd ij) true.
      change swap_2_perm with (perm_of_zx ⨉).
      rewrite zx_of_perm_of_zx_square by auto_perm.
      rewrite <- compose_assoc.
      rewrite swap_pullthrough_r.
      rewrite compose_assoc.
      rewrite n_cup_zx_comm_absorbtion.
      rewrite Hdeg by auto_perm.
      easy.
Qed.



    


Lemma ZX_io_stack_prf m n f : 
  n = big_sum (fun k => if k <? n then 1 else 0) (Nat.max n (S (Nmax m f))).
Proof.
  bdestruct (n <? S (Nmax m f)).
  - replace (Nat.max n (S (Nmax m f))) with (n + (S (Nmax m f) - n)) by lia.
    rewrite big_sum_sum.
    rewrite (big_sum_eq_bounded _ (fun _ => 1)) by (intros; bdestructΩ').
    rewrite Nsum_1.
    rewrite big_sum_0 by (intros; bdestructΩ').
    cbn; lia.
  - rewrite Nat.max_l by lia.
    rewrite (big_sum_eq_bounded _ (fun _ => 1)) by (intros; bdestructΩ').
    now rewrite Nsum_1.
Qed.

Definition ZX_io_stack_gen m n f (color : nat -> bool) : ZX m n :=
  cast _ _ 
  (eq_sym (sum_count_func_vals _ _ _ (WF_input_func_default m n f))) 
  (ZX_io_stack_prf m n f)
    (big_stack _ _ (fun k => b2ZX (color k) _ _ 0) _).

Definition ZX_io_stack_WF m n f (color : nat -> bool) 
  (Hf : WF_input_func m n f) : ZX m n :=
  cast _ _ 
  (eq_sym (sum_count_func_vals _ _ _ Hf)) 
  (eq_sym (Nsum_1 n))
    (big_stack _ _ (fun k => b2ZX (color k) _ _ 0) _).








Lemma ZX_io_stack_gen_equiv_WF m n f (color : nat -> bool) 
  (Hf : WF_input_func m n f) : 
  ZX_io_stack_gen m n f color ∝
  ZX_io_stack_WF m n f color Hf.
Proof.
  bdestruct (m =? 0); [bdestruct (n =? 0)|].
  - subst.
    unfold ZX_io_stack_gen, ZX_io_stack_WF.
    cbn.
    rewrite b2ZX_0_0_is_empty.
    rewrite stack_empty_l.
    cast_irrelevance.
  - prop_exists_nonzero 1%R.
    rewrite Mscale_1_l.
    unfold ZX_io_stack_gen, ZX_io_stack_WF.
    simpl_cast_semantics.
    subst.
    cbn.
    rewrite 2!big_stack_semantics.
    rewrite Nat.max_l by lia.
    apply big_kron'_eq_bounded_dims;
    intros k Hk; bdestructΩ'.
  - prop_exists_nonzero 1%R.
    rewrite Mscale_1_l.
    unfold ZX_io_stack_gen, ZX_io_stack_WF.
    simpl_cast_semantics.
    rewrite 2!big_stack_semantics.
    rewrite max_n_S_Nmax_WF by auto.
    apply big_kron'_eq_bounded_dims;
    intros k Hk; bdestructΩ'.
Qed.

Definition ZX_of_io m n f color : ZX m n :=
  zx_of_perm m (perm_inv' m (perm_of_input_func m f)) 
    ⟷ ZX_io_stack_gen m n f color.




  




Lemma ZX_of_io_absorb_zx_of_perm_r m n f color g 
  (Hf : WF_input_func m n f) (Hg : permutation n g) : 
  ZX_of_io m n f color ⟷ zx_of_perm n g ∝
  ZX_of_io m n (perm_inv' n g ∘ f) (color ∘ g).
Proof.
  unfold ZX_of_io.
  rewrite (ZX_io_stack_gen_equiv_WF _ _ _ _ Hf).
  assert (Hg' : perm_bounded n (perm_inv' n g)) by auto_perm.
  rewrite (ZX_io_stack_gen_equiv_WF _ _ (_ ∘ _) 
    _ (fun k => Hg' _ ∘ Hf k)).
  unfold ZX_io_stack_WF.
  rewrite (zx_of_perm_to_big_zx_of_permutation_r n g Hg).
  rewrite compose_assoc.
  rewrite cast_compose_eq_mid_join.
  erewrite cast_mor;
  [|etransitivity;
  [exact (big_zx_of_permutation_r_natural n _ _ _ g Hg)|
  let H := constr:(eq_trans (eq_sym (sum_count_func_vals _ _ _ Hf))
    (Nsum_reorder n _ g Hg)) in 
  exact (cast_compose_mid _ H H _ _)]].
  rewrite cast_compose_distribute, 2!cast_contract_eq.
  rewrite <- compose_assoc.
  apply compose_simplify.
  - unfold big_zx_of_permutation_r.
    rewrite cast_contract_eq, cast_zx_of_perm.
    pose proof (sum_count_func_vals _ _ _ Hf) as Heq.
    pose proof (fun h => proj1 (permutation_change_dims _ _ Heq h)).
    rewrite (Nsum_reorder _ _ g Hg) in H.
    rewrite compose_zx_of_perm by auto_perm.
    erewrite zx_of_perm_eq_of_perm_eq; [reflexivity|].
    rewrite <- enlarge_permutation_inv' by auto.
    rewrite <- (Nsum_reorder _ _ g Hg) in H.
    rewrite Heq.
    rewrite <- perm_inv'_compose by auto_perm.
    rewrite 2!perm_inv'_eq.
    apply perm_inv_perm_eq_proper.
    now rewrite perm_of_input_func_enlarge_permutation_l by auto.
  - rewrite (big_stack_resize (count_func_vals_compose_perm_r m n f g Hf Hg) 
      (perm_eq_refl n (fun _ => 1))), cast_contract_eq.
    apply cast_simplify.
    apply big_stack_simplify.
    intros k Hk.
    destruct (lt_dec k n); [|easy].
    now rewrite cast_b2ZX.
Qed.

Record ZX_graph_core {m : nat} := {
  core_io := m;
  core_spis : nat;
  core_infunc : nat -> nat;
  core_deg : nat * nat -> nat;
  core_color : nat -> bool;
  core_αs : nat -> R;
}.

Arguments ZX_graph_core _ : clear implicits.

Record WF_ZX_graph_core {m} {ZXG : ZX_graph_core m} : Prop := {
  WF_core_sym : forall k l, k < ZXG.(core_spis) -> l < ZXG.(core_spis) -> 
    ZXG.(core_deg) (k, l) = ZXG.(core_deg) (l, k);
  WF_core_infunc : WF_input_func m ZXG.(core_spis) ZXG.(core_infunc)
}.

Arguments WF_ZX_graph_core {_} _.

(* FIXME: Move? *)
Create HintDb WF_ZX_graph_db discriminated.
#[export] Hint Extern 0 (permutation _ _) => 
  solve [auto_perm] : WF_ZX_graph_db.
#[export] Hint Extern 0 (perm_bounded _ _) => 
  solve [auto_perm] : WF_ZX_graph_db.
#[export] Hint Extern 0 (WF_Perm _ _) => 
  solve [auto_perm] : WF_ZX_graph_db.

Definition ZX_of_ZX_graph_core {m} (ZXG : ZX_graph_core m) : ZX m 0 :=
  ZX_of_io m ZXG.(core_spis) ZXG.(core_infunc) ZXG.(core_color) ⟷
  ZX_complete_form ZXG.(core_spis) ZXG.(core_color) 
    ZXG.(core_αs) ZXG.(core_deg).

Definition ZX_of_ZX_graph_core_WF {m} (ZXG : ZX_graph_core m) 
  (HZXG : WF_ZX_graph_core ZXG) : ZX m 0 :=
  zx_of_perm m (perm_inv' m (perm_of_input_func m (ZXG.(core_infunc)))) ⟷
  ZX_io_stack_WF m ZXG.(core_spis) ZXG.(core_infunc) ZXG.(core_color) 
    HZXG.(WF_core_infunc) ⟷
  ZX_complete_form ZXG.(core_spis) ZXG.(core_color) 
    ZXG.(core_αs) ZXG.(core_deg).

Lemma ZX_of_ZX_graph_core_equiv_WF {m} (ZXG : ZX_graph_core m) 
  (HZXG : WF_ZX_graph_core ZXG) : 
  ZX_of_ZX_graph_core ZXG ∝ ZX_of_ZX_graph_core_WF ZXG HZXG.
Proof.
  apply compose_simplify; [|reflexivity].
  apply compose_simplify; [reflexivity|].
  apply ZX_io_stack_gen_equiv_WF.
Qed.

Definition permute_ZX_graph_core {m} (ZXG : ZX_graph_core m) f : 
  ZX_graph_core m := {|
  core_spis := ZXG.(core_spis);
  core_infunc := perm_inv' (ZXG.(core_spis)) f ∘ ZXG.(core_infunc);
  core_deg := ZXG.(core_deg) ∘ (fun ij => (f (fst ij), f (snd ij)));
  core_color := ZXG.(core_color) ∘ f;
  core_αs := ZXG.(core_αs) ∘ f;
|}.

Lemma permute_ZX_graph_core_WF {m} (ZXG : ZX_graph_core m) f 
  (HZXG : WF_ZX_graph_core ZXG) (Hf : permutation ZXG.(core_spis) f) : 
  WF_ZX_graph_core (permute_ZX_graph_core ZXG f).
Proof.
  constructor.
  - cbn.
    unfold compose.
    cbn.
    intros.
    apply WF_core_sym; auto_perm.
  - cbn.
    intros k Hk.
    unfold compose.
    auto using (WF_core_infunc HZXG) with perm_db.
Qed.

#[export] Hint Resolve permute_ZX_graph_core_WF : WF_ZX_graph_db.

(* FIXME: Move these up *)
Lemma ZX_complete_stack_simplify n color αs color' αs' 
  (Hcolor : forall k, k < n -> color k = color' k)
  (Hαs : forall k, k < n -> αs k = αs' k):
  ZX_complete_stack n αs color ∝ 
  ZX_complete_stack n αs' color'.
Proof.
  unfold ZX_complete_stack.
  apply cast_simplify.
  apply big_stack_simplify.
  auto using b2ZX_simplify.
Qed.

Lemma ZX_complete_connections_simplify n color deg color' deg' 
  (Hcolor : forall k, k < n -> color k = color' k)
  (Hdeg : forall k l, k < n -> l < n -> deg (k, l) = deg' (k, l)) :
  ZX_complete_connections n deg color ∝ 
  ZX_complete_connections n deg' color'.
Proof.
  unfold ZX_complete_connections.
  apply cast_simplify.
  apply big_stack_simplify.
  intros k Hk.
  rewrite (surjective_pairing (idx_to_edge n k)).
  cbn [fst snd].
  pose proof (idx_to_edge_spec n k Hk).
  now rewrite 2!Hcolor, Hdeg by lia.
Qed.


Lemma ZX_complete_form_simplify n color αs deg 
  color' αs' deg' 
  (Hcolor : forall k, k < n -> color k = color' k)
  (Hαs : forall k, k < n -> αs k = αs' k)
  (Hdeg : forall k l, k < n -> l < n -> deg (k, l) = deg' (k, l)) :
  ZX_complete_form n color αs deg ∝ 
  ZX_complete_form n color' αs' deg'.
Proof.
  unfold ZX_complete_form.
  auto using compose_simplify, ZX_complete_stack_simplify, 
  ZX_complete_connections_simplify, proportional_refl.
Qed.

Lemma permute_ZX_graph_core_correct {m} (ZXG : ZX_graph_core m)
  (HZXG : WF_ZX_graph_core ZXG) f (Hf : permutation ZXG.(core_spis) f) :
  ZX_of_ZX_graph_core ZXG ∝ 
  ZX_of_ZX_graph_core (permute_ZX_graph_core ZXG f).
Proof.
  unfold ZX_of_ZX_graph_core.
  destruct ZXG as [_ n g deg color αs].
  destruct HZXG as [Hdeg Hg].
  cbn in *.
  rewrite <- (nwire_removal_r (ZX_of_io _ _ _ _)).
  rewrite <- zx_of_perm_idn.
  rewrite <- (perm_inv_rinv_of_permutation n f Hf).
  rewrite <- compose_zx_of_perm by auto_perm.
  rewrite <- perm_inv'_eq.
  rewrite <- compose_assoc.
  rewrite ZX_of_io_absorb_zx_of_perm_r by auto.
  rewrite compose_assoc.
  rewrite ZX_complete_form_zx_of_perm_absorbtion by auto_perm.
  apply compose_simplify; [reflexivity|].
  apply ZX_complete_form_simplify;
  intros; unfold compose; 
  cbn;
  now rewrite 2?perm_inv'_perm_inv' by auto_perm.
Qed.












Require Import Bipermutations NFBiperm ZXbiperm.














(* FIXME: Generalize, move to top, use for ZX_complete_conenctions_prf_2 *)
Lemma ZX_decomp_like_spider_stack_prf n : 
  0 = big_sum (fun _ => 0) n.
Proof. rewrite Nsum_constant; lia. Qed.

Definition ZX_decomp_like_spider_stack m spis infunc 
  (color : nat -> bool) αs deg 
  (* (Hin : WF_input_func m spis)  *)
  (* (Hdeg : forall k l, k < spis -> l < spis -> deg (k, l) = deg (l, k)) *) :
  (* ZX 0 (m + big_sum (fun i => big_sum (deg i) spis) spis) := *)
  ZX 0 (big_sum (fun i => count_func_vals m infunc i + big_sum (deg i) spis) spis) :=
  cast _ _ (ZX_decomp_like_spider_stack_prf _) eq_refl
    (big_stack (fun _ => 0) _ 
      (fun k => b2ZX (color k) 0 _ (αs k)) spis).



(* 

Definition ZX_decomp_like_spider_stack_alt m spis infunc 
  (color : nat -> bool) αs deg 
  (* (Hin : WF_input_func m spis)  *)
  (* (Hdeg : forall k l, k < spis -> l < spis -> deg (k, l) = deg (l, k)) *) :
  (* ZX 0 (m + big_sum (fun i => big_sum (deg i) spis) spis) := *)
  ZX 0 (big_sum (count_func_vals m infunc) spis +
    big_sum (fun i => big_sum (deg i) spis) spis) :=
  n_cap (big_sum (fun _ => 1) spis) ⟷
    (big_stack (fun _ => 1) _ (fun k => b2ZX (color k) 1 _ (αs k)) spis
    ↕ big_stack (fun _ => 1) _ (fun k => b2ZX (color k) 1 _ (αs k)) spis).

Lemma ZX_decomp_like_spider_stack_from_alt m spis infunc color αs deg :
  ZX_decomp_like_spider_stack_alt m spis infunc color αs deg ∝
  ZX_decomp_like_spider_stack m spis infunc color αs deg ⟷
  cast _ _ (big_stack_stack_prf _ _ _) 
  (eq_trans (eq_sym (Nsum_plus _ _ _)) (eq_trans
    (big_stack_stack_prf _ _ _) (Nsum_reorder _ _ _ 
      (kron_comm_perm_permutation spis 2))))
  (big_zx_of_permutation_r (spis * 2) (kron_comm_perm spis 2) _
    (kron_comm_perm_permutation spis 2)).
Proof.
  rewrite compose_zxperm_r' by auto_zxperm.
  rewrite cast_transpose.
  rewrite big_zx_of_permutation_r_transpose.
  big_stack_stack_enlarge_kron_natural_r

  big_stack_stack_enlarge_kron_natural_r
  



Definition ZX_graph_core_to_decomp_like m k infunc color αs deg : ZX m 0 :=
  ZX_of_io m ZXG.(core_spis) ZXG.(core_infunc) ZXG.(core_color) ⟷
  ZX_complete_form ZXG.(core_spis) ZXG.(core_color) 
    ZXG.(core_αs) ZXG.(core_deg).




Lemma perm_of_input_func_succ m f :
  perm_eq (S m) (perm_of_input_func (S m) f)
    (stack_perms (count_func_vals (S m) f 0) (S m - count_func_vals (S m) f 0)
      idn (perm_of_input_func m (fun k => S ∘

Definition contract_input_func_0 m n f v :=
  Nsum_index 
  

Definition ZX_graph_core_dec_spis {m} (ZXG : ZX_graph_core m) 
  : ZX_graph_core (m - count_func_vals m ZXG.(core_infunc) 0) :=
  {|
    core_spis := ZXG.(core_spis) - 1;
    core_infunc
  |} *)




(* Lemma biperm_of_zx_nstack {n m} k (zx : ZX n m) (Hzx : ZXbiperm zx) : 
  perm_eq (k * n + k * m) (biperm_of_zx (k ⇑ zx))
  (tensor_perms k (n + m) idn (biperm_of_zx zx)).
  (* enlarge_permutation_constant *)
  (* (kron_comm_perm (n + m) k 
    ∘ tensor_perms k (n + m) idn (biperm_of_zx zx)
    ∘ kron_comm_perm k (n + m)). *)
Proof.
  bdestruct (k =? 2).
  subst. 
  assert (Hrw : 2 ⇑ zx ∝ @cast (2 * n) (2 * m) (n + n) (m + m) ltac:(lia) ltac:(lia) (zx ↕ zx)).
  cbn.
  clean_eqns rewrite stack_empty_r, cast_stack_r.
  cast_irrelevance.
  rewrite (biperm_of_zx_eq_of_prop_rw Hrw) by auto with zxbiperm_db.
  rewrite biperm_of_zx_cast.
  rewrite biperm_of_zx_stack by auto with zxbiperm_db.
  assert (Hrev : bipermutation (n + m) (biperm_of_zx zx)) 
    by (now apply biperm_of_zx_bipermutation).
  revert Hrev.
  generalize (biperm_of_zx zx).
  intros f Hf.
  eapply perm_eq_dim_change_if_nonzero;
  [rewrite stack_biperms_defn|lia].
  eapply perm_eq_dim_change_if_nonzero;
  [rewrite tensor_perms_defn|lia].
  intros k Hk.
  unfold compose at 1.
  intros k Hk.

  
  rewrite Combinators.compose_assoc, tensor_perms_kron_comm_perm_natural.
  rewrite <- Combinators.compose_assoc
  cbn [n_stack].
  


tensor_perms_kron_comm_perm_natural *)

















Lemma ZX_complete_form_first_disconnected n color alphas deg 
  (H0 : forall k, k < S n -> k <> 0 -> deg (0, k) = 0) : 
  ZX_complete_form (S n) color alphas deg ∝
  b2ZX (color 0) 1 0 (alphas O) ↕
  ZX_complete_form n (fun k => color (1 + k)) (fun k => alphas (1 + k))
    (fun ij => deg (1 + fst ij, 1 + snd ij)).
Proof.
  rewrite 2!ZX_complete_large_form_equiv.
  unfold ZX_large_form.
  rewrite <- 2!(@compose_empty_r 1).
  rewrite 2!stack_compose_distr, 2!stack_empty_l.
  assert (Heq : big_sum (Nat.double ∘ deg ∘ idx_to_edge (S n)) 
    (S n * (S n - 1) / 2) = 0 + big_sum
    (Nat.double ∘ (fun ij => deg (1 + fst ij, 1 + snd ij))
     ∘ idx_to_edge n) (n * (n - 1) / 2)). 1: {
    rewrite <- triangle_number.
    cbn [big_sum].
    rewrite Nat.add_comm.
    rewrite big_sum_sum.
    cbn [nat_is_monoid Gplus].
    f_equal.
    - rewrite big_sum_0_bounded; [reflexivity|].
      intros k Hk.
      unfold compose.
      assert (Hk' : k < S n * (S n - 1) / 2) by 
        (rewrite <- triangle_number; cbn; lia).
      rewrite idx_to_edge_succ by auto.
      simplify_bools_lia_one_kernel.
      now rewrite H0 by lia.
    - rewrite (Nsum_permutation n) by auto_perm.
      apply big_sum_eq_bounded.
      intros k Hk.
      unfold compose.
      do 2 f_equal.
      rewrite idx_to_edge_succ by 
        (rewrite <- !triangle_number in *; cbn; lia).
      replace_bool_lia (n + k <? n) false.
      now rewrite add_sub'.
  }
  pose proof Heq as Heq'.
  rewrite 2!ZX_connections_stack_alt_prf in Heq'.
  unshelve (eapply compose_simplify_casted); [auto|..].
  1: rewrite cast_compose_distribute.
  1: unshelve (eapply compose_simplify_casted). 1: {
    rewrite <- 2!Nsum_reorder by auto_perm.
    auto.
  }
  - unfold ZX_large_stack.
    rewrite (big_stack_split_add _ _ _ 1 n).
    rewrite 2!cast_contract_eq.
    cbn [big_stack].
    rewrite stack_empty_l.
    prop_exists_nonzero 1%R.
    rewrite Mscale_1_l.
    simpl_cast_semantics.
    cbn [ZX_semantics].
    simpl_cast_semantics.
    rewrite 2!big_stack_semantics.
    assert (Hsum0 : (big_sum (fun i=>((fun k0=>deg(idx_to_edge (S n) (k0/2)))
        ∘ block_to_pairs_perm (S n)) (0 * (S n - 1) + i)) (S n - 1)) = 0).
    1: {
      rewrite big_sum_0_bounded; [reflexivity|].
      intros k Hk.
      rewrite Nat.mul_0_l, Nat.add_0_l.
      unfold compose.
      rewrite block_to_pairs_defn by lia.
      unfold wire_to_ordered_edge.
      rewrite (Nat.mod_small k), (Nat.div_small k) by auto.
      cbn -[Nat.divmod Nat.div].
      replace_bool_lia (0 <=? k) true.
      rewrite Nat.div_mul by lia.
      rewrite idx_to_edge_succ by (rewrite <- triangle_number; cbn; lia).
      simplify_bools_lia_one_kernel.
      apply H0; lia.
    }
    assert (Hsumbig_step1 : perm_eq n (fun k =>
      big_sum (fun i => ((fun k0 => deg (idx_to_edge (S n) (k0 / 2)))
       ∘ block_to_pairs_perm (S n)) ((1 + k) * (S n - 1) + i)) (S n - 1))
      (fun k => big_sum (fun i => ((fun k0 => deg
      (1 + fst (idx_to_edge n (k0 / 2)), 1 + snd (idx_to_edge n (k0 / 2)))) ∘ 
       block_to_pairs_perm n) (k * (n - 1) + i)) (n - 1))). 1: {
    intros k Hk.
    replace (S n - 1) with (S (n - 1)) by lia.
    rewrite (big_sum_sum 1 (n - 1)).
    cbn [Gplus nat_is_monoid].
    etransitivity; [|apply Nat.add_0_l].
    f_equal.
    * cbn [big_sum nat_is_monoid Gplus].
      unfold compose.
      rewrite block_to_pairs_defn by nia.
      rewrite Nat.add_0_r.
      unfold wire_to_ordered_edge.
      replace (S n - 1) with (S (n - 1)) by lia.
      rewrite Nat.Div0.mod_mul, Nat.div_mul by lia.
      replace_bool_lia (0 <? 1 + k) true.
      cbn [fst snd Nat.ltb Nat.leb].
      rewrite Nat.div_add_l, Nat.add_0_r, Nat.add_0_l by lia.
      rewrite edge_to_idx_to_edge by (cbn; lia).
      apply H0; lia.
    * apply big_sum_eq_bounded.
      intros l Hl.
      unfold compose.
      rewrite block_to_pairs_defn by nia.
      cbv delta [wire_to_ordered_edge] beta.
      replace (S n - 1) with (S (n - 1)) by lia.
      rewrite Nat.div_add_l, mod_add_l, 
        (Nat.div_small (1 + _)), (Nat.mod_small (1 + _)) by lia.
      rewrite Nat.add_0_r.
      cbn zeta.
      change (1 + l <? 1 + k) with (l <? k).
      bdestruct (l <? k); cbn [fst snd].
      --replace_bool_lia (1 + k <? 1 + l) false.
        rewrite Nat.div_add_l, Nat.add_0_r, edge_to_idx_to_edge by (cbn; lia).
        rewrite block_to_pairs_defn by nia.
        cbv delta [wire_to_ordered_edge] beta.
        rewrite Nat.div_add_l, mod_add_l, 
          (Nat.div_small l), (Nat.mod_small l), Nat.add_0_r by lia.
        cbn zeta.
        replace_bool_lia (l <? k) true.
        cbn [fst snd].
        replace_bool_lia (k <? l) false.
        rewrite Nat.div_add_l, Nat.add_0_r, edge_to_idx_to_edge by (cbn; lia).
        reflexivity.
      --replace_bool_lia (1 + k <? S (1 + l)) true.
        rewrite Nat.div_mul, edge_to_idx_to_edge by (cbn; lia).
        rewrite block_to_pairs_defn by nia.
        cbv delta [wire_to_ordered_edge] beta.
        rewrite Nat.div_add_l, mod_add_l, 
          (Nat.div_small l), (Nat.mod_small l), Nat.add_0_r by lia.
        cbn zeta.
        replace_bool_lia (l <? k) false.
        cbn [fst snd].
        replace_bool_lia (k <? S l) true.
        rewrite Nat.div_mul, edge_to_idx_to_edge by (cbn; lia).
        reflexivity.
    }

    assert (Hsumbig : big_sum (fun k => big_sum (fun i =>
      ((fun k0 => deg (idx_to_edge (S n) (k0 / 2)))
        ∘ block_to_pairs_perm (S n)) ((1 + k) * (S n - 1) + i))
        (S n - 1)) n =
      big_sum ((fun k0 => deg (1 + fst (idx_to_edge n (k0 / 2)),
        1 + snd (idx_to_edge n (k0 / 2)))) ∘ block_to_pairs_perm n)
        (n * (n - 1))).
    1: {
      rewrite big_stack_mult_prf.
      apply big_sum_eq_bounded.
      apply Hsumbig_step1.
    }
    f_equal; cbn [big_sum Gplus nat_is_monoid]; rewrite ?Hsum0; [auto|..].
    + now rewrite Hsumbig.
    + now rewrite Nsum_1.
    + reflexivity.
    + apply big_kron'_eq_bounded_dims; [auto_perm..|].
      intros k Hk.
      now rewrite Hsumbig_step1 by auto.
  - unfold ZX_large_perm, big_zx_of_permutation_l.
    rewrite !cast_contract_eq.
    rewrite cast_zx_of_perm_natural_l.
    symmetry.
    rewrite cast_zx_of_perm_natural_l.
    apply cast_simplify.
    erewrite zx_of_perm_perm_eq_to_eq_proper; [reflexivity|].
    rewrite <- Nsum_reorder by auto_perm.
    symmetry.
    rewrite enlarge_permutation_defn.
    rewrite Heq', Nat.add_0_l.
    rewrite enlarge_permutation_defn.
    intros k Hk.
    rewrite 2!block_to_pairs_perm_inv'.
    assert (Hsmall : big_sum (fun k0 => 
      deg (idx_to_edge (S n) (k0 / 2))) (n * 2) = 0). 1:{
      rewrite big_sum_0_bounded; [reflexivity|].
      intros l Hl.
      assert (l / 2 < n) by show_moddy_lt.
      rewrite idx_to_edge_succ by (rewrite <- triangle_number;
        cbn -[Nat.div]; lia). 
      replace_bool_lia (l / 2 <? n) true.
      apply H0; lia.
    }
    assert (Hbig : perm_eq (n * (n - 1))
      (fun i => deg (idx_to_edge (S n) ((n * 2 + i) / 2)))
      (fun k0 => deg (1 + fst (idx_to_edge n (k0 / 2)), 
      1 + snd (idx_to_edge n (k0 / 2))))). 1: {
      intros l Hl.
      rewrite idx_to_edge_succ by (apply Nat.Div0.div_lt_upper_bound;
        rewrite (Nat.mul_comm 2), triangle_number_exact; nia).
      rewrite Nat.div_add_l by lia.
      replace_bool_lia (n + l / 2 <? n) false.
      now rewrite add_sub'.
    }
    f_equal; cycle 1.
    + replace (S n * (S n - 1)) with ((n*2) + n * (n - 1)) by (nia).
      rewrite Nsum_offset_add 
        by (replace (n*2+n*(n-1)) with (S n*(S n-1)) by nia; lia).
      rewrite Hsmall.
      cbn [Nat.ltb Nat.leb].
      rewrite Nat.sub_0_r.
      apply equal_f.
      now rewrite Hbig.
    + replace (S n * (S n - 1)) with ((n*2) + n * (n - 1)) by (nia).
      rewrite Nsum_index_add 
        by (replace (n*2+n*(n-1)) with (S n*(S n-1)) by nia; lia).
      rewrite Hsmall.
      cbn [Nat.ltb Nat.leb].
      rewrite Nat.sub_0_r.
      bdestruct (n =? 0); [subst; cbn in *; lia|].
      etransitivity;
      [apply (f_equal2 big_sum); [reflexivity|]|
        apply big_sum_eq_bounded].
      Abort.

(* Old: *)


(* Definition reps_to_front_perm n :=
  fun k => if n * n <=? k then k else
  if k mod n =? 0 (* is in front of its section *) 
  then k / n 
  else k + n - S (k / n).

Definition reps_from_front_perm n :=
  fun k => if n * n <=? k then k else
  if k <? n (* k / m =? 0 *)
  then n * (k mod n) 
  else k - (n - S ((k - n) / (n - 1))).

Lemma reps_to_front_perm_WF n : WF_Perm (n * n) (reps_to_front_perm n).
Proof. intros k Hk. unfold reps_to_front_perm. bdestructΩ'. Qed.

Lemma reps_from_front_perm_WF n : WF_Perm (n * n) (reps_from_front_perm n).
Proof. intros k Hk. unfold reps_from_front_perm. bdestructΩ'. Qed.

#[export] Hint Resolve reps_to_front_perm_WF 
  reps_from_front_perm_WF : WF_Perm_db. 

Lemma reps_to_front_perm_defn n : 
  perm_eq (n * n)
    (reps_to_front_perm n)
    (fun k => if k mod n =? 0 then k / n else k + n - S (k / n)).
Proof.
  intros k Hk.
  unfold reps_to_front_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma reps_from_front_perm_defn n : 
  perm_eq (n * n)
    (reps_from_front_perm n)
    (fun k => if k <? n then n * (k mod n) else k - (n - S ((k - n) / (n - 1)))).
Proof.
  intros k Hk.
  unfold reps_from_front_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma reps_to_front_perm_bounded n : 
  perm_bounded (n * n) (reps_to_front_perm n).
Proof.
  intros k Hk.
  rewrite reps_to_front_perm_defn by auto.
  bdestruct_one.
  - show_moddy_lt.
  - bdestruct (k <? n * (n - 1)); [lia|].
    enough (k / n >= (n - 1)) by lia.
    apply Nat.div_le_lower_bound; lia.
Qed.

Lemma reps_from_front_perm_bounded n : 
  perm_bounded (n * n) (reps_from_front_perm n).
Proof.
  intros k Hk.
  rewrite reps_from_front_perm_defn by auto.
  bdestruct_one.
  - show_moddy_lt.
  - lia.
Qed.

#[export] Hint Resolve reps_to_front_perm_bounded
  reps_from_front_perm_bounded : perm_bounded_db.

(* Lemma reps_from_front_perm_spec n : 
  perm_eq (n * n) (reps_to_front_perm n) 
    (enlarge_permutation (2 * n) (kron_comm_perm n 2)
      (fun k => if k mod 2 =? 0 then 1 else (n - 1))).
Proof.
  bdestruct (n =? 0); [subst; intros k Hk; lia|].
  assert (Heq : big_sum (fun k => if k mod 2 =? 0 then 1 else (n - 1)) (2 * n)
   = n * n).
  1: {
    change (fun k => if k mod 2 =? 0 then 1 else n - 1) with 
      (fun k => (fun (kdiv2 kmod2 : nat) => if kmod2 =? 0 then 1 else n - 1)
        (k / 2) (k mod 2)). 
    rewrite <- big_sum_double_sum.
    rewrite big_sum_constant.
    simpl.
    rewrite times_n_nat.
    nia.
  }
  rewrite reps_to_front_perm_defn.
  rewrite <- Heq.
  rewrite enlarge_permutation_defn.
  rewrite Heq.
  intros k Hk. *)

Lemma reps_to_from_front_inv n : 
  reps_to_front_perm n ∘ reps_from_front_perm n = idn.
Proof.
  eq_by_WF_perm_eq (n * n).
  rewrite reps_to_front_perm_defn, reps_from_front_perm_defn.
  intros k Hk.
  unfold compose.
  bdestruct (k <? n).
  - rewrite Nat.mul_comm, Nat.Div0.mod_mul by lia.
    cbn [Nat.eqb].
    rewrite Nat.div_mul by lia.
    apply Nat.mod_small; lia.
  - assert (n <> 1) by lia.
    assert (2 <= n) by lia.
    assert ((k - n) / (n - 1) < n) by  
      (apply Nat.Div0.div_lt_upper_bound; lia).
    replace (k - (n - S ((k - n) / (n - 1)))) with 
      (((k - n) / (n - 1)) * n + ((k - n) mod (n - 1) + 1))
      by (pose proof (Nat.div_mod_eq (k - n) (n - 1)); lia).
    rewrite if_false.
    + rewrite Nat.div_add_l by lia.
      rewrite (Nat.div_small (_ + 1)) 
        by (pose proof (Nat.mod_upper_bound (k - n) (n - 1)); lia).
      rewrite Nat.add_0_r.
      pose proof (Nat.div_mod_eq (k - n) (n - 1)); lia.
    + rewrite Nat.eqb_neq.
      rewrite mod_add_l.
      rewrite (Nat.mod_small (_ + 1)) 
        by (pose proof (Nat.mod_upper_bound (k - n) (n - 1)); lia).
      lia.
Qed.

Lemma reps_from_front_permutation n : 
  permutation (n * n) (reps_from_front_perm n).
Proof.
  apply permutation_iff_surjective.
  apply surjective_of_injective_and_bounded.
  split; [|auto_perm].
  intros k l Hk Hl.
  intros Heq.
  apply (f_equal (reps_to_front_perm n)) in Heq.
  pose proof (equal_f (reps_to_from_front_inv n) k).
  pose proof (equal_f (reps_to_from_front_inv n) l).
  unfold compose in *.
  congruence.
Qed.

#[export] Hint Resolve reps_from_front_permutation : perm_db.

Lemma reps_from_front_perm_inv n : 
  perm_eq (n * n) 
    (perm_inv (n * n) (reps_from_front_perm n))
    (reps_to_front_perm n).
Proof.
  rewrite <- (compose_idn_l (perm_inv _ _)).
  rewrite compose_perm_inv_r by auto_perm.
  now rewrite reps_to_from_front_inv.
Qed.

Lemma reps_to_front_permutation n : 
  permutation (n * n) (reps_to_front_perm n).
Proof.
  rewrite <- reps_from_front_perm_inv.
  auto_perm.
Qed.

#[export] Hint Resolve reps_to_front_permutation : perm_db.

Lemma reps_to_front_perm_inv n : 
  perm_eq (n * n) 
    (perm_inv (n * n) (reps_to_front_perm n))
    (reps_from_front_perm n).
Proof.
  rewrite perm_inv_perm_eq_iff by auto_perm.
  now rewrite reps_from_front_perm_inv.
Qed.

Lemma reps_from_to_front_inv n : 
  reps_from_front_perm n ∘ reps_to_front_perm n = idn.
Proof.
  eq_by_WF_perm_eq (n * n).
  rewrite <- reps_from_front_perm_inv.
  auto_perm.
Qed.



Fixpoint block_to_pairs_perm n := 
  match n with 
  | O => idn
  | S n' => 
    stack_perms (n' * 2) (n' * (n' - 1))
      (kron_comm_perm n' 2) 
      (block_to_pairs_perm n')
    ∘ stack_perms n' (n' * n') idn 
      (reps_to_front_perm n')
  end.

Lemma block_to_pairs_permutation n : 
  permutation (n * (n - 1)) (block_to_pairs_perm n).
Proof.
  induction n; [cbn; auto_perm|].
  cbn [block_to_pairs_perm].
  assert (S n * (S n - 1) = n * 2 + n * (n - 1)) by nia.
  auto_perm.
Qed.

#[export] Hint Resolve block_to_pairs_permutation : perm_db.

Lemma block_to_pairs_perm_spec n i j (Hi : i < j) (Hj : j < n) : 
  {(k, l) : nat * nat | k < n * (n - 1) /\ l < n * (n - 1) /\
  k / (n - 1) = i /\ l / (n - 1) = j /\
  block_to_pairs_perm n k + 1 = block_to_pairs_perm n l }.
Proof.
  induction n; [|destruct n];
  [lia..|].



 *)
