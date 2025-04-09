(* We construct ZX representations using ZXbiperm's 
   and stacks of spiders. These are an intermediate 
   representation between inductive ZX diagrams and 
   true graph representations of ZX diagrams, which
   while more amenable to graph-type reasoning than
   this IR are much harder to construct directly. 
*)
Require Export ZXCore.
Require Export ZXpermFacts.
Require Import BipermAux.
Require Import BigPerm.
Import Kronecker.
Import Setoid.
Require Export CoreRules.
Require Import ZXpermcomp.
Require Import Bipermutations BipermutationMatrices NFBiperm.
Require Import ZXbiperm.
Import ComposeRules.



Open Scope nat_scope.




(* Section ArbitraryCups. *)

Local Open Scope prg.

Definition swap_to_0_1_perm (k l n : nat) := 
  fun a => if n <=? a then a else
  if a =? min k l then 0 else
  if a =? max k l then 1 else
  if a <? min k l then a + 2 else
  if a <? max k l then a + 1 else 
  a.

Definition swap_from_0_1_perm (k l n : nat) :=
  fun a => if n <=? a then a else
  if a =? 0 then min k l else
  if a =? 1 then max k l else
  if a <? min k l + 2 then a - 2 else
  if a <? max k l + 1 then a - 1 else 
  a.

Lemma swap_to_0_1_perm_WF k l n : 
  WF_Perm n (swap_to_0_1_perm k l n).
Proof.
  apply make_WF_Perm_WF.
Qed.

#[export] Hint Resolve swap_to_0_1_perm_WF : WF_Perm_db.

Lemma swap_from_0_1_perm_WF k l n : 
  WF_Perm n (swap_from_0_1_perm k l n).
Proof.
  apply make_WF_Perm_WF.
Qed.

#[export] Hint Resolve swap_from_0_1_perm_WF : WF_Perm_db.

Lemma swap_to_0_1_perm_defn k l n : 
  perm_eq n (swap_to_0_1_perm k l n)
  (fun a => if a =? min k l then 0 else if a =? max k l then 1 else
  if a <? min k l then a + 2 else if a <? max k l then a + 1 else a).
Proof.
  apply make_WF_Perm_perm_eq.
Qed.

Lemma swap_from_0_1_perm_defn k l n : 
  perm_eq n (swap_from_0_1_perm k l n)
  (fun a => if a =? 0 then min k l else if a =? 1 then max k l else
  if a <? min k l + 2 then a - 2 else if a <? max k l + 1 then a - 1 else a).
Proof.
  apply make_WF_Perm_perm_eq.
Qed.

Lemma swap_to_0_1_perm_comm k l n : 
  swap_to_0_1_perm k l n = swap_to_0_1_perm l k n.
Proof.
  eq_by_WF_perm_eq n.
  intros a Ha.
  unfold swap_to_0_1_perm.
  now rewrite Nat.min_comm, Nat.max_comm.
Qed.

Lemma swap_from_0_1_perm_comm k l n : 
  swap_from_0_1_perm k l n = swap_from_0_1_perm l k n.
Proof.
  eq_by_WF_perm_eq n.
  intros a Ha.
  unfold swap_from_0_1_perm.
  now rewrite Nat.min_comm, Nat.max_comm.
Qed.

Lemma swap_to_0_1_perm_defn_alt k l n (Hkl : k <> l)
  (Hk : k < n) (Hl : l < n) : 
  swap_to_0_1_perm k l n = 
  stack_perms (1 + max k l) (n - (1 + max k l))
    (stack_perms 1 (max k l) idn (big_swap_perm (max k l - 1) 1)) idn ∘
  stack_perms (min k l + 1) (n - (min k l + 1))
    (big_swap_perm (min k l) 1) idn.
Proof.
  eq_by_WF_perm_eq n.
  rewrite 2!stack_perms_WF_idn by auto_perm.
  rewrite swap_to_0_1_perm_defn.
  intros a Ha.
  unfold compose, big_swap_perm, stack_perms.
  bdestructΩ'_with ltac:(try lia).
Qed.

Lemma swap_to_0_1_perm_defn_alt_simple k l n 
  (Hkl : k <> l) (Hk : k < n) (Hl : l < n) : 
  swap_to_0_1_perm k l n = 
  stack_perms 1 (max k l) idn (big_swap_perm (max k l - 1) 1) ∘
  big_swap_perm (min k l) 1.
Proof.
  rewrite swap_to_0_1_perm_defn_alt by auto.
  now rewrite 2!stack_perms_WF_idn by auto_perm.
Qed.

Lemma swap_from_0_1_perm_defn_alt k l n (Hkl : k <> l)
  (Hk : k < n) (Hl : l < n) : 
  swap_from_0_1_perm k l n = 
  stack_perms (min k l + 1) (n - (min k l + 1))
    (big_swap_perm 1 (min k l)) idn ∘
  stack_perms (1 + max k l) (n - (1 + max k l))
    (stack_perms 1 (max k l) idn (big_swap_perm 1 (max k l - 1))) idn.
Proof.
  eq_by_WF_perm_eq n.
  rewrite 2!stack_perms_WF_idn by auto_perm.
  rewrite swap_from_0_1_perm_defn.
  intros a Ha.
  unfold compose, big_swap_perm, stack_perms.
  bdestructΩ'_with ltac:(try lia).
Qed.

Lemma swap_from_0_1_perm_defn_alt_simple k l n 
  (Hkl : k <> l) (Hk : k < n) (Hl : l < n) : 
  swap_from_0_1_perm k l n = 
  big_swap_perm 1 (min k l) ∘
  stack_perms 1 (max k l) idn (big_swap_perm 1 (max k l - 1)).
Proof.
  rewrite swap_from_0_1_perm_defn_alt by auto.
  now rewrite 2!stack_perms_WF_idn by auto_perm.
Qed.

Lemma swap_to_0_1_perm_permutation k l n (Hk : k < n) (Hl : l < n) 
  (Hkl : k <> l) : 
  permutation n (swap_to_0_1_perm k l n).
Proof.
  rewrite swap_to_0_1_perm_defn_alt by auto.
  auto_perm.
Qed.

#[export] Hint Resolve swap_to_0_1_perm_permutation : perm_db.

Lemma swap_from_0_1_perm_permutation k l n (Hk : k < n) (Hl : l < n)
  (Hkl : k <> l) : 
  permutation n (swap_from_0_1_perm k l n).
Proof.
  rewrite swap_from_0_1_perm_defn_alt by auto.
  auto_perm.
Qed.

#[export] Hint Resolve swap_from_0_1_perm_permutation : perm_db.

Lemma swap_to_from_0_1_perm_inverse k l n 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  swap_to_0_1_perm k l n ∘ swap_from_0_1_perm k l n = idn.
Proof.
  eq_by_WF_perm_eq n.
  rewrite swap_to_0_1_perm_defn, swap_from_0_1_perm_defn.
  intros a Ha.
  unfold compose.
  bdestructΩ'_with ltac:(try lia).
Qed.

Lemma swap_from_to_0_1_perm_inverse k l n 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  swap_from_0_1_perm k l n ∘ swap_to_0_1_perm k l n = idn.
Proof.
  eq_by_WF_perm_eq n.
  rewrite swap_from_0_1_perm_defn, swap_to_0_1_perm_defn.
  intros a Ha.
  unfold compose.
  bdestructΩ'_with ltac:(try lia).
Qed.

Lemma swap_to_0_1_perm_inv k l n (Hk : k < n) (Hl : l < n) 
  (Hkl : k <> l) : 
  perm_eq n (perm_inv n (swap_to_0_1_perm k l n))
    (swap_from_0_1_perm k l n).
Proof.
  perm_eq_by_inv_inj (swap_to_0_1_perm k l n) n.
  now rewrite swap_from_to_0_1_perm_inverse.
Qed.

Lemma swap_to_0_1_perm_inv' k l n (Hk : k < n) (Hl : l < n) 
  (Hkl : k <> l) : 
  perm_inv' n (swap_to_0_1_perm k l n)
  = swap_from_0_1_perm k l n.
Proof. 
  eq_by_WF_perm_eq n.
  rewrite perm_inv'_eq.
  now apply swap_to_0_1_perm_inv.
Qed.

Lemma swap_from_0_1_perm_inv k l n (Hk : k < n) (Hl : l < n) 
  (Hkl : k <> l) : 
  perm_eq n (perm_inv n (swap_from_0_1_perm k l n))
    (swap_to_0_1_perm k l n).
Proof.
  perm_eq_by_inv_inj (swap_from_0_1_perm k l n) n.
  now rewrite swap_to_from_0_1_perm_inverse.
Qed.

Lemma swap_from_0_1_perm_inv' k l n (Hk : k < n) (Hl : l < n) 
  (Hkl : k <> l) : 
  perm_inv' n (swap_from_0_1_perm k l n)
  = swap_to_0_1_perm k l n.
Proof. 
  eq_by_WF_perm_eq n.
  rewrite perm_inv'_eq.
  now apply swap_from_0_1_perm_inv.
Qed.



(* FIXME: TODO: Replace "arb_cap" with "pad_cap" ? *)
Definition arb_cap_biperm k l n :=
  fun a => if n + (n - 2) <=? a then a else
  if (a <? k) && (a <? l) then n + a else
  if a =? k then l else if a =? l then k else
  if (a <? k) ⊕ (a <? l) then n + (a - 1) else
  if a <? n then n + (a - 2) else
  if (a <? n + k) && (a <? n + l) then a - n else
  if (a <? n + k - 1) ⊕ (a <? n + l - 1) then a - (n - 1) else
  a - (n - 2).

Lemma arb_cap_biperm_defn k l n :
  perm_eq (n + (n - 2)) (arb_cap_biperm k l n) 
  (fun a => 
    if (a <? k) && (a <? l) then n + a else
    if a =? k then l else if a =? l then k else
    if (a <? k) ⊕ (a <? l) then n + (a - 1) else
    if a <? n then n + (a - 2) else
    if (a <? n + k) && (a <? n + l) then a - n else
    if (a <? n + k - 1) ⊕ (a <? n + l - 1) then a - (n - 1) else
    a - (n - 2)).
Proof.
  apply make_WF_Perm_perm_eq.
Qed.

Lemma arb_cap_biperm_bounded k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_bounded (n + (n - 2)) (arb_cap_biperm k l n).
Proof.
  intros a Ha.
  rewrite arb_cap_biperm_defn by auto.
  bdestructΩ'_with ltac:(try lia).
Qed.

#[export] Hint Resolve arb_cap_biperm_bounded : perm_bounded_db.

Lemma arb_cap_biperm_WF k l n : 
  WF_Perm (n + (n - 2)) (arb_cap_biperm k l n).
Proof.
  apply make_WF_Perm_WF.
Qed.

#[export] Hint Resolve arb_cap_biperm_WF : WF_Perm_db.

Lemma arb_cap_biperm_defn_sym k l n : 
  arb_cap_biperm k l n = 
  make_WF_Perm (n + (n - 2)) (fun a =>
  if a <? min k l then n + a else
  if a =? min k l then max k l else 
  if a =? max k l then min k l else
  if a <? max k l then n + (a - 1) else
  if a <? n then n + (a - 2) else
  if a <? n + min k l then a - n else
  if a <? n + max k l - 1 then a - (n - 1) else
  a - (n - 2)).
Proof.
  eq_by_WF_perm_eq (n + (n - 2)).
  rewrite make_WF_Perm_perm_eq, arb_cap_biperm_defn.
  intros a Ha.
  bdestructΩ'_with ltac:(try lia).
Qed.

Lemma arb_cap_biperm_swaps k l n a (Ha : a = k \/ a = l) 
  (Han : a < n + (n - 2)) : 
  arb_cap_biperm k l n a = if a =? k then l else k.
Proof.
  rewrite arb_cap_biperm_defn by auto.
  replace_bool_liaP ((a <? k) && (a <? l)) false.
  blia_rec.
Qed.

Lemma arb_cap_biperm_comm k l n : 
  arb_cap_biperm k l n = arb_cap_biperm l k n.
Proof.
  eq_by_WF_perm_eq _.
  rewrite 2!arb_cap_biperm_defn_sym.
  rewrite 2!make_WF_Perm_perm_eq.
  intros a Ha.
  now rewrite (Nat.max_comm l k), (Nat.min_comm l k).
Qed.

Lemma arb_cap_biperm_to_max_min k l n : 
  arb_cap_biperm k l n = arb_cap_biperm (Nat.min k l) (Nat.max k l) n.
Proof.
  bdestruct (k <? l).
  - f_equal; lia.
  - rewrite arb_cap_biperm_comm.
    f_equal; lia.
Qed.

Import Modulus.

Lemma arb_cap_biperm_defn_alt k l n 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  arb_cap_biperm k l n = 
  biperm_compose_perm_l n (n - 2) 
  (stack_biperms 2 0 (n - 2) (n - 2) 
    (n_m_cup_cap 1 0) (idn_biperm (n - 2)))
  (swap_from_0_1_perm k l n).
Proof.
  eq_by_WF_perm_eq _.
  rewrite biperm_compose_perm_l_defn.
  rewrite stack_biperms_0_out.
  rewrite perm_inv_stack_perms, idn_inv by auto_perm.
  rewrite swap_from_0_1_perm_inv by auto.
  rewrite 2!stack_perms_WF_idn by auto_perm.
  intros a Ha.
  rewrite arb_cap_biperm_defn_sym, make_WF_Perm_perm_eq by auto.
  bdestructΩ'_with ltac:(try lia);
  unfold swap_from_0_1_perm, swap_to_0_1_perm.
  - unfold compose at 1.
    rewrite Nat.eqb_refl by lia.
    if_false_lia.
    unfold compose;
    cbn.
    now if_false_lia.
  - unfold compose at 1.
    rewrite Nat.eqb_refl by lia.
    do 2 if_false_lia. 
    change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
    cbn.
    unfold compose.
    cbn.
    now if_false_lia.
  - unfold compose at 1.
    do 3 if_false_lia; if_true_lia.
    change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
    rewrite stack_perms_right by lia.
    rewrite idn_biperm_defn by lia.
    if_true_lia.
    unfold compose.
    if_true_lia.
    lia.
  - unfold compose at 1.
    do 4 if_false_lia; if_true_lia.
    change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
    rewrite stack_perms_right by lia.
    rewrite idn_biperm_defn by lia.
    if_true_lia.
    unfold compose.
    if_true_lia.
    lia.
  - unfold compose at 1.
    do 5 if_false_lia.
    change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
    rewrite stack_perms_right by lia.
    rewrite idn_biperm_defn by lia.
    if_true_lia.
    unfold compose.
    if_true_lia.
    lia.
  - unfold compose at 1.
    if_true_lia.
    change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
    rewrite stack_perms_right by lia.
    rewrite idn_biperm_defn by lia.
    if_false_lia.
    unfold compose.
    do 3 if_false_lia; if_true_lia.
    lia.
  - unfold compose at 1.
    if_true_lia.
    change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
    rewrite stack_perms_right by lia.
    rewrite idn_biperm_defn by lia.
    if_false_lia.
    unfold compose.
    do 4 if_false_lia; if_true_lia.
    lia.
  - unfold compose at 1.
    if_true_lia.
    change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
    rewrite stack_perms_right by lia.
    rewrite idn_biperm_defn by lia.
    if_false_lia.
    unfold compose.
    do 5 if_false_lia.
    lia.
Qed.

Lemma arb_cap_bipermutation k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  bipermutation (n + (n - 2)) (arb_cap_biperm k l n).
Proof.
  rewrite arb_cap_biperm_defn_alt by lia.
  auto_biperm.
Qed.

#[export] Hint Resolve arb_cap_bipermutation : biperm_db.




Lemma swap_from_0_1_perm_compose_perm_l k l n f (Hf : permutation n f) 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_eq n (f ∘ swap_from_0_1_perm k l n)
  (swap_from_0_1_perm (f k) (f l) n ∘
  stack_perms 2 (n - 2) 
    (if f (min k l) <? f (max k l) then idn else swap_2_perm)
    (contract_biperm k l f)).
Proof.
  assert (perm_bounded n (stack_perms 2 (n - 2) 
    (if f (min k l) <? f (max k l) then idn else swap_2_perm) 
    (contract_biperm k l f))) 
    by auto_perm.
  rewrite 2!swap_from_0_1_perm_defn.
  intros a Ha.
  unfold compose at 1.
  rewrite !(if_dist _ _ _ f).
  bdestruct (a <? 2).
  - bdestruct (a =? 0).
    + subst.
      change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
      cbn.
      rewrite dist_if.
      cbn.
      rewrite if_dist.
      unfold compose.
      cbn.
      rewrite min_ltb, max_ltb.
      bdestruct (k <? l);
      blia_rec.
    + replace a with 1 in * by lia.
      change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
      cbn.
      rewrite dist_if.
      cbn.
      rewrite if_dist.
      unfold compose.
      cbn.
      rewrite min_ltb, max_ltb.
      bdestruct (k <? l);
      blia_rec.
  - do 2 if_false_lia.
    change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
    rewrite stack_perms_right by lia.
    rewrite (Nat.add_comm (contract_biperm _ _ _ _) 2).
    unfold compose.
    change (_ =? 0) with false.
    change (_ =? 1) with false.
    cbn match.
    rewrite (Nat.add_comm 2).
    rewrite Nat.add_sub.
    pattern (contract_biperm k l f (a - 2)).
    match goal with |- ?Q ?x => set (P := Q) end.
    rewrite contract_biperm_to_min_max.
    unfold contract_perm.
    replace_bool_lia (min k l <? max k l) true.
    assert (f k <> f l) 
        by (rewrite (permutation_eq_iff _ _ Hf); lia).
    replace (a - 2 + 1) with (a - 1) in * by lia.
    bdestruct (a - 2 <? min k l);
    [|bdestruct (a - 1 <? min k l);
    [|bdestruct (a - 1 <? max k l)]].
    + replace_bool_lia (a - 2 <? max k l) true.
      subst P.
      replace_bool_lia (a <? min k l + 2) true.
      assert (f (a - 2) <> f (min k l)) 
        by (rewrite (permutation_eq_iff _ _ Hf); lia).
      assert (f (a - 2) <> f (max k l)) 
        by (rewrite (permutation_eq_iff _ _ Hf); lia).
      rewrite min_ltb, max_ltb in *.
      bdestruct (k <? l).
      * rewrite min_ltb, max_ltb.
        bdestructΩ'_with ltac:(try lia).
      * rewrite min_ltb, max_ltb.
        bdestructΩ'_with ltac:(try lia).
    + replace_bool_lia (a - 1 <? max k l) true.
      subst P.
      replace_bool_lia (a <? min k l + 2) false;
      replace_bool_lia (a <? max k l + 1) true.
      assert (f (a - 1) <> f (min k l)) 
        by (rewrite (permutation_eq_iff _ _ Hf); lia).
      assert (f (a - 1) <> f (max k l)) 
        by (rewrite (permutation_eq_iff _ _ Hf); lia).
      rewrite min_ltb, max_ltb in *.
      bdestruct (k <? l).
      * rewrite min_ltb, max_ltb.
        bdestructΩ'_with ltac:(try lia).
      * rewrite min_ltb, max_ltb.
        bdestructΩ'_with ltac:(try lia).
    + subst P.
      replace_bool_lia (a <? min k l + 2) false;
      replace_bool_lia (a <? max k l + 1) true.
      assert (f (a - 1) <> f (min k l)) 
        by (rewrite (permutation_eq_iff _ _ Hf); lia).
      assert (f (a - 1) <> f (max k l)) 
        by (rewrite (permutation_eq_iff _ _ Hf); lia).
      rewrite min_ltb, max_ltb in *.
      bdestruct (k <? l).
      * rewrite min_ltb, max_ltb.
        bdestructΩ'_with ltac:(try lia).
      * rewrite min_ltb, max_ltb.
        bdestructΩ'_with ltac:(try lia).
    + replace (a - 1 + 1) with a by lia.
      subst P.
      replace_bool_lia (a <? min k l + 2) false;
      replace_bool_lia (a <? max k l + 1) false.
      assert (f (a) <> f (min k l)) 
        by (rewrite (permutation_eq_iff _ _ Hf); lia).
      assert (f (a) <> f (max k l)) 
        by (rewrite (permutation_eq_iff _ _ Hf); lia).
      rewrite min_ltb, max_ltb in *.
      bdestruct (k <? l).
      * rewrite min_ltb, max_ltb.
        bdestructΩ'_with ltac:(try lia).
      * rewrite min_ltb, max_ltb.
        bdestructΩ'_with ltac:(try lia).
Qed.




Lemma swap_to_0_1_perm_compose_perm_r k l n f (Hf : permutation n f) 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_eq n (swap_to_0_1_perm k l n ∘ f)
  (stack_perms 2 (n - 2) 
    (if perm_inv n f (min k l) <? perm_inv n f (max k l) 
    then idn else swap_2_perm)
    (contract_biperm (perm_inv n f k) (perm_inv n f l) f)
  ∘ swap_to_0_1_perm (perm_inv n f k) (perm_inv n f l) n).
Proof.
  assert (perm_inv n f k <> perm_inv n f l) by 
    (apply (@permutation_neq n); auto_perm).
  assert (permutation n (stack_perms 2 (n - 2) 
    (if perm_inv n f (min k l) <? perm_inv n f (max k l) 
    then idn else swap_2_perm) (contract_biperm k l f))) by auto_perm.
  assert (permutation n
    (swap_to_0_1_perm (perm_inv n f k) (perm_inv n f l) n)) by auto_perm.
    assert (permutation n (swap_to_0_1_perm k l n)) by auto_perm.
  apply perm_inv_inj;
  [auto_perm..|].
  rewrite 2!perm_inv_compose by auto_perm.
  rewrite 2!swap_to_0_1_perm_inv by auto_perm.
  rewrite swap_from_0_1_perm_compose_perm_l by auto_perm.
  apply compose_perm_eq_proper_r.
  rewrite perm_inv_stack_perms_change_dims by (lia + auto_perm).
  rewrite <- (perm_inv'_eq 2).
  rewrite (if_dist _ _ _ (perm_inv' 2)).
  rewrite idn_inv', swap_2_perm_inv'.
  rewrite contract_biperm_inv by auto_perm.
  now rewrite 2!perm_inv_is_rinv_of_permutation by auto.
Qed.




Lemma arb_cap_biperm_compose_perm_l k l n f (Hf : permutation n f) 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  biperm_compose_perm_l n (n - 2) (arb_cap_biperm k l n) f =
  biperm_compose_perm_r n (n - 2) (arb_cap_biperm (f k) (f l) n) 
    (contract_biperm k l f).
Proof.
  eq_by_WF_perm_eq _.
  assert (f k <> f l) by (apply (permutation_neq Hf); auto_perm).
  rewrite 2!arb_cap_biperm_defn_alt by auto_perm.
  rewrite biperm_compose_perm_l_compose by auto_biperm.
  rewrite swap_from_0_1_perm_compose_perm_l at 1 by auto.
  rewrite <- biperm_compose_perm_l_compose by auto_biperm.
  rewrite <- biperm_compose_perm_l_r_swap by auto_perm.
  ereflexivity.
  apply biperm_compose_perm_l_eq_of_perm_eq; [|reflexivity].
  rewrite biperm_compose_perm_l_defn, 
    biperm_compose_perm_r_defn.
  rewrite stack_perms_assoc_fwd_change_dims by lia.
  rewrite stack_biperms_0_out.
  rewrite 2!(perm_inv_stack_perms_change_dims (n + (n - 2)))
    by (lia + auto_perm).
  rewrite Combinators.compose_assoc, 2!stack_perms_compose by auto_biperm.
  assert (Hrw : perm_eq n idn (stack_perms 2 (n - 2) idn idn))
    by now rewrite stack_perms_idn_idn.
  rewrite idn_inv.
  rewrite Hrw at 5 6.
  rewrite 2!stack_perms_assoc_fwd_change_dims by (lia + auto_perm).
  rewrite Combinators.compose_assoc, 2!stack_perms_compose by auto_biperm.
  ereflexivity.
  apply stack_perms_perm_eq_to_eq_proper.
  - replace (n_m_cup_cap 1 0) with swap_2_perm 
      by (eq_by_WF_perm_eq (1 + 1 + (0 + 0)); 
        print_goal; by_perm_cell; reflexivity).
    rewrite <- perm_inv'_eq.
    rewrite (if_dist _ _ _ (perm_inv' 2)).
    rewrite idn_inv', swap_2_perm_inv'.
    bdestruct_one; [reflexivity|now rewrite swap_2_perm_invol].
  - unfold idn_biperm.
    rewrite <- 2!Combinators.compose_assoc.
    rewrite 2!stack_perms_big_swap_natural by auto_perm.
    rewrite 2!Combinators.compose_assoc.
    apply compose_perm_eq_proper_r.
    rewrite perm_inv_stack_perms, idn_inv by auto_perm.
    rewrite 2!stack_perms_compose by auto_perm.
    now rewrite perm_inv_perm_inv by auto_perm.
Qed.

Lemma arb_cap_biperm_0_1 :
  arb_cap_biperm 0 1 2 = swap_2_perm.
Proof.
  eq_by_WF_perm_eq _.
  cbn.
  by_perm_cell; reflexivity.
Qed.





Lemma arb_cap_biperm_add_r k l n m 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) :
  arb_cap_biperm k l (n + m) = 
  stack_biperms n (n - 2) m m (arb_cap_biperm k l n) (idn_biperm m).
Proof.
  eq_by_WF_perm_eq _;
  [eapply WF_Perm_monotone; [auto_perm|lia]..|].
  rewrite arb_cap_biperm_defn_alt by lia.
  replace (n + m - 2) with (n - 2 + m) by lia.
  rewrite <- stack_biperms_idn_idn.
  rewrite <- stack_biperms_assoc by auto_biperm.
  rewrite arb_cap_biperm_defn_alt by auto.
  rewrite <- (biperm_compose_perm_l_idn m m (idn_biperm m)) at 2
    by auto_perm.
  rewrite <- biperm_compose_perm_l_stack by auto_biperm.
  ereflexivity.
  apply biperm_compose_perm_l_eq_of_perm_eq;
  [ereflexivity; f_equal; lia|].
  rewrite swap_from_0_1_perm_defn.
  rewrite stack_perms_WF_idn by auto_perm.
  unfold swap_from_0_1_perm.
  intros a Ha.
  bdestructΩ'_with ltac:(try lia).
Qed.

Lemma swap_from_0_1_perm_add_all n m k l 
  (Hk : k < m) (Hl : l < m) (Hkl : k <> l) : 
  swap_from_0_1_perm (n + k) (n + l) (n + m) = 
  stack_perms n m idn (swap_from_0_1_perm k l m) ∘
  stack_perms (n + 2) (m - 2) (big_swap_perm 2 n) idn.
Proof.
  eq_by_WF_perm_eq _.
  rewrite stack_perms_WF_idn by auto_perm.
  rewrite swap_from_0_1_perm_defn.
  intros a Ha.
  unfold compose.
  bdestruct (a <? 2); [|do 2 if_false_lia; bdestruct (a <? n + 2)].
  - rewrite big_swap_perm_left by auto.
    rewrite stack_perms_right by lia.
    rewrite Nat.add_sub.
    rewrite swap_from_0_1_perm_defn by lia.
    destruct (ltac:(lia) : a = 0 \/ a = 1) as [-> | ->];
    cbn; lia.
  - rewrite big_swap_perm_right by lia.
    if_true_lia.
    now rewrite stack_perms_left by lia.
  - rewrite big_swap_perm_WF by lia.
    rewrite stack_perms_right by lia.
    rewrite swap_from_0_1_perm_defn by lia.
    symmetry.
    if_false_lia.
    if_false_lia.
    replace_bool_lia (a - n <? min k l + 2) 
      (a <? min (n + k) (n + l) + 2).
    replace_bool_lia (a - n <? max k l + 1) 
      (a <? max (n + k) (n + l) + 1).
    bdestructΩ'_with ltac:(try lia).
Qed.



Lemma matrix_of_arb_cap_biperm k l n 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) :
  matrix_of_biperm n (n - 2) (arb_cap_biperm k l n) = 
  @Mmult (2 ^ (n - 2)) (2^n) (2^n) (⟦ ⊃ ⟧ ⊗ I (2 ^ (n - 2)))
  (perm_to_matrix n (swap_from_0_1_perm k l n)).
Proof.
  rewrite arb_cap_biperm_defn_alt by auto.
  rewrite matrix_of_biperm_compose_perm_l_eq by auto_biperm.
  f_equal.
  rewrite matrix_of_stack_biperms' by lia + auto_biperm.
  rewrite matrix_of_biperm_n_m_cup_cap_1_0, matrix_of_idn_biperm.
  reflexivity.
Qed.



Open Scope nat_scope.
Open Scope prg.



Lemma arb_cap_biperm_add_l_r k l n m 
  (Hk : k < m) (Hl : l < m) (Hkl : k <> l) :
  arb_cap_biperm (n + k) (n + l) (n + m) = 
  stack_biperms n n m (m - 2) (idn_biperm n) (arb_cap_biperm k l m).
Proof.
  eq_by_WF_perm_eq _;
  [eapply WF_Perm_monotone; [auto_perm|lia]..|].
  apply matrix_of_biperm_inj;
  [auto with biperm_db zarith..|].
  rewrite matrix_of_arb_cap_biperm by lia.
  rewrite matrix_of_stack_biperms' by lia + auto_biperm.
  rewrite matrix_of_idn_biperm, matrix_of_arb_cap_biperm by lia.
  rewrite swap_from_0_1_perm_add_all by auto.
  rewrite perm_to_matrix_compose by auto_perm.
  rewrite perm_to_matrix_of_stack_perms' by lia + auto_perm.
  rewrite perm_to_matrix_of_stack_perms by auto_perm.
  rewrite perm_to_matrix_big_swap_perm' by lia.
  rewrite 2!perm_to_matrix_idn.
  replace (n + m - 2) with (n + (m - 2)) by lia.
  rewrite Nat.pow_add_r, <- id_kron.
  rewrite <- Mmult_assoc.
  rewrite <- kron_assoc by auto_wf.
  restore_dims.
  rewrite kron_mixed_product, kron_comm_commutes_r, kron_comm_1_l,
    Mmult_1_l by auto_wf.
  restore_dims.
  rewrite Mmult_1_l, kron_assoc by auto_wf.
  restore_dims.
  rewrite kron_id_dist_l by auto_wf.
  restore_dims.
  reflexivity.
Qed.

Definition arb_cup_biperm k l n := 
  flip_biperm n (n - 2) (arb_cap_biperm k l n).

Definition zx_padded_cap_prf {n} (Hn : 2 <= n) : 
  n = 2 + (n - 2) :=
  match n, Hn with 
  | 0, Hn => False_ind _ 
    (proj1 (Nat.le_ngt 2 0) Hn Nat.lt_0_2)
  | 1, Hn => False_ind _ 
    (proj1 (Nat.le_ngt 2 1) Hn Nat.lt_1_2)
  | 2, _ => eq_refl
  | _, _ => eq_refl
  end.
Opaque zx_padded_cap_prf.

Definition zx_padded_cap n : ZX n (n - 2) :=
  match le_lt_dec 2 n with
  | left Hle => 
    cast _ _ (zx_padded_cap_prf Hle) eq_refl 
      (⊃ ↕ n_wire (n - 2))
  | right _ => zx_dummy _ _
  end.

Definition zx_arb_cap k l n :=
  zx_of_perm n (swap_from_0_1_perm k l n) ⟷ zx_padded_cap n.

Lemma zx_arb_cap_comm k l n : 
  zx_arb_cap k l n = zx_arb_cap l k n.
Proof.
  unfold zx_arb_cap.
  now rewrite swap_from_0_1_perm_comm.
Qed.

Lemma zx_padded_cap_zxbiperm n (Hn : 2 <= n) : ZXbiperm (zx_padded_cap n).
Proof.
  unfold zx_padded_cap.
  destruct (le_lt_dec 2 n); 
  [auto with zxbiperm_db zxperm_db|lia].
Qed.

#[export] Hint Resolve zx_padded_cap_zxbiperm : zxbiperm_db.

Lemma zx_arb_cap_zxbiperm k l n (Hn : 2 <= n) : ZXbiperm (zx_arb_cap k l n).
Proof.
  unfold zx_arb_cap.
  auto with zxbiperm_db zxperm_db.
Qed.

#[export] Hint Resolve zx_arb_cap_zxbiperm : zxbiperm_db.

Lemma zx_arb_cap_zxbiperm_alt k l n 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  ZXbiperm (zx_arb_cap k l n).
Proof.
  auto with zxbiperm_db zarith. 
Qed.

#[export] Hint Resolve zx_arb_cap_zxbiperm : zxbiperm_db.

Lemma zx_arb_cap_semantics k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  ⟦ zx_arb_cap k l n ⟧ = matrix_of_biperm n (n - 2) (arb_cap_biperm k l n).
Proof.
  cbn. 
  unfold zx_padded_cap.
  destruct (le_lt_dec 2 n); [|lia].
  simpl_cast_semantics.
  rewrite zx_of_perm_semantics by auto_perm.
  rewrite arb_cap_biperm_defn_alt by auto.
  rewrite matrix_of_biperm_compose_perm_l_eq by auto_biperm.
  rewrite matrix_of_stack_biperms' by (lia + auto_biperm).
  rewrite matrix_of_idn_biperm.
  ereflexivity.
  rewrite zx_stack_spec.
  rewrite n_wire_semantics.
  do 2 f_equal.
  change 2 with (1 + 1).
  rewrite matrix_of_biperm_n_m_cup_cap_0_r.
  now rewrite kron_n_1 by auto_wf.
Qed.

Lemma biperm_of_zx_arb_cap k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  biperm_of_zx (zx_arb_cap k l n) = 
  arb_cap_biperm k l n.
Proof.
  eq_by_WF_perm_eq _.
  assert (ZXbiperm (zx_arb_cap k l n)) by auto with zxbiperm_db zarith.
  apply matrix_of_biperm_inj;
  [auto_biperm..|].
  apply matrix_of_biperm_mat_equiv_of_prop.
  rewrite matrix_of_biperm_of_zx by auto.
  ereflexivity.
  apply zx_arb_cap_semantics; auto.
Qed.

Lemma zx_arb_cap_compose_zx_of_perm_l n f k l 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) 
  (Hf : permutation n f) :
  zx_of_perm n f ⟷ zx_arb_cap k l n ∝
  zx_arb_cap (f k) (f l) n ⟷ zx_of_perm (n - 2) (contract_biperm k l f).
Proof.
  assert (2 <= n) by lia.
  assert (f k <> f l) by (apply (permutation_neq Hf); lia).
  apply ZXbiperm_prop_by_biperm_eq;
  [auto with zxbiperm_db zxperm_db..|].
  rewrite biperm_of_compose_zxperm_l, biperm_of_compose_zxperm_r
    by (auto with zxbiperm_db zxperm_db).
  rewrite 2!biperm_of_zx_arb_cap by auto_perm.
  rewrite 2!perm_of_zx_of_perm_eq by auto_perm.
  ereflexivity.
  apply arb_cap_biperm_compose_perm_l; auto.
Qed.





Lemma zx_arb_cap_f_to_vec k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) f : 
  ⟦ zx_arb_cap k l n ⟧ × f_to_vec n f =
  (b2R (eqb (f k) (f l))) .*
  f_to_vec (n - 2) (fun a =>
  if a <? min k l then f a else 
  if a <? max k l - 1 then f (a + 1) else f (a + 2)).
Proof.
  cbn.
  rewrite Mmult_assoc.
  rewrite zx_of_perm_semantics by auto_perm.
  rewrite perm_to_matrix_permutes_qubits by auto_perm.
  replace (f_to_vec n) with (f_to_vec (2 + (n - 2))) by (f_equal; lia).
  rewrite f_to_vec_split'_eq.
  unfold zx_padded_cap.
  destruct (le_lt_dec 2 n); [|lia].
  simpl_cast_semantics.
  rewrite zx_stack_spec.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite cap_f_to_vec.
  rewrite n_wire_semantics, Mmult_1_l by auto_wf.
  restore_dims.
  distribute_scale.
  rewrite kron_1_l by auto_wf.
  restore_dims.
  f_equal.
  - do 2 f_equal. 
    rewrite 2!swap_from_0_1_perm_defn by lia.
    cbn.
    rewrite min_ltb, max_ltb.
    bdestruct_one; 
    [reflexivity|apply bool_eqb_comm].
  - apply f_to_vec_eq.
    intros a Ha.
    rewrite swap_from_0_1_perm_defn by lia.
    change (_ =? 0) with false.
    change (_ =? 1) with false.
    cbn match.
    rewrite add_sub'.
    rewrite (add_sub' (1 + a) 1 : 2 + a - 1 = 1 + a).
    rewrite 2!(Nat.add_comm _ a).
    rewrite 2!(if_dist _ _ _ f).
    repeat apply f_equal_if; reflexivity + blia_eq.
Qed.


Lemma n_cup_succ_prf {n} : S n + S n - 2 = n + n.
Proof. lia. Qed.

Lemma n_cup_succ_arb_cap_gen n k (Hk : k < S n) : 
  n_cup (S n) ∝
  zx_arb_cap k (S n + k) (S n + S n) ⟷
  cast _ _ n_cup_succ_prf eq_refl (n_cup n).
Proof.
  apply ZX_prop_by_mat_prop.
  ereflexivity.
  apply equal_on_basis_states_implies_equal;
  [auto_wf..|].
  intros f.
  rewrite zx_compose_spec.
  rewrite Mmult_assoc.
  simpl_cast_semantics.
  rewrite zx_arb_cap_f_to_vec by lia.
  restore_dims.
  rewrite Nat.min_l, Nat.max_r by lia.
  restore_dims.
  replace (S n + S n - 2) with (n + n) by lia.
  distribute_scale.
  rewrite 2!n_cup_f_to_vec.
  restore_dims.
  distribute_scale.
  f_equal.
  rewrite <- RtoC_mult, b2R_mult.
  do 2 f_equal.
  apply eq_iff_eq_true.
  rewrite andb_true_iff, eqb_true_iff, 2!forallb_seq0.
  setoid_rewrite eqb_true_iff.
  split.
  - intros Hall.
    split; [now apply Hall|].
    intros a Hs.
    bdestructΩ';
    rewrite Hall by lia;
    f_equal; lia.
  - intros [Hfk Hfnotk].
    intros s Hs.
    bdestruct (s =? k);
    [|bdestruct (s <? k)].
    + subst.
      apply Hfk.
    + generalize (Hfnotk s ltac:(lia)).
      if_true_lia.
      intros ->.
      if_false_lia.
      if_true_lia.
      f_equal; lia.
    + generalize (Hfnotk (s - 1) ltac:(lia)).
      if_false_lia.
      if_true_lia.
      rewrite Nat.sub_add by lia.
      intros ->.
      if_false_lia.
      if_false_lia.
      f_equal; lia.
Qed.

Lemma n_cup_succ_arb_top n : 
  n_cup (S n) ∝
  zx_arb_cap 0 (S n) _ ⟷
  cast _ _ n_cup_succ_prf eq_refl (n_cup n).
Proof.
  rewrite (n_cup_succ_arb_cap_gen n 0) by lia.
  now rewrite Nat.add_0_r.
Qed.

Lemma n_cup_succ_arb_bot n : 
  n_cup (S n) ∝
  zx_arb_cap n (S n + n) _ ⟷
  cast _ _ n_cup_succ_prf eq_refl (n_cup n).
Proof.
  apply (n_cup_succ_arb_cap_gen n n); lia.
Qed.





Lemma cap_to_arb_cap : ⊃ ∝ zx_arb_cap 0 1 2.
Proof. 
  unfold zx_arb_cap.
  cbn.
  rewrite stack_empty_r_fwd, cast_contract_eq, cast_id.
  rewrite <- (nwire_removal_l) at 1.
  apply compose_simplify; [|reflexivity].
  by_perm_eq.
  by_perm_cell; reflexivity.
Qed.

Lemma zx_arb_cap_n_wire_r_prf {k l n m} 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  n - 2 + m = n + m - 2.
Proof. lia. Qed.



Lemma zx_arb_cap_stack_n_wire_r k l n m
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  zx_arb_cap k l n ↕ n_wire m ∝
  cast _ _ eq_refl (zx_arb_cap_n_wire_r_prf Hk Hl Hkl)
  (zx_arb_cap k l (n + m)).
Proof.
  apply ZXbiperm_prop_by_biperm_eq;
  [auto with zxbiperm_db zxperm_db zarith..|].
  rewrite biperm_of_zx_cast, biperm_of_zx_stack 
    by auto with zxbiperm_db zxperm_db zarith.
  rewrite 2!biperm_of_zx_arb_cap by lia.
  rewrite biperm_of_n_wire.
  now rewrite arb_cap_biperm_add_r.
Qed.

Lemma zx_arb_cap_n_wire_l_prf {k l n m} 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  m + (n - 2) = m + n - 2.
Proof. lia. Qed.

Lemma zx_arb_cap_stack_n_wire_l k l n m
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  n_wire m ↕ zx_arb_cap k l n ∝
  cast _ _ eq_refl (zx_arb_cap_n_wire_l_prf Hk Hl Hkl)
  (zx_arb_cap (m + k) (m + l) (m + n)).
Proof.
  apply ZXbiperm_prop_by_biperm_eq;
  [auto with zxbiperm_db zxperm_db zarith..|].
  rewrite biperm_of_zx_cast, biperm_of_zx_stack 
    by auto with zxbiperm_db zxperm_db zarith.
  rewrite 2!biperm_of_zx_arb_cap by lia.
  rewrite biperm_of_n_wire.
  now rewrite arb_cap_biperm_add_l_r.
Qed.



Lemma cap_stack_n_wire_r_to_arb_cap n : 
  ⊃ ↕ n_wire n ∝
  cast _ _ eq_refl (eq_sym (add_sub' n 2)) 
  (zx_arb_cap 0 1 (2 + n)).
Proof.
  rewrite cap_to_arb_cap.
  clean_eqns rewrite zx_arb_cap_stack_n_wire_r.
  cast_irrelevance.
Qed.

Lemma cap_stack_n_wire_l_to_arb_cap n : 
  n_wire n ↕ ⊃ ∝
  cast _ _ eq_refl (eq_sym (
    eq_trans (Nat.add_sub n 2) (eq_sym (Nat.add_0_r _)))) 
  (zx_arb_cap n (S n) (n + 2)).
Proof.
  rewrite cap_to_arb_cap.
  clean_eqns rewrite zx_arb_cap_stack_n_wire_l.
  apply cast_simplify.
  ereflexivity.
  f_equal; lia.
Qed.

Lemma cap_stack_l_r_prf {n m o} : n + 0 + o = n + m + o - m.
Proof. lia. Qed.

Lemma cap_stack_n_wire_l_r_to_arb_cap n m : 
  n_wire n ↕ ⊃ ↕ n_wire m ∝
  cast _ _ eq_refl cap_stack_l_r_prf
    (zx_arb_cap n (S n) (n + 2 + m)).
Proof.
  rewrite cap_stack_n_wire_l_to_arb_cap.
  rewrite cast_stack_l_fwd.
  clean_eqns rewrite zx_arb_cap_stack_n_wire_r.
  rewrite cast_contract_eq.
  cast_irrelevance.
Qed.



(* FIXME: Move *)
Lemma cast_zx_arb_cap_natural_l n m n' k l prfn prfm : 
  cast n m prfn prfm (zx_arb_cap k l n') = 
  cast n m eq_refl (eq_trans prfm (f_equal (fun k=>k-2) (eq_sym prfn))) 
  (zx_arb_cap k l n).
Proof.
  now subst.
Qed.

Lemma cast_zx_arb_cap_natural_r_prf {n m n'}
  (prfn : n = n') (prfm : m = n' - 2) (Hn : 2 <= n) : 
  n = m + 2.
Proof. lia. Qed.

Lemma cast_zx_arb_cap_natural_r n m n' k l prfn prfm (Hn : 2 <= n) : 
  cast n m prfn prfm (zx_arb_cap k l n') =
  cast n m (cast_zx_arb_cap_natural_r_prf prfn prfm Hn) 
    (eq_sym (Nat.add_sub m 2))
  (zx_arb_cap k l (m + 2)).
Proof.
  subst.
  symmetry.
  rewrite cast_zx_arb_cap_natural_l.
  now rewrite 2!cast_id_eq.
Qed.


Definition zx_arb_cup k l n := 
  (zx_arb_cap k l n) ⊤%ZX.





















(* Section on edgefuncs, etc. *)

Definition edge_to_sidx n ij : nat :=
  edge_to_idx (S n) (fst ij, S (snd ij)).

Definition sidx_to_edge n k : nat * nat :=
  let ij := idx_to_edge (S n) k in 
  (fst ij, snd ij - 1).

Lemma sidx_to_edge_spec n k : 
  k < (n + 1) * n / 2 -> 
  fst (sidx_to_edge n k) <= snd (sidx_to_edge n k) < n.
Proof.
  intros Hk.
  pose proof (idx_to_edge_spec (S n) k).
  replace (S n - 1) with n in * by lia.
  replace (n + 1) with (S n) in * by lia.
  unfold sidx_to_edge.
  cbn [fst snd].
  lia.
Qed.

Lemma sidx_to_edge_succ n k (Hk : k < (S n + 1) * (S n) / 2) : 
  sidx_to_edge (S n) k =
  if k <? S n then (0, k) else
  (fun ij => (S (fst ij), S (snd ij))) 
  (sidx_to_edge n (k - S n)).
Proof.
  cbv delta [sidx_to_edge] beta.
  rewrite idx_to_edge_succ by (apply (Nat.lt_le_trans _ _ _ Hk); 
    ereflexivity; f_equal; lia).
  bdestruct (k <? S n).
  - cbn zeta.
    f_equal; cbn; lia.
  - cbn zeta.
    f_equal; cbn; lia.
Qed.

Lemma edge_to_sidx_bounded n ij (Hi : fst ij <= snd ij) (Hj : snd ij < n) : 
  edge_to_sidx n ij < (n + 1) * n / 2.
Proof.
  unfold edge_to_sidx.
  pose proof (edge_to_idx_bounded (S n) (fst ij, S (snd ij))) as Hlt.
  rewrite <- triangle_number, triangle_number' in Hlt.
  apply Hlt;
  cbn; lia.
Qed.

Lemma edge_to_sidx_succ n ij (Hi : fst ij <= snd ij) (Hj : snd ij < S n) : 
  edge_to_sidx (S n) ij =
  (if fst ij =? 0 then snd ij else
    S n + edge_to_sidx n (fst ij - 1, snd ij - 1)).
Proof.
  unfold edge_to_sidx at 1.
  rewrite edge_to_idx_succ by (cbn; lia).
  cbn [fst snd].
  bdestruct (fst ij =? 0); [lia|].
  f_equal.
  unfold edge_to_sidx.
  f_equal.
  f_equal; cbn; lia.
Qed.

Lemma edge_to_sidx_to_edge n ij (Hi : fst ij <= snd ij) (Hj : snd ij < n) : 
  sidx_to_edge n (edge_to_sidx n ij) = ij.
Proof.
  cbv delta [sidx_to_edge edge_to_sidx] beta.
  rewrite edge_to_idx_to_edge by (cbn; lia).
  cbn; rewrite (surjective_pairing ij); cbn; f_equal; lia.
Qed.

Lemma sidx_to_edge_to_sidx n k (Hk : k < (n + 1) * n / 2) :
  edge_to_sidx n (sidx_to_edge n k) = k.
Proof.
  cbv delta [edge_to_sidx sidx_to_edge] beta zeta.
  cbn [fst snd].
  assert (k < (S n) * (S n - 1) / 2) as Hk' by 
    (apply (Nat.lt_le_trans _ _ _ Hk); 
    ereflexivity; f_equal; lia).
  etransitivity; 
  [|apply (idx_to_edge_to_idx (S n) k); auto].
  f_equal.
  rewrite surjective_pairing.
  f_equal.
  unfold idx_to_edge.
  cbn; lia.
Qed.



















Definition edge_eq (ij ij' : nat * nat) : Prop :=
  (fst ij = fst ij' /\ snd ij = snd ij') \/
  (fst ij = snd ij' /\ snd ij = fst ij').

Lemma edge_eq_refl ij : edge_eq ij ij.
Proof. left; split; reflexivity. Qed.

Lemma edge_eq_swap k l : edge_eq (k, l) (l, k).
Proof. right; split; reflexivity. Qed.

Lemma edge_eq_sym ij ij' : edge_eq ij ij' -> edge_eq ij' ij.
Proof. unfold edge_eq. lia. Qed.

Lemma edge_eq_sym_iff ij ij' : edge_eq ij' ij <-> edge_eq ij ij'.
Proof. split; apply edge_eq_sym. Qed.

Lemma edge_eq_trans ij ij' ij'' : edge_eq ij ij' -> 
  edge_eq ij' ij'' -> edge_eq ij ij''.
Proof. unfold edge_eq. lia. Qed.

Lemma edge_eq_defn_l ij ij' : 
  edge_eq ij ij' <-> (ij = ij' \/ ij = (snd ij', fst ij')).
Proof.
  unfold edge_eq.
  rewrite (surjective_pairing ij), (surjective_pairing ij').
  cbn [fst snd].
  rewrite 2!pair_equal_spec.
  reflexivity.
Qed.

Lemma edge_eq_defn_r ij ij' : 
  edge_eq ij ij' <-> (ij' = ij \/ ij' = (snd ij, fst ij)).
Proof.
  rewrite edge_eq_sym_iff.
  apply edge_eq_defn_l.
Qed.

Definition edge_eqb ij ij' :=
  (fst ij =? fst ij') && (snd ij =? snd ij') ||
  (fst ij =? snd ij') && (snd ij =? fst ij').

Lemma edge_eqb_eq ij ij' : 
  edge_eqb ij ij' = true <-> edge_eq ij ij'.
Proof.
  unfold edge_eqb.
  rewrite orb_true_iff, 2!andb_true_iff, 4!Nat.eqb_eq.
  reflexivity.
Qed.

Lemma edge_eqb_edge_eq_reflect ij ij' : 
  reflect (edge_eq ij ij') (edge_eqb ij ij').
Proof.
  apply iff_reflect.
  symmetry.
  apply edge_eqb_eq.
Qed.

#[export] Hint Resolve edge_eqb_edge_eq_reflect : bdestruct.

Add Parametric Relation : (nat * nat) (edge_eq) 
  reflexivity proved by edge_eq_refl
  symmetry proved by edge_eq_sym
  transitivity proved by edge_eq_trans
  as edge_eq_setoid.

Add Parametric Morphism : edge_eqb with signature
  edge_eq ==> edge_eq ==> eq as edge_eqb_edge_eq_proper.
Proof.
  intros ij ij' Hij kl kl' Hkl.
  apply eq_iff_eq_true; rewrite 2!edge_eqb_eq.
  now rewrite Hij, Hkl.
Qed. 

Lemma edge_eqb_refl ij : edge_eqb ij ij = true.
Proof. rewrite edge_eqb_eq; reflexivity. Qed.

Lemma edge_eqb_swap i j : edge_eqb (i, j) (j, i) = true.
Proof. rewrite edge_eqb_eq; apply edge_eq_swap. Qed.

Lemma edge_eqb_comm ij kl : edge_eqb ij kl = edge_eqb kl ij.
Proof. 
  apply eq_iff_eq_true; rewrite 2!edge_eqb_eq.
  split; auto with relations. 
Qed.

Definition perm_edge_eq n (f g : nat -> nat * nat) :=
  forall k, k < n -> edge_eq (f k) (g k).

Lemma perm_edge_eq_refl n f : perm_edge_eq n f f.
Proof. intros k Hk; reflexivity. Qed.

Lemma perm_edge_eq_sym n f g : perm_edge_eq n f g -> perm_edge_eq n g f.
Proof. intros Hfg k Hk; symmetry; now apply Hfg. Qed.

Lemma perm_edge_eq_sym_iff n f g : perm_edge_eq n f g <-> perm_edge_eq n g f.
Proof. split; apply perm_edge_eq_sym. Qed.

Lemma perm_edge_eq_trans n f g h : 
  perm_edge_eq n f g -> perm_edge_eq n g h -> perm_edge_eq n f h.
Proof. intros Hfg Hgh k Hk; now rewrite (Hfg k), (Hgh k) by auto. Qed.

Add Parametric Relation n : (nat -> nat * nat) (perm_edge_eq n) 
  reflexivity proved by (perm_edge_eq_refl n)
  symmetry proved by (perm_edge_eq_sym n)
  transitivity proved by (perm_edge_eq_trans n)
  as perm_edge_eq_setoid.

Definition perm_edgefunc_eq n (f g : nat -> nat * nat) :=
  forall k, k < n -> f k = g k.

Lemma perm_edgefunc_eq_refl n f : 
  perm_edgefunc_eq n f f.
Proof. intros k Hk; reflexivity. Qed.

Lemma perm_edgefunc_eq_sym n f g : 
  perm_edgefunc_eq n f g -> perm_edgefunc_eq n g f.
Proof. intros Hfg k Hk; symmetry; now apply Hfg. Qed.

Lemma perm_edgefunc_eq_sym_iff n f g : 
  perm_edgefunc_eq n f g <-> perm_edgefunc_eq n g f.
Proof. split; apply perm_edgefunc_eq_sym. Qed.

Lemma perm_edgefunc_eq_trans n f g h : 
  perm_edgefunc_eq n f g -> perm_edgefunc_eq n g h ->
  perm_edgefunc_eq n f h.
Proof. 
  intros Hfg Hgh k Hk.
  now rewrite (Hfg k Hk), (Hgh k Hk).
Qed.

Add Parametric Relation n : (nat -> nat * nat) (perm_edgefunc_eq n)
  reflexivity proved by (perm_edgefunc_eq_refl n)
  symmetry proved by (perm_edgefunc_eq_sym n)
  transitivity proved by (perm_edgefunc_eq_trans n)
  as perm_edgefunc_eq_setoid.

Instance perm_edgefunc_eq_edge_eq n : 
  subrelation (perm_edgefunc_eq n) (perm_edge_eq n).
Proof.
  intros f g Hfg.
  intros k Hk.
  ereflexivity; now apply Hfg.
Qed.

Definition perm_deg_eq n (f g : nat * nat -> nat) := 
  forall kl, fst kl < n -> snd kl < n -> f kl = g kl.

Lemma perm_deg_eq_refl n f : perm_deg_eq n f f.
Proof. intros kl Hk Hl; reflexivity. Qed.

Lemma perm_deg_eq_sym n f g : perm_deg_eq n f g -> perm_deg_eq n g f.
Proof. intros Hfg kl Hk Hl; symmetry; now apply Hfg. Qed.

Lemma perm_deg_eq_sym_iff n f g : perm_deg_eq n f g <-> perm_deg_eq n g f.
Proof. split; apply perm_deg_eq_sym. Qed.

Lemma perm_deg_eq_trans n f g h : 
  perm_deg_eq n f g -> perm_deg_eq n g h -> perm_deg_eq n f h.
Proof.
  intros Hfg Hgh kl Hk Hl; now rewrite (Hfg kl), (Hgh kl) by auto. 
Qed.

Add Parametric Relation n : (nat * nat -> nat) (perm_deg_eq n) 
  reflexivity proved by (perm_deg_eq_refl n)
  symmetry proved by (perm_deg_eq_sym n)
  transitivity proved by (perm_deg_eq_trans n)
  as perm_deg_eq_setoid.

Definition perm_deg_eqb n f g :=
  forallb (fun k => forallb (fun l => f (k,l) =? g (k, l)) (seq 0 n)) (seq 0 n).

Lemma perm_deg_eqb_eq n f g : 
  perm_deg_eqb n f g = true <-> perm_deg_eq n f g.
Proof.
  unfold perm_deg_eqb, perm_deg_eq.
  rewrite forallb_seq0.
  setoid_rewrite forallb_seq0.
  setoid_rewrite Nat.eqb_eq.
  split.
  - intros Heq **.
    destruct kl;
    now apply Heq.
  - intros Heq **.
    now apply Heq.
Qed.

Definition edge_to_func (ij : nat * nat) : nat -> nat :=
  fun k => if k =? 0 then fst ij else if k =? 1 then snd ij else 0.

Definition edgefunc_of_infunc (f : nat -> nat) : nat -> nat * nat :=
  fun k => (f (k * 2), f (k * 2 + 1)).

Definition infunc_of_edgefunc (f : nat -> nat * nat) : nat -> nat :=
  fun k => edge_to_func (f (k / 2)) (k mod 2).

Lemma infunc_of_edgefunc_of_infunc f : 
  infunc_of_edgefunc (edgefunc_of_infunc f) = f.
Proof.
  apply functional_extensionality.
  intros k.
  unfold infunc_of_edgefunc, edgefunc_of_infunc, edge_to_func.
  pose proof (Nat.mod_upper_bound k 2 ltac:(lia)).
  pose proof (Nat.div_mod_eq k 2).
  bdestructΩ'_with ltac:(try lia); cbn [fst snd]; 
  f_equal; lia.
Qed.

Lemma edgefunc_of_infunc_of_edgefunc f : 
  edgefunc_of_infunc (infunc_of_edgefunc f) = f.
Proof.
  apply functional_extensionality.
  intros kl.
  unfold infunc_of_edgefunc, edgefunc_of_infunc, edge_to_func.
  rewrite Nat.Div0.mod_mul, mod_add_l.
  cbn [Nat.modulo Nat.divmod Nat.eqb fst snd Nat.sub].
  rewrite Nat.div_mul, div_2_add_l_1 by lia.
  symmetry.
  apply surjective_pairing.
Qed.


Definition edgefunc_of_deg m deg : nat -> nat * nat :=
  sidx_to_edge m ∘ (Nsum_index ((m + 1) * m / 2) (deg ∘ sidx_to_edge m)).

Add Parametric Morphism m : (edgefunc_of_deg m) with signature
  perm_deg_eq (S m) ==> eq as edgefunc_of_deg_perm_eq_to_eq.
Proof.
  intros deg deg' Hdeg.
  unfold edgefunc_of_deg.
  f_equal.
  apply Nsum_index_perm_eq_to_eq.
  intros k Hk.
  pose proof (sidx_to_edge_spec m k Hk).
  unfold compose.
  apply Hdeg; lia.
Qed.

Definition deg_of_edgefunc n f : nat * nat -> nat :=
  fun ij => big_sum (fun k => Nat.b2n (edge_eqb (f k) ij)) n.

Add Parametric Morphism n : (deg_of_edgefunc n) with signature
  perm_edge_eq n ==> eq as deg_of_edgefunc_perm_edge_eq_to_eq.
Proof.
  intros deg deg' Hdeg.
  apply functional_extensionality.
  intros kl.
  apply big_sum_eq_bounded.
  intros k Hk.
  now rewrite (Hdeg k Hk).
Qed.

Add Parametric Morphism n : (deg_of_edgefunc n) with signature
  perm_edge_eq n ==> edge_eq ==> eq 
  as deg_of_edgefunc_perm_edge_eq_to_edge_eq_to_eq.
Proof.
  intros deg deg' Hdeg kl kl' Hkl.
  apply big_sum_eq_bounded.
  intros k Hk.
  now rewrite (Hdeg k Hk), Hkl.
Qed.

Lemma deg_of_edgefunc_sym n f k l :
  deg_of_edgefunc n f (k, l) = deg_of_edgefunc n f (l, k).
Proof.
  now rewrite edge_eq_swap.
Qed.

Lemma deg_of_edgefunc_sum n m f : 
  deg_of_edgefunc (n + m) f =
  (fun kl => deg_of_edgefunc n f kl + 
    deg_of_edgefunc m (fun k => f (n + k)) kl).
Proof.
  apply functional_extensionality.
  intros kl.
  unfold deg_of_edgefunc.
  exact (big_sum_sum _ _ _).
Qed.




Lemma deg_of_edgefunc_big_sum n ns f :
  deg_of_edgefunc (big_sum ns n) f =
  (fun kl => big_sum (fun k => 
  deg_of_edgefunc (ns k) (fun i => f (big_sum ns k + i)) kl) n).
Proof.
  apply functional_extensionality.
  intros kl.
  apply big_sum_Nsum.
Qed.


Definition WF_edgefunc n m (f : nat -> nat * nat) :=
  forall k, k < n -> fst (f k) < m /\ snd (f k) < m.

Add Parametric Morphism n m : (WF_edgefunc n m) with signature
  perm_edge_eq n ==> iff as WF_edgefunc_perm_edge_eq_to_iff.
Proof.
  intros f g Hfg. 
  apply forall_lt_iff.
  intros k Hk.
  pose proof (Hfg k Hk).
  unfold edge_eq in *.
  lia.
Qed.

Lemma WF_edgefunc_reorder n m f g (Hg : permutation n g) : 
  WF_edgefunc n m f <-> WF_edgefunc n m (f ∘ g).
Proof.
  apply (forall_lt_iff_permute n g Hg).
Qed.

Lemma sidx_to_edge_WF n : WF_edgefunc ((n + 1) * n / 2) n (sidx_to_edge n).
Proof. 
  intros k Hk.
  pose proof (sidx_to_edge_spec n k Hk).
  lia.
Qed.

Lemma infunc_of_deg_WF m deg : 
  WF_edgefunc ((big_sum (deg ∘ sidx_to_edge m) ((m + 1) * m / 2))) m
  (edgefunc_of_deg m deg).
Proof.
  intros k Hk.
  unfold edgefunc_of_deg.
  apply sidx_to_edge_WF.
  apply Nsum_index_bounded.
  intros Hf; rewrite Hf in Hk; easy.
Qed.

Lemma edgefunc_of_deg_add_big_sum_l m deg i j 
  (Hi : i < (m + 1) * m / 2) (Hj : j < (deg ∘ sidx_to_edge m) i) :
  edgefunc_of_deg m deg (big_sum (deg ∘ sidx_to_edge m) i + j) = 
  sidx_to_edge m i.
Proof.
  unfold edgefunc_of_deg.
  unfold compose at 1.
  f_equal.
  now apply Nsum_index_add_big_sum_l.
Qed.


Lemma deg_of_edgefunc_of_deg_not_sym m deg : 
  forall k l, k <= l -> l < m -> 
  deg_of_edgefunc ((big_sum (deg ∘ sidx_to_edge m) ((m + 1) * m / 2))) 
    (edgefunc_of_deg m deg) (k, l) = 
    deg (k, l).
Proof.
  intros k l Hk Hl.
  rewrite deg_of_edgefunc_big_sum.
  apply big_sum_unique.
  exists (edge_to_sidx m (k, l)).
  split; [now apply edge_to_sidx_bounded|split].
  - unfold deg_of_edgefunc.
    unfold compose.
    rewrite edge_to_sidx_to_edge by auto.
    erewrite big_sum_eq_bounded;
    [apply Nsum_1|].
    intros i Hi.
    unfold Nat.b2n.
    apply if_true.
    rewrite edge_eqb_eq.
    rewrite edgefunc_of_deg_add_big_sum_l;
    [|now apply edge_to_sidx_bounded|];
    unfold compose;
    now rewrite edge_to_sidx_to_edge.
  - intros i Hi.
    intros Hneq.
    apply (@big_sum_0_bounded nat).
    intros j Hj.
    rewrite edgefunc_of_deg_add_big_sum_l by auto.
    apply if_false, not_true_iff_false.
    rewrite edge_eqb_eq.
    intros Hedge; apply Hneq.
    pose proof (sidx_to_edge_spec m i Hi).
    unfold edge_eq in Hedge.
    cbn [fst snd] in Hedge.
    assert (Hkv : fst (sidx_to_edge m i) = k) by lia.
    assert (Hlv : snd (sidx_to_edge m i) = l) by lia.
    rewrite <- Hkv, <- Hlv.
    rewrite <- surjective_pairing.
    now apply sidx_to_edge_to_sidx.
Qed.

Definition deg_symm n (deg : nat * nat -> nat)
  := forall k l, k < n -> l < n -> deg (k, l) = deg (l, k).

Lemma deg_of_edgefunc_of_deg m deg (Hdeg : deg_symm m deg) : 
  perm_deg_eq m
  (deg_of_edgefunc ((big_sum (deg ∘ sidx_to_edge m) ((m + 1) * m / 2))) 
    (edgefunc_of_deg m deg)) deg.
Proof.
  intros [k l].
  cbn [fst snd].
  intros Hk Hl.
  assert (Hor : k <= l \/ l <= k) by lia.
  by_symmetry Hor.
  - now apply deg_of_edgefunc_of_deg_not_sym.
  - clear k l Hor.
    intros k l Hkl Hk Hl.
    rewrite deg_of_edgefunc_sym, Hdeg by auto.
    auto.
Qed.

Lemma deg_of_edgefunc_reorder n f g (Hg : permutation n g) :
  deg_of_edgefunc n (f ∘ g) = deg_of_edgefunc n f.
Proof.
  apply functional_extensionality.
  intros kl.
  unfold deg_of_edgefunc.
  symmetry.
  exact (Nsum_reorder _ _ g Hg).
Qed.






Lemma deg_of_edgefunc_pos_witness n f kl : 
  deg_of_edgefunc n f kl <> 0 ->
  {i | i < n /\ edge_eq (f i) kl}.
Proof.
  intros H.
  destruct (Nsum_b2n_pos_witness _ _ H) as (i & Hi & Hfi).
  exists i.
  apply edge_eqb_eq in Hfi.
  auto.
Qed.

Lemma deg_of_edgefunc_succ n f : 
  deg_of_edgefunc (S n) f = 
  (fun kl => 
  deg_of_edgefunc n f kl + Nat.b2n (edge_eqb (f n) kl)).
Proof.
  reflexivity.
Qed.

Lemma deg_of_edgefunc_succ_eq_contract_eq_at_boundary 
  n m f g (Hfg : edge_eq (f n) (g n)) : 
  perm_deg_eq m (deg_of_edgefunc (S n) f) (deg_of_edgefunc (S n) g) ->
  perm_deg_eq m (deg_of_edgefunc n f) (deg_of_edgefunc n g).
Proof.
  intros Hdegfg kl Hk Hl.
  generalize (Hdegfg kl Hk Hl).
  rewrite 2!deg_of_edgefunc_succ.
  rewrite Hfg.
  lia.
Qed.

(* FIXME: Move *)
Lemma WF_edgefunc_mono_r n m m' (Hm : m <= m') f : 
  WF_edgefunc n m f -> WF_edgefunc n m' f.
Proof.
  intros Hf k Hk.
  pose proof (Hf k Hk).
  lia.
Qed.

Lemma WF_edgefunc_mono_l n n' m (Hn' : n <= n') f : 
  WF_edgefunc n' m f -> WF_edgefunc n m f.
Proof.
  intros Hf k Hk.
  apply Hf; lia.
Qed.

Lemma deg_of_edgefunc_eq_permutation_witness n m f g 
  (Hf : WF_edgefunc n m f) (Hg : WF_edgefunc n m g)
  (Hfg : perm_deg_eq m (deg_of_edgefunc n f) (deg_of_edgefunc n g)) : 
  {h | permutation n h /\ WF_Perm n h /\ perm_edge_eq n (f ∘ h) g}.
Proof.
  revert f g Hf Hg Hfg;
  induction n; intros f g Hf Hg Hfg.
  - exists idn; split; [auto_perm|easy].
  - assert (Hm : m <> 0) by (specialize (Hf 0); lia).
    assert (Hgdn : deg_of_edgefunc (S n) g (g n) <> 0) 
      by (rewrite deg_of_edgefunc_succ, 
        edge_eqb_refl; cbn; lia).
    pose proof (Hg n ltac:(auto)) as Hgn.
    assert (Hfdn : deg_of_edgefunc (S n) f (g n) <> 0)
      by now rewrite Hfg by easy.
    destruct (deg_of_edgefunc_pos_witness _ _ _ Hfdn) 
      as (k & Hk & Hfk).
    destruct (IHn (f ∘ swap_perm k n (S n)) g) as 
      (hrec & Hhrec & HhWF & Hheq).
    + apply (WF_edgefunc_mono_l n (S n) m ltac:(auto)).
      now rewrite <- WF_edgefunc_reorder by auto_perm.
    + now apply (WF_edgefunc_mono_l n (S n) m ltac:(auto)).
    + apply deg_of_edgefunc_succ_eq_contract_eq_at_boundary.
      * unfold compose.
        now rewrite swap_perm_right by lia.
      * now rewrite deg_of_edgefunc_reorder by auto_perm.
    + exists (swap_perm k n (S n) ∘ hrec).
      split; [|split].
      * auto using (permutation_monotonic_of_WF hrec n (S n))
        with perm_db zarith.
      * auto using (WF_Perm_monotone n (S n)) with WF_Perm_db.
      * unfold perm_edge_eq. 
        apply forall_nat_lt_S.
        split; [|apply Hheq].
        unfold compose.
        now rewrite HhWF, swap_perm_right by lia.
Qed.



Lemma infunc_of_edgefunc_compose_r n f g : 
  perm_eq (n * 2) (infunc_of_edgefunc (f ∘ g)) 
  (infunc_of_edgefunc f ∘ tensor_perms n 2 g idn).
Proof.
  rewrite tensor_perms_defn.
  intros k Hk.
  unfold infunc_of_edgefunc, compose.
  rewrite Nat.div_add_l, mod_add_l, mod_div, 
    Nat.Div0.mod_mod, Nat.add_0_r by lia.
  reflexivity.
Qed.


Lemma infunc_of_edgefunc_perm_edge_eq n f g (Hfg : perm_edge_eq n f g) : 
  perm_eq (n * 2) (infunc_of_edgefunc f) 
  (infunc_of_edgefunc g ∘ 
    big_stack_perms n (fun _ => 2) (fun k => 
    if fst (f k) =? snd (g k) then swap_2_perm else idn)).
Proof.
  rewrite big_stack_perms_constant_alt.
  rewrite perm_eq_split_times_2_iff.
  intros k Hk.
  unfold compose.
  rewrite Nat.div_mul, div_2_add_l_1, mod_add_l, 
    Nat.Div0.mod_mul by lia.
  rewrite 2!dist_if; cbn.
  unfold infunc_of_edgefunc.
  rewrite Nat.div_mul, div_2_add_l_1, 3!mod_add_l, 
    2!Nat.div_add_l, Nat.Div0.mod_mul by lia.
  rewrite 2!Nat.div_small, 3!Nat.mod_small by bdestructΩ'.
  rewrite Nat.add_0_r.
  pose proof (Hfg k Hk) as Hed.
  unfold edge_eq in Hed.
  bdestruct_one; cbn; lia.
Qed.

Add Parametric Morphism n : edgefunc_of_infunc with signature
  perm_eq (n * 2) ==> perm_edgefunc_eq n as edgefunc_of_infunc_perm_eq_proper.
Proof.
  intros f g Hfg.
  intros k Hk.
  unfold edgefunc_of_infunc.
  now rewrite 2!Hfg by show_moddy_lt.
Qed.

Add Parametric Morphism n : infunc_of_edgefunc with signature
  perm_edgefunc_eq n ==> perm_eq (n * 2) as infunc_of_edgefunc_perm_eq_proper.
Proof.
  intros f g Hfg.
  intros k Hk.
  unfold infunc_of_edgefunc.
  now rewrite Hfg by (apply Nat.Div0.div_lt_upper_bound; lia).
Qed. 


Lemma edgefunc_of_infunc_compose_tensor_r n f g : 
  perm_edge_eq n  
    (edgefunc_of_infunc (f ∘ tensor_perms n 2 g idn))
    (edgefunc_of_infunc f ∘ g).
Proof.
  rewrite tensor_perms_defn.
  intros k Hk.
  unfold edgefunc_of_infunc, compose.
  rewrite Nat.div_mul, div_2_add_l_1, Nat.Div0.mod_mul, mod_add_l by lia.
  now rewrite Nat.add_0_r.
Qed.

Lemma edgefunc_of_infunc_WF n m f (Hf : WF_input_func (n * 2) m f) : 
  WF_edgefunc n m (edgefunc_of_infunc f).
Proof.
  intros k Hk.
  unfold edgefunc_of_infunc.
  cbn [fst snd].
  split; apply Hf; show_moddy_lt.
Qed.

Lemma infunc_of_edgefunc_WF n m f (Hf : WF_edgefunc n m f) : 
  WF_input_func (n * 2) m (infunc_of_edgefunc f).
Proof.
  intros k Hk.
  unfold infunc_of_edgefunc.
  pose proof (Hf (k / 2) ltac:(apply Nat.Div0.div_lt_upper_bound; lia)).
  unfold edge_to_func.
  bdestructΩ'_with ltac:(try lia).
Qed.

Definition edgeperm_of_perm g : nat * nat -> nat * nat :=
  fun kl => (g (fst kl), g (snd kl)).

Add Parametric Morphism g : (edgeperm_of_perm g) with signature
  edge_eq ==> edge_eq as edgeperm_of_perm_edge_eq_proper.
Proof.
  intros kl kl'.
  unfold edge_eq, edgeperm_of_perm;
  cbn.
  intros [[] | []]; [left | right];
  split;
  congruence.
Qed.

Definition edgefunc_deg n f := 
  fun k => big_sum (fun l => 
    Nat.b2n (fst (f l) =? k) + Nat.b2n (snd (f l) =? k)) n.

Add Parametric Morphism n : (edgefunc_deg n) with signature
  perm_edge_eq n ==> eq as edgefunc_deg_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  apply functional_extensionality.
  intros x.
  apply big_sum_eq_bounded.
  intros k Hk.
  destruct (Hfg k Hk) as [[]|[]]; [congruence|].
  rewrite Nat.add_comm.
  congruence.
Qed.

Lemma edgefunc_deg_reorder n f g (Hg : permutation n g) : 
  edgefunc_deg n (f ∘ g) = edgefunc_deg n f.
Proof.
  apply functional_extensionality.
  intros x.
  symmetry.
  exact (Nsum_reorder n _ g Hg).
Qed.

Lemma edgefunc_deg_compose_perm_r n m f g (Hg : permutation m g) 
  (Hf : WF_edgefunc n m f): 
  perm_eq m (edgefunc_deg n f ∘ g)
    (edgefunc_deg n (edgeperm_of_perm (perm_inv' m g) ∘ f)).
Proof.
  intros k Hk.
  unfold compose, edgefunc_deg.
  cbn [fst snd edgeperm_of_perm].
  apply big_sum_eq_bounded.
  intros l Hl.
  rewrite 2!perm_inv'_eq by (now apply Hf).
  now rewrite 2!perm_inv_eqb_iff by (assumption + now apply Hf).
Qed.


(* FIXME: Move to by zx_arb_cup *)
Lemma zx_arb_cup_comm k l n : 
  zx_arb_cup k l n = zx_arb_cup l k n.
Proof.
  unfold zx_arb_cup.
  now rewrite zx_arb_cap_comm.
Qed.

Ltac unshelve_tac tac :=
  unshelve (tac).

(* FIXME: Move *)
Tactic Notation "unshelve" tactic3(tac) "eby" tactic3(solve_tac) :=
  unshelve_tac (tac); 
  match goal with |- ?G => 
    tryif has_evar G then let H := fresh in set (H := G) else
    idtac
  end;
  (first [match goal with |- ?H => subst H end | solve [solve_tac]]).

Tactic Notation "unshelve" tactic3(tac) :=
  unshelve_tac tac.


(* FIXME: Move to by zx_of_enlarge_to_big_zx_of_permutation_l *)
Lemma zx_of_enlarge_to_big_zx_of_permutation_r n f ns (Hf : permutation n f) :
  zx_of_perm (big_sum ns n) (enlarge_permutation n f ns)
  ∝ cast _ _ (Nsum_reorder n ns f Hf) (eq_trans (Nsum_reorder n ns f Hf)
    (Nsum_reorder n (ns ∘ f) _ (perm_inv'_permutation n f Hf)))
    (big_zx_of_permutation_r n (perm_inv' n f) (ns ∘ f) 
    (perm_inv'_permutation n f Hf)).
Proof.
  unfold big_zx_of_permutation_r.
  rewrite cast_zx_of_perm_natural_l, cast_contract_eq, 
    cast_zx_of_perm.
  ereflexivity.
  apply zx_of_perm_eq_of_perm_eq.
  rewrite perm_inv'_perm_inv', Combinators.compose_assoc,
    perm_inv'_is_rinv_of_permutation_compose by auto.
  reflexivity.
Qed.



Lemma nstack_zx_of_perm_passthrough {n m} (zx : ZX n m) k 
  f (Hf : permutation k f) : 
  k ⇑ zx ⟷ zx_of_perm _ (tensor_perms k m f idn) ∝
  zx_of_perm _ (tensor_perms k n f idn) ⟷ k ⇑ zx.
Proof.
  rewrite <- (perm_inv'_perm_inv' k f Hf).
  rewrite <- enlarge_permutation_constant.
  rewrite n_stack_to_big_stack.
  rewrite cast_compose_l, cast_zx_of_perm_natural_l.
  rewrite cast_compose_r_eq_mid, cast_contract_eq.
  unshelve rewrite zx_of_enlarge_to_big_zx_of_permutation_r eby auto_perm.
  rewrite cast_compose_r_eq_mid.
  rewrite cast_contract_eq.
  erewrite cast_mor;
  [|refine (big_zx_of_permutation_r_natural _ _ _ _ _ _)].
  cbv delta [compose] beta.
  unfold big_zx_of_permutation_r.
  rewrite cast_compose_l_eq_mid.
  rewrite cast_contract_eq.
  rewrite cast_compose_distribute, cast_zx_of_perm_natural_l, 
    cast_compose_l, cast_contract_eq, cast_id.
  apply compose_simplify; [|cast_irrelevance].
  cbv delta [compose] beta.
  rewrite enlarge_permutation_constant.
  now rewrite perm_inv'_perm_inv' by auto_perm.
Qed.


Lemma n_stacked_caps_zx_of_perm_absorbtion n f (Hf : permutation n f) : 
  zx_of_perm _ (tensor_perms n 2 f idn) ⟷ n_stacked_caps n ∝
  n_stacked_caps n.
Proof.
  unfold n_stacked_caps.
  rewrite cast_compose_r.
  rewrite cast_zx_of_perm_natural_r, cast_compose_l_eq_mid, cast_contract_eq.
  apply cast_simplify.
  rewrite <- nstack_zx_of_perm_passthrough by auto.
  rewrite zx_of_perm_eq_idn by (rewrite Nat.mul_0_r; apply perm_eq_0).
  rewrite zx_of_perm_idn; apply nwire_removal_r.
Qed.

Lemma n_stacked_cups_zx_of_perm_absorbtion n f (Hf : permutation n f) : 
  n_stacked_cups n ⟷ zx_of_perm _ (tensor_perms n 2 f idn) ∝
  n_stacked_cups n.
Proof.
  apply transpose_diagrams.
  cbn.
  rewrite n_stacked_cups_tranpose.
  rewrite zx_of_perm_transpose by auto_perm.
  replace (perm_inv' (n + n)) with (perm_inv' (n * 2)) by (f_equal; lia).
  rewrite tensor_perms_inv', idn_inv' by auto_perm.
  apply n_stacked_caps_zx_of_perm_absorbtion.
  auto_perm.
Qed.


Lemma n_stacked_cups_succ n : 
  n_stacked_cups (S n) ∝
  cast _ _ eq_refl n_stacked_caps_succ_prf
    (⊂ ↕ n_stacked_cups n).
Proof.
  unfold n_stacked_cups.
  rewrite cast_stack_r_fwd, cast_contract_eq.
  cast_irrelevance.
Qed.

Lemma cup_cap : ⊂ ⟷ ⊃ ∝ ⦰.
Proof.
  apply ZXbiperm_prop_by_biperm_eq; 
  [auto with zxbiperm_db..|apply perm_eq_0].
Qed.



Lemma Rsum_nonneg_0_iff n (f : nat -> R) 
  (Hf : forall k, k < n -> Rle 0 (f k)) : 
  big_sum f n = 0%R <->
  forall k, k < n -> f k = 0%R.
Proof.
  induction n; [easy|].
  cbn.
  specialize (IHn ltac:(auto)).
  rewrite forall_nat_lt_S, <- IHn.
  pose proof (Hf n ltac:(auto)).
  enough ((0 <= big_sum f n)%R) by lra.
  apply Rsum_ge_0_on.
  auto.
Qed.

(* FIXME: Move *)
Lemma iff_True_r P : 
  (P <-> True) <-> P.
Proof. tauto. Qed.

Lemma iff_True_l P : 
  (True <-> P) <-> P.
Proof. tauto. Qed.

Lemma Csum_real_pos_0_iff n (f : nat -> C) 
  (Hfreal : forall k, k < n -> Im (f k) = 0%R)
  (Hfpos : forall k, k < n -> Rle 0 (Re (f k))) :
  Σ f n = C0 <->
  forall k, k < n -> f k = C0.
Proof.
  rewrite (surjective_pairing (Σ f n)).
  unfold RtoC at 1.
  rewrite (@pair_equal_spec R R).
  unshelve (erewrite (_ : snd (Σ f n) = 0%R <-> True)).
  1: {
    rewrite iff_True_r.
    rewrite Im_big_sum.
    refine (big_sum_0_bounded _ _ _).
    auto.
  }
  rewrite and_True_r.
  rewrite Re_big_sum.
  rewrite Rsum_nonneg_0_iff by auto.
  apply forall_lt_iff.
  intros k Hk.
  rewrite (surjective_pairing (f k)) at 2.
  unfold RtoC.
  rewrite (@pair_equal_spec R R).
  rewrite <- (and_True_r (_ = _)) at 1.
  apply ZifyClasses.and_morph; [reflexivity|].
  rewrite iff_True_l.
  auto.
Qed.

(* FIXME: Move *)
Lemma forall_impl_comm {A} (P : A -> Prop) Q : 
  (forall a, Q -> P a) <-> (Q -> forall a, P a).
Proof. intuition auto. Qed.

Lemma forall_lt_forall_comm (P : nat -> nat -> Prop) n : 
  (forall i j, i < n -> P i j) <->
  (forall i, i < n -> forall j, P i j).
Proof. intuition auto. Qed.


Lemma mat_equiv_1_1_iff (A B : Matrix 1 1) : 
  A == B <-> A 0 0 = B 0 0.
Proof.
  unfold mat_equiv.
  rewrite forall_lt_forall_comm.
  now rewrite 2!forall_nat_lt_1.
Qed.

Lemma adjoint_e_i n i : adjoint (@e_i n i) = (@e_i n i) ⊤.
Proof. 
  lma'. 
  autounfold with U_db; cbn. 
  bdestruct_all; lca. 
Qed.

Definition real_pos_matrix {n m} (A : Matrix n m) : Prop :=
  forall k l, k < n -> l < m ->
  (0 <= Re (A k l) /\ Im (A k l) = 0)%R.

Lemma Mmult_real_pos_0_iff {n m o} (A : Matrix n m) (B : Matrix m o) 
  (HA : real_pos_matrix A) (HB : real_pos_matrix B) i j 
  (Hi : i < n) (Hj : j < o) : 
  (A × B) i j = C0 <->
  (forall k, k < m -> 
  (e_i i) ⊤ × A × (e_i k) × ((e_i k) ⊤ × B × e_i j) == Zero).
                          (* FIXME: Change this to ≡ ^ *)
Proof.
  unfold Mmult at 1.
  rewrite Csum_real_pos_0_iff.
  - apply forall_lt_iff.
    intros k Hk.
    rewrite get_entry_with_e_i, (get_entry_with_e_i B), 
      2!adjoint_e_i by auto.
    symmetry.
    rewrite mat_equiv_1_1_iff.
    cbn.
    now rewrite Cplus_0_l.
  - intros k Hk.
    pose proof (HA i k Hi Hk) as [_ HAik].
    pose proof (HB k j Hk Hj) as [_ HBkj].
    cbn.
    unfold Im in *.
    rewrite HAik, HBkj.
    lra.
  - intros k Hk.
    pose proof (HA i k Hi Hk) as [HApos HAik].
    pose proof (HB k j Hk Hj) as [HBpos HBkj].
    cbn.
    unfold Re, Im in *.
    rewrite HAik, HBkj.
    rewrite Rmult_0_l, Rminus_0_r.
    now apply Rmult_le_pos.
Qed.

Lemma Csum_binval_is_scale n (f : nat -> C) x
  (Hf : forall k, k < n -> f k = C0 \/ f k = x) :
  exists (l : nat), Σ f n = Cmult (INR l) x.
Proof.
  induction n.
  - exists 0; lca.
  - destruct (IHn ltac:(auto)) as [l Hl].
    destruct (Hf n ltac:(auto)) as [Hfn | Hfn].
    + exists l.
      cbn.
      rewrite Hfn, <- Hl.
      apply Cplus_0_r.
    + exists (S l).
      rewrite S_INR, RtoC_plus, Cmult_plus_distr_r.
      rewrite Cmult_1_l.
      cbn.
      congruence.
Qed.


(* FIXME: Move to Complex *)
Definition Ceqb (x y : C) : bool :=
  RMicromega.sumboolb (Ceq_dec x y).

Lemma Ceqb_eq x y : 
  Ceqb x y = true <-> x = y.
Proof.
  unfold Ceqb.
  destruct (Ceq_dec x y); easy.
Qed.

Lemma Ceqb_sym x y : 
  Ceqb x y = Ceqb y x.
Proof.
  apply eq_iff_eq_true; rewrite 2!Ceqb_eq.
  easy.
Qed.

Lemma Ceqb_eq_reflect x y : 
  reflect (x = y) (Ceqb x y).
Proof.
  apply iff_reflect; symmetry; apply Ceqb_eq.
Qed.

#[export] Hint Resolve Ceqb_eq_reflect : bdestruct.

Lemma Csum_binval_is_scale_value n (f : nat -> C) x
  (Hf : forall k, k < n -> f k = C0 \/ f k = x) :
  Σ f n = Cmult (INR (big_sum 
    (Nat.b2n ∘ (fun k => ¬ Ceqb (f k) C0)) n)) x.
Proof.
  induction n.
  - cbn; lca.
  - cbn.
    rewrite IHn by auto.
    rewrite plus_INR, RtoC_plus, Cmult_plus_distr_r.
    f_equal.
    unfold compose.
    bdestruct (Ceqb (f n) 0%R); cbn;
    [rewrite Cmult_0_l; congruence|].
    rewrite Cmult_1_l.
    destruct (Hf n ltac:(auto)); easy.
Qed.

Lemma Cmult_eq_0_iff (x y : C) : 
  Cmult x y = C0 <-> x = C0 \/ y = C0.
Proof.
  split.
  - apply Cmult_integral.
  - intros [-> | ->]; lca.
Qed.

Lemma RtoC_inj_iff (r s : R) : RtoC r = RtoC s <-> r = s.
Proof.
  split; [apply RtoC_inj|congruence].
Qed.

Lemma INR_nonneg n : Rle 0 (INR n).
Proof.
  induction n; [apply Rle_refl|].
  rewrite S_INR.
  lra.
Qed.

Lemma INR_eq_0_iff n : INR n = 0%R <-> n = 0.
Proof.
  split; [|now intros ->].
  destruct n; [easy|].
  rewrite S_INR.
  pose proof (INR_nonneg n).
  lra.
Qed.

Lemma Csum_binval_0_iff n (f : nat -> C) x
  (Hf : forall k, k < n -> f k = C0 \/ f k = x) :
  Σ f n = C0 <->
  forall k, k < n -> f k = C0.
Proof.
  erewrite Csum_binval_is_scale_value by eassumption.
  rewrite Cmult_eq_0_iff.
  rewrite RtoC_inj_iff, INR_eq_0_iff.
  rewrite Nsum_b2n_zero_iff.
  setoid_rewrite negb_false_iff.
  setoid_rewrite Ceqb_eq.
  intuition idtac.
  destruct (Hf k ltac:(auto)); congruence.
Qed.

Definition binval_matrix {n m} (A : Matrix n m) : Prop :=
  exists x, forall k l, k < n -> l < m ->
  (A k l = C0 \/ A k l = x)%R.

Lemma binval_matrix_scale {n m} (A : Matrix n m) c : 
  binval_matrix A -> binval_matrix (c .* A).
Proof.
  intros [x Hx].
  exists (c * x)%C.
  intros k l Hk Hl.
  unfold scale.
  destruct (Hx k l Hk Hl) as [-> | ->];
  [left; lca|now right].
Qed.

Add Parametric Morphism n m : binval_matrix with signature
  mat_prop n m ==> iff as binval_matrix_of_prop_iff.
Proof.
  intros A B HAB.
  split.
  - symmetry in HAB.
    destruct HAB as (c & HAB & Hc).
    rewrite HAB.
    apply binval_matrix_scale.
  - destruct HAB as (c & HAB & Hc).
    rewrite HAB.
    apply binval_matrix_scale.
Qed.

Lemma matrix_of_biperm_binval n m f : 
  binval_matrix (matrix_of_biperm n m f).
Proof.
  exists 1%R.
  intros k l Hk Hl.
  rewrite matrix_of_biperm_defn by auto.
  bdestruct_one;
  [now right | now left].
Qed.






Lemma Mmult_binval_0_iff {n m o} (A : Matrix n m) (B : Matrix m o) 
  (HA : binval_matrix A) (HB : binval_matrix B) i j 
  (Hi : i < n) (Hj : j < o) : 
  (A × B) i j = C0 <->
  (forall k, k < m -> 
  (e_i i) ⊤ × A × (e_i k) × ((e_i k) ⊤ × B × e_i j) == Zero).
                          (* FIXME: Change this to ≡ ^ *)
Proof.
  unfold Mmult at 1.
  destruct HA as [a Ha].
  destruct HB as [b Hb].
  rewrite Csum_binval_0_iff.
  - apply forall_lt_iff.
    intros k Hk.
    rewrite get_entry_with_e_i, (get_entry_with_e_i B), 
      2!adjoint_e_i by auto.
    symmetry.
    rewrite mat_equiv_1_1_iff.
    cbn.
    now rewrite Cplus_0_l.
  - intros k Hk.
    destruct (Ha i k Hi Hk) as [-> | ->],
      (Hb k j Hk Hj) as [-> | ->];
    [left; lca..|right;reflexivity].
Qed.

(* FIXME: Move *)
Lemma if_diff_eq_l {A} (b : bool) (u v : A) (Huv : u <> v) : 
  (if b then u else v) = u <-> b = true.
Proof.
  destruct b; intuition auto; easy.
Qed.

Lemma if_diff_eq_r {A} (b : bool) (u v : A) (Huv : u <> v) : 
  (if b then u else v) = v <-> b = false.
Proof.
  destruct b; intuition auto; easy.
Qed.

Lemma Cmult_nonzero_l_eq_iff (a b c : C) : a <> C0 -> 
  Cmult a b = c <-> b = (c / a)%C.
Proof.
  intros Ha.
  split; [intros <- | intros ->]; 
  C_field.
Qed.

Lemma Cmult_nonzero_r_eq_iff (a b c : C) : b <> C0 -> 
  Cmult a b = c <-> a = (c / b)%C.
Proof.
  intros Hb.
  rewrite Cmult_comm.
  now apply Cmult_nonzero_l_eq_iff.
Qed.

Lemma Cdiv_0_l c : (C0 / c)%C = C0.
Proof.
  lca.
Qed.

Lemma mat_prop_eq_0_iff {n m} (A B : Matrix n m) : A [∝] B ->
  forall i j,
  A i j = C0 <-> B i j = C0.
Proof.
  intros (c & HAB & Hc).
  rewrite HAB.
  intros i j.
  unfold scale.
  rewrite Cmult_nonzero_l_eq_iff by auto.
  now rewrite Cdiv_0_l.
Qed.

Lemma matrix_compose_biperms_spec n m o f g 
  (Hf : bipermutation (n + m) f) (Hg : bipermutation (m + o) g) : 
  forall i j, i < 2 ^ o -> j < 2 ^ n -> 
  matrix_of_biperm n o (compose_biperms n m o f g) i j = C0 <->
  forall k, k < 2 ^ m ->
  matrix_of_biperm n m f k j = C0 \/
  matrix_of_biperm m o g i k = C0.
Proof.
  intros i j Hi Hj.
  rewrite (mat_prop_eq_0_iff _ _ 
    (matrix_of_biperm_compose n m o f g Hf Hg)).
  rewrite Mmult_binval_0_iff by auto using matrix_of_biperm_binval.
  apply forall_lt_iff.
  intros k Hk.
  rewrite mat_equiv_1_1_iff.
  unfold Mmult at 1.
  cbn.
  rewrite Cplus_0_l, <- 2!adjoint_e_i, <- 2!get_entry_with_e_i by auto.
  rewrite Cmult_eq_0_iff.
  apply or_comm.
Qed.

Lemma forall_nat_lt_dec P n (HP : forall k, k < n -> {P k} + {~ P k}) :
  {forall k, k < n -> P k} + {exists k, k < n /\ ~ P k}.
Proof.
  induction n; [now left|].
  destruct (IHn ltac:(auto)) as [? | Hf].
  - destruct (HP n ltac:(auto)).
    + left.
      now rewrite forall_nat_lt_S.
    + right.
      exists n.
      auto.
  - right.
    destruct Hf as (k & Hk & HnPk).
    exists k.
    split; [lia | auto].
Qed.

Lemma forall_nat_lt_dec_not_forall_ex 
  P n (HP : forall k, k < n -> {P k} + {~ P k}) :
  ~ (forall k, k < n -> P k) <-> exists k, k < n /\ ~ P k.
Proof.
  pose proof (forall_nat_lt_dec P n HP) as [HT | HF].
  - split; [intros; easy|].
    intros (? & ? & ?).
    auto.
  - split; [easy|].
    intros (? & ? & ?).
    auto.
Qed.



#[export] Hint Resolve eqb_spec : bdestruct.

Lemma b2R_plus b c :
  (b2R b + b2R c = b2R (b || c) + b2R (b && c))%R.
Proof.
  destruct b, c; cbn; lra.
Qed.

Lemma b2R_plus_exclusive b c : b && c = false ->
  (b2R b + b2R c = b2R (b || c))%R.
Proof.
  rewrite b2R_plus.
  intros ->.
  apply Rplus_0_r.
Qed.

Lemma andb_forallb {A} f g (l : list A) : 
  forallb f l && forallb g l = 
  forallb (fun k => f k && g k) l.
Proof.
  induction l; [easy|].
  cbn.
  rewrite <- IHl.
  Btauto.btauto.
Qed.


Lemma andb_shuffle1 a b c d : 
  a && b && (c && d) = 
  a && c && (b && d).
Proof. Btauto.btauto. Qed.

Lemma eqb_false_l b : eqb false b = ¬ b.
Proof. now destruct b. Qed.

Lemma eqb_false_r b : eqb b false = ¬ b.
Proof. now destruct b. Qed.

Lemma andb_orb_distr_same_r b c d e : c = e -> 
  b && c || d && e = (b || d) && c.
Proof. intros ->; Btauto.btauto. Qed.

Lemma andb_orb_distr_same_l b c d e : b = d -> 
  b && c || d && e = b && (c || e).
Proof. intros ->; Btauto.btauto. Qed.

Lemma iff_eq_distr {A} (a b c d : A) : 
  a = b -> c = d -> a = c <-> b = d.
Proof. now intros -> ->. Qed.

Lemma zx_arb_cap_f_to_vec_opp k l n 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) f : 
  (f_to_vec (n - 2) f) ⊤ × (⟦ zx_arb_cap k l n ⟧) = 
  (f_to_vec n (fun a => 
  if a =? min k l then true else 
  if a =? max k l then true else
  if a <? min k l then f a else
  if a <? max k l then f (a - 1) else
  f (a - 2)) .+
  f_to_vec n (fun a => 
  if a =? min k l then false else 
  if a =? max k l then false else
  if a <? min k l then f a else
  if a <? max k l then f (a - 1) else
  f (a - 2))) ⊤.
Proof.
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros g.
  rewrite Mmult_assoc.
  rewrite zx_arb_cap_f_to_vec by auto.
  rewrite Mplus_transpose.
  distribute_plus.
  distribute_scale.
  rewrite 3!f_to_vec_transpose_f_to_vec.
  rewrite <- Mscale_plus_distr_l.
  distribute_scale.
  f_equal.
  assert (min k l < max k l) by lia.
  assert (max k l < n) by lia.
  replace (seq 0 (n - 2)) with 
    (seq 0 (min k l + (max k l - (min k l + 1)) + (n - 2 - (max k l - 1))))
    by (f_equal; lia).
  replace (seq 0 n) with (seq 0 (min k l + 1 + 
    (max k l - (min k l + 1)) + 1 + (n - (max k l + 1)))) 
    by (f_equal; lia).
  rewrite <- RtoC_mult, <- RtoC_plus.
  f_equal.
  rewrite b2R_mult, b2R_plus_exclusive.
  2: {
    rewrite !seq_app, !forallb_app.
    match goal with 
    |- context [forallb ?f] => set (F := forallb f)
    end.
    match goal with 
    |- context [forallb ?f] => set (F' := forallb f)
    end.
    cbn [Nat.add].
    enough (F' (seq (min k l) 1) && F (seq (min k l) 1) = false) as 
      HF%andb_false_iff by 
      (destruct HF as [-> | ->]; simpl_bools; reflexivity).
    subst F F'.
    cbn [Nat.add forallb seq].
    rewrite Nat.eqb_refl.
    rewrite eqb_false_l, eqb_true_l.
    Btauto.btauto.
  }
  f_equal.
  rewrite !seq_app, !forallb_app.
  match goal with 
  |- context [forallb ?f] => set (G := forallb f)
  end.
  match goal with 
  |- context [forallb ?f] => set (F := forallb f)
  end.
  match goal with 
  |- context [forallb ?f] => set (F' := forallb f)
  end.
  rewrite andb_orb_distr_same_r. 2:{
    subst F F'.
    apply eq_iff_eq_true.
    rewrite 2!forallb_seq.
    apply forall_lt_iff.
    intros i Hi.
    apply iff_eq_distr; [|reflexivity].
    f_equal.
    do 2 if_false_lia; reflexivity.
  }
  rewrite <- !andb_assoc.
  rewrite andb_orb_distr_same_l. 2:{
    subst F F'.
    apply eq_iff_eq_true.
    rewrite 2!forallb_seq.
    apply forall_lt_iff.
    intros i Hi.
    apply iff_eq_distr; [|reflexivity].
    f_equal.
    do 2 if_false_lia; reflexivity.
  }
  assert (forall b c d, b && (c && d) = b && d && c) 
    as andb_assoc_comm by (intros; Btauto.btauto).
  rewrite 2!andb_assoc.
  rewrite 2!andb_assoc_comm.
  rewrite andb_orb_distr_same_r. 2: {
    subst F F'.
    apply eq_iff_eq_true.
    rewrite 2!forallb_seq.
    apply forall_lt_iff.
    intros i Hi.
    apply iff_eq_distr; [|reflexivity].
    f_equal.
    do 2 if_false_lia; reflexivity.
  }
  rewrite !andb_assoc.
  rewrite (andb_comm _ (orb _ _)).
  rewrite <- !andb_assoc.
  f_equal.
  - replace (0 + (min k l + 1 + (max k l - (min k l + 1)))) with (max k l)
      by lia.
    subst F F'.
    cbn.
    rewrite 2!Nat.eqb_refl.
    if_false_lia.
    simpl_bools.
    rewrite 2!eqb_true_l. 
    change (eqb false ?x) with (¬ x).
    apply eq_iff_eq_true.
    rewrite eqb_true_iff.
    rewrite min_ltb, max_ltb.
    bdestruct_one;
    now destruct (g k), (g l).
  - f_equal; [|f_equal].
    + subst G F.
      apply eq_iff_eq_true.
      rewrite 2!forallb_seq.
      apply forall_lt_iff.
      intros i Hi.
      apply iff_eq_distr; [|reflexivity].
      f_equal; blia_rec.
    + subst G F.
      apply eq_iff_eq_true.
      rewrite 2!forallb_seq.
      apply forall_lt_iff.
      intros i Hi.
      apply iff_eq_distr; [|reflexivity].
      f_equal; repeat (if_false_lia + if_true_lia); f_equal; lia.
    + transitivity (G (seq (max k l - 1) (n - 1 - max k l)));
        [do 2 f_equal; lia|].
      transitivity (F (seq (max k l + 1) (n - 1 - max k l)));
        [|do 2 f_equal; lia].
      subst G F.
      apply eq_iff_eq_true.
      rewrite 2!forallb_seq.
      apply forall_lt_iff.
      intros i Hi.
      apply iff_eq_distr; [|reflexivity].
      f_equal; repeat (if_false_lia + if_true_lia); f_equal; lia.
Qed.


Notation "'subst!' y 'for' x 'in' f" := (match y with x => f end) (at level 10).

Ltac app_beta f x :=
  match f with
  | (fun y => ?F) => constr:(subst! x for y in F)
  end.

Ltac app_beta_let f x a :=
  match f with
  | (fun y => ?F) => 
    constr:(let x := a in subst! x for y in F)
  end.

Ltac simpl_let_1 := 
  match goal with 
  |- context G [let b := ?x in @?F b] => 
    let F' := app_beta F x in 
    let goal' := context G [F'] in 
    change goal'
  end.

Ltac hypothesize_let :=
  match goal with 
  |- context G [let b := ?x in @?F b] => 
    tryif set (b := x) then 
    let F' := app_beta F b in 
    let goal' := context G [F'] in 
    change goal'
    else
    let b' := fresh b in set (b' := x);
    let F' := app_beta F b' in 
    let goal' := context G [F'] in 
    change goal'
  end.

Ltac dehyp_let :=
  lazymatch goal with 
  | a := _ |- _ =>
    repeat match goal with
    | H : context [a] |- _ => revert H
    end;
    match goal with 
    | a := ?f |- ?F =>
    let a' := fresh a in 
    pattern a;
    match goal with 
    |- ?P a => 
      let fEa' := app_beta_let P a' f in 
      change (fEa'); clear a
    end end
  end.

Ltac simpl_beta_1 :=
  match goal with 
  |- context E [(fun y => ?F) ?x] => 
    let Fx := constr:(subst! x for y in F) in 
    let E' := context E [Fx] in 
    change E'
  end.

Ltac let_to_comp := 
  match goal with 
  |- context G [fun y => let b := @?x y in @?F b] =>
    let G' := context G [F ∘ x]
    in change G' 
    (* tryif set (b := x) then 
    let F' := app_beta F b in 
    let goal' := context G [F'] in 
    change goal'
    else
    let b' := fresh b in set (b' := x);
    let F' := app_beta F b' in 
    let goal' := context G [F'] in 
    change goal' *)
  end.




Ltac equal_f_lem feq :=
  lazymatch type of feq with 
  | @eq (forall x : ?A, @?B x) ?fdef ?f =>
    (* let _ := match goal with _ => idtac A B fdef f end in *)
    constr:((fun x : A => 
      ltac:(let r := equal_f_lem constr:(eq_refl : (fdef x) = (f x))
        in exact r)) : forall x, fdef x = f x)
  | ?fdef = ?f => 
    (* let _ := match goal with _ => idtac fdef f end in *)
    constr:(eq_refl : fdef = f)
  end.

Ltac get_fold_eqn f :=
  let fdef := eval red in f in 
  let r := equal_f_lem (eq_refl : fdef = f) in 
  let rtyp := type of r in 
  let rettyp := eval cbn beta in rtyp in 
  constr:(r : rettyp).

Ltac fold_fun f :=
  let r := get_fold_eqn f in 
  rewrite r.




Definition biperm_compose_cup_l_base n m f :=
  make_WF_Perm (n - 2 + m) (fun k =>
  if k + 2 =? f 0 then f 1 - 2 else 
  if k + 2 =? f 1 then f 0 - 2 else
  f (k + 2) - 2).

Lemma biperm_compose_cup_l_base_defn n m f :
  perm_eq (n - 2 + m) (biperm_compose_cup_l_base n m f)
  (fun k =>
  if k + 2 =? f 0 then f 1 - 2 else 
  if k + 2 =? f 1 then f 0 - 2 else
  f (k + 2) - 2).
Proof. 
  apply make_WF_Perm_perm_eq. 
Qed.

Lemma biperm_compose_cup_l_base_bipermutation n m f 
  (Hn : 2 <= n) (Hf : bipermutation (n + m) f) : 
  bipermutation (n - 2 + m) (biperm_compose_cup_l_base n m f).
Proof.
  rewrite biperm_compose_cup_l_base_defn.
  intros k Hk.
  split; [|split].
  - bdestructΩ'_with idtac;
    [pose proof (Hf 1) | pose proof (Hf 0)| pose proof (Hf (k + 2))];
    lia.
  - bdestructΩ'_with idtac.
    + assert (2 <= f 1). 1: {
        enough (f 1 <> 1 /\ f 1 <> 0) by lia.
        split; [apply Hf; lia|].
        erewrite bipermutation_eq_iff; eauto with zarith.
      }
      assert (f 1 <> f 0) 
        by (apply (@permutation_neq (n + m)); lia + auto_perm).
      lia.
    + assert (2 <= f 0). 1: {
        enough (f 0 <> 1 /\ f 0 <> 0) by lia.
        split; [|apply Hf; lia].
        erewrite bipermutation_eq_iff; eauto with zarith.
      }
      assert (f 1 <> f 0) 
        by (apply (@permutation_neq (n + m)); lia + auto_perm).
      lia.
    + rewrite <- 2!(bipermutation_eq_iff (k + 2) _ Hf) in * by lia.
      pose proof (Hf (k + 2)).
      lia.
  - bdestruct (k + 2 =? f 0); 
    [|bdestruct (k + 2 =? f 1)]. 
    + assert (2 <= f 1). 1: {
        enough (f 1 <> 1 /\ f 1 <> 0) by lia.
        split; [apply Hf; lia|].
        erewrite bipermutation_eq_iff; eauto with zarith.
      }
      assert (f 1 <> f 0) 
        by (apply (@permutation_neq (n + m)); lia + auto_perm).
      bdestructΩ'.
    + assert (2 <= f 0). 1: {
        enough (f 0 <> 1 /\ f 0 <> 0) by lia.
        split; [|apply Hf; lia].
        erewrite bipermutation_eq_iff; eauto with zarith.
      }
      assert (f 1 <> f 0) 
        by (apply (@permutation_neq (n + m)); lia + auto_perm).
      bdestructΩ'.
    + rewrite <- 2!(bipermutation_eq_iff (k + 2) _ Hf) in * by lia.
      pose proof (Hf (k + 2)).
      rewrite Nat.sub_add by lia.
      rewrite (bipermutation_involutive _ Hf) by lia.
      rewrite 2!(@permutation_eqb_iff (n + m)) by lia + auto_perm.
      do 2 if_false_lia.
      lia.
Qed.

#[export] Hint Resolve biperm_compose_cup_l_base_bipermutation : biperm_db.

Lemma cap_f_to_vec_opp f : 
  (f_to_vec 0 f) ⊤ × (⟦ ⊃ ⟧) = 
  (f_to_vec 2 (fun _ => true)) ⊤ .+
  (f_to_vec 2 (fun _ => false)) ⊤.
Proof. lma'. Qed.

Lemma cup_f_to_vec_opp f : 
  (⟦ ⊂ ⟧) × (f_to_vec 0 f) = 
  (f_to_vec 2 (fun _ => true)) .+
  (f_to_vec 2 (fun _ => false)).
Proof. lma'. Qed.

Lemma cup_to_f_to_vec : 
  (⟦ ⊂ ⟧) = 
  (f_to_vec 2 (fun _ => true)) .+
  (f_to_vec 2 (fun _ => false)).
Proof. lma'. Qed.

Lemma biperm_compose_cup_l_base_f_0 n m f (Hf : bipermutation (n + m) f) 
  (Hn : 2 <= n) (Hf0 : f 0 <> 1) :
  biperm_compose_cup_l_base n m f (f 0 - 2) = 
  f 1 - 2.
Proof.
  bdestruct (n + m =? 2).
  - unfold biperm_compose_cup_l_base.
    unfold make_WF_Perm.
    if_true_lia.
    pose (Hf 0); pose (Hf 1); lia.
  - rewrite biperm_compose_cup_l_base_defn 
      by (pose proof (Hf 0); lia).
    assert (f 0 <> 0) by (apply Hf; lia).
    rewrite Nat.sub_add by lia.
    now if_true_lia.
Qed.

Lemma biperm_compose_cup_l_base_f_1 n m f (Hf : bipermutation (n + m) f) 
  (Hn : 2 <= n) (Hf1 : f 1 <> 0) :
  biperm_compose_cup_l_base n m f (f 1 - 2) = 
  f 0 - 2.
Proof.
  bdestruct (n + m =? 2).
  - unfold biperm_compose_cup_l_base.
    unfold make_WF_Perm.
    if_true_lia.
    pose (Hf 0); pose (Hf 1); lia.
  - rewrite biperm_compose_cup_l_base_defn 
      by (pose proof (Hf 1); lia).
    assert (f 1 <> 1) by (apply Hf; lia).
    rewrite Nat.sub_add by lia.
    assert (f 1 <> f 0) by (apply (@permutation_neq (n + m)); lia + auto_perm).
    if_false_lia;
    now if_true_lia.
Qed.

Lemma and_impl_r P Q : 
  P /\ (P -> Q) <-> P /\ Q.
Proof. tauto. Qed.

Lemma and_impl_l P Q : 
  (Q -> P) /\ Q <-> P /\ Q.
Proof. tauto. Qed.

Lemma and_or_distr_same_l P Q P' R : 
  P <-> P' ->
  P /\ Q \/ P' /\ R <-> P /\ (Q \/ R).
Proof.
  intros ->; tauto.
Qed.

Lemma and_or_distr_same_r P Q R Q' : 
  Q <-> Q' ->
  P /\ Q \/ R /\ Q' <-> (P \/ R) /\ Q.
Proof.
  intros ->; tauto.
Qed.

Lemma or_true_false_iff_ex P : 
  (P true \/ P false) <-> (exists b, P b).
Proof.
  split; [intros []; eauto|].
  intros [[] ]; auto.
Qed.

Ltac or_true_false_iff_ex :=
  match goal with 
  |- context E [?Ptrue \/ ?Pfalse] =>
    match Ptrue with | context [true] =>
    let Pt := eval pattern true in Ptrue in 
    match Pt with | ?P true =>
    let goal' := context E [P true \/ P false] in
    change goal';
    rewrite or_true_false_iff_ex
  end end end.

Lemma matrix_of_biperm_compose_cup_l_base_neq n m f (Hn : 2 <= n) 
  (Hf : bipermutation (n + m) f) (Hf0 : f 0 <> 1) : 
  matrix_of_biperm (n - 2) m (biperm_compose_cup_l_base n m f) = 
  matrix_of_biperm n m f × (⟦ ⊂ ⟧ ⊗ I (2 ^ (n - 2))).
Proof.
  apply equal_on_conj_basis_states_implies_equal; [auto_wf..|].
  assert (f 1 <> 0) by (rewrite (bipermutation_eq_iff _ _ Hf); lia).
  intros g h.
  rewrite Mmult_assoc.
  rewrite <- (kron_1_l _ _ (f_to_vec (n - 2) g)) by auto_wf.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_r, Mmult_1_l by auto_wf.
  rewrite cup_to_f_to_vec.
  distribute_plus.
  rewrite 2!f_to_vec_merge.
  replace (2 + (n - 2)) with n by lia.
  rewrite kron_1_l by auto_wf.
  rewrite <- 3!Mmult_assoc.
  rewrite 3!matrix_of_biperm_funbool_conj_eq by auto_biperm.
  rewrite <- Mscale_plus_distr_l.
  f_equal.
  rewrite <- 3!(if_dist R C _ RtoC).
  do 3 fold_fun b2R.
  rewrite <- RtoC_plus.
  f_equal.
  rewrite b2R_plus_exclusive.
  2: {
    apply not_true_iff_false.
    rewrite andb_true_iff, 2!funbool_preserved_iff_all_lt_eq.
    intros [Htrue Hfalse].
    specialize (Htrue 0 ltac:(lia)).
    specialize (Hfalse 0 ltac:(lia)).
    revert Htrue Hfalse.
    do 2 if_true_lia.
    assert (f 0 <> 0) by (apply Hf; lia).
    replace_bool_lia (f 0 <? 2) false.
    congruence.
  }
  f_equal.
  apply eq_iff_eq_true.
  rewrite orb_true_iff, 3!funbool_preserved_iff_all_lt_eq.
  assert (2 <= f 0) by (enough (f 0 <> 0); pose (Hf 0); lia).
  assert (2 <= f 1) by (enough (f 1 <> 1); pose (Hf 1); lia).
  or_true_false_iff_ex.
  split. 
  - intros Hcomp.
    assert ((if (f 1 - 2) <? n - 2 then g (f 1 - 2) 
      else h ((f 1 - 2) - (n - 2))) = if (f 0 - 2) <? n - 2 
      then g (f 0 - 2) else h ((f 0 - 2) - (n - 2))) as Hgh1 by
      (symmetry; rewrite Hcomp by (pose proof (Hf 0); lia);
       now rewrite biperm_compose_cup_l_base_f_0 by auto).
    replace (f 0 - 2 - (n - 2)) with (f 0 - n) in * by lia.
    replace (f 1 - 2 - (n - 2)) with (f 1 - n) in * by lia.
    set (b := (if f 0 - 2 <? n - 2 then g (f 0 - 2) else h (f 0 - n))).
    pose proof (ltac:(let r := get_fold_eqn b in exact r)) as Hgh0.
    rewrite Hgh0 in Hgh1.
    exists b.
    replace (n + m) with (2 + (n - 2 + m)) by lia.
    rewrite (forall_nat_lt_add 2).
    split.
    1: {
      by_perm_cell;
      do 2 if_true_lia;
      [rewrite <- Hgh0 at 1|rewrite <- Hgh1 at 1]; 
      bdestructΩ'_with ltac:(try (lia + reflexivity)).
    }
    intros k Hk.
    change (?x + _ <? ?x) with false.
    cbn match.
    rewrite add_sub'.
    replace (2 + k - n) with (k - (n - 2)) by lia.
    replace_bool_lia (2 + k <? n) (k <? n - 2).
    rewrite Hcomp by auto.
    rewrite (Nat.add_comm 2 k).
    pattern (biperm_compose_cup_l_base n m f k).
    match goal with |- ?Q ?x => set (P := Q) end.
    rewrite (biperm_compose_cup_l_base_defn n m f k Hk).
    bdestruct_one; [|bdestruct_one];
    [subst P; replace -> (k + 2);
    replace (f 0 - 2 - (n - 2)) with (f 0 - n) in * by lia;
    replace (f 1 - 2 - (n - 2)) with (f 1 - n) in * by lia;
    (rewrite Hgh0 || rewrite Hgh1);
    rewrite (bipermutation_involutive _ Hf) by lia;
    now if_true_lia..|].
    subst P.
    assert (2 <= f (k + 2)) by 
      (enough (f (k + 2) <> 0 /\ f (k + 2) <> 1) by lia;
        rewrite 2!(bipermutation_eq_iff (k + 2) _ Hf); lia + auto_perm).
    cbn beta.
    replace_bool_lia (f (k + 2) - 2 <? n - 2) (f (k + 2) <? n).
    replace_bool_lia (f (k + 2) <? 2) false.
    bdestruct_one; [reflexivity|].
    f_equal; lia.
  - intros [b Hb].
    assert ((if f 1 - 2 <? n - 2 then g (f 1 - 2) else h (f 1 - n)) = b)
      as Hgh1. 1:{
      replace_bool_lia (f 1 - 2 <? n - 2) (f 1 <? n).
      generalize (Hb (f 1) ltac:(apply Hf; lia)).
      replace_bool_lia (f 1 <? 2) false.
      intros ->.
      rewrite (bipermutation_involutive _ Hf) by lia.
      now if_true_lia.
    }
    assert ((if f 0 - 2 <? n - 2 then g (f 0 - 2) else h (f 0 - n)) = b)
      as Hgh0. 1:{
      replace_bool_lia (f 0 - 2 <? n - 2) (f 0 <? n).
      generalize (Hb (f 0) ltac:(apply Hf; lia)).
      replace_bool_lia (f 0 <? 2) false.
      intros ->.
      rewrite (bipermutation_involutive _ Hf) by lia.
      now if_true_lia.
    }
    intros k Hk.
    generalize (Hb (k + 2) ltac:(lia)).
    replace_bool_lia (k + 2 <? n) (k <? n - 2).
    replace_bool_lia (k + 2 <? 2) false.
    rewrite Nat.add_sub.
    replace (k + 2 - n) with (k - (n - 2)) by lia.
    intros ->.
    pattern (biperm_compose_cup_l_base n m f k).
    match goal with |- ?Q ?x => set (P := Q) end.
    rewrite (biperm_compose_cup_l_base_defn n m f k Hk).
    bdestruct_one; [|bdestruct_one];
    [subst P; replace -> (k + 2);
    replace (f 0 - 2 - (n - 2)) with (f 0 - n) in * by lia;
    replace (f 1 - 2 - (n - 2)) with (f 1 - n) in * by lia;
    (rewrite Hgh0 || rewrite Hgh1);
    rewrite (bipermutation_involutive _ Hf) by lia;
    now if_true_lia..|].
    subst P.
    assert (2 <= f (k + 2)) by 
      (enough (f (k + 2) <> 0 /\ f (k + 2) <> 1) by lia;
        rewrite 2!(bipermutation_eq_iff (k + 2) _ Hf); lia + auto_perm).
    cbn beta.
    replace_bool_lia (f (k + 2) - 2 <? n - 2) (f (k + 2) <? n).
    replace_bool_lia (f (k + 2) <? 2) false.
    bdestruct_one; [reflexivity|].
    f_equal; lia.
Qed.

(* FIXME: Move to Bipermutations.v *)
Lemma biperm_eq_stack_shift_of_small_eq_swap_l n m f 
  (Hf : bipermutation (n + m) f) (Hf0 : f 0 = 1) 
  (Hn : 2 <= n) :
  perm_eq (n + m) f 
  (stack_biperms 2 0 (n - 2) m (n_m_cup_cap 1 0) (fun k => (f (k + 2) - 2))).
Proof.
  assert (Hf1 : f 1 = 0) by (rewrite (bipermutation_eq_iff _ _ Hf); lia).
  rewrite stack_biperms_0_out.
  rewrite (perm_eq_stack_parts_of_lower_bounded (n + m) 2 f) at 1;
  [|auto_perm|lia|].
  - ereflexivity.
    replace (n + m - 2) with (n - 2 + m) by lia.
    apply stack_perms_perm_eq_to_eq_proper;
    [|intros k Hk; now rewrite Nat.add_comm].
    by_perm_cell; assumption.
  - by_perm_cell; lia.
Qed. 

Lemma matrix_of_biperm_compose_cup_l_base_eq n m f (Hn : 2 <= n) 
  (Hf : bipermutation (n + m) f) (Hf0 : f 0 = 1) : 
  matrix_of_biperm (n - 2) m (biperm_compose_cup_l_base n m f) = 
  / C2 .* (matrix_of_biperm n m f × (⟦ ⊂ ⟧ ⊗ I (2 ^ (n - 2)))).
Proof.
  assert (Hf1 : f 1 = 0) by (rewrite (bipermutation_eq_iff _ _ Hf); lia).
  assert (perm_eq 2 f swap_2_perm) by (now by_perm_cell).
  symmetry.
  rewrite (biperm_eq_stack_shift_of_small_eq_swap_l n m f) at 1 by auto.
  rewrite matrix_of_stack_biperms';
  [|auto_biperm|eapply bipermutation_change_dims;
    [|apply bipermutation_shift_of_eq_swap; eassumption]; lia|lia..].
  rewrite matrix_of_biperm_n_m_cup_cap_1_0.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite cap_times_cup.
  rewrite Mmult_1_r by auto_wf.
  distribute_scale.
  rewrite kron_1_l by auto_wf.
  autorewrite with C_db.
  rewrite Mscale_1_l.
  apply matrix_of_biperm_eq_of_perm_eq.
  rewrite biperm_compose_cup_l_base_defn.
  intros k Hk.
  now do 2 if_false_lia.
Qed.

Lemma matrix_of_biperm_compose_cup_l_base_prop n m f (Hn : 2 <= n) 
  (Hf : bipermutation (n + m) f) : 
  matrix_of_biperm (n - 2) m (biperm_compose_cup_l_base n m f) [∝]
  matrix_of_biperm n m f × (⟦ ⊂ ⟧ ⊗ I (2 ^ (n - 2))).
Proof.
  bdestruct (f 0 =? 1).
  - prop_exists_nonzero (/ C2).
    now apply matrix_of_biperm_compose_cup_l_base_eq.
  - ereflexivity.
    now apply matrix_of_biperm_compose_cup_l_base_neq.
Qed.

Add Parametric Morphism n m (Hn : 2 <= n) : 
  (biperm_compose_cup_l_base n m) with signature
  perm_eq (n + m) ==> eq as biperm_compose_cup_l_base_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  eq_by_WF_perm_eq (n - 2 + m);
  [apply make_WF_Perm_WF..|].
  rewrite 2!biperm_compose_cup_l_base_defn.
  intros k Hk.
  now rewrite !Hfg by lia.
Qed.


Definition biperm_compose_arb_cup_l n m k l f :=
  biperm_compose_cup_l_base n m (
      biperm_compose_perm_l n m f (swap_to_0_1_perm k l n)).

Lemma matrix_of_biperm_compose_arb_cup_l n m k l f 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) (Hf : bipermutation (n + m) f) : 
  matrix_of_biperm (n - 2) m (biperm_compose_arb_cup_l n m k l f) [∝]
  matrix_of_biperm n m f × ⟦ zx_arb_cup k l n ⟧.
Proof.
  unfold zx_arb_cup.
  cbn [ZXCore.transpose zx_arb_cap].
  rewrite zx_of_perm_transpose, swap_from_0_1_perm_inv' by auto_perm.
  unfold zx_padded_cap.
  destruct (le_lt_dec 2 n); [|lia].
  rewrite cast_transpose.
  rewrite zx_compose_spec.
  simpl_cast_semantics.
  cbn [ZXCore.transpose].
  rewrite n_wire_transpose.
  rewrite zx_stack_spec, n_wire_semantics.
  rewrite zx_of_perm_semantics by auto_perm.
  unfold biperm_compose_arb_cup_l.
  rewrite matrix_of_biperm_compose_cup_l_base_prop by auto_biperm.
  rewrite matrix_of_biperm_compose_perm_l_eq by auto_biperm.
  now rewrite Mmult_assoc.
Qed.



(* Definition biperm_compose_arb_cap_r n m k l f :=
  flip_biperm (m - 2) n (biperm_compose_arb_cup_l m n k l (flip_biperm n m f)). *)

(* Lemma biperm_compose_arb_cap_r_bipermutation n m k l f *)

(* Lemma matrix_of_biperm_compose_arb_cup_l n m k l f 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) (Hf : bipermutation (n + m) f) : 
  matrix_of_biperm (n - 2) m (biperm_compose_arb_cup_l n m k l f) [∝]
  matrix_of_biperm n m f × ⟦ zx_arb_cup k l n ⟧.
Proof.
  unfold zx_arb_cup.
  cbn [ZXCore.transpose zx_arb_cap].
  rewrite zx_of_perm_transpose, swap_from_0_1_perm_inv' by auto_perm.
  unfold zx_padded_cap.
  destruct (le_lt_dec 2 n); [|lia].
  rewrite cast_transpose.
  rewrite zx_compose_spec.
  simpl_cast_semantics.
  cbn [ZXCore.transpose].
  rewrite n_wire_transpose.
  rewrite zx_stack_spec, n_wire_semantics.
  rewrite zx_of_perm_semantics by auto_perm.
  unfold biperm_compose_arb_cup_l.
  rewrite matrix_of_biperm_compose_cup_l_base_prop by auto_biperm.
  rewrite matrix_of_biperm_compose_perm_l_eq by auto_biperm.
  now rewrite Mmult_assoc.
Qed. *)


(*
  Lemma biperm_compose_arb_cup_l_defn_alt n m k l f 
    (Hk : k < n) (Hl : l < n) (Hkl : k <> l) (Hf : bipermutation (n + m) f) :
    perm_eq (n - 2 + m) (biperm_compose_arb_cup_l n m k l f) 
      ().
  Proof.
    cbv delta [biperm_compose_arb_cup_l] beta.
    rewrite make_WF_Perm_perm_eq.
    do 2 let_to_comp.
    assert (2 <= n) by lia.
    rewrite biperm_compose_cup_l_base_defn.

    replace (biperm_compose_perm_l n m f (swap_to_0_1_perm k l n) 0)
      with (f (min k l)).
    2: {
      rewrite biperm_compose_perm_l_defn by lia.
      unfold compose at 1.
      rewrite <- perm_inv'_eq by (lia + auto_perm).
      rewrite perm_inv'_stack_perms, idn_inv',
        swap_to_0_1_perm_inv' by (lia + auto_perm).
      
    }


    
  Lemma biperm_compose_arb_cap_r_eq n m k l f 
    (Hk : k < m) (Hl : l < m) (Hkl : k <> l) (Hf : bipermutation (n + m) f)

  .


  Definition biperm_compose_arb_cap_r (n m : nat) k l (f : nat -> nat) :=
    make_WF_Perm (n + (m - 2))
    (fun a => 
      let a' :=
        if a <? n + min k l then a else
        if a <? n + max k l - 1 then a + 1
        else a + 2 in 
      let fa' := 
        if f a' =? n + min k l then f (n + max k l) else
        if f a' =? n + max k l then f (n + min k l) else
        f a' in 
      if fa' <? n + min k l then fa' else
      if fa' <? n + max k l then fa' - 1 else
      fa' - 2).

  Lemma biperm_compose_arb_cap_r_defn n m k l f : 
    perm_eq (n + (m - 2))
      (biperm_compose_arb_cap_r n m k l f)
      (fun a => 
        let a' :=
          if a <? n + min k l then a else
          if a <? n + max k l - 1 then a + 1
          else a + 2 in 
        let fa' := 
          if f a' =? n + min k l then f (n + max k l) else
          if f a' =? n + max k l then f (n + min k l) else
          f a' in 
        if fa' <? n + min k l then fa' else
        if fa' <? n + max k l then fa' - 1 else
        fa' - 2).
  Proof.
    apply make_WF_Perm_perm_eq.
  Qed.

  Lemma biperm_compose_arb_cap_r_bipermutation n m k l f 
    (Hf : bipermutation (n + m) f) (Hk : k < m) (Hl : l < m) (Hkl : k <> l) : 
    bipermutation (n + (m - 2)) (biperm_compose_arb_cap_r n m k l f).
  Proof.
    assert (Hor : k < l \/ l < k) by lia.
    by_symmetry Hor.
    2: {
      intros a b Hab Hb Ha Hba.
      erewrite bipermutation_of_perm_eq;
      [eauto|].
      rewrite 2!biperm_compose_arb_cap_r_defn;
      intros i Hi.
      now rewrite Nat.min_comm, Nat.max_comm.
    }
    rewrite bipermutation_defn.
    assert (perm_bounded (n + (m - 2)) (biperm_compose_arb_cap_r n m k l f));
    [|split; [easy|split]].
    - intros a Ha.
      rewrite biperm_compose_arb_cap_r_defn by auto.
      rewrite Nat.min_l, Nat.max_r by lia.
      hypothesize_let. 
      hypothesize_let. 
      assert (f a' < n + m) by (apply Hf; subst a'; bdestructΩ').
      assert (f (n + k) < n + m) by (apply Hf; lia).
      assert (f (n + l) < n + m) by (apply Hf; lia).
      enough (fa' < n + m) by bdestructΩ'.
      subst fa'.
      bdestructΩ'.
    - intros a Ha.
      rewrite biperm_compose_arb_cap_r_defn by auto.
      rewrite Nat.min_l, Nat.max_r by lia.
      hypothesize_let.
      assert (a' < n + m) by (subst a'; bdestructΩ').
      hypothesize_let.
      replace a with (if a' <? n + k then a' else 
        if a' <? n + l then a' - 1 else a' - 2) 
        by (subst a'; bdestruct_all; lia).
      
      repeat bdestruct_one.
      + assert (f a <> a) by (apply Hf; lia).
        assert (f a' <> a') by (apply Hf; lia).
        assert (f (n + k) <> f (n + l)) 
          by (apply (@permutation_neq (n + m)); lia + auto_perm).
        subst fa'; rewrite 2!(bipermutation_eqb_iff _ _ Hf) by lia; bdestructΩ'.
      + subst fa'.
        (* revert H0. *)
        subst a'.
        bdestructΩ'.
      + subst fa' a'.
        bdestructΩ'.
      + subst fa' a'; bdestructΩ'.
        * enough (f (n + l) <> n + k) by lia.
          replace <- (n + k).
          apply (@permutation_neq (n + m)); lia + auto_perm.
        * enough (f (n + k) <> n + k) by lia.
          apply Hf; lia.
      + subst fa' a'; bdestructΩ'.
        * assert (f (n + l) <> f (n + k)) by 
          (apply (@permutation_neq (n + m) f); 
            auto with perm_db zarith).
          rewrite (bipermutation_eq_iff (a + 1) (n + k) Hf) in * by lia.
          replace -> (a + 1).
          enough (f (n + l) <> n + k) by lia.
          erewrite bipermutation_eq_iff; eauto with zarith.
        * assert (f (n + k) <> n + k) by (apply Hf; lia).
          assert (f (n + k) <> a + 1) 
            by (erewrite bipermutation_eq_iff; eauto with zarith).
          lia.
        * assert (f (a + 1) <> a + 1) by (apply Hf; lia).
          lia.
      + subst fa' a'; bdestructΩ'.
        * enough (f (n + l) <> n + k) by lia.
          erewrite bipermutation_eq_iff; eauto with zarith.
          replace <- (n + k).
          erewrite bipermutation_involutive; eauto with zarith.
        * enough (f (n + k) <> n + k) by lia.
          apply Hf; lia.
      + subst fa' a'; bdestructΩ'.
        * enough (f (n + l) <> n + l) by lia.
          apply Hf; lia.
        * enough (f (n + k) <> n + l) by lia.
          erewrite bipermutation_eq_iff; eauto with zarith.
          replace <- (n + l).
          erewrite bipermutation_involutive; eauto with zarith.
      + subst fa' a'; bdestructΩ'.
        * enough (f (n + l) <> n + l) by lia.
          apply Hf; lia.
        * enough (f (n + k) <> n + l) by lia.
          erewrite bipermutation_eq_iff; eauto with zarith.
          replace <- (n + l).
          erewrite bipermutation_involutive; eauto with zarith.
      + subst fa' a'; bdestructΩ'.
        * assert (f (n + l) <> f (n + k)) by 
          (apply (@permutation_neq (n + m) f); 
            now auto with perm_db zarith).
          rewrite (bipermutation_eq_iff (a + 2) (n + k) Hf) in * by lia.
          replace -> (a + 2).
          enough (f (n + l) <> n + l) by lia.
          apply Hf; lia.
        * assert (f (n + k) <> a + 2) 
            by (erewrite bipermutation_eq_iff; eauto with zarith).
          enough (f (n + k) <> n + l) by lia.
          erewrite bipermutation_eq_iff; eauto with zarith.
          replace <- (n + l).
          erewrite bipermutation_involutive; eauto with zarith.
        * assert (f (a + 2) <> a + 2) by (apply Hf; lia).
          lia.
    - rewrite 2!biperm_compose_arb_cap_r_defn at 1.
      rewrite Nat.min_l, Nat.max_r by lia.
      intros a Ha.
      change ((?f ∘ ?g) a) with ((f ∘ idn) (g a)).
      cbn beta.
      (* cbv delta [compose]. *)
      do 2 hypothesize_let.
      bdestruct (f a' =? n + k);
      [|bdestruct (f a' =? n + l)].
      + subst fa'.
        assert (f (n + l) <> n + l) by (apply Hf; lia).
        bdestruct (f (n + l) <? n + k);
        [|bdestruct (f (n + l) <? n + l)].
        --cbv delta [compose] beta.
          if_true_lia.
          simpl_let_1.
          erewrite bipermutation_involutive by eauto with zarith.
          if_false_lia.
          rewrite Nat.eqb_refl.
          cbn zeta.
          dehyp_let.
          cbn zeta.
          rewrite (bipermutation_eq_iff _ _ Hf) by bdestructΩ'.
          intros <-.
          bdestructΩ'_with ltac:(idtac); lia.
        --cbv delta [compose] beta.
          assert (f (n + l) <> n + k) 
            by (replace <- (n + k); eapply permutation_neq; subst a';
            [eauto with perm_db|lia|bdestructΩ'..]).
          if_false_lia.
          if_true_lia.
          rewrite Nat.sub_add by lia.
          simpl_let_1.
          erewrite bipermutation_involutive by eauto with zarith.
          if_false_lia.
          rewrite Nat.eqb_refl.
          cbn zeta.
          dehyp_let.
          cbn zeta.
          rewrite (bipermutation_eq_iff _ _ Hf) by bdestructΩ'.
          intros <-.
          bdestructΩ'_with ltac:(idtac); lia.
        --cbv delta [compose] beta.
          do 2 if_false_lia.
          rewrite Nat.sub_add by lia.
          simpl_let_1.
          erewrite bipermutation_involutive by eauto with zarith.
          if_false_lia.
          rewrite Nat.eqb_refl.
          cbn zeta.
          dehyp_let.
          cbn zeta.
          rewrite (bipermutation_eq_iff _ _ Hf) by bdestructΩ'.
          intros <-.
          bdestructΩ'_with ltac:(idtac); lia.
      + subst fa'.
        assert (f (n + k) <> n + k) by (apply Hf; lia).
        bdestruct (f (n + k) <? n + k);
        [|bdestruct (f (n + k) <? n + l)].
        --cbv delta [compose] beta.
          if_true_lia.
          simpl_let_1.
          erewrite bipermutation_involutive by eauto with zarith.
          rewrite Nat.eqb_refl.
          cbn zeta.
          dehyp_let.
          cbn zeta.
          intros ?.
          rewrite (bipermutation_eq_iff _ _ Hf) by bdestructΩ'.
          intros <-.
          bdestructΩ'_with ltac:(idtac); lia.
        --cbv delta [compose] beta.
          assert (f (n + k) <> n + k) 
            by (apply Hf; lia).
          if_false_lia.
          if_true_lia.
          rewrite Nat.sub_add by lia.
          simpl_let_1.
          erewrite bipermutation_involutive by eauto with zarith.
          rewrite Nat.eqb_refl.
          cbn zeta.
          dehyp_let.
          cbn zeta.
          intros ?.
          rewrite (bipermutation_eq_iff _ _ Hf) by bdestructΩ'.
          intros <-.
          bdestructΩ'_with ltac:(idtac); lia.
        --cbv delta [compose] beta.
          assert (f (n + k) <> n + l) 
            by (replace <- (n + l); eapply permutation_neq; subst a';
              [eauto with perm_db|lia|bdestructΩ'..]).
          do 2 if_false_lia.
          rewrite Nat.sub_add by lia.
          simpl_let_1.
          erewrite bipermutation_involutive by eauto with zarith.
          rewrite Nat.eqb_refl.
          cbn zeta.
          dehyp_let.
          cbn zeta.
          intros ?.
          rewrite (bipermutation_eq_iff _ _ Hf) by bdestructΩ'.
          intros <-.
          bdestructΩ'_with ltac:(idtac); lia.
      + subst fa'.
        let_to_comp.
        rewrite compose_idn_r.
        change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
        match goal with
        |- ?F ?x = a => 
          transitivity (F (f a'));
          [apply (f_equal F);bdestructΩ'|]
        end.
        unfold compose.
        rewrite (bipermutation_involutive _ Hf) by 
          (subst a'; clear -Ha; bdestructΩ').
        assert (a' <> n + k) by 
          (subst a'; clear -Ha; bdestructΩ').
        assert (a' <> n + l) by 
          (subst a'; clear -Ha Hor; bdestructΩ').
        replace_bool_lia (a' =? n + k) false.
        replace_bool_lia (a' =? n + l) false.
        subst a'.
        clear -Ha.
        bdestructΩ'.
  Qed.

  #[export] Hint Resolve biperm_compose_arb_cap_r_bipermutation : biperm_db.


  Lemma compose_zx_arb_cap_n_stacked_cups k l n
    (Hk : k < n + n) (Hl : l < n + n) (Hkl : k <> l) prf1 : 
    n_stacked_cups n ⟷ zx_arb_cap k l (n + n) ∝
    if k / 2 =? l / 2 then 
      cast _ _ eq_refl double_sub_2_prf (n_stacked_cups (n - 1))
    else
      cast _ _ eq_refl prf1 (n_stacked_cups (n - 2)) ⟷  
      zx_arb_cup (n_m_cup_cap 0 n k) (n_m_cup_cap 0 n l) _.


        apply f_equal_if_precedent.




      rewrite and_or_distr_same_r.
      2: {
        apply forall_lt_iff; intros k Hk.
        change (?x + _ <? ?x) with false.
        cbn match.
        apply iff_eq_distr; [reflexivity|].



      }

    split. 
    - intros Hcomp.
      
      + left.
        
        split.
    
    transitivity (
      (fun k  => if k <? n - 2 then g k else h (k - (n - 2))) (f 0 - 2) =
      (fun k => if k <? n - 2 then g k else h (k - (n - 2))) (f 1 - 2) /\
      funbool_preserved 
        (fun k => if k <? n - 2 then g k else h (k - (n - 2)))
        (fun k => f (k + 2)) (n - 2 + m) = true).
    - rewrite 2!funbool_preserved_iff_all_lt_eq.
      split.
      + intros Hcomp.
        rewrite <- and_impl_r;
        split;
        [|].
        intros Hf01 k Hk.
        rewrite Hcomp by auto.
        

        replace (biperm_compose_cup_l_base n m f (f 0 - 2))
        generalize (Hcomp (f 0))
    rewrite Mmult_assoc.




  Lemma matrix_of_biperm_compose_arb_cap_r_not_cancel n m k l f 
    (Hf : bipermutation (n + m) f) (Hk : k < m) (Hl : l < m) (Hkl : k <> l) 
    (Hfkl : f (n + k) <> n + l) : 
    matrix_of_biperm n (m - 2) (biperm_compose_arb_cap_r n m k l f) = 
    (⟦ zx_arb_cap k l m ⟧) × matrix_of_biperm n m f.
  Proof.
    
    apply equal_on_conj_basis_states_implies_equal; [auto_wf..|].
    intros g h.
    rewrite <- !Mmult_assoc.
    rewrite matrix_of_biperm_funbool_conj_eq by auto_biperm.
    rewrite zx_arb_cap_f_to_vec_opp by auto.
    rewrite Mplus_transpose.
    distribute_plus.
    rewrite 2!matrix_of_biperm_funbool_conj_eq by auto_perm.
    rewrite <- Mscale_plus_distr_l.
    f_equal.
    rewrite <- !(if_dist R C _ RtoC).
    do 3 fold_fun b2R.
    rewrite <- RtoC_plus.
    f_equal.
    rewrite b2R_plus_exclusive.
    2: {
      apply not_true_iff_false.
      rewrite andb_true_iff, 2!funbool_preserved_iff_all_lt_eq.
      intros [Htrue Hfalse].
      specialize (Htrue (n + min k l) ltac:(lia)).
      specialize (Hfalse (n + min k l) ltac:(lia)).
      revert Htrue Hfalse.
      if_false_lia.
      if_true_lia.
      assert (n <= f (n + min k l) -> f (n + min k l) - n <> min k l)
        by (pose proof (Hf (n + min k l)); lia).
      assert (f (n + l) <> n + k) 
        by (erewrite bipermutation_eq_iff; eauto with zarith).
      assert (n <= f (n + min k l) -> f (n + min k l) - n <> max k l)
        by (rewrite min_ltb, max_ltb; bdestruct_one; lia).
      bdestruct_all; congruence.
    }
    f_equal.
    apply eq_iff_eq_true; 
    rewrite orb_true_iff, 3!funbool_preserved_iff_all_lt_eq.
    split.
    - intros Hcomp.
      destruct (
        let fa := f (n + min k l) in 
        if fa <? n + min k l then h (fa - n) else
        if fa <? n + max k l then h (fa - n - 1) else
        h (fa - n - 2)) eqn:e.
      + left.
        intros a Ha.
        bdestruct (a <? n);
        [|bdestruct (a - n =? min k l); 
        [|bdestruct (a - n =? max k l); 
        [|bdestruct (a - n <? min k l); 
        [|bdestruct (a - n <? max k l)]]]].
        * specialize (Hcomp a ltac:(lia)); revert Hcomp.
          if_true_lia.
          intros ->.
          symmetry.
          bdestruct (f a <? n);
          [|bdestruct (f a - n =? min k l); 
          [|bdestruct (f a - n =? max k l); 
          [|bdestruct (f a - n <? min k l); 
          [|bdestruct (f a - n <? max k l)]]]].
          --replace (biperm_compose_arb_cap_r n m k l f a) with (f a);
            [now if_true_lia|].
            rewrite biperm_compose_arb_cap_r_defn by lia.
            if_true_lia.
            simpl_let_1.
            do 2 if_false_lia.
            cbn zeta.
            now if_true_lia.
          --assert (a = f (n + min k l)) by 
              (apply (bipermutation_eq_iff _ _ Hf); lia).
            subst a.
          do 2 bdestruct_one.

    (* let fpat := uconstr:(fun x => ltac:(app_beta fdef uconstr:(_) in 
    idtac fpat. *)
    (* match constr:(fun x : nat => x + x) with 
    | fun x => @?F x => idtac F
    end.
    assert (1 + 2 + 5 + f (1 + 2) + Nat.b2n (f 0 =? 0) = 0). *)
    (* Tactic Notation "eunify" open_constr(x) open_constr(y) :=
    unify x y. *)

    Ltac print_pat f :=
      match type of f with 
      | forall _ : ?A, _ => 
        let r := constr:(fun x : A => 
        ltac:(let fx := eval hnf in (f x) in 
        match fx with 
        | context E [x] => 
          let r := uconstr:(context E [_]) in 
          idtac r
        end;
        let pf := eval pattern x in fx in 
        (* idtac pf; *)
        exact (f x)
        )) in 
        idtac
      end.
    print_pat Nat.b2n.
    
    Ltac efold1 f :=
      let fhole := open_constr:(f _) in 
    let fdef := eval hnf in fhole in 
    match goal with 

    idtac fdef.
    efold1 Nat.b2n.
    idtac fhold.
    

    let r := eunify
    match goal with 
    |- context E [Nat.add ?x ?y] => idtac E
    end.

    (* let r := uconstr:(subst! _ for x in x + x) in  *)
    let r := uconstr:(_ + _) in idtac r.
    evar (x : nat).
    fold (b2R (funbool_preserved (fun k0 : nat => if k0 <? n then g k0 else h (k0 - n))
    (biperm_compose_arb_cap_r n m k l f) (n + (m - 2)))).
    
    match goal with 
    |- context E [?x + ?x] => idtac E
    end.
    let r' := eval cbv beta in (fun x => r ) in 
    idtac r'.
    efold1 b2R.
    fold (b2R _).
    destruct (f (n + k))
    distribute_scale.


  Lemma compose_biperms_arb_cap_r n m k l f (Hf : bipermutation (n + m) f)
    (Hk : k < m) (Hl : l < m) (Hkl : k <> l) :
    perm_eq (n + (m - 2)) 
      (compose_biperms n m (m - 2) f (arb_cap_biperm k l m))
      (fun a => 
        if a <? n then 
          if f a <? n then f a else
          if f a =? n + k then f (n + l) else 
          if f a =? n + l then f (n + k) else
          if f a <? n + min k l then f a else
          if f a <? n + max k l then f a - 1 else
          ) 
*)


(* Lemma funbool_preserved_compose_biperms_spec n m o f g 
  (Hf : bipermutation (n + m) f) (Hg : bipermutation (m + o) g) : 
  forall i j, i < 2 ^ o -> j < 2 ^ n -> 
  matrix_of_biperm n o (compose_biperms n m o f g) i j = C0 <->
  forall k, k < 2 ^ m ->
  matrix_of_biperm n m f k j = C0 \/
  matrix_of_biperm m o g i k = C0. *)

(* Lemma matrix_compose_biperms_spec n m o f g 
  (Hf : bipermutation (n + m) f) (Hg : bipermutation (m + o) g) : 
  matrix_of_biperm n o (compose_biperms n m o f g) ≡
  (if ) *)


Fixpoint func_of_nrel n (f : nat -> nat -> bool) :=
  match n with 
  | 0 => fun k => k
  | S n' => fun k => if f k n' then n' else func_of_nrel n' f k
  end.

Lemma func_of_nrel_of_nonrel n f k : 
  (forall a, a < n -> f k a = false) -> 
  func_of_nrel n f k = k.
Proof.
  intros Hf.
  induction n; [easy|].
  cbn.
  rewrite Hf by auto.
  apply IHn; auto.
Qed.

Lemma func_of_nrel_irrefl_idn_iff n f k : 
  (forall a, a < n -> f a a = false) -> 
  func_of_nrel n f k = k <-> (forall a, a < n -> f k a = false).
Proof.
  intros Hirrefl.
  split; [|apply func_of_nrel_of_nonrel].
  induction n; [easy|].
  cbn.
  destruct (f k n) eqn:Hfkn.
  - intros ->.
    now rewrite Hirrefl in Hfkn by auto.
  - intros Heq.
    rewrite forall_nat_lt_S.
    split; [easy|].
    apply IHn; auto.
Qed.

Lemma func_of_nrel_bounded_or_idn_spec n f k : 
  (f k (func_of_nrel n f k) = true /\ func_of_nrel n f k < n /\
  (forall a, func_of_nrel n f k < a < n -> f k a = false)) \/ 
  ((forall a, a < n -> f k a = false) /\ (func_of_nrel n f k = k)).
Proof.
  induction n.
  - right; easy.
  - cbn.
    destruct (f k n) eqn:fkn;
    [left; intuition lia|].
    destruct IHn as [(Hftrue & Hbdd & Hffalse) | (Hffalse & Heq)].
    + left.
      split; [easy|split; [lia|]].
      intros a Ha.
      bdestruct (a =? n); [now subst|].
      auto with zarith.
    + right.
      split; [|auto].
      rewrite forall_nat_lt_S.
      easy.
Qed.

Lemma func_of_nrel_eq_iff n f k l :
  func_of_nrel n f k = l <->
  (f k l = true /\ l < n /\ (forall a, l < a < n -> f k a = false)) \/
  ((forall a, a < n -> f k a = false) /\ l = k).
Proof.
  split.
  - intros <-.
    apply func_of_nrel_bounded_or_idn_spec.
  - intros [(Hfk & Hl & Hffalse) | (Hffalse & Hl)].
    + induction Hl.
      * cbn.
        now rewrite Hfk.
      * specialize (IHHl ltac:(auto with zarith)).
        cbn.
        rewrite Hffalse by auto.
        apply IHHl.
    + subst.
      now apply func_of_nrel_of_nonrel.
Qed.

Definition nrel_of_func (f : nat -> nat) :=
  fun k l => f k =? l.

Lemma func_of_nrel_of_func_bounded f n (Hf : perm_bounded n f) : 
  perm_eq n (func_of_nrel n (nrel_of_func f)) f.
Proof.
  intros k Hk.
  rewrite func_of_nrel_eq_iff.
  left. 
  split; [apply Nat.eqb_eq; reflexivity|].
  split; [now apply Hf|].
  intros a Ha.
  apply Nat.eqb_neq.
  lia.
Qed.


Lemma func_of_nrel_bounded_of_related n f k (Hk : k < n) : 
  f k (func_of_nrel n f k) = true -> 
  func_of_nrel n f k < n.
Proof.
  destruct (func_of_nrel_bounded_or_idn_spec n f k).
  - easy.
  - intuition congruence.
Qed.

Definition nrel_functional n (f : nat -> nat -> bool) :=
  forall k, k < n -> 
  exists! l, l < n /\ f k l = true.

Lemma nrel_functional_iff_eq_func_of_nrel f n : 
  nrel_functional n f <-> 
  (forall k, k < n -> 
  f k (func_of_nrel n f k) = true /\ 
  forall l, l < n -> l <> func_of_nrel n f k -> 
  f k l = false).
Proof.
  symmetry; split.
  - intros Hall.
    intros k Hk.
    specialize (Hall k Hk) as [Hfk Hfnotk].
    exists (func_of_nrel n f k); split.
    + auto using func_of_nrel_bounded_of_related, Hfk.
    + intros l [Hl Hfl].
      specialize (Hfnotk l Hl).
      bdestructΩ (func_of_nrel n f k =? l).
      specialize (Hfnotk ltac:(auto)).
      congruence.
  - intros Hfunc k Hk.
    pose proof (Hfunc k Hk) as (fk & [Hfk Hfkfk] & Hfkunique).
    destruct (func_of_nrel_bounded_or_idn_spec n f k) as
    [? | [Hfalse _]];
    [|now rewrite Hfalse in Hfkfk by auto].
    assert (fk = func_of_nrel n f k) by (now apply Hfkunique).
    subst fk.
    split; [easy|].
    intros l Hl Hne.
    apply not_true_iff_false.
    intros Htrue.
    apply Hne; symmetry; auto.
Qed.

Lemma nrel_functional_iff_eq_func_of_nrel_alt f n : 
  nrel_functional n f <-> 
  (forall k, k < n -> 
  f k (func_of_nrel n f k) = true /\ 
  forall l, l < n -> f k l = true -> 
  l = func_of_nrel n f k).
Proof.
  rewrite nrel_functional_iff_eq_func_of_nrel.
  apply forall_lt_iff.
  intros k Hk.
  apply ZifyClasses.and_morph; [reflexivity|].
  apply forall_lt_iff.
  intros l Hl.
  rewrite <- not_true_iff_false.
  intuition lia.
Qed.

Lemma nrel_of_func_of_nrel_functional f n (Hf : nrel_functional n f) : 
  forall k l, k < n -> l < n -> 
  f k l = nrel_of_func (func_of_nrel n f) k l.
Proof.
  intros k l Hk Hl.
  rewrite nrel_functional_iff_eq_func_of_nrel in Hf.
  bdestruct (l =? func_of_nrel n f k). 
  - subst.
    unfold nrel_of_func.
    rewrite Nat.eqb_refl.
    now apply Hf.
  - rewrite (fun k Hk => proj2 (Hf k Hk)) by auto.
    symmetry.
    apply Nat.eqb_neq.
    easy.
Qed.

Lemma nrel_of_bounded_functional n f (Hf : perm_bounded n f) :
  nrel_functional n (nrel_of_func f).
Proof.
  intros k Hk.
  exists (f k).
  split; [split; [auto|apply Nat.eqb_refl]|].
  intros l [Hl Hleq].
  now apply Nat.eqb_eq in Hleq.
Qed.

Lemma nrel_of_func_functional_iff_bounded n f : 
  nrel_functional n (nrel_of_func f) <-> perm_bounded n f.
Proof.
  split; [|apply nrel_of_bounded_functional].
  intros Hfunc k Hk.
  specialize (Hfunc k Hk) as [fk [[Hfk Hfkeq]]].
  apply Nat.eqb_eq in Hfkeq.
  now subst.
Qed.

Lemma nrel_of_func_permutation_spec n f (Hf : permutation n f) : 
  nrel_functional n (nrel_of_func f) /\
  nrel_functional n (fun k l => nrel_of_func f l k).
Proof.
  split; [apply nrel_of_bounded_functional; auto_perm|].
  intros k Hk.
  exists (perm_inv n f k).
  split.
  - split; [auto_perm|].
    apply Nat.eqb_eq.
    apply perm_inv_is_rinv_of_permutation; auto.
  - intros l [Hl Hfl%Nat.eqb_eq].
    rewrite perm_inv_eq_iff by auto_perm.
    auto.
Qed.

Lemma nrel_of_func_permutation_spec_iff n f : 
  permutation n f <->
  nrel_functional n (nrel_of_func f) /\
  nrel_functional n (fun k l => nrel_of_func f l k).
Proof.
  split; [apply nrel_of_func_permutation_spec|].
  intros [_ Hfunc].
  unfold nrel_functional, nrel_of_func in Hfunc.
  apply permutation_iff_surjective.
  intros k Hk.
  destruct (Hfunc k Hk) as [l [[Hl Hfl%Nat.eqb_eq] ?]].
  now exists l.
Qed.

Definition perm_nrel_eq n (f g : nat -> nat -> bool) :=
  forall k l, k < n -> l < n -> f k l = g k l.

Lemma perm_nrel_eq_refl n f : perm_nrel_eq n f f.
Proof. easy. Qed.

Lemma perm_nrel_eq_sym n f g : perm_nrel_eq n f g -> perm_nrel_eq n g f.
Proof. intros ? ? **; symmetry; auto. Qed.

Lemma perm_nrel_eq_trans n f g h : perm_nrel_eq n f g -> 
  perm_nrel_eq n g h -> perm_nrel_eq n f h.
Proof. intros ? ? ? **; etransitivity; eauto. Qed.

Add Parametric Relation n : (nat -> nat -> bool) (perm_nrel_eq n) 
  reflexivity proved by (perm_nrel_eq_refl n)
  symmetry proved by (perm_nrel_eq_sym n)
  transitivity proved by (perm_nrel_eq_trans n) 
  as perm_nrel_eq_setoid.

Lemma func_of_nrel_perm_eq_to_eq_helper n m f g 
  (Hfg : perm_nrel_eq n f g) : m <= n ->
  perm_eq n (func_of_nrel m f) (func_of_nrel m g).
Proof.
  intros H.
  induction m; [easy|].
  intros k Hk.
  specialize (IHm ltac:(lia)).
  cbn.
  now rewrite Hfg, IHm by auto.
Qed.

Add Parametric Morphism n : (func_of_nrel n) with signature
  perm_nrel_eq n ==> perm_eq n as func_of_nrel_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  now apply func_of_nrel_perm_eq_to_eq_helper.
Qed.

Lemma func_of_nrel_permutation_iff n f (Hf : nrel_functional n f) : 
  permutation n (func_of_nrel n f) <->
  nrel_functional n (fun k l => f l k).
Proof.
  split.
  - intros Hperm.
    rewrite nrel_functional_iff_eq_func_of_nrel_alt in Hf.
    intros k Hk.
    exists (perm_inv n (func_of_nrel n f) k).
    split; [split; [auto_perm|]|].
    + erewrite <- (fun H => 
      proj1 (Hf (perm_inv n (func_of_nrel n f) k) H)) by auto_perm.
      now rewrite perm_inv_is_rinv_of_permutation.
    + intros l [Hl Hflk].
      rewrite perm_inv_eq_iff by auto_perm.
      apply Hf; auto.
  - intros Hfunc.
    apply permutation_iff_surjective.
    intros k Hk.
    destruct (Hfunc k Hk) as (l & [Hl Hfl] & Hlunique).
    destruct (Hf l Hl) as (k' & [Hk' Hfk'] & Hk'unique).
    assert (k' = k) by (now apply Hk'unique).
    subst.
    exists l.
    split; [easy|].
    rewrite func_of_nrel_eq_iff.
    left.
    split; [easy|].
    split; [easy|].
    intros a [].
    apply not_true_iff_false.
    intros Htrue.
    specialize (Hk'unique a ltac:(auto)).
    lia.
Qed.


Lemma nrel_of_bipermutation_spec n f (Hf : bipermutation n f) : 
  (forall k, k < n -> nrel_of_func f k k = false) /\ 
  perm_nrel_eq n (nrel_of_func f) (fun k l => nrel_of_func f l k) /\
  nrel_functional n (fun k l => nrel_of_func f l k).
Proof.
  split; [|split; [|apply nrel_of_func_permutation_spec; auto_perm]].
  - intros k Hk;
    now apply Nat.eqb_neq, Hf.
  - intros k l Hk Hl.
    apply eq_iff_eq_true.
    unfold nrel_of_func.
    rewrite (bipermutation_eqb_iff _ _ Hf) by auto.
    now rewrite Nat.eqb_sym.
Qed.

Add Parametric Morphism n : (nrel_functional n) with signature
  perm_nrel_eq n ==> iff as nrel_functional_perm_nrel_eq_to_iff.
Proof.
  intros f g Hfg.
  unfold nrel_functional.
  apply forall_lt_iff.
  intros k Hk.
  split.
  - intros (l & Hl & Hlunique).
    exists l.
    split; [now rewrite <- Hfg|].
    intros a [].
    rewrite <- Hfg in * by easy.
    now apply Hlunique.
  - intros (l & Hl & Hlunique).
    exists l.
    split; [now rewrite Hfg|].
    intros a [].
    rewrite Hfg in * by easy.
    now apply Hlunique.
Qed.

Lemma func_of_nrel_bipermutation_iff n f (Hf : nrel_functional n f) : 
  bipermutation n (func_of_nrel n f) <->
  (forall k, k < n -> f k k = false) /\
  perm_nrel_eq n f (fun k l => f l k).
Proof.
  split.
  - intros Hbiperm.
    split.
    + intros k Hk.
      pose proof (Hbiperm k Hk) as (Hbdd & Hne & Hff).
      rewrite nrel_functional_iff_eq_func_of_nrel in Hf.
      now apply Hf.
    + intros k l Hk Hl.
      rewrite 2!(nrel_of_func_of_nrel_functional f n) by easy.
      apply eq_iff_eq_true.
      unfold nrel_of_func.
      rewrite 2!Nat.eqb_eq.
      erewrite bipermutation_eq_iff; eauto.
      easy.
  - intros [Hirrefl Hsym].
    rewrite bipermutation_defn_alt.
    assert (permutation n (func_of_nrel n f)) by 
      now rewrite func_of_nrel_permutation_iff, <- Hsym by auto.
    split; [easy|split].
    + intros k Hk.
      rewrite func_of_nrel_eq_iff.
      specialize (Hirrefl k Hk).
      intros [[]|[Hfalse _]]; [congruence|].
      destruct (Hf k Hk) as (l & [Hl ?] & _).
      specialize (Hfalse l Hl).
      congruence.
    + apply (compose_perm_inv_l _ _ idn);
      [auto_perm..|].
      symmetry.
      intros k Hk.
      unfold compose.
      rewrite func_of_nrel_eq_iff.
      left.
      rewrite nrel_functional_iff_eq_func_of_nrel in Hf.
      pose proof (Hf k Hk).
      split; [now rewrite Hsym by auto_perm|].
      split; [easy|].
      intros a Ha.
      rewrite Hsym by auto_perm.
      apply Hf; auto_perm.
      eapply permutation_neq; eauto with zarith.
Qed.


(* Lemma compose_biperms_spec_defn n m o f g 
  (Hf : bipermutation (n + m) f) (Hg : bipermutation (m + o) g) : 
  perm_eq (n + o) (compose_biperms n m o f g)
  (fun ) *)


(* Lemma compose_biperms_spec n m o f g 
  (Hf : bipermutation (n + m) f) (Hg : bipermutation (m + o) g) : 
  compose_biperms n m o f g  *)







Lemma double_sub_2_prf {n} : n + n - 2 = n - 1 + (n - 1).
Proof. lia. Qed.

Lemma n_stacked_cups_compose_zx_padded_cap n : 
  n_stacked_cups n ⟷ zx_padded_cap (n + n) ∝
  cast _ _ eq_refl double_sub_2_prf (n_stacked_cups (n - 1)).
Proof.
  destruct n.
  - cbn -[cast].
    rewrite cast_id.
    unfold n_stacked_cups.
    rewrite cast_id.
    cbn.
    rewrite compose_empty_l.
    apply Z_0_0_is_empty.
  - unfold zx_padded_cap.
    destruct (le_lt_dec 2 (S n + S n)); [|lia].
    rewrite n_stacked_cups_succ.
    rewrite <- ((fun H => cast_n_wire H H) 
      (ltac:(lia) : S n + S n - 2 = n + n)).
    rewrite cast_stack_r_fwd, cast_contract_eq.
    rewrite cast_compose_eq_mid_join.
    rewrite <- stack_compose_distr.
    rewrite cup_cap, stack_empty_l.
    rewrite nwire_removal_r.
    apply ZX_prop_by_mat_prop.
    simpl_cast_semantics.
    ereflexivity.
    cbn.
    rewrite 2!n_stacked_cups_semantics.
    now rewrite Nat.sub_0_r.
Qed.

Create HintDb divmod_db discriminated.
#[export] Hint Resolve 
  Nat.Div0.div_lt_upper_bound Nat.mod_upper_bound 
  Nat.div_le_lower_bound : divmod_db.

Ltac dmlia :=
  auto with divmod_db zarith.

(* FIXME: Move *)
Lemma n_stacked_cups_resize {n m} (H : n = m) :
  n_stacked_cups n = 
  cast _ _ eq_refl (f_equal Nat.double H) (n_stacked_cups m).
Proof.
  subst.
  reflexivity.
Qed.

(* FIXME: Move *)
Lemma swap_from_0_1_perm_0_1 n :
  swap_from_0_1_perm 0 1 n = idn.
Proof.
  eq_by_WF_perm_eq n.
  rewrite swap_from_0_1_perm_defn.
  intros a Ha.
  destruct a as [|[| a]]; reflexivity.
Qed.

Lemma le_lt_dec_le {n m} (H : n <= m) : 
  le_lt_dec n m = left H.
Proof.
  destruct (le_lt_dec n m); [|lia].
  f_equal.
  apply Peano_dec.le_unique.
Qed.

Lemma lt_unique : forall n m (h1 h2 : n < m), h1 = h2.
Proof.
  intros.
  apply Peano_dec.le_unique.
Qed.

Lemma le_lt_dec_lt {n m} (H : m < n) : 
  le_lt_dec n m = right H.
Proof.
  destruct (le_lt_dec n m); [lia|].
  f_equal.
  apply lt_unique.
Qed.


Lemma zx_arb_cap_0_1 n (Hn : 2 <= n) : 
  zx_arb_cap 0 1 n ∝
  cast n (n-2) (zx_padded_cap_prf Hn) eq_refl
  (⊃ ↕ n_wire (n - 2)).
Proof.
  unfold zx_arb_cap.
  rewrite swap_from_0_1_perm_0_1, zx_of_perm_idn, nwire_removal_l.
  unfold zx_padded_cap.
  rewrite (le_lt_dec_le Hn).
  apply cast_simplify.
  reflexivity.
Qed.

Lemma zx_arb_cap_lt_2 k l n (Hk : k < 2) (Hl : l < 2) 
  (Hkl : k <> l) (Hn : 2 <= n) : 
  zx_arb_cap k l n ∝
  cast n (n-2) (zx_padded_cap_prf Hn) eq_refl
  (⊃ ↕ n_wire (n - 2)).
Proof.
  assert (Hor : k < l \/ l < k) by lia.
  by_symmetry Hor 
    by (intros ? ? H ? ?; rewrite zx_arb_cap_comm; auto).
  replace k with 0 in * by lia.
  replace l with 1 in * by lia.
  apply zx_arb_cap_0_1.
Qed.


Lemma compose_zx_arb_cap_n_stacked_cups_base k l n 
  (Hk : k < 2) (Hl : l < 2) (Hkl : k <> l) : 
  n_stacked_cups n ⟷ zx_arb_cap k l (n + n) ∝
  cast _ _ eq_refl (double_sub_2_prf) (n_stacked_cups (n - 1)).
Proof.
  destruct n as [|n].
  - rewrite cast_id.
    unfold zx_arb_cap.
    rewrite zx_of_perm_0.
    unfold zx_padded_cap.
    simpl.
    rewrite compose_empty_l.
    etransitivity; [|apply compose_empty_r].
    apply compose_simplify_r.
    apply Z_0_0_is_empty.
  - auto_cast_eqn rewrite zx_arb_cap_lt_2 by auto.
    rewrite n_stacked_cups_succ.
    rewrite cast_compose_l, cast_contract_eq.
    auto_cast_eqn erewrite (cast_stack_distribute (m':=0) (p':=S n + S n - 2) _ _ _ 
      eq_refl _ _ ⊃ (n_wire (S n + S n - 2))).
    rewrite cast_id.
    rewrite (stack_split_diag ⊃), <- compose_assoc.
    rewrite <- stack_compose_distr, cup_cap.
    rewrite 2!stack_empty_l.
    rewrite nwire_removal_r, cast_compose_r.
    rewrite nwire_removal_r.
    rewrite 2!cast_contract_eq.
    rewrite (n_stacked_cups_resize (ltac:(lia) : S n - 1 = n)).
    rewrite cast_contract_eq.
    apply cast_simplify.
    reflexivity.
Qed.

(* Lemma zx_arb_cap_small k l n (Hk : k < 4) (Hl : l < 4) 
  (Hkl : k / 2 = l / 2) (Hn : 4 <= n) :
  zx_arb_cap k l n ∝ 
  cast _ _ _ _ () *)

(* Lemma comp_zx_arb_small_prf {n} (Hn : 2 <= n) : 
  n + n - 2 = 2 + (n - 2 + (n - 2)).
Proof. lia. Qed. *)

Lemma zx_arb_split_prf {n m} (Hn : 2 <= n) : 
  n + m - 2 = n - 2 + m.
Proof. lia. Qed.

Lemma swap_from_0_1_perm_split_r k l n m 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) :
  swap_from_0_1_perm k l (n + m) = 
  stack_perms n m (swap_from_0_1_perm k l n) idn.
Proof.
  eq_by_WF_perm_eq (n + m).
  rewrite 2!swap_from_0_1_perm_defn, stack_perms_defn.
  intros a Ha.
  bdestructΩ'.
Qed.

Lemma zx_padded_cap_add_r n m (Hn : 2 <= n) : 
  zx_padded_cap (n + m) ∝ 
  cast _ _ eq_refl (zx_arb_split_prf Hn) (zx_padded_cap n ↕ n_wire m).
Proof.
  unfold zx_padded_cap.
  rewrite (le_lt_dec_le Hn).
  rewrite (le_lt_dec_le (ltac:(lia) : 2 <= n + m)).
  rewrite cast_stack_l_fwd.
  auto_cast_eqn rewrite stack_assoc, n_wire_stack.
  rewrite 2!cast_contract_eq.
  rewrite <- ((fun H => cast_n_wire H H) (ltac:(lia) : n+m-2=n-2+m)).
  rewrite cast_stack_r_fwd.
  rewrite cast_contract_eq.
  apply cast_simplify.
  reflexivity.
Qed.


Lemma zx_arb_cap_split_nwire_r k l n m (Hk : k < n) (Hl : l < n) 
  (Hkl : k <> l) (Hn : 2 <= n) :
  zx_arb_cap k l (n + m) ∝
  cast _ _ eq_refl (zx_arb_split_prf Hn) (zx_arb_cap k l n ↕ n_wire m).
Proof.
  unfold zx_arb_cap.
  rewrite swap_from_0_1_perm_split_r by auto.
  auto_cast_eqn rewrite zx_padded_cap_add_r.
  rewrite <- stack_zx_of_perm by auto_perm.
  rewrite cast_compose_r_eq_mid.
  rewrite <- stack_compose_distr.
  rewrite zx_of_perm_idn, nwire_removal_l.
  apply cast_simplify.
  reflexivity.
Qed.

Lemma zx_arb_cap_resize {n m} (H : n = m) k l :
  zx_arb_cap k l n ∝ 
  cast _ _ H (f_equal (fun x => x - 2) H)
  (zx_arb_cap k l m).
Proof.
  subst.
  reflexivity.
Qed.

Lemma n_stacked_cups_add n m : 
  n_stacked_cups (n + m) ∝
  cast _ _ eq_refl (double_add _ _) (n_stacked_cups n ↕ n_stacked_cups m).
Proof.
  unfold n_stacked_cups.
  rewrite cast_stack_l_fwd, cast_stack_r_fwd.
  auto_cast_eqn rewrite nstack_split.
  rewrite !cast_contract_eq.
  apply cast_simplify.
  reflexivity.
Qed.

Lemma zx_arb_cap_4_cases k l (Hk : k < 2) (Hl : 2 <= l < 4) : 
  zx_arb_cap k l 4 ∝
  (if k =? 0 then ⨉ else n_wire 2) ↕
  (if l =? 3 then ⨉ else n_wire 2) ⟷
  (— ↕ ⊃ ↕ —).
Proof.
  apply ZXbiperm_prop_by_biperm_eq; 
    [bdestruct_all; auto with zxbiperm_db zxperm_db..|].
  rewrite biperm_of_zx_arb_cap by lia.
  simpl.
  assert (Hk' : k = 0 \/ k = 1) by lia.
  assert (Hl' : l = 2 \/ l = 3) by lia.
  destruct Hk', Hl'; subst; simpl; by_perm_cell; reflexivity.
Qed.

Lemma cup_cup_cap_yank : 
  ⊂ ↕ ⊂ ⟷ (— ↕ ⊃ ↕ —) ∝ ⊂.
Proof.
  apply ZXbiperm_prop_by_biperm_eq; 
    [auto with zxbiperm_db..|].
  simpl.
  by_perm_cell; reflexivity.
Qed.

Lemma compose_zx_arb_cap_n_stacked_cups_small k l n 
  (Hk : k < 4) (Hl : l < 4) (Hkl : k / 2 <> l / 2) (Hn : 2 <= n) : 
  n_stacked_cups n ⟷ zx_arb_cap k l (n + n) ∝
  cast _ _ eq_refl double_sub_2_prf (n_stacked_cups (n - 1)).
Proof.
  assert (Hkl' : k <> l) by (intros ->; lia).
  assert (H : n = 2 + (n - 2)) by lia.
  rewrite (n_stacked_cups_resize H).
  assert (H' : n + n = 4 + (n - 2 + (n - 2))) by lia.
  rewrite (zx_arb_cap_resize H').
  rewrite n_stacked_cups_add, cast_contract_eq.
  rewrite cast_compose_eq_mid_join.
  auto_cast_eqn rewrite zx_arb_cap_split_nwire_r by lia.
  rewrite cast_compose_r_eq_mid.
  assert (H'' : n - 1 = 1 + (n - 2)) by lia.
  rewrite (n_stacked_cups_resize H'').
  rewrite n_stacked_cups_add.
  rewrite 3!cast_contract_eq.
  rewrite <- stack_compose_distr.
  rewrite nwire_removal_r.
  apply cast_simplify.
  apply stack_simplify; [|reflexivity].
  assert (Hor : k < l \/ l < k) by lia.
  by_symmetry Hor 
    by (intros ? ? Hi **; rewrite zx_arb_cap_comm; apply Hi; lia).
  assert (Hkl2 : k / 2 < l / 2) by 
    (enough (k / 2 <= l / 2) by lia;
    apply div0_div_le_mono; lia).
  assert (l / 2 < 2) by dmlia.
  assert (k / 2 = 0) as Hk2 by lia.
  assert (l / 2 = 1) as Hl2 by lia.
  rewrite div_eq_iff in Hk2, Hl2 by easy.
  rewrite zx_arb_cap_4_cases by lia.
  unfold n_stacked_cups.
  cbn [n_stack].
  rewrite <- compose_assoc.
  auto_cast_eqn rewrite stack_empty_r.
  rewrite !cast_id.
  rewrite <- (stack_compose_distr ⊂ _ ⊂).
  etransitivity; [|apply cup_cup_cap_yank].
  apply compose_simplify; [|reflexivity].
  rewrite 2!(if_dist _ _ _ (fun x => ⊂ ⟷ x)).
  apply stack_simplify; bdestruct_one;
  apply cup_swap_absorbtion + apply nwire_removal_r.
Qed.
   





(* FIXME: Move to PermutationFacts.v *)
Lemma tensor_perms_lt_iff_gen n m f g k (Hk : k < n * m) : 
  tensor_perms n m f g k < m <->
  f (k / m) = 0 /\ g (k mod m) < m.
Proof.
  rewrite tensor_perms_defn by auto.
  nia.
Qed.

Lemma tensor_perms_lt n m f g k (Hk : k < n * m) 
  (Hg : perm_bounded m g) : 
  f (k / m) = 0 ->
  tensor_perms n m f g k < m.
Proof.
  rewrite tensor_perms_lt_iff_gen by auto.
  specialize (Hg (k mod m)).
  dmlia.
Qed.

Lemma swap_to_0_1_perm_left_min k l n (Hk : k <= l) (Hl : l < n) : 
  swap_to_0_1_perm k l n k = 0.
Proof.
  rewrite swap_to_0_1_perm_defn by lia.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_right_min k l n (Hk : k <= l) (Hl : l < n) : 
  swap_to_0_1_perm l k n k = 0.
Proof.
  rewrite swap_to_0_1_perm_defn by lia.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_left_max k l n (Hl : l < k) (Hk : k < n) : 
  swap_to_0_1_perm k l n k = 1.
Proof.
  rewrite swap_to_0_1_perm_defn by lia.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_right_max k l n (Hl : l < k) (Hk : k < n) : 
  swap_to_0_1_perm l k n k = 1.
Proof.
  rewrite swap_to_0_1_perm_defn by lia.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_min k l n (Hk : k < n) (Hl : l < n) : 
  swap_to_0_1_perm k l n (min k l) = 0.
Proof.
  rewrite swap_to_0_1_perm_defn by lia.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_max k l n (Hk : k < n) (Hl : l < n) (Hkl : k <> l) :
  swap_to_0_1_perm k l n (max k l) = 1.
Proof.
  rewrite swap_to_0_1_perm_defn by lia.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_neither_bound k l a n 
  (Ha : a < n) (Hak : a <> k) (Hal : a <> l) (Hkl : k <> l) :
  2 <= swap_to_0_1_perm k l n a.
Proof.
  rewrite swap_to_0_1_perm_defn by lia.
  bdestructΩ'.
Qed.

Lemma swap_to_0_1_perm_neither k l a n 
  (Ha : a < n) (Hak : a <> k) (Hal : a <> l) (Hkl : k <> l) :
  swap_to_0_1_perm k l n a = 
  if a <? min k l then a + 2 else if a <? max k l then a + 1 else a.
Proof.
  rewrite swap_to_0_1_perm_defn by lia.
  bdestructΩ'.
Qed.


Lemma comp_zx_cap_stacked_prf {n} : n + n - 2 - 2 = n - 2 + (n - 2).
Proof. lia. Qed.

Lemma n_stacked_cups_biperm_semantics n : 
  ⟦ n_stacked_cups n ⟧ = matrix_of_biperm 0 (n + n) (n_m_cup_cap 0 n).
Proof.
  rewrite matrix_of_biperm_n_m_cup_cap_0_l.
  apply n_stacked_cups_semantics.
Qed.

Lemma n_stacked_caps_biperm_semantics n : 
  ⟦ n_stacked_caps n ⟧ = matrix_of_biperm (n + n) 0 (n_m_cup_cap n 0).
Proof.
  rewrite matrix_of_biperm_n_m_cup_cap_0_r.
  apply n_stacked_caps_semantics.
Qed.

Lemma compose_zx_arb_cap_n_stacked_cups_step1 k l n
  (Hk : k < n + n) (Hl : l < n + n) (Hkl : k <> l) : 
  n_stacked_cups n ⟷ zx_arb_cap k l (n + n) ∝
  (zx_arb_cup k l (n + n) ⟷ n_stacked_caps n) ⊤%ZX.
Proof.
  cbn [ZXCore.transpose].
  unfold zx_arb_cup.
  rewrite <- n_stacked_cups_tranpose, 2!Proportional.transpose_involutive.
  reflexivity.
Qed.


Lemma matrix_of_zx_of_bipermutation n m f Hf : 
  ⟦ zx_of_bipermutation n m f Hf ⟧ =
  matrix_of_biperm n m f.
Proof.
  unfold zx_of_bipermutation.
  simpl_cast_semantics.
  unfold zx_of_NF_uncasted.
  pose proof (NF_of_biperm_spec n m f Hf) as (HWF & Hin & Hout & Hreal).
  pose proof HWF as (Hins & Houts & Hperml & Hpermr).
  rewrite <- (matrix_of_biperm_eq_of_perm_eq Hreal).
  rewrite (matrix_of_realize_NF_biperm' n m) by assumption + congruence.
  cbn -[NF_of_biperm].
  rewrite Hins in Hperml. rewrite Houts in Hpermr.
  rewrite 2!zx_of_perm_semantics by auto.
  rewrite n_wire_semantics.
  rewrite n_stacked_cups_semantics, n_stacked_caps_semantics.
  rewrite matrix_of_biperm_n_m_cup_cap_split, 
    matrix_of_biperm_n_m_cup_cap_0_l, matrix_of_biperm_n_m_cup_cap_0_r.
  rewrite Mmult_assoc.
  rewrite <- Hins, <- Houts, Hin, Hout.
  reflexivity.
Qed.

Lemma matrix_of_zx_of_biperm n m f (Hf : bipermutation (n + m) f) : 
  ⟦ zx_of_biperm n m f ⟧ =
  matrix_of_biperm n m f.
Proof.
  rewrite zx_of_biperm_bipermutation with n m f Hf.
  apply matrix_of_zx_of_bipermutation.
Qed.

(* FIXME: Move *)
Lemma biperm_compose_arb_cup_l_bipermutation n m k l
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) f (Hf : bipermutation (n + m) f) : 
  bipermutation ((n - 2) + m) (biperm_compose_arb_cup_l n m k l f).
Proof.
  unfold biperm_compose_arb_cup_l.
  apply biperm_compose_cup_l_base_bipermutation.
  - lia.
  - auto_biperm.
Qed.

#[export] Hint Resolve biperm_compose_arb_cup_l_bipermutation : biperm_db.

Lemma compose_zx_arb_cap_n_stacked_cups_step2 k l n
  (Hk : k < n + n) (Hl : l < n + n) (Hkl : k <> l) : 
  n_stacked_cups n ⟷ zx_arb_cap k l (n + n) ∝
  (zx_of_biperm (n + n - 2) 0 
    (biperm_compose_arb_cup_l (n + n) 0 k l (n_m_cup_cap n 0)))⊤%ZX.
Proof.
  rewrite compose_zx_arb_cap_n_stacked_cups_step1 by auto.
  apply transpose_mor.
  apply ZX_prop_by_mat_prop.
  rewrite matrix_of_zx_of_biperm by auto_biperm.
  rewrite matrix_of_biperm_compose_arb_cup_l by auto_biperm.
  cbn [ZX_semantics].
  rewrite n_stacked_caps_biperm_semantics.
  reflexivity.
Qed.


(* Lemma biperm_compose_arb_cup_l_n_m_cup_cap_0_r_cases k l n
  (Hk : k < n + n) (Hl : l < n + n) (Hkl : k <> l) : 
  perm_eq (n + n - 2 + 0) 
    (biperm_compose_arb_cup_l (n + n) 0 k l (n_m_cup_cap n 0))
    (if k / 2 =? l / 2 then
      n_m_cup_cap (n - 1) 0
    else
      biperm_compose_perm_l (n - 1 + (n - 1)) 0
        (n_m_cup_cap (n - 1) 0)
        (swap_to_0_1_perm (2 * (min k l / 2))
          (2 * (max k l / 2) - 1) (n - 1 + (n - 1)))).
Proof.
  assert (Hn : 1 <= n) by lia.
  bdestruct (k / 2 =? l / 2).
  - admit.
  - unfold biperm_compose_arb_cup_l.
    replace (n + n - 2) with (n - 1 + (n - 1)) by (clear; lia).
    rewrite (biperm_compose_perm_l_defn (n-1+(n-1)) 0).
    rewrite <- perm_inv'_eq.

    rewrite perm_inv'_stack_perms by auto_perm.
    intros i Hi.
    
    unfold biperm_compose_perm_l. *)


Lemma compose_zx_arb_cap_n_stacked_cups k l n
  (Hk : k < n + n) (Hl : l < n + n) (Hkl : k <> l) : 
  n_stacked_cups n ⟷ zx_arb_cap k l (n + n) ∝
  if k / 2 =? l / 2 then 
    cast _ _ eq_refl double_sub_2_prf (n_stacked_cups (n - 1))
  else
    cast _ _ eq_refl comp_zx_cap_stacked_prf (n_stacked_cups (n - 2)) ⟷  
    zx_arb_cup (2 * (min k l / 2)) 
      (2 * (max k l / 2) - 1) _.
Proof.
  assert (Hor : k < l \/ l < k) by lia.
  by_symmetry Hor by 
    (intros **; rewrite Nat.eqb_sym, 
    zx_arb_cap_comm, zx_arb_cup_comm; auto).
  bdestruct (k / 2 =? l / 2).
  - assert (k / 2 < n) by dmlia.
    rewrite <- (n_stacked_cups_zx_of_perm_absorbtion n 
      (stack_perms (k / 2 + 1) (n - S (k / 2)) (big_swap_perm (k / 2) 1) idn))
      by auto_perm.
    unfold zx_arb_cap.
    rewrite compose_assoc, <- (compose_assoc (zx_of_perm _ _)).
    rewrite compose_zx_of_perm by auto_perm.
    rewrite zx_of_perm_eq_idn.
    + rewrite zx_of_perm_idn, nwire_removal_l.
      now rewrite n_stacked_cups_compose_zx_padded_cap.
    + replace (n + n) with (n * 2) by lia.
      rewrite tensor_perms_defn.
      intros a Ha.
      change ((?f ∘ ?g) ?x) with ((f ∘ idn) (g x)).
      rewrite swap_from_0_1_perm_defn by auto.
      pose proof (Nat.div_mod_eq k 2).
      pose proof (Nat.div_mod_eq l 2).
      pose proof (Nat.mod_upper_bound l 2 ltac:(lia)).
      rewrite Nat.min_l, Nat.max_r by lia.
      bdestruct_all; unfold compose.
      * rewrite stack_perms_left, big_swap_perm_right by lia.
        lia.
      * rewrite stack_perms_left, big_swap_perm_right by lia.
        lia.
      * rewrite mod_sub_n_r by lia.
        rewrite stack_perms_left, big_swap_perm_left by dmlia.
        rewrite div_sub_n_r by lia.
        rewrite Nat.sub_add by dmlia.
        pose proof (Nat.div_mod_eq a 2).
        lia.
      * rewrite stack_perms_right by dmlia.
        rewrite Nat.sub_add by dmlia.
        pose proof (Nat.div_mod_eq a 2).
        lia.
  - assert (k / 2 < n) by dmlia.
    assert (l / 2 < n) by dmlia.
    assert (k / 2 < l / 2) by 
      (enough (k / 2 <= l / 2) by lia;
      apply div0_div_le_mono; lia).
    rewrite <- (n_stacked_cups_zx_of_perm_absorbtion n 
      (swap_to_0_1_perm (k / 2) (l / 2) n))
      by auto_perm.
    rewrite compose_assoc.
    rewrite zx_arb_cap_compose_zx_of_perm_l by auto_perm.
    rewrite <- compose_assoc.
    rewrite compose_zx_arb_cap_n_stacked_cups_small.
    + unfold zx_arb_cup, zx_arb_cap.
      cbn [ZXCore.transpose].
      rewrite <- compose_assoc.
      match goal with 
      |- ?B ⟷ _ ∝ ?A ⟷ _ => 
        assert (Hrw : A ∝ B)
      end.
      1: {
        unfold zx_padded_cap.
        auto_cast_eqn erewrite le_lt_dec_le.
        rewrite cast_transpose.
        cbn [ZXCore.transpose].
        rewrite n_wire_transpose.
        rewrite cast_compose_r.
        rewrite <- push_out_top.
        rewrite cast_contract_eq.
        rewrite (n_stacked_cups_resize (ltac:(lia) : n - 1 = S (n - 2))).
        rewrite cast_contract_eq.
        rewrite n_stacked_cups_succ.
        rewrite cast_stack_r_fwd.
        rewrite 2!cast_contract_eq.
        apply cast_simplify; reflexivity.
      }
      rewrite Hrw.
      rewrite Nat.min_l, Nat.max_r by lia.
      assert (Hk2up : k / 2 < n - 1). 1: {
        rewrite (Nat.div_mod_eq l 2) in Hl.
        lia.
      }
      assert (Hkup : 2 * (k / 2) < 2 * (n - 1)) by lia.
      assert (Hlup : 2 * (l / 2) - 1 < 2 * (n - 1)) by lia.
      rewrite zx_of_perm_transpose by 
        auto with perm_db zarith.
      

      apply compose_simplify_r.
      ereflexivity.
      apply zx_of_perm_eq_of_perm_eq.
      rewrite swap_from_0_1_perm_inv' by lia.
      unfold contract_biperm.
      if_true_lia.
      replace (n + n - 2) with (n + n - 1 - 1) by lia.
      rewrite (swap_to_0_1_perm_defn (_ * _)).
      intros a Ha.
      rewrite Nat.min_l, Nat.max_r by lia.
      assert (Hval2k2 : contract_perm (tensor_perms n 2 (swap_to_0_1_perm 
        (k / 2) (l / 2) n) idn) l (2 * (k / 2)) = 0). 1: {
        unfold contract_perm.
        rewrite tensor_perms_defn by lia.
        rewrite div_mul_l, (Nat.mul_comm 2 (_/_)), Nat.Div0.mod_mul
          by easy.
        pose proof (Nat.div_mod_eq k 2) as Hkeq.
        if_true_lia.
        clear Hkeq.
        rewrite swap_to_0_1_perm_left_min by lia.
        bdestruct_one; reflexivity.
      }
      assert (Hval2k21 : contract_perm (tensor_perms n 2 (swap_to_0_1_perm 
        (k / 2) (l / 2) n) idn) l (2 * (k / 2) + 1) = 1). 1: {
        unfold contract_perm.
        pose proof (Nat.div_mod_eq l 2) as Hleq.
        if_true_lia.
        clear Hleq.
        rewrite 2!tensor_perms_defn by lia.
        rewrite (Nat.mul_comm 2 (k/2)), div_2_add_l_1.
        rewrite mod_add_l.
        rewrite swap_to_0_1_perm_left_min, 
          swap_to_0_1_perm_right_max by lia.
        reflexivity.
      }
      assert (Hvalk : contract_perm (tensor_perms n 2 (swap_to_0_1_perm 
        (k / 2) (l / 2) n) idn) l k = k mod 2). 1: {
        unfold contract_perm.
        if_true_lia.
        rewrite 2!tensor_perms_defn by lia.
        rewrite swap_to_0_1_perm_left_min, 
          swap_to_0_1_perm_right_max by lia.
        assert (k mod 2 < 2) by dmlia.
        if_true_lia.
        reflexivity.
      }
      assert (Hval2l21 : contract_perm (tensor_perms n 2 (swap_to_0_1_perm 
        (k / 2) (l / 2) n) idn) l (2 * (l / 2) - 1) = 
        (if l / 2 - 1 =? k / 2 then 1 else 2 * (l / 2))). 1: {
        unfold contract_perm.
        pose proof (Nat.div_mod_eq l 2) as Hleq.
        if_true_lia.
        clear Hleq.
        rewrite 2!tensor_perms_defn by lia.
        rewrite (Nat.mul_comm 2 (l/2)), mod_mul_sub_le, div_sub by lia.
        change (1 mod 2) with 1.
        change (Nat.b2n _) with 1.
        rewrite swap_to_0_1_perm_right_max by lia.
        rewrite Nat.sub_0_r.
        rewrite swap_to_0_1_perm_defn by lia.
        rewrite Nat.min_l, Nat.max_r by lia.
        replace_bool_lia (l / 2 - 1 =? l / 2) false.
        replace_bool_lia (l / 2 - 1 <? k / 2) false.
        replace_bool_lia (l / 2 - 1 <? l / 2) true.
        assert (l mod 2 < 2) by dmlia.
        rewrite Nat.sub_add by lia.
        replace_bool_lia ((if l / 2 - 1 =? k / 2 then 0 else l / 2) * 2 
          + (2 * 1 - 1) <? 1 * 2 + l mod 2) ((l / 2 - 1 =? k / 2)).
        bdestruct_one; [reflexivity|].
        apply Nat.add_sub.
      }
      assert (Hval2l2 : contract_perm (tensor_perms n 2 (swap_to_0_1_perm 
        (k / 2) (l / 2) n) idn) l (2 * (l / 2)) = 
        2). 1: {
        unfold contract_perm.
        pose proof (Nat.div_mod_eq l 2) as Hleq.
        rewrite 2!tensor_perms_defn by lia.
        rewrite (Nat.mul_comm 2 (l/2)), Nat.div_mul, Nat.Div0.mod_mul by lia.
        rewrite tensor_perms_defn, div_2_add_l_1, mod_add_l by lia.
        rewrite swap_to_0_1_perm_right_max by lia.
        pose proof (Nat.div_mod_eq l 2).
        bdestructΩ'.
      }
      (* assert (Hvall : contract_perm (tensor_perms n 2 (swap_to_0_1_perm 
        (k / 2) (l / 2) n) idn) l l = 
        2 - l mod 2). 1: {
        unfold contract_perm.
        if_false_lia.
        rewrite 2!tensor_perms_defn by lia.
        rewrite (Nat.mul_comm 2 (l/2)), Nat.div_mul, Nat.Div0.mod_mul by lia.
        rewrite tensor_perms_defn, div_2_add_l_1, mod_add_l by lia.
        rewrite swap_to_0_1_perm_right_max by lia.
        pose proof (Nat.div_mod_eq l 2).
        bdestructΩ'.
      } *)

      bdestruct (a =? 2 * (k / 2)). 1: {
        subst a.
        unfold contract_perm at 1.
        rewrite Hval2k2, Hvalk, Hval2k21.
        assert (k mod 2 < 2) by dmlia.
        bdestructΩ'.
      }
      bdestruct (a =? 2 * (l / 2) - 1). 1: {
        subst a.
        unfold contract_perm at 1.
        rewrite Nat.sub_add by lia.
        rewrite Hval2l21, Hvalk, Hval2l2.
        assert (k < 2 * (l / 2)). 1: {
          rewrite (Nat.div_mod_eq k 2).
          replace (l / 2) with (k / 2 + (l / 2 - k / 2)) by lia.
          rewrite Nat.mul_add_distr_l.
          enough (k mod 2 < 2) by lia.
          dmlia.
        }
        if_false_lia.
        assert (k mod 2 < 2) by dmlia.
        if_false_lia.
        reflexivity.
      }
      bdestruct (a <? 2 * (k / 2)); [|bdestruct (a <? 2 * (l / 2) - 1)].
      * unfold contract_perm at 1.
        pose proof (Nat.div_mod_eq k 2) as Heqk.
        if_true_lia.
        rewrite Hvalk.
        pattern (contract_perm (tensor_perms n 2 (swap_to_0_1_perm 
          (k/2) (l/2) n) idn) l a).
        match goal with |- ?Q _ => set (P := Q) end.
        unfold contract_perm.
        if_true_lia.
        clear Heqk.
        rewrite 2!tensor_perms_defn by lia.
        rewrite swap_to_0_1_perm_right_max by lia.
        assert (a / 2 < k / 2) by dmlia.
        rewrite swap_to_0_1_perm_neither by dmlia.
        rewrite Nat.min_l, Nat.max_r by lia.
        replace_bool_lia (a / 2 <? k / 2) true.
        assert (l mod 2 < 2) by dmlia.
        if_false_lia.
        unfold P.
        assert (k mod 2 < 2) by dmlia.
        if_false_lia.
        pose proof (Nat.div_mod_eq a 2).
        lia.
      * unfold contract_perm at 1.
        pose proof (Nat.div_mod_eq k 2).
        assert (k mod 2 < 2) by dmlia.
        if_false_lia.
        rewrite Hvalk.
        pattern (contract_perm (tensor_perms n 2 (swap_to_0_1_perm 
          (k/2) (l/2) n) idn) l (a+1)).
        match goal with |- ?Q _ => set (P := Q) end.
        unfold contract_perm.
        pose proof (Nat.div_mod_eq l 2).
        if_true_lia.
        rewrite 2!tensor_perms_defn by lia.
        rewrite swap_to_0_1_perm_right_max by lia.
        assert ((a + 1) / 2 < l / 2) by dmlia.
        assert (k / 2 < (a + 1) / 2). 1: {
          apply (Nat.lt_le_trans _ (k / 2 + 1)); [lia|].
          apply Nat.div_le_lower_bound; lia.
        }
        rewrite swap_to_0_1_perm_neither by lia.
        rewrite Nat.min_l, Nat.max_r by lia.
        replace_bool_lia ((a + 1)/2 <? k/2) false.
        replace_bool_lia ((a + 1)/2 <? l/2) true.
        assert (l mod 2 < 2) by dmlia.
        if_false_lia.
        unfold P.
        assert (k mod 2 < 2) by dmlia.
        if_false_lia.
        pose proof (Nat.div_mod_eq (a + 1) 2).
        lia.
      * unfold contract_perm at 1.
        pose proof (Nat.div_mod_eq k 2).
        assert (k mod 2 < 2) by dmlia.
        if_false_lia.
        rewrite Hvalk.
        pattern (contract_perm (tensor_perms n 2 (swap_to_0_1_perm 
          (k/2) (l/2) n) idn) l (a+1)).
        match goal with |- ?Q _ => set (P := Q) end.
        unfold contract_perm.
        pose proof (Nat.div_mod_eq l 2).
        assert (l mod 2 < 2) by dmlia.
        if_false_lia.
        rewrite 2!tensor_perms_defn by lia.
        rewrite swap_to_0_1_perm_right_max by lia.
        replace (a+1+1) with (a+2) by apply (Nat.add_assoc a 1 1).

        assert (k / 2 < (a + 2) / 2). 1: {
          apply (Nat.lt_le_trans _ (k / 2 + 1)); [lia|].
          apply Nat.div_le_lower_bound; lia.
        }
        assert (l / 2 < (a + 2) / 2). 1: {
          apply (Nat.lt_le_trans _ (l / 2 + 1)); [lia|].
          apply Nat.div_le_lower_bound; lia.
        }
        rewrite swap_to_0_1_perm_neither by dmlia.
        rewrite Nat.min_l, Nat.max_r by lia.
        replace_bool_lia ((a + 2)/2 <? k/2) false.
        replace_bool_lia ((a + 2)/2 <? l/2) false.
        if_false_lia.
        unfold P.
        if_false_lia.
        pose proof (Nat.div_mod_eq (a + 2) 2).
        lia.
    + rewrite tensor_perms_defn by lia.
      rewrite swap_to_0_1_perm_left_min by lia.
      assert (k mod 2 < 2) by dmlia.
      lia.
    + rewrite tensor_perms_defn by lia.
      rewrite swap_to_0_1_perm_right_max by lia.
      assert (l mod 2 < 2) by dmlia.
      lia.
    + rewrite 2!tensor_perms_defn by lia.
      rewrite swap_to_0_1_perm_left_min, swap_to_0_1_perm_right_max by lia.
      rewrite 2!Nat.div_add_l, 2!mod_div; lia.
    + lia.
  - rewrite H by auto.
    bdestruct_one; [reflexivity|].
    rewrite zx_arb_cup_comm.
    rewrite Nat.max_comm, Nat.min_comm.
    reflexivity.
Qed.


  





  


(* Definition compose_arb_cup_zx_of_edgeperm *)






(* UNFINISHED - Construct an edgefunc by taking a base edgefunc f with n 
   edges, adding ncap edges specified by g (thought of as 
   giving the inputs for the edges of each cap connecting
   two inputs), and giving all remaining nin edges using h
   (thought of as assigning an input to the spider to which 
   it connects). *)
(* Definition edgefunc_of_base_edge_caps_iofunc n 
  (f : nat -> nat * nat) ncap (g : nat -> nat * nat) 
  nin (h : nat -> nat) :=
  fun k => if k <? n then f k else 
    if k <? n + ncup then h (k - n) else
    let k' := Nsum_index (ncup * 2 + nin)
      (fun a => 1 - edgefunc_deg ncup h a) k in 
    (k', g (k' - n)) 
    if g (k - n) <? n then (k, g (k - n)) else
    if k - n <? g (k - n) then 

Definition edge_is_bounded m (ij : nat * nat) : bool :=
  (fst ij <? m) && (snd ij <? m).

Definition base_edge_func_of_edgefunc n f : (nat -> nat * nat) :=
  fun k => Nsum_index n  *)



























(* FIXME: Move to ZXperm and ZXpermSemantics *)
Fixpoint is_ZXperm {n m} (zx : ZX n m) : bool :=
  match zx with 
  | ⦰ => true
  | — => true
  | ⨉ => true
  | zx0 ↕ zx1 => is_ZXperm zx0 && is_ZXperm zx1
  | zx0 ⟷ zx1 => is_ZXperm zx0 && is_ZXperm zx1
  | _ => false
  end.

Lemma is_ZXperm_ZXperm {n m} (zx : ZX n m) : 
  is_ZXperm zx = true -> ZXperm zx.
Proof.
  induction zx.
  1-8: cbn; discriminate + constructor.
  1,2: cbn; rewrite andb_true_iff; intros []; auto_zxperm.
Qed.

Lemma ZXperm_is_ZXperm {n m} (zx : ZX n m) : 
  ZXperm zx -> is_ZXperm zx = true.
Proof.
  intros H.
  induction H; [reflexivity.. | |]; cbn; rewrite andb_true_iff; auto.
Qed.

Lemma ZXperm_iff_is_ZXperm {n m} (zx : ZX n m) : 
  ZXperm zx <-> is_ZXperm zx = true.
Proof.
  split.
  - apply ZXperm_is_ZXperm.
  - apply is_ZXperm_ZXperm.
Qed.

Inductive ZXperm_t : forall {n m}, ZX n m -> Set :=
	| PermEmpty_t : ZXperm_t ⦰
  | PermWire_t : ZXperm_t —
  | PermSwap_t : ZXperm_t ⨉
  | PermStack_t {n0 m0 n1 m1} (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) :
    ZXperm_t zx0 -> ZXperm_t zx1 -> ZXperm_t (zx0 ↕ zx1)
  | PermComp_t {n m o} (zx0 : ZX n m) (zx1 : ZX m o) :
    ZXperm_t zx0 -> ZXperm_t zx1 -> ZXperm_t (zx0 ⟷ zx1).

Lemma is_ZXperm_ZXperm_t {n m} (zx : ZX n m) : 
  is_ZXperm zx = true -> ZXperm_t zx.
Proof.
  induction zx.
  1-8: cbn; discriminate + constructor.
  1,2: cbn; intros Heq; apply andb_true_iff in Heq; 
    destruct Heq; constructor; auto.
Qed.

Lemma ZXperm_t_is_ZXperm {n m} (zx : ZX n m) : 
  ZXperm_t zx -> is_ZXperm zx = true.
Proof.
  intros H.
  induction H; [reflexivity.. | |]; cbn; rewrite andb_true_iff; auto.
Qed.

Definition ZXperm_t_of_ZXperm {n m} (zx : ZX n m) 
  (Hzx : ZXperm zx) : ZXperm_t zx :=
  is_ZXperm_ZXperm_t zx (ZXperm_is_ZXperm zx Hzx).

Lemma ZXperm_of_ZXperm_t {n m} (zx : ZX n m) : ZXperm_t zx -> ZXperm zx.
Proof.
  intros Hzx.
  now apply is_ZXperm_ZXperm, ZXperm_t_is_ZXperm.
Qed.

Lemma ZXperm_compose_inv {n m o} {zx0 : ZX n m} {zx1 : ZX m o} 
  (H : ZXperm (zx0 ⟷ zx1)) : ZXperm zx0 /\ ZXperm zx1.
Proof.
  rewrite !ZXperm_iff_is_ZXperm in *; now apply andb_true_iff.
Qed.

Lemma ZXperm_stack_inv {n0 m0 n1 m1} {zx0 : ZX n0 m0} {zx1 : ZX n1 m1} 
  (H : ZXperm (zx0 ↕ zx1)) : ZXperm zx0 /\ ZXperm zx1.
Proof.
  rewrite !ZXperm_iff_is_ZXperm in *; now apply andb_true_iff.
Qed.

Open Scope nat_scope.
Definition ZXperm_rect (P : forall n m, ZX n m -> Type)
  (Pemp : P 0 0 ⦰) (Pwire : P 1 1 —) (Pswap : P 2 2 ⨉)
  (Pstack : forall {n0 m0 n1 m1} (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  ZXperm zx0 -> P n0 m0 zx0 -> ZXperm zx1 -> P n1 m1 zx1 -> 
  P (n0 + n1) (m0 + m1) (zx0 ↕ zx1)) 
  (Pcomp : forall {n m o} (zx0 : ZX n m) (zx1 : ZX m o),
   ZXperm zx0 -> P n m zx0 -> ZXperm zx1 -> P m o zx1 -> P n o (zx0 ⟷ zx1)) : 
  forall {n m : nat} (zx : ZX n m) (Hzx : ZXperm zx), P n m zx :=
  fix rect {n m} (zx : ZX n m) {struct zx} : ZXperm zx -> P n m zx :=
  match zx as z in ZX n' m' return ZXperm z -> P n' m' z with 
  | ⦰ => fun _ => Pemp
  | — => fun _ => Pwire
  | ⨉ => fun _ => Pswap
  | zx0 ↕ zx1 => fun Hzx =>
    Pstack zx0 zx1
      (proj1 (ZXperm_stack_inv Hzx))
        (rect zx0 (proj1 (ZXperm_stack_inv Hzx)))
      (proj2 (ZXperm_stack_inv Hzx)) 
        (rect zx1 (proj2 (ZXperm_stack_inv Hzx)))  
  | zx0 ⟷ zx1 => fun Hzx =>
    Pcomp zx0 zx1
      (proj1 (ZXperm_compose_inv Hzx)) 
        (rect zx0 (proj1 (ZXperm_compose_inv Hzx)))
      (proj2 (ZXperm_compose_inv Hzx)) 
        (rect zx1 (proj2 (ZXperm_compose_inv Hzx)))
  | z => fun Hzx => 
    False_rect _ (diff_false_true (ZXperm_is_ZXperm z Hzx))
  end.



Require Import ZXbiperm.

(* FIXME: Move to ZXbiperm *)
Fixpoint is_ZXbiperm {n m} (zx : ZX n m) : bool :=
  match zx with 
  | ⦰ => true
  | — => true
  | ⨉ => true
  | ⊃ => true
  | ⊂ => true
  | zx0 ↕ zx1 => is_ZXbiperm zx0 && is_ZXbiperm zx1
  | zx0 ⟷ zx1 => is_ZXbiperm zx0 && is_ZXbiperm zx1
  | _ => false
  end.

Lemma is_ZXbiperm_ZXbiperm {n m} (zx : ZX n m) : 
  is_ZXbiperm zx = true -> ZXbiperm zx.
Proof.
  induction zx.
  1-8: cbn; discriminate + constructor.
  1,2: cbn; rewrite andb_true_iff; intros []; auto with zxbiperm_db.
Qed.

Lemma ZXbiperm_is_ZXbiperm {n m} (zx : ZX n m) : 
  ZXbiperm zx -> is_ZXbiperm zx = true.
Proof.
  intros H.
  induction H; [reflexivity.. | |]; cbn; rewrite andb_true_iff; auto.
Qed.

Lemma ZXbiperm_iff_is_ZXbiperm {n m} (zx : ZX n m) : 
  ZXbiperm zx <-> is_ZXbiperm zx = true.
Proof.
  split.
  - apply ZXbiperm_is_ZXbiperm.
  - apply is_ZXbiperm_ZXbiperm.
Qed.

Inductive ZXbiperm_t : forall {n m}, ZX n m -> Set :=
	| BipermEmpty_t : ZXbiperm_t ⦰
  | BipermWire_t : ZXbiperm_t —
  | BipermSwap_t : ZXbiperm_t ⨉
  | BipermCap_t : ZXbiperm_t ⊃
  | BipermCup_t : ZXbiperm_t ⊂
  | BipermStack_t {n0 m0 n1 m1} (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) :
    ZXbiperm_t zx0 -> ZXbiperm_t zx1 -> ZXbiperm_t (zx0 ↕ zx1)
  | BipermComp_t {n m o} (zx0 : ZX n m) (zx1 : ZX m o) :
    ZXbiperm_t zx0 -> ZXbiperm_t zx1 -> ZXbiperm_t (zx0 ⟷ zx1).

Lemma is_ZXbiperm_ZXbiperm_t {n m} (zx : ZX n m) : 
  is_ZXbiperm zx = true -> ZXbiperm_t zx.
Proof.
  induction zx.
  1-8: cbn; discriminate + constructor.
  1,2: cbn; intros Heq; apply andb_true_iff in Heq; 
    destruct Heq; constructor; auto.
Defined.
Opaque is_ZXbiperm_ZXbiperm_t.

Lemma ZXbiperm_t_is_ZXbiperm {n m} (zx : ZX n m) : 
  ZXbiperm_t zx -> is_ZXbiperm zx = true.
Proof.
  intros H.
  induction H; [reflexivity.. | |]; cbn; rewrite andb_true_iff; auto.
Defined.
Opaque ZXbiperm_t_is_ZXbiperm.

Definition ZXbiperm_t_of_ZXbiperm {n m} (zx : ZX n m) 
  (Hzx : ZXbiperm zx) : ZXbiperm_t zx :=
  is_ZXbiperm_ZXbiperm_t zx (ZXbiperm_is_ZXbiperm zx Hzx).

Lemma ZXbiperm_of_ZXbiperm_t {n m} (zx : ZX n m) : ZXbiperm_t zx -> ZXbiperm zx.
Proof.
  intros Hzx.
  now apply is_ZXbiperm_ZXbiperm, ZXbiperm_t_is_ZXbiperm.
Qed.

Lemma ZXbiperm_stack_inv {n0 m0 n1 m1} {zx0 : ZX n0 m0} {zx1 : ZX n1 m1}
  (Hzx01 : ZXbiperm (zx0 ↕ zx1)) : ZXbiperm zx0 /\ ZXbiperm zx1.
Proof.
  rewrite !ZXbiperm_iff_is_ZXbiperm in *.
  now apply andb_true_iff.
Qed.

Lemma ZXbiperm_compose_inv {n m o} {zx0 : ZX n m} {zx1 : ZX m o}
  (Hzx01 : ZXbiperm (zx0 ⟷ zx1)) : ZXbiperm zx0 /\ ZXbiperm zx1.
Proof.
  rewrite !ZXbiperm_iff_is_ZXbiperm in *.
  now apply andb_true_iff.
Qed.

Open Scope nat_scope.
Definition ZXbiperm_rect (P : forall n m, ZX n m -> Type)
  (Pemp : P 0 0 ⦰) (Pwire : P 1 1 —) (Pswap : P 2 2 ⨉)
  (Pcap : P 2 0 ⊃) (Pcup : P 0 2 ⊂)
  (Pstack : forall {n0 m0 n1 m1} (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  ZXbiperm zx0 -> P n0 m0 zx0 -> ZXbiperm zx1 -> P n1 m1 zx1 -> 
  P (n0 + n1) (m0 + m1) (zx0 ↕ zx1)) 
  (Pcomp : forall {n m o} (zx0 : ZX n m) (zx1 : ZX m o),
   ZXbiperm zx0 -> P n m zx0 -> ZXbiperm zx1 -> P m o zx1 -> P n o (zx0 ⟷ zx1)) : 
  forall {n m : nat} (zx : ZX n m) (Hzx : ZXbiperm zx), P n m zx :=
  fix rect {n m} (zx : ZX n m) {struct zx} : ZXbiperm zx -> P n m zx :=
  match zx as z in ZX n' m' return ZXbiperm z -> P n' m' z with 
  | ⦰ => fun _ => Pemp
  | — => fun _ => Pwire
  | ⨉ => fun _ => Pswap
  | ⊃ => fun _ => Pcap
  | ⊂ => fun _ => Pcup
  | zx0 ↕ zx1 => fun Hzx =>
    Pstack zx0 zx1
      (proj1 (ZXbiperm_stack_inv Hzx))
        (rect zx0 (proj1 (ZXbiperm_stack_inv Hzx)))
      (proj2 (ZXbiperm_stack_inv Hzx)) 
        (rect zx1 (proj2 (ZXbiperm_stack_inv Hzx)))  
  | zx0 ⟷ zx1 => fun Hzx =>
    Pcomp zx0 zx1
      (proj1 (ZXbiperm_compose_inv Hzx)) 
        (rect zx0 (proj1 (ZXbiperm_compose_inv Hzx)))
      (proj2 (ZXbiperm_compose_inv Hzx)) 
        (rect zx1 (proj2 (ZXbiperm_compose_inv Hzx)))
  | z => fun Hzx => 
    False_rect _ (diff_false_true (ZXbiperm_is_ZXbiperm z Hzx))
  end.



Record ZXdecomp {n m : nat} : Set := {
  mid_size : nat;
  spiders : ZX 0 mid_size;
  iobiperm : ZX (mid_size + n) m;
}.

Arguments ZXdecomp (_ _)%nat_scope : clear implicits.

Definition ZX_of_decomp {n m} (zxd : ZXdecomp n m) : ZX n m :=
  zxd.(spiders) ↕ n_wire n ⟷ zxd.(iobiperm).

Arguments ZX_of_decomp _ /.

Coercion ZX_of_decomp : ZXdecomp >-> ZX.

Definition ZXdecomp_compose {n m o} 
  (zxd0 : ZXdecomp n m) (zxd1 : ZXdecomp m o) : ZXdecomp n o := {|
  mid_size := zxd1.(mid_size) + zxd0.(mid_size);
  spiders := zxd1.(spiders) ↕ zxd0.(spiders);
  iobiperm := 
    cast _ _ (eq_sym (Nat.add_assoc _ _ _)) eq_refl
    (n_wire zxd1.(mid_size) ↕ zxd0.(iobiperm) ⟷ zxd1.(iobiperm))
|}.

Definition ZXdecomp_compose_comp {n m o} 
  (zxd0 : ZXdecomp n m) (zxd1 : ZXdecomp m o) : ZXdecomp n o := {|
  mid_size := zxd1.(mid_size) + zxd0.(mid_size);
  spiders := zxd1.(spiders) ↕ zxd0.(spiders);
  iobiperm := 
    cast _ _ add_assoc_comp' eq_refl
    (n_wire zxd1.(mid_size) ↕ zxd0.(iobiperm) ⟷ zxd1.(iobiperm))
|}.

Lemma ZXdecomp_compose_comp_eq {n m o} 
  (zxd0 : ZXdecomp n m) (zxd1 : ZXdecomp m o) : 
  ZXdecomp_compose_comp zxd0 zxd1 = ZXdecomp_compose zxd0 zxd1.
Proof.
  unfold ZXdecomp_compose_comp, ZXdecomp_compose.
  f_equal.
  now apply cast_simplify_eq.
Qed.


Import ComposeRules.

Lemma ZXdecomp_compose_correct {n m o} 
  (zxd0 : ZXdecomp n m) (zxd1 : ZXdecomp m o) : 
  ZXdecomp_compose zxd0 zxd1 ∝ zxd0 ⟷ zxd1.
Proof.
  destruct zxd0 as [k spi0 io0].
  destruct zxd1 as [l spi1 io1].
  cbn.
  clean_eqns rewrite (@stack_assoc 0 0).
  rewrite cast_compose_eq_mid_join.
  cbn.
  rewrite <- compose_assoc.
  rewrite <- (stack_compose_distr spi1 _ (spi0 ↕ n_wire n)).
  rewrite stack_split_antidiag, stack_empty_l, nwire_removal_r.
  apply compose_assoc.
Qed.

Program Definition ZXdecomp_stack {n0 m0 n1 m1} 
  (zxd0 : ZXdecomp n0 m0) (zxd1 : ZXdecomp n1 m1) : 
  ZXdecomp (n0 + n1) (m0 + m1) := {|
  mid_size := zxd0.(mid_size) + zxd1.(mid_size);
  spiders := zxd0.(spiders) ↕ zxd1.(spiders);
  iobiperm := cast _ _ _ _
  (n_wire zxd0.(mid_size) ↕ zx_comm zxd1.(mid_size) n0 ↕ n_wire n1) 
    ⟷ (zxd0.(iobiperm) ↕ zxd1.(iobiperm)) 
    (* cast _ _ (eq_sym (Nat.add_assoc _ _ _)) eq_refl
    (n_wire zxd1.(mid_size) ↕ zxd0.(iobiperm) ⟷ zxd1.(iobiperm)) *)
|}.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.





Definition ZXdecomp_stack_comp {n0 m0 n1 m1} 
  (zxd0 : ZXdecomp n0 m0) (zxd1 : ZXdecomp n1 m1) : 
  ZXdecomp (n0 + n1) (m0 + m1) := {|
  mid_size := zxd0.(mid_size) + zxd1.(mid_size);
  spiders := zxd0.(spiders) ↕ zxd1.(spiders);
  iobiperm := cast _ _ 
  (eq_trans add_assoc_comp (f_equal (fun k => k + n1)%nat add_assoc_comp'))
  (eq_trans add_assoc_comp (f_equal (fun k => k + n1)%nat add_assoc_comp'))
  (n_wire zxd0.(mid_size) ↕ zx_comm_comp zxd1.(mid_size) n0 ↕ n_wire n1) 
    ⟷ (zxd0.(iobiperm) ↕ zxd1.(iobiperm)) 
|}. 

Lemma ZXdecomp_stack_comp_eq {n0 m0 n1 m1} 
  (zxd0 : ZXdecomp n0 m0) (zxd1 : ZXdecomp n1 m1) : 
  ZXdecomp_stack_comp zxd0 zxd1 = ZXdecomp_stack zxd0 zxd1.
Proof.
  unfold ZXdecomp_stack_comp, ZXdecomp_stack.
  f_equal.
  f_equal.
  rewrite zx_comm_comp_eq.
  now apply cast_simplify_eq.
Qed.




Lemma ZXdecomp_stack_correct {n0 m0 n1 m1} 
  (zxd0 : ZXdecomp n0 m0) (zxd1 : ZXdecomp n1 m1) : 
  ZXdecomp_stack zxd0 zxd1 ∝ zxd0 ↕ zxd1.
Proof.
  destruct zxd0 as [k spi0 io0].
  destruct zxd1 as [l spi1 io1].
  cbn.
  rewrite stack_compose_distr.
  rewrite <- compose_assoc.
  apply compose_simplify; [|reflexivity].
  rewrite <- n_wire_stack.
  clean_eqns rewrite (stack_assoc spi0 spi1), 
    (stack_assoc_back spi1), cast_stack_r, cast_contract_eq,
    (stack_assoc_back spi0), cast_contract_eq.
  rewrite cast_compose_eq_mid_join.
  rewrite <- 2!stack_compose_distr, zx_comm_commutes_r.
  rewrite zx_comm_0_l, cast_compose_l, nwire_removal_l, cast_contract_eq.
  rewrite nwire_removal_r.
  clean_eqns rewrite cast_stack_r, nwire_removal_r.
  clean_eqns rewrite stack_assoc_back.
  clean_eqns rewrite cast_contract_eq, cast_stack_l.
  clean_eqns rewrite stack_assoc.
  now rewrite 2!cast_contract_eq, cast_id.
Qed.



Definition ZXdecomp_Z n m α : ZXdecomp n m := {|
  mid_size := m + n;
  spiders := Z 0 (m + n) α;
  iobiperm := cast _ _ (eq_sym (Nat.add_assoc _ _ _)) (eq_sym (Nat.add_0_r _))
    (n_wire m ↕ n_cup n)
|}.

Definition ZXdecomp_X n m α : ZXdecomp n m := {|
  mid_size := m + n;
  spiders := X 0 (m + n) α;
  iobiperm := cast _ _ (eq_sym (Nat.add_assoc _ _ _)) (eq_sym (Nat.add_0_r _))
    (n_wire m ↕ n_cup n)
|}.

Fixpoint n_cup_unswapped_comp n : ZX (n + n) 0 :=
  match n as n0 return (ZX (n0 + n0) 0) with
  | 0%nat => ⦰
  | S n0 => 
  cast (S n0 + S n0) (1 + 0 + 1) 
    (eq_trans add_succ_r_comp (@add_comm_comp' (1 + n0 + n0) 1)) eq_refl
    (— ↕ n_cup_unswapped_comp n0 ↕ —) ⟷ ⊃
  end.

Definition n_cup_comp n : ZX (n + n) 0 := 
  n_swap n ↕ n_wire n ⟷ n_cup_unswapped_comp n.

Lemma n_cup_unswapped_comp_eq n : 
  n_cup_unswapped_comp n = n_cup_unswapped n.
Proof.
  induction n; [reflexivity|].
  cbn.
  f_equal.
  apply cast_simplify_eq.
  now rewrite IHn.
Qed.

Lemma n_cup_comp_eq n : n_cup_comp n = n_cup n.
Proof.
  unfold n_cup_comp.
  now rewrite n_cup_unswapped_comp_eq.
Qed.

Definition ZXdecomp_Z_comp n m α : ZXdecomp n m := {|
  mid_size := m + n;
  spiders := Z 0 (m + n) α;
  iobiperm := cast _ _ add_assoc_comp' add_0_r_comp'
    (n_wire m ↕ n_cup_comp n)
|}.

Definition ZXdecomp_X_comp n m α : ZXdecomp n m := {|
  mid_size := m + n;
  spiders := X 0 (m + n) α;
  iobiperm := cast _ _ add_assoc_comp' add_0_r_comp'
    (n_wire m ↕ n_cup_comp n)
|}.

Lemma ZXdecomp_Z_comp_eq n m α : 
  ZXdecomp_Z_comp n m α = ZXdecomp_Z n m α.
Proof.
  unfold ZXdecomp_Z_comp, ZXdecomp_Z.
  rewrite n_cup_comp_eq.
  f_equal.
  now apply cast_simplify_eq.
Qed.

Lemma ZXdecomp_X_comp_eq n m α : 
  ZXdecomp_X_comp n m α = ZXdecomp_X n m α.
Proof.
  unfold ZXdecomp_X_comp, ZXdecomp_X.
  rewrite n_cup_comp_eq.
  f_equal.
  now apply cast_simplify_eq.
Qed.
  


Lemma ZXdecomp_Z_correct n m α : 
  ZXdecomp_Z n m α ∝ Z n m α.
Proof.
  cbn.
  rewrite Z_n_wrap_over_l_base.
  rewrite stack_nwire_distribute_r.
  apply n_cap_n_cup_pullthrough.
Qed.

Lemma ZXdecomp_X_correct n m α : 
  ZXdecomp_X n m α ∝ X n m α.
Proof.
  cbn.
  rewrite X_n_wrap_over_l_base.
  rewrite stack_nwire_distribute_r.
  apply n_cap_n_cup_pullthrough.
Qed.


Definition ZXdecomp_box : ZXdecomp 1 1 := {|
  mid_size := 6;
  spiders := Z 0 2 (PI / 2) ↕ X 0 2 (PI / 2) ↕ Z 0 2 (PI / 2);
  iobiperm := — ↕ ⊃ ↕ ⊃ ↕ ⊃;
|}.

(* Import ZXbiperm.  *)
Lemma ZXdecomp_box_correct : 
  ZXdecomp_box ∝ □. 
Proof.
  rewrite box_decomp_ZXZ.
  rewrite compose_assoc.
  rewrite <- ZXdecomp_Z_correct, <- ZXdecomp_X_correct.
  rewrite <- 2!ZXdecomp_compose_correct.
  cbn -[n_stack1].
  apply compose_simplify; [reflexivity|].
  rewrite !cast_id.
  rewrite <- (n_wire_stack 1 3), <- (n_wire_stack 1 1).
  clean_eqns rewrite 2!(stack_assoc (n_wire 1)).
  clean_eqns rewrite (stack_assoc —), cast_id, (stack_assoc —).
  rewrite !cast_id.
  rewrite <- (stack_compose_distr (n_wire 1) (n_wire 1)).
  rewrite nwire_removal_l.
  rewrite <- (stack_compose_distr (n_wire 1) (n_wire 1)).
  apply stack_simplify; [rewrite nwire_removal_l; apply wire_to_n_wire|].
  rewrite (ltac:((clean_eqns rewrite stack_empty_r, cast_id); reflexivity) 
    : n_cup 1 ∝ n_cup 1 ↕ ⦰).
  clean_eqns rewrite 2!(stack_assoc_back _ (n_wire 1)), 2!cast_id.
  rewrite 2!n_wire_stack.
  rewrite <- (stack_compose_distr (n_wire (1 + 1)) (n_cup 1) (n_cup 1 ↕ ⦰) ⦰).
  rewrite compose_empty_r, nwire_removal_l.
  clean_eqns rewrite (stack_assoc_back (n_cup 1) (n_cup 1) ⦰), cast_id.
  rewrite <- (stack_compose_distr (n_wire (3 + 1)) (n_cup 1 ↕ n_cup 1) 
    (n_cup 1 ↕ ⦰) ⦰).
  clean_eqns rewrite nwire_removal_l, compose_empty_r, stack_empty_r, cast_id.
  now rewrite n_cup_1_cup.
Qed.


Definition ZXdecomp_biperm {n m} (zx : ZX n m) : ZXdecomp n m :=
  {| mid_size := 0; spiders := ⦰; iobiperm := zx; |}.

Lemma ZX_decomp_biperm_correct {n m} (zx : ZX n m) : 
  ZXdecomp_biperm zx ∝ zx.
Proof.
  cbn.
  now rewrite stack_empty_l, nwire_removal_l.
Qed.


Fixpoint ZXdecomp_of_ZX {n m} (zx : ZX n m) : ZXdecomp n m :=
  match zx with 
  | Z n m α => ZXdecomp_Z n m α
  | X n m α => ZXdecomp_X n m α
  | □ => ZXdecomp_box
  | ⦰ => ZXdecomp_biperm ⦰
  | — => ZXdecomp_biperm —
  | ⨉ => ZXdecomp_biperm ⨉
  | ⊂ => ZXdecomp_biperm ⊂
  | ⊃ => ZXdecomp_biperm ⊃
  | zx0 ↕ zx1 => ZXdecomp_stack (ZXdecomp_of_ZX zx0) 
    (ZXdecomp_of_ZX zx1)
  | zx0 ⟷ zx1 => ZXdecomp_compose (ZXdecomp_of_ZX zx0) 
    (ZXdecomp_of_ZX zx1)
  end.

(* NB : Future optimization *)
Fixpoint ZXdecomp_of_ZX_alt {n m} (zx : ZX n m) : ZXdecomp n m :=
  if is_ZXbiperm zx then ZXdecomp_biperm zx else
  match zx with 
  | Z n m α => ZXdecomp_Z n m α
  | X n m α => ZXdecomp_X n m α
  | □ => ZXdecomp_box
  | zx0 ↕ zx1 => ZXdecomp_stack (ZXdecomp_of_ZX_alt zx0) 
    (ZXdecomp_of_ZX_alt zx1)
  | zx0 ⟷ zx1 => ZXdecomp_compose (ZXdecomp_of_ZX_alt zx0) 
    (ZXdecomp_of_ZX_alt zx1)
  | zx => ZXdecomp_biperm zx
  end.

Fixpoint ZXdecomp_of_ZX_alt_comp {n m} (zx : ZX n m) : ZXdecomp n m :=
  if is_ZXbiperm zx then ZXdecomp_biperm zx else
  match zx with 
  | Z n m α => ZXdecomp_Z_comp n m α
  | X n m α => ZXdecomp_X_comp n m α
  | □ => ZXdecomp_box
  | zx0 ↕ zx1 => ZXdecomp_stack_comp (ZXdecomp_of_ZX_alt_comp zx0) 
    (ZXdecomp_of_ZX_alt_comp zx1)
  | zx0 ⟷ zx1 => ZXdecomp_compose_comp (ZXdecomp_of_ZX_alt_comp zx0) 
    (ZXdecomp_of_ZX_alt_comp zx1)
  | zx => ZXdecomp_biperm zx
  end.

Lemma ZXdecomp_of_ZX_alt_comp_eq {n m} (zx : ZX n m) : 
  ZXdecomp_of_ZX_alt_comp zx = ZXdecomp_of_ZX_alt zx.
Proof.
  induction zx; 
  [reflexivity.. | | | |].
  - apply ZXdecomp_X_comp_eq.
  - apply ZXdecomp_Z_comp_eq.
  - cbn -[is_ZXbiperm].
    apply f_equal_if_precedent_same; [reflexivity|].
    intros _.
    rewrite IHzx1, IHzx2.
    apply ZXdecomp_stack_comp_eq.
  - cbn -[is_ZXbiperm].
    apply f_equal_if_precedent_same; [reflexivity|].
    intros _.
    rewrite IHzx1, IHzx2.
    apply ZXdecomp_compose_comp_eq.
Qed.

Lemma ZXdecomp_of_ZX_correct {n m} (zx : ZX n m) : 
  ZXdecomp_of_ZX zx ∝ zx.
Proof.
  induction zx; [apply ZX_decomp_biperm_correct.. | | | | |].
  - apply ZXdecomp_box_correct.
  - apply ZXdecomp_X_correct.
  - apply ZXdecomp_Z_correct.
  - cbn -[ZX_of_decomp]. 
    rewrite ZXdecomp_stack_correct.
    now apply stack_simplify.
  - cbn -[ZX_of_decomp]. 
    rewrite ZXdecomp_compose_correct.
    now apply compose_simplify.
Qed.

Lemma ZXdecomp_of_ZX_alt_correct {n m} (zx : ZX n m) : 
  ZXdecomp_of_ZX_alt zx ∝ zx.
Proof.
  induction zx;
  [apply ZX_decomp_biperm_correct.. | | | | |].
  - apply ZXdecomp_box_correct.
  - apply ZXdecomp_X_correct.
  - apply ZXdecomp_Z_correct.
  - cbn [ZXdecomp_of_ZX_alt].
    destruct (is_ZXbiperm (zx1 ↕ zx2)) eqn:e;
    [apply ZX_decomp_biperm_correct|].
    rewrite ZXdecomp_stack_correct. 
    now apply stack_simplify.
  - cbn [ZXdecomp_of_ZX_alt].
    destruct (is_ZXbiperm (zx1 ⟷ zx2)) eqn:e;
    [apply ZX_decomp_biperm_correct|].
    rewrite ZXdecomp_compose_correct. 
    now apply compose_simplify.
Qed.



Inductive ZXstack : forall {n m}, ZX n m -> Prop :=
  | ZXstack_empty : ZXstack ⦰
  | ZXstack_Z n m α : ZXstack (Z n m α)
  | ZXstack_X n m α : ZXstack (X n m α)
  | ZXstack_stack {n0 m0 n1 m1} (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) : 
    ZXstack zx0 -> ZXstack zx1 -> ZXstack (zx0 ↕ zx1).

Scheme ZXstack_ind_dep := Induction for ZXstack Sort Prop.

Lemma ZXstack_cast {n m n' m'} (zx : ZX n m) prfn prfm : 
  ZXstack zx -> ZXstack (cast n' m' prfn prfm zx).
Proof. now subst. Qed.

Fixpoint is_ZXstack {n m} (zx : ZX n m) := 
  match zx with 
  | ⦰ => true
  | Z _ _ _ => true
  | X _ _ _ => true
  | zx0 ↕ zx1 => is_ZXstack zx0 && is_ZXstack zx1
  | _ => false
  end.

Lemma ZXstack_iff_is_ZXstack {n m} (zx : ZX n m) : 
  ZXstack zx <-> is_ZXstack zx = true.
Proof.
  split.
  - intros H; induction H; [reflexivity..|cbn; now apply andb_true_iff].
  - intros H. 
    induction zx; cbn in H; try discriminate; constructor; 
    apply andb_true_iff in H; destruct H; auto.
Qed.

Lemma ZXstack_stack_inv {n0 m0 n1 m1} {zx0 : ZX n0 m0} {zx1 : ZX n1 m1} 
  (H : ZXstack (zx0 ↕ zx1)) : ZXstack zx0 /\ ZXstack zx1.
Proof.
  rewrite !ZXstack_iff_is_ZXstack in *; now apply andb_true_iff.
Qed.

Open Scope nat_scope.
Definition ZXstack_rect (P : forall n m, ZX n m -> Type)
  (Pemp : P 0 0 ⦰) (PX : forall n m α, P n m (X n m α))
  (PZ : forall n m α, P n m (Z n m α))
  (Pstack : forall {n0 m0 n1 m1} (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
    ZXstack zx0 -> ZXstack zx1 -> P n0 m0 zx0 -> P n1 m1 zx1 -> 
    P (n0 + n1) (m0 + m1) (zx0 ↕ zx1)) :
  forall {n m : nat} (zx : ZX n m) (Hzx : ZXstack zx), P n m zx :=
  fix rect {n m} (zx : ZX n m) {struct zx} : ZXstack zx -> P n m zx :=
  match zx as z in ZX n' m' return ZXstack z -> P n' m' z with 
  | ⦰ => fun _ => Pemp
  | Z n m α => fun _ => PZ n m α
  | X n m α => fun _ => PX n m α
  | zx0 ↕ zx1 => fun Hzx =>
    Pstack zx0 zx1
      (proj1 (ZXstack_stack_inv Hzx))
      (proj2 (ZXstack_stack_inv Hzx)) 
        (rect zx0 (proj1 (ZXstack_stack_inv Hzx)))
        (rect zx1 (proj2 (ZXstack_stack_inv Hzx)))  
  | z => fun Hzx => 
    False_rect _ (diff_false_true (proj1 (ZXstack_iff_is_ZXstack z) Hzx))
  end.

Fixpoint ZXstack_size {n m} (zx : ZX n m) : nat :=
  match zx with
  | ⦰ => 0
  | Z _ _ _ => 1
  | X _ _ _ => 1
  | zx0 ↕ zx1 => ZXstack_size zx0 + ZXstack_size zx1
  | _ => 0
  end.

Fixpoint ZXstack_in_dims {n m} (zx : ZX n m) : nat -> nat :=
  match zx with
  | ⦰ => fun _ => 0
  | Z n _ _ => fun _ => n
  | X n _ _ => fun _ => n
  | zx0 ↕ zx1 => 
    fun k => if k <? ZXstack_size zx0 then ZXstack_in_dims zx0 k
      else ZXstack_in_dims zx1 (k - ZXstack_size zx0)
  | _ => fun _ => 0
  end.

Fixpoint ZXstack_out_dims {n m} (zx : ZX n m) : nat -> nat :=
  match zx with
  | ⦰ => fun _ => 0
  | Z _ m _ => fun _ => m
  | X _ m _ => fun _ => m
  | zx0 ↕ zx1 => 
    fun k => if k <? (ZXstack_size zx0) then ZXstack_out_dims zx0 k
      else ZXstack_out_dims zx1 (k - ZXstack_size zx0)
  | _ => fun _ => 0
  end.

Fixpoint ZXstack_phases {n m} (zx : ZX n m) : nat -> R :=
  match zx with
  | ⦰ => fun _ => 0%R
  | Z _ _ α => fun _ => α
  | X _ _ α => fun _ => α
  | zx0 ↕ zx1 => 
    fun k => if k <? ZXstack_size zx0 then ZXstack_phases zx0 k
      else ZXstack_phases zx1 (k - ZXstack_size zx0)
  | _ => fun _ => 0%R
  end.


Fixpoint ZXstack_colors {n m} (zx : ZX n m) : nat -> bool :=
  match zx with
  | ⦰ => fun _ => false
  | Z _ _ _ => fun _ => false
  | X _ _ _ => fun _ => true
  | zx0 ↕ zx1 => 
    fun k => if k <? ZXstack_size zx0 then ZXstack_colors zx0 k
      else ZXstack_colors zx1 (k - ZXstack_size zx0)
  | _ => fun _ => false
  end.

Lemma ZXstack_in_dims_spec {n m} (zx : ZX n m) (Hzx : ZXstack zx) :
  n = big_sum (ZXstack_in_dims zx) (ZXstack_size zx).
Proof.
  induction Hzx; [reflexivity..|].
  cbn.
  rewrite Nsum_if_lt.
  now f_equal.
Qed.

Lemma ZXstack_out_dims_spec {n m} (zx : ZX n m) (Hzx : ZXstack zx) :
  m = big_sum (ZXstack_out_dims zx) (ZXstack_size zx).
Proof.
  induction Hzx; [reflexivity..|].
  cbn.
  rewrite Nsum_if_lt.
  now f_equal.
Qed.





Lemma ZXstack_to_big_stack {n m} (zx : ZX n m) (Hzx : ZXstack zx) : 
  zx ∝ 
  cast _ _ (ZXstack_in_dims_spec zx Hzx)
    (ZXstack_out_dims_spec zx Hzx)
    (big_stack _ _ 
      (fun k => b2ZX (ZXstack_colors zx k) _ _ 
      (ZXstack_phases zx k)) (ZXstack_size zx)).
Proof.
  induction Hzx using ZXstack_ind_dep;
  [cbn; now rewrite cast_id, 1?stack_empty_l..|].
  cbn [ZXstack_size].
  rewrite IHHzx1, IHHzx2 at 1.
  rewrite cast_stack_l_r.
  rewrite big_stack_join_add, cast_contract_eq.
  apply big_stack_simplify_casted_casted_abs;
  [reflexivity..|].
  intros k ? ? Hk.
  cbn.
  bdestruct_one; now rewrite cast_b2ZX.
Qed.














