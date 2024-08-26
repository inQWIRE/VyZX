Require Import Setoid.
Require Import CoreRules.
Import CoreData CoreAutomation.
Import CastRules.
From QuantumLib Require Import Bits.
Require Export QuantumLib.Permutations.
Import QuantumLib.VectorStates Modulus Kronecker.
Require Import ZXpermAutomation ZXpermFacts.
Require Import NFBiperm.


(* NB ncap' and ncup' have inverse interpretations to the diagrams *)
Definition cap_NF_biperm : NF_biperm := {|
  lperm' := idn; rperm' := idn;
  ncup' := 1; 
  ncap' := 0;
  nid' := 0;
|}.

Definition cup_NF_biperm : NF_biperm := {|
  lperm' := idn; rperm' := idn;
  ncup' := 0; 
  ncap' := 1;
  nid' := 0;
|}.

Definition wire_NF_biperm : NF_biperm := {|
  lperm' := idn; rperm' := idn;
  ncup' := 0; 
  ncap' := 0;
  nid' := 1;
|}.

Definition swap_NF_biperm : NF_biperm := {|
  lperm' := swap_2_perm; rperm' := idn;
  ncup' := 0; ncap' := 0;
  nid' := 2;
|}.

Lemma cap_NF_biperm_WF : WF_NF_biperm cap_NF_biperm.
Proof.
  split; cbn; auto with perm_db.
Qed.

Lemma cup_NF_biperm_WF : WF_NF_biperm cup_NF_biperm.
Proof.
  split; cbn; auto with perm_db.
Qed.

Lemma wire_NF_biperm_WF : WF_NF_biperm wire_NF_biperm.
Proof.
  split; cbn; auto with perm_db.
Qed.

Lemma swap_NF_biperm_WF : WF_NF_biperm swap_NF_biperm.
Proof.
  split; cbn; auto with perm_db.
Qed.

Lemma matrix_of_empty_NF_biperm : 
  matrix_of_NF_biperm empty_NF_biperm = ⟦ ⦰ ⟧.
Proof.
  apply matrix_of_biperm_0_0.
Qed.

Lemma matrix_of_cap_NF_biperm : 
  matrix_of_NF_biperm cap_NF_biperm = ⟦ Cap ⟧.
Proof.
  prep_matrix_equivalence.
  by_cell; reflexivity.
Qed.

Lemma matrix_of_cup_NF_biperm : 
  matrix_of_NF_biperm cup_NF_biperm = ⟦ Cup ⟧.
Proof.
  prep_matrix_equivalence.
  by_cell; reflexivity.
Qed.

Lemma matrix_of_wire_NF_biperm : 
  matrix_of_NF_biperm wire_NF_biperm = ⟦ — ⟧.
Proof.
  prep_matrix_equivalence.
  by_cell; reflexivity.
Qed.

Lemma matrix_of_swap_NF_biperm : 
  matrix_of_NF_biperm swap_NF_biperm = ⟦ ⨉ ⟧.
Proof.
  prep_matrix_equivalence.
  by_cell; reflexivity.
Qed.

Inductive ZXbiperm : forall {n m}, ZX n m -> Prop :=
  | BipermEmpty : ZXbiperm Empty
  | BipermWire : ZXbiperm Wire 
  | BipermCup : ZXbiperm Cup
  | BipermCap : ZXbiperm Cap
  | BipermSwap : ZXbiperm Swap
  | BipermCompose {n m o} {zx0 : ZX n m} {zx1 : ZX m o} : 
    ZXbiperm zx0 -> ZXbiperm zx1 -> ZXbiperm (zx0 ⟷ zx1)
  | BipermStack {n m o p} {zx0 : ZX n m} {zx1 : ZX o p} : 
    ZXbiperm zx0 -> ZXbiperm zx1 -> ZXbiperm (zx0 ↕ zx1).

Fixpoint NF_of_zx {n m} (zx : ZX n m) : NF_biperm :=
  match zx with 
  | ⦰ => empty_NF_biperm
  | Cup => cup_NF_biperm
  | Cap => cap_NF_biperm
  | — => wire_NF_biperm
  | ⨉ => swap_NF_biperm
  | zx0 ↕ zx1 => stack_NF_biperms (NF_of_zx zx0) (NF_of_zx zx1)
  | zx0 ⟷ zx1 => compose_NF_biperms (NF_of_zx zx0) (NF_of_zx zx1)
  (* Junk cases: *)
  | Box => empty_NF_biperm
  | X_Spider _ _ _ => empty_NF_biperm
  | Z_Spider _ _ _ => empty_NF_biperm
  end.

Lemma NF_insize_compose_NF_biperms b c  
  (Hb : WF_NF_biperm b) (Hc : WF_NF_biperm c) 
  (Hbc : NF_outsize b = NF_insize c) : 
  NF_insize (compose_NF_biperms b c) = NF_insize b.
Proof.
  unfold compose_NF_biperms.
  cbn.
  rewrite double_add, <- Nat.add_assoc.
  rewrite ncup_ncup_nid_compose_n_caps_NF_l;
  [cbn; lia..|].
  apply compose_perm_l_NF_biperm_WF;
  [apply Hc | rewrite <- Hbc; apply Hb].
Qed.

Lemma NF_outsize_compose_NF_biperms b c  
  (Hb : WF_NF_biperm b) (Hc : WF_NF_biperm c) 
  (Hbc : NF_outsize b = NF_insize c) : 
  NF_outsize (compose_NF_biperms b c) = NF_outsize c.
Proof.
  unfold compose_NF_biperms.
  cbn.
  rewrite ncap_ncap_nid_compose_n_caps_NF_l;
  [cbn; lia..|].
  apply compose_perm_l_NF_biperm_WF;
  [apply Hc | rewrite <- Hbc; apply Hb].
Qed.

Lemma NF_of_zx_size_and_WF {n m} (zx : ZX n m) (H : ZXbiperm zx) : 
  WF_NF_biperm (NF_of_zx zx) /\ 
  NF_insize (NF_of_zx zx) = n /\ 
  NF_outsize (NF_of_zx zx) = m.
Proof.
  induction H; cbn [NF_of_zx].
  - split; [|easy]; apply empty_NF_biperm_WF.
  - split; [|easy]; apply wire_NF_biperm_WF.
  - split; [|easy]; apply cup_NF_biperm_WF.
  - split; [|easy]; apply cap_NF_biperm_WF.
  - split; [|easy]; apply swap_NF_biperm_WF.
  - split. 
    + apply compose_NF_biperms_WF; lia + easy.
    + rewrite NF_insize_compose_NF_biperms by lia + easy.
      rewrite NF_outsize_compose_NF_biperms by lia + easy.
      lia.
  - split; [|cbn; lia..].
    apply stack_NF_biperms_WF; easy.
Qed.

Lemma NF_of_zx_WF {n m} (zx : ZX n m) (H : ZXbiperm zx) : 
  WF_NF_biperm (NF_of_zx zx).
Proof. now apply NF_of_zx_size_and_WF. Qed.

Lemma NF_insize_NF_of_zx {n m} (zx : ZX n m) (H : ZXbiperm zx) : 
  NF_insize (NF_of_zx zx) = n.
Proof. now apply NF_of_zx_size_and_WF. Qed.

Lemma NF_outsize_NF_of_zx {n m} (zx : ZX n m) (H : ZXbiperm zx) : 
  NF_outsize (NF_of_zx zx) = m.
Proof. now apply NF_of_zx_size_and_WF. Qed.

Lemma NF_of_zx_correct {n m} (zx : ZX n m) (H : ZXbiperm zx) : 
  ⟦ zx ⟧ [∝] matrix_of_NF_biperm (NF_of_zx zx).
Proof.
  induction H; cbn [NF_of_zx].
  - now rewrite matrix_of_empty_NF_biperm.
  - now rewrite matrix_of_wire_NF_biperm.
  - now rewrite matrix_of_cup_NF_biperm.
  - now rewrite matrix_of_cap_NF_biperm.
  - now rewrite matrix_of_swap_NF_biperm.
  - destruct (NF_of_zx_size_and_WF zx0 ltac:(assumption))
      as (HWF1 & Hin1 & Hout1).
    destruct (NF_of_zx_size_and_WF zx1 ltac:(assumption))
      as (HWF2 & Hin2 & Hout2).
    rewrite compose_NF_biperms_correct by assumption + lia.
    rewrite Hin1, Hin2, Hout2.
    now apply Mmult_mat_prop_proper.
  - destruct (NF_of_zx_size_and_WF zx0 ltac:(assumption))
      as (HWF1 & Hin1 & Hout1).
    destruct (NF_of_zx_size_and_WF zx1 ltac:(assumption))
      as (HWF2 & Hin2 & Hout2).
    rewrite stack_NF_biperms_correct by assumption + lia.
    rewrite Hin1, Hin2, Hout1, Hout2.
    now apply kron_mat_prop_proper.
Qed.

Notation biperm_of_zx zx := (realize_NF_biperm (NF_of_zx zx)).

Lemma ZXbiperm_prop_by_biperm_eq {n m} (zx0 zx1 : ZX n m) 
  (Hzx0 : ZXbiperm zx0) (Hzx1 : ZXbiperm zx1) : 
  perm_eq (m + n) (biperm_of_zx zx0) (biperm_of_zx zx1) ->
  zx0 ∝ zx1.
Proof.
  intros Heq.
  change (⟦zx0⟧ [∝] ⟦zx1⟧).
  rewrite 2!NF_of_zx_correct by easy.
  unfold matrix_of_NF_biperm.
  rewrite !NF_insize_NF_of_zx, !NF_outsize_NF_of_zx by assumption.
  erewrite matrix_of_biperm_eq_of_perm_eq;
  [|rewrite Nat.add_comm; apply Heq].
  easy.
Qed.

(* Automation and specific instances *)

Lemma zxbiperm_cast {n m n' m'} (zx : ZX n m) prfn prfm : 
  ZXbiperm zx -> ZXbiperm (cast n' m' prfn prfm zx).
Proof.
  now subst.
Qed.

Create HintDb zxbiperm_db discriminated.

#[export] Hint Constructors ZXbiperm : zxbiperm_db.
#[export] Hint Resolve zxbiperm_cast : zxbiperm_db.
(* Makes it handle dimensions better, particularly 
  for small, concrete examples: *)
#[export] Hint Extern 0 (ZXbiperm (_ ⟷ _)) =>
  apply BipermCompose : zxbiperm_db.
#[export] Hint Extern 0 (ZXbiperm (?zx0 ↕ ?zx1)) =>
  match type of zx0 with
  | ZX ?n0 ?m0 =>
  match type of zx1 with
  | ZX ?n1 ?m1 =>
  apply (@BipermStack _ _ _ _ zx0 zx1)
  end end : zxbiperm_db.

Lemma zxperm_zxbiperm {n} (zx : ZX n n) : ZXperm n zx -> ZXbiperm zx.
Proof.
  intros H.
  induction H; auto with zxbiperm_db.
Qed.

(* NB for this to do anything, zxperm_db will have to be used
   as well, e.g. auto with zxbiperm_db zxperm_db *)
#[export] Hint Resolve zxperm_zxbiperm : zxbiperm_db.

Lemma transpose_zxbiperm {n m} (zx : ZX n m) (H : ZXbiperm zx) :
  ZXbiperm (ZXCore.transpose zx).
Proof.
  induction H; cbn; auto with zxbiperm_db.
Qed.

Lemma colorswap_zxbiperm {n m} (zx : ZX n m) (H : ZXbiperm zx) :
  ZXbiperm (⊙ zx).
Proof.
  induction H; cbn; auto with zxbiperm_db.
Qed.

Lemma adjoint_zxbiperm {n m} (zx : ZX n m) (H : ZXbiperm zx) :
  ZXbiperm (ZXCore.adjoint zx).
Proof.
  induction H; cbn; auto with zxbiperm_db.
Qed.

#[export] Hint Resolve transpose_zxbiperm 
  colorswap_zxbiperm adjoint_zxbiperm : zxbiperm_db.

Lemma n_stack_zxbiperm {m o} (zx : ZX m o) n (H : ZXbiperm zx) : 
  ZXbiperm (n ⇑ zx).
Proof.
  induction n; cbn; auto with zxbiperm_db.
Qed.

#[export] Hint Resolve n_stack_zxbiperm : zxbiperm_db.


Lemma n_stacked_pf_1 {n} : n + n = n * 2. Proof. lia. Qed.
Lemma n_stacked_pf_2 {n} : 0 = n * 0. Proof. lia. Qed.
Definition n_stacked_caps n : ZX (n + n) 0 :=
  cast _ _ n_stacked_pf_1 n_stacked_pf_2 (n ⇑ ⊃).

Definition n_stacked_cups n : ZX 0 (n + n) :=
  cast _ _ n_stacked_pf_2 n_stacked_pf_1 (n ⇑ ⊂).

Lemma n_stacked_caps_zxbiperm n : 
  ZXbiperm (n_stacked_caps n).
Proof. 
  unfold n_stacked_caps. 
  auto with zxbiperm_db.
Qed.

Lemma n_stacked_cups_zxbiperm n : 
  ZXbiperm (n_stacked_cups n).
Proof. 
  unfold n_stacked_cups. 
  auto with zxbiperm_db.
Qed.

#[export] Hint Resolve n_stacked_caps_zxbiperm 
  n_stacked_cups_zxbiperm : zxbiperm_db.

Lemma n_stack_semantics {n m} (zx : ZX n m) k : 
  ⟦ k ⇑ zx ⟧ = kron_n k (⟦ zx ⟧).
Proof.
  induction k; [easy|].
  rewrite kron_n_assoc by auto_wf.
  cbn.
  f_equal;
  [rewrite Nat.mul_comm; apply Nat.pow_mul_r..|].
  easy.
Qed.

Lemma n_stacked_caps_semantics n : 
  ⟦ n_stacked_caps n ⟧ = kron_n n (⟦ ⊃ ⟧).
Proof.
  unfold n_stacked_caps.
  rewrite cast_semantics_dim.
  unfold cast_semantics_dim_eqn.
  apply n_stack_semantics.
Qed.

Lemma n_stacked_cups_semantics n : 
  ⟦ n_stacked_cups n ⟧ = kron_n n (⟦ ⊂ ⟧).
Proof.
  unfold n_stacked_cups.
  rewrite cast_semantics_dim.
  unfold cast_semantics_dim_eqn.
  apply n_stack_semantics.
Qed.

Definition zx_of_NF_uncasted (b : NF_biperm) : 
  ZX (NF_insize b) (NF_outsize b) :=
  zx_of_perm (NF_insize b) (lperm' b) ⟷
    ((n_stacked_caps (ncup' b) ⟷ n_stacked_cups (ncap' b)) 
    ↕ n_wire (nid' b)) ⟷
  zx_of_perm (NF_outsize b) (rperm' b).

Lemma zx_of_NF_uncasted_semantics b (Hb : WF_NF_biperm b) : 
  ⟦ zx_of_perm (NF_insize b) (lperm' b) ⟷
      ((n_stacked_caps (ncup' b) ⟷ n_stacked_cups (ncap' b)) 
      ↕ n_wire (nid' b)) ⟷
    zx_of_perm (NF_outsize b) (rperm' b) ⟧ = 
  matrix_of_NF_biperm b.
Proof.
  cbn [ZX_semantics].
  rewrite 2!zx_of_perm_semantics by apply Hb.
  rewrite n_stacked_cups_semantics, n_stacked_caps_semantics.
  rewrite matrix_of_WF_NF_biperm by easy.
  rewrite matrix_of_biperm_n_m_cup_cap, n_wire_semantics.
  rewrite Mmult_assoc.
  easy.
Qed.

Lemma zx_of_NF_uncasted_zxbiperm b : 
  ZXbiperm (zx_of_NF_uncasted b).
Proof.
  unfold zx_of_NF_uncasted.
  auto with zxbiperm_db zxperm_db.
Qed.

#[export] Hint Resolve zx_of_NF_uncasted_zxbiperm : zxbiperm_db.

Definition zx_of_bipermutation n m f 
  (Hf : bipermutation (m + n) f) : ZX n m :=
  cast _ _ 
    (eq_sym (NF_insize_NF_of_biperm n m f Hf))
    (eq_sym (NF_outsize_NF_of_biperm n m f Hf))
    (zx_of_NF_uncasted (NF_of_biperm n m f)).

(* FIXME: Move *)
Definition true_rel {A} : relation A :=
  fun _ _ => True.

Instance true_rel_superrel {A} (R : relation A) : 
  subrelation R true_rel.
Proof.
  intros x y H.
  constructor.
Qed.

Add Parametric Morphism n m f : (zx_of_bipermutation n m f) 
  with signature
  true_rel ==> eq as 
  zx_of_bipermutation_proper.
Proof.
  intros H H' _.
  unfold zx_of_bipermutation.
  f_equal; 
  apply Peano_dec.UIP_nat.
Qed.

Definition bipermutation_dec n f : 
  {bipermutation n f} + {~ bipermutation n f}.
Proof.
  destruct (permutation_dec f n);
  [|right; rewrite bipermutation_defn_alt; tauto].
  destruct (perm_eq_dec n (perm_inv n f) f);
  [|right; rewrite bipermutation_defn_alt; tauto].
  destruct (bool_dec (forallb (fun k => negb (f k =? k)) 
    (seq 0 n)) true) as [e | e];
  rewrite forallb_seq0 in e;
  setoid_rewrite negb_true_iff in e;
  setoid_rewrite Nat.eqb_neq in e;
  [left | right];
  rewrite bipermutation_defn_alt;
  tauto.
Qed.

Definition zx_dummy n m : ZX n m :=
  Z n m 0.

Global Opaque zx_dummy.

Definition zx_of_biperm n m f :=
  match bipermutation_dec (m + n) f with 
  | left Hf => zx_of_bipermutation n m f Hf
  | right _ => zx_dummy n m
  end.

Lemma n_cup_unswapped_zxbiperm n : ZXbiperm (n_cup_unswapped n).
Proof.
  induction n; cbn -[Nat.add]; auto with zxbiperm_db.
Qed.

#[export] Hint Resolve n_cup_unswapped_zxbiperm : zxbiperm_db.

Lemma n_cup_zxbiperm n : ZXbiperm (n_cup n).
Proof.
  unfold n_cup.
  auto with zxbiperm_db zxperm_db.
Qed.

#[export] Hint Resolve n_cup_zxbiperm : zxbiperm_db.

Lemma n_cap_zxbiperm n : ZXbiperm (n_cap n).
Proof.
  unfold n_cap; auto with zxbiperm_db.
Qed.

#[export] Hint Resolve n_cap_zxbiperm : zxbiperm_db.



Lemma kron_f_to_vec_eq {n m p q : nat} (A : Matrix (2^n) (2^m))
  (B : Matrix (2^p) (2^q)) (f : nat -> bool) : WF_Matrix A -> WF_Matrix B -> 
  A ⊗ B × f_to_vec (m + q) f
  = A × f_to_vec m f ⊗ (B × f_to_vec q (fun k : nat => f (m + k))).
Proof.
  intros.
  prep_matrix_equivalence.
  apply kron_f_to_vec.
Qed.

Lemma realize_NF_biperm_spec b (Hb : WF_NF_biperm b) :
  perm_eq (NF_outsize b + NF_insize b) 
    (realize_NF_biperm b) 
    (stack_perms (NF_outsize b) (NF_insize b) 
      (reflect_perm (NF_outsize b) ∘ perm_inv (NF_outsize b) (rperm' b) 
        ∘ reflect_perm (NF_outsize b))
      (reflect_perm (NF_insize b) ∘ lperm' b
        ∘ reflect_perm (NF_insize b)) ∘
      stack_biperms (nid' b) (nid' b) (ncap' b + ncap' b) (ncup' b + ncup' b)
      (idn_biperm (nid' b)) (n_m_cup_cap (ncup' b) (ncap' b)) ∘
    stack_perms (NF_outsize b) (NF_insize b) 
      (reflect_perm (NF_outsize b) ∘ rperm' b
        ∘ reflect_perm (NF_outsize b))
      (reflect_perm (NF_insize b) ∘ perm_inv (NF_insize b) (lperm' b)
        ∘ reflect_perm (NF_insize b))).
Proof.
  unfold realize_NF_biperm, uncurry_NF_biperm.
  unfold realize_biperm_data.
  rewrite biperm_compose_perm_l_spec.
  destruct Hb.
  rewrite biperm_compose_perm_r_spec by auto with biperm_db.
  rewrite !compose_assoc, stack_perms_compose, 
    <- ! compose_assoc, stack_perms_compose by auto with perm_bounded_db.
  rewrite 2!compose_idn_l, 2!compose_idn_r.
  rewrite !perm_inv_compose by auto with perm_db.
  repeat rewrite reflect_perm_inv at 1.
  rewrite perm_inv_perm_inv by auto with perm_db.
  easy.
Qed.

Lemma div_eq a b : a / b = (a - a mod b) / b.
Proof.
  rewrite (Nat.div_mod_eq a b) at 2.
  rewrite Nat.add_sub.
  bdestruct (b =? 0).
  - now subst.
  - now rewrite Nat.mul_comm, Nat.div_mul by easy.
Qed.

(* Search Nat.modulo Nat.sub. *)
Lemma div_sub a b c : c <> 0 -> 
  (b * c - a) / c = b - a / c - Nat.b2n (¬ a mod c =? 0).
Proof.
  intros Hc.
  bdestruct (a <? b * c); cycle 1.
  - replace (b * c - a) with 0 by lia.
    rewrite Nat.Div0.div_0_l.
    pose proof (Nat.div_le_lower_bound a c b); lia.
  - assert (a / c < b) by show_moddy_lt.
    apply (Nat.mul_cancel_r _ _ c Hc).
    rewrite div_mul_not_exact by easy.
    rewrite 2!Nat.mul_sub_distr_r.
    rewrite div_mul_not_exact by easy.
    pose proof (Nat.mod_le (b * c - a) c Hc).
    pose proof (Nat.mod_le a c Hc).
    enough (a + (b * c - a) mod c = 
      (a + c * Nat.b2n (¬ a mod c =? 0) - a mod c))
      by lia.
    rewrite <- Nat.add_sub_assoc by 
      (pose proof (Nat.mod_upper_bound a c Hc);
      bdestructΩ'; cbn; lia).
    f_equal.
    Abort.



Lemma kron_comm_perm_2_n_conj_reflect_perm_eq n : 
  reflect_perm (n + n) ∘ kron_comm_perm 2 n ∘ reflect_perm (n + n) = 
  kron_comm_perm 2 n.
Proof.
  replace (n + n) with (2 * n) by lia.
  eq_by_WF_perm_eq (2 * n).
  do 2 rewrite reflect_perm_defn at 1.
  rewrite kron_comm_perm_defn.
  unfold compose.
  intros k Hk.
  Abort.


Lemma reflect_perm_NF_rep n : 
  is_NF_representative (n + n) (n + n) 
    {| lperm' := idn; rperm' := kron_comm_perm 2 n;
      ncup' := 0; ncap' := n; nid' := 0|} (reflect_perm (n + n)).
Proof.
  split.
  split; cbn; auto with perm_db; 
  eapply permutation_change_dims; [| auto with perm_db]; lia.
  split; split; [cbn; lia..|].
  rewrite realize_NF_biperm_constructor.
  unfold realize_biperm_data.
  eapply perm_eq_dim_change_if_nonzero;
  [rewrite biperm_compose_perm_l_spec|lia].
  rewrite biperm_compose_perm_r_spec by auto with biperm_db.
  rewrite compose_assoc.
  cleanup_perm.
  zarith.
  eapply permutation_change_dims; [|auto with perm_db];
   solve [eauto with perm_db zarith].
  Abort.

Lemma n_cup_unswapped_semantics n : 
  ⟦ n_cup_unswapped n ⟧ = 
  matrix_of_biperm 0 (n + n) 
    (reflect_perm (n + n)).
Proof.
  induction n.
  - cbn.
    now rewrite matrix_of_biperm_0_0.
  - cbn.
    simpl_rewrite' matrix_of_cap_NF_biperm.
Abort.



(* FIXME: These lemmas go in BipermutationMatrices.v *)

Lemma number_preserved_0 f n : 
  number_preserved 0 f n = true.
Proof.
  rewrite number_preserved_iff_all_lt_eq.
  intros; now rewrite 2!Nat.bits_0.
Qed.

Lemma matrix_of_biperm_entry_0_0 n m f : 
  matrix_of_biperm m n f 0 0 = C1.
Proof.
  unfold matrix_of_biperm.
  do 2 simplify_bools_moddy_lia_one_kernel.
  now rewrite number_preserved_0.
Qed.

Lemma matrix_of_biperm_mat_equiv_of_prop n m f g : 
  matrix_of_biperm m n f [∝] matrix_of_biperm m n g ->
  matrix_of_biperm m n f ≡ matrix_of_biperm m n g.
Proof.
  intros (c & Heq & Hc).
  assert (Hc' : (matrix_of_biperm m n f 0 0 = 
    c * matrix_of_biperm m n g 0 0)%C)
  by now rewrite Heq.
  rewrite 2!matrix_of_biperm_entry_0_0 in Hc'.
  Csimpl_in Hc'.
  rewrite <- Hc' in Heq.
  rewrite Heq.
  now rewrite Mscale_1_l.
Qed.


(* Lemma matrix_of_biperm_reflect_perm_grow_0_l *)

Lemma compose_NF_biperms_correct' (b c : NF_biperm) n m : 
  WF_NF_biperm b -> WF_NF_biperm c -> 
  NF_outsize b = NF_insize c ->
  NF_insize b = n -> NF_outsize c = m ->
  matrix_of_biperm n m (realize_NF_biperm (compose_NF_biperms b c)) [∝]
  @Mmult (2^n) (2^NF_insize c) (2^m) 
    (matrix_of_NF_biperm c) (matrix_of_NF_biperm b).
Proof.
  intros.
  subst n m.
  rewrite <- (compose_NF_biperms_correct c b) by easy.
  unfold matrix_of_NF_biperm.
  rewrite NF_insize_compose_NF_biperms, 
    NF_outsize_compose_NF_biperms by easy.
  easy.
Qed.

Lemma fn_cast_eq {A} {n m n' m'} (f : forall {n m}, ZX n m -> A) (zx : ZX n m) 
  prfn prfm : 
  f (cast n' m' prfn prfm zx) = f zx.
Proof.
  now subst.
Qed.

(* FIXME: Move *)
Create HintDb WF_NF_biperm_db discriminated.
#[export] Hint Resolve 
  empty_NF_biperm_WF wire_NF_biperm_WF cup_NF_biperm_WF cap_NF_biperm_WF
  swap_NF_biperm_WF 
  NF_of_zx_WF
  stack_NF_biperms_WF compose_NF_biperms_WF
  : WF_NF_biperm_db.

Create HintDb zxbiperm_cleanup_db.
#[export] Hint Rewrite @NF_insize_NF_of_zx 
  @NF_outsize_NF_of_zx using 
  solve [auto with zxbiperm_db] : zxbiperm_cleanup_db.
#[export] Hint Rewrite 
  NF_insize_stack_NF_biperms 
  NF_outsize_stack_NF_biperms : zxbiperm_cleanup_db.

Fixpoint make_n_cup_zxperm n : ZX (n * 2) (n * 2) :=
  match n return ZX (n * 2) (n * 2) with 
  | O => Empty
  | S n' => 
    (fun H G => 
    @cast ((S n') * 2) ((S n') * 2) _ _
      H G (— ↕ (zx_comm (n' * 2) 1))) 
      ltac:(lia) ltac:(lia) ⟷ (n_wire 2 ↕ make_n_cup_zxperm n')
  end.

Import CoreRules.

Lemma stack_split_diag {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) : 
  zx0 ↕ zx1 ∝ zx0 ↕ n_wire o ⟷ (n_wire m ↕ zx1).
Proof.
  now cleanup_zx.
Qed.

Lemma stack_split_antidiag {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) : 
  zx0 ↕ zx1 ∝ (n_wire n ↕ zx1) ⟷ (zx0 ↕ n_wire p).
Proof.
  now cleanup_zx.
Qed.



Lemma make_n_cup_zxperm_correct n : 
  ltac:(let l := constr:((fun H G => n_cup_unswapped n ∝ 
  cast (n + n) 0 H G (make_n_cup_zxperm n ⟷ n_stack n ⊃))
  ltac:(lia) ltac:(lia)) in 
  let l' := eval cbn beta in l in exact l').
Proof.
  induction n.
  cbn.
  now rewrite cast_id, compose_empty_r.
  cbn -[Nat.add Nat.mul n_stack1].
  rewrite compose_assoc.
  rewrite <- (stack_compose_distr (n_wire 2) ⊃ (make_n_cup_zxperm n) (n ⇑ ⊃)).
  apply (cast_mor (n * 2) (n * 0) (n + n) 0 ltac:(lia) ltac:(lia) _ _) in IHn.
  clean_eqns rewrite cast_contract, cast_compose_distribute, 2!cast_id in IHn.
  rewrite <- IHn.
  rewrite nwire_removal_l.
  clean_eqns rewrite cast_compose_distribute.
  cbn [Nat.mul Nat.add]. 
  clean_eqns simpl_rewrite (@cast_stack_distribute 2 2 0 0).
  clean_eqns rewrite cast_id, !cast_contract.
  rewrite (stack_split_antidiag ⊃).
  rewrite <- compose_assoc.
  rewrite cast_compose_l, cast_id.
  change (n_wire 2) with (— ↕ n_wire 1).
  rewrite <- wire_to_n_wire.
  clean_eqns rewrite (stack_assoc — —), cast_id.
  rewrite cast_compose_l, cast_id.
  rewrite <- (stack_wire_distribute_l (zx_comm (n * 2) 1) 
    (— ↕ $ n * 2, 0 ::: n_cup_unswapped n $)).
  rewrite zx_comm_commutes_l.
  rewrite cast_compose_distribute.
  apply compose_simplify; [|now clean_eqns rewrite stack_empty_r, 2!cast_id].
  rewrite (ltac:(unfold zx_comm; (clean_eqns rewrite cast_id); by_perm_eq) : zx_comm 0 1 ∝ —).
  rewrite wire_removal_r.
  clean_eqns rewrite cast_stack_l, cast_stack_r, cast_contract.
  clean_eqns rewrite stack_assoc_back, cast_contract.
  now apply cast_simplify.
Qed.



Lemma biperm_of_n_cup_unswapped n : 
  perm_eq (n + n)
    (biperm_of_zx (n_cup_unswapped n))
    (reflect_perm (n + n)).
Proof.
  rewrite reflect_perm_defn.
  induction n; [easy|].
  rewrite <- Nat.add_0_r at 1.
  apply matrix_of_biperm_inj.
  - rewrite <- (NF_insize_NF_of_zx (n_cup_unswapped (S n))) at 1
      by auto with zxbiperm_db.
    pose proof (NF_outsize_NF_of_zx (n_cup_unswapped (S n)) 
      ltac:(auto with zxbiperm_db)) as Heq.
    rewrite <- Heq at 4.
    apply realize_NF_biperm_bipermutation_alt.
    apply NF_of_zx_WF; auto with zxbiperm_db.
  - intros k Hk; lia.
  - apply matrix_of_biperm_mat_equiv_of_prop.
    cbn -[Nat.add].
    rewrite compose_NF_biperms_correct' by 
      (autorewrite with zxbiperm_cleanup_db; 
      auto with WF_NF_biperm_db zxbiperm_db;
      cbn; lia).
    rewrite fn_cast_eq.
    cbn [NF_of_zx].
    rewrite 2!stack_NF_biperms_correct 
      by auto with WF_NF_biperm_db zxbiperm_db.
    rewrite matrix_of_cap_NF_biperm, matrix_of_wire_NF_biperm.
    prop_exists_nonzero 1%R.
    restore_dims.
    rewrite Mscale_1_l.
    autorewrite with zxbiperm_cleanup_db.
    cbn -[Nat.add ZX_semantics].
    apply mat_equiv_eq; 
    [auto using WF_Matrix_dim_change with wf_db zarith..|].
    apply WF_Matrix_dim_change; [lia..|].
    apply WF_mult; [auto_wf|..].
    repeat apply WF_kron; unify_pows_two; try lia; 
    auto_wf.
    autorewrite with zxbiperm_cleanup_db.
    eapply WF_Matrix_dim_change; 
    [..|apply matrix_of_NF_biperm_WF];
    autorewrite with zxbiperm_cleanup_db; reflexivity.
    unify_pows_two.
    eapply WF_Matrix_dim_change; 
    [..|apply matrix_of_biperm_WF];
    cbn [Nat.add]; unify_pows_two; reflexivity.
    apply mat_equiv_of_all_basis_conj.
    intros i j Hi Hj.
    cbn [Nat.add] in *.
    unify_pows_two.
    rewrite basis_f_to_vec_alt by (revert Hj; now unify_pows_two).
    apply matrix_of_NF_biperm_WF.
Abort.


(* Lemma yank_r: forall n, n_cup n ∝ n_wire n ↕ n_swap n ⟷ n_cup_unswapped n.
Proof.
  intros n.
  bdestruct (n =? 1).
  subst.
  unfold n_cup.
  cbn.
  rewrite cast_id.
  apply ZXbiperm_prop_by_biperm_eq; [admit..|].
  Time ZXpermAutomation.by_perm_cell; reflexivity.
  prop_exists_nonzero 1.
  rewrite Mscale_1_l.
  lma'.
Qed. *)






























