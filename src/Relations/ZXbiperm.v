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
  insize' := 2;
  outsize' := 0;
|}.

Definition cup_NF_biperm : NF_biperm := {|
  lperm' := idn; rperm' := idn;
  ncup' := 0; 
  ncap' := 1;
  nid' := 0;
  insize' := 0;
  outsize' := 2;
|}.

Definition wire_NF_biperm : NF_biperm := {|
  lperm' := idn; rperm' := idn;
  ncup' := 0; 
  ncap' := 0;
  nid' := 1;
  insize' := 1;
  outsize' := 1;
|}.

Definition swap_NF_biperm : NF_biperm := {|
  lperm' := swap_2_perm; rperm' := idn;
  ncup' := 0; ncap' := 0;
  nid' := 2;
  insize' := 2;
  outsize' := 2;
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

#[export] Hint Resolve 
  cup_NF_biperm_WF cap_NF_biperm_WF
  wire_NF_biperm_WF swap_NF_biperm_WF : WF_NF_biperm_db.

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

Lemma matrix_of_stack_NF_biperms b c 
  (Hb : WF_NF_biperm b) (Hc : WF_NF_biperm c) : 
  matrix_of_NF_biperm (stack_NF_biperms b c) = 
  matrix_of_NF_biperm b ⊗ matrix_of_NF_biperm c.
Proof.
  prep_matrix_equivalence.
  unfold matrix_of_NF_biperm.
  rewrite realize_stack_NF_biperms by auto.
  now rewrite matrix_of_stack_biperms' by auto_biperm.
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

Fixpoint NF_of_zx_rec {n m} (zx : ZX n m) : NF_biperm :=
  match zx with 
  | ⦰ => empty_NF_biperm
  | Cup => cup_NF_biperm
  | Cap => cap_NF_biperm
  | — => wire_NF_biperm
  | ⨉ => swap_NF_biperm
  | zx0 ↕ zx1 => stack_NF_biperms (NF_of_zx_rec zx0) (NF_of_zx_rec zx1)
  | zx0 ⟷ zx1 => compose_NF_biperms (NF_of_zx_rec zx0) (NF_of_zx_rec zx1)
  (* Junk cases: *)
  | Box => empty_NF_biperm
  | X_Spider _ _ _ => empty_NF_biperm
  | Z_Spider _ _ _ => empty_NF_biperm
  end.

Definition NF_of_zx {n m} (zx : ZX n m) : NF_biperm :=
  cast_NF_biperm (NF_of_zx_rec zx) n m.

(* FIXME: Move to NFBiperm *)
#[export] Hint Resolve compose_NF_biperms_WF : WF_NF_biperm_db.

Lemma NF_insize_compose_NF_biperms b c  
  (Hb : WF_NF_biperm b) (Hc : WF_NF_biperm c) 
  (Hbc : NF_outsize b = NF_insize c) : 
  NF_insize (compose_NF_biperms b c) = NF_insize b.
Proof.
  rewrite <- insize_WF, <- outsize_WF in Hbc by auto.
  rewrite <- 2!insize_WF by auto with WF_NF_biperm_db.
  easy.
Qed.

Lemma NF_outsize_compose_NF_biperms b c  
  (Hb : WF_NF_biperm b) (Hc : WF_NF_biperm c) 
  (Hbc : NF_outsize b = NF_insize c) : 
  NF_outsize (compose_NF_biperms b c) = NF_outsize c.
Proof.
  rewrite <- insize_WF, <- outsize_WF in Hbc by auto.
  rewrite <- 2!outsize_WF by auto with WF_NF_biperm_db.
  easy.
Qed.

Lemma NF_of_zx_rec_size_and_WF {n m} (zx : ZX n m) (H : ZXbiperm zx) : 
  WF_NF_biperm (NF_of_zx_rec zx) /\ 
  insize' (NF_of_zx_rec zx) = n /\ 
  outsize' (NF_of_zx_rec zx) = m.
Proof.
  induction H; [auto with WF_NF_biperm_db..| |];
  destruct IHZXbiperm1 as (HWF1 & Hin1 & Hout1);
  destruct IHZXbiperm2 as (HWF2 & Hin2 & Hout2);
  auto with WF_NF_biperm_db zarith.
Qed.

Lemma NF_of_zx_rec_WF {n m} (zx : ZX n m) (H : ZXbiperm zx) :
  WF_NF_biperm (NF_of_zx_rec zx).
Proof. now apply NF_of_zx_rec_size_and_WF. Qed.

Lemma insize_NF_of_zx_rec {n m} (zx : ZX n m) (H : ZXbiperm zx) :
  insize' (NF_of_zx_rec zx) = n.
Proof. now apply NF_of_zx_rec_size_and_WF. Qed.

Lemma outsize_NF_of_zx_rec {n m} (zx : ZX n m) (H : ZXbiperm zx) :
  outsize' (NF_of_zx_rec zx) = m.
Proof. now apply NF_of_zx_rec_size_and_WF. Qed.

#[export] Hint Resolve NF_of_zx_rec_WF
  insize_NF_of_zx_rec outsize_NF_of_zx_rec : WF_NF_biperm_db.

(* FIXME: Move to by its definition *)
#[export] Hint Resolve cast_NF_biperm_WF : WF_NF_biperm_db.

Lemma cast_NF_biperm_WF' b insize outsize (Hb : WF_NF_biperm b) 
  (Hin : insize' b = insize) (Hout : outsize' b = outsize) : 
  WF_NF_biperm (cast_NF_biperm b insize outsize).
Proof.
  auto with WF_NF_biperm_db.
Qed.

#[export] Hint Resolve cast_NF_biperm_WF' : WF_NF_biperm_db.

Lemma NF_of_zx_defn {n m} (zx : ZX n m) (H : ZXbiperm zx) : 
  NF_of_zx zx = NF_of_zx_rec zx.
Proof.
  apply cast_NF_biperm_defn; symmetry; auto with WF_NF_biperm_db.
Qed.

Lemma NF_of_zx_WF {n m} (zx : ZX n m) (H : ZXbiperm zx) : 
  WF_NF_biperm (NF_of_zx zx).
Proof.
  rewrite NF_of_zx_defn by auto.
  auto with WF_NF_biperm_db.
Qed.

#[export] Hint Resolve NF_of_zx_WF : WF_NF_biperm_db.


Lemma NF_insize_NF_of_zx {n m} (zx : ZX n m) (H : ZXbiperm zx) : 
  NF_insize (NF_of_zx zx) = n.
Proof. now rewrite <- insize_WF by auto with WF_NF_biperm_db. Qed.

Lemma NF_outsize_NF_of_zx {n m} (zx : ZX n m) (H : ZXbiperm zx) : 
  NF_outsize (NF_of_zx zx) = m.
Proof. now rewrite <- outsize_WF by auto with WF_NF_biperm_db. Qed.

Lemma NF_of_zx_correct {n m} (zx : ZX n m) (H : ZXbiperm zx) : 
  ⟦ zx ⟧ [∝] matrix_of_NF_biperm (NF_of_zx zx).
Proof.
  rewrite NF_of_zx_defn by auto.
  induction H; cbn [NF_of_zx_rec].
  - now rewrite matrix_of_empty_NF_biperm.
  - now rewrite matrix_of_wire_NF_biperm.
  - now rewrite matrix_of_cup_NF_biperm.
  - now rewrite matrix_of_cap_NF_biperm.
  - now rewrite matrix_of_swap_NF_biperm.
  - destruct (NF_of_zx_rec_size_and_WF zx0 ltac:(assumption))
      as (HWF1 & Hin1 & Hout1).
    destruct (NF_of_zx_rec_size_and_WF zx1 ltac:(assumption))
      as (HWF2 & Hin2 & Hout2).
    rewrite compose_NF_biperms_correct by assumption + lia.
    rewrite Hin1, Hin2, Hout2.
    now apply Mmult_mat_prop_proper.
  - destruct (NF_of_zx_rec_size_and_WF zx0 ltac:(assumption))
      as (HWF1 & Hin1 & Hout1).
    destruct (NF_of_zx_rec_size_and_WF zx1 ltac:(assumption))
      as (HWF2 & Hin2 & Hout2).
    rewrite stack_NF_biperms_correct by assumption + lia.
    rewrite Hin1, Hin2, Hout1, Hout2.
    now apply kron_mat_prop_proper.
Qed.

Notation biperm_of_zx zx := (realize_NF_biperm (NF_of_zx zx)).

Lemma matrix_of_biperm_of_zx {n m} (zx : ZX n m) (Hzx : ZXbiperm zx) : 
  matrix_of_biperm n m (biperm_of_zx zx) [∝]
  ⟦ zx ⟧.
Proof.
  now rewrite NF_of_zx_correct by easy.
Qed.

Lemma ZXbiperm_prop_by_biperm_eq {n m} (zx0 zx1 : ZX n m) 
  (Hzx0 : ZXbiperm zx0) (Hzx1 : ZXbiperm zx1) : 
  perm_eq (n + m) (biperm_of_zx zx0) (biperm_of_zx zx1) ->
  zx0 ∝ zx1.
Proof.
  intros Heq.
  change (⟦zx0⟧ [∝] ⟦zx1⟧).
  rewrite 2!NF_of_zx_correct by easy.
  unfold matrix_of_NF_biperm.
  now rewrite Heq.
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
#[export] Hint Extern 0 (ZXbiperm (?zx0 ⟷ ?zx1)) =>
  match type of zx0 with
  | ZX ?n0 ?m0 =>
  match type of zx1 with
  | ZX ?n1 ?m1 =>  
  apply (@BipermCompose _ _ _ zx0 zx1)
  end end : zxbiperm_db.
#[export] Hint Extern 0 (ZXbiperm (?zx0 ↕ ?zx1)) =>
  match type of zx0 with
  | ZX ?n0 ?m0 =>
  match type of zx1 with
  | ZX ?n1 ?m1 =>
  apply (@BipermStack _ _ _ _ zx0 zx1)
  end end : zxbiperm_db.

Lemma zxperm_zxbiperm {n m} (zx : ZX n m) : ZXperm zx -> ZXbiperm zx.
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

Lemma zxbiperm_colorswap_eq {n m} (zx : ZX n m) (Hzx : ZXbiperm zx) : 
  ⊙ zx = zx.
Proof.
  induction Hzx; simpl; now f_equal.
Qed.

Lemma zxbiperm_adjoint_eq {n m} (zx : ZX n m) (Hzx : ZXbiperm zx) : 
  zx ⊼ = zx.
Proof.
  induction Hzx; simpl; now f_equal.
Qed.

(* Lemma kron_comm_perm_2_n_ind n : 
  kron_comm_perm 2 (S n) = 
  stack_perms 2 (2 * n) idn (kron_comm_perm 2 n) ∘
  stack_perms 1 (1 + 2 * n) idn (big_swap_perm (2 * n) 1).
Proof. *)


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
  rewrite <- insize_WF, <- outsize_WF by auto.
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
  (Hf : bipermutation (n + m) f) : ZX n m :=
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
  match bipermutation_dec (n + m) f with 
  | left Hf => zx_of_bipermutation n m f Hf
  | right _ => zx_dummy n m
  end.

Lemma zx_of_biperm_bipermutation n m f (Hf : bipermutation (n + m) f) : 
  zx_of_biperm n m f = zx_of_bipermutation n m f Hf.
Proof.
  unfold zx_of_biperm.
  destruct (bipermutation_dec (n + m) f); [|easy].
  Morphisms.f_equiv.
Qed.


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
  rewrite Nat.mul_comm.
  rewrite mod_mul_sub_le by lia.
  rewrite div_sub by lia.
  rewrite <- even_eqb, Nat.negb_even, Nat.odd_succ, even_eqb.
  rewrite mod_2_succ.
  pose proof (Nat.mod_upper_bound k 2 ltac:(lia)).
  destruct (ltac:(lia) : k mod 2 = 0 \/ k mod 2 = 1) as [Hk2 | Hk2];
  rewrite Hk2.
  - cbn -[Nat.div].
    replace (S k / 2) with (k / 2).
    + enough (k / 2 < n) by lia.
      apply Nat.Div0.div_lt_upper_bound; lia.
    + change (S k) with (1 + k).
      rewrite (Nat.div_mod_eq k 2).
      rewrite Hk2, Nat.add_0_r.
      rewrite Nat.mul_comm, Nat.div_add by lia.
      rewrite Nat.div_mul by lia.
      cbn; lia.
  - cbn -[Nat.div].
    replace (S k / 2) with (S (k / 2)).
    + enough (k / 2 < n) by lia.
      apply Nat.Div0.div_lt_upper_bound; lia. 
    + change (S k) with (1 + k).
      rewrite (Nat.div_mod_eq k 2) at 2.
      rewrite Hk2.
      rewrite Nat.add_comm, <- Nat.add_assoc, <- Nat.mul_succ_r.
      now rewrite Nat.mul_comm, Nat.div_mul by lia.
Qed.


Lemma kron_comm_perm_n_2_conj_reflect_perm_eq n : 
  reflect_perm (n + n) ∘ kron_comm_perm n 2 ∘ reflect_perm (n + n) = 
  kron_comm_perm n 2.
Proof.
  eq_by_WF_perm_eq (n + n).
  pose proof (fun f => proj1 (permutation_change_dims 
    (n * 2) (n + n) ltac:(lia) f)).
  apply perm_inv_inj;
  [apply permutation_compose;
  [apply permutation_compose|]|..];
  [auto with perm_db..|].
  rewrite 2!perm_inv_compose by auto with perm_db.
  do 2 rewrite reflect_perm_inv at 1.
  pose proof (kron_comm_perm_inv n 2) as Hinv.
  replace (n * 2) with (n + n) in * by lia.
  rewrite Hinv.
  rewrite <- compose_assoc.
  now rewrite kron_comm_perm_2_n_conj_reflect_perm_eq.
Qed.

(* Lemma reflect_perm_NF_rep n : 
  is_NF_representative 0 (n + n) 
    {| lperm' := idn; rperm' := kron_comm_perm n 2;
      ncup' := 0; ncap' := n; nid' := 0|} 
    (big_swap_perm n n).
Proof.
  split.
  split; cbn; auto with perm_db; 
  eapply permutation_change_dims; [| auto with perm_db]; lia.
  split; [|split]; [cbn; lia..|].
  rewrite realize_NF_biperm_constructor.
  unfold realize_biperm_data.
  eapply perm_eq_dim_change_if_nonzero;
  [rewrite biperm_compose_perm_l_spec|lia].
  rewrite biperm_compose_perm_r_spec by auto with biperm_db.
  rewrite compose_assoc.
  rewrite !Nat.add_0_r.
  rewrite kron_comm_perm_n_2_conj_reflect_perm_eq.
  replace (n + n) with (n * 2) by lia.
  rewrite kron_comm_perm_inv.
  replace (n * 2) with (n + n) by lia.
  rewrite (ltac:(easy) : perm_eq 0 (perm_inv 0 (reflect_perm 0 ∘
    perm_inv 0 idn ∘ reflect_perm 0)) idn).
  rewrite (ltac:(easy) : perm_eq 0 (reflect_perm 0 ∘
    perm_inv 0 idn ∘ reflect_perm 0) idn).
  rewrite stack_perms_idn_idn, compose_idn_r, compose_idn_l.
  rewrite <- compose_assoc.
  intros k Hk.
  unfold compose at 1.
  rewrite stack_perms_left by easy.
  unfold compose at 1.
  unfold stack_biperms.
  cbn.
  rewrite n_m_cup_cap_ltb_double by constructor.
  rewrite Nat.sub_0_r.
  pose proof (kron_comm_perm_bounded n 2 k ltac:(lia)).
  bdestructΩ'.
  rewrite stack_perms_left 
    by (now rewrite n_m_cup_cap_lt_double_iff by lia).
  unfold kron_comm_perm.
  replace_bool_lia (n * 2 <=? k) false.
  replace (2 * n) with (n + n) by lia.
  rewrite n_m_cup_cap_geb_double by constructor.
  replace (n + n) with (2 * n) in * by lia.
  assert (k mod n * 2 + k / n < 2 * n) by show_moddy_lt.
  replace_bool_lia (2 * n <=? k mod n * 2 + k / n) false.
  rewrite n_m_cup_cap_eqb.
  cbn [Nat.add].
  replace_bool_lia (n + n <=? k mod n * 2 + k / n) false.
  rewrite div_mul_not_exact by lia.
  rewrite mod_add_l.
  assert (k / n < 2) 
    by (apply Nat.Div0.div_lt_upper_bound; lia).
  rewrite (Nat.mod_small (k / n) 2) by assumption.
  rewrite Nat.add_sub, (Nat.add_comm (_ * 2)).
  rewrite Nat.Div0.mod_add, Nat.div_add by lia.
  rewrite (Nat.div_small _ 2) by lia.
  rewrite Nat.mod_small by lia.
  unfold big_swap_perm.
  bdestruct_all; try lia.
  - rewrite Nat.div_small, Nat.mod_small; lia.
  - replace (k / n) with 1 by 
      (symmetry; rewrite div_eq_iff; lia).
    rewrite mod_n_to_2n by lia.
    lia.
Qed. *)




(* Definition zx_reflect n : ZX n n :=
  zx_of_perm n (reflect_perm n). (* NB : is ∝ n_swap n *)

Lemma zx_reflect_zxperm n : ZXperm n (zx_reflect n).
Proof.
  unfold zx_reflect.
  auto with zxperm_db.
Qed.

Lemma perm_of_zx_reflect n : 
  perm_of_zx (zx_reflect n) = reflect_perm n.
Proof.
  unfold zx_reflect.
  cleanup_perm_of_zx.
Qed. *)

Import CoreRules.



(* Lemma n_cup_unswapped_zxperm_pullthrough_top n zx (Hzx : ZXperm n zx) : 
  zx ↕ n_wire n ⟷ n_cup_unswapped n ∝ 
  n_wire n ↕ (n_swap n ⟷ zx ⊤ ⟷ n_swap n) 
    ⟷ n_cup_unswapped n.
Proof.
  prop_exists_nonzero 1.
  rewrite Mscale_1_l.
  cbn.
  rewrite n_wire_semantics.
  rewrite 2!perm_of_zx_permutation_semantics, 
    zxperm_inv'_semantics by auto with zxperm_db.
  rewrite perm_of_n_swap.
  apply equal_on_basis_states_implies_equal'; [auto_wf..|].
  intros f.
  rewrite 2!Mmult_assoc.
  restore_dims.
  rewrite 2!kron_f_to_vec_eq, !Mmult_assoc by auto_wf.
  generalize (perm_of_zx_permutation n zx Hzx).
  generalize (perm_of_zx zx).
  clear zx Hzx.
  (* Subproof :/ *)
  intros g Hg.
  rewrite (perm_to_matrix_eq_of_perm_eq _ _ _ (perm_inv'_eq n _)).
  rewrite !perm_to_matrix_permutes_qubits by auto with zxperm_db perm_db.
  rewrite 2!Mmult_1_l by auto_wf.
  rewrite 2!f_to_vec_merge.
  rewrite 2!n_cup_unswapped_f_to_vec.
  f_equal.
  f_equal.
  f_equal.
  apply eq_iff_eq_true.
  rewrite 2!forallb_seq0.
  setoid_rewrite eqb_true_iff.
  split.
  - intros Hf.
    intros s Hs.
    simplify_bools_lia_one_kernel.
    generalize (Hf (perm_inv n g s) ltac:(auto with perm_bounded_db)).
    pose proof (perm_inv_bounded n g s Hs).
    do 3 simplify_bools_lia_one_kernel.
    rewrite perm_inv_is_rinv_of_permutation by easy.
    intros ->.
    unfold reflect_perm.
    simplify_bools_lia_one_kernel.
    replace (n + n - S s - n)%nat with (n - S s)%nat by lia.
    rewrite sub_S_sub_S by lia.
    simplify_bools_lia_one_kernel.
    f_equal; lia.
  - intros Hf.
    intros s Hs.
    simplify_bools_lia_one_kernel.
    generalize (Hf (g s) ltac:(auto with perm_bounded_db)).
    pose proof (permutation_is_bounded n g Hg s Hs).
    do 3 simplify_bools_lia_one_kernel.
    intros ->.
    unfold reflect_perm.
    simplify_bools_lia_one_kernel.
    replace (n + n - S (g s) - n)%nat with (n - S (g s))%nat by lia.
    rewrite sub_S_sub_S by lia.
    rewrite perm_inv_is_linv_of_permutation by easy.
    simplify_bools_lia_one_kernel.
    f_equal; lia.
Qed. *)

(* Lemma n_cup_unswapped_zxperm_pullthrough_bot n zx (Hzx : ZXperm n zx) : 
  n_wire n ↕ zx ⟷ n_cup_unswapped n ∝ 
  (n_swap n ⟷ zxperm_inv' zx ⟷ n_swap n) ↕ n_wire n 
    ⟷ n_cup_unswapped n.
Proof.
  rewrite n_cup_unswapped_zxperm_pullthrough_top,
    2!zxperm_inv'_compose by auto with zxperm_db.
  rewrite !compose_assoc, zxperm_inv'_linv, 
    <- !compose_assoc, zxperm_inv'_rinv, zxperm_inv'_involutive 
    by auto with zxperm_db.
  now cleanup_zx.
Qed. *)

Lemma n_cup_inv_n_swap_n_wire : forall n, 
  n_cup n ∝ n_wire n ↕ n_swap n ⟷ n_cup_unswapped n.
Proof.
  intros n.
  rewrite n_cup_unswapped_pullthrough_bot by auto with zxperm_db.
  rewrite zxperm_transpose_right_inverse, nwire_removal_l by auto_zxperm.
  reflexivity.
Qed.


Lemma n_cup_unswapped_semantics n : 
  ⟦ n_cup_unswapped n ⟧ = 
  matrix_of_biperm (n + n) 0 
    (reflect_perm (n + n)).
Proof.
  apply equal_on_conj_basis_states_implies_equal; [auto_wf..|].
  intros f g.
  rewrite n_cup_unswapped_f_to_vec.
  rewrite <- Mmult_assoc.
  prep_matrix_equivalence.
  intros [] []; [|lia..]; intros _ _.
  rewrite matrix_of_biperm_funbool_conj by 
    (rewrite Nat.add_0_r; auto_perm).
  unfold scale; cbn.
  Csimpl.
  unfold b2R.
  rewrite (if_dist _ _ _ RtoC).
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite forallb_seq0.
  rewrite funbool_preserved_iff_all_lt_eq.
  setoid_rewrite eqb_true_iff.
  split.
  - intros Hf.
    intros s Hs.
    unfold reflect_perm.
    do 3 simplify_bools_lia_one_kernel.
    bdestruct (s <? n).
    + apply Hf; lia. 
    + symmetry; rewrite Hf by lia.
      now rewrite sub_S_sub_S by lia.
  - intros Hf s Hs.
    generalize (Hf s ltac:(lia)).
    unfold reflect_perm.
    do 3 simplify_bools_lia_one_kernel.
    easy.
Qed.





(* FIXME: These lemmas go in BipermutationMatrices.v *)

Open Scope nat.

Lemma number_preserved_0 f n : 
  number_preserved 0 f n = true.
Proof.
  rewrite number_preserved_iff_all_lt_eq.
  now rewrite nat_to_funbool_0.
Qed.

Lemma matrix_of_biperm_entry_0_0 n m f : 
  matrix_of_biperm m n f 0 0 = C1.
Proof.
  rewrite matrix_of_biperm_defn by show_nonzero.
  rewrite Nat.mul_0_l.
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
  outsize' b = insize' c ->
  insize' b = n -> outsize' c = m ->
  matrix_of_biperm n m (realize_NF_biperm (compose_NF_biperms b c)) [∝]
  @Mmult (2^m) (2^insize' c) (2^n) 
    (matrix_of_NF_biperm c) (matrix_of_NF_biperm b).
Proof.
  intros Hb Hc Hbc Hn Hm.
  subst n m.
  rewrite (compose_NF_biperms_correct c b) by easy.
  easy.
Qed.

Lemma fn_cast_eq {A} {n m n' m'} (f : forall {n m}, ZX n m -> A) (zx : ZX n m) 
  prfn prfm : 
  f (cast n' m' prfn prfm zx) = f zx.
Proof.
  now subst.
Qed.

(* FIXME: Check we can remove: *)
(* #[export] Hint Resolve 
  empty_NF_biperm_WF wire_NF_biperm_WF cup_NF_biperm_WF cap_NF_biperm_WF
  swap_NF_biperm_WF 
  NF_of_zx_WF
  stack_NF_biperms_WF compose_NF_biperms_WF
  : WF_NF_biperm_db. *)

Create HintDb zxbiperm_cleanup_db.
#[export] Hint Rewrite @NF_insize_NF_of_zx 
  @NF_outsize_NF_of_zx using 
  solve [auto with zxbiperm_db] : zxbiperm_cleanup_db.
#[export] Hint Rewrite 
  NF_insize_stack_NF_biperms 
  NF_outsize_stack_NF_biperms : zxbiperm_cleanup_db.
#[export] Hint Rewrite 
  NF_insize_compose_NF_biperms
  NF_outsize_compose_NF_biperms 
  using solve [auto with WF_NF_biperm_db]: zxbiperm_cleanup_db.

(* FIXME: Move *)
Lemma realize_NF_biperm_bipermutation' n m b : 
  WF_NF_biperm b -> n = insize' b -> m = outsize' b -> 
  bipermutation (n + m) (realize_NF_biperm b).
Proof.
  intros; subst.
  auto with biperm_db.
Qed.

Lemma biperm_of_zx_bipermutation {n m} (zx : ZX n m) (Hzx : ZXbiperm zx) : 
  bipermutation (n + m) (biperm_of_zx zx).
Proof.
  induction Hzx; (apply realize_NF_biperm_bipermutation'; 
    [cbn; auto using NF_of_zx_WF with WF_NF_biperm_db zxbiperm_db |..]; 
    reflexivity).
Qed.

#[export] Hint Resolve biperm_of_zx_bipermutation : biperm_db.
  
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
  rewrite (ltac:(prop_exists_nonzero 1%R; now rewrite zx_comm_semantics, 
    kron_comm_1_r, Mscale_1_l) : zx_comm 0 1 ∝ —).
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
  (* rewrite reflect_perm_defn. *)
  (* induction n; [easy|]. *)
  rewrite <- Nat.add_0_r at 1.
  apply matrix_of_biperm_inj.
  - auto with biperm_db zxbiperm_db.
  - rewrite Nat.add_0_r, reflect_perm_defn. intros k Hk; lia.
  - apply matrix_of_biperm_mat_equiv_of_prop.
    rewrite <- n_cup_unswapped_semantics.
    now rewrite matrix_of_biperm_of_zx by auto with zxbiperm_db.
Qed.

(* FIXME: Move *)
Lemma idn_biperm_eq n : idn_biperm n = big_swap_perm n n.
Proof. reflexivity. Qed.

Open Scope prg.

Lemma biperm_of_zxperm {n m} (zx : ZX n m) (Hzx : ZXperm zx) : 
  perm_eq (n + m) 
    (biperm_of_zx zx) 
    (biperm_compose_perm_l n n (idn_biperm n) 
      (perm_of_zx zx)).
Proof.
  induction (zxperm_square zx Hzx).
  apply matrix_of_biperm_inj; [auto with biperm_db zxbiperm_db..|].
  apply matrix_of_biperm_mat_equiv_of_prop.
  rewrite matrix_of_biperm_compose_perm_l_eq by auto with biperm_db.
  rewrite matrix_of_idn_biperm, Mmult_1_l by auto_wf.
  rewrite matrix_of_biperm_of_zx by auto with zxbiperm_db.
  rewrite <- perm_of_zx_permutation_semantics by easy.
  easy.
Qed.


Lemma biperm_of_compose_zxperm_l {n m o} (zxp : ZX n m) (zxb : ZX m o) : 
  ZXperm zxp -> ZXbiperm zxb ->
  perm_eq (n + o) (biperm_of_zx (zxp ⟷ zxb)) 
    (biperm_compose_perm_l m o (biperm_of_zx zxb) 
      (perm_of_zx zxp)).
Proof.
  intros Hp Hb.
  induction (zxperm_square zxp Hp).
  apply matrix_of_biperm_inj; [auto with biperm_db zxbiperm_db..|].
  apply matrix_of_biperm_mat_equiv_of_prop.
  rewrite matrix_of_biperm_of_zx by auto with zxbiperm_db.
  rewrite matrix_of_biperm_compose_perm_l_eq by auto with biperm_db.
  cbn.
  rewrite matrix_of_biperm_of_zx, <- perm_of_zx_permutation_semantics by easy.
  easy.
Qed.

































