Require Import Setoid.
Require Import CoreRules.
Import CoreData CoreAutomation.
Import CastRules.
From QuantumLib Require Import Bits.
Require Export QuantumLib.Permutations.
Import QuantumLib.VectorStates Modulus Kronecker.
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































