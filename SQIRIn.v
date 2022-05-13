Require Import externals.SQIR.SQIR.SQIR.
Require Import externals.SQIR.SQIR.UnitarySem.
Require Import externals.QuantumLib.Quantum.
Require Import Arith.
Require Import Reals.
Require Import Complex.
Require Export ZX.
Require Export Gates.
Require Export VyZX.Proportional.
Require Export Rules.
Require Import Matrix.
Require Import Setoid.
Require Import Quantum.
Require Import ZX_A_G_2.

Local Open Scope R_scope.

(* Arbitrary Swap Diagrams and Conversion to Base ZX Diagrams *)

(* A ZX diagram with arbitrary swaps to make circuit ingestion easier
   Constructions are mostly the same as a base ZX diagram, it has an
   arbitrary swap instead of a 2x2 swap *)
Inductive ZX_Arb_Swaps : nat -> nat -> Type := 
  | AS_Empty   : ZX_Arb_Swaps 0 0
  | ZX_AS_X_spider nIn nOut (α : R) : ZX_Arb_Swaps nIn nOut
  | ZX_AS_Z_spider nIn nOut (α : R) : ZX_Arb_Swaps nIn nOut
  | AS_Cap : ZX_Arb_Swaps 0 2
  | AS_Cup : ZX_Arb_Swaps 2 0
  | AS_Stack {nIn0 nIn1 nOut0 nOut1} (zx0 : ZX_Arb_Swaps nIn0 nOut0) (zx1 : ZX_Arb_Swaps nIn1 nOut1) :
      ZX_Arb_Swaps (nIn0 + nIn1) (nOut0 + nOut1)
  | AS_Compose {nIn nMid nOut} (zx0 : ZX_Arb_Swaps nIn nMid) (zx1 : ZX_Arb_Swaps nMid nOut) : ZX_Arb_Swaps nIn nOut
  | A_Swap (n : nat) : ZX_Arb_Swaps n n.
Local Close Scope R_scope.

(* Notations and useful definitions within arbitrary swap diagrams *)

Infix "⟷A" := AS_Compose (left associativity, at level 40).
Infix "↕A" := AS_Stack (left associativity, at level 40).

Definition ArbWire := ZX_AS_Z_spider 1 1 0.

Definition ZX_AS_Z : ZX_Arb_Swaps 1 1 := ZX_AS_Z_spider 1 1 PI.

Definition ZX_AS_X : ZX_Arb_Swaps 1 1 := ZX_AS_X_spider 1 1 PI.

Definition ZX_AS_Y : ZX_Arb_Swaps 1 1 := AS_Compose ZX_AS_Z ZX_AS_X.

Definition ZX_AS_CNOT : ZX_Arb_Swaps 2 2 := ZX_AS_Z_spider 1 2 0 ↕A ArbWire ⟷A (ArbWire ↕A ZX_AS_X_spider 2 1 0).

Definition ZX_AS_CNOT_flipped : ZX_Arb_Swaps 2 2 := ZX_AS_X_spider 1 2 0 ↕A ArbWire ⟷A (ArbWire ↕A ZX_AS_Z_spider 2 1 0).

Definition ZX_ucom_rot (x y z : R) : ZX_Arb_Swaps 1 1 := 
  ZX_AS_Y ⟷A ZX_AS_Z_spider 1 1 y ⟷A ZX_AS_Y ⟷A ZX_AS_X_spider 1 1 z ⟷A ZX_AS_Z_spider 1 1 x.

Reserved Notation "n ↑A zx" (at level 41).
Fixpoint nStack1 n (zx : ZX_Arb_Swaps 1 1) : ZX_Arb_Swaps n n :=
  match n with
  | 0 => AS_Empty
  | S n' => zx ↕A (n' ↑A zx)
  end
  where "n ↑A zx" := (nStack1 n zx).

Definition nArbWire := fun n => nStack1 n ArbWire.

Fixpoint ZX_A_1_1_pad {dim} : nat -> ZX_Arb_Swaps 1 1 -> ZX_Arb_Swaps dim dim :=
  fun n zx =>
    match dim with
    | 0   => AS_Empty
    | S k => match n with
             | 0 => zx ↕A (nArbWire k)
             | S m => ArbWire ↕A (@ZX_A_1_1_pad k m zx)
             end
    end.

(* Conversion  to base ZX diagrams *)

Fixpoint ZX_top_to_bottom_helper (n : nat) : ZX (S n) (S n) :=
  match n with 
  | 0   => Wire
  | S k => Compose (Stack Swap (nWire k)) (Stack Wire (ZX_top_to_bottom_helper k))
  end.

Definition ZX_top_to_bottom (n : nat) : ZX n n :=
  match n with
  | 0 => Empty
  | S k => ZX_top_to_bottom_helper k
  end.

Definition ZX_bottom_to_top (n : nat) : ZX n n :=
  (ZX_top_to_bottom n)⊺.

Definition A_Swap_ZX (n : nat) : ZX n n :=
  match n with
  | 0   => Empty
  | S k => ZX_top_to_bottom (S k)
    ⟷ eq_rect (k + 1)%nat (fun n0 : nat => ZX n0 n0) 
        (ZX_bottom_to_top k ↕ —) (S k) (Nat.add_1_r k)
  end.

Fixpoint ZX_Arb_to_ZX {nIn nOut : nat} (zxa : ZX_Arb_Swaps nIn nOut) : ZX nIn nOut :=
  match zxa with
  | AS_Empty           => Empty
  | ZX_AS_X_spider inp out a  => X_Spider inp out a
  | ZX_AS_Z_spider inp out a  => Z_Spider inp out a
  | AS_Cap             => Cap
  | AS_Cup             => Cup
  | AS_Stack zx1 zx2   => Stack (ZX_Arb_to_ZX zx1) (ZX_Arb_to_ZX zx2)
  | AS_Compose zx1 zx2 => Compose (ZX_Arb_to_ZX zx1) (ZX_Arb_to_ZX zx2)
  | A_Swap n           => A_Swap_ZX n
  end.

(* Arbitrary Swap Semantics *)

(* A linear mapping which takes | x y1 ... yn > -> | y1 .. yn x > *)
Fixpoint Top_wire_to_bottom (n : nat) : Square (2 ^ n) :=
  match n with
  | 0   => I 1
  | S k => match k with
           | 0   => I 2
           | S j => (@Mmult _ (2^n) _) ((I 2) ⊗ (Top_wire_to_bottom k)) (swap ⊗ (j ⨂ (I 2)))
           end
  end.

Definition Bottom_wire_to_top (n : nat) : Square (2 ^ n) :=
  (Top_wire_to_bottom n)⊤.

Definition A_Swap_semantics (n : nat) : Square (2 ^ n) :=
  match n with
  | 0   => I 1
  | S k => (@Mmult _ (2 ^ n) _ ((Bottom_wire_to_top k) ⊗ (I 2)) (Top_wire_to_bottom (S k)))
  end.

Fixpoint ZX_Arb_Swaps_Semantics {nIn nOut : nat} (zxa : ZX_Arb_Swaps nIn nOut) : Matrix (2 ^ nOut) (2 ^ nIn) :=
  match zxa with
  | AS_Empty           => I 1
  | ZX_AS_X_spider _ _ a      => X_semantics nIn nOut a
  | ZX_AS_Z_spider _ _ a      => Z_semantics nIn nOut a
  | AS_Cap             => ZX_semantics Cap
  | AS_Cup             => ZX_semantics Cup
  | AS_Stack zx0 zx1   => ZX_Arb_Swaps_Semantics zx0 ⊗ ZX_Arb_Swaps_Semantics zx1
  | AS_Compose zx0 zx1 => ZX_Arb_Swaps_Semantics zx1 × ZX_Arb_Swaps_Semantics zx0
  | A_Swap n           => A_Swap_semantics n
  end.

(* Well foundedness of semantics *)

Lemma WF_Top_to_bottom (n : nat) : WF_Matrix (Top_wire_to_bottom n).
Proof.
  destruct n; try auto with wf_db.
  induction n.
  - simpl; auto with wf_db.
  - simpl. try auto with wf_db.
Qed.

Global Hint Resolve WF_Top_to_bottom : wf_db.

Lemma WF_Bottom_to_top (n : nat) : WF_Matrix (Bottom_wire_to_top n).
Proof. unfold Bottom_wire_to_top. auto with wf_db. Qed.

Global Hint Resolve WF_Bottom_to_top : wf_db.

Lemma WF_A_Swap_semantics (n : nat) : WF_Matrix (A_Swap_semantics n).
Proof. destruct n; [ auto with wf_db | simpl; destruct n; auto with wf_db ]. Qed.

Global Hint Resolve WF_A_Swap_semantics : wf_db.

Lemma WF_ZX_Arb_Swap_Semantics : forall (nIn nOut : nat) (zxa : ZX_Arb_Swaps nIn nOut), WF_Matrix (ZX_Arb_Swaps_Semantics zxa).
Proof.
  intros.
  induction zxa; simpl; auto with wf_db;
    apply WF_list2D_to_matrix;
    try easy; (* case list of length 4 *)
    try intros; simpl in H; repeat destruct H; try discriminate; try (subst; easy). (* Case of 4 lists length 1 *)
Qed.

Global Hint Resolve WF_ZX_Arb_Swap_Semantics : wf_db.

(* Semantics for useful definitions and notations *)

Lemma nStack1A_n_kron : forall n (zx : ZX_Arb_Swaps 1 1), ZX_Arb_Swaps_Semantics (n ↑A zx) = n ⨂ ZX_Arb_Swaps_Semantics zx.
Proof.
  intros.
  induction n.
  - unfold nStack. reflexivity.
  - simpl.
    rewrite IHn.
    restore_dims.
    rewrite <- kron_n_assoc; auto.
    apply WF_ZX_Arb_Swap_Semantics.
Qed.

Lemma ArbWire_semantics : ZX_Arb_Swaps_Semantics (ArbWire) = I 2.
Proof.
  simpl.
  replace (Z_semantics 1 1 0) with (ZX_semantics Wire); [ | reflexivity ].
  apply wire_identity_semantics.
Qed.

Opaque ArbWire.


Lemma nArbWire_semantics : forall n, ZX_Arb_Swaps_Semantics (nArbWire n) = I (2 ^ n).
Proof.
  intros.
  simpl.
  induction n.
  - easy.
  - simpl.
    replace (2 ^ n + (2 ^ n + 0))%nat with (2 * 2 ^ n)%nat by lia.
    rewrite <- id_kron.
    rewrite <- IHn.
    rewrite ArbWire_semantics.
    easy.
Qed.

Lemma A_Swap_2_is_swap : A_Swap_semantics 2 = swap.
Proof.
  simpl.
  unfold Bottom_wire_to_top.
  simpl.
  rewrite id_transpose_eq.
  repeat rewrite kron_1_r.
  repeat rewrite id_kron.
  simpl.
  repeat rewrite Mmult_1_l.
  1: reflexivity.
  1-3: auto with wf_db.
Qed.

(* Proving correctness of conversion *)

Lemma Top_to_bottom_correct : forall n, ZX_semantics (ZX_top_to_bottom n) = Top_wire_to_bottom n.
Proof.
  intros.
  destruct n; [ reflexivity | ].
  destruct n; [ apply wire_identity_semantics | ].
  induction n.
  - simpl.
    rewrite wire_identity_semantics.
    Local Transparent nWire.
    unfold nWire.
    simpl.
    reflexivity.
  - simpl.
    simpl in IHn.
    rewrite <- IHn.
    rewrite wire_identity_semantics.
    rewrite nwire_identity_semantics.
    rewrite nStack1_n_kron.
    rewrite wire_identity_semantics.
    rewrite <- kron_n_assoc; [ | auto with wf_db ].
    reflexivity.
Qed.

Lemma Bottom_to_top_correct : forall n, ZX_semantics (ZX_bottom_to_top n) = Bottom_wire_to_top n.
Proof.
  intros.
  unfold ZX_bottom_to_top.
  unfold Bottom_wire_to_top.
  rewrite ZX_semantics_Transpose_comm.
  rewrite Top_to_bottom_correct.
  reflexivity.
Qed.

Opaque ZX_bottom_to_top.
Opaque ZX_top_to_bottom.

Lemma A_Swap_Correct : forall n, ZX_semantics (A_Swap_ZX n) = A_Swap_semantics n.
Proof.
  intros.
  unfold A_Swap_semantics.
  destruct n; [ reflexivity | ].
  destruct n.
  - simpl.
    rewrite <- eq_rect_eq.
    simpl.
    rewrite wire_identity_semantics.
    rewrite Bottom_to_top_correct.
    rewrite Top_to_bottom_correct.
    reflexivity.
  - rewrite <- Bottom_to_top_correct.
    rewrite <- Top_to_bottom_correct.
    simpl.
    elim_eq_rect.
    elim_eq_rect.
    rewrite <- eq_rect_eq.
    simpl.
    rewrite wire_identity_semantics.
    reflexivity.
Qed.

Lemma ZX_Arb_to_ZX_semantics {nIn nOut} : 
  forall (zxa : ZX_Arb_Swaps nIn nOut), 
    (ZX_Arb_Swaps_Semantics zxa) = (ZX_semantics (ZX_Arb_to_ZX zxa)).
Proof.
  induction zxa; try auto.
  1-2 : simpl; rewrite <- IHzxa1, IHzxa2; auto.
  symmetry.
  apply A_Swap_Correct.
Qed.


Definition Arb_Swaps_proportional {nIn nOut} (zx0 : ZX_Arb_Swaps nIn nOut) (zx1 : ZX_Arb_Swaps nIn nOut) :=
  proportional_general ZX_Arb_Swaps_Semantics zx0 zx1.

Infix "∝A" := Arb_Swaps_proportional (at level 70).

Lemma Arb_Swaps_proportional_refl : forall {nIn nOut} (zx : ZX_Arb_Swaps nIn nOut), zx ∝A zx.
Proof.
  intros.
  apply proportional_general_refl.
Qed.

Lemma Arb_Swaps_proportional_symm : forall {nIn nOut} (zx0 zx1 : ZX_Arb_Swaps nIn nOut),
  zx0 ∝A zx1 -> zx1 ∝A zx0.
Proof.
  intros.
  apply proportional_general_symm; assumption.
Qed.

Lemma Arb_Swaps_proportional_trans : forall {nIn nOut} (zx0 zx1 zx2 : ZX_Arb_Swaps nIn nOut),
  zx0 ∝A zx1 -> zx1 ∝A zx2 -> zx0 ∝A zx2.
Proof.
  intros.
  apply (proportional_general_trans _ _ _ ZX_Arb_Swaps_Semantics zx0 zx1 zx2); assumption.
Qed.

Add Parametric Relation (nIn nOut : nat) : (ZX_Arb_Swaps nIn nOut) (@Arb_Swaps_proportional nIn nOut)
  reflexivity proved by Arb_Swaps_proportional_refl
  symmetry proved by Arb_Swaps_proportional_symm
  transitivity proved by Arb_Swaps_proportional_trans
  as zx_Arb_Swaps_prop_equiv_rel.

Lemma Arb_Swaps_stack_compat :
  forall nIn0 nOut0 nIn1 nOut1,
    forall zx0 zx1 : ZX_Arb_Swaps nIn0 nOut0, zx0 ∝A zx1 ->
    forall zx2 zx3 : ZX_Arb_Swaps nIn1 nOut1, zx2 ∝A zx3 ->
    zx0 ↕A zx2 ∝A zx1 ↕A zx3.
Proof.
  intros.
  destruct H; destruct H; destruct H0; destruct H0.
  exists (x * x0).
  split.
  - simpl; rewrite H; rewrite H0.
    lma.
  - apply Cmult_neq_0; try assumption.
Qed.

Add Parametric Morphism (nIn0 nOut0 nIn1 nOut1 : nat) : (@AS_Stack nIn0 nIn1 nOut0 nOut1)
  with signature (@Arb_Swaps_proportional nIn0 nOut0) ==> (@Arb_Swaps_proportional nIn1 nOut1) ==> 
                 (@Arb_Swaps_proportional (nIn0 + nIn1) (nOut0 + nOut1)) as Arb_Swaps_stack_mor.
Proof. apply Arb_Swaps_stack_compat; assumption. Qed.

Lemma Arb_Swaps_compose_compat :
  forall nIn nMid nOut,
    forall zx0 zx1 : ZX_Arb_Swaps nIn  nMid, zx0 ∝A zx1 ->
    forall zx2 zx3 : ZX_Arb_Swaps nMid nOut, zx2 ∝A zx3 ->
    (AS_Compose zx0 zx2) ∝A (AS_Compose zx1 zx3).
Proof.
  intros.
  destruct H; destruct H; destruct H0; destruct H0.
  simpl.
  exists (x * x0).
  split.
  - simpl; rewrite H; rewrite H0.
    rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    restore_dims.
    rewrite Mscale_mult_dist_l.
    rewrite Mscale_assoc.
    reflexivity.
  - apply Cmult_neq_0; try assumption.
Qed.

Add Parametric Morphism (nIn nMid nOut : nat)  : (@AS_Compose nIn nMid nOut)
  with signature (@Arb_Swaps_proportional nIn nMid) ==> (@Arb_Swaps_proportional nMid nOut) ==> 
                 (@Arb_Swaps_proportional nIn nOut) as Arb_Swaps_compose_mor.
Proof. apply Arb_Swaps_compose_compat; assumption. Qed.

(* Injestion to ZX_Arb_Swaps *)

Lemma sub_add_b : forall (dim1 dim2 : nat), dim1 <=? dim2 = true -> ((dim2 - dim1 + dim1) = dim2)%nat.
Proof.
  intros.
  apply Nat.sub_add.
  apply leb_complete.
  apply H.
Qed.


Definition Pad_Above {dim1 : nat} (dim2 : nat) (zxa : ZX_Arb_Swaps dim1 dim1) : ZX_Arb_Swaps dim2 dim2.
Proof.
  specialize (le_dec dim1 dim2); intros.
  destruct H; [ | apply nArbWire ].
  rewrite <- (Nat.sub_add dim1 dim2); [ | exact l].
  apply AS_Stack; [ apply nArbWire | apply zxa ].
Defined.

Lemma Pad_Above_Sem : forall {dim1} dim2 (zxa : ZX_Arb_Swaps dim1 dim1), dim1 <= dim2 -> ZX_Arb_Swaps_Semantics (Pad_Above dim2 zxa) = ZX_Arb_Swaps_Semantics ((nArbWire (dim2 - dim1)) ↕A zxa).
Proof.
  intros.
  unfold Pad_Above.
  destruct (le_dec dim1 dim2); [ | congruence ].
  simplify_eqs.
  replace (dim2 - dim1 + dim1 - dim1)%nat with (dim2 - dim1)%nat by lia.
  easy.
Qed.

Definition Pad_Below {dim1 : nat} (dim2 : nat) (zxa : ZX_Arb_Swaps dim1 dim1) : ZX_Arb_Swaps dim2 dim2.
Proof.
  specialize (le_dec dim1 dim2); intros.
  destruct H; [ | apply nArbWire ].
  rewrite <- (Nat.sub_add dim1 dim2); [ | exact l].
  rewrite Nat.add_comm.
  - apply AS_Stack; [ apply zxa | apply nArbWire ].
Defined.

Lemma Pad_Below_Sem : forall {dim1} dim2 (zxa : ZX_Arb_Swaps dim1 dim1), dim1 <= dim2 -> ZX_Arb_Swaps_Semantics (Pad_Below dim2 zxa) = ZX_Arb_Swaps_Semantics (zxa ↕A (nArbWire (dim2 - dim1))).
Proof.
  intros.
  unfold Pad_Below.
  destruct (le_dec dim1 dim2); [ | congruence ].
  simplify_eqs.
  simpl_eq.
  replace (dim1 + (dim2 - dim1) - dim1)%nat with (dim2 - dim1)%nat by lia.
  easy.
Qed.

Definition ASwapfromto {dim : nat} (pos1 pos2 : nat) : ZX_Arb_Swaps dim dim :=
  if (pos1 <? pos2)
     then Pad_Below dim (Pad_Above pos2 (A_Swap (pos2 - pos1)))
     else Pad_Below dim (Pad_Above pos1 (A_Swap (pos1 - pos2))).

Lemma ASwapfromto_Sem_p1_le_p2 : forall {dim} pos1 pos2, pos1 < pos2 -> pos2 <= dim -> ZX_Arb_Swaps_Semantics (@ASwapfromto dim pos1 pos2) = ZX_Arb_Swaps_Semantics ((nArbWire (pos1) ↕A (A_Swap (pos2 - pos1)) ↕A nArbWire (dim - pos2))).
Proof.
  intros.
  unfold ASwapfromto.
  assert (pos1 <? pos2 = true) by (apply Nat.ltb_lt; assumption).
  rewrite H1.
  rewrite Pad_Below_Sem; [ | assumption ].
  simpl.
  rewrite Pad_Above_Sem; [ | apply Nat.le_sub_l ].
  simpl.
  replace (pos2 - (pos2 - pos1))%nat with pos1 by lia.
  reflexivity.
Qed.

Lemma ASwapfromto_Sem_p2_le_p1 : forall {dim} pos1 pos2, pos1 > pos2 -> pos1 <= dim -> ZX_Arb_Swaps_Semantics (@ASwapfromto dim pos1 pos2) = ZX_Arb_Swaps_Semantics ((nArbWire (pos2) ↕A (A_Swap (pos1 - pos2)) ↕A nArbWire (dim - pos1))).
Proof.
  intros.
  unfold ASwapfromto.
  assert (pos1 <? pos2 = false) by (apply Nat.ltb_ge; apply Nat.lt_le_incl; assumption).
  rewrite H1.
  rewrite Pad_Below_Sem; [ | assumption ].
  simpl.
  rewrite Pad_Above_Sem; [ | apply Nat.le_sub_l ].
  simpl.
  replace (pos1 - (pos1 - pos2))%nat with pos2 by lia.
  reflexivity.
Qed.

Definition PaddedCnot {dim : nat} (control : nat) : ZX_Arb_Swaps dim dim :=
  Pad_Below dim (Pad_Above (S control) ZX_AS_CNOT).

Lemma PaddedCnot_Sem : forall {dim} control, (control >= 1) -> (S control <= dim) -> ZX_Arb_Swaps_Semantics (@PaddedCnot dim control) = ZX_Arb_Swaps_Semantics ((nArbWire (pred control)) ↕A ZX_AS_CNOT ↕A (nArbWire (dim - S control))).
Proof.
  intros.
  unfold PaddedCnot.
  rewrite Pad_Below_Sem; [ | assumption ].
  simpl.
  rewrite Pad_Above_Sem; [ | apply le_n_S; assumption ].
  simpl.
  rewrite pred_of_minus.
  reflexivity.
Qed.

Definition CNOTInj {dim : nat} (pos1 pos2 : nat) : ZX_Arb_Swaps dim dim :=
  if (pos1 <? pos2)
     then ASwapfromto pos2 (S pos1) ⟷A PaddedCnot pos1 ⟷A ASwapfromto pos2 (S pos1)
     else ASwapfromto pos1 (S pos2) ⟷A ASwapfromto pos2 (S pos2) 
          ⟷A PaddedCnot pos2 ⟷A ASwapfromto pos2 (S pos2) 
          ⟷A ASwapfromto pos1 (S pos2).

Local Open Scope ucom.


Fixpoint base_ucom_to_ZX {dim} (c : base_ucom dim) : ZX_Arb_Swaps dim dim :=
match c with
| ucl ; ucr => base_ucom_to_ZX ucl ⟷A base_ucom_to_ZX ucr 
| uapp1 U1 n => match U1 with
                | U_R θ ϕ λ => ZX_A_1_1_pad n (ZX_ucom_rot θ ϕ λ)
                end
| uapp2 U2 n m => match U2 with
               | U_CNOT => CNOTInj n m
              end
| uapp3 U3 n m l => match U3 with
                 end
end.


Program Lemma ZX_AS_Stack_assoc : forall {nIn0 nOut0 nIn1 nOut1 nIn2 nOut2} (zx0 : ZX_Arb_Swaps nIn0 nOut0) (zx1 : ZX_Arb_Swaps nIn1 nOut1) (zx2 : ZX_Arb_Swaps nIn2 nOut2),
                          zx0 ↕A (zx1 ↕A zx2) ∝A zx0 ↕A zx1 ↕A zx2.
Proof.
  intros.
  prop_exist_non_zero (RtoC 1).  
  simpl_eqs.
  Msimpl.
  rewrite kron_assoc; auto with wf_db.
Qed.

Program Lemma ZX_AS_Stack_assoc' : forall {nIn0 nOut0 nIn1 nOut1 nIn2 nOut2} (zx0 : ZX_Arb_Swaps nIn0 nOut0) (zx1 : ZX_Arb_Swaps nIn1 nOut1) (zx2 : ZX_Arb_Swaps nIn2 nOut2),
                        zx0 ↕A zx1 ↕A zx2 ∝A zx0 ↕A (zx1 ↕A zx2).
Proof.
  intros.
  prop_exist_non_zero (RtoC 1).  
  simpl_eqs.
  Msimpl.
  rewrite kron_assoc; auto with wf_db.
Qed.

Lemma nArbWire_r : forall n, nArbWire (n + 1) ∝A (nArbWire n) ↕A ArbWire.
Proof.
  intros.
  induction n.
  - simpl.
    unfold nArbWire.
    simpl.
    prop_exist_non_zero (RtoC 1).
    simpl.
    Msimpl; auto with wf_db.
  - simpl.
    unfold nArbWire in *.
    simpl.
    rewrite IHn.
    rewrite ZX_AS_Stack_assoc.
    simpl_eqs.
    easy.
Qed.


Lemma ZX_A_1_1_pad_growth: forall dim zx n, n < dim -> @ZX_A_1_1_pad (dim + 1) n zx ∝A @ZX_A_1_1_pad dim n zx ↕A ArbWire.
Proof.
  intro dim.
  induction dim; intros.
  - simpl.
    exfalso.
    lia.
  - simpl.
    destruct n.
    + specialize (IHdim zx 0).
      rewrite nArbWire_r.
      rewrite (ZX_AS_Stack_assoc' zx _ _).
      simpl_eqs.
      easy.
    + rewrite IHdim; [ | lia ].
      rewrite (ZX_AS_Stack_assoc' ArbWire _ _).
      simpl_eqs.
      easy.
Qed.

Lemma rot_sem_base : forall a b c, ZX_Arb_Swaps_Semantics (ZX_ucom_rot a b c) = rotation a b c.
Admitted.

Lemma pad_1_1_sem_eq : forall {dim} n (zx : ZX_Arb_Swaps 1 1) A, WF_Matrix A -> ZX_Arb_Swaps_Semantics zx = A -> n < dim -> Pad.pad_u dim n A = ZX_Arb_Swaps_Semantics (@ZX_A_1_1_pad dim n zx).
Proof.
  intros.
  simpl.
  generalize dependent n.
  induction dim; intros.
  - exfalso.
    lia.
  - simpl.
    destruct n.
    Set Printing Implicit.
    + unfold Pad.pad_u, Pad.pad.
      assert (0 + 1 <=? S dim = true) by (apply leb_correct; lia).
      rewrite H2.
      Msimpl.
      simpl.
      rewrite nArbWire_semantics.
      replace (dim - 0)%nat with dim by lia.
      apply kron_simplify; [ | easy].
      easy.
    + simpl.
      rewrite <- IHdim; [ | lia ].
      unfold Pad.pad_u, Pad.pad.
      assert (S n + 1 <=? S dim = true) by (apply leb_correct; lia).
      assert (n + 1 <=? dim = true) by (apply leb_correct; lia).
      rewrite H2, H3.
      rewrite ArbWire_semantics.
      rewrite (kron_assoc (I (2 ^ n)) _ _); try auto with wf_db.
      restore_dims.
      rewrite <- (kron_assoc (I 2) _ _); try auto with wf_db.
      rewrite id_kron.
      replace (2 * 2 ^ n)%nat with (2 ^ (S n))%nat by reflexivity.
      rewrite <- kron_assoc; try auto with wf_db.
Qed.

Lemma rot_sem_eq : forall {dim} a b c n, n < dim -> @uc_eval dim (uapp1 (U_R a b c) n) = ZX_Arb_Swaps_Semantics (@ZX_A_1_1_pad dim n (ZX_ucom_rot a b c)).
Proof.
  intros.
  apply pad_1_1_sem_eq; try auto with wf_db.
  apply rot_sem_base.
Qed.

Theorem equal_sem : forall dim (c : base_ucom dim), uc_well_typed c -> ZX_Arb_Swaps_Semantics (base_ucom_to_ZX c) = uc_eval c.
Proof.
  intros dim c.
  induction c; intros.
  - simpl.
    inversion H.
    rewrite IHc1, IHc2; [ | assumption | assumption ].
    easy.
  - simpl.
    inversion H.
    subst.
Abort.

 

Local Open Scope R_scope.

Lemma increase_Z {α} {nIn nOut} : Z_Spider nIn nOut α ∝ Z_Spider nIn nOut (α + (2 * PI)).
Proof.
  prop_exist_non_zero 1.
  rewrite Mscale_1_l.
  simpl.
  unfold_spider.
  rewrite Cexp_add.
  rewrite Cexp_2PI.
  rewrite Cmult_1_r.
  reflexivity.
Qed.

Lemma reduce_Z {α} {nIn nOut} : Z_Spider nIn nOut α ∝ Z_Spider nIn nOut (α - (2 * PI)).
Proof.
  prop_exist_non_zero 1.
  rewrite Mscale_1_l.
  simpl.
  unfold_spider.
  rewrite Rminus_unfold.
  rewrite Cexp_add.
  rewrite Cexp_neg.
  rewrite Cexp_2PI.
  rewrite <- (Cmult_1_l (/C1)).
  rewrite Cinv_r; try nonzero.
  rewrite Cmult_1_r.
  reflexivity.
Qed.

Lemma increase_X {α} {nIn nOut} : X_Spider nIn nOut α ∝ X_Spider nIn nOut (α + (2 * PI)).
Proof. swap_colors_of (@increase_Z α). Qed.

Lemma reduce_X {α} : X_Spider 1 1 α ∝ X_Spider 1 1 (α - (2 * PI)).
Proof. swap_colors_of (@reduce_Z α). Qed.

Theorem ingestion_equiv forall {dim} (u : base_ucom dim), exists c, uc_eval u = c .* ZX_Arb_Swaps_Semantics (ZX) 

Local Close Scope ucom.
Local Close Scope R_scope.
