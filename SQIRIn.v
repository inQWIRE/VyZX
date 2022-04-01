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

Definition PaddedCnot {dim : nat} (control : nat) : ZX_Arb_Swaps dim dim :=
  Pad_Below dim (Pad_Above (S control) ZX_AS_CNOT).

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

Theorem equal_sem : forall dim (c : base_ucom dim) w, ZX_Arb_Swaps_Semantics (base_ucom_to_ZX c w) = uc_eval c.
Proof.
  intros dim c.
  unfold base_ucom_to_ZX.
  induction c; intros.
  - simpl.
    simpl in w.
    clear_eq_ctx.
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
