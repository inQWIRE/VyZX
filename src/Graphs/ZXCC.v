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
Import Setoid.
Require Export CoreRules.



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

(* FIXME: Move *)
Lemma perm_of_zx_comm n m : 
  perm_of_zx (zx_comm n m) = big_swap_perm m n.
Proof.
  apply perm_of_zx_of_perm_cast_eq_WF; auto_perm.
Qed.

#[export] Hint Rewrite perm_of_zx_comm : perm_of_zx_cleanup_db.

Lemma zx_comm_0_l n : zx_comm 0 n ∝
  cast _ _ eq_refl (Nat.add_0_r n) (n_wire n).
Proof.
  by_perm_eq_nosimpl.
  rewrite perm_of_zx_cast, perm_of_n_wire.
  rewrite perm_of_zx_comm.
  now rewrite big_swap_perm_0_r.
Qed.

Lemma zx_comm_0_r n : zx_comm n 0 ∝
  cast _ _ (Nat.add_0_r n) eq_refl (n_wire n).
Proof.
  by_perm_eq_nosimpl.
  rewrite perm_of_zx_cast, perm_of_n_wire.
  rewrite perm_of_zx_comm.
  now rewrite big_swap_perm_0_l.
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

(* FIXME: Move *)
Lemma compose_box_r {n} (zx0 zx1 : ZX n 1) : 
  zx0 ⟷ □ ∝ zx1 <-> zx0 ∝ zx1 ⟷ □.
Proof.
  split; [intros <- | intros ->]; 
  now rewrite compose_assoc, box_compose, 
    wire_removal_r.
Qed.

Lemma compose_box_l {n} (zx0 zx1 : ZX 1 n) : 
  □ ⟷ zx0 ∝ zx1 <-> zx0 ∝ □ ⟷ zx1.
Proof.
  split; [intros <- | intros ->]; 
  now rewrite <- compose_assoc, box_compose, 
    wire_removal_l.
Qed.

Lemma colorswap_is_bihadamard_1_1 (zx : ZX 1 1) : 
  ⊙ zx ∝ □ ⟷ zx ⟷ □.
Proof.
  rewrite colorswap_is_bihadamard.
  cbn. 
  clean_eqns rewrite stack_empty_r, cast_id.
  now rewrite compose_assoc.
Qed.

Lemma box_decomp_ZXZ : Box ∝
  Z 1 1 (PI / 2) ⟷ X 1 1 (PI / 2) ⟷ Z 1 1 (PI / 2).
Proof.
  rewrite <- wire_removal_r, compose_box_l.
  change (X 1 1 (PI / 2)) with (⊙ (Z 1 1 (PI / 2))).
  rewrite colorswap_is_bihadamard_1_1.
  let zx := constr:(□ ⟷ Z 1 1 (PI / 2)) in
  transitivity (zx ⟷ zx ⟷ zx); [| now rewrite !compose_assoc].
  prop_exists_nonzero (Cexp (- (PI / 4))).
  rewrite Cexp_neg, <- Mscale_inv by nonzero.
  let zx := constr:(□ ⟷ Z 1 1 (PI / 2)) in
  change (Cexp (PI / 4) .* I 2 = ⟦ zx ⟧ × ⟦ zx ⟧ × ⟦ zx ⟧).
  let zx := constr:(□ ⟷ Z 1 1 (PI / 2)) in
  compute_matrix (⟦ zx ⟧).
  prep_matrix_equivalence.
  rewrite Cexp_PI2, Cexp_PI4, make_WF_equiv.
  unfold scale.
  by_cell; cbn; C_field; lca.
Qed.

Lemma box_decomp_XZX : Box ∝
  X 1 1 (PI / 2) ⟷ Z 1 1 (PI / 2) ⟷ X 1 1 (PI / 2).
Proof. colorswap_of (box_decomp_ZXZ). Qed.

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



Definition WF_ZXdecomp {n m} (zx : ZXdecomp n m) : Prop :=
  ZXstack (zx.(spiders)) /\ ZXbiperm (zx.(iobiperm)).

Create HintDb wf_zx_db discriminated.
#[export] Hint Extern 100 (ZXbiperm _) => 
  solve [auto with zxbiperm_db | auto with zxbiperm_db zxperm_db] 
  : wf_zx_db.
Hint Constructors ZXstack : wf_zx_db.
Hint Resolve ZXstack_cast : wf_zx_db.
Hint Extern 100 (WF_ZXdecomp _) => split : wf_zx_db.
Hint Extern 0 (ZXstack (?zx0 ↕ ?zx1)) =>
  apply (ZXstack_stack zx0 zx1) : wf_zx_db.

Lemma WF_ZXdecomp_ZXstack {n m} (zx : ZXdecomp n m) : 
  WF_ZXdecomp zx -> ZXstack (zx.(spiders)).
Proof. now unfold WF_ZXdecomp. Qed.

Lemma WF_ZXdecomp_ZXbiperm {n m} (zx : ZXdecomp n m) : 
  WF_ZXdecomp zx -> ZXbiperm (zx.(iobiperm)).
Proof. now unfold WF_ZXdecomp. Qed.

#[export] Hint Resolve WF_ZXdecomp_ZXstack WF_ZXdecomp_ZXbiperm : wf_zx_db. 

Lemma WF_ZXdecomp_biperm {n m} (zx : ZX n m) (Hzx : ZXbiperm zx) :  
  WF_ZXdecomp (ZXdecomp_biperm zx).
Proof.
  auto with wf_zx_db.
Qed.

#[export] Hint Resolve WF_ZXdecomp_biperm : wf_zx_db.

Lemma WF_ZXdecomp_stack {n0 m0 n1 m1} (zx0 : ZXdecomp n0 m0)
  (zx1 : ZXdecomp n1 m1) : WF_ZXdecomp zx0 -> WF_ZXdecomp zx1 ->
  WF_ZXdecomp (ZXdecomp_stack zx0 zx1).
Proof.
  intros Hzx0 Hzx1.
  split; cbn; [auto with wf_zx_db|].
  auto with wf_zx_db zxbiperm_db.
Qed.

#[export] Hint Resolve WF_ZXdecomp_stack : wf_zx_db.

Lemma WF_ZXdecomp_compose {n m o} (zx0 : ZXdecomp n m)
  (zx1 : ZXdecomp m o) : WF_ZXdecomp zx0 -> WF_ZXdecomp zx1 ->
  WF_ZXdecomp (ZXdecomp_compose zx0 zx1).
Proof.
  intros Hzx0 Hzx1.
  split; cbn; [auto with wf_zx_db|].
  auto with wf_zx_db zxbiperm_db.
Qed.

#[export] Hint Resolve WF_ZXdecomp_compose : wf_zx_db.

Lemma WF_ZXdecomp_Z n m α : WF_ZXdecomp (ZXdecomp_Z n m α).
Proof. split; cbn; auto with wf_zx_db. Qed.

Lemma WF_ZXdecomp_X n m α : WF_ZXdecomp (ZXdecomp_X n m α).
Proof. split; cbn; auto with wf_zx_db. Qed.

Lemma WF_ZXdecomp_box : WF_ZXdecomp (ZXdecomp_box).
Proof. split; cbn; auto with wf_zx_db. Qed.

#[export] Hint Resolve WF_ZXdecomp_Z WF_ZXdecomp_X 
  WF_ZXdecomp_box : wf_zx_db.

Lemma WF_ZXdecomp_of_ZX {n m} (zx : ZX n m) : WF_ZXdecomp (ZXdecomp_of_ZX zx).
Proof. induction zx; cbn [ZXdecomp_of_ZX]; auto with wf_zx_db. Qed.

Lemma WF_ZXdecomp_of_ZX_alt {n m} (zx : ZX n m) : 
  WF_ZXdecomp (ZXdecomp_of_ZX_alt zx).
Proof. 
  induction zx;
  [apply WF_ZXdecomp_biperm; constructor.. | | | | |];
  [cbn; auto with wf_zx_db.. | |];
  cbn [ZXdecomp_of_ZX_alt].
  - destruct (is_ZXbiperm (zx1 ↕ zx2)) eqn:e;
    auto using is_ZXbiperm_ZXbiperm with wf_zx_db.
  - destruct (is_ZXbiperm (zx1 ⟷ zx2)) eqn:e;
    auto using is_ZXbiperm_ZXbiperm with wf_zx_db.
Qed.

#[export] Hint Resolve WF_ZXdecomp_of_ZX WF_ZXdecomp_of_ZX_alt : wf_zx_db.




















(* The subset of ZX diagrams forming the CCC structure
  (or, ZX-Cap/Cup) *)
  Inductive ZXCC : forall n m : nat, Set :=
  | CCEmpty : ZXCC 0 0
  | CCWire : ZXCC 1 1 
  | CCSwap : ZXCC 2 2
  | CCCap : ZXCC 2 0
  | CCCup : ZXCC 0 2
  | CCCompose {n m o} (zxc0 : ZXCC n m) (zxc1 : ZXCC m o) : ZXCC n o
  | CCStack {n0 m0 n1 m1} 
    (zxc0 : ZXCC n0 m0) (zxc1 : ZXCC n1 m1) : ZXCC (n0 + n1) (m0 + m1).

Fixpoint ZXCC_to_ZX {n m} (zxc : ZXCC n m) : ZX n m :=
  match zxc with
  | CCEmpty => Empty
  | CCWire => Wire
  | CCSwap => Swap
  | CCCap => Cap
  | CCCup => Cup
  | CCCompose zxc0 zxc1 => ZXCC_to_ZX zxc0 ⟷ ZXCC_to_ZX zxc1
  | CCStack zxc0 zxc1 => ZXCC_to_ZX zxc0 ↕ ZXCC_to_ZX zxc1
  end.

Coercion ZXCC_to_ZX : ZXCC >-> ZX.

Lemma ZXCC_biperm {n m} (zxc : ZXCC n m) : ZXbiperm zxc.
Proof.
  induction zxc; cbn; auto with zxbiperm_db.
Defined.
Opaque ZXCC_biperm.

Lemma ZXCC_biperm_t {n m} (zxc : ZXCC n m) : ZXbiperm_t zxc.
Proof.
  induction zxc; cbn; now constructor. 
Defined.

Fixpoint ZXCC_of_ZXbiperm_t {n m} (zx : ZX n m) (Hzx : ZXbiperm_t zx) 
  : ZXCC n m := 
  match Hzx with
  | BipermEmpty_t => CCEmpty
  | BipermWire_t => CCWire
  | BipermSwap_t => CCSwap
  | BipermCap_t => CCCap
  | BipermCup_t => CCCup
  | BipermStack_t zx0 zx1 Hzx0 Hzx1 => CCStack
    (ZXCC_of_ZXbiperm_t zx0 Hzx0) (ZXCC_of_ZXbiperm_t zx1 Hzx1)
  | BipermComp_t zx0 zx1 Hzx0 Hzx1 => CCCompose
    (ZXCC_of_ZXbiperm_t zx0 Hzx0) (ZXCC_of_ZXbiperm_t zx1 Hzx1)
  end.


Definition ZXCC_of_ZXbiperm {n m} (zx : ZX n m) (Hzx : ZXbiperm zx) 
  : ZXCC n m := ZXCC_of_ZXbiperm_t zx (ZXbiperm_t_of_ZXbiperm zx Hzx).

Lemma ZX_of_ZXCC_of_ZXbiperm {n m} (zx : ZX n m) (Hzx : ZXbiperm zx) :
  zx = ZXCC_of_ZXbiperm zx Hzx.
Proof.
  unfold ZXCC_of_ZXbiperm.
  generalize (ZXbiperm_t_of_ZXbiperm zx Hzx).
  clear Hzx.
  intros Hzx.
  induction Hzx; cbn; now f_equal.
Qed.

Lemma ZXCC_of_ZXbiperm_t_of_ZXCC {n m} (zxc : ZXCC n m) : 
  zxc = ZXCC_of_ZXbiperm_t zxc (ZXCC_biperm_t zxc).
Proof.
  induction zxc; cbn; now f_equal.
Qed.


(* Spider stack diagrams *)
Inductive ZXSS : forall (n : nat), Set :=
  | SSX_Spider n (α : R) : ZXSS n
  | SSZ_Spider n (α : R) : ZXSS n
  | SSStack {n m} (zxs0 : ZXSS n) (zxs1 : ZXSS m) : ZXSS (n + m).

Fixpoint ZXSS_to_ZX {n} (zxs : ZXSS n) : ZX 0 n :=
  match zxs with 
  | SSX_Spider n α => X 0 n α
  | SSZ_Spider n α => Z 0 n α
  | SSStack zxs0 zxs1 => ZXSS_to_ZX zxs0 ↕ ZXSS_to_ZX zxs1
  end.

Coercion ZXSS_to_ZX : ZXSS >-> ZX.



Inductive ZXSSCC : forall (n m : nat), Set :=
  | ZX_SS_CC {n m k} (zxs : ZXSS k) (zxc : ZXCC (k + n) m) : ZXSSCC n m.

Definition ZX_of_ZXSSCC {n m} (zxsc : ZXSSCC n m) : ZX n m :=
  match zxsc in ZXSSCC n' m' return ZX n' m' with
  | @ZX_SS_CC n m k zxs zxc =>
    zxs ↕ n_wire n ⟷ zxc
  end.

Coercion ZX_of_ZXSSCC : ZXSSCC >-> ZX.

(* Definition ZXSSCC_Compose {n m o} 
  (zxsc0 : ZXSSCC n m) (zxsc1 : ZXSSCC m o) : ZXSSCC n o.
Proof.
  destruct zxsc0 as [n m k zxs0 zxc0].
  destruct zxsc1 as [m o l zxs1 zxc1].
  apply (ZX_SS_CC (SSStack zxs0 zxs1)). *)



