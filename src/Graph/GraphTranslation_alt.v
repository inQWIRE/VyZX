Require Import CoreData.CoreData.
Require Import Ingest.SQIRIngest.
Require Import CoreRules.CoreRules.
From Coq Require Import Lists.List.
From Coq Require Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.Compare_dec.
Import ListNotations.
Require Import Lia.

Require Import Recdef.

Require PermutationAutomation PermutationDefinitions
  PermutationFacts PermutationInstances PermutationRules
  ZXperm ZXpermFacts ZXpermSemantics.

Module PermToZX.

Local Open Scope nat_scope.

Lemma NoDup_app_l {A} (l l' : list A) : NoDup (l ++ l') -> NoDup l.
Proof.
  induction l as [|a l IHl]; [constructor|].
  simpl.
  rewrite 2!NoDup_cons_iff, in_app_iff.
  intros []; split; [|apply IHl]; auto.
Qed.

Lemma NoDup_app_r {A} (l l' : list A) : NoDup (l ++ l') -> NoDup l'.
Proof.
  induction l' as [|a l' IHl']; [constructor|].
  simpl.
  intros H; apply NoDup_remove in H.
  rewrite in_app_iff in H; destruct H.
  apply NoDup_cons; auto.
Qed.



Fixpoint index_of {A} (test : A -> bool) (l : list A) : nat :=
  match l with
  | [] => 0
  | x :: ls => if test x then 0 else S (index_of test ls)
  end.

Lemma nth_index_of {A} (test : A -> bool) (a : A) (Ha : test a = true) :
  forall (l : list A), 
  test (nth (index_of test l) l a) = true.
Proof.
  intros l.
  induction l as [|x ls IHls]; [easy|].
  simpl.
  destruct (test x) eqn:e; easy.
Qed.

Fixpoint index_of_err {A} (test : A -> bool) (l : list A) : option nat :=
  match l with
  | [] => None
  | x :: ls => if test x then Some 0 else 
      option_map S (index_of_err test ls)
  end.

Definition index_of_default {A} (test : A -> bool) (l : list A) (d : nat) : nat :=
  maybe (index_of_err test l) d.

Arguments index_of_default {_} _ !l _ /.

Lemma maybe_option_map {A B} (f : A -> B) (a : option A) (d : A) :
  maybe (option_map f a) (f d) = f (maybe a d).
Proof.
  destruct a; easy.
Qed.

Lemma index_of_eq_index_of_default_length {A} (test : A -> bool) (l : list A) : 
  index_of test l = index_of_default test l (length l).
Proof.
  induction l.
  - easy.
  - simpl.
    rewrite (if_dist _ _ _ maybe).
    destruct (test a); [easy|].
    rewrite IHl, maybe_option_map.
    easy.
Qed.


    

Fixpoint fin_index_of_err {A} (test : A -> bool) (l : list A) 
  : option (Fin.t (length l)) :=
  match l with
  | [] => None
  | x :: ls => 
    if test x 
    then Some Fin.F1 
    else option_map Fin.FS (fin_index_of_err test ls)
  end.

Definition perm_of_list (l : list nat) : nat -> nat :=
  fun k => nth k l k.

Definition invperm_of_list (l : list nat) : nat -> nat :=
  fun k => index_of_default (eqb k) l k.

Definition dec_gt (n : nat) (l : list nat) : list nat := 
  map (fun x => if n <? x then pred x else x) l.

Definition inc_ge (n : nat) (l : list nat) :=
  map (fun x => if n <=? x then S x else x) l.

Function is_perm_list (l : list nat) {measure length l} : bool :=
  match l with
  | [] => true
  | 0 :: [] => true
  | S _ :: [] => false
  | k :: ls => (k <=? length ls) 
    && (forallb (fun a => negb (a =? k)) ls) && is_perm_list (dec_gt k ls)
  end.
Proof.
  all: intros; simpl;
    unfold dec_gt;
    rewrite map_length;
    constructor.
Qed.

Lemma length_dec_gt (n : nat) (l : list nat) :
  length (dec_gt n l) = length l.
Proof. apply map_length. Qed.
  
Lemma length_inc_ge (n : nat) (l : list nat) :
  length (inc_ge n l) = length l.
Proof. apply map_length. Qed.

Lemma dec_gt_inc_ge (n : nat) (l : list nat) :
  dec_gt n (inc_ge n l) = l.
Proof.
  induction l; [easy|].
  simpl.
  rewrite IHl; f_equal.
  bdestruct_all; easy.
Qed.

Lemma notIn_inc_ge (n : nat) (l : list nat) :
  ~ In n (inc_ge n l).
Proof.
  induction l; [easy|].
  simpl.
  intros [Heq | Hin]; [|auto].
  revert Heq.
  bdestruct_all; lia.
Qed.

Lemma NoDup_inc_ge (n : nat) (l : list nat) (H : NoDup l) : NoDup (inc_ge n l).
Proof.
  apply FinFun.Injective_map_NoDup; [|easy].
  intros a b.
  bdestruct_all; lia.
Qed.

Inductive IsPermList : list nat -> Prop :=
  | IsPermNil : IsPermList []
  | IsPermCons (n : nat) (l : list nat) (H : IsPermList l) (Hn : n <= length l) : 
      IsPermList (n :: (inc_ge n l)).

Lemma NoDup_of_IsPermList (l : list nat) (H : IsPermList l) : NoDup l.
Proof.
  induction H; [constructor|].
  constructor.
  - apply notIn_inc_ge.
  - apply NoDup_inc_ge; easy.
Qed.

Lemma inc_ge_dec_gt_notIn (n : nat) (l : list nat) (H : ~ In n l) :
  inc_ge n (dec_gt n l) = l.
Proof.
  induction l; [easy|].
  - simpl in *.
    rewrite IHl; [|auto]; f_equal.
    bdestruct_all; lia.
Qed.

Lemma is_perm_list_dec_gt_of_is_perm_list (n : nat) (l : list nat) : 
  is_perm_list (n :: l) = true -> is_perm_list (dec_gt n l) = true.
Proof.
  rewrite is_perm_list_equation.
  destruct n, l; rewrite 2?andb_true_iff; try easy.
  rewrite is_perm_list_equation; easy.
Qed.

Lemma le_length_of_is_perm_list (n : nat) (l : list nat) : 
  is_perm_list (n :: l) = true -> n <= length l.
Proof.
  rewrite is_perm_list_equation.
  destruct n, l; try easy; bdestruct_all; lia.
Qed.

Lemma is_perm_list_consEb (n : nat) (l : list nat) : 
  is_perm_list (n :: l) = 
  (n <=? length l) && (forallb (fun a=>negb(a=?n)) l)
    && (is_perm_list (dec_gt n l)).
Proof.
  rewrite is_perm_list_equation.
  destruct n, l; try easy + constructor.
  simpl.
  rewrite is_perm_list_equation.
  easy.
Qed.

Lemma notIn_of_forall_neqb (n : nat) (l : list nat) : 
  forallb (fun a => ¬ a =? n) l = true -> ~ In n l.
Proof.
  intros H.
  induction l; [easy|].
  simpl in *.
  rewrite andb_true_iff in H.
  intros [Hf | Hin].
  - bdestruct (a =? n); lia.
  - apply IHl; easy.
Qed.

Lemma forall_neqb_of_notIn (n : nat) (l : list nat) : 
  ~ In n l -> forallb (fun a => ¬ a =? n) l = true.
Proof.
  intros H.
  induction l; [easy|].
  simpl in *.
  apply andb_true_iff; split.
  - bdestruct_all; lia.
  - apply IHl; auto.
Qed.

Lemma forall_neqb_iff_notIn (n : nat) (l : list nat) : 
  forallb (fun a => ¬ a =? n) l = true <-> ~ In n l.
Proof.
  split.
  - apply notIn_of_forall_neqb.
  - apply forall_neqb_of_notIn.
Qed.

Lemma is_perm_list_cons_iff (n : nat) (l : list nat) : 
  is_perm_list (n :: l) = true <-> 
    n <= length l /\ ~ In n l /\ is_perm_list (dec_gt n l) = true.
Proof.
  rewrite is_perm_list_consEb, 2!andb_true_iff.
  rewrite Nat.leb_le.
  rewrite forall_neqb_iff_notIn.
  apply and_assoc.
Qed.



Lemma forall_neqb_inc_ge (n : nat) (l : list nat) : 
  forallb (fun a => ¬ a =? n) (inc_ge n l) = true.
Proof.
  induction l; simpl; rewrite ?IHl; bdestruct_all; easy.
Qed.

Lemma is_perm_list_ind' (P : forall l : list nat, Prop)
  (base : P [])
  (rec : forall a l, a <= length l -> is_perm_list (dec_gt a l) = true ->
    ~ In a l -> P (dec_gt a l) -> P (a :: l)) : 
    forall l, is_perm_list l = true -> P l.
Proof.
  intros l.
  remember (length l) as k.
  revert l Heqk.
  induction k.
  - destruct l; easy.
  - destruct l as [|n l]; [easy|].
    simpl.
    intros H; injection H; clear H; intros H.
    rewrite is_perm_list_consEb.
    bdestruct_all; easy + simpl.
    rewrite andb_true_iff.
    intros [Hnotin Hperm].
    apply rec; auto.
    apply notIn_of_forall_neqb; easy.
    apply IHk; auto.
    rewrite length_dec_gt; easy.
Qed.

Lemma NoDup_of_has_ltn (l : list nat) (H : forall k, k < length l -> In k l) :
  NoDup l.
Proof.
  apply NoDup_incl_NoDup with (seq 0 (length l)).
  - apply seq_NoDup.
  - rewrite seq_length; easy.
  - intros a.
    rewrite in_seq.
    intros; apply H; lia.
Qed.

Lemma has_ltn_of_is_perm_list (l : list nat) (H: is_perm_list l = true) : 
  forall k, k < length l -> In k l.
Proof.
  pattern l.
  apply is_perm_list_ind'; try easy.
  clear l H.
  intros a l Hlen Hisperm Hnotin Hind.
  rewrite length_dec_gt in Hind.
  simpl.
  intros k H.
  bdestruct (a =? k); [left; easy|right].
  bdestruct (a <? k).
  - pose proof (Hind (pred k) ltac:(lia)) as Hin.
    apply in_map_iff in Hin.
    destruct Hin as [k' [Hk'eq Hin]].
    enough (k = k') by (subst; easy).
    revert Hk'eq.
    bdestruct (a <? k'); [lia|].
    intros; subst.
    replace (pred k) with a in * by lia.
    easy.
  - pose proof (Hind k ltac:(lia)) as Hin.
    apply in_map_iff in Hin.
    destruct Hin as [k' [Heq Hin]].
    revert Heq. 
    bdestruct_all; try lia.
    intros; subst; easy.
Qed.

Lemma NoDup_of_is_perm_list (l : list nat) :
  is_perm_list l = true -> NoDup l.
Proof.
  intros.
  apply NoDup_of_has_ltn, has_ltn_of_is_perm_list, H.
Qed.

Lemma is_perm_listP (l : list nat) : reflect (IsPermList l) (is_perm_list l).
Proof.
  apply iff_reflect; split.
  - intros H.
    induction H.
    + rewrite is_perm_list_equation. easy. 
    + rewrite is_perm_list_equation.
      rewrite dec_gt_inc_ge.
      rewrite length_inc_ge.
      rewrite IHIsPermList.
      bdestruct_all.
      rewrite forall_neqb_inc_ge.
      destruct n, l; easy.
  - remember (length l) as k.
    revert l Heqk.
    induction k.
    + intros []; easy || intros; constructor.
    + intros [|n l]; [easy|].
      simpl.
      intros Hlen Hperm.
      rewrite <- (inc_ge_dec_gt_notIn n l).
      * constructor.
        apply IHk.
        --rewrite length_dec_gt; lia.
        --apply is_perm_list_dec_gt_of_is_perm_list; easy. 
        --rewrite length_dec_gt.
          apply le_length_of_is_perm_list; easy.
      * rewrite is_perm_list_cons_iff in Hperm.
        apply Hperm.
Qed.

Lemma seq_Permutation_of_is_perm_list (l : list nat) : 
  is_perm_list l = true -> Permutation (seq 0 (length l)) l.
Proof.
  intros Hperm.
  apply NoDup_Permutation_bis.
  - apply seq_NoDup. 
  - now rewrite seq_length.
  - intros a; rewrite in_seq.
    intros H.
    apply has_ltn_of_is_perm_list; easy + lia.
Qed.

Local Open Scope program_scope.

Lemma index_of_err_nth (l : list nat) (Hl : NoDup l) 
  (k d: nat) (Hk : k < length l) :
  index_of_err (eqb (nth k l d)) l = Some k.
Proof.
  revert k d Hk;
  induction l; [easy|];
  intros k d Hk.
  simpl in *.
  inversion Hl; subst.
  destruct k.
  - now rewrite Nat.eqb_refl.
  - rewrite IHl by (auto + lia).
    bdestruct_all; [|easy].
    enough (In a l) by contradiction.
    replace <- a.
    apply nth_In.
    lia.
Qed.

Lemma index_of_default_nth (l : list nat) (Hl : NoDup l) 
  (k a : nat) (Hk : k < length l) : 
  index_of_default (eqb (nth k l a)) l (nth k l a) = k.
Proof.
  unfold index_of_default.
  rewrite index_of_err_nth by auto.
  easy.
Qed.  

Lemma invperm_of_list_linv (l : list nat) (H : is_perm_list l = true) :
  forall k, k < length l -> invperm_of_list l (perm_of_list l k) = k.
Proof.
  intros k Hk.
  unfold perm_of_list, invperm_of_list.
  apply index_of_default_nth; auto.
  now apply NoDup_of_is_perm_list.
Qed.

Lemma invperm_of_list_rinv (l : list nat) (H : is_perm_list l = true) :
  forall k, k < length l -> perm_of_list l (invperm_of_list l k) = k.
Proof.
  intros k Hk.
  unfold perm_of_list, invperm_of_list.
  pose proof (has_ltn_of_is_perm_list l H k Hk) as Hin.
  destruct (In_nth _ _ k Hin) as [n [Hnlt Hnthn]].
  rewrite <- Hnthn.
  rewrite index_of_default_nth; (now apply NoDup_of_is_perm_list) + auto.
  apply nth_indep; easy.
Qed.

Lemma perm_of_list_bdd (l : list nat) (H : is_perm_list l = true) : 
  forall k, k < length l -> perm_of_list l k < length l.
Proof.
  intros k Hk.
  unfold perm_of_list.
  assert (In (nth k l k) l) by
    (apply nth_In; easy).
  generalize dependent (nth k l k).
  intros a.
  rewrite <- (Permutation_in' eq_refl (seq_Permutation_of_is_perm_list l H)).
  rewrite in_seq.
  easy.
Qed.

Lemma index_of_err_aux {A} (test : A -> bool) (l : list A) :
  match (index_of_err test l) with
  | Some a => a < length l
  | None => True
  end.
Proof.
  induction l; [easy|].
  simpl.
  destruct (test a); [lia|].
  destruct (index_of_err test l) as [b |].
  simpl; lia.
  easy.
Qed.

Lemma index_of_default_lt_length {A} (test : A -> bool) (l : list A) 
  (d : nat) (Hd : d < length l) : 
  index_of_default test l d < length l.
Proof.
  unfold index_of_default.
  pose proof (index_of_err_aux test l) as H.
  destruct (index_of_err test l); easy.
Qed.

Lemma invperm_of_list_bdd (l : list nat) (H : is_perm_list l = true) : 
  forall k, k < length l -> invperm_of_list l k < length l.
Proof.
  intros k Hk.
  unfold invperm_of_list.
  apply index_of_default_lt_length.
  easy.
Qed.

Lemma perm_of_list_permutation_of_is_perm_list 
  (l : list nat) (H : is_perm_list l = true) : 
  permutation (length l) (perm_of_list l).
Proof.
  exists (invperm_of_list l).
  intros k Hk.
  repeat split.
  - now apply perm_of_list_bdd.
  - now apply invperm_of_list_bdd.
  - now apply invperm_of_list_linv.
  - now apply invperm_of_list_rinv.
Qed.

Definition list_of_perm (n : nat) (f : nat -> nat) : list nat :=
  map f (seq 0 n).

Lemma perm_of_list_cons (a : nat) (l : list nat) 
  (k : nat) (Hk : k < length l) :
  perm_of_list (a :: l) (S k) = perm_of_list l k.
Proof.
  unfold perm_of_list.
  simpl.
  now apply nth_indep.
Qed.

Lemma map_perm_of_list_seq_cons (a : nat) (l : list nat) :
  map (perm_of_list (a :: l)) (seq 1 (length l)) = 
  map (perm_of_list l) (seq 0 (length l)).
Proof.
  rewrite <- seq_shift.
  rewrite map_map.
  apply map_ext_in.
  intros b.
  rewrite in_seq.
  intros [_ Hlt].
  induction l; [easy|].
  unfold perm_of_list.
  simpl.
  destruct b; [easy|].
  apply nth_indep.
  simpl in *; lia.
Qed.


Lemma list_of_perm_of_list (l : list nat) :
  list_of_perm (length l) (perm_of_list l) = l.
Proof.
  induction l; [easy|].
  simpl.
  unfold list_of_perm.
  simpl.
  rewrite map_perm_of_list_seq_cons.
  f_equal.
  apply IHl.
Qed.

Lemma perm_of_list_of_perm (n : nat) (f : nat -> nat) : 
  forall k, k < n -> perm_of_list (list_of_perm n f) k = f k.
Proof.
  revert f; induction n; intros f k Hk; [easy|].
  unfold list_of_perm in *.
  simpl.
  destruct k; [easy|].
  rewrite perm_of_list_cons by (rewrite map_length, seq_length; lia).
  rewrite <- seq_shift, map_map.
  rewrite IHn; lia.
Qed.

Section ToZX.

Import PermutationRules.

(* FIXME: Move to the proper place *)
Lemma zx_of_perm_zxperm (n : nat) (f : nat -> nat) : 
  ZXperm _ (zx_of_perm n f).
Proof.
  apply zx_of_swap_list_zxperm.
Qed.
Hint Resolve zx_of_perm_zxperm : perm_db.



Definition zx_of_list (l : list nat) :=
  ZXperm.zx_of_perm (length l) (perm_of_list l).

Definition zx_of_list_proof (l : list nat) := 
  (eq_sym
     (length_insertion_sort_list (length l)
        (perm_inv (length l) (perm_of_list l)))).

Definition zx_of_list_casted (l : list nat) : ZX (length l) (length l) :=
  cast (length l) (length l) (zx_of_list_proof l) (zx_of_list_proof l)
  (zx_of_list l).

Definition invzx_of_list (l : list nat) :=
  ZXperm.zx_of_perm (length l) (invperm_of_list l).

Definition invzx_of_list_proof (l : list nat) := 
  (eq_sym
     (length_insertion_sort_list (length l)
        (perm_inv (length l) (invperm_of_list l)))).

Definition invzx_of_list_casted (l : list nat) : ZX (length l) (length l) := 
  cast (length l) (length l) (invzx_of_list_proof l) (invzx_of_list_proof l)
    (invzx_of_list l).

Definition zx_between_lists (l l' : list nat) : ZX _ _ :=
  ZXperm.zx_of_perm (length l) 
    (fun k => invperm_of_list l' (perm_of_list l k)).

Definition zx_between_lists_proof (l l' : list nat) :=
  (eq_sym
     (length_insertion_sort_list (length l)
        (perm_inv (length l) 
        (fun k => invperm_of_list l' (perm_of_list l k))))).


Definition zx_between_lists_casted (l l' : list nat) 
  : ZX (length l) (length l) :=
  cast (length l) (length l) 
  (zx_between_lists_proof l l') (zx_between_lists_proof l l')
  (zx_between_lists l l').


(* TO DO : maybe try this alternate? 
  Test if this is correct or wrong/the inverse permutation.
  Also if it's even any better...
Definition zx_between_lists (l l' : list nat) :=
  zx_of_list (map (invperm_of_list l) l').

Definition zx_between_lists (l l' : list nat) :=
  zx_of_list_casted (map (invperm_of_list l) l'). *)


Lemma zx_of_list_zxperm (l : list nat) : ZXperm _ (zx_of_list l).
Proof. apply zx_of_swap_list_zxperm. Qed.

Lemma zx_of_list_casted_zxperm (l : list nat) 
  : ZXperm _ (zx_of_list_casted l).
Proof. apply zxperm_iff_cast, zx_of_swap_list_zxperm. Qed.

Lemma invzx_of_list_zxperm (l : list nat) : ZXperm _ (invzx_of_list l).
Proof. apply zx_of_swap_list_zxperm. Qed.

Lemma invzx_of_list_casted_zxperm (l : list nat) 
  : ZXperm _ (invzx_of_list_casted l).
Proof. apply zxperm_iff_cast, zx_of_swap_list_zxperm. Qed.

Lemma zx_between_lists_zxperm (l l' : list nat) 
  : ZXperm _ (zx_between_lists l l').
Proof. apply zx_of_swap_list_zxperm. Qed.

Lemma zx_between_lists_casted_zxperm (l l' : list nat) 
  : ZXperm _ (zx_between_lists_casted l l').
Proof. apply zxperm_iff_cast, zx_of_swap_list_zxperm. Qed.

Hint Resolve 
  zx_of_list_zxperm
  zx_of_list_casted_zxperm
  invzx_of_list_zxperm
  invzx_of_list_casted_zxperm
  zx_between_lists_zxperm
  zx_between_lists_casted_zxperm : perm_db.

Local Open Scope nat_scope.

Lemma perm_of_zx_of_list (l : list nat) (Hl : is_perm_list l = true) : 
  forall k, k < length l -> perm_of_zx (zx_of_list l) k = perm_of_list l k.
Proof.
  intros k Hk.
  unfold zx_of_list, ZXperm.zx_of_perm.
  rewrite perm_of_zx_of_swap_list by apply insertion_sort_list_is_swap_list.
  rewrite <- perm_of_insertion_sort_list_of_perm_inv_eq; try easy.
  now apply perm_of_list_permutation_of_is_perm_list.
Qed.

End ToZX.

End PermToZX.

Module GraphToDiagram.

Import PermToZX.

(* Local Notation zxnode := (nat * bool * R)%type.
Local Notation node_id A := (@fst nat bool (@fst _ R A)).
Local Notation node_typ A := (@snd nat bool (@fst _ R A)).
Local Notation node_rot A := (@snd (nat * bool) R A). *)
Notation edge := (prod nat nat).

Record zxnode := mk_zxnode {
  node_typ : bool;
  node_rot : R;
}.

Record zxgraph := mk_zxgraph {
  inputs : list nat;
  outputs : list nat;
  nodeids : list nat;
  nodevals : list zxnode;
  edges : list edge;
}.

Local Open Scope nat_scope.


Definition pair_degree (n : nat) (e : edge) :=
  Nat.b2n (n =? fst e) + Nat.b2n (n =? snd e).

Arguments pair_degree _ !_ /.

Definition edgelist_degree (n : nat) (es : list edge) :=
  list_sum (map (pair_degree n) es).

Definition permute_list {A} (f : nat -> nat) (l : list A) : list A :=
  match l with
  | [] => []
  | a :: l' => 
    map (fun n => nth n (a :: l') a) (seq 0 (S (length l')))
  end.

Definition permute_edges (f : nat -> nat) (l : list edge) : list edge :=
  map (fun ab => (f (fst ab), f (snd ab))) l.

Definition permute_graph (f : nat -> nat) (G : zxgraph) : zxgraph :=
  {|
    inputs := G.(inputs);
    outputs := G.(outputs);
    nodeids := G.(nodeids);
    nodevals := permute_list f G.(nodevals);
    edges := permute_edges f G.(edges)
  |}.

Definition is_isomorphism (f : nat -> nat) (G H : zxgraph) :=
  permute_graph f G = H.

Definition get_zxnode_by_id (G : zxgraph) (n : nat) : option zxnode :=
  match (index_of_err (eqb n) G.(nodeids)) with
  | Some n' => nth_error G.(nodevals) n'
  | None => None
  end.

Definition eqb_natpair (e e' : nat * nat) : bool :=
  match e, e' with
  | (e1, e2), (e1', e2') => (e1 =? e1') && (e2 =? e2')
  end.

Lemma eqb_natpair_eq (e e' : nat * nat) : 
  reflect (e = e') (eqb_natpair e e').
Proof.
  destruct e, e'.
  simpl.
  apply iff_reflect.
  rewrite andb_true_iff, 2!Nat.eqb_eq.
  split;
  intros H; inversion H; subst; easy.
Qed.

Definition natpair_eq_dec (e e' : nat * nat) :
  {e = e'} + {e <> e'} :=
  match e, e' with 
  | (e1,e2), (e1', e2') =>
  match Nat.eq_dec e1 e1', Nat.eq_dec e2 e2' with
  | left Heq1, left Heq2 => 
    left (proj2 (pair_equal_spec _ _ _ _) (conj Heq1 Heq2))
  | right Hneq1, _ =>
    right (fun Heq => 
    Hneq1 (proj1 (proj1 (pair_equal_spec _ _ _ _) Heq)))
  | _, right Hneq2 =>
    right (fun Heq => 
    Hneq2 (proj2 (proj1 (pair_equal_spec _ _ _ _) Heq)))
  end
  end.
(* Definition eqb_edge (e e' : edge) : bool :=
  match e, e' with
  | (e1, e2), (e1', e2') => 
    ((e1 =? e1') && (e2 =? e2'))
    || ((e1 =? e2') && (e2 =? e1'))
  end. *)

Definition pairswap {A B} (p : A * B) : B * A :=
  let (pa, pb) := p in (pb, pa).

Lemma pairswap_inv {A B} (p : A * B) :
  pairswap (pairswap p) = p.
Proof.
  now destruct p.
Qed.

Fixpoint Inb {A} (eqbA : A -> A -> bool) (a : A) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: ls => eqbA x a || Inb eqbA a ls
  end.

Lemma InP {A} {eqbA : A -> A -> bool} 
  (eqb_eqA : forall a b : A, reflect (a = b) (eqbA a b)) : 
  forall (a : A) (l : list A),
  reflect (In a l) (Inb eqbA a l).
Proof.
  intros a l.
  induction l; [auto using reflect|].
  simpl.
  apply iff_reflect.
  rewrite orb_true_iff.
  rewrite (reflect_iff _ _ IHl).
  apply or_iff_compat_r.
  apply reflect_iff; easy.
Qed.

Lemma Inb_In {A} {eqbA : A -> A -> bool} 
  (eqb_eqA : forall a b : A, reflect (a = b) (eqbA a b)) : 
  forall (a : A) (l : list A),
  In a l <-> Inb eqbA a l = true.
Proof.
  now intros; apply reflect_iff, InP.
Qed.

Definition inb_edge_list (e : edge) (edges : list edge) :=
  Inb eqb_natpair e (edges ++ (map pairswap edges)).

Lemma inb_edge_list_alt (e : edge) (edges : list edge) :
  inb_edge_list e edges = Inb eqb_natpair e edges 
    || Inb eqb_natpair (pairswap e) edges.
Proof.
  unfold inb_edge_list.
  apply eq_true_iff_eq.
  rewrite orb_true_iff.
  rewrite <- 3!(Inb_In eqb_natpair_eq).
  rewrite in_app_iff, in_map_iff.
  apply or_iff_compat_l.
  split.
  - intros [x [Heq Hin]]; subst.
    now rewrite pairswap_inv.
  - intros Hin.
    exists (pairswap e).
    rewrite pairswap_inv.
    easy.
Qed.

Definition inb_node_list (a : nat) (nodes : list nat) :=
  Inb eqb a nodes.

Section deceq_list.

Context {A : Type} (eq_dec : (forall x y : A, {x = y}+{x <> y})).

Fixpoint remove_one 
  (x : A) (l : list A) : list A := 
  match l with
      | [] => []
      | x'::xs => if (eq_dec x x') then xs else x'::(remove_one x xs)
  end.

Lemma length_pos_In {a : A} {l : list A} (Hin : In a l) :
  0 < length l.
Proof.
  induction l; easy + simpl; lia.
Qed.

Lemma length_remove_one_in (a : A) (l : list A) (Hin : In a l) : 
  length (remove_one a l) = length l - 1.
Proof.
  induction l; [easy|].
  simpl.
  destruct (eq_dec a a0); [lia|].
  simpl in *.
  destruct Hin as [Ha | Hin]; [congruence|].
  rewrite IHl by auto.
  pose proof (length_pos_In Hin); lia.
Qed.

Lemma remove_one_not_in (a : A) (l : list A) (Hnotin : ~ In a l) :
  remove_one a l = l.
Proof.
  induction l as [|b ls IHl]; [easy|].
  simpl.
  destruct (eq_dec a b).
  - subst; exfalso; apply Hnotin; left; easy.
  - rewrite IHl; [easy|].
    simpl in Hnotin.
    auto.
Qed.

Lemma count_remove_one (a : A) (l : list A) :
  count_occ eq_dec (remove_one a l) a = 
  pred (count_occ eq_dec l a).
Proof.
  destruct (in_dec eq_dec a l) as [Hi | Hni].
  - induction l as [|b ls IHl]; [easy|].
    simpl in *.
    destruct (eq_dec a b) as [Hab | Hnab];
    destruct (eq_dec b a); try congruence + easy.
    simpl.
    destruct (eq_dec b a); try easy.
    apply IHl; destruct Hi; easy.
  - rewrite (remove_one_not_in _ _ Hni).
    rewrite (count_occ_not_In eq_dec l a) in Hni.
    rewrite Hni; easy.
Qed.

Definition star (edges : list edge) (vtx : nat) : list edge :=
  filter (fun e => 0 <? pair_degree vtx e) edges.

Definition neighborhood (edges : list edge) (vtx : nat) : list nat :=
  map (fun e : edge => let (e1, e2) := e in 
    if vtx =? e1 then e2 else e1) (star edges vtx).

Lemma degree_star (edges : list edge) (vtx : nat) :
  edgelist_degree vtx (star edges vtx) = 
  edgelist_degree vtx edges.
Proof.
  induction edges as [|a edges]; [easy|].
  simpl.
  unfold edgelist_degree.
  rewrite if_dist.
  simpl.
  replace (list_sum (if 0 <? pair_degree vtx a
  then pair_degree vtx a :: map (pair_degree vtx) (star edges vtx)
  else map (pair_degree vtx) (star edges vtx)))
  with (list_sum (pair_degree vtx a :: map (pair_degree vtx) (star edges vtx))).
  - simpl; f_equal; apply IHedges.
  - destruct (0 <? pair_degree vtx a) eqn:e; [easy|].
    rewrite Nat.ltb_nlt in e.
    replace (pair_degree vtx a) with 0 by lia.
    easy.
Qed.


Fixpoint list_diff (l l' : list A) : list A :=
  match l with
  | [] => []
  | x :: ls => 
    if in_dec eq_dec x l' 
    then list_diff ls l'
    else x :: list_diff ls l'
  end.

Fixpoint list_union (l l' : list A) : list A :=
  match l with
  | [] => l'
  | x :: ls => if in_dec eq_dec x l'
    then list_union ls l'
    else x :: list_union ls l'
  end.

Fixpoint list_intersection (l l' : list A) : list A :=
  match l with
  | [] => []
  | x :: ls => if in_dec eq_dec x l'
    then x :: list_intersection ls l'
    else list_intersection ls l'
  end.


Lemma in_list_diff (l l' : list A) (a : A) : 
  In a (list_diff l l') <-> 
  In a l /\ ~ In a l'.
Proof.
  induction l as [|b ls IHl]; [easy|].
  simpl.
  destruct (eq_dec a b) as [Hab | Hnab].
  - subst.
    destruct (in_dec eq_dec b l') as [Hin | Hnin].
    + rewrite IHl; easy.
    + split; simpl; constructor; auto.
  - destruct (in_dec eq_dec b l') as [Hin | Hnin].
    + rewrite IHl.
      split; intros H; constructor; try right; apply H + auto.
      destruct (proj1 H); easy + congruence.
    + simpl.
      rewrite IHl.
      split; intros []; try apply or_intror; constructor;
      apply H + (right; apply H) + auto.
      destruct H; easy + congruence.
Qed.

Lemma in_list_union (l l' : list A) (a : A) : 
  In a (list_union l l') <-> 
  In a l \/ In a l'.
Proof.
  induction l as [|b ls IHl]; [repeat intros [] + split + right + easy|].
  simpl.
  rewrite or_assoc, <- IHl.
  destruct (in_dec eq_dec b l') as [Hin | Hnin].
  - split; try (right; easy).
    intros [Heq | Hr]; [|easy].
    rewrite IHl.
    right; subst; easy.
  - easy.
Qed.

Lemma in_list_intersection (l l' : list A) (a : A) : 
  In a (list_intersection l l') <-> 
  In a l /\ In a l'.
Proof.
  induction l as [|b ls IHl]; [easy|].
  simpl.
  (* rewrite or_assoc, <- IHl. *)
  destruct (in_dec eq_dec b l') as [Hin | Hnin].
  - simpl.
    rewrite IHl.
    split.
    + intros [Heq | Hrhs]; [subst; auto|].
      split; try right; apply Hrhs.
    + intros [[Heq | Hbin] Hbin'];
      [left; easy|].
      right; auto.
  - rewrite IHl.
    split.
    + intros []; split; [right|]; easy.
    + intros [[Heq | Hainls] Hainl'].
      * subst; easy.
      * easy.
Qed.

Lemma NoDup_list_diff (l l' : list A) (Hl : NoDup l) : 
  NoDup (list_diff l l').
Proof.
  induction l; [easy|].
  rewrite NoDup_cons_iff in Hl.
  simpl.
  destruct (in_dec eq_dec a l') as [Hin | Hnin].
  - apply IHl, Hl.
  - apply NoDup_cons_iff.
    rewrite in_list_diff.
    split; [|apply IHl, Hl].
    intros []; easy.
Qed.

Lemma NoDup_list_union (l l' : list A) 
  (Hl : NoDup l) (Hl' : NoDup l') : NoDup (list_union l l').
Proof.
  induction l; [easy|].
  simpl.
  rewrite NoDup_cons_iff in Hl.
  destruct (in_dec eq_dec a l') as [Hin | Hnin].
  - apply IHl, Hl.
  - apply NoDup_cons.
    + rewrite in_list_union.
      intros []; [apply Hl|]; auto.
    + apply IHl, Hl.
Qed.

Lemma NoDup_list_intersection (l l' : list A) (Hl : NoDup l) : 
  NoDup (list_intersection l l').
Proof.
  induction l; [easy|].
  simpl.
  rewrite NoDup_cons_iff in Hl.
  destruct (in_dec eq_dec a l') as [Hin | Hnin].
  - apply NoDup_cons.
    + rewrite in_list_intersection.
      intros []; apply Hl; auto.
    + apply IHl, Hl.
  - apply IHl, Hl.
Qed.

End deceq_list.


Fixpoint renumber_edges (es : list edge) (old new : nat) : list edge :=
  match es with
  | [] => []
  | (e1, e2) :: es' => 
    match Nat.eq_dec e1 old, Nat.eq_dec e2 old with
    | left Heq1, left Heq2 =>
      (new, S new) :: (renumber_edges es' old (S (S new)))
    | left Heq1, right Hneq2 => 
      (new, e2) :: (renumber_edges es' old (S new))
    | right Hneq1, left Heq2 => 
      (e1, new) :: (renumber_edges es' old (S new))
    | right Hneq1, right Hneq2 =>
      (e1, e2) :: (renumber_edges es' old new)
    end
  end.

Lemma degree_renumber_edges (es : list edge) (old new : nat) (H : old < new) :
  edgelist_degree old (renumber_edges es old new) = 0.
Proof.
  unfold edgelist_degree.
  revert old new H; 
  induction es as [|[a1 a2] es IHes]; [easy|];
  intros old new H.
  simpl.
  destruct (Nat.eq_dec a1 old) as [Heq1 | Hneq1], 
    (Nat.eq_dec a2 old) as [Heq2 | Hneq2];
  simpl; rewrite IHes; bdestruct_all; simpl; lia.
Qed.

Fixpoint renumber_idxs (idxs : list nat) (old new : nat) : list nat :=
  match idxs with
  | [] => []
  | x :: idxs' =>
    match Nat.eq_dec x old with
    | left Heq => new :: (renumber_idxs idxs' old (S new))
    | right Hneq => x :: (renumber_idxs idxs' old new)
    end
  end.

Lemma count_occ_renumber_idxs_old (idxs : list nat) (old new : nat) 
  (Hnew : old < new) :
  count_occ Nat.eq_dec (renumber_idxs idxs old new) old = 0.
Proof.
  revert old new Hnew; 
  induction idxs; [easy|];
  intros old new Hnew.
  simpl.
  destruct (Nat.eq_dec a old).
  - simpl.
    rewrite IHidxs by lia.
    destruct (Nat.eq_dec new old); lia.
  - simpl.
    rewrite IHidxs by lia.
    destruct (Nat.eq_dec a old); lia.
Qed.

Lemma count_occ_renumber_idxs_lt_new (idxs : list nat) (old new : nat) 
  (v : nat) (Hv : v < new) (Hold : v <> old) :
  count_occ Nat.eq_dec (renumber_idxs idxs old new) v = 
  count_occ Nat.eq_dec idxs v.
Proof.
  revert old new Hv Hold; 
  induction idxs; [easy|];
  intros old new Hv Hold.
  simpl.
  destruct (Nat.eq_dec a old).
  - simpl.
    rewrite IHidxs by lia.
    destruct (Nat.eq_dec new v), (Nat.eq_dec a v); lia.
  - simpl.
    rewrite IHidxs by lia.
    easy.
Qed.


Lemma renumber_idxs_nodup (idxs : list nat) : forall (old new : nat) 
  (Hold : old < new)
  (Hidxs : forall n, n <> old -> count_occ Nat.eq_dec idxs n <= 1)
  (Hnew : forall n, In n idxs -> n < new),
  NoDup (renumber_idxs idxs old new).
Proof.
  induction idxs; [constructor|].
  intros old new Hold Hidxs Hnew.
  simpl.
  replace (if Nat.eq_dec a old
    then new :: renumber_idxs idxs old (S new)
    else a :: renumber_idxs idxs old new)
  with (
    (if Nat.eq_dec a old then new else a) ::
    renumber_idxs idxs old (if Nat.eq_dec a old then S new else new))
  by (destruct (Nat.eq_dec a old); easy).
  apply NoDup_cons.
  - rewrite (count_occ_not_In Nat.eq_dec).
    rewrite count_occ_renumber_idxs_lt_new; 
    destruct (Nat.eq_dec a old) as [Heq | Hneq]; try lia.
    + rewrite <- count_occ_not_In.
      intros Hf.
      enough (new < new) by lia.
      apply Hnew.
      right; easy.
    + specialize (Hidxs a Hneq).
      simpl in Hidxs.
      destruct (Nat.eq_dec a a); lia.
    + now apply Hnew; left.
  - apply IHidxs; destruct (Nat.eq_dec a old) as [Heq | Hneq]; try lia.
    + intros n Hn.
      specialize (Hidxs n Hn).
      simpl in Hidxs.
      destruct (Nat.eq_dec a n); lia.
    + intros n Hn.
      specialize (Hidxs n Hn).
      simpl in Hidxs.
      destruct (Nat.eq_dec a n); lia.
    + intros n Hn.
      specialize (Hnew n (or_intror Hn)).
      lia.
    + intros n Hn.
      apply (Hnew n (or_intror Hn)).
Qed.

Fixpoint renumber_edges_remove_self (es : list edge) (old new : nat) : list edge :=
  match es with
  | [] => []
  | (e1, e2) :: es' => 
    match Nat.eq_dec e1 old, Nat.eq_dec e2 old with
    | left Heq1, left Heq2 =>
      (renumber_edges_remove_self es' old new)
    | left Heq1, right Hneq2 => 
      (new, e2) :: (renumber_edges_remove_self es' old (S new))
    | right Hneq1, left Heq2 => 
      (e1, new) :: (renumber_edges_remove_self es' old (S new))
    | right Hneq1, right Hneq2 =>
      (e1, e2) :: (renumber_edges_remove_self es' old new)
    end
  end.

Fixpoint renumber_edges_remove_self_record 
  (es : list edge) (old new : nat) : list edge * list nat:=
  match es with
  | [] => ([], [])
  | (e1, e2) :: es' => 
    match Nat.eq_dec e1 old, Nat.eq_dec e2 old with
    | left Heq1, left Heq2 =>
      (renumber_edges_remove_self_record es' old new)
    | left Heq1, right Hneq2 => 
      let (newes, used) := (renumber_edges_remove_self_record es' old (S new)) in
      ((new, e2) :: newes, new :: used)
    | right Hneq1, left Heq2 => 
      let (newes, used) := (renumber_edges_remove_self_record es' old (S new)) in
      ((e1, new) :: newes, new :: used)
    | right Hneq1, right Hneq2 =>
      let (newes, used) := (renumber_edges_remove_self_record es' old new) in
      ((e1, e2) :: newes, used)
    end
  end.

Lemma degree_renumber_edges_remove_self_record_aux (es : list edge) (old new : nat) 
  (Hnew : forall n, 0 < edgelist_degree n es -> n < new) : 
  edgelist_degree new es = 0.
Proof.
  bdestruct (0 <? edgelist_degree new es); [|lia].
  enough (new < new) by lia.
  apply Hnew.
  easy.
Qed.

Lemma edgelist_degree_cons_pair (e1 e2 : nat) (es : list edge) (n : nat) :
  edgelist_degree n ((e1, e2) :: es) = 
  (if Nat.eq_dec e1 n then 1 else 0) 
  + (if Nat.eq_dec e2 n then 1 else 0)
  + edgelist_degree n es.
Proof.
  unfold edgelist_degree.
  simpl.
  bdestruct (n =? e1);
  bdestruct (n =? e2);
  destruct (Nat.eq_dec e1 n), (Nat.eq_dec e2 n); 
  easy + lia.
Qed.


Section no_simpl_sub.

Local Arguments sub : simpl never.

Lemma double_self_edge_count_le_degree (es : list edge) (n : nat) : 
  2 * count_occ natpair_eq_dec es (n, n) <= edgelist_degree n es.
Proof.
  induction es as [|[a1 a2] es IHes]; [easy|].
  simpl.
  rewrite edgelist_degree_cons_pair.
  destruct (Nat.eq_dec a1 n), (Nat.eq_dec a2 n); lia.
Qed.


Lemma renumber_edges_remove_self_record_eq (es : list edge) (old new : nat) :
  renumber_edges_remove_self_record es old new = 
  (renumber_edges_remove_self es old new, 
    seq new 
    ((edgelist_degree old es) 
    - 2 * count_occ natpair_eq_dec es (old, old))). 
Proof.
  revert new;
  induction es as [|[a1 a2] es IHes]; [easy|]. 
  intros new.
  rewrite edgelist_degree_cons_pair.
  simpl; rewrite !IHes.
  destruct (Nat.eq_dec a1 old) as [H1 | Hn1],
    (Nat.eq_dec a2 old) as [H2 | Hn2]; simpl.
  - do 2 f_equal; lia.
  - rewrite Nat.sub_succ_l 
    by (apply double_self_edge_count_le_degree).
    easy.
  - rewrite Nat.sub_succ_l 
    by (apply double_self_edge_count_le_degree).
    easy.
  - easy.
Qed.

End no_simpl_sub.


Lemma degree_renumber_edges_remove_self_record (es : list edge) (old new : nat) 
  (Hnew : forall n, 0 < edgelist_degree n es -> n < new) :
  let (es', used) := renumber_edges_remove_self_record es old new in  
  forall n, edgelist_degree 


Fixpoint new_verts_in_edgelist (verts : list nat) (es : list edges) : list nat :=
  match es with
  | [] => []
  | (e1, e2) :: es' => 
    (if in_dec Nat.eq_dec e1 verts then [] else [e1])
    ++ (if in_dec Nat.eq_dec e2 verts)

Definition inputs_of_truncate (G : zxgraph) (v : nat) : list nat :=
  list_diff Nat.eq_dec G.(inputs) (neighborhood G.(edges) v).

Definition outputs_of_truncate (G : zxgraph) (v : nat) : list nat :=
  renumber_idxs

Definition truncate_vtx (G : zxgraph) (v : nat) : zxgraph 



End GraphToDiagram.


Module WFzxgraph.

Import PermToZX GraphToDiagram.

Definition WFzxgraph (G : zxgraph) : Prop :=
  let allids := G.(inputs) ++ G.(nodeids) ++ G.(outputs) in
  length G.(nodeids) = length G.(nodevals) 
  /\ NoDup allids
  /\ Forall 
    (fun e : edge => let (e1, e2) := e in 
      In e1 allids /\ In e2 allids) G.(edges)
  /\ Forall 
    (fun a : nat => edgelist_degree a G.(edges) = S O)
    (G.(inputs) ++ G.(outputs)).

Section WFzxgraph_dec.

Fixpoint NoDupb {A} (eqbA : A -> A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: ls => negb (Inb eqbA x ls) && NoDupb eqbA ls
  end.

Lemma NoDupP {A} {eqbA : A -> A -> bool} 
  (eqb_eqA : forall a b : A, reflect (a = b) (eqbA a b)) :
  forall (l : list A), 
  reflect (NoDup l) (NoDupb eqbA l).
Proof.
  intros l.
  apply iff_reflect.
  induction l; [split; easy+constructor|].
  simpl.
  rewrite NoDup_cons_iff.
  rewrite (Inb_In eqb_eqA).
  rewrite andb_true_iff, negb_true_iff, IHl.
  apply and_iff_compat_r.
  destruct (Inb eqbA a l); easy.
Qed.

Lemma NoDup_Nodupb {A} {eqbA : A -> A -> bool} 
  (eqb_eqA : forall a b : A, reflect (a = b) (eqbA a b)) :
  forall (l : list A), 
  NoDup l <-> NoDupb eqbA l = true.
Proof.
  now intros; apply reflect_iff, NoDupP.
Qed.



Definition WFzxgraphb (G : zxgraph) : bool :=
  let allids := G.(inputs) ++ G.(nodeids) ++ G.(outputs) in
  (length G.(nodeids) =? length G.(nodevals) )
  && NoDupb eqb allids
  && forallb 
    (fun e : edge => let (e1, e2) := e in 
      Inb eqb e1 allids && Inb eqb e2 allids) G.(edges)
  && forallb
    (fun a : nat => edgelist_degree a G.(edges) =? S O)
    (G.(inputs) ++ G.(outputs)).

Lemma forall_iff {A} (P Q : A -> Prop) :
  (forall a, (P a <-> Q a)) ->
  ((forall a, P a) <-> (forall a, Q a)).
Proof.
  intros Hiff.
  now setoid_rewrite Hiff.
Qed.

Lemma and_iff_compat (P P' Q Q' : Prop) : 
  (P <-> P') -> (Q <-> Q') ->
  (P /\ Q <-> P' /\ Q').
Proof.
  now intros Hl Hr; rewrite Hl, Hr.
Qed.

Lemma or_iff_compat (P P' Q Q' : Prop) : 
  (P <-> P') -> (Q <-> Q') ->
  (P \/ Q <-> P' \/ Q').
Proof.
  now intros Hl Hr; rewrite Hl, Hr.
Qed.

Lemma WFzxgraph_WFzxgraphb (G : zxgraph) : 
  WFzxgraph G <-> WFzxgraphb G = true.
Proof.
  destruct G.
  unfold WFzxgraph, WFzxgraphb.
  simpl.
  rewrite 3!andb_true_iff, Nat.eqb_eq.
  rewrite !and_assoc.
  apply and_iff_compat_l.
  rewrite (NoDup_Nodupb beq_reflect).
  apply and_iff_compat_l.
  rewrite 2!forallb_forall, 2!Forall_forall.
  apply and_iff_compat; 
  apply forall_iff; [intros []|intros]; 
  apply imp_iff_compat_l.
  - now rewrite andb_true_iff, 2!(Inb_In beq_reflect).
  - now rewrite Nat.eqb_eq.
Qed.

Lemma WFzxgraphP (G : zxgraph) : 
  reflect (WFzxgraph G) (WFzxgraphb G).
Proof.
  apply iff_reflect, WFzxgraph_WFzxgraphb.
Qed.



End WFzxgraph_dec.



Section WFzxgraph_results.

Context (G : zxgraph) (HG : WFzxgraph G).

Lemma NoDup_allids : NoDup (G.(inputs) ++ G.(nodeids) ++ G.(outputs)).
Proof. apply HG. Qed.

Lemma length_nodeids_nodevals : length G.(nodeids) = length G.(nodevals).
Proof. apply HG. Qed.

Lemma edge_members_in : Forall 
  (fun e : edge => let (e1, e2) := e in 
  In e1 (G.(inputs) ++ G.(nodeids) ++ G.(outputs)) 
  /\ In e2 (G.(inputs) ++ G.(nodeids) ++ G.(outputs))) G.(edges).
Proof. apply HG. Qed.



Lemma inputs_NoDup : NoDup G.(inputs).
Proof.
  eapply NoDup_app_l.
  exact NoDup_allids.
Qed.

Lemma outputs_NoDup : NoDup G.(outputs).
Proof.
  eapply NoDup_app_r, NoDup_app_r.
  exact NoDup_allids.
Qed.

Lemma nodeids_NoDup : NoDup G.(nodeids).
Proof.
  eapply NoDup_app_l, NoDup_app_r.
  exact NoDup_allids.
Qed.






End WFzxgraph_results.

End WFzxgraph.

(* TODO: Complete, and maybe make nicer?

Definition WF_zxgraph : zxgraph -> Prop := 
  fun g => 
     (g.(inputs) = iota (length g.(inputs)) 0)
  /\ (g.(nodeids) = iota (length g.(nodeids)) (length g.(inputs)))
  /\ (g.(outputs) = iota (length g.(outputs))
    (length g.(inputs) + (length g.(nodeids)))). *)






(* Translate graphical adjacency list ZX data type with connection information into semantically equivalent ZX diagram *)

(*  This entire section has the goal of constructing any general 
    ZX swap structure that can swap between any two qubit permutations.
    The ZX swap only swaps adjacent wires, so a bubblesort is needed.
*)

Definition indexed_list (A : Type) : Type := list (A * nat).

(*  Provides indices for an existing list invreverse order
    so the element closest to nil is index 0
    [1, 2, 3] -> [(1, 2), (2, 1), (3, 0)]*)
Definition create_indexed_list {A : Type} (l : list A) : indexed_list A :=
  combine l (rev (seq 0 (length l))).

Definition indexed_list_to_list {A : Type} (il : indexed_list A) : list A :=
  map (fun l' => fst l') il.

(* Correctness/WF proof *)
Fixpoint indexed_list_correct_aux {A : Type} (il : indexed_list A) (i : nat) : Prop :=
  match il with
  | (_, n) :: ils => n = i /\ (indexed_list_correct_aux ils (pred i))
  | [] => True
  end.

Definition indexed_list_correct {A : Type} (il : indexed_list A) : Prop :=
  indexed_list_correct_aux il (pred (length il)).

Lemma rev_seq_S : 
  forall (len : nat) (start : nat), rev (seq start (S len)) = [(add start len)] ++ rev (seq start len).
Proof.
    intros; rewrite seq_S; rewrite rev_app_distr; auto.
Qed.

Lemma create_indexed_list_WF : 
  forall (A : Type) (l : list A), indexed_list_correct (create_indexed_list l).
Proof.
    intros. induction l; unfold create_indexed_list, indexed_list_correct in *; simpl.
    - auto.
    - simpl. destruct (length l) eqn:E. simpl; split; auto.
    apply length_zero_iff_nil in E; subst; auto.
    rewrite rev_seq_S; simpl; split; rewrite combine_length in *; rewrite app_length in *; 
    rewrite rev_length in *; rewrite seq_length in *; simpl in *;
    rewrite E in *; rewrite PeanoNat.Nat.add_1_r in *; rewrite PeanoNat.Nat.min_id in *; simpl in *; auto.
Qed.

(* Again, this is general as this should really be bounded by the length
  of the list it is referring to, it should only contain indices that
  can represent a swap in list l -> [0, length l) *)
Definition swap_list : Type := list nat.

(* Attribute this properly *)
(* I grabbed this from here: https://codeberg.org/mathprocessing/coq-examples/src/branch/master/sorts/bubblesort.v
    There is a verified version here which could replace this:
    https://github.com/holmuk/Sorticoq/blob/master/src/BubbleSort.v *)
Fixpoint bubblesort_pass (l : indexed_list nat) (sl : swap_list) : (indexed_list nat * swap_list * bool) :=
  match l with
  | [] => ([], sl, false)
  | x :: xs =>
      match bubblesort_pass xs sl with
      | ([], sl', b) => ([x], sl', b)
      | (x' :: xs', sl', b) =>
          if Nat.ltb (fst x') (fst x) 
            then (((fst x'), (snd x)) :: ((fst x), (snd x')) :: xs', ((snd x') :: sl'), true)
            else (x :: x' :: xs', sl', b)
      end
  end.

Fixpoint bubblesort_aux (gas : nat) (l : indexed_list nat) (sl : swap_list) : indexed_list nat * swap_list :=
  match gas with
  | O => (l, sl)
  | S gas' => 
    match bubblesort_pass l sl with
      | (x :: xs, sl', true) => 
        match (bubblesort_aux gas' xs sl) with
        |(xs', sl'') => ((x :: xs'), (rev sl') ++ sl'')
        end
      | _ => (l, sl)
      end
  end.

(* Needs proof of correctness *)
Definition bubblesort (l : list nat) : indexed_list nat * swap_list :=
  bubblesort_aux (pred (length l)) (create_indexed_list l) [].

Definition generate_swap_list (l : list nat) : swap_list := 
  snd (bubblesort l).

(* Could be tested more *)
(* The correct swapping procedure. Given index i, swaps the ith and i + 1th index. *)
(* 0 <= i < len(il), with index conventions as above *)
Fixpoint swap_adjacent_in_ind_list (il : indexed_list nat) (i : nat) : indexed_list nat :=
  match il with
  | [] => []
  | (x, i') :: xs => 
    match xs with
    | [] => [(x, i')]
    | (x', i'') :: xs' => 
      if (i =? i'') then 
        (x', i') :: (x, i'') :: xs'
      else
        (x, i') :: swap_adjacent_in_ind_list xs i
    end
  end.

(*  Constructing the swap structure *)
(*  From a swap index, the idea is to create a stack of wires with a 
    swap at the correct index. The convention used is imagining the 
    wire permutation indicies increasing from bottom to top in a stack.
    [(wire_1, 2), (wire_2, 1), (wire_3), 0] --> [wire_1, 2]
                                                [wire_2, 1]
                                                [wire_3, 0]
    A swap index of 1 would swap wire_1 and wire_2 above. 
    A swap index of 0 would swap wire_2 and wire_3 above. 
*)                                              
Lemma build_swap_at_index_aux_aux : 
  forall i len, le 2 len -> le (plus 2 i) len -> 
    len = plus (sub len (plus 2 i)) (plus 2 i).
Proof.
  lia.
Qed.

(* This could be rewritten as below ones *)
Fixpoint build_swap_at_index (i len : nat) : ZX len len.
Proof.
  destruct (le_lt_dec (plus 2 i) len); destruct (le_lt_dec 2 len).
  - eapply cast. 
    + eapply (build_swap_at_index_aux_aux i len).
      * exact l0.
      * exact l.
    + eapply (build_swap_at_index_aux_aux i len).
      * exact l0.
      * exact l.
    + eapply (pad_top (sub len (plus 2 i)) (pad_bot i Swap)).
  - exact (n_wire len).
  - exact (n_wire len).
  - exact (n_wire len).
Defined.

Lemma _eq_nat_eq : forall n m : nat, eq_nat n m -> n = m.
Proof.
  induction n; simpl; intro m; destruct m; simpl.
  - reflexivity.
  - contradiction.
  - contradiction.
  - intros; apply f_equal; exact (IHn m H).
Defined.

(* Putting it all together, to find the sequence of arbitrary swaps between
    two arbitrary permutations, two bubble sorts are done for each and the
    second is reversed, which creates a path between the permutations *)

(* Preserves left-right order (head-first list order) of swap list *)
Definition arbitrary_swap_from_swaplist (sl : swap_list) (len : nat) : ZX len len :=
  fold_left (fun cur_zx r => cur_zx ⟷ (build_swap_at_index r len))
            sl (n_wire len).

Definition create_arbitrary_swap_old (l l' : list nat) : ZX (length l) (length l).
Proof.
  destruct (eq_nat_decide (length l) (length l')).
  - eapply Compose.
      + eapply (arbitrary_swap_from_swaplist (generate_swap_list l) (length l)).
      + eapply cast.
        * eapply _eq_nat_eq; exact e.
        * eapply _eq_nat_eq; exact e.
        * eapply (arbitrary_swap_from_swaplist (rev (generate_swap_list l')) (length l')).
  - (* Dummy case *)
    exact (n_wire (length l)).
Defined.

Definition create_arbitrary_swap (l l' : list nat) :=
  PermToZX.zx_between_lists_casted l l'.

Local Hint Unfold 
  create_arbitrary_swap
  arbitrary_swap_from_swaplist
  pad_bot
  pad_top
  : bubblesort_swap_eval_db.

Ltac eval_bubblsort_swap :=
try (
  repeat(
  autounfold with bubblesort_swap_eval_db;
  simpl);
  simpl_casts;
  cleanup_zx;
  simpl_casts;
  simpl)
.





Fixpoint is_n_wire {n m : nat} (zx : ZX n m) : bool :=
  match zx with
  | ⦰ => true
  | — => true
  | zx0 ↕ zx1 => is_n_wire zx0 && is_n_wire zx1
  | _ => false
  end.

Lemma n_wire_is_n_wire (n : nat) : is_n_wire (n_wire n) = true.
Proof.
  induction n; easy.
Qed.

Lemma is_n_wire_square {n m : nat} (zx : ZX n m) : 
  is_n_wire zx = true -> n = m.
Proof.
  intros H.
  induction zx; try easy.
  simpl in H.
  rewrite andb_true_iff in H.
  rewrite IHzx1, IHzx2; easy.
Qed.

Definition nwire_of_is {n m : nat} {zx : ZX n m}
  (H : is_n_wire zx = true) : ZX n m :=
  cast n m eq_refl (eq_sym (is_n_wire_square zx H)) (n_wire n).

Lemma is_n_wire_propto_n_wire {n m : nat} 
  (zx : ZX n m) (H: is_n_wire zx = true) : 
  zx ∝ nwire_of_is H.
Proof.
  unfold nwire_of_is.
  induction zx; try easy.
  1,2: rewrite cast_id; try easy.
  1: apply wire_to_n_wire.
  simpl in H.
  pose proof H as H'.
  rewrite andb_true_iff in H'.
  pose proof (is_n_wire_square _ (proj1 H')).
  pose proof (is_n_wire_square _ (proj2 H')).
  subst.
  rewrite cast_id.
  rewrite (IHzx1 (proj1 H')), cast_id, (IHzx2 (proj2 H')), cast_id.
  rewrite n_wire_stack.
  easy.
Qed.

Lemma is_n_wire_removal_l {n m : nat} (zxid : ZX n n) 
  (H : is_n_wire zxid = true) (zx : ZX n m):
  zxid ⟷ zx ∝ zx.
Proof.
  now rewrite (is_n_wire_propto_n_wire zxid H); unfold nwire_of_is;
  rewrite cast_id, nwire_removal_l.
Qed.

Lemma is_n_wire_removal_r {n m : nat} (zxid : ZX m m) 
  (H : is_n_wire zxid = true) (zx : ZX n m):
  zx ⟷ zxid ∝ zx.
Proof.
  now rewrite (is_n_wire_propto_n_wire zxid H); unfold nwire_of_is;
  rewrite cast_id, nwire_removal_r.
Qed.

Fixpoint func_remove_nwire {n m : nat} (zx : ZX n m) : ZX n m :=
  match zx in ZX a b return ZX a b with
  | @Compose n m o zx0 zx1 =>
    match bool_dec (is_n_wire zx0) true with
    | left H => cast n o (is_n_wire_square zx0 H) eq_refl 
        (func_remove_nwire zx1)
    | right Hfalse => (* zx0 ⟷ zx1 *)
      match bool_dec (is_n_wire zx1) true with
      | left H => cast n o eq_refl (eq_sym (is_n_wire_square zx1 H))
          (func_remove_nwire zx0)
      | right H => func_remove_nwire zx0 ⟷ func_remove_nwire zx1
      end
    end
  | zx0 ↕ zx1 => func_remove_nwire zx0 ↕ func_remove_nwire zx1
  | a => a
  end.

Lemma func_remove_nwire_prop {n m : nat} (zx : ZX n m) : 
  func_remove_nwire zx ∝ zx.
Proof.
  induction zx; try easy.
  - rewrite <- IHzx1, <- IHzx2 at 2; easy.
  - unfold func_remove_nwire.
    destruct (bool_dec (is_n_wire zx1)) as [Hwire1 | Hnot1].
    + rewrite (is_n_wire_propto_n_wire zx1 Hwire1) at 2.
      unfold nwire_of_is.
      rewrite cast_compose_l, nwire_removal_l, 
        cast_contract, IHzx2.
      easy.
    + destruct (bool_dec (is_n_wire zx2)) as [Hwire2 | Hnot2].
      * rewrite IHzx1.
        rewrite (is_n_wire_propto_n_wire zx2 Hwire2) at 2.
        unfold nwire_of_is.
        rewrite cast_compose_r, nwire_removal_r,
          cast_contract.
        easy.
      * rewrite IHzx1, IHzx2.
        easy.
Qed.

(* FIXME: Put in cast place *)
Lemma cast_fn_eq (f: forall n m, ZX n m) {n n' m m'} prfn prfm :
  cast n' m' prfn prfm (f n m) = f n' m'.
Proof.
  subst.
  apply PermutationAutomation.cast_id_eq.
Qed.

Lemma fn_cast_eq_gen {A : forall n m : nat, Type} 
  (f : forall {n m} (zx : ZX n m), A n m) 
  {n n' m m' : nat} (prfn : n' = n) (prfm : m' = m) (zx : ZX n m) : 
  f (cast n' m' prfn prfm zx) = 
  eq_rect_r (fun n' => A n' m')
  (eq_rect_r (A n) (f zx) prfm) prfn.
Proof.
  subst.
  rewrite PermutationAutomation.cast_id_eq.
  reflexivity. 
Qed.

Lemma fn_cast_eq_fn {A} 
  (f : forall {n m} (zx : ZX n m), A) 
  {n n' m m' : nat} (prfn : n' = n) (prfm : m' = m) (zx : ZX n m) : 
  f (cast n' m' prfn prfm zx) = (f zx).
Proof.
  subst.
  rewrite PermutationAutomation.cast_id_eq.
  reflexivity. 
Qed.

Lemma fn_cast_eq_zx {ndim mdim : nat -> nat -> nat}
  (f : forall {n m} (zx : ZX n m), ZX (ndim n m) (mdim n m))
  {n n' m m' : nat} (prfn : n' = n) (prfm : m' = m) (zx : ZX n m) : 
  f (cast n' m' prfn prfm zx) = 
  cast (ndim n' m') (mdim n' m') 
    (f_equal2 ndim prfn prfm) (f_equal2 mdim prfn prfm) 
    (f zx).
Proof.
  subst.
  rewrite 2!PermutationAutomation.cast_id_eq.
  easy.
Qed.

Lemma fn_cast_eq_zx_samedims (f : forall {n m} (zx : ZX n m), ZX n m)
  {n n' m m' : nat} (prfn : n' = n) (prfm : m' = m) (zx : ZX n m) : 
  f (cast n' m' prfn prfm zx) = 
  cast n' m' prfn prfm
    (f zx).
Proof.
  subst.
  rewrite 2!PermutationAutomation.cast_id_eq.
  easy.
Qed.


Fixpoint zx_structural_weight {n m : nat} (zx : ZX n m) : nat :=
  match zx with
  | zx0 ↕ zx1 => zx_structural_weight zx0 + zx_structural_weight zx1
  | zx0 ⟷ zx1 => zx_structural_weight zx0 + zx_structural_weight zx1 
  | _ => S (n + m)
  end.

Lemma zx_structural_weight_gt_dimsum {n m} (zx : ZX n m) : 
  (n + m < zx_structural_weight zx)%nat.
Proof.
  induction zx; simpl; lia.
Qed.

Lemma zx_structural_weight_pos {n m} (zx : ZX n m) : 
  (0 < zx_structural_weight zx)%nat.
Proof.
  pose proof (zx_structural_weight_gt_dimsum zx); lia.
Qed.

Lemma iter_S {A} (n : nat) (f : A -> A) (a : A) : 
  iter A (S n) f a = iter A n f (f a).
Proof.
  induction n; easy + simpl.
  now rewrite <- IHn.
Qed.

Lemma iter_fix {A} {n : nat} (f : A -> A) (a : A)
  (Ha : f a = a) : iter A n f a = a.
Proof.
  induction n; easy + now rewrite iter_S, Ha.
Qed.

Lemma zx_structural_weight_fixpoint_termination 
  (f : forall {n m} (zx : ZX n m), ZX n m) 
  (fdec_or_fix : forall {n m} (zx : ZX n m),
    ((zx_structural_weight (f zx)) < (zx_structural_weight zx))%nat \/
    (f zx = zx)) : forall {n m} (zx : ZX n m),
    let res := iter (ZX n m) (zx_structural_weight zx) (@f n m) zx in 
    f (res) = res.
Proof.
  intros n m zx.
  remember (zx_structural_weight zx) as k.
  assert (Hle: (zx_structural_weight zx <= k)%nat) by lia.
  clear Heqk.
  revert n m zx Hle.
  induction k.
  - simpl.
    intros n m zx HeqkHle.
    destruct (fdec_or_fix n m zx); [lia | easy].
  - intros n m zx Hle.
    rewrite iter_S.
    destruct (fdec_or_fix n m zx) as [Hdec | Hfix].
    + apply IHk; lia.
    + rewrite Hfix, iter_fix by easy.
      apply Hfix.
Qed.

Local Arguments cast : simpl never.

Lemma func_remove_nwire_dec_or_fix {n m} (zx : ZX n m) :
  (zx_structural_weight (func_remove_nwire zx) < zx_structural_weight zx)%nat 
  \/ func_remove_nwire zx = zx.
Proof.
  induction zx; try (right; easy).
  - simpl.
    destruct IHzx1, IHzx2; (left; 
    try replace -> (func_remove_nwire zx1);
    try replace -> (func_remove_nwire zx2); lia) || right; now f_equal.
  - simpl.
    destruct (bool_dec (is_n_wire zx1) true) as [H1wire | H1notwire].
    + left; rewrite fn_cast_eq_fn.
      pose proof (zx_structural_weight_pos zx1);
      destruct IHzx2 as [Hlt | Heq]; try rewrite Heq; lia.
    + destruct (bool_dec (is_n_wire zx2) true) as [H2wire | H2notwire].
      * left; rewrite fn_cast_eq_fn.
        pose proof (zx_structural_weight_pos zx2);
        destruct IHzx1 as [Hlt | Heq]; try rewrite Heq; lia.
      * destruct IHzx1, IHzx2; 
        (right; f_equal; assumption) || 
        left; simpl;
        try replace -> (func_remove_nwire zx1);
        try replace -> (func_remove_nwire zx2); lia.
Qed.





Ltac eval_create_arbitrary_swap :=
  unfold create_arbitrary_swap, 
    PermToZX.zx_between_lists_casted, 
    PermToZX.zx_between_lists,
    ZXperm.zx_of_perm;
  simpl;
  unfold ZXperm.zx_to_bot, a_swap, bottom_to_top;
  simpl.

Ltac remove_wires := 
  rewrite ?wire_removal_l, ?wire_removal_r;
  rewrite wire_to_n_wire;
  repeat rewrite ?n_wire_stack, 
  ?nwire_removal_l, ?nwire_removal_r.

Local Definition stack_empty_r' {n m} (zx : ZX n m) :=
  stack_empty_r zx (Nat.add_0_r n) (Nat.add_0_r m).

Ltac eval_create_arbitrary_swap' :=
  eval_create_arbitrary_swap;
  rewrite ?stack_empty_l, ?stack_empty_r';
  rewrite ?PermutationAutomation.cast_id_eq.
  (* cleanup_zx; *)
  (* simpl_casts; *)
  (* remove_wires. *)

(* Paste these examples into the ZX visualizer once simplified, equivs are clearly not true just to make a prop *)
Example bubblesort_test0 : (create_arbitrary_swap [1%nat;2%nat;3%nat] [3%nat;2%nat;1%nat]) ∝ n_wire 3.
Proof.
  eval_create_arbitrary_swap'.
  remove_wires.
Abort.

Example bubblesort_test1 : (create_arbitrary_swap [] []) ∝ n_wire 0.
Proof.
  eval_create_arbitrary_swap'.
  easy.
Qed.

Example bubblesort_test2 : (create_arbitrary_swap [1%nat] [1%nat]) ∝ n_wire 1.
Proof.
  eval_create_arbitrary_swap'.
  remove_wires.
  easy.
Qed.

Example bubblesort_test3 : (create_arbitrary_swap [1%nat;7%nat;9%nat;3%nat] [3%nat;1%nat;9%nat;7%nat]) ∝ n_wire 4.
Proof.
  eval_create_arbitrary_swap'.
  remove_wires.
Abort.



(* Semantic proof section here *)


(* Full translation *)

(* ZX Digraph input type *)

Inductive zx_color : Type :=
  | X_typ
  | Z_typ
.

Record zx_node := mk_node
{ id_no : nat;
  color : zx_color;
  angle : R 
}.

Definition dummy_node := (mk_node 0%nat X_typ R0). 

Inductive zx_output_node : nat -> Type :=
  | Outp (n : nat) : zx_output_node n.

(* Inputs, outputs, and nodes are all disjoint, with unique nat assignments *)
(* Mapping corresponds to nodes exactly with id_no information lining up *)
(* EDGE RULES HERE *)
Record zx_graph := mk_graph
{ mapping : list zx_node;
  inputs : list nat;
  outputs : list nat;
  nodes : list nat;
  edges : list (nat * nat)
}.


Definition get_zx_node_by_id_old (G : zx_graph) (n : nat) : zx_node :=
  match (find (fun node => (id_no node) =? n) (mapping G)) with
  | Some x => x
  | _ => dummy_node (* Could change this*)
  end.

Definition get_zx_node_by_id (G : zx_graph) (n : nat) : option zx_node :=
  (find (fun node => (id_no node) =? n) (mapping G)).
  
Definition inb_zx_edge_list (l : list (nat * nat)) (e : nat * nat) : bool :=
  match e with
  | (e1, e2) => 
    match (find 
      (fun e' => ((fst e' =? e1) && (snd e' =? e2)) 
              || ((snd e' =? e1) && (fst e' =? e2))) l) with
    | Some _ => true
    | _ => false
    end
  end.


Definition inb_zx_node_list (l : list nat) (x : nat) : bool :=
  if (in_dec Nat.eq_dec x l) then true else false.

Fixpoint remove_one {A} (eq_dec : (forall x y : A, {x = y}+{x <> y})) 
  (x : A) (l : list A) : list A := 
  match l with
      | [] => []
      | x'::xs => if (eq_dec x x') then xs else x'::(remove_one eq_dec x xs)
  end.

Definition flatten_list_of_pairs {A} (l : list (A * A)) : list A :=
  fold_right 
    (fun e es => match e with (e1, e2) => e1::e2::es end)
    []
    l. 

Definition join_list_partition {A} (l : list A * list A) : list A :=
  fst l ++ snd l.

(*  Given two lists, lsplit (list to be split), and lpool, returns 
    a pair of lists, the left list is elements of lsplit that are in lpool
    , and the right is those that are not. This accounts for duplicates,
    so its like subtracting lpool from lsplit *)
Fixpoint largest_subset_and_rest_split (lsplit lpool : list nat) 
    : list nat * list nat  :=
  match lsplit with
  | [] => ([], [])
  | x::xs => 
    if (inb_zx_node_list lpool x) then 
      match (largest_subset_and_rest_split xs 
              (remove_one Nat.eq_dec x lpool)) with
      | (l1, l2) => (x :: l1, l2)
      end
    else
      match (largest_subset_and_rest_split xs lpool) with
      | (l1, l2) => (l1, x::l2)
      end
  end.

(* Test more? *)
(* Compute (largest_subset_and_rest_split [1%nat; 2%nat; 3%nat; 4%nat; 4%nat] [4%nat; 5%nat; 4%nat; 3%nat]). *)


Definition get_connections (G : zx_graph) (node : nat) : list (nat * nat) :=
  filter (fun n => orb (node =? (fst n)) (node =? (snd n))) (edges G).

Definition get_neighbors (G : zx_graph) (node : nat) : list nat :=
  map (fun n => if ((fst n) =? node) then (snd n) else fst n) (get_connections G node).


Definition partition_self_edges (G : zx_graph) : list (nat * nat) * list (nat * nat) :=
  partition (fun n => ((fst n) =? (snd n))) (edges G).


Definition get_self_edges (G : zx_graph) : list (nat * nat) :=
  fst (partition_self_edges G).


Definition removed_self_edges (G : zx_graph) : list (nat * nat) :=
  snd (partition_self_edges G).

Definition get_edges_within_boundary_state (G : zx_graph) (b_state : list nat) : list (nat * nat) :=
  filter (fun e => match e with (e1, e2) => 
    (inb_zx_node_list b_state e1) && (inb_zx_node_list b_state e2) end) (edges G).

Definition get_input_state_loops_unflattened (G : zx_graph) : list nat * list nat :=
    (largest_subset_and_rest_split
      (inputs G)
      (flatten_list_of_pairs (get_edges_within_boundary_state G (inputs G)))).

Definition get_output_state_loops_unflattened (G : zx_graph) : list nat * list nat :=
    (largest_subset_and_rest_split
      (outputs G)
      (flatten_list_of_pairs (get_edges_within_boundary_state G (outputs G)))).

Definition get_input_state_cleaned (G : zx_graph) : list nat :=
  snd
    (largest_subset_and_rest_split
      (inputs G)
      (flatten_list_of_pairs (get_edges_within_boundary_state G (inputs G)))).

Definition get_output_state_cleaned (G : zx_graph) : list nat :=
  snd
    (largest_subset_and_rest_split
      (outputs G)
      (flatten_list_of_pairs (get_edges_within_boundary_state G (outputs G)))).

Definition get_input_state_loops_ordered (G : zx_graph) : list nat :=
  let es := (get_edges_within_boundary_state G (inputs G)) in
    (flatten_list_of_pairs es) ++ (get_input_state_cleaned G).

Definition get_output_state_loops_ordered (G : zx_graph) : list nat :=
  let es := (get_edges_within_boundary_state G (outputs G)) in
  (flatten_list_of_pairs es) ++ (get_output_state_cleaned G).

(* Check on pair order here *)
Definition distribute_inputs_outputs (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat * list nat :=
  largest_subset_and_rest_split (get_neighbors G cur_node) cur_state.

Definition get_cur_inputs (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  fst (distribute_inputs_outputs G cur_state cur_node).

Definition get_cur_outputs (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  snd (distribute_inputs_outputs G cur_state cur_node).

Definition split_cur_state (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat * list nat :=
  largest_subset_and_rest_split cur_state (get_cur_inputs G cur_state cur_node).

Definition get_goal_ordering (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  join_list_partition (split_cur_state G cur_state cur_node).

Definition get_cur_inputs_in_state (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  fst (split_cur_state G cur_state cur_node).

Definition get_rest_cur_state (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  snd (split_cur_state G cur_state cur_node).

Definition get_new_state (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  (repeat cur_node (length (get_cur_outputs G cur_state cur_node))) ++ 
  (get_rest_cur_state G cur_state cur_node).


Lemma largest_subset_and_rest_split_length : 
  forall lsplit lpool l1 l2,
  largest_subset_and_rest_split lsplit lpool = (l1, l2) ->
  length lsplit = ((length l1) + (length l2))%nat.
Proof.
  induction lsplit; intros.
    - inversion H; easy.
    - simpl; simpl in H; destruct (inb_zx_node_list lpool a).
      + destruct (largest_subset_and_rest_split lsplit (remove_one Nat.eq_dec a lpool)) eqn: E; inversion H;
        simpl; f_equal; eapply (IHlsplit (remove_one Nat.eq_dec a lpool) l l2); subst; exact E.
      + destruct (largest_subset_and_rest_split lsplit lpool) eqn:E; inversion H; simpl; subst;
        rewrite Nat.add_comm; simpl; f_equal; rewrite Nat.add_comm; eapply IHlsplit; exact E.
Defined.

Lemma build_node_structure_aux : forall G (cur_state : list nat) cur_node, 
  length cur_state = ((length (get_cur_inputs_in_state G cur_state cur_node)) + (length (get_rest_cur_state G cur_state cur_node)))%nat.
Proof.
  intros; unfold get_rest_cur_state, get_cur_inputs_in_state, split_cur_state.
  destruct (largest_subset_and_rest_split cur_state (get_cur_inputs G cur_state cur_node)) eqn:E.
  eapply largest_subset_and_rest_split_length; simpl; exact E.
Qed.

(* Check that this swap is correct *)
Definition build_swap_structure (G : zx_graph) (cur_state : list nat) (cur_node : nat) : ZX (length cur_state) (length cur_state) :=
  create_arbitrary_swap cur_state (get_goal_ordering G cur_state cur_node).

Definition zx_node_id_to_spider_aux_old (G : zx_graph) (id_no n m : nat) : ZX n m :=
  let node := (get_zx_node_by_id_old G id_no) in 
    match color node with 
    | X_typ => X_Spider n m (angle node)
    | _ => Z_Spider n m (angle node)
    end.

Definition zx_node_id_to_spider_aux (G : zx_graph) (id_no n m : nat) 
  : option (ZX n m) :=
  option_map (fun node =>
    match color node with 
    | X_typ => X_Spider n m (angle node)
    | _ => Z_Spider n m (angle node)
    end) (get_zx_node_by_id G id_no).


Fixpoint add_k_self_loops_to_spider {n m} (k : nat) 
  (cur : ZX (k + n) (k + m)) : ZX n m := 
  match k as k' return (ZX (k' + n) (k' + m) -> ZX n m) with
  | O => fun cur => cur
  | S k' => 
    fun cur => add_k_self_loops_to_spider k' 
      (⊂ ↕ (n_wire (k' + n)) ⟷ (— ↕ cur) ⟷ (⊃ ↕ (n_wire (k' + m))))
  end cur.
(* Proof.
  destruct k.
  - exact cur.
  - apply add_k_self_loops_to_spider with (k := k); eapply Compose.
    + exact (pad_bot (k + n) ⊂).
    + eapply Compose. assert (H : forall i, (2 + i = 1 + S (i))%nat). reflexivity.
      * eapply cast.
        { specialize H with (k + n)%nat; exact H. }
        { specialize H with (k + m)%nat; exact H. }
        { eapply Stack. eapply Wire. exact cur. }
      *  exact (pad_bot (k + m) ⊃).
Defined. *)

Definition get_self_edges_by_id (G : zx_graph) 
  (self_edges : list (nat * nat)) (id_no : nat) : list (nat * nat) :=
  filter (fun e => (fst e =? id_no)) self_edges.

(* Need to consider box edges? *)
Definition zx_node_id_to_spider (G : zx_graph) 
  (self_edges : list (nat * nat)) (id_no n m : nat) : option (ZX n m) :=
  let k := (length (get_self_edges_by_id G self_edges id_no)) in
  option_map (fun node => add_k_self_loops_to_spider k node)
      (zx_node_id_to_spider_aux G id_no (k + n) (k + m))%nat.


Definition build_node_structure (G : zx_graph) 
  (self_edges : list (nat * nat)) (cur_state : list nat) (cur_node : nat) : 
  option (ZX (length cur_state) ((length (get_cur_outputs G cur_state cur_node)) 
    + (length (get_rest_cur_state G cur_state cur_node)))) :=
  option_map (fun zx => 
    cast _ _ (build_node_structure_aux G cur_state cur_node) eq_refl
    (pad_bot (length (get_rest_cur_state G cur_state cur_node)) zx))
    (zx_node_id_to_spider G self_edges cur_node 
      (length (get_cur_inputs_in_state G cur_state cur_node))
      (length (get_cur_outputs G cur_state cur_node))).
(* Proof.
  intros; eapply cast.
  - exact (build_node_structure_aux G cur_state cur_node).
  - reflexivity.
  - exact (pad_bot 
    (length (get_rest_cur_state G cur_state cur_node))
    (zx_node_id_to_spider G self_edges cur_node 
      (length (get_cur_inputs_in_state G cur_state cur_node))
      (length (get_cur_outputs G cur_state cur_node)))).
Defined. *)

Definition one_node_translate (G : zx_graph) 
  (self_edges : list (nat * nat)) (cur_state : list nat) (cur_node : nat) : 
  option
  (ZX (length cur_state) ((length (get_cur_outputs G cur_state cur_node)) 
    + (length (get_rest_cur_state G cur_state cur_node)))) :=
  option_map (fun zx => (build_swap_structure G cur_state cur_node) ⟷ zx)
    (build_node_structure G self_edges cur_state cur_node). 


(* Dummys could be replaced *)
Definition dummy_spider (n m : nat) : ZX n m := X_Spider n m R0.

Lemma build_n_capcup_pf (n : nat) : 
  ((S (n + (S n)) = (2 + (Nat.double n)))%nat).
Proof.
  unfold Nat.double.
  lia.
Qed.

Fixpoint build_n_capcup (n : nat) (cup : bool) : 
  ZX (if cup then Nat.double n else 0) (if cup then 0 else Nat.double n) :=
  match n as n' return 
    ZX (if cup then Nat.double n' else 0) (if cup then 0 else Nat.double n')
    with
  | O => match cup as b return 
    ZX (if b then Nat.double 0 else 0) (if b then 0 else Nat.double 0)
    with
    | true => Empty
    | false => Empty
    end
  | S n' => match cup as b return 
    ZX  (if b then Nat.double (S n') else 0) (if b then 0 else Nat.double (S n'))
    with
    | true => cast _ _ (build_n_capcup_pf n') eq_refl 
                (⊃ ↕ (build_n_capcup n' true))
    | false => cast _ _ eq_refl (build_n_capcup_pf n') 
                (⊂ ↕ (build_n_capcup n' false))
    end
  end.
(* Proof.
  assert (Htemp : forall n, ((S (n + (S n)) = (2 + (Nat.double n)))%nat)). 
  intros; unfold Nat.double in *; lia.
  induction n; destruct cup eqn:Ec; unfold Nat.double in *.
  - exact Empty.
  - exact Empty. 
  - simpl; eapply cast.
    + exact (Htemp n).
    + exact (eq_sym (Nat.add_0_r (0%nat))).
    + eapply Stack.
      * eapply Cup.
      * exact (build_n_capcup n true).
  - simpl; eapply cast.
    + exact (eq_sym (Nat.add_0_r (0%nat))).
    + exact (Htemp n).
    + eapply Stack.
      * eapply Cap.
      * exact (build_n_capcup n false).
Defined. *)

Lemma remove_loops_from_output_aux_aux : forall G (loops outps : list nat), 
  (get_output_state_loops_unflattened G) = (loops, outps) -> 
  (length (outputs G)) = ((length loops) + (length outps))%nat.
Proof.
  intros. 
  unfold get_output_state_loops_unflattened in H. 
  apply (largest_subset_and_rest_split_length) with (lpool :=  (flatten_list_of_pairs
  (get_edges_within_boundary_state G (outputs G)))); exact H.
Qed.

Definition remove_loops_from_output_aux (G : zx_graph) (n m halfn : nat) 
  (Heven : n = (Nat.double halfn)%nat) : 
  ZX m (n + m) :=
  (cast _ _ eq_refl Heven (build_n_capcup halfn false)) ↕ n_wire m.
(* Proof.
  eapply cast.
    - assert (H :  m = (0 + m)%nat). reflexivity. exact H.
    - reflexivity.
    - eapply Stack.
      * eapply cast.
        { reflexivity. }
        { exact Heven. }
        { exact (build_n_capcup halfn false). }
      * exact (n_wire m).
Defined. *)

Lemma even_explicit_div2 : forall n m, 
  Nat.even n = true -> m = div2 n -> n = (Nat.double m)%nat.
Proof.
  intros; apply Nat.even_spec in H; subst; eapply Nat.Even_double; easy.
Qed.

Lemma length_get_output_state_loops_eq_length_outputs (G : zx_graph) :
  length (get_output_state_loops_ordered G) = length (outputs G).
Proof.
  unfold get_output_state_loops_ordered.
  unfold get_output_state_cleaned.
  destruct G as [mapp inpts outpts nods edgs].
  simpl.
  unfold get_output_state_cleaned.
  simpl.
  induction outpts.
  - simpl.
    unfold get_edges_within_boundary_state.
    simpl.
    induction edgs; [easy|];
    simpl;
    destruct a;
    easy.
  - simpl.
    unfold get_edges_within_boundary_state in *.
    simpl in *.
    destruct (inb_zx_node_list
    (flatten_list_of_pairs
       (filter
          (fun e : nat * nat =>
           let (e1, e2) := e in
           inb_zx_node_list (a :: outpts) e1 &&
           inb_zx_node_list (a :: outpts) e2) edgs))
    a) eqn:E.
    + destruct (largest_subset_and_rest_split outpts
    (remove_one Nat.eq_dec a
       (flatten_list_of_pairs
          (filter
             (fun e : nat * nat =>
              let (e1, e2) := e in
              inb_zx_node_list (a :: outpts) e1 &&
              inb_zx_node_list (a :: outpts) e2)
             edgs)))) eqn:Els.

    
  match goal with 
  |- context[get_edges_within_boundary_state ?G ?o] => 
    generalize (get_edges_within_boundary_state G o)
  end.
  (* TODO: add WF to make this true*)

  generalize (outputs G).
  intros l.
  induction l.
  - cbn.

Definition remove_loops_from_output (G : zx_graph) : 
  option (ZX (length (get_output_state_cleaned G)) (length (outputs G))).
(* refine (
  let (loops, outps) := get_output_state_loops_unflattened G in
  match bool_dec (Nat.even (length loops)) true with
  | left Eeven =>
    Compose 
      (cast _ _ 
        _
        (remove_loops_from_output_aux_aux G loops outps eq_refl)
        (remove_loops_from_output_aux G (length loops) (length outps) halfn
              (even_explicit_div2 (length loops) halfn Eeven Heqhalfn)))
      ()
  | right Eeven 
). *)
Proof.
  destruct (get_output_state_loops_unflattened G) as [loops outps] eqn:Eoutps; 
  destruct (Nat.even (length loops)) eqn:Eeven;
    remember (div2 (length loops)) as halfn.
  - eapply Some.
    eapply Compose.
    +  eapply cast.
      * unfold get_output_state_cleaned; unfold get_output_state_loops_unflattened in Eoutps;
        destruct (largest_subset_and_rest_split (outputs G)
          (flatten_list_of_pairs
          (get_edges_within_boundary_state G (outputs G)))); 
          simpl; inversion Eoutps; reflexivity.
      * apply remove_loops_from_output_aux_aux; exact Eoutps.
      * exact (remove_loops_from_output_aux G (length loops) (length outps) halfn
              (even_explicit_div2 (length loops) halfn Eeven Heqhalfn)).
    + destruct (eq_nat_decide (length (get_output_state_loops_ordered G)) (length (outputs G))) as [L|R]. 
      apply _eq_nat_eq in L; eapply cast.
      * exact (eq_sym L).
      * exact (eq_sym L).
      * exact (create_arbitrary_swap (get_output_state_loops_ordered G) (outputs G)).
      * (* Another dummy case*) apply dummy_spider.
  - (* dummy case, there would always be an even number here *)
    apply dummy_spider.
Defined.

Definition gtb_last_fence_post (G : zx_graph) (cur_state : list nat) : ZX (length cur_state) (length (outputs G)).
Proof.
  eapply Compose.
  - exact (create_arbitrary_swap cur_state (get_output_state_cleaned G)).
  - destruct (eq_nat_decide (length cur_state) (length (get_output_state_cleaned G))) as [L | R].
    + eapply cast.
      * exact (_eq_nat_eq (length cur_state) (length (get_output_state_cleaned G)) L).
      * reflexivity.
      * exact (remove_loops_from_output G).
    (* Dummy output below *)
    + apply dummy_spider.
Defined.

(* Remove rewrites? *)
Lemma graph_to_block_structure_aux_aux : 
  forall G cur_state cur_node, (length (get_new_state G cur_state cur_node) = (length (get_cur_outputs G cur_state cur_node) + length (get_rest_cur_state G cur_state cur_node)))%nat.
Proof.
  intros; unfold get_new_state.
  rewrite app_length; rewrite repeat_length; easy.
Qed.

Fixpoint graph_to_block_structure_aux (G : zx_graph) (node_order : list nat) (cur_state : list nat) (self_edges : list (nat * nat)) : 
  ZX (length cur_state) (length (outputs G)).
Proof.
  destruct node_order as [| cur_node ns] eqn:E.
  - exact (gtb_last_fence_post G cur_state).
  - eapply Compose.
    + exact (one_node_translate G self_edges cur_state cur_node).
    + eapply cast.
      * exact (eq_sym (graph_to_block_structure_aux_aux G cur_state cur_node)). 
      * reflexivity.
      * exact (graph_to_block_structure_aux G ns (get_new_state G cur_state cur_node) self_edges).
Defined.

Lemma remove_loops_from_input_aux_aux : forall G (loops inpts : list nat), 
  (get_input_state_loops_unflattened G) = (loops, inpts) -> 
  (length (inputs G)) = ((length loops) + (length inpts))%nat.
Proof.
  intros. 
  unfold get_input_state_loops_unflattened in H. 
  apply (largest_subset_and_rest_split_length) with (lpool := (flatten_list_of_pairs
  (get_edges_within_boundary_state G (inputs G)))); exact H.
Defined.

Definition remove_loops_from_input_aux (G : zx_graph) (n m halfn : nat) (Heven : n = (Nat.double halfn)%nat) : 
  ZX (n + m) m.
Proof.
  eapply cast.
    - reflexivity.
    - assert (H :  m = (0 + m)%nat). reflexivity. exact H.
    - eapply Stack.
      * eapply cast.
        { exact Heven. }
        { reflexivity. }
        { exact (build_n_capcup halfn true). }
      * exact (n_wire m).
Defined.

Definition remove_loops_from_input (G : zx_graph) : ZX (length (inputs G)) (length (get_input_state_cleaned G)) .
Proof.
  destruct (get_input_state_loops_unflattened G) as [loops inpts] eqn:Einpts; 
  destruct (Nat.even (length loops)) eqn:Eeven; remember (div2 (length loops)) as halfn.
  - eapply Compose.
    + exact (create_arbitrary_swap (inputs G) (get_input_state_loops_ordered G)).
    + eapply cast.
      * apply remove_loops_from_input_aux_aux; exact Einpts.
      * unfold get_input_state_cleaned; unfold get_input_state_loops_unflattened in Einpts;
        destruct (largest_subset_and_rest_split (inputs G)
          (flatten_list_of_pairs
          (get_edges_within_boundary_state G (inputs G)))); 
          simpl; inversion Einpts; reflexivity.
      * exact (remove_loops_from_input_aux G (length loops) (length inpts) halfn
              (even_explicit_div2 (length loops) halfn Eeven Heqhalfn)).
  - (* dummy case, there would always be an even number here *)
    apply dummy_spider.
Defined.

(* Translation function *)
Definition graph_to_block_structure (G : zx_graph) : ZX (length (inputs G)) (length (outputs G)) :=
  let G' := mk_graph (mapping G) (inputs G) (outputs G) (nodes G) (removed_self_edges G) in
    (remove_loops_from_input G') ⟷
    graph_to_block_structure_aux G' (nodes G') (get_input_state_cleaned G') (get_self_edges G).

Local Hint Unfold 
  graph_to_block_structure 
  remove_loops_from_input
  remove_loops_from_input_aux
  graph_to_block_structure_aux 
  get_edges_within_boundary_state
  get_input_state_loops_unflattened
  get_input_state_cleaned
  get_input_state_loops_ordered
  gtb_last_fence_post
  get_output_state_loops_unflattened
  get_output_state_cleaned
  get_output_state_loops_ordered
  build_n_capcup
  Nat.double
  one_node_translate
  build_node_structure
  build_swap_structure
  zx_node_id_to_spider
  get_self_edges_by_id
  add_k_self_loops_to_spider
  zx_node_id_to_spider_aux
  get_new_state
  get_rest_cur_state
  get_cur_inputs_in_state
  get_goal_ordering
  split_cur_state
  get_cur_outputs
  get_cur_inputs
  distribute_inputs_outputs
  removed_self_edges
  get_self_edges
  partition_self_edges
  get_neighbors
  get_connections
  remove_loops_from_output
  remove_loops_from_output_aux
  inb_zx_node_list
  : graph_translate_eval_db.

Ltac eval_graph_translation :=
  try (
    repeat(
    autounfold with graph_translate_eval_db;
    simpl);
    simpl_casts;
    cleanup_zx;
    simpl)
  .
(* Need to update tactic, include bubble_sort evaluation tactic *)

Definition node0 := mk_node 9%nat X_typ R0.
Definition node1 := mk_node 4%nat X_typ R1.
Definition node2 := mk_node 5%nat X_typ PI.
Definition node4 := mk_node 4%nat X_typ R0.
Definition node5 := mk_node 5%nat X_typ R0.
Definition node6 := mk_node 6%nat X_typ R0.
Definition node7 := mk_node 7%nat Z_typ R0.
Definition node8 := mk_node 8%nat Z_typ R0.
Definition node9 := mk_node 9%nat Z_typ R0.



(* inputs and outputs are just nat ids as well *)
Definition test0 := mk_graph
  [node0] 
  [0%nat]
  [1%nat]
  [4%nat]
  [(0%nat, 4%nat); (4%nat, 4%nat); (4%nat, 4%nat); (4%nat, 1%nat)].

Definition test1 := mk_graph
  [node1; node2] 
  [1%nat; 0%nat]
  [2%nat; 3%nat]
  [4%nat; 5%nat]
  [(0%nat, 4%nat); (1%nat, 5%nat); (4%nat, 3%nat); (5%nat, 2%nat)].

(* Compute (get_zx_node_by_id test1 5%nat). *)

Definition test2 := mk_graph
  [node4; node5; node6; node7; node8; node9]
  [0%nat; 1%nat]
  [2%nat; 3%nat]
  [4%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat]
  [(0%nat, 7%nat); (7%nat, 4%nat); (7%nat, 5%nat); (4%nat, 0%nat); (4%nat, 8%nat);
   (5%nat, 8%nat); (5%nat, 9%nat); (6%nat, 8%nat); (6%nat, 9%nat); (6%nat, 2%nat);
   (9%nat, 3%nat)].

Definition test3 := mk_graph
  [node8]
  [0%nat; 1%nat; 2%nat; 3%nat]
  [4%nat; 5%nat; 6%nat; 7%nat]
  [8%nat]
  [(0%nat, 2%nat); (4%nat, 7%nat); (1%nat, 6%nat); (3%nat, 8%nat); (8%nat, 5%nat)].

(* Need to account for even predicate in simplifying *)

(* Compute ((graph_to_block_structure test3)). *)

Example see_if_algo_works1 : 
  (graph_to_block_structure test1) ∝ n_wire _.
Proof.
Abort.