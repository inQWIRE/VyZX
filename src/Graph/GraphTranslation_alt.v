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

Module GraphToDiagram_prelim.

Export PermToZX.

Notation edge := (prod nat nat).

Notation count_nat := (count_occ Nat.eq_dec).

Lemma nat_eq_dec_eq {m n : nat} (H : m = n) : 
  Nat.eq_dec m n = left H.
Proof.
  destruct (Nat.eq_dec m n); [|easy].
  f_equal.
  apply UIP_nat.
Qed.

Record zxnode := mk_zxnode {
  node_typ : bool;
  node_rot : R;
}.

Definition ZX_of_zxnode (zx : zxnode) (m n : nat) : ZX m n :=
  if node_typ zx 
  then X_Spider m n (node_rot zx) 
  else Z_Spider m n (node_rot zx).

Open Scope nat_scope.


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

Fixpoint filter_key {A B} (f : A -> bool) (l : list A) (l' : list B) 
  : list (A*B) :=
  match l, l' with
  | [], _ => []
  | _, [] => []
  | a :: ls, b :: ls' =>
    (if f a then [(a,b)] else []) ++ filter_key f ls ls'
  end.

Lemma len_filter_key {A B} (f : A -> bool) (l : list A) (l' : list B) :
  length (fst (split (filter_key f l l'))) 
  = length (snd (split (filter_key f l l'))).
Proof.
  rewrite split_length_r, split_length_l; easy.
Qed.

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

Definition get_zxnode_by_id (nodeids : list nat)
  (nodevals : list zxnode) (n : nat) : option zxnode :=
  match (index_of_err (eqb n) nodeids) with
  | Some n' => nth_error nodevals n'
  | None => None
  end.

Definition star_no_self (edges : list edge) (vtx : nat) : list edge :=
  filter (fun e => pair_degree vtx e =? 1) edges.

Definition neighborhood_no_self (edges : list edge) (vtx : nat) : list nat :=
  map (fun e : edge => match e with 
  | (e1, e2) => if vtx =? e1 then e2 else e1
  end) (star_no_self edges vtx).

Lemma neighborhood_no_self_not_In (edges : list edge) (vtx : nat) : 
  ~ In vtx (neighborhood_no_self edges vtx).
Proof.
  unfold neighborhood_no_self.
  induction edges as [|[a1 a2] es IHes]; [easy|].
  simpl.
  bdestruct (vtx =? a1); 
  bdestruct (vtx =? a2); 
  try apply IHes;
  simpl;
  bdestruct_all;
  (intros [Heq | Hind];
  [congruence | apply IHes, Hind]).
Qed.

Definition inputs_of_right_truncate (inputs : list nat) (v : nat) : list nat :=
  filter (fun k => ¬ v =? k) inputs.

Definition outputs_of_right_truncate (edges : list edge) (outputs : list nat)
  (v : nat) : list nat :=
  neighborhood_no_self edges v 
  ++ filter (fun k => ¬ v =? k) outputs.

Definition edges_of_right_truncate (edges : list edge) (v : nat) : list edge :=
  filter (fun e => pair_degree v e =? 0) edges.

Definition nodeidsvals_of_right_truncate (nodeids : list nat)
  (nodevals : list zxnode) (v : nat) : list (nat * zxnode) :=
  filter_key (fun k => ¬ v =? k) nodeids nodevals.

Definition nodeids_of_right_truncate (nodeids : list nat)
  (nodevals : list zxnode) (v : nat) : list nat :=
  fst (split (nodeidsvals_of_right_truncate nodeids nodevals v)).

Definition nodevals_of_right_truncate (nodeids : list nat)
  (nodevals : list zxnode) (v : nat) : list zxnode :=
  snd (split (nodeidsvals_of_right_truncate nodeids nodevals v)).

Definition num_ids_of_right_truncate (num_ids : nat) 
  (inputs : list nat) (v : nat) :=
  num_ids + count_occ Nat.eq_dec inputs v.


Lemma length_nodeids_nodes_right_truncate nodeids nodevals (v : nat) : 
  length (nodeids_of_right_truncate nodeids nodevals v) 
  = length (nodevals_of_right_truncate nodeids nodevals v).
Proof.
  apply len_filter_key.
Qed.

Lemma fst_split_app {A B} (l l' : list (A*B)) : 
  fst (split (l ++ l')) = fst(split l) ++ fst(split l').
Proof.
  induction l as [|[a b] l IHl]; [easy|].
  simpl.
  rewrite (surjective_pairing (split (l ++ l'))).
  rewrite (surjective_pairing (split l)).
  rewrite IHl.
  easy.
Qed.

Lemma In_fst_filter_key {A B} (f : A -> bool) (l : list A) (l' : list B)
  (a : A) : 
  In a (fst (split (filter_key f l l'))) -> 
  In a l.
Proof.
  revert l';
  induction l as [|a' l IHl]; [easy|];
  intros l'.
  simpl.
  destruct l' as [|b l']; [easy|].
  rewrite fst_split_app.
  destruct (f a'); [|intros H; right; eapply IHl, H].
  simpl.
  intros [Heq | Hin]; 
  [left; easy | right; eapply IHl, Hin].
Qed.

Lemma NoDup_filter_key {A B} (f : A -> bool) (l : list A) (l' : list B) 
  (Hl : NoDup l) :
  NoDup (fst (split (filter_key f l l'))).
Proof.
  revert l';
  induction l as [|a l IHl];
  intros l'; [constructor|].
  simpl.
  destruct l' as [|b l']; [constructor|].
  rewrite NoDup_cons_iff in Hl.
  destruct (f a); [|apply IHl, Hl].
  rewrite fst_split_app.
  simpl.
  apply NoDup_cons.
  - intros Hin; apply Hl, (In_fst_filter_key _ _ _ _ Hin).
  - apply IHl, Hl.
Qed.

Lemma NoDup_nodeids_right_truncate nodeids nodevals (v : nat) (H : NoDup nodeids) :
  NoDup (nodeids_of_right_truncate nodeids nodevals v).
Proof.
  apply NoDup_filter_key, H.
Qed.

Lemma fst_filter_key_length_le {A B} (f : A -> bool) (l : list A) (l' : list B) 
  (Hlen : (length l <= length l')%nat) :
  fst (split (filter_key f l l')) =
  filter f l.
Proof.
  revert l' Hlen;
  induction l as [|a l IHl]; [easy|];
  intros l' Hlen.
  simpl.
  destruct l' as [|b l']; [easy|].
  rewrite fst_split_app, IHl by (simpl in *; lia).
  destruct (f a); easy.
Qed.

Lemma in_fst_filter_key {A B} (f : A -> bool) (l : list A) (l' : list B) 
  (a : A) (Hin : In a l) (Hlen : length l = length l') :
  f a = true -> In a (fst (split (filter_key f l l'))).
Proof.
  rewrite fst_filter_key_length_le by lia.
  rewrite filter_In; easy.
Qed.

Lemma forall_in_nodeids_edges_right_truncate edges nodeids nodevals
  (v : nat) (Hlen : length nodeids = length nodevals) 
  (Hmem : Forall (fun e => 
    match e with
    | (e1, e2) => In e1 nodeids /\ In e2 nodeids
    end) edges): 
  Forall
  (fun e : edge =>
    match e with
    | (e1, e2) =>
        In e1 (nodeids_of_right_truncate nodeids nodevals v) 
        /\ In e2 (nodeids_of_right_truncate nodeids nodevals v)
    end)
  (edges_of_right_truncate edges v).
Proof.
  unfold nodeids_of_right_truncate, 
  nodeidsvals_of_right_truncate, edges_of_right_truncate.
  simpl.
  induction edges as [|[e1 e2] es IHes]; [constructor|].
  rewrite Forall_cons_iff in Hmem.
  simpl.
  bdestruct (v =? e1);
  bdestruct (v =? e2);
  try (apply IHes, Hmem).
  apply Forall_cons;
  [|apply IHes, Hmem].
  split; apply in_fst_filter_key; 
  try apply Hlen;
  try apply Hmem;
  bdestruct_all; easy.
Qed.

Lemma nodeids_of_right_truncate_eq nodeids nodevals (v : nat)
  (Hlen : length nodeids = length nodevals) : 
  nodeids_of_right_truncate nodeids nodevals v = 
  filter (fun k => ¬ v =? k) nodeids.
Proof.
  apply fst_filter_key_length_le.
  lia.
Qed.

Lemma forall_in_nodeids_inputs_outputs inputs outputs nodeids nodevals edges
  (v : nat) (Hlen : length nodeids = length nodevals) 
  (Hmem : Forall (fun e => 
    match e with
    | (e1, e2) => In e1 nodeids /\ In e2 nodeids
    end) edges)
  (Hin : Forall (fun k : nat => In k nodeids) (inputs ++ outputs)) : 
  Forall (fun k : nat => In k (nodeids_of_right_truncate nodeids nodevals v))
  (inputs_of_right_truncate inputs v 
  ++ outputs_of_right_truncate edges outputs v).
Proof.
  rewrite nodeids_of_right_truncate_eq by easy.
  unfold inputs_of_right_truncate, outputs_of_right_truncate.
  simpl.
  rewrite 2!Forall_app in *.
  rewrite 3!Forall_forall in *.
  destruct Hin as [Hin_in Hin_out].
  setoid_rewrite filter_In.
  split; [|split].
  1,3: intros x []; split; [auto|easy].
  induction edges as [|[e1 e2] es IHes]; [easy|].
  assert (Hind_es : (forall x : edge, In x es ->
    let (e1, e2) := x in In e1 nodeids /\ In e2 nodeids)) by
      (intros; apply Hmem; right; easy).
  specialize (IHes Hind_es).
  clear Hind_es.
  intros w.
  unfold neighborhood_no_self.
  simpl.
  rewrite if_dist.
  simpl.
  bdestruct (v =? e1); 
  bdestruct (v =? e2); simpl; subst; try apply IHes;
  specialize (Hmem (e1, e2) ltac:(left; easy));
  simpl in Hmem;
  (intros [Heq | Hin]; 
  [subst; split; [apply Hmem|bdestruct_all; easy]|]);
  apply IHes, Hin.
Qed.

Lemma nodeidsvals_of_right_truncate_not_In nodeids nodevals
  (vid : nat) (Hnin : ~ In vid nodeids) : 
  nodeidsvals_of_right_truncate nodeids nodevals vid = combine nodeids nodevals.
Proof.
  revert nodevals;
  induction nodeids as [|n ns IHns]; [easy|];
  intros nodevals.
  specialize (IHns (fun Hin => Hnin (or_intror Hin))).
  unfold nodeidsvals_of_right_truncate.
  simpl.
  destruct nodevals as [|v nvs]; [easy|].
  simpl in Hnin.
  bdestruct (vid =? n); [lia|].
  simpl.
  rewrite <- IHns.
  easy.
Qed.

Lemma nodeidsvals_of_right_truncate_hd nodeids nodevals 
  (vid : nat) (vnode : zxnode) : 
  NoDup (vid :: nodeids) ->
  nodeidsvals_of_right_truncate (vid::nodeids) (vnode::nodevals) vid 
  = combine nodeids nodevals.
Proof.
  intros Hdup.
  unfold nodeidsvals_of_right_truncate.
  simpl.
  bdestruct_all.
  simpl.
  rewrite NoDup_cons_iff in Hdup.
  apply nodeidsvals_of_right_truncate_not_In, Hdup.
Qed.

Definition nwire_cast {n n' : nat} (H : n = n') : ZX n n' :=
  cast n n' H eq_refl (n_wire n').


Fixpoint kth_occ (l : list nat) (k : nat) (v : nat) : nat :=
  match l with 
  | [] => 0
  | x :: ls =>
    match Nat.eq_dec x v with
    | left Heq => 
        match k with
        | 0 => 0
        | S k' => S (kth_occ ls k' v)
        end
    | right Hneq =>
        S (kth_occ ls k v)
    end
  end.

Lemma filter_of_map {A B} (f : B -> bool) (g : A -> B) (l : list A) :
  filter f (map g l) = map g (filter (fun a => f (g a)) l).
Proof.
  induction l; [easy|].
  simpl.
  rewrite IHl.
  destruct (f (g a)); easy.
Qed.

Lemma kth_occ_eq (l : list nat) (k : nat) (v : nat) :
  kth_occ l k v =
  nth 
    k 
    (filter 
      (fun idx => nth idx l (S v) =? v) 
      (seq 0 (length l))) 
    (length l).
Proof.
  revert k;
  induction l; [destruct k; easy|].
  intros k.
  simpl.
  destruct (Nat.eq_dec a v) as [Heq | Hneq];
  bdestruct_all.
  - rewrite <- seq_shift, filter_of_map.
    destruct k; [easy|].
    simpl.
    rewrite map_nth.
    f_equal.
    apply IHl.
  - rewrite <- seq_shift, filter_of_map, map_nth.
    f_equal.
    apply IHl.
Qed.

(* Lemma kth_occ_0 (l : list nat) (v : nat) : 
  kth_occ l 0 v  *)

(* Lemma nth_kth_occ (l : list nat) (k : nat) (v : nat) :
  nth (kth_occ l k v) l v = v.
Proof.
  rewrite kth_occ_eq.
  revert k;
  induction l; [destruct k; easy|].
  intros k.
  simpl.
  bdestruct_all.
  - destruct k; [easy|].
    simpl.

  induction k.
  - induction l.
  match k with 
  match count_occ  *)

Fixpoint nth_neq (idx : nat) (l : list nat) (v : nat) (def : nat) : nat :=
  match l with
  | [] => def
  | x :: ls => 
    match Nat.eq_dec x v with
    | left Heq => nth_neq idx ls v def
    | right Hneq => match idx with
      | 0 => x
      | S idx' => nth_neq idx' ls v def
      end
    end
  end.

Definition bring_to_front_invperm (l : list nat) (v : nat) : nat -> nat :=
  fun k =>
    if k <? count_occ Nat.eq_dec l v
    then kth_occ l k v
    else nth_neq k l v k.

Definition bring_to_front_perm (l : list nat) (v : nat) : nat -> nat :=
  fun k =>
  if k <? length l then
    match Nat.eq_dec (nth k l (S v)) v with
    | left Heq => 
      count_occ Nat.eq_dec (firstn k l) v
    | right Hneq =>
      count_occ Nat.eq_dec (skipn k l) v + k
    end
  else k.

Lemma bring_to_front_perm_WF (l : list nat) (v : nat) :
  forall k, length l <= k -> 
  bring_to_front_perm l v k = k.
Proof.
  intros; unfold bring_to_front_perm; bdestruct_all; lia.
Qed.

Lemma bring_to_front_perm_0 (l : list nat) (v a : nat) : 
  bring_to_front_perm (a :: l) v 0 = 
  if Nat.eq_dec a v then 0 else count_nat l v.
Proof.
  unfold bring_to_front_perm.
  simpl. 
  destruct (Nat.eq_dec a v); lia.
Qed.

Lemma bring_to_front_perm_hd (l : list nat) (v a k : nat) : 
  bring_to_front_perm (a :: l) v (S k) = 
  if k <? length l then
  (if (Nat.eq_dec a v) 
  then S (bring_to_front_perm l v k)
  else 
    if (Nat.eq_dec (nth k l (S v)) v) 
    then bring_to_front_perm l v k
    else S (bring_to_front_perm l v k)
  )
  else (S k).
Proof.
  unfold bring_to_front_perm.
  simpl.
  destruct (Nat.eq_dec a v);
  destruct (Nat.eq_dec (nth k l (S v)) v); 
  bdestruct_all; easy.
Qed.

Lemma bring_to_front_perm_hd' (l : list nat) (v a k : nat) : 
  bring_to_front_perm (a :: l) v (S k) = 
  if k <? length l then
  (if (¬ a =? v) && (nth k l (S v) =? v) 
    then bring_to_front_perm l v k
    else S (bring_to_front_perm l v k))
  else (S k).
Proof.
  rewrite bring_to_front_perm_hd.
  destruct (Nat.eq_dec a v), (Nat.eq_dec (nth k l (S v)) v);
  bdestruct_all; simpl; lia.
Qed.

Lemma bring_to_front_not_In (l : list nat) (v : nat) (Hv : ~ In v l) :
  forall k, bring_to_front_perm l v k = k.
Proof.
  induction l; [easy|].
  intros k.
  simpl in Hv.
  specialize (IHl (fun k => Hv (or_intror k))).
  destruct k.
  - rewrite bring_to_front_perm_0.
    destruct (Nat.eq_dec a v); [easy|].
    apply count_occ_not_In.
    auto. 
  - rewrite bring_to_front_perm_hd.
    destruct (Nat.eq_dec a v); [lia|].
    bdestruct (k <? length l); [|easy].
    rewrite IHl.
    destruct (Nat.eq_dec (nth k l (S v)) v); [|easy].
    exfalso. 
    apply Hv; right.
    replace <- v.
    apply nth_In; easy.
Qed.

Lemma nth_eq_lt_length {l : list nat} {k : nat} {v : nat} :
  nth k l (S v) = v ->
  k < length l.
Proof.
  revert k;
  induction l; intros k.
  - destruct k; 
    simpl; lia.
  - destruct k.
    + simpl; lia.
    + simpl.
      intros H.
      specialize (IHl k H).
      lia.
Qed.

Lemma bring_to_front_perm_nth_eq_v (l : list nat) (v k : nat)
  (Hk : nth k l (S v) = v) :
  bring_to_front_perm l v k < count_nat l v.
Proof.
  revert k Hk.
  induction l; [destruct k; simpl; lia|].
  destruct k.
  - rewrite bring_to_front_perm_0.
    simpl.
    intros Heq.
    rewrite (nat_eq_dec_eq Heq); lia.
  - simpl. 
    intros Heq.
    specialize (IHl k Heq).
    rewrite bring_to_front_perm_hd.
    pose proof (nth_eq_lt_length Heq).
    bdestruct (k <? length l); [|lia].
    rewrite (nat_eq_dec_eq Heq).
    destruct (Nat.eq_dec a v); lia.
Qed.

Lemma bring_to_front_perm_nth_neq {l : list nat} {v k : nat} :
  nth k l (S v) <> v -> 
  count_nat l v <= bring_to_front_perm l v k.
Proof.
  revert k; 
  induction l; 
  intros k; [simpl; lia|].
  destruct k.
  - rewrite bring_to_front_perm_0.
    simpl.
    intros.
    destruct (Nat.eq_dec a v); easy.
  - simpl.
    rewrite bring_to_front_perm_hd.
    intros Hk.
    specialize (IHl k Hk).
    destruct (Nat.eq_dec (nth k l (S v)) v); [easy|].
    pose proof (count_occ_bound Nat.eq_dec v l).
    destruct (Nat.eq_dec a v); bdestruct_all; lia.
Qed.

Lemma bring_to_front_perm_bounded (l : list nat) (v : nat) : 
  forall k, k < length l -> 
  bring_to_front_perm l v k < length l.
Proof.
  induction l; [easy|].
  simpl.
  intros k.
  destruct k.
  - intros _.
    rewrite bring_to_front_perm_0.
    pose proof (count_occ_bound Nat.eq_dec v l).
    destruct (Nat.eq_dec a v); lia.
  - intros Hlt.
    rewrite bring_to_front_perm_hd'.
    specialize (IHl k ltac:(lia)).
    bdestruct_all; simpl; lia.
Qed.

Lemma bring_to_front_perm_aux (l : list nat) (v : nat) : 
  forall k j, 
  bring_to_front_perm l v k = bring_to_front_perm l v j ->
  j <? length l = (k <? length l).
Proof.
  intros k j Heq.
  bdestruct (j <? length l); bdestruct (k <? length l); try easy;
  epose proof (bring_to_front_perm_WF _ v _ ltac:(eassumption));
  epose proof (bring_to_front_perm_bounded _ v _ ltac:(eassumption));
  lia.
Qed.

Lemma ltb_S (n m : nat) : 
  (S n <? S m) = (n <? m).
Proof.
  bdestruct_all; lia.
Qed.

Lemma bring_to_front_perm_inj (l : list nat) (v : nat) : 
  forall k j, bring_to_front_perm l v k = bring_to_front_perm l v j ->
  k = j.
Proof.
  induction l.
  - intros k j.
    rewrite 2! bring_to_front_perm_WF by (simpl; lia); easy.
  - intros k j Heq.
    pose proof (bring_to_front_perm_aux _ _ _ _ Heq) as Hlt.
    revert j Heq Hlt.
    destruct k.
    intros j.
    destruct j.
    + easy.
    + rewrite bring_to_front_perm_0.
      rewrite bring_to_front_perm_hd.
      destruct (Nat.eq_dec a v); [bdestruct_all; easy|].
      bdestruct_all; simpl in *; try lia.
      destruct (Nat.eq_dec (nth j l (S v)) v).
      * pose proof (bring_to_front_perm_nth_eq_v _ _ _ e).
        lia.
      * pose proof (bring_to_front_perm_nth_neq n0).
        lia.
    + intros j.
      destruct j.
      * rewrite bring_to_front_perm_0.
        rewrite bring_to_front_perm_hd.
        destruct (Nat.eq_dec a v); [bdestruct_all; easy|].
        bdestruct_all; simpl in *; try lia.
        destruct (Nat.eq_dec (nth k l (S v)) v).
        --pose proof (bring_to_front_perm_nth_eq_v _ _ _ e).
          lia.
        --pose proof (bring_to_front_perm_nth_neq n0).
          lia.
      * intros H' H; revert H'.
        simpl in H.
        rewrite 2!ltb_S in H.
        rewrite 2!bring_to_front_perm_hd'.
        rewrite H.
        bdestruct (k <? length l); [|easy].
        bdestruct_all; simpl; auto with arith.
        --pose proof (bring_to_front_perm_nth_eq_v l v k ltac:(easy)).
          pose proof (bring_to_front_perm_nth_neq ltac:(eassumption)).
          lia.
        --pose proof (bring_to_front_perm_nth_eq_v l v j ltac:(easy)).
          pose proof (bring_to_front_perm_nth_neq ltac:(eassumption)).
          lia.
Qed.

(* FIXME: This is in the new quantumlib version; just need to 
  remove this Admitted lemma once that's out *)
Lemma permutation_iff_surjective : forall n f, 
  permutation n f <-> 
  (forall k, k < n -> exists k', k' < n /\ f k' = k).
Admitted.

Lemma bring_to_front_perm_permutation (l : list nat) (v : nat) : 
  permutation (length l) (bring_to_front_perm l v).
Proof.
  apply permutation_iff_surjective.
  apply PermutationFacts.surjective_of_injective_and_bounded.
  split.
  - intros ? ? ? ?. 
    apply bring_to_front_perm_inj.
  - apply bring_to_front_perm_bounded.
Qed.

Lemma count_occ_eq_S_In {A} (eq_dec : forall a b : A, {a=b}+{a<>b})
  (l : list A) (a : A) (m : nat) (Hl : count_occ eq_dec l a = S m) :
  In a l.
Proof.
  induction l as [|b l IHl]; [easy|].
  simpl in Hl.
  destruct (eq_dec b a).
  - left; easy.
  - right; apply (IHl Hl).
Qed.

(* TODO: We can even do this as a function if we want *)
Lemma in_split_nat (x : nat) (l : list nat) (Ha : In x l) :
  exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1.
Proof.
  induction l; [easy|].
  simpl in Ha.
  destruct (Nat.eq_dec a x).
  exists [], l. 
  split; subst; easy.
  destruct Ha as [Heq | Hin]; [easy|].
  destruct (IHl Hin) as [l1 [l2 [Heq Hnin]]].
  exists (a::l1), l2.
  split; [simpl; f_equal; easy|].
  intros []; easy.
Qed.



Lemma count_occ_eq_S_split (x : nat) (l : list nat) 
  (m : nat) (Hl : count_occ Nat.eq_dec l x = S m) :
  exists l1 l2, l = l1 ++ x :: l2 /\ count_occ Nat.eq_dec l2 x = m.
Proof.
  induction l as [|a l IHl]; [easy|].
  destruct (count_occ_eq_S_In _ _ _ _ Hl) as [Heq | Hin].
  - exists [], l.
    split; [subst; easy|simpl in *].
    destruct (Nat.eq_dec a x); lia.
  - destruct (Nat.eq_dec a x) as [Heq | Hneq].
    + exists [], l.
      split; [subst; easy|simpl in *].
      destruct (Nat.eq_dec a x); lia.
    + destruct (in_split_nat _ _ Hin) as [l1 [l2 [Heq Hnin]]].
      exists (a :: l1), l2.
      split; [subst; easy|].
      subst l.
      simpl in Hl.
      destruct (Nat.eq_dec a x); [easy|].
      rewrite count_occ_app in Hl.
      rewrite (proj1 (count_occ_not_In _ _ _) Hnin) in Hl.
      simpl in Hl.
      destruct (Nat.eq_dec x x); lia.
Qed.

Lemma kth_occ_app_not_In (l l' : list nat) (k v : nat) (Hl : ~ In v l) : 
  kth_occ (l ++ l') k v = length l + kth_occ l' k v.
Proof.
  induction l; [easy|].
  simpl in *.
  destruct (Nat.eq_dec a v); [lia|].
  rewrite (IHl (fun Hin => Hl (or_intror Hin))).
  easy.
Qed.

Lemma kth_occ_count_occ_firstn (l : list nat) (k : nat) (v : nat) :
  nth k l (S v) = v ->
  (kth_occ l (count_occ Nat.eq_dec (firstn k l) v) v) = k.
Proof.
  revert k;
  induction l.
  - destruct k; simpl; easy + lia.
  - destruct k as [|k].
    + simpl.
      intros Heq.
      rewrite (nat_eq_dec_eq Heq).
      easy.
    + simpl.
      destruct (Nat.eq_dec a v) as [Heq | Hneq];
      intros H;
      rewrite (IHl _ H);
      easy.
Qed.

(* Lemma nth_neq_count_occ_firstn (l : list nat) (k : nat) (v : nat) :
  nth k l (S v) = v ->
  nth_neq (count_nat (firstn k l) v - count_nat l v) l v
    (count_nat (firstn k (a :: l)) v) = k *)

Lemma nth_neq_not_In (idx : nat) (l : list nat) (v def : nat) :
  ~ In v l ->
  nth_neq idx l v def = nth idx l def.
Proof.
  revert idx;
  induction l; [destruct idx; easy|]; intros idx.
  simpl.
  intros Hnin.
  destruct (Nat.eq_dec a v); [lia|].
  destruct idx; [easy|].
  apply IHl.
  intros H; apply Hnin; right; easy.
Qed.



Lemma nth_neq_ge_length (l : list nat) (v def idx : nat) :
  length l <= idx ->
  nth_neq idx l v def = def.
Proof.
  revert idx;
  induction l; [easy|]. 
  intros idx.
  destruct idx; [easy|].
  simpl.
  intros H.
  destruct (Nat.eq_dec a v); 
  apply IHl; lia.
Qed.

Lemma kth_occ_ge_length (l : list nat) (k v : nat) : 
  length l <= k -> 
  kth_occ l k v = length l.
Proof.
  revert k;
  induction l; [easy|].
  intros k Hk.
  destruct k; [easy|].
  simpl in *.
  destruct (Nat.eq_dec a v);
  rewrite IHl; lia.
Qed.


Lemma bring_to_front_invperm_WF (l : list nat) (v : nat) :
  forall k, length l <= k -> 
  bring_to_front_invperm l v k = k.
Proof.
  intros k Hk; unfold bring_to_front_invperm.
  pose proof (count_occ_bound Nat.eq_dec v l).
  bdestruct_all.
  apply nth_neq_ge_length; easy.
Qed.

Lemma count_nat_firstn_le (l : list nat) (k v : nat) :
  count_nat (firstn k l) v <= count_nat l v.
Proof.
  revert k;
  induction l; [destruct k; easy|].
  intros k.
  destruct k.
  - simpl.
    destruct (Nat.eq_dec a v); lia.
  - simpl.
    destruct (Nat.eq_dec a v); specialize (IHl k); lia.
Qed.



(* Lemma count_nat_skipn_plus_gt (l : list nat) (k v : nat) :
  k < length l -> 
  nth k l (S v) <> v ->
  count_nat l v < count_nat (skipn k l) v + k.
Proof.
  revert k;
  induction l; [easy|];
  intros k.
  destruct k.
  - simpl. *)

Lemma bring_to_front_perm_linv' (l : list nat) (v : nat) :
  forall k, k < length l ->
  bring_to_front_invperm l v (bring_to_front_perm l v k) = k.
Proof.
  induction l; [easy|].
  simpl.
  intros k Hk.
  unfold bring_to_front_invperm, bring_to_front_perm.
  destruct (Nat.eq_dec (nth k (a :: l) (S v)) v) as [Heq | Hneq].
  - simpl.
    destruct (Nat.eq_dec a v).
    + bdestruct_all; simpl.
      * destruct k; [easy|simpl].
        destruct (Nat.eq_dec a v); [|easy].
        now rewrite (kth_occ_count_occ_firstn l k v Heq).
      * simpl.
        destruct k; [easy|].
        simpl in *.
        rewrite (nat_eq_dec_eq e) in *.
        pose proof (count_nat_firstn_le l k v).
        pose proof (IHl k ltac:(lia)) as Hind.
        unfold bring_to_front_invperm, bring_to_front_perm in Hind.
        revert Hind.
        rewrite (nat_eq_dec_eq Heq).
        bdestruct (k <? length l); [|lia].
        bdestruct_all.
        intros Hind.
        rewrite <- Hind at 3.
        

        lia.
    + pose proof (count_nat_firstn_le (a::l) k v).
      simpl in H.
      destruct (Nat.eq_dec a v); try lia.
      bdestruct_all.
      destruct k.
      easy.
      simpl in *.
      destruct (Nat.eq_dec a v); [easy|].
      f_equal.
      rewrite kth_occ_count_occ_firstn; easy.
  - bdestruct (k <? length (a :: l)); [|simpl in *; lia].
    destruct k.
    simpl in *.
    destruct (Nat.eq_dec a v); [easy|].
    rewrite 
    bdestruct_all.
    destruct k.
    simpl in *.
    destruct (Nat.eq_dec a v); try easy.

    simpl in *.


        simpl in *.
        easy.
        rewrite nth_neq_not_In.
        unfold nth_neq
Admitted.

Lemma kth_occ_count_occ_firstn (l : list nat) (k : nat) (v : nat) :
  count_occ Nat.eq_dec (firstn k l) v <
    count_occ Nat.eq_dec l v ->
  (kth_occ l (count_occ Nat.eq_dec (firstn k l) v) v) = k.
Proof.
  remember (count_occ Nat.eq_dec l v) as m.
  revert l k Heqm.
  induction m; [easy|].
  intros l k Hl Hlt.
  destruct (count_occ_eq_S_split _ _ _ (eq_sym Hl)) as [l1 [l2 [Hleq Hnin]]].
  subst l.
  assert (Hnin1 : ~ In v l1). 1:{
    rewrite (count_occ_not_In Nat.eq_dec).
    rewrite count_occ_app in Hl; 
    simpl in Hl.
    destruct (Nat.eq_dec v v); lia.
  }
  rewrite kth_occ_app_not_In by easy.

  (* CHECK HERE *)

  induction l as [|a l IHl]; [easy|].
  destruct k.
  - simpl in *.
    destruct (Nat.eq_dec a v); [easy|].




  revert k; induction l; [easy|].
  intros k. 
  destruct k.
  - simpl.
    destruct (Nat.eq_dec a v); [easy|].
    destruct l; [easy|].
    simpl.
  simpl. [easy|]. *)



Lemma bring_to_front_perm_rinv (l : list nat) (v : nat) :
  forall k, k < length l ->
  bring_to_front_perm l v (bring_to_front_invperm l v k) = k.
Proof.
  induction l; [easy|].
  simpl.
  intros k Hk.
  unfold bring_to_front_invperm, bring_to_front_perm.
Admitted.


Fixpoint add_k_self_loops_to_spider {n m} (k : nat) 
  (cur : ZX (k + n) (k + m)) : ZX n m := 
  match k as k' return (ZX (k' + n) (k' + m) -> ZX n m) with
  | O => fun cur => cur
  | S k' => 
    fun cur => add_k_self_loops_to_spider k' 
      (⊂ ↕ (n_wire (k' + n)) ⟷ (— ↕ cur) ⟷ (⊃ ↕ (n_wire (k' + m))))
  end cur.


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


End GraphToDiagram_prelim.


Module GraphToDiagram.

Export GraphToDiagram_prelim.

(* Local Notation zxnode := (nat * bool * R)%type.
Local Notation node_id A := (@fst nat bool (@fst _ R A)).
Local Notation node_typ A := (@snd nat bool (@fst _ R A)).
Local Notation node_rot A := (@snd (nat * bool) R A). *)



Record zxgraph := mk_zxgraph {
  inputs : list nat;
  outputs : list nat;
  nodeids : list nat;
  nodevals : list zxnode;
  edges : list edge;
  num_ids : nat;
}.

Notation input_degree G v :=
  (count_occ Nat.eq_dec G.(inputs) v).

Notation output_degree G v :=
  (count_occ Nat.eq_dec G.(outputs) v).

Definition permute_graph (f : nat -> nat) (G : zxgraph) : zxgraph :=
  {|
    inputs := G.(inputs);
    outputs := G.(outputs);
    nodeids := G.(nodeids);
    nodevals := permute_list f G.(nodevals);
    edges := permute_edges f G.(edges);
    num_ids := G.(num_ids)
  |}.

Definition is_isomorphism (f : nat -> nat) (G H : zxgraph) :=
  permute_graph f G = H.




Definition right_truncate (G : zxgraph) (v : nat) : zxgraph :=
  {|
    inputs := inputs_of_right_truncate G.(inputs) v;
    outputs := outputs_of_right_truncate G.(edges) G.(outputs) v;
    nodeids := nodeids_of_right_truncate G.(nodeids) G.(nodevals) v;
    nodevals := nodevals_of_right_truncate G.(nodeids) G.(nodevals) v;
    edges := edges_of_right_truncate G.(edges) v;
    num_ids := num_ids_of_right_truncate G.(num_ids) G.(inputs) v;
  |}.



End GraphToDiagram.


Module WFzxgraph.

Import PermToZX GraphToDiagram.

Definition WFzxgraph (G : zxgraph) : Prop :=
  length G.(nodeids) = length G.(nodevals) 
  /\ NoDup G.(nodeids)
  /\ Forall 
    (fun e => 
    match e with
    | (e1, e2) => 
      In e1 G.(nodeids) /\ In e2 G.(nodeids)
    end) G.(edges)
  /\ Forall 
    (fun k => In k G.(nodeids))
    (G.(inputs) ++ G.(outputs)).

Section WFzxgraph_dec.




Definition WFzxgraphb (G : zxgraph) : bool :=
  (length G.(nodeids) =? length G.(nodevals) )
  && NoDupb eqb G.(nodeids)
  && forallb 
    (fun e : edge => let (e1, e2) := e in 
      Inb eqb e1 G.(nodeids) && Inb eqb e2 G.(nodeids)) G.(edges)
  && forallb
    (fun a : nat => Inb eqb a G.(nodeids))
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
  - now rewrite (Inb_In beq_reflect). 
Qed.

Lemma WFzxgraphP (G : zxgraph) : 
  reflect (WFzxgraph G) (WFzxgraphb G).
Proof.
  apply iff_reflect, WFzxgraph_WFzxgraphb.
Qed.



End WFzxgraph_dec.



Section WFzxgraph_results.

Context (G : zxgraph) (HG : WFzxgraph G).

Lemma NoDup_nodeids : NoDup (G.(nodeids)).
Proof. apply HG. Qed.

Lemma length_nodeids_nodevals : length G.(nodeids) = length G.(nodevals).
Proof. apply HG. Qed.

Lemma edge_members_in : Forall 
  (fun e : edge => let (e1, e2) := e in 
  In e1 (G.(nodeids)) 
  /\ In e2 (G.(nodeids))) G.(edges).
Proof. apply HG. Qed.


End WFzxgraph_results.




Lemma WF_right_truncate (G : zxgraph) (v : nat) (HG : WFzxgraph G) :
  WFzxgraph (right_truncate G v).
Proof.
  unfold right_truncate, WFzxgraph.
  simpl; repeat split.
  - apply length_nodeids_nodes_right_truncate.
  - apply NoDup_nodeids_right_truncate, HG.
  - apply forall_in_nodeids_edges_right_truncate; apply HG.
  - apply forall_in_nodeids_inputs_outputs; apply HG.
Qed.


Section GraphTranslation.






(* Lemma nodeidsvals_of_right_truncate_hd {inputs outputs nodeids 
  nodevals edges num_ids}
  (vid : nat) (vnode : zxnode) :
  NoDup (vid :: nodeids) ->
  length nodeids = length nodevals ->
  let Gbase := {|
    inputs := inputs;
    outputs := outputs;
    nodeids := vid::nodeids;
    nodevals := vnode::nodevals;
    edges := edges;
    num_ids := num_ids;
  |} in
  nodeidsvals_of_right_truncate Gbase vid = combine nodeids nodevals.
Proof.
  unfold nodeidsvals_of_right_truncate.

  revert nodevals; 
  induction nodeids as [| n ns IHns'];
  intros nodevals Hdup Hlength.
  - simpl.
    unfold nodeidsvals_of_right_truncate.
    simpl.
    bdestruct_all; easy.
  - assert (Hnodup : NoDup (vid :: ns)). 1:{
      rewrite 2!NoDup_cons_iff in *.
      split; try apply Hdup.
      intros Hf.
      apply (proj1 Hdup).
      right; easy.
    }
    pose proof (fun nodevals => IHns' nodevals Hnodup) as IHns.
    simpl in IHns.
    unfold nodeidsvals_of_right_truncate in IHns.
    simpl in IHns.
    bdestruct (vid =? vid); [|easy].
    simpl in IHns.
    specialize (IHns )
    rewrite NoDup_cons_iff in Hdup.

    Search (NoDup (_ :: _ :: _)).
  [easy|]. *)



Lemma right_truncate_hd {inputs outputs nodeids nodevals edges num_ids}
  (vid : nat) (vnode : zxnode) : 
  NoDup (vid :: nodeids) ->
  length nodeids = length nodevals ->
  right_truncate {|
    inputs := inputs;
    outputs := outputs;
    nodeids := vid::nodeids;
    nodevals := vnode::nodevals;
    edges := edges;
    num_ids := num_ids;
  |} vid = {|
    inputs := inputs_of_right_truncate inputs vid;
    outputs := outputs_of_right_truncate edges outputs vid;
    nodeids := nodeids;
    nodevals := nodevals;
    edges := edges_of_right_truncate edges vid;
    num_ids := num_ids_of_right_truncate num_ids inputs vid;
  |}.
Proof.
  intros Hdup Hlen.
  unfold right_truncate.
  f_equal;
  unfold nodeids_of_right_truncate, nodevals_of_right_truncate;
  simpl;
  rewrite (nodeidsvals_of_right_truncate_hd nodeids nodevals vid vnode Hdup);
  rewrite (combine_split _ _ Hlen); easy.
Qed.


Local Open Scope nat_scope.

Definition graph_in_size (inputs : list nat) num_ids : nat :=
  num_ids + length inputs.

Definition graph_out_size (outputs : list nat) num_ids : nat :=
  num_ids + length outputs.

Definition vtx_in_size inputs outputs edges num_ids (v : nat) : nat :=
  num_ids
  + ((count_nat inputs v
  + length (neighborhood_no_self edges v))
  + length (filter (fun k => ¬ v =? k) outputs)).
  (* + length (outputs_of_right_truncate G v). *)

Definition vtx_out_size outputs num_ids (v : nat) : nat :=
  num_ids
  + (count_nat outputs v
  + length (filter (fun k => ¬ v =? k) outputs)).

(* Lemma diagram_of_vtx_pf_one  *)

Definition diagram_of_vtx inputs outputs nodeids nodevals edges
  num_ids (v : nat) : 
  option (ZX 
    (vtx_in_size inputs outputs edges num_ids v) 
    (vtx_out_size outputs num_ids v)) :=
  option_map 
  (fun zx => n_wire num_ids 
    ↕ (ZX_of_zxnode zx _ _
    ↕ n_wire _)) (get_zxnode_by_id nodeids nodevals v).

Definition zx_of_perm_casted_pf (n : nat) (f : nat -> nat) : 
  n = length (PermutationDefinitions.insertion_sort_list n 
  (PermutationDefinitions.perm_inv n f)) :=
  eq_sym (PermutationFacts.length_insertion_sort_list n
  (PermutationDefinitions.perm_inv n f)).

Definition zx_of_perm_casted (n : nat) (f : nat -> nat) : ZX n n :=
  cast n n (zx_of_perm_casted_pf n f) (zx_of_perm_casted_pf n f)
  (ZXperm.zx_of_perm n f).

Definition diagram_of_vtx_permed inputs outputs nodeids 
  nodevals edges num_ids (v : nat) : 
  option (ZX 
    (vtx_in_size inputs outputs edges num_ids v) 
    (vtx_out_size outputs num_ids v)) :=
  option_map 
  (fun zx => n_wire num_ids
    ↕ (ZX_of_zxnode zx _ (count_occ Nat.eq_dec outputs v)
    ↕ n_wire _
      ⟷ zx_of_perm_casted _
        (bring_to_front_invperm 
          (outputs_of_right_truncate edges outputs v) v))) 
  (get_zxnode_by_id nodeids nodevals v).

Lemma right_truncate_cast_pf_one inputs num_ids (v : nat) : 
  graph_in_size inputs num_ids = 
  graph_in_size 
    (inputs_of_right_truncate inputs v)
    (num_ids_of_right_truncate num_ids inputs v).
Proof.
  unfold right_truncate, graph_in_size, num_ids_of_right_truncate.
  rewrite <- Nat.add_assoc.
  f_equal.
  unfold inputs_of_right_truncate.
  simpl.
  induction inputs as [|a inputs IHinp]; [easy|].
  simpl; rewrite IHinp.
  destruct (Nat.eq_dec a v);
  bdestruct (v =? a); try congruence;
  try easy; simpl.
  lia.
Qed.

Lemma right_truncate_cast_pf_two inputs outputs edges num_ids (v : nat) : 
  graph_out_size 
    (outputs_of_right_truncate edges outputs v)
    (num_ids_of_right_truncate num_ids inputs v) = 
    vtx_in_size inputs outputs edges num_ids v.
Proof.
  unfold right_truncate, graph_out_size, 
    vtx_in_size, outputs_of_right_truncate, num_ids_of_right_truncate.
  rewrite app_length.
  lia.
Qed.

Lemma right_truncate_cast_pf_three outputs num_ids (v : nat) : 
  vtx_out_size outputs num_ids v = graph_out_size outputs num_ids.
Proof.
  unfold graph_out_size, vtx_out_size.
  f_equal.
  induction outputs; [easy|].
  simpl.
  destruct (Nat.eq_dec a v);
  bdestruct_all; simpl; lia.
Qed.



Fixpoint GraphAttrs_to_ZX (nodeids : list nat) 
  (inputs : list nat) (outputs : list nat)
  (nodevals : list zxnode) (edges : list edge) (num_ids : nat) : 
  (* let G := {|  
    inputs := inputs;
    outputs := outputs;
    nodeids := nodeids;
    nodevals := nodevals;
    edges := edges;
    num_ids := num_ids;
  |} in *)
  option 
  (ZX (graph_in_size inputs num_ids) 
      (graph_out_size outputs num_ids)) := 
  (* let G := {|  
    inputs := inputs;
    outputs := outputs;
    nodeids := nodeids;
    nodevals := nodevals;
    edges := edges;
    num_ids := num_ids;
  |} in *)
  match nodeids, nodevals with
  | [], _ 
  | _, [] => 
    match Nat.eq_dec 
      (graph_in_size inputs num_ids) 
      (graph_out_size outputs num_ids) with
    | left Heq => Some (nwire_cast Heq)
    | right Hneq => None
    end
  | vtx :: nodeids', zx :: nodevals' => 
    match (diagram_of_vtx inputs outputs 
      nodeids nodevals edges num_ids vtx) with
    | Some vtx_zx => 
      (option_map 
        (fun graph_zx =>
        
        (n_wire num_ids ↕ 
        zx_of_perm_casted 
          (length inputs)
          (bring_to_front_perm inputs vtx)) ⟷
        nwire_cast (right_truncate_cast_pf_one inputs num_ids vtx) ⟷
        graph_zx ⟷
        nwire_cast (right_truncate_cast_pf_two inputs 
          outputs edges num_ids vtx) ⟷
        vtx_zx ⟷
        nwire_cast (right_truncate_cast_pf_three outputs num_ids vtx))
        (GraphAttrs_to_ZX 
          nodeids'
          (inputs_of_right_truncate inputs vtx)
          (outputs_of_right_truncate edges outputs vtx)
          nodevals'
          (edges_of_right_truncate edges vtx)
          (num_ids_of_right_truncate num_ids inputs vtx)))
    | None => None
    end
  end.

Definition Graph_to_ZX (G : zxgraph) :=
  GraphAttrs_to_ZX G.(nodeids) G.(inputs) G.(outputs) 
    G.(nodevals) G.(edges) G.(num_ids).

Lemma inputs_of_empty_nodeids (G : zxgraph) (HG : WFzxgraph G) 
  (Hnode : G.(nodeids) = []) : G.(inputs) = [].
Proof.
  destruct HG as [? [? [ ? H]]].
  destruct (inputs G); [easy|].
  inversion H; subst.
  rewrite Hnode in *.
  easy.
Qed.

Lemma outputs_of_empty_nodeids (G : zxgraph) (HG : WFzxgraph G) 
  (Hnode : G.(nodeids) = []) : G.(outputs) = [].
Proof.
  destruct HG as [? [? [ ? H]]].
  destruct (outputs G); [easy|].
  rewrite Forall_app in H.
  destruct H as [_ H].
  inversion H; subst.
  rewrite Hnode in *.
  easy.
Qed.

Lemma graph_in_size_eq_graph_out_size (G : zxgraph) (HG : WFzxgraph G) 
  (Hnode : G.(nodeids) = []) :
  graph_in_size G.(inputs) G.(num_ids) = graph_out_size G.(outputs) G.(num_ids).
Proof.
  unfold graph_in_size, graph_out_size.
  now rewrite (inputs_of_empty_nodeids _ HG Hnode),
    (outputs_of_empty_nodeids _ HG Hnode).
Qed.

Lemma diagram_of_vtx_hd inputs outputs ns nvs edges num_ids n v :
  exists zx, 
  diagram_of_vtx inputs outputs (n::ns)
    (v::nvs) edges num_ids n = Some zx.
Proof.
  unfold diagram_of_vtx, get_zxnode_by_id.
  simpl.
  rewrite Nat.eqb_refl.
  eexists; easy.
Qed.

Lemma GraphAttrs_to_ZX_WFzxgraph (nodeids : list nat) 
  (inputs : list nat) (outputs : list nat)
  (nodevals : list zxnode) (edges : list edge) (num_ids : nat) : 
  WFzxgraph {|
    inputs := inputs;
    outputs := outputs;
    nodeids := nodeids;
    nodevals := nodevals;
    edges := edges;
    num_ids := num_ids;
  |} -> 
  exists zx, 
  GraphAttrs_to_ZX nodeids inputs outputs 
    nodevals edges num_ids = Some zx.
Proof.
  revert inputs outputs nodevals edges num_ids;
  induction nodeids as [|v ns IHns]; [simpl|].
  - intros * HG.
    pose proof (nat_eq_dec_eq 
      (graph_in_size_eq_graph_out_size _ HG eq_refl)) as p;
      simpl in p; rewrite p; clear p.
    eexists; reflexivity.
  - intros inputs outputs nodevals edges num_ids HG.
    destruct nodevals as [|n nvs]; [destruct HG; easy|].
    simpl.
    destruct (diagram_of_vtx_hd inputs outputs ns nvs edges num_ids v n)
      as [vtx_zx Hvtx_zx].
    rewrite Hvtx_zx.
    pose proof (WF_right_truncate _ v HG) as HWF.
    rewrite (right_truncate_hd v n 
      ltac:(apply HG)) in HWF.
    2: {
      destruct HG as [H ?]; simpl in H; injection H;
      exact (fun x => x).
    }
    destruct (IHns _ _ _ _ _ HWF) as [zx Hzx].
    rewrite Hzx.
    simpl.
    eexists; reflexivity.
Qed.

Lemma Graph_to_ZX_WFzxgraph (G : zxgraph) (HG : WFzxgraph G) : 
  exists zx, 
  Graph_to_ZX G = Some zx.
Proof.
  apply GraphAttrs_to_ZX_WFzxgraph, HG.
Qed.

End GraphTranslation.

End WFzxgraph.





Module DecidablePermutation.


Local Open Scope nat_scope.

Fixpoint for_all_nat_lt (f : nat -> bool) (k : nat) := 
  match k with
  | 0 => true
  | S k' => f k' && for_all_nat_lt f k'
  end.

Lemma forall_nat_lt_S (P : forall k : nat, Prop) (n : nat) : 
  (forall k, k < S n -> P k) <-> P n /\ (forall k, k < n -> P k).
Proof.
  split.
  - intros Hall.
    split; intros; apply Hall; lia.
  - intros [Hn Hall].
    intros k Hk.
    bdestruct (k=?n); [subst; easy | apply Hall; lia].
Qed.

Lemma for_all_nat_ltE {f : nat -> bool} {P : forall k : nat, Prop} 
  (ref : forall k, reflect (P k) (f k)) : 
  forall n, (forall k, k < n -> P k) <-> (for_all_nat_lt f n = true).
Proof.
  induction n.
  - easy.
  - rewrite forall_nat_lt_S.
    simpl.
    rewrite andb_true_iff.
    apply WFzxgraph.and_iff_compat; [|easy].
    apply reflect_iff; easy.
Qed.

Lemma for_all_nat_ltP {f : nat -> bool} {P : forall k : nat, Prop} 
  (ref : forall k, reflect (P k) (f k)) : 
  forall n, reflect (forall k, k < n -> P k) (for_all_nat_lt f n).
Proof.
  intros n.
  apply iff_reflect, for_all_nat_ltE.
  easy.
Qed.

Fixpoint Forall_nat_lt (P : forall k : nat, Prop) (n : nat) :=
  match n with
  | 0 => True
  | S n' => P n' /\ Forall_nat_lt P n'
  end.

Lemma Forall_nat_ltE (P : forall k : nat, Prop) (n : nat) : 
  Forall_nat_lt P n <-> forall k, k < n -> P k.
Proof.
  induction n; [easy|].
  simpl.
  rewrite IHn, forall_nat_lt_S.
  easy.
Qed.

Import PermutationDefinitions PermutationAutomation PermutationFacts.

Local Open Scope nat_scope.

Definition perm_inv_is_inv_pred (f : nat -> nat) (n : nat) : Prop :=
  forall k, k < n ->
    f k < n /\ perm_inv n f k < n /\ 
    perm_inv n f (f k) = k /\ f (perm_inv n f k) = k.

Definition is_permutation (f : nat -> nat) (n : nat) :=
  for_all_nat_lt 
    (fun k => 
      (f k <? n) && (perm_inv n f k <? n)
      && (perm_inv n f (f k) =? k)
      && (f (perm_inv n f k) =? k)) n.

Lemma permutation_iff_perm_inv_is_inv (f : nat -> nat) (n : nat) : 
  permutation n f <-> perm_inv_is_inv_pred f n.
Proof.
  split.
  - intros Hperm.
    intros k Hk.
    repeat split.
    + destruct Hperm as [g Hg];
      apply (Hg k Hk).
    + apply perm_inv_bdd; easy.
    + apply perm_inv_is_linv_of_permutation; easy.
    + apply perm_inv_is_rinv_of_permutation; easy.
  - intros Hperminv.
    exists (perm_inv n f); easy.
Qed.

Lemma is_permutationE (f : nat -> nat) (n : nat) : 
  perm_inv_is_inv_pred f n <-> is_permutation f n = true.
Proof.
  unfold perm_inv_is_inv_pred, is_permutation.
  apply for_all_nat_ltE.
  intros k.
  apply iff_reflect.
  rewrite 3!andb_true_iff.
  rewrite 2!Nat.ltb_lt, 2!Nat.eqb_eq, 2!and_assoc.
  easy.
Qed.

Lemma permutation_iff_is_permutation (f : nat -> nat) (n : nat) : 
  permutation n f <-> is_permutation f n = true.
Proof.
  rewrite permutation_iff_perm_inv_is_inv.
  apply is_permutationE.
Qed.

Lemma permutationP (f : nat -> nat) (n : nat) :
  reflect (permutation n f) (is_permutation f n).
Proof.
  apply iff_reflect, permutation_iff_is_permutation.
Qed.

Definition permutation_dec (f : nat -> nat) (n : nat) :
  {permutation n f} + {~ permutation n f} :=
  reflect_dec _ _ (permutationP f n).

End DecidablePermutation.
































Module GraphToDiagram_perm.

Export GraphToDiagram_prelim.

(* Local Notation zxnode := (nat * bool * R)%type.
Local Notation node_id A := (@fst nat bool (@fst _ R A)).
Local Notation node_typ A := (@snd nat bool (@fst _ R A)).
Local Notation node_rot A := (@snd (nat * bool) R A). *)



Record zxgraph := mk_zxgraph {
  inputs : list nat;
  outputs : list nat;
  nodeids : list nat;
  nodevals : list zxnode;
  edges : list edge;
  num_ids : nat;
  left_perm : nat -> nat;
  right_perm : nat -> nat;
}.

Notation input_degree G v :=
  (count_occ Nat.eq_dec G.(inputs) v).

Notation output_degree G v :=
  (count_occ Nat.eq_dec G.(outputs) v).




Definition right_truncate (G : zxgraph) (v : nat) : zxgraph :=
  {|
    inputs := inputs_of_right_truncate G.(inputs) v;
    outputs := outputs_of_right_truncate G.(edges) G.(outputs) v;
    nodeids := nodeids_of_right_truncate G.(nodeids) G.(nodevals) v;
    nodevals := nodevals_of_right_truncate G.(nodeids) G.(nodevals) v;
    edges := edges_of_right_truncate G.(edges) v;
    num_ids := num_ids_of_right_truncate G.(num_ids) G.(inputs) v;
    left_perm := G.(left_perm);
    right_perm := bring_to_front_perm G.(outputs) v;
  |}.



End GraphToDiagram_perm.


Module WFzxgraph_perm.

Import PermToZX GraphToDiagram_perm.

Definition WFzxgraph (G : zxgraph) : Prop :=
  length G.(nodeids) = length G.(nodevals) 
  /\ NoDup G.(nodeids)
  /\ Forall 
    (fun e => 
    match e with
    | (e1, e2) => 
      In e1 G.(nodeids) /\ In e2 G.(nodeids)
    end) G.(edges)
  /\ Forall 
    (fun k => In k G.(nodeids))
    (G.(inputs) ++ G.(outputs))
  /\ permutation (G.(num_ids) + length G.(inputs)) G.(left_perm)
  /\ permutation (G.(num_ids) + length G.(outputs)) G.(right_perm).

Section WFzxgraph_dec.

Import DecidablePermutation.

Definition WFzxgraphb (G : zxgraph) : bool :=
  (length G.(nodeids) =? length G.(nodevals) )
  && NoDupb eqb G.(nodeids)
  && forallb 
    (fun e : edge => let (e1, e2) := e in 
      Inb eqb e1 G.(nodeids) && Inb eqb e2 G.(nodeids)) G.(edges)
  && forallb
    (fun a : nat => Inb eqb a G.(nodeids))
    (G.(inputs) ++ G.(outputs))
  && is_permutation G.(left_perm) (G.(num_ids) + length G.(inputs))
  && is_permutation G.(right_perm) (G.(num_ids) + length G.(outputs)).

Lemma WFzxgraph_WFzxgraphb (G : zxgraph) : 
  WFzxgraph G <-> WFzxgraphb G = true.
Proof.
  destruct G.
  unfold WFzxgraph, WFzxgraphb.
  simpl.
  rewrite 5!andb_true_iff, Nat.eqb_eq.
  rewrite !and_assoc.
  apply and_iff_compat_l.
  rewrite (NoDup_Nodupb beq_reflect).
  apply and_iff_compat_l.
  rewrite <- !and_assoc.
  rewrite <- 2!permutation_iff_is_permutation.
  do 2 apply and_iff_compat_r.
  rewrite 2!forallb_forall, 2!Forall_forall.
  apply and_iff_compat; 
  apply forall_iff; [intros []|intros]; 
  apply imp_iff_compat_l.
  - now rewrite andb_true_iff, 2!(Inb_In beq_reflect).
  - now rewrite (Inb_In beq_reflect). 
Qed.

Lemma WFzxgraphP (G : zxgraph) : 
  reflect (WFzxgraph G) (WFzxgraphb G).
Proof.
  apply iff_reflect, WFzxgraph_WFzxgraphb.
Qed.



End WFzxgraph_dec.



Section WFzxgraph_results.

Context (G : zxgraph) (HG : WFzxgraph G).

Lemma NoDup_nodeids : NoDup (G.(nodeids)).
Proof. apply HG. Qed.

Lemma length_nodeids_nodevals : length G.(nodeids) = length G.(nodevals).
Proof. apply HG. Qed.

Lemma edge_members_in : Forall 
  (fun e : edge => let (e1, e2) := e in 
  In e1 (G.(nodeids)) 
  /\ In e2 (G.(nodeids))) G.(edges).
Proof. apply HG. Qed.

Lemma left_perm_permutation : 
  permutation (G.(num_ids) + length G.(inputs)) G.(left_perm).
Proof.  apply HG. Qed.

Lemma right_perm_permutation : 
  permutation (G.(num_ids) + length G.(outputs)) G.(right_perm).
Proof.  apply HG. Qed.

End WFzxgraph_results.




Lemma WF_right_truncate (G : zxgraph) (v : nat) (HG : WFzxgraph G) :
  WFzxgraph (right_truncate G v).
Proof.
  unfold right_truncate, WFzxgraph.
  simpl; repeat split.
  - apply length_nodeids_nodes_right_truncate.
  - apply NoDup_nodeids_right_truncate, HG.
  - apply forall_in_nodeids_edges_right_truncate; apply HG.
  - apply forall_in_nodeids_inputs_outputs; apply HG.
Qed.


Section GraphTranslation.






(* Lemma nodeidsvals_of_right_truncate_hd {inputs outputs nodeids 
  nodevals edges num_ids}
  (vid : nat) (vnode : zxnode) :
  NoDup (vid :: nodeids) ->
  length nodeids = length nodevals ->
  let Gbase := {|
    inputs := inputs;
    outputs := outputs;
    nodeids := vid::nodeids;
    nodevals := vnode::nodevals;
    edges := edges;
    num_ids := num_ids;
  |} in
  nodeidsvals_of_right_truncate Gbase vid = combine nodeids nodevals.
Proof.
  unfold nodeidsvals_of_right_truncate.

  revert nodevals; 
  induction nodeids as [| n ns IHns'];
  intros nodevals Hdup Hlength.
  - simpl.
    unfold nodeidsvals_of_right_truncate.
    simpl.
    bdestruct_all; easy.
  - assert (Hnodup : NoDup (vid :: ns)). 1:{
      rewrite 2!NoDup_cons_iff in *.
      split; try apply Hdup.
      intros Hf.
      apply (proj1 Hdup).
      right; easy.
    }
    pose proof (fun nodevals => IHns' nodevals Hnodup) as IHns.
    simpl in IHns.
    unfold nodeidsvals_of_right_truncate in IHns.
    simpl in IHns.
    bdestruct (vid =? vid); [|easy].
    simpl in IHns.
    specialize (IHns )
    rewrite NoDup_cons_iff in Hdup.

    Search (NoDup (_ :: _ :: _)).
  [easy|]. *)



Lemma right_truncate_hd {inputs outputs nodeids nodevals edges num_ids}
  (vid : nat) (vnode : zxnode) : 
  NoDup (vid :: nodeids) ->
  length nodeids = length nodevals ->
  right_truncate {|
    inputs := inputs;
    outputs := outputs;
    nodeids := vid::nodeids;
    nodevals := vnode::nodevals;
    edges := edges;
    num_ids := num_ids;
  |} vid = {|
    inputs := inputs_of_right_truncate inputs vid;
    outputs := outputs_of_right_truncate edges outputs vid;
    nodeids := nodeids;
    nodevals := nodevals;
    edges := edges_of_right_truncate edges vid;
    num_ids := num_ids_of_right_truncate num_ids inputs vid;
  |}.
Proof.
  intros Hdup Hlen.
  unfold right_truncate.
  f_equal;
  unfold nodeids_of_right_truncate, nodevals_of_right_truncate;
  simpl;
  rewrite (nodeidsvals_of_right_truncate_hd nodeids nodevals vid vnode Hdup);
  rewrite (combine_split _ _ Hlen); easy.
Qed.


Local Open Scope nat_scope.

Definition graph_in_size (inputs : list nat) num_ids : nat :=
  num_ids + length inputs.

Definition graph_out_size (outputs : list nat) num_ids : nat :=
  num_ids + length outputs.

Definition vtx_in_size inputs outputs edges num_ids (v : nat) : nat :=
  num_ids
  + ((count_nat inputs v
  + length (neighborhood_no_self edges v))
  + length (filter (fun k => ¬ v =? k) outputs)).
  (* + length (outputs_of_right_truncate G v). *)

Definition vtx_out_size outputs num_ids (v : nat) : nat :=
  num_ids
  + (count_nat outputs v
  + length (filter (fun k => ¬ v =? k) outputs)).

(* Lemma diagram_of_vtx_pf_one  *)

Definition diagram_of_vtx inputs outputs nodeids nodevals edges
  num_ids (v : nat) : 
  option (ZX 
    (vtx_in_size inputs outputs edges num_ids v) 
    (vtx_out_size outputs num_ids v)) :=
  option_map 
  (fun zx => n_wire num_ids 
    ↕ (ZX_of_zxnode zx _ _
    ↕ n_wire _)) (get_zxnode_by_id nodeids nodevals v).

Definition zx_of_perm_casted_pf (n : nat) (f : nat -> nat) : 
  n = length (PermutationDefinitions.insertion_sort_list n 
  (PermutationDefinitions.perm_inv n f)) :=
  eq_sym (PermutationFacts.length_insertion_sort_list n
  (PermutationDefinitions.perm_inv n f)).

Definition zx_of_perm_casted (n : nat) (f : nat -> nat) : ZX n n :=
  cast n n (zx_of_perm_casted_pf n f) (zx_of_perm_casted_pf n f)
  (ZXperm.zx_of_perm n f).

Definition diagram_of_vtx_permed inputs outputs nodeids 
  nodevals edges num_ids (v : nat) : 
  option (ZX 
    (vtx_in_size inputs outputs edges num_ids v) 
    (vtx_out_size outputs num_ids v)) :=
  option_map 
  (fun zx => n_wire num_ids
    ↕ (ZX_of_zxnode zx _ (count_occ Nat.eq_dec outputs v)
    ↕ n_wire _
      ⟷ zx_of_perm_casted _
        (bring_to_front_invperm 
          (outputs_of_right_truncate edges outputs v) v))) 
  (get_zxnode_by_id nodeids nodevals v).

Lemma right_truncate_cast_pf_one inputs num_ids (v : nat) : 
  graph_in_size inputs num_ids = 
  graph_in_size 
    (inputs_of_right_truncate inputs v)
    (num_ids_of_right_truncate num_ids inputs v).
Proof.
  unfold right_truncate, graph_in_size, num_ids_of_right_truncate.
  rewrite <- Nat.add_assoc.
  f_equal.
  unfold inputs_of_right_truncate.
  simpl.
  induction inputs as [|a inputs IHinp]; [easy|].
  simpl; rewrite IHinp.
  destruct (Nat.eq_dec a v);
  bdestruct (v =? a); try congruence;
  try easy; simpl.
  lia.
Qed.

Lemma right_truncate_cast_pf_two inputs outputs edges num_ids (v : nat) : 
  graph_out_size 
    (outputs_of_right_truncate edges outputs v)
    (num_ids_of_right_truncate num_ids inputs v) = 
    vtx_in_size inputs outputs edges num_ids v.
Proof.
  unfold right_truncate, graph_out_size, 
    vtx_in_size, outputs_of_right_truncate, num_ids_of_right_truncate.
  rewrite app_length.
  lia.
Qed.

Lemma right_truncate_cast_pf_three outputs num_ids (v : nat) : 
  vtx_out_size outputs num_ids v = graph_out_size outputs num_ids.
Proof.
  unfold graph_out_size, vtx_out_size.
  f_equal.
  induction outputs; [easy|].
  simpl.
  destruct (Nat.eq_dec a v);
  bdestruct_all; simpl; lia.
Qed.



Fixpoint GraphAttrs_to_ZX (nodeids : list nat) 
  (inputs : list nat) (outputs : list nat)
  (nodevals : list zxnode) (edges : list edge) (num_ids : nat) : 
  (* let G := {|  
    inputs := inputs;
    outputs := outputs;
    nodeids := nodeids;
    nodevals := nodevals;
    edges := edges;
    num_ids := num_ids;
  |} in *)
  option 
  (ZX (graph_in_size inputs num_ids) 
      (graph_out_size outputs num_ids)) := 
  (* let G := {|  
    inputs := inputs;
    outputs := outputs;
    nodeids := nodeids;
    nodevals := nodevals;
    edges := edges;
    num_ids := num_ids;
  |} in *)
  match nodeids, nodevals with
  | [], _ 
  | _, [] => 
    match Nat.eq_dec 
      (graph_in_size inputs num_ids) 
      (graph_out_size outputs num_ids) with
    | left Heq => Some (nwire_cast Heq)
    | right Hneq => None
    end
  | vtx :: nodeids', zx :: nodevals' => 
    match (diagram_of_vtx inputs outputs 
      nodeids nodevals edges num_ids vtx) with
    | Some vtx_zx => 
      (option_map 
        (fun graph_zx =>
        
        (n_wire num_ids ↕ 
        zx_of_perm_casted 
          (length inputs)
          (bring_to_front_perm inputs vtx)) ⟷
        nwire_cast (right_truncate_cast_pf_one inputs num_ids vtx) ⟷
        graph_zx ⟷
        nwire_cast (right_truncate_cast_pf_two inputs 
          outputs edges num_ids vtx) ⟷
        vtx_zx ⟷
        nwire_cast (right_truncate_cast_pf_three outputs num_ids vtx))
        (GraphAttrs_to_ZX 
          nodeids'
          (inputs_of_right_truncate inputs vtx)
          (outputs_of_right_truncate edges outputs vtx)
          nodevals'
          (edges_of_right_truncate edges vtx)
          (num_ids_of_right_truncate num_ids inputs vtx)))
    | None => None
    end
  end.

Definition Graph_to_ZX (G : zxgraph) :=
  GraphAttrs_to_ZX G.(nodeids) G.(inputs) G.(outputs) 
    G.(nodevals) G.(edges) G.(num_ids).

Lemma inputs_of_empty_nodeids (G : zxgraph) (HG : WFzxgraph G) 
  (Hnode : G.(nodeids) = []) : G.(inputs) = [].
Proof.
  destruct HG as [? [? [ ? H]]].
  destruct (inputs G); [easy|].
  inversion H; subst.
  rewrite Hnode in *.
  easy.
Qed.

Lemma outputs_of_empty_nodeids (G : zxgraph) (HG : WFzxgraph G) 
  (Hnode : G.(nodeids) = []) : G.(outputs) = [].
Proof.
  destruct HG as [? [? [ ? H]]].
  destruct (outputs G); [easy|].
  rewrite Forall_app in H.
  destruct H as [_ H].
  inversion H; subst.
  rewrite Hnode in *.
  easy.
Qed.

Lemma graph_in_size_eq_graph_out_size (G : zxgraph) (HG : WFzxgraph G) 
  (Hnode : G.(nodeids) = []) :
  graph_in_size G.(inputs) G.(num_ids) = graph_out_size G.(outputs) G.(num_ids).
Proof.
  unfold graph_in_size, graph_out_size.
  now rewrite (inputs_of_empty_nodeids _ HG Hnode),
    (outputs_of_empty_nodeids _ HG Hnode).
Qed.

Lemma diagram_of_vtx_hd inputs outputs ns nvs edges num_ids n v :
  exists zx, 
  diagram_of_vtx inputs outputs (n::ns)
    (v::nvs) edges num_ids n = Some zx.
Proof.
  unfold diagram_of_vtx, get_zxnode_by_id.
  simpl.
  rewrite Nat.eqb_refl.
  eexists; easy.
Qed.

Lemma GraphAttrs_to_ZX_WFzxgraph (nodeids : list nat) 
  (inputs : list nat) (outputs : list nat)
  (nodevals : list zxnode) (edges : list edge) (num_ids : nat) : 
  WFzxgraph {|
    inputs := inputs;
    outputs := outputs;
    nodeids := nodeids;
    nodevals := nodevals;
    edges := edges;
    num_ids := num_ids;
  |} -> 
  exists zx, 
  GraphAttrs_to_ZX nodeids inputs outputs 
    nodevals edges num_ids = Some zx.
Proof.
  revert inputs outputs nodevals edges num_ids;
  induction nodeids as [|v ns IHns]; [simpl|].
  - intros * HG.
    pose proof (nat_eq_dec_eq 
      (graph_in_size_eq_graph_out_size _ HG eq_refl)) as p;
      simpl in p; rewrite p; clear p.
    eexists; reflexivity.
  - intros inputs outputs nodevals edges num_ids HG.
    destruct nodevals as [|n nvs]; [destruct HG; easy|].
    simpl.
    destruct (diagram_of_vtx_hd inputs outputs ns nvs edges num_ids v n)
      as [vtx_zx Hvtx_zx].
    rewrite Hvtx_zx.
    pose proof (WF_right_truncate _ v HG) as HWF.
    rewrite (right_truncate_hd v n 
      ltac:(apply HG)) in HWF.
    2: {
      destruct HG as [H ?]; simpl in H; injection H;
      exact (fun x => x).
    }
    destruct (IHns _ _ _ _ _ HWF) as [zx Hzx].
    rewrite Hzx.
    simpl.
    eexists; reflexivity.
Qed.

Lemma Graph_to_ZX_WFzxgraph (G : zxgraph) (HG : WFzxgraph G) : 
  exists zx, 
  Graph_to_ZX G = Some zx.
Proof.
  apply GraphAttrs_to_ZX_WFzxgraph, HG.
Qed.

End GraphTranslation.

End WFzxgraph.























Section ZXperm_temp.

Lemma ZXperm_le_1 {n} (zx : ZX n n) (Hzx : ZXperm.ZXperm n zx) 
  (Hn : n <= 1) : zx ∝ n_wire n.
Proof.
  induction Hzx; try (now cleanup_zx).
  - now rewrite <- wire_to_n_wire.
  - specialize (IHHzx1 ltac:(lia)).
    specialize (IHHzx2 ltac:(lia)).
    rewrite IHHzx1, IHHzx2.
    now rewrite n_wire_stack.
  - specialize (IHHzx1 ltac:(lia)).
    specialize (IHHzx2 ltac:(lia)).
    rewrite IHHzx1, IHHzx2.
    now rewrite nwire_removal_l.
Qed.

Lemma ZXperm_0 (zx : ZX 0 0) (Hzx : ZXperm.ZXperm 0 zx) : zx ∝ ⦰.
Proof.
  now rewrite ZXperm_le_1 by (easy + lia).
Qed.

Lemma X_spider_ZXperm_absorption_l {n} (zx : ZX n n) 
  (Hzx : ZXperm.ZXperm n zx) (m : nat) (r : R) :
  zx ⟷ X n m r ∝ X n m r.
Proof.
  revert m r;
  induction Hzx; intros m r.
  - cleanup_zx; easy.
  - cleanup_zx; easy.
  - apply X_self_swap_absorbtion_left_base.
  - rewrite X_add_l_base_rot, <- compose_assoc, <- stack_compose_distr at 1.
    rewrite IHHzx1, IHHzx2.
    now rewrite <- X_add_l_base_rot. 
  - now rewrite compose_assoc, IHHzx2, IHHzx1.
Qed.

Lemma X_spider_ZXperm_absorption_r {m} (zx : ZX m m) 
  (Hzx : ZXperm.ZXperm m zx) (n : nat) (r : R) :
  X n m r ⟷ zx ∝ X n m r.
Proof.
  revert n r;
  induction Hzx; intros n' r.
  - cleanup_zx; easy.
  - cleanup_zx; easy.
  - now rewrite X_self_swap_absorbtion_right_base.
  - rewrite X_add_r_base_rot, compose_assoc at 1.
    rewrite <- (stack_compose_distr (X 1 n0 0) zx0 (X 1 n1 0) zx1).
    rewrite IHHzx1, IHHzx2.
    now rewrite <- X_add_r_base_rot. 
  - now rewrite <- compose_assoc, IHHzx1, IHHzx2.
Qed.

Lemma color_swap_ZXperm {n} (zx : ZX n n) (Hzx : ZXperm.ZXperm n zx) : 
  color_swap zx = zx.
Proof.
  induction Hzx; simpl; f_equal; easy.
Qed.

Lemma Z_spider_ZXperm_absorption_l {n} (zx : ZX n n) 
  (Hzx : ZXperm.ZXperm n zx) (m : nat) (r : R) :
  zx ⟷ Z n m r ∝ Z n m r.
Proof.
  rewrite <- (color_swap_ZXperm zx) by easy.
  apply colorswap_diagrams; simpl.
  rewrite colorswap_involutive.
  apply (X_spider_ZXperm_absorption_l zx Hzx m r).
Qed.

Lemma Z_spider_ZXperm_absorption_r {m} (zx : ZX m m) 
  (Hzx : ZXperm.ZXperm m zx) (n : nat) (r : R) :
  Z n m r ⟷ zx ∝ Z n m r.
Proof.
  rewrite <- (color_swap_ZXperm zx) by easy.
  apply colorswap_diagrams; simpl.
  rewrite colorswap_involutive.
  apply (X_spider_ZXperm_absorption_r zx Hzx n r).
Qed.

End ZXperm_temp.







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

