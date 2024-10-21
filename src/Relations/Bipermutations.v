(** The definition of and facts about bipermutations (involutive 
  fixed-point-free permutations) that don't involve or require matrices 
**)

(* Require Import ZXCore. *)
Require Import CoreRules.
Import CoreData CoreAutomation.
Import CastRules.
From QuantumLib Require Import Bits.
Require Export QuantumLib.Permutations.
Import QuantumLib.VectorStates Modulus Kronecker.
Require Export BipermAux.
Export Setoid.

Open Scope prg.
Open Scope nat_scope.

(* Section Bipermutations.v *)


(* ORDERING: Bottom to top, outputs first. I.e., 
7  \/ —     3
6  /\ \/    2
5  —  /\ ╲  1
4  —  —  ╱  0
*)

Create HintDb biperm_db discriminated.

  



Ltac auto_biperm_to n := 
  auto n with biperm_db perm_db perm_bounded_db WF_Perm_db.

Ltac auto_biperm := 
  auto 6 with biperm_db perm_db perm_bounded_db WF_Perm_db.

Tactic Notation "auto_biperm" int_or_var(n) :=
  auto_biperm_to n.

Tactic Notation "auto_biperm" :=
  auto_biperm 6.

(* Section Bipermutations. *)

Local Open Scope nat.

Definition bipermutation n f :=
  (forall k : nat, k < n -> f k < n /\ f k <> k /\ f (f k) = k).

Add Parametric Morphism n : (bipermutation n) with signature
  perm_eq n ==> iff as bipermutation_of_perm_eq.
Proof.
  enough (H : forall x y : nat -> nat,
  perm_eq n x y -> bipermutation n x -> bipermutation n y) by 
  (intros; split; apply H; easy).
  intros f g Hfg.
  unfold bipermutation.
  intros Hf k Hk.
  destruct (Hf k Hk) as (? & ? & ?).
  rewrite <- !Hfg by easy.
  easy.
Qed.

Lemma bipermutation_change_dims n m f : n = m ->
  bipermutation m f -> bipermutation n f.
Proof.
  now intros [].
Qed.

Lemma bipermutation_defn n f : 
  bipermutation n f <-> 
  (perm_bounded n f /\ (forall k, k < n -> f k <> k) 
    /\ perm_eq n (f ∘ f) idn).
Proof.
  split.
  - intros Hf; repeat split; intros ? ?; now apply Hf.
  - unfold compose. intros (? & ? & ?) k Hk; auto.
Qed.

(* To apply *)
Lemma by_bipermutation_defn n f : 
  perm_bounded n f -> (forall k, k < n -> f k <> k) ->
  perm_eq n (f ∘ f) idn ->
  bipermutation n f.
Proof.
  rewrite bipermutation_defn.
  auto.
Qed.

Lemma permutation_of_bipermutation {n f} : bipermutation n f -> permutation n f.
Proof.
  intros Hbiperm.
  exists f.
  intros k Hk.
  repeat split;
  apply Hbiperm, Hk.
Qed.

#[export] Hint Resolve permutation_of_bipermutation : perm_db biperm_db.

Lemma perm_inv_bipermutation n f (Hf : bipermutation n f) : 
  perm_eq n (perm_inv n f) f.
Proof.
  rewrite <- (compose_idn_r (perm_inv n f)).
  rewrite compose_perm_inv_l by cleanup_perm.
  symmetry.
  exact (fun k Hk => proj2 (proj2 (Hf k Hk))).
Qed.

Lemma bipermutation_defn_alt n f : 
  bipermutation n f <-> 
  (permutation n f /\ (forall k, k < n -> f k <> k) 
    /\ perm_eq n (perm_inv n f) f).
Proof.
  split.
  - intros Hf.
    repeat split.
    + auto with perm_db.
    + now apply bipermutation_defn in Hf.
    + now apply perm_inv_bipermutation.
  - intros (? & ? & Hfinv).
    rewrite bipermutation_defn.
    intuition auto with perm_db.
    rewrite <- Hfinv at 1.
    cleanup_perm_inv.
Qed.

Lemma by_bipermutation_defn_alt n f : 
  permutation n f -> (forall k, k < n -> f k <> k) ->
  perm_eq n (perm_inv n f) f ->
  bipermutation n f.
Proof.
  rewrite bipermutation_defn_alt.
  auto.
Qed.

Lemma bipermutation_is_bounded n f : bipermutation n f -> 
  perm_bounded n f.
Proof.
  intros Hf k Hk; now apply Hf.
Qed. 

#[export] Hint Resolve bipermutation_is_bounded : biperm_db perm_bounded_db.

Lemma bipermutation_involutive {n f} k : bipermutation n f -> k < n ->
  f (f k) = k.
Proof.
  intros Hbiperm Hk.
  apply (Hbiperm k Hk).
Qed.

Lemma bipermutation_involutive_eq {n f} (Hf : bipermutation n f) : 
  perm_eq n (f ∘ f) idn.
Proof.
  intros k; now apply bipermutation_involutive.
Qed.

Lemma bipermutation_involutive_eq_WF {n f} (Hf : bipermutation n f) 
  (HfWF : WF_Perm n f) : 
  (f ∘ f) = idn.
Proof.
  eq_by_WF_perm_eq n.
  now apply bipermutation_involutive_eq.
Qed.

Lemma bipermutation_dim_ne_1 {n f} (Hf : bipermutation n f) : 
  n <> 1.
Proof.
  intros contra.
  specialize (Hf 0).
  lia.
Qed.

(* #[export] Hint Rewrite @bipermutation_involutive 
  using (solve [auto with biperm_db perm_db perm_bounded_db zarith]) :
  perm_cleanup_db. *)

Lemma bipermutation_eqb_iff {n f} a b : bipermutation n f -> a < n -> b < n ->
  f a =? b = (a =? f b).
Proof.
  intros Hbiperm Ha Hb.
  rewrite <- (bipermutation_involutive b Hbiperm Hb) at 1.
  rewrite (permutation_eqb_iff a (f b) (permutation_of_bipermutation Hbiperm) Ha).
  - easy.
  - apply Hbiperm, Hb.
Qed.

Lemma bipermutation_eq_iff {n f} a b : bipermutation n f -> a < n -> b < n ->
  f a = b <-> a = f b.
Proof.
  intros Hbiperm Ha Hb.
  pose proof (bipermutation_eqb_iff a b Hbiperm Ha Hb) as H.
  revert H.
  bdestructΩ'.
Qed.

Lemma bipermutation_injective {n} {g : nat -> nat} 
  (Hg : bipermutation n g) i j (Hi : i < n) (Hj : j < n) : 
  g i = g j <-> i = j.
Proof.
  rewrite (bipermutation_eq_iff _ _ Hg), (proj2 (proj2 (Hg j Hj)));
  lia + apply Hg; lia.
Qed.

Lemma bipermutation_inj {n} {g : nat -> nat} 
  (Hg : bipermutation n g) i j (Hi : i < n) (Hj : j < n) : 
  g i = g j -> i = j.
Proof.
  now apply (bipermutation_injective Hg).
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

Definition is_bipermutation n f : bool :=
  RMicromega.sumboolb (bipermutation_dec n f).

Lemma is_bipermutation_true_iff n f : 
  is_bipermutation n f = true <-> bipermutation n f.
Proof.
  unfold is_bipermutation. 
  now destruct (bipermutation_dec n f).
Qed.




Lemma bipermutation_shift_of_eq_swap n f 
  (Hf : bipermutation n f) (Hfsmall : perm_eq 2 f swap_2_perm) : 
  bipermutation (n - 2) (fun k => f (k + 2) - 2).
Proof.
  intros k Hk.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (Hf (k + 2)).
  assert (2 <= f (k + 2)). 1: {
    enough (~ (f (k + 2) = 0 \/ f (k + 2) = 1)) by lia.
    rewrite 2!(bipermutation_eq_iff _ _ Hf) by lia.
    rewrite 2!Hfsmall by lia.
    cbn; lia.
  }
  repeat split.
  - lia.
  - lia. 
  - rewrite Nat.sub_add by lia; lia.
Qed.

Lemma bipermutation_shrink_of_eq_swap n f 
  (Hf : bipermutation n f) 
  (Hfbig : perm_eq 2 
    (fun k => f ((n - 2) + k)) (fun k => swap_2_perm k + (n - 2))) : 
  bipermutation (n - 2) f.
Proof.
  intros k Hk.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (Hf k ltac:(lia)).
  repeat split; [|easy..].
  enough (~ (f k = n - 2 \/ f k = n - 1)) by lia.
  rewrite 2!(bipermutation_eq_iff _ _ Hf) by lia.
  replace (n - 2) with (n - 2 + 0) by lia.
  replace (n - 1) with (n - 2 + 1) by lia.
  rewrite 2!Hfbig by lia.
  lia.
Qed.

Definition compose_perm_biperm n f g :=
  make_WF_Perm n (g ∘ f ∘ perm_inv n g).

Lemma compose_perm_biperm_defn n f g :
  perm_eq n (compose_perm_biperm n f g) 
    (g ∘ f ∘ perm_inv n g).
Proof.
  apply make_WF_Perm_perm_eq.
Qed.

Lemma compose_perm_bipermutation n f g 
  (Hf : bipermutation n f) (Hg : permutation n g) :
  bipermutation n (compose_perm_biperm n f g).
Proof.
  rewrite compose_perm_biperm_defn.
  apply by_bipermutation_defn_alt.
  - auto with perm_db.
  - intros k Hk.
    unfold compose.
    symmetry.
    rewrite <- (perm_inv_eq_iff Hg) by auto with perm_bounded_db.
    symmetry.
    apply Hf; cleanup_perm_inv.
  - rewrite 2!perm_inv_compose by auto_biperm.
    rewrite (perm_inv_bipermutation n f Hf).
    rewrite perm_inv_perm_inv by auto.
    reflexivity.
Qed.

#[export] Hint Resolve compose_perm_bipermutation : biperm_db.

Lemma compose_perm_biperm_WF n f g : WF_Perm n (compose_perm_biperm n f g).
Proof.
  apply make_WF_Perm_WF.
Qed.

#[export] Hint Resolve compose_perm_biperm_WF : WF_Perm_db.

Lemma compose_perm_biperm_compose n f g h 
  (Hg : permutation n g) (Hh : permutation n h) :
  compose_perm_biperm n (compose_perm_biperm n f g) h =
  compose_perm_biperm n f (h ∘ g).
Proof.
  eq_by_WF_perm_eq n.
  rewrite !compose_perm_biperm_defn.
  now rewrite perm_inv_compose.
Qed.

Lemma compose_perm_biperm_idn n f : 
  perm_eq n (compose_perm_biperm n f idn) f.
Proof.
  rewrite compose_perm_biperm_defn, idn_inv.
  easy.
Qed.

Lemma biperm_conj_inv_perm_l_bipermutation n f g g' 
  (Hf : bipermutation n f) (Hg : permutation n g) 
  (Hg' : perm_eq n g' (perm_inv n g)) : 
  bipermutation n (g' ∘ f ∘ g).
Proof.
  rewrite Hg'.
  rewrite <- (perm_inv_perm_inv n g Hg) at 2.
  rewrite <- compose_perm_biperm_defn.
  auto_biperm.
Qed.

Lemma biperm_conj_inv_perm_r_bipermutation n f g g' 
  (Hf : bipermutation n f) (Hg : permutation n g) 
  (Hg' : perm_eq n g' (perm_inv n g)) : 
  bipermutation n (g ∘ f ∘ g').
Proof.
  rewrite Hg'.
  rewrite <- compose_perm_biperm_defn.
  auto_biperm.
Qed.

Add Parametric Morphism n : (compose_perm_biperm n) with signature
  on_predicate_relation_l (fun f => perm_bounded n f)
    (perm_eq n) ==> 
  (perm_eq n) ==> eq as compose_perm_biperm_perm_eq_bounded_to_eq.
Proof.
  intros f f' [Hfbdd Hf] g g' Hg. 
  eq_by_WF_perm_eq n.
  rewrite 2!compose_perm_biperm_defn.
  rewrite Hg at 2.
  rewrite <- Hf.
  now rewrite Hg.
Qed.

Add Parametric Morphism n : (compose_perm_biperm n) with signature
  perm_eq n ==> eq ==> eq as compose_perm_biperm_perm_eq_eq_to_eq.
Proof.
  intros f f' Hf g.
  eq_by_WF_perm_eq n.
  rewrite 2!compose_perm_biperm_defn.
  now rewrite Hf.
Qed.


Definition biperm_compose_perm_l n m f g : nat -> nat :=
  (* f is a biperm on n + m, g a perm on n; 
     graphically, we put g on the left of f *)
  compose_perm_biperm (n + m) f (stack_perms n m g idn).

Lemma biperm_compose_perm_l_defn n m f g : 
  perm_eq (n + m) (biperm_compose_perm_l n m f g) 
    (stack_perms n m g idn ∘ f ∘ perm_inv (n + m) (stack_perms n m g idn)).
Proof.
  apply compose_perm_biperm_defn.
Qed.

Lemma biperm_compose_perm_l_defn_alt n m f g (Hg : permutation n g) : 
  perm_eq (n + m) (biperm_compose_perm_l n m f g) 
  (fun k => 
  if k <? n then
    (if f (perm_inv n g k) <? n then 
      g (f (perm_inv n g k))
    else 
      f (perm_inv n g k))
  else
    (if k <? n + m then 
      (if f k <? n then 
        g (f k)
      else
        f k)
    else 
      k)).
Proof.
  unfold biperm_compose_perm_l.
  rewrite compose_perm_biperm_defn.
  rewrite perm_inv_stack_perms by auto_perm.
  rewrite idn_inv.
  rewrite 2!stack_perms_f_idn.
  unfold compose.
  intros k Hk.
  bdestructΩ'.
Qed.

Definition biperm_compose_perm_r n m f g : nat -> nat :=
  (* f is a biperm on n + m, g a perm on m; 
     graphically, we put g on the right of f *)
  compose_perm_biperm (n + m) f (stack_perms n m idn (perm_inv m g)).

Lemma biperm_compose_perm_r_defn n m f g :
  perm_eq (n + m) (biperm_compose_perm_r n m f g) 
    (stack_perms n m idn (perm_inv m g) ∘ f 
      ∘ perm_inv (n + m) (stack_perms n m idn (perm_inv m g))).
Proof.
  apply compose_perm_biperm_defn.
Qed.

Lemma biperm_compose_perm_r_defn' n m f g 
  (Hg : permutation m g) : 
  perm_eq (n + m) (biperm_compose_perm_r n m f g) 
    (stack_perms n m idn (perm_inv m g) ∘ f ∘ stack_perms n m idn g).
Proof.
  rewrite biperm_compose_perm_r_defn.
  now rewrite perm_inv_stack_perms, (perm_inv_perm_inv m g), 
    idn_inv by auto_perm.
Qed.


Lemma biperm_compose_perm_r_defn_alt n m f g 
  (Hf : perm_bounded (n + m) f) (Hg : permutation m g) : 
  perm_eq (n + m) (biperm_compose_perm_r n m f g)
  (fun k => 
  if k <? n then 
    if f k <? n then f k else
      n + perm_inv m g (f k - n)
  else 
    if f (n + g (k - n)) <? n then 
      f (n + g (k - n))
    else
      n + perm_inv m g (f (n + g (k - n)) - n)).
Proof.
  rewrite biperm_compose_perm_r_defn' by auto.
  rewrite 2!stack_perms_defn.
  unfold compose.
  intros k Hk.
  rewrite (Nat.add_comm _ n).
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_l_WF n m f g :
  WF_Perm (n + m) (biperm_compose_perm_l n m f g).
Proof.
  apply compose_perm_biperm_WF.
Qed.

Lemma biperm_compose_perm_r_WF n m f g :
  WF_Perm (n + m) (biperm_compose_perm_r n m f g).
Proof.
  apply compose_perm_biperm_WF.
Qed.

#[export] Hint Resolve biperm_compose_perm_l_WF
  biperm_compose_perm_r_WF : WF_Perm_db. 

Add Parametric Morphism n m : (biperm_compose_perm_r n m) with signature
  (* on_predicate_relation_l (fun f => perm_bounded (n + m) f)  *)
    (perm_eq (n + m)) ==> 
  (* on_predicate_relation_l (fun f => perm_bounded m f)  *)
    (perm_eq m) ==> eq as 
    biperm_compose_perm_r_eq_of_perm_eq.
Proof.
  intros f f' Hf g g' Hg.
  eq_by_WF_perm_eq (n + m).
  rewrite 2!biperm_compose_perm_r_defn, 2!compose_assoc.
  now rewrite Hf, Hg.
Qed.

Add Parametric Morphism n m : (biperm_compose_perm_l n m) with signature
  (* on_predicate_relation_l (fun f => perm_bounded (n + m) f)  *)
    (perm_eq (n + m)) ==> 
  (* on_predicate_relation_l (fun f => perm_bounded n f)  *)
    (perm_eq n) ==> eq as 
    biperm_compose_perm_l_eq_of_perm_eq.
Proof.
  intros f f' Hf g g' Hg.
  eq_by_WF_perm_eq (n + m).
  rewrite 2!biperm_compose_perm_l_defn, 2!compose_assoc.
  now rewrite Hf, Hg.
Qed.

Lemma biperm_compose_perm_l_bounded n m f g 
  (Hf : perm_bounded (n + m) f) (Hg : perm_bounded n g) :
  perm_bounded (n + m) (biperm_compose_perm_l n m f g).
Proof.
  intros k Hk.
  rewrite biperm_compose_perm_l_defn by auto.
  rewrite compose_assoc.
  auto_perm.
Qed.

Lemma biperm_compose_perm_r_bounded n m f g 
  (Hf : perm_bounded (n + m) f) (Hg : perm_bounded m g) :
  perm_bounded (n + m) (biperm_compose_perm_r n m f g).
Proof.
  intros k Hk.
  rewrite biperm_compose_perm_r_defn by auto.
  rewrite compose_assoc.
  auto_perm.
Qed.

#[export] Hint Resolve biperm_compose_perm_l_bounded
  biperm_compose_perm_r_bounded : perm_bounded_db. 



Lemma biperm_compose_perm_r_biperm n m f g 
  (Hf : bipermutation (n + m) f) (Hg : permutation m g) : 
  bipermutation (n + m) (biperm_compose_perm_r n m f g).
Proof.
  unfold biperm_compose_perm_r.
  auto_biperm.
Qed.

Lemma biperm_compose_perm_l_biperm n m f g 
  (Hf : bipermutation (n + m) f) (Hg : permutation n g) : 
  bipermutation (n + m) (biperm_compose_perm_l n m f g).
Proof.
  unfold biperm_compose_perm_l.
  auto_biperm.
Qed.

#[export] Hint Resolve biperm_compose_perm_l_biperm
  biperm_compose_perm_r_biperm : biperm_db.

Lemma biperm_compose_perm_l_compose n m f g h 
  (Hf : bipermutation (n + m) f)
  (Hg : permutation n g) (Hh : permutation n h) :
  biperm_compose_perm_l n m (biperm_compose_perm_l n m f g) h =
  biperm_compose_perm_l n m f (h ∘ g)%prg.
Proof.
  eq_by_WF_perm_eq (n + m).
  unfold biperm_compose_perm_l.
  rewrite compose_perm_biperm_compose by auto_perm.
  now rewrite stack_perms_compose_idn by auto_perm.
Qed.

Lemma biperm_compose_perm_r_compose n m f g h 
  (Hg : permutation m g) (Hh : permutation m h) :
  biperm_compose_perm_r n m (biperm_compose_perm_r n m f g) h =
  biperm_compose_perm_r n m f (g ∘ h).
Proof.
  eq_by_WF_perm_eq (n + m).
  unfold biperm_compose_perm_r.
  rewrite compose_perm_biperm_compose by auto_perm.
  now rewrite perm_inv_compose, stack_perms_idn_compose by auto_perm.
Qed.

Lemma biperm_compose_perm_l_r_swap n m f g h : 
  (* bipermutation (n + m) f -> *) permutation n g -> permutation m h ->
  biperm_compose_perm_l n m (biperm_compose_perm_r n m f h) g =
  biperm_compose_perm_r n m (biperm_compose_perm_l n m f g) h.
Proof.
  intros Hg Hh.
  unfold biperm_compose_perm_l, biperm_compose_perm_r.
  rewrite 2!compose_perm_biperm_compose by auto_perm.
  now rewrite <- stack_perms_diag_split, <- stack_perms_antidiag_split 
    by auto_perm.
Qed.

Lemma biperm_compose_perm_l_0_r n f g (Hf : perm_bounded n f) : 
  biperm_compose_perm_l n 0 f g = compose_perm_biperm n f g.
Proof.
  eq_by_WF_perm_eq (n + 0);
  [rewrite Nat.add_0_r; now auto_perm..|].
  rewrite biperm_compose_perm_l_defn.
  rewrite stack_perms_0_r, Nat.add_0_r.
  do 2 rewrite make_WF_Perm_perm_eq at 1.
  now rewrite compose_perm_biperm_defn.
Qed.

Lemma biperm_compose_perm_r_0_l m f g (Hf : perm_bounded m f) : 
  biperm_compose_perm_r 0 m f g = compose_perm_biperm m f (perm_inv m g).
Proof.
  eq_by_WF_perm_eq _.
  rewrite biperm_compose_perm_r_defn.
  rewrite stack_perms_0_l.
  do 2 rewrite make_WF_Perm_perm_eq at 1.
  now rewrite compose_perm_biperm_defn.
Qed.

(* Lemma biperm_compose_perm_r_lt_small n m f g : 
  forall k, k < n ->
  biperm_compose_perm_r n m f g k < n <-> f k < n.
Proof.
  intros k Hk.
  unfold biperm_compose_perm_r.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_r_lt_big n m f g : 
  forall k, n <= k -> k < n + m ->
  biperm_compose_perm_r n m f g k < n <-> f (n + g (k - n)) < n.
Proof.
  intros k Hkl Hku.
  unfold biperm_compose_perm_r.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_r_ltb_small n m f g : 
  forall k, k < n ->
  biperm_compose_perm_r n m f g k <? n = (f k <? n).
Proof.
  intros k Hk.
  unfold biperm_compose_perm_r.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_r_ltb_big n m f g : 
  forall k, n <= k -> k < n + m ->
  biperm_compose_perm_r n m f g k <? n = (f (n + g (k - n)) <? n).
Proof.
  intros k Hkl Hku.
  unfold biperm_compose_perm_r.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed. *)

(* Lemma biperm_compose_perm_l_lt_small n m f g : 
  forall k, k < n ->
  biperm_compose_perm_l n m f g k < n <-> f (g k) < n.
Proof.
  intros k Hk.
  unfold biperm_compose_perm_l.
  simplify_bools_lia_one_kernel.
  pose proof (perm_inv_bounded n g (f (g k))).
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_l_lt_big n m f g : 
  forall k, n <= k -> k < n + m ->
  biperm_compose_perm_l n m f g k < n <-> f k < n.
Proof.
  intros k Hkl Hku.
  unfold biperm_compose_perm_l.
  do 2 simplify_bools_lia_one_kernel.
  pose proof (perm_inv_bounded n g (f k)).
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_l_ltb_small n m f g : 
  forall k, k < n ->
  biperm_compose_perm_l n m f g k <? n = (f (g k) <? n).
Proof.
  intros k Hk.
  unfold biperm_compose_perm_l.
  simplify_bools_lia_one_kernel.
  pose proof (perm_inv_bounded n g (f (g k))).
  bdestructΩ'.
Qed.

Lemma biperm_compose_perm_l_ltb_big n m f g : 
  forall k, n <= k -> k < n + m ->
  biperm_compose_perm_l n m f g k <? n = (f k <? n).
Proof.
  intros k Hkl Hku.
  unfold biperm_compose_perm_l.
  do 2 simplify_bools_lia_one_kernel.
  pose proof (perm_inv_bounded n g (f k)).
  bdestructΩ'.
Qed. *)


Lemma biperm_compose_perm_r_idn n m f 
  (Hf : perm_bounded (n + m) f) : 
  perm_eq (n + m) (biperm_compose_perm_r n m f idn) f.
Proof.
  unfold biperm_compose_perm_r.
  rewrite idn_inv, stack_perms_idn_idn.
  apply compose_perm_biperm_idn.
Qed.

Lemma biperm_compose_perm_l_idn n m f 
  (Hf : perm_bounded (n + m) f) : 
  perm_eq (n + m) (biperm_compose_perm_l n m f idn) f.
Proof.
  unfold biperm_compose_perm_l.
  rewrite stack_perms_idn_idn.
  apply compose_perm_biperm_idn.
Qed.


Definition stack_biperms (n0 m0 n1 m1 : nat) (f g : nat -> nat) : nat -> nat :=
  compose_perm_biperm (n0 + n1 + (m0 + m1)) 
    (stack_perms (n0 + m0) (n1 + m1) f g)
    (stack_perms (n0 + m0 + n1) m1
      (stack_perms n0 (m0 + n1) idn 
        (big_swap_perm m0 n1)) idn).

Lemma stack_biperms_defn n0 m0 n1 m1 f g :
  perm_eq (n0 + n1 + (m0 + m1)) 
  (stack_biperms n0 m0 n1 m1 f g)
  ((stack_perms (n0 + m0 + n1) m1
    (stack_perms n0 (m0 + n1) idn 
      (big_swap_perm m0 n1)) idn) ∘
    (stack_perms (n0 + m0) (n1 + m1) f g) ∘
   (stack_perms (n0 + m0 + n1) m1
    (stack_perms n0 (m0 + n1) idn 
      (big_swap_perm n1 m0)) idn)).
Proof.
  unfold stack_biperms.
  rewrite compose_perm_biperm_defn.
  replace (n0 + n1 + (m0 + m1)) with (n0 + m0 + (n1 + m1)) by lia.
  rewrite Nat.add_assoc.
  (* replace (n0 + m0 + (n1 + m1)) with (n0 + m0 + n1 + m1) by lia. *)
  (* eapply perm_eq_dim_change_if_nonzero; *)
  rewrite perm_inv_stack_perms by auto_perm.
  rewrite <- (Nat.add_assoc n0 m0 n1). 
  rewrite perm_inv_stack_perms by auto_perm.
  rewrite (stack_perms_perm_eq_to_eq_proper n0 (m0 + n1)
    _ _ (idn_inv n0) _ _ (big_swap_perm_inv m0 n1)).
  rewrite idn_inv.
  easy.
Qed.

Lemma stack_biperms_defn_alt n0 m0 n1 m1 f g 
  (Hf : perm_bounded (n0 + m0) f)
  (Hg : perm_bounded (n1 + m1) g) :
  perm_eq (n0 + n1 + (m0 + m1)) 
  (stack_biperms n0 m0 n1 m1 f g)
  (fun k =>
  if k <? n0 then 
    if f k <? n0 then f k else n1 + f k
  else if k - n0 <? n1 then 
    if g (k - n0) <? n1 then n0 + g (k - n0) else n0 + m0 + g (k - n0)
  else if k - (n0 + n1) <? m0 then
    if f (k - n1) <? n0 then f (k - n1) else n1 + f (k - n1)
  else (* n0 + n1 + m0 < k < n0 + n1 + m0 + m1 *)
    if g (k - (n0 + m0)) <? n1 then n0 + g (k - (n0 + m0)) 
      else n0 + m0 + g (k - (n0 + m0))).
Proof.
  rewrite stack_biperms_defn.
  replace (n0 + n1 + (m0 + m1)) with (n0 + m0 + (n1 + m1)) by lia.
  rewrite (stack_perms_defn _ _ f g).

  rewrite big_swap_perm_defn, 
    (stack_perms_perm_eq_to_eq_proper n0 (m0 + n1)
    _ _ (perm_eq_refl n0 idn) _ _ (big_swap_perm_defn_alt n1 m0)).
  rewrite <- (Nat.add_assoc n0 m0 n1).
  rewrite 2!(stack_perms_defn n0 (m0 + n1)).
  rewrite (Nat.add_assoc n0 m0 n1).
  rewrite <- (Nat.add_assoc n0 m0 n1) at 1.
  rewrite Nat.add_assoc.
  rewrite 2!stack_perms_f_idn.
  intros k Hk.
  unfold compose.
  rewrite !(if_dist nat nat).
  pose proof (Hf k).
  pose proof (Hf (k - n1)).
  assert (sub_add_four : forall a b c, a <= b -> b - a + c + a = b + c)
    by lia.
  assert (add_sub_four : forall a b c, b + a - c - a = b - c)
    by lia.
  assert (sub_sub_four : forall a b c, a + c <= b -> b - a - c + a = b - c)
    by lia.
  bdestructΩ'_with ltac:(
    try first [
      rewrite sub_add_four by lia |
      rewrite 1?Nat.sub_add_distr, add_sub_four |
      rewrite sub_sub_four by lia
    ]; 
    try reflexivity; try lia).
Qed.

Lemma stack_biperms_WF n0 m0 n1 m1 f g :
  WF_Perm (n0 + n1 + (m0 + m1)) (stack_biperms n0 m0 n1 m1 f g).
Proof.
  unfold stack_biperms.
  auto_perm.
Qed.

#[export] Hint Resolve stack_biperms_WF : WF_Perm_db.

Lemma stack_biperms_bounded n0 m0 n1 m1 f g : 
  perm_bounded (n0 + m0) f -> perm_bounded (n1 + m1) g ->
  perm_bounded (n0 + n1 + (m0 + m1)) (stack_biperms n0 m0 n1 m1 f g).
Proof.
  intros Hf Hg k Hk.
  rewrite stack_biperms_defn by auto.
  revert k Hk.
  rewrite Combinators.compose_assoc.
  now auto_perm.
Qed.

#[export] Hint Resolve stack_biperms_bounded : perm_bounded_db.

Lemma stack_biperms_eq_of_perm_eq 
  {n0 m0 f f'} (Hf : perm_eq (n0 + m0) f f') 
  {n1 m1 g g'} (Hg : perm_eq (n1 + m1) g g')
  : stack_biperms n0 m0 n1 m1 f g = stack_biperms n0 m0 n1 m1 f' g'.
Proof.
  unfold stack_biperms.
  now rewrite Hf, Hg.
Qed.

Add Parametric Morphism n0 m0 n1 m1 
  : (stack_biperms n0 m0 n1 m1) 
  with signature
  perm_eq (n0 + m0) ==> perm_eq (n1 + m1) ==> eq
  as stack_biperms_eq_of_perm_eq_proper.
Proof.
  intros.
  now apply stack_biperms_eq_of_perm_eq.
Qed.

Lemma stack_biperms_eq_of_perm_eq'
  {nm0 f f'} (Hf : perm_eq nm0 f f') 
  {g g' nm1} (Hg : perm_eq nm1 g g') n0 m0 n1 m1  
  (H0 : n0 + m0 = nm0) (H1 : n1 + m1 = nm1)
  : stack_biperms n0 m0 n1 m1 f g = stack_biperms n0 m0 n1 m1 f' g'.
Proof.
  subst nm0 nm1.
  now apply stack_biperms_eq_of_perm_eq.
Qed.

Lemma stack_biperms_bipermutation {n0 n1 m0 m1} {f g} 
  (Hf : bipermutation (n0 + m0) f) (Hg : bipermutation (n1 + m1) g) :
  bipermutation (n0 + n1 + (m0 + m1)) (stack_biperms n0 m0 n1 m1 f g).
Proof.
  unfold stack_biperms.
  apply compose_perm_bipermutation; [|auto_perm].
  apply by_bipermutation_defn_alt.
  - auto_perm.
  - intros k Hk.
    rewrite stack_perms_defn by lia.
    bdestruct_one.
    + apply Hf; lia.
    + pose proof (Hg (k - (n0 + m0))); lia.
  - replace (n0 + n1 + (m0 + m1)) with (n0 + m0 + (n1 + m1)) by lia.
    rewrite perm_inv_stack_perms by auto_perm.
    now rewrite 2!perm_inv_bipermutation by auto.
Qed.

#[export] Hint Resolve stack_biperms_bipermutation : biperm_db.
#[export] Hint Extern 5 (bipermutation ?nm 
  (stack_biperms ?n0 ?m0 ?n1 ?m1 ?f ?g)) =>
  apply (bipermutation_change_dims nm (n0 + n1 + (m0 + m1)) 
    (stack_biperms n0 m0 n1 m1 f g) ltac:(lia));
  apply stack_biperms_bipermutation : biperm_db.

#[export] Hint Extern 3 (WF_Perm ?nm 
  (stack_biperms ?n0 ?m0 ?n1 ?m1 ?f ?g)) =>
  apply (WF_Perm_change_dims nm (n0 + n1 + (m0 + m1)) 
    (stack_biperms n0 m0 n1 m1 f g) ltac:(lia));
  apply stack_biperms_WF : WF_Perm_db.

#[export] Hint Extern 3 (perm_bounded ?nm 
  (stack_biperms ?n0 ?m0 ?n1 ?m1 ?f ?g)) =>
  apply (perm_bounded_change_dims nm (n0 + n1 + (m0 + m1)) 
    ltac:(lia) (stack_biperms n0 m0 n1 m1 f g));
  apply stack_biperms_bounded : perm_bounded_db.



Lemma stack_biperms_0_out n0 n1 m1 f g : 
  stack_biperms n0 0 n1 m1 f g = 
  stack_perms n0 (n1 + m1) f g.
Proof.
  eq_by_WF_perm_eq (n0 + n1 + (0 + m1)).
  rewrite stack_biperms_defn.
  rewrite big_swap_perm_0_l, big_swap_perm_0_r.
  rewrite !stack_perms_idn_idn, Nat.add_0_r.
  easy.
Qed.

Lemma stack_biperms_0_in n0 m0 m1 f g : 
  stack_biperms n0 m0 0 m1 f g = 
  stack_perms (n0 + m0) m1 f g.
Proof.
  eq_by_WF_perm_eq (n0 + 0 + (m0 + m1)).
  rewrite stack_biperms_defn.
  rewrite big_swap_perm_0_l, big_swap_perm_0_r.
  rewrite !stack_perms_idn_idn.
  easy.
Qed.

Definition idn_biperm (n : nat) : nat -> nat :=
  big_swap_perm n n.

Lemma idn_biperm_bipermutation n : 
  bipermutation (n + n) (idn_biperm n).
Proof.
  unfold idn_biperm.
  apply by_bipermutation_defn_alt; [auto_perm| |cleanup_perm_inv].
  intros k Hk; unfold big_swap_perm; bdestructΩ'.
Qed.

#[export] Hint Resolve idn_biperm_bipermutation : biperm_db.

Lemma idn_biperm_defn n : 
  perm_eq (n + n) (idn_biperm n)
  (fun k => if k <? n then k + n else k - n).
Proof.
  apply big_swap_perm_defn.
Qed.

Lemma idn_biperm_WF n : WF_Perm (n + n) (idn_biperm n).
Proof.
  unfold idn_biperm.
  auto_perm.
Qed.

#[export] Hint Resolve idn_biperm_WF : WF_Perm_db.

Lemma idn_biperm_eq n : idn_biperm n = big_swap_perm n n.
Proof. reflexivity. Qed.

Definition flip_biperm n m (f : nat -> nat) : nat -> nat :=
  compose_perm_biperm (m + n) f (big_swap_perm n m).

Lemma flip_biperm_defn n m f : 
  perm_eq (m + n) (flip_biperm n m f) 
    (big_swap_perm n m ∘ f ∘ big_swap_perm m n).
Proof.
  unfold flip_biperm.
  rewrite compose_perm_biperm_defn.
  now rewrite big_swap_perm_inv_change_dims by lia.
Qed.

Lemma flip_biperm_defn_alt n m f :
  perm_eq (m + n) (flip_biperm n m f) 
    (fun k =>
    let outval :=
      if k <? m then f (k + n) else 
      if k <? n + m then f (k - m) else f k 
    in
      if outval <? n then outval + m else 
      if outval <? n + m then outval - n else outval).
Proof.
  rewrite flip_biperm_defn.
  rewrite (big_swap_perm_defn m n).
  intros k Hk.
  simplify_bools_lia_one_kernel.
  unfold compose, big_swap_perm.
  bdestructΩ'.
Qed.

Lemma flip_biperm_bipermutation n m f (Hf : bipermutation (n + m) f) : 
  bipermutation (m + n) (flip_biperm n m f).
Proof.
  unfold flip_biperm.
  rewrite Nat.add_comm.
  auto_biperm.
Qed.

#[export] Hint Resolve flip_biperm_bipermutation : biperm_db.

Lemma flip_biperm_WF n m f : 
  WF_Perm (m + n) (flip_biperm n m f).
Proof.
  apply compose_perm_biperm_WF.
Qed.

#[export] Hint Resolve flip_biperm_WF : WF_Perm_db.

Add Parametric Morphism n m : (flip_biperm n m) with signature 
  perm_eq (n + m) ==> eq as flip_biperm_eq_of_perm_eq.
Proof.
  unfold flip_biperm.
  rewrite Nat.add_comm.
  now intros f g ->.
Qed.

Lemma flip_biperm_stack_biperms n0 m0 n1 m1 f g 
  (Hf : perm_bounded (n0 + m0) f) (Hg : perm_bounded (n1 + m1) g) : 
  flip_biperm (n0 + n1) (m0 + m1) (stack_biperms n0 m0 n1 m1 f g) =
  stack_biperms m0 n0 m1 n1 (flip_biperm n0 m0 f) (flip_biperm n1 m1 g).
Proof.
  eq_by_WF_perm_eq (m0 + m1 + (n0 + n1)).
  symmetry.
  rewrite stack_biperms_defn.
  symmetry.
  rewrite flip_biperm_defn, Nat.add_comm, stack_biperms_defn.
  rewrite 2!flip_biperm_defn.
  rewrite <- stack_perms_compose by auto_perm.
  symmetry.
  rewrite <- compose_assoc, compose_assoc.
  symmetry.
  rewrite <- compose_perm_inv_r by auto_perm.
  rewrite perm_inv_compose by auto_perm.
  rewrite 2!(perm_inv_stack_perms_change_dims (n0 + n1 + (m0 + m1))) 
    by (lia + auto_perm).
  etransitivity.
  1: {
    apply compose_perm_eq_proper_r.
    rewrite (perm_inv_stack_perms_change_dims) by lia + auto_perm.
    rewrite idn_inv, 2!big_swap_perm_inv.
    rewrite big_swap_perm_inv_change_dims by lia.
    reflexivity.
  }
  rewrite !compose_assoc.
  pose proof (big_swap_perm_pair_mid_l m0 m1 n0 n1).
  replace (n0 + m0 + n1) with (m0 + n0 + n1) by lia.
  rewrite_compose_assoc_r big_swap_perm_pair_mid_l.
  replace (m0 + n0 + m1) with (m0 + m1 + n0) by lia.
  rewrite_compose_assoc_r @stack_perms_compose; [|auto_perm..].
  rewrite (Nat.add_comm n0 m1).
  rewrite stack_perms_compose by auto_perm.
  rewrite big_swap_perm_invol.
  rewrite !compose_idn_l, idn_inv.
  rewrite !stack_perms_idn_idn, compose_idn_l.
  rewrite stack_perms_compose by auto_perm.
  rewrite 2!big_swap_perm_invol, stack_perms_idn_idn, compose_idn_r.
  rewrite <- !compose_assoc.
  rewrite big_swap_perm_pair_mid_r.
  rewrite (Nat.add_comm m0 n0), (Nat.add_comm m1 n1).
  rewrite <- stack_perms_compose, <- compose_assoc by auto_perm.
  easy.
Qed.

Lemma flip_biperm_compose_perm_l n m f g 
  (Hg : permutation n g) : 
  flip_biperm n m (biperm_compose_perm_l n m f g) = 
  biperm_compose_perm_r m n (flip_biperm n m f) (perm_inv n g).
Proof.
  eq_by_WF_perm_eq (m + n).
  rewrite flip_biperm_defn.
  rewrite biperm_compose_perm_r_defn, flip_biperm_defn.
  rewrite Nat.add_comm, biperm_compose_perm_l_defn.
  rewrite perm_inv_perm_inv by auto.
  rewrite perm_inv_stack_perms, perm_inv_stack_perms_change_dims by 
    (lia + auto_perm).
  rewrite !compose_assoc.
  rewrite stack_perms_big_swap_natural by auto_perm.
  rewrite <- !compose_assoc.
  now rewrite stack_perms_big_swap_natural by auto_perm.
Qed.

Lemma flip_biperm_compose_perm_r n m f g 
  (Hg : permutation m g) : 
  flip_biperm n m (biperm_compose_perm_r n m f g) = 
  biperm_compose_perm_l m n (flip_biperm n m f) (perm_inv m g).
Proof.
  eq_by_WF_perm_eq (m + n).
  rewrite flip_biperm_defn.
  rewrite biperm_compose_perm_l_defn, flip_biperm_defn.
  rewrite Nat.add_comm, biperm_compose_perm_r_defn.
  rewrite !compose_assoc.
  rewrite perm_inv_stack_perms, perm_inv_stack_perms_change_dims by 
    (lia + auto_perm).
  rewrite stack_perms_big_swap_natural by auto_perm.
  rewrite <- !compose_assoc.
  now rewrite stack_perms_big_swap_natural by auto_perm.
Qed.

Lemma flip_biperm_invol n m f : 
  perm_eq (n + m) (flip_biperm m n (flip_biperm n m f)) f.
Proof.
  (rewrite_strat innermost flip_biperm_defn).
  rewrite flip_biperm_defn.
  rewrite !compose_assoc.
  rewrite big_swap_perm_invol, compose_idn_r.
  rewrite <- compose_assoc.
  now rewrite big_swap_perm_invol.
Qed.

Lemma flip_biperm_idn n : 
  flip_biperm n n (idn_biperm n) = 
  idn_biperm n.
Proof.
  eq_by_WF_perm_eq (n + n).
  unfold idn_biperm.
  rewrite flip_biperm_defn.
  now rewrite big_swap_perm_invol.
Qed.

Lemma flip_biperm_0_l m f : 
  perm_eq (m + 0) (flip_biperm 0 m f) f.
Proof.
  rewrite flip_biperm_defn.
  now rewrite big_swap_perm_0_l, big_swap_perm_0_r.
Qed.

Lemma flip_biperm_0_r n f : 
  perm_eq (0 + n) (flip_biperm n 0 f) f.
Proof.
  rewrite flip_biperm_defn.
  now rewrite big_swap_perm_0_l, big_swap_perm_0_r.
Qed.

Definition contract_biperm k l f :=
  if (k <? l) then 
    contract_perm (contract_perm f l) k
  else 
    contract_perm (contract_perm f k) l.

Add Parametric Morphism n k l (Hk : k < n) 
  (Hl : l < n) (Hkl : k <> l) : (contract_biperm k l) with signature
  perm_eq n ==> 
  perm_eq (n - 2) as contract_biperm_perm_eq_proper.
Proof.
  intros f g Hfg.
  unfold contract_biperm.
  replace (n - 2) with (n - 1 - 1) by lia.
  bdestructΩ'; now rewrite Hfg.
Qed.

Lemma contract_biperm_comm f k l : 
  contract_biperm k l f = contract_biperm l k f.
Proof.
  unfold contract_biperm.
  bdestructΩ'.
  now replace k with l by lia.
Qed.

Lemma contract_biperm_bounded n f 
  (Hf : perm_bounded n f) k l (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_bounded (n - 2) (contract_biperm k l f).
Proof.
  unfold contract_biperm.
  replace (n - 2) with (n - 1 - 1) by lia.
  bdestructΩ';
  repeat apply contract_perm_bounded; lia + auto.
Qed.

#[export] Hint Resolve contract_biperm_bounded : perm_bounded_db.

Lemma contract_biperm_permutation n f 
  (Hf : permutation n f) k l (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  permutation (n - 2) (contract_biperm k l f).
Proof.
  unfold contract_biperm.
  replace (n - 2) with (n - 1 - 1) by lia.
  bdestructΩ';
  repeat apply contract_perm_permutation; 
  auto with perm_bounded_db zarith.
Qed.

#[export] Hint Resolve contract_biperm_permutation : perm_db.

Lemma contract_biperm_inv n f 
  (Hf : permutation n f) k l (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  perm_eq (n - 2) (perm_inv (n - 2) (contract_biperm k l f))
    (contract_biperm (f k) (f l) (perm_inv n f)).
Proof.
  replace (n - 2) with (n - 1 - 1) by lia.
  unfold contract_biperm.
  bdestructΩ'.
  - cleanup_perm_inv.
    replace (contract_perm f l k) with (f k); [easy|].
    unfold contract_perm.
    bdestructΩ'.
  - cleanup_perm_inv.
    replace (contract_perm f l k) with (f k - 1) 
      by (unfold contract_perm; bdestructΩ').
    intros i Hi.
    unfold contract_perm.
    pose proof (permutation_is_injective n f Hf k l).
    rewrite Nat.sub_add by lia.
    rewrite !perm_inv_is_linv_of_permutation by cleanup_perm.
    replace_bool_lia (f k - 1 <? f l) false.
    replace_bool_lia (f l <? f k) true.
    replace_bool_lia (k <? l) true.
    replace_bool_lia (l <? k) false.
    repeat match goal with |- context[ i <? ?a] =>
      bdestruct (i <? a); try lia
    end.
    + bdestructΩ'.
    + replace_bool_lia (i + 1 <? f k) true.
      bdestructΩ'.
    + bdestructΩ'.
  - cleanup_perm_inv.
    erewrite contract_perm_perm_eq_of_perm_eq.
    3: (apply contract_perm_inv; auto).
    2: (pose proof (permutation_is_bounded n f Hf l Hl); 
      unfold contract_perm; bdestructΩ').
    replace (contract_perm f k l) with (f l - 1) by
      (unfold contract_perm; bdestructΩ').
    intros i Hi.
    unfold contract_perm.
    pose proof (permutation_is_injective n f Hf k l).
    rewrite Nat.sub_add by lia.
    rewrite !perm_inv_is_linv_of_permutation by cleanup_perm.
    replace_bool_lia (f l - 1 <? f k) false.
    replace_bool_lia (f k <? f l) true.
    replace_bool_lia (k <? l) false.
    replace_bool_lia (l <? k) true.
    repeat match goal with |- context[ i <? ?a] =>
      bdestruct (i <? a); try lia
    end.
    + bdestructΩ'.
    + replace_bool_lia (i + 1 <? f l) true.
      bdestructΩ'.
    + bdestructΩ'.
  - rewrite contract_perm_inv by auto with perm_db zarith.
    pose proof (permutation_is_injective n f Hf k l).
    replace (contract_perm f k l) with (f l) by
      (unfold contract_perm; bdestructΩ').
    pose proof (permutation_is_bounded n f Hf l Hl).
    pose proof (permutation_is_bounded n f Hf k Hk).
    rewrite (contract_perm_inv n f Hf k) by easy.
    easy.
Qed.

Lemma contract_biperm_bipermutation_iff n f 
  (Hf : bipermutation n f) k (Hk : k < n) : 
  bipermutation (n - 2) (contract_biperm k (f k) f) <->
  (forall a, a < n - 2 -> contract_biperm k (f k) f a <> a).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  rewrite bipermutation_defn_alt.
  assert (Hrw : 
    permutation (n - 2) (contract_biperm k (f k) f)
      <-> True). 
  1: {
    intuition idtac.
    apply contract_biperm_permutation;
      try symmetry; try apply Hf; auto with perm_db.
  }
  rewrite Hrw; clear Hrw.
  rewrite and_True_l.
  symmetry.
  rewrite <- (and_True_r (forall k, _ -> _)) at 1.
  apply and_iff_distr_l.
  intros Hne.
  split; [intros _ | easy].
  rewrite contract_biperm_inv by 
    (try (symmetry; apply Hf); auto with perm_db).
  pose proof (Hfne k Hk).
  pose proof (Hfbdd k Hk).
  rewrite Hfeq by lia.
  rewrite contract_biperm_comm.
  erewrite contract_biperm_perm_eq_proper;
  [|easy..|apply (perm_inv_bipermutation n f Hf)].
  easy.
Qed.

Lemma contract_biperm_to_min_max k l f : 
  contract_biperm k l f = 
  contract_perm (contract_perm f (max k l)) (min k l).
Proof.
  unfold contract_biperm.
  rewrite max_ltb, min_ltb.
  now destruct (k <? l).
Qed.


(* Section on n_m_cup_cap, in Bipermutations.v *)
Definition n_m_cup_cap (n m : nat) : nat -> nat :=
  tensor_perms (n + m) 2 idn (swap_2_perm).

Lemma n_m_cup_cap_defn n m : 
  perm_eq (n + n + (m + m)) (n_m_cup_cap n m)
  (fun k => k / 2 * 2 + swap_perm 0 1 2 (k mod 2)).
Proof.
  eapply perm_eq_dim_change_if_nonzero;
  [apply tensor_perms_defn|lia].
Qed. 

Lemma n_m_cup_cap_defn_alt n m : 
  perm_eq (n + n + (m + m))
  (n_m_cup_cap n m)
  (fun k => if Nat.even k then S k else pred k).
Proof.
  rewrite n_m_cup_cap_defn.
  intros k Hk.
  pose proof (Nat.mod_upper_bound k 2 ltac:(lia)) as Hk2.
  rewrite even_eqb.
  unfold swap_2_perm.
  bdestruct_one.
  - replace (k mod 2) with 0 by lia.
    rewrite swap_perm_left by lia.
    pose proof (Nat.div_mod_eq k 2).
    lia.
  - replace (k mod 2) with 1 by lia.
    rewrite swap_perm_right by lia.
    pose proof (Nat.div_mod_eq k 2).
    lia.
Qed.


Lemma n_m_cup_cap_WF n m : 
  WF_Perm (n + n + (m + m)) (n_m_cup_cap n m).
Proof.
  unfold n_m_cup_cap.
  auto_perm.
Qed.

(* Lemma n_m_cup_cap_WF_alt n m : 
  WF_Perm (n + n + (m + m)) (n_m_cup_cap m n).
Proof.
  intros k Hk; unfold n_m_cup_cap; bdestructΩ'.
Qed. *)

#[export] Hint Resolve n_m_cup_cap_WF (* n_m_cup_cap_WF_alt *) : WF_Perm_db.


Lemma n_m_cup_cap_defn_alt_eq n m : 
  (n_m_cup_cap n m) = 
  (fun k => if n + n + (m + m) <=? k then k else 
    if Nat.even k then S k else pred k).
Proof.
  change (n_m_cup_cap n m = make_WF_Perm (n + n + (m + m))
    (fun k => if Nat.even k then S k else pred k)).
  eq_by_WF_perm_eq (n + n + (m + m)).
  rewrite n_m_cup_cap_defn_alt.
  now rewrite make_WF_Perm_perm_eq.
Qed.

Lemma n_m_cup_cap_comm n m : 
  n_m_cup_cap n m = n_m_cup_cap m n.
Proof.
  unfold n_m_cup_cap.
  now rewrite Nat.add_comm.
Qed.


Lemma n_m_cup_cap_bipermutation (n m : nat) : 
  bipermutation (n + n + (m + m)) (n_m_cup_cap n m).
Proof.
  assert (Hev : Nat.even (n + n + (m + m)) = true) by
    now rewrite 3!Nat.even_add, !eqb_reflx.
  replace (n + n + (m + m)) with ((n + m) * 2) by lia.
  apply by_bipermutation_defn_alt; 
  [unfold n_m_cup_cap; auto_perm|..].
  - intros k Hk.
    rewrite n_m_cup_cap_defn by lia.
    pose proof (Nat.div_mod_eq k 2).
    pose proof (Nat.mod_upper_bound k 2).
    bdestruct (k mod 2 =? 0).
    + replace (k mod 2) with 0 by lia.
      rewrite swap_perm_left; lia.
    + replace (k mod 2) with 1 by lia.
      rewrite swap_perm_right; lia.
  - unfold n_m_cup_cap.
    rewrite tensor_perms_inv by auto_perm.
    now rewrite idn_inv, swap_2_perm_inv.
Qed.

(* Lemma n_m_cup_cap_bipermutation' ncup ncap : 
  bipermutation (ncap + ncap + (ncup + ncup))
  (n_m_cup_cap ncup ncap).
Proof.
  rewrite Nat.add_comm.
  apply n_m_cup_cap_bipermutation.
Qed. *)

Hint Resolve n_m_cup_cap_bipermutation
  (* n_m_cup_cap_bipermutation' *) : biperm_db.

#[export] Hint Extern 5 (bipermutation ?nnmm (n_m_cup_cap ?n ?m)) => 
  apply (bipermutation_change_dims nnmm (n + n + (m + m))
    (n_m_cup_cap n m) ltac:(lia) (n_m_cup_cap_bipermutation n m)) : biperm_db.

Lemma n_m_cup_cap_bounded n m : 
  perm_bounded (n + n + (m + m)) (n_m_cup_cap n m).
Proof.
  auto_biperm.
Qed.

Lemma n_m_cup_cap_lt_double_iff m n a k : 
  a <= m + n ->
  n_m_cup_cap m n k < a + a <-> k < a + a.
Proof.
  intros Ha.
  rewrite n_m_cup_cap_defn_alt_eq.
  split; bdestructΩ'.
  - destruct k; [easy|].
    simpl.
    apply succ_even_lt_even; [|apply even_add_same].
    now rewrite even_succ_false in Heqb.
  - apply succ_even_lt_even; auto using even_add_same.
Qed.

Lemma n_m_cup_cap_even_plus n m a k : 
  Nat.even a = true -> a + k < n + n + m + m ->
  n_m_cup_cap n m (a + k) = a + n_m_cup_cap n m k.
Proof.
  intros Ha Hak.
  rewrite n_m_cup_cap_defn_alt_eq.
  do 2 simplify_bools_lia_one_kernel.
  rewrite Nat.even_add, Ha, eqb_true_l.
  bdestructΩ'; destruct k; [easy|lia].
Qed.

Lemma n_m_cup_cap_double_plus n m a k : 
  a + a + k < n + n + m + m ->
  n_m_cup_cap n m (a + a + k) = a + a + n_m_cup_cap n m k.
Proof.
  apply n_m_cup_cap_even_plus, even_add_same.
Qed.

Lemma n_m_cup_cap_sub_double n m a k : 
  a + a <= k -> k < n + n + m + m ->
  n_m_cup_cap n m (k - (a + a)) = n_m_cup_cap n m k - (a + a).
Proof.
  intros Hak Hk.
  rewrite <- (add_sub' k (a + a)) at 2.
  rewrite <- Nat.add_sub_assoc by lia.
  rewrite n_m_cup_cap_double_plus by lia.
  now rewrite add_sub'.
Qed.


Lemma n_m_cup_cap_ge_double_iff m n a k :
  a <= m + n -> 
  a + a <= n_m_cup_cap m n k <-> a + a <= k.
Proof.
  pose proof (n_m_cup_cap_lt_double_iff m n a k).
  lia.
Qed.

Lemma n_m_cup_cap_ltb_double m n a k :
  a <= m + n -> 
  n_m_cup_cap m n k <? a + a = (k <? a + a).
Proof.
  intros Ha.
  pose proof (n_m_cup_cap_lt_double_iff m n a k Ha).
  bdestructΩ'.
Qed.

Lemma n_m_cup_cap_double_leb m n a k :
  a <= m + n -> 
  a + a <=? n_m_cup_cap m n k = (a + a <=? k).
Proof.
  intros Ha.
  pose proof (n_m_cup_cap_ge_double_iff m n a k Ha).
  bdestructΩ'.
Qed.

Lemma n_m_cup_cap_twice_plus n m a k :
  a * 2 + k < n + n + m + m ->
  n_m_cup_cap n m (a*2 + k) = 
  a*2 + n_m_cup_cap n m k.
Proof.
  replace (a*2) with (a+a) by lia.
  apply n_m_cup_cap_double_plus.
Qed.

Lemma n_m_cup_cap_geb_double m n a k : a <= m + n -> 
  (a + a <=? n_m_cup_cap m n k) = (a + a <=? k).
Proof.
  intros Ha.
  apply eq_iff_eq_true; 
  rewrite !Nat.leb_le.
  now apply n_m_cup_cap_ge_double_iff.
Qed.

(* Lemma n_m_cup_cap_double_sub n m a k (Hk : k < a + a) (Ha : a <= m + n) : 
  n_m_cup_cap m n (a + a - S k) = a + a - n_m_cup_cap m n (k).
Proof.
  rewrite (Nat.div_mod_eq k 2).
  enough (n_m_cup_cap m n (k) + n_m_cup_cap m n (a + a - S k) = a + a) by lia.
  rewrite 2!n_m_cup_cap_eqb.
  do 2 simplify_bools_lia_one_kernel.
  symmetry.

  replace (a + a) with (S k + (a + a - S k)) at 1 by lia.
  Search ((_ - _ ) mod _). *)

Lemma n_m_cup_cap_eqb' n m :
  n_m_cup_cap n m = 
  (fun k => 
  if n + n + (m + m) <=? k then k else
  k / 2 * 2 + (1 - (k mod 2))).
Proof.
  change (n_m_cup_cap n m = make_WF_Perm (n+n+(m+m))
  (fun k => k / 2 * 2 + (1 - (k mod 2)))).
  eq_by_WF_perm_eq (n+n+(m+m)).
  rewrite n_m_cup_cap_defn, make_WF_Perm_perm_eq.
  intros k Hk.
  f_equal.
  pose proof (Nat.mod_upper_bound k 2).
  unfold swap_perm.
  bdestructΩ'.
Qed.

Lemma n_m_cup_cap_eqb n m k :
  n_m_cup_cap n m k = 
  if n + n + (m + m) <=? k then k else
  k / 2 * 2 + (1 - (k mod 2)).
Proof.
  now rewrite n_m_cup_cap_eqb'.
Qed.





Lemma n_m_cup_cap_stack_biperms_decomp' ncup ncap :
  n_m_cup_cap ncup ncap = 
  stack_perms (ncup + ncup) (ncap + ncap) 
    (n_m_cup_cap 0 ncup) (n_m_cup_cap 0 ncap).
Proof.
  unfold n_m_cup_cap.
  rewrite !double_mult.
  rewrite !(Nat.mul_comm 2).
  apply tensor_perms_idn_l_split.
Qed.

Lemma n_m_cup_cap_stack_biperms_decomp ncup ncap :
  n_m_cup_cap ncup ncap = 
  stack_biperms (ncap + ncap) 0 0 (ncup + ncup) 
    (n_m_cup_cap 0 ncap) (n_m_cup_cap ncup 0).
Proof.
  rewrite n_m_cup_cap_comm, n_m_cup_cap_stack_biperms_decomp'.
  rewrite stack_biperms_0_in, ?Nat.add_0_r, ?Nat.add_0_l.
  now rewrite (n_m_cup_cap_comm _ 0).
Qed.

Lemma n_m_cup_cap_stack_biperms_decomp_alt ncup ncap :
  n_m_cup_cap ncup ncap = 
  stack_biperms (ncup + ncup) 0 0 (ncap + ncap) 
    (n_m_cup_cap 0 ncup) (n_m_cup_cap ncap 0).
Proof.
  rewrite n_m_cup_cap_comm.
  apply n_m_cup_cap_stack_biperms_decomp.
Qed.

Lemma n_m_cup_cap_plus_plus_decomp n0 n1 m0 m1 :
  n_m_cup_cap (n0 + n1) (m0 + m1) = 
  stack_biperms (n0 + n0) (m0 + m0) (n1 + n1) (m1 + m1)
  (n_m_cup_cap n0 m0) (n_m_cup_cap n1 m1).
Proof.
  eq_by_WF_perm_eq (n0 + n0 + (n1 + n1) + ((m0 + m0) + (m1 + m1))).
  1: {
    rewrite <- 2!double_add.
    auto_perm.
  }
  rewrite stack_biperms_defn_alt by auto_biperm.
  intros k Hk.
  rewrite !n_m_cup_cap_ltb_double by lia.
  bdestructΩ'.
  - rewrite 2!n_m_cup_cap_eqb; bdestructΩ'.
  - replace k with (n0 + n0 + (k - (n0 + n0))) at 1 by lia.
    rewrite n_m_cup_cap_double_plus by lia.
    rewrite 2!n_m_cup_cap_eqb; bdestructΩ'.
  - replace k with (n1 + n1 + (k - (n1 + n1))) at 1 by lia.
    rewrite n_m_cup_cap_double_plus by lia.
    rewrite 2!n_m_cup_cap_eqb; bdestructΩ'.
  - replace k with ((n0+m0)+(n0+m0) + (k - (n0 + n0 + (m0 + m0)))) 
      at 1 by lia.
    rewrite n_m_cup_cap_double_plus by lia.
    rewrite 2!n_m_cup_cap_eqb; bdestructΩ'.
Qed.

Lemma flip_biperm_n_m_cup_cap n m : 
  flip_biperm (n + n) (m + m) (n_m_cup_cap n m) = n_m_cup_cap m n.
Proof.
  eq_by_WF_perm_eq ((m + m) + (n + n));
  [apply compose_perm_biperm_WF..|].
  rewrite flip_biperm_defn.
  rewrite n_m_cup_cap_stack_biperms_decomp'.
  rewrite compose_assoc, stack_perms_big_swap_natural by 
    (apply (n_m_cup_cap_bounded 0)).
  rewrite <- compose_assoc, big_swap_perm_invol.
  now rewrite (n_m_cup_cap_stack_biperms_decomp' m n).
Qed.

(* TODO: Change to perm_eq *)
Lemma n_m_cup_cap_absorb_stacked_swap_perm_l padl padr m :
  forall k, k < (padl + 1 + padr) + (padl + 1 + padr) + (m + m) ->
  biperm_compose_perm_r (m + m) ((padl + 1 + padr) + (padl + 1 + padr))
  (n_m_cup_cap m (padl + 1 + padr))
  (stack_perms (padl+padl+2) (padr+padr)
    (stack_perms (padl + padl) 2 idn (swap_perm 0 1 2)) idn) k =
  n_m_cup_cap m (padl + 1 + padr) k.
Proof. Abort. (* TODO: Aborted for performance. Do we want this? *) (*
  intros k Hk.
  unfold biperm_compose_perm_r.
  (* TODO: Try to remove all XXX.XXX references (except, say, Nat); at 
    least for PermutationInstances. They are fragile and should be imported. *)
  pose proof (@PermutationInstances.stack_perms_bounded (padl+padl) 2 idn
    (swap_perm 0 1 2) ltac:(easy) ltac:(unfold swap_perm;intros;bdestructΩ'))
    as Hstbdd.
  pose proof (@PermutationInstances.stack_perms_bounded _ (padr+padr) _ idn
    Hstbdd ltac:(easy)) as Hsbdd.
  assert (Hsperm : permutation (padl + 1 + padr + (padl + 1 + padr))
    (stack_perms (padl+padl+2) (padr+padr)
    (stack_perms (padl + padl) 2 idn (swap_perm 0 1 2)) idn)) by
    (rewrite !double_add; auto with perm_db).
  rewrite !n_m_cup_cap_ltb_double by lia.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
  rewrite n_m_cup_cap_double_plus, add_sub' 
    by (pose proof (Hsbdd (k-(m+m))); lia).
  rewrite !double_add.
  rewrite perm_inv_stack_perms; auto with perm_db.
  2: {
    change 2 with (1 + 1).
    rewrite <- 2!double_add, n_m_cup_cap_lt_double_iff, !double_add;
    specialize (Hsbdd (k - (m + m))); simpl; lia.
  }
  rewrite stack_perms_f_idn.
  rewrite stack_perms_idn_f.
  rewrite <- stack_perms_idn_f at 1.
  rewrite !(if_dist' (n_m_cup_cap m (padl + 1 + padr))).
  rewrite n_m_cup_cap_sub_double by lia.
  pose proof (fun x => n_m_cup_cap_lt_double_iff m (padl+1+padr) x k) 
    as Hltdbl.
  bdestruct (k - (m + m) <? padl + padl + 2).
  - simpl_bools.
    bdestructΩ'simp.
    + unfold stack_perms at 1.
      pose proof (Hltdbl (m + padl + 1)).
      simplify_bools_lia.
      rewrite perm_inv_stack_perms by (lia + auto with perm_db).
      pose proof (Hltdbl (m+padl)).
      rewrite stack_perms_left by lia.
      rewrite idn_inv; 
      pose proof (Hltdbl m); lia.
    + assert (Hdisj: k = (m + padl + (m + padl))
          \/ k = S (m + padl + (m + padl))) by lia; destruct Hdisj; subst.
      * unfold swap_perm at 2.
        simplify_bools_lia.
        unfold n_m_cup_cap.
        rewrite even_succ_add_same, even_add_same.
        simplify_bools_lia.
        rewrite stack_perms_left by lia.
        rewrite perm_inv_stack_perms by lia + auto with perm_db.
        rewrite stack_perms_right by lia.
        rewrite swap_perm_inv by lia.
        unfold swap_perm; bdestructΩ'.
      * unfold swap_perm at 2.
        replace (S (m + padl + (m + padl)) - (m + m) - (padl + padl))
          with 1 by lia.
        simpl.
        unfold n_m_cup_cap.
        rewrite even_succ_add_same, even_add_same.
        simplify_bools_lia.
        rewrite stack_perms_left by lia.
        rewrite perm_inv_stack_perms by lia + auto with perm_db.
        rewrite stack_perms_right by lia.
        rewrite swap_perm_inv by lia.
        unfold swap_perm; bdestructΩ'.
  - rewrite stack_perms_right by 
      (pose proof (Hltdbl (m+padl+1));
      pose proof (Hltdbl (m+padl+1+padr)); lia).
    rewrite idn_inv 
      by (pose proof (Hltdbl (m+padl+1+padr)); lia).
    rewrite Nat.sub_add by (pose proof (Hltdbl (m+padl+1)); lia).
    pose proof (Hltdbl m); lia.
Qed.*)

(* TODO: Change to perm_eq *)
Lemma n_m_cup_cap_absorb_swap_block_perm_l padl padm padr m :
  forall k, k < (padl + 1 + padm + 1 + padr) 
    + (padl + 1 + padm + 1 + padr) + (m + m) ->
  biperm_compose_perm_r (m + m) 
    ((padl + 1 + padm + 1 + padr) + (padl + 1 + padm + 1 + padr))
  (n_m_cup_cap m (padl + 1 + padm + 1 + padr))
  (swap_block_perm (padl + padl) (padm + padm) 2) k =
  n_m_cup_cap m (padl + 1 + padm + 1 + padr) k.
Proof. Abort. (* TODO: Aborted for performance. Do we want this? *) (*
  intros k Hk.
  unfold biperm_compose_perm_r.
  rewrite !double_add.
  rewrite swap_block_perm_inv 
    by (pose proof (n_m_cup_cap_bounded m (padl+1+padm+1+padr) k); lia).
  simplify_bools_lia_one_kernel.
  rewrite !n_m_cup_cap_ltb_double by lia.
  simplify_bools_lia_one_kernel.
  bdestructΩ'.
  rewrite swap_block_perm_sub by easy.
  pose proof (swap_block_perm_bounded (m+m+(padl+padl)) (padm+padm) (padr+padr) 
    2 k ltac:(lia)).
  pose proof (fun k x => n_m_cup_cap_lt_double_iff m (padl+1+padm+1+padr) x k) 
    as Hltdbl.
  rewrite swap_block_perm_inv
    by (pose proof (Hltdbl (m + m + (swap_block_perm 
      (m + m + (padl + padl)) (padm + padm) 2 k - (m + m))) 
      (m + padl+1+padm+1+padr));
      lia).
  rewrite n_m_cup_cap_double_plus, n_m_cup_cap_sub_double by 
    lia + (unfold swap_block_perm; bdestructΩ').
  rewrite add_sub'.
  rewrite swap_block_perm_sub
    by (rewrite n_m_cup_cap_ge_double_iff by lia; 
      unfold swap_block_perm; bdestructΩ').
  unfold swap_block_perm at 1.
  change 2 with (1 + 1).
  rewrite <- !double_add.
  rewrite !n_m_cup_cap_ltb_double by lia.
  unfold swap_block_perm.
  bdestructΩ';
  match goal with 
  |- context [n_m_cup_cap _ _ ?K ] =>
      pose proof (Hltdbl K m);
      try rewrite Nat.add_sub_assoc, add_sub' by lia
  end;
  try easy.
  - rewrite (Nat.add_comm k), <- double_add, n_m_cup_cap_double_plus;
    pose proof (Hltdbl k m); lia.
  - rewrite <- double_add, n_m_cup_cap_sub_double;
    pose proof (Hltdbl k (1+padm)); lia.
Qed.*)

(* Used in the following, currently unused, lemma
Lemma swap_perm_invol' a b n k : a < n -> b < n -> 
  swap_perm a b n (swap_perm a b n k) = k.
Proof.
  intros Ha Hb.
  pose proof (swap_perm_invol a b n Ha Hb) as H.
  apply (f_equal_inv k) in H.
  apply H.
Qed.
*)
Lemma n_m_cup_cap_absorb_tensor_2_idn_swap_perm_l n m 
  a b (Ha : a < n) (Hb : b < n) :
  perm_eq (n + n + m + m)
  (biperm_compose_perm_r (m + m) 
    (n + n)
  (n_m_cup_cap m n)
  (tensor_perms n 2 (swap_perm a b n) idn))
  (n_m_cup_cap m n).
Proof. Abort. (* TODO: Aborted for performance. Do we need this? *) (*
  intros k HK.
  unfold biperm_compose_perm_r.
  simplify_bools_lia_one_kernel.
  replace (n + n) with (n * 2) in * by lia.
  rewrite 2!n_m_cup_cap_ltb_double by lia.
  simplify_bools_lia_one_kernel.
  bdestruct (k <? m + m); [easy|].
  pose proof (tensor_perms_bounded n 2 (swap_perm a b n) idn 
    ltac:(cleanup_perm) ltac:(cleanup_perm) (k - (m + m)) ltac:(lia)).
  rewrite n_m_cup_cap_double_plus by lia.
  rewrite add_sub'.
  rewrite tensor_perms_inv; auto with perm_db;
  [|replace (n*2) with (n + n);
  [apply n_m_cup_cap_lt_double_iff|]; lia].
  unfold tensor_perms at 2.
  simplify_bools_lia_one_kernel.
  pose proof (swap_perm_bounded a b n Ha Hb ((k - (m + m)) / 2)
    ltac:(apply Nat.Div0.div_lt_upper_bound; lia)).
  assert ((k - (m + m)) mod 2 < 2) by show_moddy_lt.
  rewrite n_m_cup_cap_twice_plus by 
    (apply (Nat.lt_le_trans _ ((n - 1)*2 + 2)); [nia | show_pow2_le]).
  rewrite n_m_cup_cap_eqb.
  simplify_bools_lia_one_kernel.
  rewrite mod_div, Nat.mul_0_l, Nat.add_0_l.
  rewrite Nat.mod_small by easy.
  unfold tensor_perms.
  simplify_bools_lia_one_kernel.
  rewrite Nat.div_add_l, (Nat.div_small (1 - _)), Nat.add_0_r by lia.
  rewrite mod_add_l, Nat.mod_small by lia.
  rewrite swap_perm_inv, swap_perm_invol', idn_inv by lia. 
  symmetry.
  replace k with (m + m + (k - (m + m))) at 1 by lia.
  rewrite n_m_cup_cap_double_plus by lia.
  f_equal.
  rewrite n_m_cup_cap_eqb.
  bdestructΩ'.
Qed. *)

Local Arguments Nat.modulo : simpl never.
Local Arguments Nat.div : simpl never.
Local Arguments perm_inv : simpl never.
Local Arguments Nat.sub : simpl nomatch.


Lemma n_m_cup_cap_absorb_tensor_2_idn_perm_l n m f 
  (Hf : permutation n f) :
  perm_eq (n + n + (m + m))
  (biperm_compose_perm_l (n + n) (m + m) 
  (n_m_cup_cap n m)
  (tensor_perms n 2 f idn))
  (n_m_cup_cap n m).
Proof.
  (* rewrite Nat.add_assoc. *)
  rewrite biperm_compose_perm_l_defn.
  rewrite perm_inv_stack_perms, idn_inv by auto_perm.
  rewrite n_m_cup_cap_stack_biperms_decomp'.
  rewrite stack_perms_compose by (exact (n_m_cup_cap_bounded 0 _)).
  rewrite stack_perms_compose by auto_perm.
  erewrite stack_perms_perm_eq_to_eq_proper; [reflexivity| | reflexivity].
  replace (n + n) with (n * 2) by lia.
  rewrite tensor_perms_inv by auto_perm.
  unfold n_m_cup_cap.
  cbn.
  rewrite 2!tensor_perms_compose by auto_perm.
  rewrite idn_inv, perm_inv_rinv_of_permutation by auto.
  easy.
Qed.

Lemma n_m_cup_cap_absorb_tensor_2_idn_perm_l_eq n m f
  (Hf : permutation n f) : 
  biperm_compose_perm_l (n + n) (m + m)
    (n_m_cup_cap n m) (tensor_perms n 2 f idn) 
  = n_m_cup_cap n m.
Proof.
  eq_by_WF_perm_eq ((n + n) + (m + m)).
  now apply n_m_cup_cap_absorb_tensor_2_idn_perm_l.
Qed.

Lemma n_m_cup_cap_absorb_reflect_perm_l n m :
  biperm_compose_perm_l (n + n) (m + m)
    (n_m_cup_cap n m) (reflect_perm (n + n))
  = n_m_cup_cap n m.
Proof.
  eq_by_WF_perm_eq ((n + n) + (m + m)).
  rewrite biperm_compose_perm_l_defn.
  rewrite perm_inv_stack_perms, reflect_perm_inv, idn_inv by auto_perm.
  rewrite n_m_cup_cap_stack_biperms_decomp'.
  rewrite stack_perms_compose by (exact (n_m_cup_cap_bounded 0 _)).
  rewrite stack_perms_compose by auto_perm.
  erewrite stack_perms_perm_eq_to_eq_proper; [reflexivity | | reflexivity].
  rewrite n_m_cup_cap_defn_alt.
  replace (n + n) with (n * 2) by lia.
  rewrite reflect_perm_defn at 2.
  intros k Hk.
  unfold compose.
  rewrite Nat.even_sub, Nat.even_mul, (Nat.even_succ k) by lia.
  rewrite orb_true_r, eqb_true_l.
  rewrite <- Nat.negb_even.
  destruct (Nat.even k) eqn:e.
  - cbn [negb].
    unfold reflect_perm.
    simplify_bools_lia_one_kernel.
    assert (Hev: Nat.even (n * 2) = true) by 
      (now rewrite Nat.mul_comm, Nat.even_mul).
    pose proof (succ_even_lt_even k (n * 2) e Hev Hk).
    lia.
  - cbn [negb].
    unfold reflect_perm.
    assert (k <> 0) by (intros ->; cbn in *; easy).
    simplify_bools_lia_one_kernel.
    lia.
Qed.

Lemma n_m_cup_cap_absorb_perm_swap_even_S_l n m a 
  (Ha : Nat.even a = true) :
  biperm_compose_perm_l (n + n) (m + m)
    (n_m_cup_cap n m) (swap_perm a (S a) (n + n))
  = n_m_cup_cap n m.
Proof.
  eq_by_WF_perm_eq ((n + n) + (m + m)).
  bdestruct (a <? n + n).
  2: {
    rewrite swap_perm_big_eq by lia.
    apply biperm_compose_perm_l_idn, n_m_cup_cap_bounded.
  }
  assert (Hev : Nat.even (n + n) = true) by (apply even_add_same).
  assert (S a < n + n) by (now apply succ_even_lt_even).
  rewrite biperm_compose_perm_l_defn.
  rewrite perm_inv_stack_perms, swap_perm_inv, idn_inv by auto_perm.
  rewrite n_m_cup_cap_stack_biperms_decomp'.
  rewrite stack_perms_compose by (exact (n_m_cup_cap_bounded 0 _)).
  rewrite stack_perms_compose by auto_perm.
  erewrite stack_perms_perm_eq_to_eq_proper; [reflexivity | | reflexivity].
  change (n + n) with ((0 + 0) + (n + n)).
  rewrite compose_assoc.
  pose proof (n_m_cup_cap_bipermutation 0 n).
  rewrite swap_perm_defn at 1 by lia.
  rewrite n_m_cup_cap_defn_alt, swap_perm_defn by lia.
  intros k Hk.
  unfold compose.
  assert (Nat.even (S a) = false) by (now apply even_succ_false).
  pose proof (Nat.even_succ_succ k).
  bdestructΩ'.
  - congruence.
  - replace k with (S (S a)) in * by lia.
    rewrite !Nat.even_succ_succ in *.
    congruence.
Qed.

Lemma n_m_cup_cap_absorb_perm_swap_0_1_l n m :
  biperm_compose_perm_l (n + n) (m + m)
    (n_m_cup_cap n m) (swap_perm 0 1 (n + n))
  = n_m_cup_cap n m.
Proof.
  now apply n_m_cup_cap_absorb_perm_swap_even_S_l.
Qed.




(* TODO: Move these to earlier in the file, maybe? Maybe better to have them
  concentrated, though, since we can't really use them in this file anyways *)

(* Create HintDb biperm_db_alt.

#[export] Hint Resolve idn_biperm_bipermutation flip_biperm_bipermutation
  n_m_cup_cap_bipermutation (* remove_swap_bipermutation *)
  stack_biperms_bipermutation
  stack_biperms_bipermutation_alt (* compose_swap_biperm_gen_bipermutation *)
  (* biperm_of_zxbiperm_folio_bipermutation *)
  bipermutation_is_bounded bipermutation_involutive
  (* compose_swap_biperm_bipermutation *) (* compose_cap_biperm_l_bipermutation *)
  (* compose_cup_biperm_l_bipermutation *) 
  biperm_compose_perm_l_biperm biperm_compose_perm_r_biperm
  : biperm_db.

#[export] Hint Resolve idn_biperm_bipermutation flip_biperm_bipermutation
  n_m_cup_cap_bipermutation (* remove_swap_bipermutation *)
  stack_biperms_bipermutation
  stack_biperms_bipermutation_alt (* compose_swap_biperm_gen_bipermutation *)
  (* biperm_of_zxbiperm_folio_bipermutation *)
  bipermutation_is_bounded bipermutation_involutive
  (* compose_swap_biperm_bipermutation *) (* compose_cap_biperm_l_bipermutation *)
  (* compose_cup_biperm_l_bipermutation *) 
  biperm_compose_perm_l_biperm biperm_compose_perm_r_biperm
  : biperm_db_alt. *)

(* TODO: Test these replacements *)
(* Hint Extern 0 (permutation _ _) => auto with perm_db : biperm_db biperm_db_alt. *)

Hint Extern 100 (permutation _ _) => solve [auto with perm_db] 
  : biperm_db (* biperm_db_alt *).


(* Hint Extern 0 (_ < _) => auto with perm_bounded_db : biperm_db biperm_db_alt. *)

Hint Extern 100 (_ < _) => 
  solve [auto with perm_bounded_db] : biperm_db (* biperm_db_alt *).



(* Hint Extern 4 (bipermutation (?n + ?m) _) => 
  (* idtac n m; *) rewrite (Nat.add_comm n m); auto with biperm_db_alt : biperm_db. *)
(*
Hint Extern 4 (bipermutation (?n + ?m) _) => 
  rewrite (Nat.add_comm n m) : biperm_db.
*)

(* Hint Extern 4 (bipermutation (?n) _) => 
  let k := fresh in 
  evar (k : nat); 
  replace n with k;
  unfold k;
  auto with biperm_db_alt;
  lia : biperm_db. *)
(*
Hint Extern 4 (bipermutation (?n) _) =>
  is_ground n;
  let k := fresh in 
  evar (k : nat); 
  replace n with k; 
  unfold k;
  [ solve [auto with biperm_db_alt] |];
  [| (lia || cbn; lia)] : biperm_db.
*)

(* Hint Extern 4 (permutation (?n) _) => 
  let k := fresh in 
  evar (k : nat); 
  replace n with k;
  unfold k;
  auto with biperm_db_alt;
  lia : biperm_db. *)
(*
Hint Extern 4 (permutation (?n) _) => 
  is_ground n;
  let k := fresh in 
  evar (k : nat); 
  replace n with k;
  unfold k;
  [ solve [auto with biperm_db_alt] |];
  [|(lia || cbn; lia)] : biperm_db.
*)