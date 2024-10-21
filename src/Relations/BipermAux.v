Require Import StackRules ComposeRules StackComposeRules.
Require Import CoreData CoreAutomation.
Require Import ZXpermAutomation.
Import CastRules.
Import Setoid.
From QuantumLib Require Import Bits.
Require Export QuantumLib.Permutations.
Import QuantumLib.VectorStates Modulus Kronecker.

Open Scope prg.
Open Scope nat_scope.

(* FIXME: Move to Qlib.PermutationAutomation *)
Ltac ereflexivity :=
  lazymatch goal with 
  | |- ?R ?A ?B => 
    let H := fresh in 
    enough (H : A = B) by 
    (first [rewrite H; reflexivity 
      | rewrite H at 1; reflexivity
      | fail 1 "Could not use" A "=" B "to show goal by rewriting" ])
  | _ => fail "Could not recognize goal as a relation"
  end.

(* FIXME: Move to Qlib *)
Tactic Notation "eq_by_WF_perm_eq" uconstr(n) :=
  eapply (eq_of_WF_perm_eq n); 
  [auto_perm..|].

(* FIXME: Move to Qlib.PermutationAutomation - or to Prelim, so it
  can be used in PermutationsBase / elsewhere *)
Lemma predicate_symmetry : forall A (R : relation A),   (* params *)
  forall (P : forall (a b : A), Prop),                  (* predicates *)
  forall (HP : forall a b, R a b -> P a b)              
    (HPsymm : forall a b, P a b -> P b a),              (* branches *)
  forall a b, (R a b \/ R b a) ->                       (* arguments *)
  P a b.                                                (* conclusion *)
Proof.
  intuition auto.
Qed.

Tactic Notation "by_symmetry" constr(H) "by" tactic3(tac) :=
  match type of H with 
  | ?R ?k ?l \/ ?R ?l ?k => 
    match type of R with 
    | forall (a b : ?T), _ =>
      pattern k, l;
      let G := fresh in 
      match goal with 
      |- ?P k l =>
        set (G := P);
        move H at top;
        gen l; intros l H;
        move H at top;
        gen k; intros k H;
        pattern k, l;
        refine (predicate_symmetry T R _ _ _ k l H);
        [clear k l H; intros k l H;
        intros;
        unfold G; clear G | unfold G; clear G; tac]
      end
    end
  end.

Tactic Notation "by_symmetry" constr(H) :=
  by_symmetry H by idtac.





Inductive reflectb (P Q : Prop) : bool -> Set :=
  | ReflectbT : P -> reflectb P Q true 
  | ReflectbF : Q -> reflectb P Q false.

(* NB: This is a CMorphisms statement 
  Proper (impl ==> impl ==> eq ==> arrow) reflectb *)
Lemma reflectb_of_arrow P Q P' Q' b : 
  (P -> P') -> (Q -> Q') -> reflectb P Q b -> 
  reflectb P' Q' b.
Proof.
  intros HP HQ [];
  constructor; auto.
Qed.

Lemma reflectb_of_arrow_r P Q Q' b : (Q -> Q') -> 
  reflectb P Q b -> reflectb P Q' b.
Proof.
  intros HQ.
  now apply reflectb_of_arrow.
Qed.

Lemma reflectb_of_arrow_l P P' Q b : (P -> P') -> 
  reflectb P Q b -> reflectb P' Q b.
Proof.
  intros HP.
  now apply reflectb_of_arrow.
Qed.

Lemma if_reflectb P Q b : 
  (b = true -> P) -> (b = false -> Q) -> reflectb P Q b.
Proof.
  destruct b; auto using ReflectbT, ReflectbF.
Qed.

Lemma reflectb_if P Q b : 
  reflectb P Q b -> (b = true -> P) /\ (b = false -> Q).
Proof.
  now intros [].
Qed.

Lemma reflect_reflectb P b : 
  reflect P b -> reflectb P (~ P) b.
Proof.
  intros []; now constructor.
Qed.

Lemma reflect_reflectb_impl P P' notP' b : 
  reflect P b -> 
  (P -> P') -> (~ P -> notP') -> 
  reflectb P' notP' b.
Proof.
  intros H; apply reflect_reflectb in H.
  eauto using reflectb_of_arrow.
Qed.

Lemma reflectb_by_reflect {P P' notP' b} :
  (reflect P b) -> 
  (P -> P') -> (~ P -> notP') -> 
  reflectb P' notP' b.
Proof. 
  apply reflect_reflectb_impl. 
Qed.

Lemma ble_reflectb n m : reflectb (n <= m) (m < n) (n <=? m).
Proof.
  apply (reflectb_by_reflect (ble_reflect n m)); lia.
Qed.

Lemma blt_reflectb n m : reflectb (n < m) (m <= n) (n <? m).
Proof.
  apply (reflectb_by_reflect (blt_reflect n m)); lia.
Qed.

Lemma beq_reflectb n m : reflectb (n = m) (n <> m) (n =? m).
Proof.
  apply (reflect_reflectb _ _ (beq_reflect n m)).
Qed.

Lemma orb_reflectb Pb Qb b Pc Qc c : 
  reflectb Pb Qb b -> reflectb Pc Qc c ->
  reflectb (Pb \/ Pc) (Qb /\ Qc) (b || c).
Proof.
  intros [] []; constructor; now auto.
Qed.

Lemma andb_reflectb Pb Qb b Pc Qc c : 
  reflectb Pb Qb b -> reflectb Pc Qc c ->
  reflectb (Pb /\ Pc) (Qb \/ Qc) (b && c).
Proof.
  intros [] []; constructor; now auto.
Qed.

Lemma xorb_reflectb Pb Qb b Pc Qc c : 
  reflectb Pb Qb b -> reflectb Pc Qc c ->
  reflectb ((Pb /\ Qc) \/ (Qb /\ Pc))
    ((Pb /\ Pc) \/ (Qb /\ Qc))
    (b ⊕ c).
Proof.
  intros [] []; constructor; now auto.
Qed.

Lemma implb_reflectb Pb Qb b Pc Qc c : 
  reflectb Pb Qb b -> reflectb Pc Qc c ->
  reflectb (Qb \/ (Pb /\ Pc)) (Pb /\ Qc) (implb b c).
Proof.
  intros [] []; cbn; constructor; now auto.
Qed.

Hint Resolve ble_reflectb blt_reflectb beq_reflectb
  orb_reflectb andb_reflectb xorb_reflectb implb_reflectb : bdestruct.

Ltac bdestructP b :=
  let H := fresh in
  let Pt := fresh "Pt" in
  let Pf := fresh "Pf" in
  evar ( Pt : Prop );
  evar ( Pf : Prop ); 
  assert (H : reflectb Pt Pf b) by 
  (subst Pt Pf; eauto with bdestruct); 
  subst Pt Pf;
  destruct H as [H| H].

Ltac replace_bool_liaP b0 b1 :=
  replace b0 with b1 by
  (bdestructP b0;
    first [lia | bdestructP b1; lia]).

Lemma reflectb_is_true {P Q b} : 
  reflectb P Q b ->
  ~ Q -> b = true.
Proof.
  now intros [].
Qed.

Lemma reflectb_is_false {P Q b} : 
  reflectb P Q b ->
  ~ P -> b = false.
Proof.
  now intros [].
Qed.

Lemma reflectb_if_ind {P Q b} : 
  reflectb P Q b -> forall (L R : Prop),
  (P -> L) -> (Q -> R) -> 
  if b then L else R.
Proof.
  intros []; auto.
Qed.

Lemma reflectb_if_eq {P Q b} : 
  reflectb P Q b -> forall (A : Type) (l r rhs : A),
  (P -> l = rhs) -> (Q -> r = rhs) -> 
  (if b then l else r) = rhs.
Proof.
  intros []; auto.
Qed.

Lemma reflectb_eq_reflectb {Pb Qb b Pc Qc c} :
  reflectb Pb Qb b -> 
  reflectb Pc Qc c ->
  ~ (Pb /\ Qc) -> ~ (Qb /\ Pc) -> 
  b = c.
Proof.
  intros [] []; tauto.
Qed.

Ltac blia :=
  let H := fresh in 
  lazymatch goal with 
  | |- ?b = true =>
    eassert (H : reflectb _ _ b) by (once eauto with bdestruct);
    apply (reflectb_is_true H);
    lia
  | |- ?b = false =>
    eassert (H : reflectb _ _ b) by (once eauto with bdestruct);
    apply (reflectb_is_false H);
    lia
  | |- true = ?b =>
    eassert (H : reflectb _ _ b) by (once eauto with bdestruct);
    symmetry;
    apply (reflectb_is_true H);
    lia
  | |- false = ?b =>
    eassert (H : reflectb _ _ b) by (once eauto with bdestruct);
    symmetry;
    apply (reflectb_is_false H);
    lia
  end.

Ltac blia_eq :=
  let H := fresh in 
  let G := fresh in 
  match goal with
  | |- ?b = ?c => 
    eassert (H : reflectb _ _ b) by (once eauto with bdestruct);
    eassert (G : reflectb _ _ c) by (once eauto with bdestruct);
    apply (reflectb_eq_reflectb H G);
    lia
  end.


Ltac blia_rec :=
  let end_tac := solve [blia | reflexivity | lia] in 
  let H := fresh in
  lazymatch goal with 
  | |- match ?b with | true => ?P | false => ?Q end =>
    eassert (H : reflectb _ _ b) by (once eauto with bdestruct);
    apply (reflectb_if_ind H P Q);
    intros ?; solve [end_tac | blia_rec]
  | |- @eq ?A (match ?b with | true => ?l | false => ?r end) ?rhs =>
    eassert (H : reflectb _ _ b) by (once eauto with bdestruct);
    apply (reflectb_if_eq H A l r rhs);
    intros ?; solve [end_tac | blia_rec]
  | |- @eq ?A ?rhs (match ?b with | true => ?l | false => ?r end) =>
    eassert (H : reflectb _ _ b) by (once eauto with bdestruct);
    symmetry;
    apply (reflectb_if_eq H A l r rhs);
    intros ?; solve [end_tac | blia_rec]
  | _ => end_tac
  end.



Ltac if_true_lia :=
  lazymatch goal with 
  |- context[ match ?b with | true => _ | false => _ end ] =>
    replace b with true by blia
  end.

Ltac if_false_lia :=
  lazymatch goal with 
  |- context[ match ?b with | true => _ | false => _ end ] =>
    replace b with false by blia
  end.








(* FIXME: Move *)
Definition true_rel {A} : relation A := 
	fun _ _ => True.

Add Parametric Relation A : A true_rel 
	reflexivity proved by ltac:(easy)
	symmetry proved by ltac:(easy)
	transitivity proved by ltac:(easy) 
	as true_rel_equivalence.

#[export] Hint Unfold true_rel : typeclass_instances.



(* Section Preliminary. *)

(* FIXME: TODO: Move, probably to Modulus *)
Lemma and_True_l P : True /\ P <-> P.
Proof. tauto. Qed.

Lemma and_True_r P : P /\ True <-> P.
Proof. tauto. Qed.

Lemma and_iff_distr_l P Q R : 
  (P -> (Q <-> R)) <-> (P /\ Q <-> P /\ R).
Proof. tauto. Qed.

Lemma and_iff_distr_r P Q R : 
  (P -> (Q <-> R)) <-> (Q /\ P <-> R /\ P).
Proof. rewrite and_iff_distr_l. now rewrite 2!(and_comm P). Qed.


(* FIXME: Move, probably to Qlib *)
Lemma forall_lt_iff n (P Q : nat -> Prop) 
  (HPQ : forall k, k < n -> P k <-> Q k) :
  (forall k, k < n -> P k) <-> (forall k, k < n -> Q k).
Proof.
  apply forall_iff; intros k.
  apply impl_iff; intros Hk.
  auto.
Qed.

Lemma forall_lt_iff_permute n f (Hf : permutation n f) 
  (P : nat -> Prop) : 
  (forall k, k < n -> P k) <-> (forall k, k < n -> P (f k)).
Proof.
  split; intros HP.
  - intros k Hk.
    apply HP.
    auto with perm_bounded_db.
  - intros k Hk.
    generalize (HP (perm_inv n f k) (perm_inv_bounded n f k Hk)).
    now rewrite perm_inv_is_rinv_of_permutation by easy.
Qed.

Lemma forall_lt_iff_of_permute_l n f (Hf : permutation n f) 
  (P Q : nat -> Prop) (HPQ : forall k, k < n -> P (f k) <-> Q k) :
  (forall k, k < n -> P k) <-> (forall k, k < n -> Q k).
Proof.
  rewrite (forall_lt_iff_permute n f Hf).
  apply forall_iff; intros k.
  apply impl_iff; intros Hk.
  now apply HPQ.
Qed.

Lemma forall_lt_iff_of_permute_r n f (Hf : permutation n f) 
  (P Q : nat -> Prop) (HPQ : forall k, k < n -> P k <-> Q (f k)) :
  (forall k, k < n -> P k) <-> (forall k, k < n -> Q k).
Proof.
  symmetry.
  apply (forall_lt_iff_of_permute_l n f Hf).
  intros k Hk.
  now rewrite HPQ.
Qed.

(* FIXME: Move, perhaps to Qlib.PermutationsBase? *)
Lemma forall_nat_lt_add n m (P : nat -> Prop) :
  (forall k, k < n + m -> P k) <->
  (forall k, k < n -> P k) /\ (forall k, k < m -> P (n + k)).
Proof.
  split; [auto with zarith|].
  intros [Hlow Hhigh] k Hk.
  bdestruct (k <? n); [auto|].
  replace k with (n + (k - n)) by lia.
  auto with zarith.
Qed.

Lemma forall_nat_lt_1 P : (forall k , k < 1 -> P k) <-> P 0.
Proof.
  split; [now auto|].
  intros HP0 []; [auto|lia].
Qed.

Lemma forall_nat_lt_0 (P : nat -> Prop) : 
  (forall k, k < 0 -> P k) <-> True.
Proof.
  split; [easy|].
  lia.
Qed.

(* FIXME: Move *)
Lemma exists_iff {A} (P Q : A -> Prop) : 
  (forall a, P a <-> Q a) -> 
  (exists a, P a) <-> (exists a, Q a).
Proof.
  intros HPQ.
  split; 
  intros [a Ha]; 
  exists a; 
  specialize (HPQ a); 
  tauto.
Qed.

Lemma list_cons_eq_iff {A} (a b : A) (l m : list A) : 
  a :: l = b :: m <-> a = b /\ l = m.
Proof.
  split; [|now intros [-> ->]].
  intros H.
  injection H.
  easy.
Qed.

Lemma forall_lt_eq_iff_list_eq_gen {A} (f g : nat -> A) m n :
  (forall k, k < n -> f (m + k) = g (m + k)) <-> 
  map f (seq m n) = map g (seq m n).
Proof.
  revert m;
  induction n; [easy|]; intros m.
  rewrite (forall_nat_lt_add 1 n).
  rewrite forall_nat_lt_1.
  cbn.
  rewrite list_cons_eq_iff.
  rewrite Nat.add_0_r.
  apply ZifyClasses.and_morph; [reflexivity|].
  rewrite <- IHn. 
  apply forall_lt_iff.
  intros k Hk.
  now rewrite Nat.add_succ_r.
Qed.

Lemma forall_lt_eq_iff_list_eq {A} (f g : nat -> A) n :
  (forall k, k < n -> f k = g k) <-> 
  map f (seq 0 n) = map g (seq 0 n).
Proof.
  exact (forall_lt_eq_iff_list_eq_gen f g 0 n).
Qed.



(* FIXME: Move all of this *)
Lemma b2R_mult b c : (b2R b * b2R c = b2R (b && c))%R.
Proof.
  destruct b, c; cbn; lra.
Qed.

Lemma b2n_0_iff b : Nat.b2n b = 0 <-> b = false.
Proof. now destruct b. Qed.

Lemma b2n_1_iff b : Nat.b2n b = 1 <-> b = true.
Proof. now destruct b. Qed.




Section bool_lemmas.

Lemma dist_if {A B} (x : A) (f g : A -> B) (b : bool) : 
  (if b then f else g) x = if b then f x else g x.
Proof. 
  now destruct b.
Qed.

Lemma eqb_true_l b : eqb true b = b.
Proof. now destruct b. Qed.

Lemma eqb_true_r b : eqb b true = b.
Proof. now destruct b. Qed.

(* FIXME: Move to Modulus *)
Lemma bool_eqb_comm b c : eqb b c = eqb c b.
Proof. now destruct b, c. Qed.

End bool_lemmas.

Lemma diff_divs_lower_bound a b k n : 
  (a < n -> b < n -> a / k <> b / k -> k < n)%nat.
Proof.
  intros Ha Hb Hne.
  bdestructΩ (k <? n).
  exfalso; apply Hne.
  now rewrite 2!Nat.div_small by lia.
Qed.

Lemma even_eqb n : Nat.even n = (n mod 2 =? 0).
Proof.
  rewrite (Nat.div_mod_eq n 2) at 1.
  rewrite Nat.even_add, Nat.even_mul.
  cbn [Nat.even orb].
  rewrite eqb_true_l.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)).
  now destruct ((ltac:(lia) : n mod 2 = O \/ n mod 2 = 1%nat)) as
    [-> | ->].
Qed.

Lemma even_le_even_of_le_succ m n 
  (Hm : Nat.even m = true) (Hn : Nat.even n = true) : 
  (n <= S m -> n <= m)%nat.
Proof.
  intros Hnm.
  bdestructΩ (n =? S m).
  replace -> n in Hn.
  rewrite Nat.even_succ, <- Nat.negb_even in Hn.
  now rewrite Hm in Hn.
Qed.







(* FIXME: Move to Modulus *)
Lemma div_2_mul_2_exact_iff_even n : 
  n / 2 * 2 = n <-> Nat.even n = true.
Proof.
  rewrite even_eqb, Nat.eqb_eq.
  pose proof (Nat.div_mod_eq n 2).
  lia.
Qed.

(* FIXME: Move to Qlib.Modulus *)
Lemma max_ltb n m : max n m = if n <? m then m else n.
Proof.
  blia_rec.
Qed.

(* FIXME: Move to Modulus *)
Lemma sub_mul_div x y z : y * z <= x -> 
(x - y * z) / z = x / z - y.
Proof.
intros H.
bdestruct (z =? 0).
- subst.
  now rewrite !Nat.div_0_r.
- assert (y <= x / z) by (apply Nat.div_le_lower_bound; lia).
  pose proof (Nat.div_mod_eq x z) as Hxz.
  replace (x - y * z) with ((x / z - y) * z + x mod z) by nia.
  rewrite Nat.div_add_l by auto.
  rewrite mod_div.
  lia.
Qed.

(* FIXME: Move to Qlib.Modulus *)
Lemma div_add_n_r a n (Hn : n <> 0) : 
  (a + n) / n = a / n + 1.
Proof.
  pose proof (Nat.div_mod_eq (a + n) n).
  rewrite mod_add_n_r in H.
  pose proof (Nat.div_mod_eq a n).
  nia.
Qed.

Lemma div_sub_n_r a n : 
  (a - n) / n = a / n - 1.
Proof.
  bdestruct (n =? 0); [subst; reflexivity|].
  bdestruct (a <? n).
  - replace (a - n) with 0 by lia.
    now rewrite 2!Nat.div_small by lia.
  - replace (a / n) with (((a - n) + n) / n) by (f_equal; lia).
    rewrite div_add_n_r by auto.
    lia.
Qed.

Lemma div_2_add_l_1 a : (a * 2 + 1) / 2 = a.
Proof. 
  rewrite Nat.div_add_l by lia.
  apply Nat.add_0_r.
Qed.

Lemma div_2_add_l_1' a : (2 * a + 1) / 2 = a.
Proof. 
  rewrite Nat.mul_comm. 
  apply div_2_add_l_1.
Qed.

Lemma div_2_add_l a b : (a * 2 + b) / 2 = a + b / 2.
Proof. 
  now rewrite Nat.div_add_l by lia.
Qed.

Lemma div_2_add_l' a b : (2 * a + b) / 2 = a + b / 2.
Proof. 
  rewrite Nat.mul_comm. 
  apply div_2_add_l.
Qed.

Lemma mod_add_l' a b c : (b * a + c) mod b = c mod b.
Proof.
  rewrite Nat.mul_comm.
  apply mod_add_l.
Qed.

Lemma mod_sub_n_r a n (Ha : n <= a) : 
  (a - n) mod n = a mod n.
Proof.
  replace (a - n) with (a - 1 * n) by lia.
  now rewrite sub_mul_mod by lia.
Qed.

(* FIXME: Move to Qlib *)
Lemma nat_to_funbool_add_pow2_split i j n m 
  (Hi : i < 2 ^ n) (Hj : j < 2 ^ m) : 
  nat_to_funbool (n + m) (i * 2 ^ m + j) =
  (fun s => 
    if s <? n then nat_to_funbool n i s
    else nat_to_funbool m j (s - n)).
Proof.
  apply functional_extensionality; intros s.
  rewrite !nat_to_funbool_eq.
  rewrite testbit_add_pow2_split by easy.
  bdestructΩ'; try (f_equal; lia).
  - replace n with 0 in * by lia.
    replace m with 0 in * by lia.
    destruct i, j; [|cbn in Hi, Hj; lia..].
    easy.
  - replace m with 0 in * by lia.
    destruct j; [|cbn in Hj; lia].
    easy.
Qed.

(* FIXME: Move to Qlib *)
Lemma nat_to_funbool_inj_upto_small i j n (Hi : i < 2^n) (Hj : j < 2^n) :
  (forall s, s < n -> nat_to_funbool n i s = nat_to_funbool n j s) <->
  i = j.
Proof.
  split; [|now intros ->].
  intros Hij.
  rewrite <- (bits_inj_upto_small i j n) by assumption.
  intros s Hs.
  generalize (Hij (n - S s) ltac:(lia)).
  rewrite 2!nat_to_funbool_eq.
  simplify_bools_lia_one_kernel.
  now rewrite sub_S_sub_S.
Qed.





(* FIXME: Move to Summation *)
Lemma big_sum_Nsum {G} {H : Monoid G} n ns (f : nat -> G) : 
  big_sum f (big_sum ns n) = 
  big_sum (fun k => big_sum (fun i => f (big_sum ns k + i)) (ns k)) n.
Proof.
  induction n; [reflexivity|].
  cbn.
  rewrite big_sum_sum.
  f_equal. 
  apply IHn.
Qed.

Lemma Nsum_1 n : big_sum (fun _ => 1) n = n.
Proof.
  rewrite big_sum_constant, times_n_nat; lia.
Qed.

Lemma Nsum_constant d n : 
  big_sum (fun _ => d) n = n * d.
Proof.
  rewrite big_sum_constant, times_n_nat; lia.
Qed.

(* FIXME: generalize to Comm_Group as well, and move to Qlib *)
Lemma Nsum_plus n f g : 
  big_sum (fun k => f k + g k) n = big_sum f n + big_sum g n.
Proof.
  induction n; cbn; lia.
Qed.

(* FIXME: Move *)
Lemma Nsum_le_r n m f : n <= m -> 
  big_sum f n <= big_sum f m.
Proof.
  intros Hle.
  induction Hle; cbn; lia.
Qed.

(* FIXME: Move to Qlib.Summation *)
Lemma big_sum_if_lt {G} {HG : Monoid G} n m (f g : nat -> G) : 
  big_sum (fun k => if k <? n then f k else g (k - n)) (n + m) = 
  (big_sum f n + big_sum g m)%G.
Proof.
  rewrite big_sum_sum.
  f_equal; apply big_sum_eq_bounded; intros k Hk.
  - bdestructΩ'.
  - rewrite add_sub'.
    bdestructΩ'.
Qed.

Lemma Nsum_if_lt n m f g : 
  big_sum (fun k => if k <? n then f k else g (k - n)) (n + m) = 
  big_sum f n + big_sum g m.
Proof. exact (big_sum_if_lt n m f g). Qed.


(* FIXME: Move *)
Lemma Nsum_0_iff n f : 
  big_sum f n = 0 <-> (forall k, k < n -> f k = 0).
Proof.
  induction n; [easy|].
  rewrite forall_nat_lt_S.
  cbn.
  rewrite <- IHn.
  lia.
Qed.

Lemma Nsum_constant_0' n : 
  0 = big_sum (fun _ => 0) n.
Proof.
  rewrite Nsum_constant; lia.
Qed.

Lemma Nsum_if_1_0_unique_iff n (f : nat -> bool) : 
  big_sum (fun i => if f i then 1 else 0) n = 1 <->
  exists k, k < n /\ f k = true /\ 
    forall l, l < n -> l <> k -> f l = false.
Proof.
  split.
  - induction n; [cbn; discriminate|].
    cbn.
    destruct (f n) eqn:efn.
    + intros Heq.
      exists n.
      split; [|split]; [now auto..|].
      intros l Hl Hln.
      assert (H0 : big_sum (fun i => if f i then 1 else 0) n = 0) by lia.
      rewrite Nsum_0_iff in H0.
      specialize (H0 l ltac:(lia)).
      destruct (f l); easy.
    + rewrite Nat.add_0_r.
      intros Heq.
      specialize (IHn Heq).
      destruct IHn as (k & Hk & Hfk & Hfnotk).
      exists k.
      split; [|split]; [now auto..|].
      intros l Hl Hlk.
      bdestruct (l =? n); [now subst|].
      apply Hfnotk; lia.
  - intros (k & Hk & Hfk & Hfnotk).
    apply big_sum_unique.
    exists k.
    rewrite Hfk.
    split; [|split]; [now auto..|].
    intros l Hl Hkl.
    now rewrite Hfnotk by auto.
Qed.

Lemma Nsum_b2n_zero_iff n (f : nat -> bool) : 
  big_sum (Nat.b2n ∘ f) n = 0 <->
  (forall k, k < n -> f k = false).
Proof.
  induction n.
  - rewrite forall_nat_lt_0; cbn; lia.
  - cbn.
    rewrite Nat.eq_add_0.
    rewrite IHn.
    unfold compose.
    rewrite b2n_0_iff.
    rewrite forall_nat_lt_S.
    apply and_comm.
Qed.

Lemma Nsum_b2n_pos_witness n (f : nat -> bool) : 
  big_sum (Nat.b2n ∘ f) n <> 0 ->
  {k | k < n /\ f k = true}.
Proof.
  induction n; [easy|].
  cbn.
  unfold compose at 2.
  destruct (f n) eqn:e.
  - intros _.
    exists n; split; [lia|easy].
  - rewrite Nat.add_0_r.
    intros H.
    destruct (IHn H) as (k & Hk & Hfk).
    exists k; split; [lia|easy].
Qed.

Lemma Nsum_b2n_pos_iff n (f : nat -> bool) : 
  big_sum (Nat.b2n ∘ f) n <> 0 <->
  exists k, k < n /\ f k = true.
Proof.
  split.
  - intros H.
    destruct (Nsum_b2n_pos_witness _ _ H) as [k Hk].
    exists k; apply Hk.
  - intros (k & Hk & Hfk).
    rewrite Nsum_b2n_zero_iff.
    intros H.
    specialize (H k Hk).
    congruence.
Qed.

Lemma triangle_number_exact n : 
  n * (n - 1) / 2 * 2 = n * (n - 1).
Proof.
  pose proof (Nat.div_mod_eq (n * (n - 1)) 2).
  enough ((n * (n - 1)) mod 2 = 0) by lia.
  bdestruct (n =? 0); [now subst|].
  bdestruct (n =? 1); [now subst|].
  rewrite <- Nat.eqb_eq.
  rewrite <- even_eqb.
  rewrite Nat.even_mul, Nat.even_sub by lia.
  cbn.
  now destruct (Nat.even n).
Qed.
  

Lemma triangle_number n : 
  big_sum idn n = (n * (n - 1)) / 2.
Proof.
  induction n; [reflexivity|].
  cbn [big_sum nat_is_monoid Gplus].
  rewrite IHn.
  rewrite <- Nat.div_add by lia.
  f_equal.
  nia.
Qed.

Lemma triangle_number' n : 
  big_sum idn (S n) = (n + 1) * n / 2.
Proof.
  rewrite triangle_number.
  f_equal; lia.
Qed.

Lemma Nsum_permutation n f (Hf : permutation n f) : 
  big_sum f n = (n * (n - 1)) / 2.
Proof.
  rewrite <- (compose_idn_l f).
  rewrite <- Nsum_reorder by auto.
  apply triangle_number.
Qed.

Lemma Nsum_reflect_perm n k (Hk : k < n) : 
  big_sum (reflect_perm n) k = 
  n * k - ((k + 1) * k / 2).
Proof.
  replace ((k + 1) * k) with ((S k) * (S k - 1)) by lia.
  rewrite <- triangle_number.
  induction k; [cbn; lia|].
  cbn [big_sum Gplus nat_is_monoid].
  rewrite IHk by lia.
  cbn [big_sum Gplus nat_is_monoid].
  rewrite reflect_perm_defn by lia.
  enough (big_sum idn k + k <= n * k) by nia.
  change (big_sum idn k + k) with (big_sum idn (1 + k)).
  rewrite big_sum_sum.
  rewrite Nat.add_0_l.
  rewrite <- times_n_nat, <- big_sum_constant.
  apply Nsum_le.
  lia.
Qed.





Add Parametric Morphism n : (Nsum_offset n) 
  with signature perm_eq n ==> eq as Nsum_offset_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  apply functional_extensionality; intros k.
  unfold Nsum_offset.
  f_equal.
  bdestruct (n =? 0); [now subst|].
  pose proof (Nsum_index_bounded n g k ltac:(auto)).
  rewrite (Nsum_index_perm_eq_to_eq _ _ _ Hfg).
  apply big_sum_eq_bounded.
  auto with zarith.
Qed.

Lemma Nsum_index_1 n k (Hk : k < n) : 
  Nsum_index n (fun _ => 1) k = k.
Proof.
  induction n; [lia|].
  cbn.
  rewrite Nsum_1.
  bdestruct_one; lia.
Qed.

Lemma Nsum_offset_1 n k (Hk : k < n) : 
  Nsum_offset n (fun _ => 1) k = 0.
Proof.
  pose proof (Nsum_index_offset_spec n (fun _ => 1) k).
  rewrite Nsum_1 in H.
  lia.
Qed.

Lemma Nsum_index_constant n d k (Hk : k < n * d) : 
  Nsum_index n (fun _ => d) k = k / d.
Proof.
  induction n; [lia|].
  cbn.
  rewrite Nsum_constant.
  bdestructΩ'.
  symmetry.
  apply Kronecker.div_eq_iff; lia.
Qed.

Lemma Nsum_offset_constant n d k (Hk : k < n * d) : 
  Nsum_offset n (fun _ => d) k = k mod d.
Proof.
  pose proof (Nsum_index_offset_spec n (fun _ => d) k 
    ltac:(rewrite Nsum_constant; lia)).
  rewrite Nsum_index_constant, Nsum_constant in H
    by auto.
  pose proof (Nat.div_mod_eq k d).
  lia.
Qed.

Lemma Nsum_index_big n g k (Hk : big_sum g n <= k) : 
  Nsum_index n g k = pred n.
Proof.
  induction n; [reflexivity|].
  cbn in *.
  bdestructΩ'.
Qed.

Lemma Nsum_index_add n m g k (Hk : k < big_sum g (n + m)) : 
  Nsum_index (n + m) g k = 
  if k <? big_sum g n then (Nsum_index n g k)
  else n + (Nsum_index m (fun i => (g (n + i))) (k - big_sum g n)).
Proof.
  induction m.
  - rewrite Nat.add_0_r in *; bdestructΩ'.
  - pose proof (Nsum_le_r n (n + m) g ltac:(lia)).
    pose proof (big_sum_sum n m g) as Hsplit.
    cbn [nat_is_monoid Gplus] in Hsplit.
    rewrite Nat.add_succ_r.
    cbn -[Nat.ltb].
    bdestructΩ'.
Qed.

Lemma Nsum_offset_add n m g k (Hk : k < big_sum g (n + m)) : 
  Nsum_offset (n + m) g k = 
  if k <? big_sum g n then (Nsum_offset n g k)
  else Nsum_offset m (fun i => (g (n + i))) (k - big_sum g n).
Proof.
  unfold Nsum_offset.
  rewrite Nsum_index_add by auto.
  bdestruct (k <? big_sum g n); [auto|].
  rewrite big_sum_sum.
  cbn; lia.
Qed.

Lemma Nsum_index_succ n g k (Hk : k < big_sum g (S n)) : 
  Nsum_index (S n) g k = 
  if k <? g 0 then 0
  else S (Nsum_index n (g ∘ S) (k - g 0)).
Proof.
  exact (Nsum_index_add 1 n g k Hk).
Qed.

Lemma Nsum_offset_succ n g k (Hk : k < big_sum g (S n)) : 
  Nsum_offset (S n) g k = 
  if k <? g 0 then k
  else Nsum_offset n (g ∘ S) (k - g 0).
Proof.
  change (S n) with (1 + n).
  rewrite (Nsum_offset_add 1 n g k Hk).
  apply f_equal_if_precedent_same; [|reflexivity].
  unfold Nsum_offset.
  cbn; if_true_lia; cbn; lia.
Qed.

Lemma Nsum_offset_succ_defn n g k : 
  Nsum_offset (S n) g k = 
  if big_sum g n <=? k then k - big_sum g n else
  Nsum_offset n g k.
Proof.
  unfold Nsum_offset.
  cbn.
  bdestructΩ'.
Qed.

Lemma Nsum_index_succ_r n ns k : 
  Nsum_index (S n) ns k = 
  if k <? big_sum ns n then 
    Nsum_index n ns k
  else n.
Proof.
  cbn.
  now rewrite Nat.leb_antisym, negb_if.
Qed.

Lemma Nsum_offset_succ_r n ns k : 
  Nsum_offset (S n) ns k = 
  if k <? big_sum ns n then 
    Nsum_offset n ns k
  else k - big_sum ns n.
Proof.
  unfold Nsum_offset.
  rewrite Nsum_index_succ_r.
  now bdestruct_one.
Qed.

(* NB : This goes with Nsum (/ _index / _offset) lemmas, 
   not just general lemmas. *)
Lemma big_sum_double_sum_indexed {G} {H : Monoid G} fs ns n :
  big_sum (fun k => big_sum (fs k) (ns k)) n =
  big_sum (fun k => fs (Nsum_index n ns k) (Nsum_offset n ns k)) 
    (big_sum ns n).
Proof.
  induction n; [reflexivity|].
  cbn.
  rewrite big_sum_sum.
  f_equal.
  - rewrite IHn.
    apply big_sum_eq_bounded.
    intros k Hk.
    rewrite Nsum_offset_succ_defn.
    now simplify_bools_lia_one_kernel.
  - apply big_sum_eq_bounded.
    intros k Hk.
    simplify_bools_lia_one_kernel.
    now rewrite Nsum_offset_add_big_sum_l by lia.
Qed.




Lemma Nsum_index_lt_iff n ns k l (Hl : l < n) :
  Nsum_index n ns k < l <-> k < big_sum ns l.
Proof.
  bdestruct (k <? big_sum ns n).
  - pose proof (Nsum_index_offset_spec n ns k ltac:(auto)).
    split.
    + intros Hlt.
      pose proof (Nsum_le_r (S (Nsum_index n ns k)) l ns).
      cbn in *.
      lia.
    + intros Hlt.
      pose proof (Nsum_index_spec n ns k ltac:(auto)).
      pose proof (Nsum_le_r l (Nsum_index n ns k) ns).
      lia.
  - rewrite Nsum_index_big by auto.
    pose proof (Nsum_le_r l n ns).
    lia.
Qed.

Lemma Nsum_index_eq_iff n ns k l (Hk : k < big_sum ns n) (Hl : l < n) : 
  Nsum_index n ns k = l <-> (big_sum ns l <= k < big_sum ns (S l)).
Proof.
  split.
  - intros; subst l. 
    pose proof (Nsum_index_offset_spec n ns k Hk).
    cbn. 
    lia.
  - intros [Hle Hlt].
    enough (~ Nsum_index n ns k < l /\ Nsum_index n ns k < S l) by lia.
    rewrite Nsum_index_lt_iff by auto.
    split; [lia|].
    bdestruct (S l =? n).
    + replace -> (S l).
      apply Nsum_index_bounded; lia.
    + rewrite Nsum_index_lt_iff by lia.
      auto.
Qed.

Lemma Nsum_index_eqb_iff n ns k l (Hk : k < big_sum ns n) (Hl : l < n) : 
  (Nsum_index n ns k =? l) = 
  (big_sum ns l <=? k) && (k <? big_sum ns (S l)).
Proof.
  apply eq_iff_eq_true; 
  rewrite Nat.eqb_eq, andb_true_iff, Nat.ltb_lt, Nat.leb_le.
  now apply Nsum_index_eq_iff.
Qed.

Lemma Nsum_index_if_lt n m ns ms k 
  (Hk : k < big_sum (fun i => if i <? n then ns i else ms i) (n + m)): 
  Nsum_index (n + m) (fun i => if i <? n then ns i else ms i) k = 
  if k <? big_sum ns n then Nsum_index n ns k else
  n + Nsum_index m (fun i => ms (n + i)) (k - big_sum ns n).
Proof.
  rewrite Nsum_index_add by auto.
  rewrite (big_sum_eq_bounded _ ns) by (intros; bdestructΩ').
  bdestruct (k <? big_sum ns n).
  - erewrite Nsum_index_perm_eq_to_eq; [reflexivity|].
    intros l Hl; bdestructΩ'.
  - erewrite Nsum_index_perm_eq_to_eq; [reflexivity|].
    intros l Hl; bdestructΩ'.
Qed.

Lemma Nsum_offset_if_lt n m ns ms k 
  (Hk : k < big_sum (fun i => if i <? n then ns i else ms i) (n + m)): 
  Nsum_offset (n + m) (fun i => if i <? n then ns i else ms i) k = 
  if k <? big_sum ns n then Nsum_offset n ns k else
  Nsum_offset m (fun i => ms (n + i)) (k - big_sum ns n).
Proof.
  rewrite Nsum_offset_add by auto.
  rewrite (big_sum_eq_bounded _ ns) by (intros; bdestructΩ').
  bdestruct (k <? big_sum ns n).
  - erewrite Nsum_offset_perm_eq_to_eq; [reflexivity|].
    intros l Hl; bdestructΩ'.
  - erewrite Nsum_offset_perm_eq_to_eq; [reflexivity|].
    intros l Hl; bdestructΩ'.
Qed.


(* Section on extra permutation lemmas, in Preliminary.v *)

Lemma perm_big_of_small_eq_idn n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) : 
  forall k, n <= k < m -> n <= f k.
Proof.
  assert (Hfeqinv : forall k, k < m -> f k < n -> k < n). 1:{
    intros k Hk Hfk.
    enough (f k = k) by lia.
    apply (permutation_is_injective m f Hf); [lia..|].
    now apply Hfeq.
  }
  intros k [].
  bdestructΩ (n <=? f k).
  specialize (Hfeqinv k); lia.
Qed.

Lemma perm_inv_perm_eq_idn_of_perm_eq_idn_up_to n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) :
  perm_eq n (perm_inv m f) idn.
Proof.
  intros k Hk.
  apply (permutation_is_injective m f Hf); [auto with perm_bounded_db..|].
  cleanup_perm.
  symmetry.
  now apply Hfeq.
Qed.

Lemma perm_shift_permutation_of_small_eq_idn n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) : 
  permutation (m - n) (fun k => f (k + n) - n).
Proof.
  pose proof (perm_big_of_small_eq_idn n m f Hm Hf Hfeq) as Hfbig.
  pose proof (perm_big_of_small_eq_idn n m _ Hm (perm_inv_permutation m f Hf) 
    (perm_inv_perm_eq_idn_of_perm_eq_idn_up_to n m f Hm Hf Hfeq))
    as Hfinvbig.
  exists (fun k => (perm_inv m f (k + n) - n)).
  intros k Hk; repeat split.
  - pose proof (permutation_is_bounded m f Hf (k + n)).
    lia.
  - pose proof (perm_inv_bounded m f (k + n)).
    lia.
  - rewrite Nat.sub_add by (apply Hfbig; lia).
    cleanup_perm;
    lia.
  - rewrite Nat.sub_add by (apply Hfinvbig; lia).
    cleanup_perm;
    lia.
Qed.
  
#[export] Hint Resolve perm_shift_permutation_of_small_eq_idn : perm_db.


Lemma perm_eq_of_small_eq_idn n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) : 
  perm_eq m f (stack_perms n (m - n) idn (fun k => f (k + n) - n)).
Proof.
  assert (Hfeqinv : forall k, k < m -> f k < n -> k < n). 1:{
    intros k Hk Hfk.
    enough (f k = k) by lia.
    apply (permutation_is_injective m f Hf); [lia..|].
    now apply Hfeq.
  }
  assert (Hfbig : forall k, n <= k < m -> n <= f k). 1: {
    intros k [].
    bdestructΩ (n <=? f k).
    specialize (Hfeqinv k); lia.
  }
  intros k Hk.
  bdestruct (k <? n).
  - rewrite stack_perms_left by lia.
    now apply Hfeq.
  - rewrite stack_perms_right by lia.
    rewrite (Nat.sub_add n k) by lia.
    specialize (Hfbig k).
    lia.
Qed.

(* TODO: Move, ideally to Qlib *)
Lemma perm_eq_dim_change_if_nonzero n m f g :  
  perm_eq m f g -> (n <> 0 -> n = m) -> perm_eq n f g.
Proof.
  intros Hfg H k Hk.
  rewrite H in Hk by lia.
  now apply Hfg.
Qed.

Lemma big_swap_perm_conj_reflect_eq' n p q : n = p + q ->
  reflect_perm n ∘ big_swap_perm p q ∘ reflect_perm n =
  big_swap_perm q p.
Proof.
  intros ->.
  eq_by_WF_perm_eq (p + q).
  rewrite reflect_perm_defn at 2.
  rewrite reflect_perm_defn.
  intros k Hk.
  unfold compose, big_swap_perm.
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_perm_permutation_alt | 10 : perm_db.

#[export] Hint Extern 100 (WF_Matrix _) => 
  apply WF_Matrix_dim_change : wf_db.

Definition swap_2_to_2_perm a b c d n := 
  fun k =>
  if n <=? k then k else
  if b =? c then (
    if k =? a then b else
    if k =? b then d else
    if k =? d then a else k
  ) else if a =? d then (
    if k =? a then c else
    if k =? c then b else
    if k =? b then a else k
  ) else (
    if k =? a then c else 
    if k =? b then d else
    if k =? c then a else
    if k =? d then b else k).

Lemma swap_2_to_2_perm_WF a b c d n :
  WF_Perm n (swap_2_to_2_perm a b c d n).
Proof.
  intros k Hk.
  unfold swap_2_to_2_perm; bdestructΩ'.
Qed.

#[export] Hint Resolve swap_2_to_2_perm_WF : WF_Perm_db.

Lemma swap_2_to_2_perm_invol a b c d n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hd : d < n) 
  (Hab : a <> b) (Hbc : b <> c) (Hcd : c <> d) 
  (Had : a <> d) :
  swap_2_to_2_perm a b c d n ∘ swap_2_to_2_perm a b c d n = idn.
Proof.
  eq_by_WF_perm_eq n.
  intros k Hk.
  unfold swap_2_to_2_perm, compose.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_2_to_2_perm_invol : perm_inv_db.

Lemma swap_2_to_2_perm_bounded a b c d n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hd : d < n) : 
  perm_bounded n (swap_2_to_2_perm a b c d n).
Proof.
  intros k Hk.
  unfold swap_2_to_2_perm.
  simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_2_to_2_perm_bounded : perm_bounded_db.

Lemma swap_2_to_2_perm_permutation a b c d n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hd : d < n) 
  (Hab : a <> b) (Hcd : c <> d) : 
  permutation n (swap_2_to_2_perm a b c d n).
Proof.
  bdestruct (b =? c);
  [|bdestruct (a =? d)].
  - exists (swap_2_to_2_perm d b b a n).
    intros k Hk; repeat split;
    unfold swap_2_to_2_perm;
    do 2 simplify_bools_lia_one_kernel;
    bdestructΩ'.
  - exists (swap_2_to_2_perm a c b a n).
    intros k Hk; repeat split;
    unfold swap_2_to_2_perm;
    do 2 simplify_bools_lia_one_kernel;
    bdestructΩ'.
  - perm_by_inverse (swap_2_to_2_perm a b c d n).
Qed.

#[export] Hint Resolve swap_2_to_2_perm_permutation : perm_db.

Lemma swap_2_to_2_perm_first a b c d n (Ha : a < n) : 
  swap_2_to_2_perm a b c d n a = c.
Proof.
  unfold swap_2_to_2_perm; bdestructΩ'.
Qed.

Lemma swap_2_to_2_perm_second a b c d n (Ha : b < n) (Hab : a <> b) : 
  swap_2_to_2_perm a b c d n b = d.
Proof.
  unfold swap_2_to_2_perm.
  bdestructΩ'.
Qed.


(* FIXME: Move *)

Lemma perm_inj_mono n m (Hm : m <= n) (f : nat -> nat) 
  (Hf : perm_inj n f) : perm_inj m f.
Proof. auto with zarith. Qed.

(* FIXME: Move *)
Lemma perm_eq_mono n m (Hnm : n <= m) f g : 
  perm_eq m f g -> perm_eq n f g.
Proof.
  unfold perm_eq; auto with zarith.
Qed.

Lemma permutation_eqb_iff_WF n f (Hf : permutation n f) (HWFf : WF_Perm n f) 
  a b : 
  (f a =? f b) = (a =? b).
Proof.
  apply eq_iff_eq_true; rewrite 2!Nat.eqb_eq.
  split; [|now intros []].
  pose proof (permutation_is_bounded n f Hf) as Hfbdd.
  pose proof (Hfbdd a).
  pose proof (Hfbdd b).
  pose proof (fun Ha Hb => (proj1 (permutation_eq_iff a b Hf Ha Hb))).
  pose proof (HWFf a).
  pose proof (HWFf b).
  bdestruct (a <? n);
  bdestruct (b <? n); lia.
Qed.

(* FIXME: Move *)
Lemma permutation_neq_iff {n f} (Hf : permutation n f) a b : 
  a < n -> b < n -> a <> b <-> f a <> f b.
Proof.
  pose proof (permutation_eq_iff a b Hf); lia.
Qed.

Lemma permutation_neq {n f} (Hf : permutation n f) a b : 
  a < n -> b < n -> a <> b -> f a <> f b.
Proof.
  pose proof (permutation_eq_iff a b Hf); lia.
Qed.

Lemma perm_eq_split_times_2_iff n f g : 
  perm_eq (n * 2) f g <-> 
  (forall k, k < n -> 
  f (k * 2) = g (k * 2) /\ f (k * 2 + 1) = g (k * 2 + 1)).
Proof.
  split.
  - intros Hfg k Hk.
    now rewrite 2!Hfg by show_moddy_lt.
  - intros Hfg k Hk.
    rewrite (Nat.div_mod_eq k 2).
    pose proof (Nat.mod_upper_bound k 2).
    destruct (ltac:(lia) : k mod 2 = 0 \/ k mod 2 = 1) as [-> | ->].
    + rewrite Nat.add_0_r, Nat.mul_comm.
      apply Hfg.
      apply Nat.Div0.div_lt_upper_bound; lia.
    + rewrite Nat.mul_comm.
      apply Hfg.
      apply Nat.Div0.div_lt_upper_bound; lia.
Qed.


(* FIXME: Move to Qlib *)
Definition make_WF_Perm n f :=
  fun k => if n <=? k then k else f k.

Lemma make_WF_Perm_perm_eq n f : 
  perm_eq n (make_WF_Perm n f) f.
Proof.
  intros k Hk.
  unfold make_WF_Perm.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite make_WF_Perm_perm_eq : perm_cleanup_db.
#[export] Hint Resolve make_WF_Perm_perm_eq : perm_cleanup_db.

Lemma make_WF_Perm_WF n f : WF_Perm n (make_WF_Perm n f).
Proof.
  intros k Hk.
  unfold make_WF_Perm.
  bdestructΩ'.
Qed.

#[export] Hint Resolve make_WF_Perm_WF : WF_Perm_db.

Add Parametric Morphism n : (make_WF_Perm n) with signature
  perm_eq n ==> eq as make_WF_Perm_eq_of_perm_eq.
Proof.
  intros f g Hfg.
  eq_by_WF_perm_eq n.
  cleanup_perm.
Qed.

Lemma make_WF_Perm_permutation n f : 
  permutation n f -> permutation n (make_WF_Perm n f).
Proof.
  cleanup_perm.
Qed.

#[export] Hint Resolve make_WF_Perm_permutation : perm_db.

Lemma make_WF_Perm_bounded n f : 
  perm_bounded n f -> perm_bounded n (make_WF_Perm n f).
Proof.
  intros Hf k Hk.
  rewrite make_WF_Perm_perm_eq; auto.
Qed.

#[export] Hint Resolve make_WF_Perm_bounded : perm_bounded_db.

Lemma make_WF_Perm_inv n f : 
  perm_eq n (perm_inv n (make_WF_Perm n f)) (perm_inv n f).
Proof.
  now rewrite make_WF_Perm_perm_eq.
Qed.

Lemma make_WF_Perm_inv' n f :
  perm_inv' n (make_WF_Perm n f) = perm_inv' n f.
Proof.
  apply perm_inv'_eq_of_perm_eq.
  cleanup_perm.
Qed.

Lemma make_WF_Perm_of_WF n f : WF_Perm n f -> 
  make_WF_Perm n f = f.
Proof.
  intros Hf.
  eq_by_WF_perm_eq n.
  apply make_WF_Perm_perm_eq.
Qed.

Lemma WF_Perm_change_dims n m f (Hnm : n = m) : 
  WF_Perm m f -> WF_Perm n f.
Proof. now subst. Qed.

(* FIXME: Move *)
Lemma permutation_if n (b : bool) (f g : nat -> nat) : 
  permutation n f -> permutation n g -> 
  permutation n (if b then f else g).
Proof.
  now destruct b.
Qed.

#[export] Hint Resolve permutation_if : perm_db.

(* FIXME: Move to Qlib *)
Lemma WF_Perm_rw {n f g} (Hfg : perm_eq n f g) : 
  WF_Perm n f -> WF_Perm n g -> f = g.
Proof.
  intros Hf Hg.
  now eq_by_WF_perm_eq n.
Qed.

(* FIXME: Move to Qlib *)
Lemma WF_Perm_monotone n m f :
  WF_Perm n f -> n <= m -> WF_Perm m f.
Proof.
  unfold WF_Perm.
  auto with zarith.
Qed.


(* FIXME: Move *)
Lemma perm_eq_0 f g :
  perm_eq 0 f g.
Proof. 
  easy.
Qed.

Lemma perm_eq_1 f g (Hf : perm_bounded 1 f) (Hg : perm_bounded 1 g) : 
  perm_eq 1 f g.
Proof.
  specialize (Hf 0).
  specialize (Hg 0).
  intros [] Hk; lia.
Qed.

Lemma permutation_0 f : permutation 0 f.
Proof. 
  exists idn.
  easy.
Qed.

(* FIXME: Move *)
Lemma permutation_1_case f (Hf : permutation 1 f) : 
  perm_eq 1 f idn.
Proof.
  apply perm_eq_1; auto_perm.
Qed.

Lemma permutation_2_case f (Hf : permutation 2 f) : 
  {perm_eq 2 f idn} + {perm_eq 2 f swap_2_perm}.
Proof.
  assert (f 0 < 2) by auto_perm.
  assert (f 1 < 2) by auto_perm.
  assert (f 1 <> f 0) by (apply (permutation_neq Hf); lia).
  bdestruct (f 0 =? 0).
  - left.
    by_perm_cell; lia.
  - right.
    by_perm_cell; cbn; lia.
Qed.

(* FIXME: Move to Qlib.PermutationInstances *)
Lemma stack_perms_0_l m f g : 
  stack_perms 0 m f g = make_WF_Perm m g.
Proof.
  eq_by_WF_perm_eq m.
  rewrite stack_perms_defn, make_WF_Perm_perm_eq.
  intros k Hk.
  simpl.
  now rewrite Nat.sub_0_r, Nat.add_0_r.
Qed.

Lemma stack_perms_0_r n f g : 
  stack_perms n 0 f g = make_WF_Perm n f.
Proof.
  eq_by_WF_perm_eq n.
  rewrite <- (Nat.add_0_r n).
  rewrite Nat.add_0_r at 2.
  rewrite stack_perms_defn, make_WF_Perm_perm_eq.
  intros k Hk.
  bdestructΩ'.
Qed.

(* FIXME: Move to Qlib.PermutationInstances *)

Lemma stack_perms_assoc_fwd_change_dims n0 n1 n2 n01 f g h : 
  n01 = n0 + n1 ->
  stack_perms n01 n2 (stack_perms n0 n1 f g) h = 
  stack_perms n0 (n1 + n2) f (stack_perms n1 n2 g h).
Proof.
  intros ->.
  apply stack_perms_assoc.
Qed.

Lemma stack_perms_assoc_rev_change_dims n0 n1 n2 n12 f g h : 
  n12 = n1 + n2 ->
  stack_perms n0 n12 f (stack_perms n1 n2 g h) = 
  stack_perms (n0 + n1) n2 (stack_perms n0 n1 f g) h.
Proof.
  intros ->.
  symmetry.
  apply stack_perms_assoc.
Qed.


(* FIXME: Move, likely to Qlib *)
(* TODO: version for idn_r *)
Lemma tensor_perms_stack_l_split n0 n1 m f0 f1 g : 
  tensor_perms (n0 + n1) m (stack_perms n0 n1 f0 f1) g =
  stack_perms (n0 * m) (n1 * m)
    (tensor_perms n0 m f0 g)
    (tensor_perms n1 m f1 g).
Proof.
  eq_by_WF_perm_eq ((n0 + n1) * m).
  rewrite (stack_perms_defn n0 n1).
  rewrite !tensor_perms_defn, Nat.mul_add_distr_r, stack_perms_defn.
  intros k HK.
  pose proof (Nat.Div0.div_lt_upper_bound k m n0).
  pose proof (Nat.div_le_lower_bound k m n0 ltac:(lia)).
  bdestructΩ'.
  rewrite sub_mul_mod by lia.
  rewrite sub_mul_div by lia.
  lia.
Qed.

Lemma tensor_perms_idn_l_split n0 n1 m f :
  tensor_perms (n0 + n1) m idn f =
  stack_perms (n0 * m) (n1 * m) 
  (tensor_perms n0 m idn f)
  (tensor_perms n1 m idn f).
Proof.
  now rewrite <- tensor_perms_stack_l_split, stack_perms_idn_idn.
Qed.






(* FIXME: Move to Qlib.PermutationInstances *)
Lemma big_swap_perm_ltb_r n m k : 
  big_swap_perm n m k <? m = ((¬ k <? n) && (k <? n + m)).
Proof.
  unfold big_swap_perm.
  bdestructΩ'.
Qed.

(* FIXME: Move, to various places *)
Lemma big_swap_perm_join_hex_l a b c :
  stack_perms (a + c) b (big_swap_perm a c) idn ∘
  stack_perms a (b + c) idn (big_swap_perm b c) = 
  big_swap_perm (a + b) c.
Proof.
  eq_by_WF_perm_eq (a + b + c).
  rewrite big_swap_perm_defn.
  replace (a + b + c) with (a + c + b) by lia.
  rewrite stack_perms_defn.
  rewrite big_swap_perm_defn.
  replace (a + c + b) with (a + (b + c)) by lia.
  rewrite stack_perms_defn.
  rewrite Nat.add_assoc, big_swap_perm_defn.
  intros k Hk.
  unfold compose.
  bdestructΩ'.
Qed.

Lemma big_swap_perm_join_hex_r a b c :
  stack_perms b (a + c) idn (big_swap_perm a c) ∘
  stack_perms (a + b) c (big_swap_perm a b) idn = 
  big_swap_perm a (b + c).
Proof.
  eq_by_WF_perm_eq (a + (b + c)).
  rewrite big_swap_perm_defn.
  replace (a + (b + c)) with (b + (a + c)) by lia.
  rewrite stack_perms_defn.
  rewrite big_swap_perm_defn.
  replace (b + (a + c)) with (a + b + c) by lia.
  rewrite stack_perms_defn.
  rewrite <- Nat.add_assoc, big_swap_perm_defn.
  intros k Hk.
  unfold compose.
  bdestructΩ'.
Qed.

Lemma kron_comm_perm_div_r p q k (Hk : k < p * q) : 
  kron_comm_perm p q k / q = k mod p.
Proof.
  rewrite kron_comm_perm_defn by auto.
  rewrite Nat.div_add_l by lia.
  rewrite Nat.div_small by show_moddy_lt.
  lia.
Qed.

Lemma kron_comm_perm_mod_r p q k (Hk : k < p * q) : 
  (kron_comm_perm p q k) mod q = k / p.
Proof.
  rewrite kron_comm_perm_defn by auto.
  rewrite mod_add_l by lia.
  now rewrite Nat.mod_small by show_moddy_lt.
Qed.


(* FIXME: Move this improved version to Qlib *)
Lemma compose_perm_inv_r :forall (n : nat) (f g h : nat -> nat),
  permutation n f ->
  perm_eq n (g ∘ perm_inv n f) h <-> perm_eq n g (h ∘ f).
Proof.
  intros n f g h Hf.
  split;
  [intros <- | intros ->];
  cleanup_perm.
Qed.

(* FIXME: Move to Qlib *)
Lemma perm_inv_stack_perms_change_dims nm n m f g 
  (Hf : permutation n f) (Hg : permutation m g) (Hnm : nm = n + m) :
  perm_eq nm (perm_inv nm (stack_perms n m f g))
  (stack_perms n m (perm_inv n f) (perm_inv m g)).
Proof.
  subst.
  now apply perm_inv_stack_perms.
Qed.

(* FIXME: Move to Qlib *)
Lemma big_swap_perm_left p q a : a < p -> 
  big_swap_perm p q a = a + q.
Proof. unfold big_swap_perm; bdestructΩ'. Qed.

Lemma big_swap_perm_right p q a : p <= a < p + q -> 
  big_swap_perm p q a = a - p.
Proof. unfold big_swap_perm; bdestructΩ'. Qed.

Lemma big_swap_perm_pair_mid_l a b c d : 
  stack_perms (a + c + d) b
  (stack_perms c (a + d) idn (big_swap_perm d a)) idn ∘
  big_swap_perm (a + b) (c + d) =
  stack_perms (a + c) (b + d) 
    (big_swap_perm a c) (big_swap_perm b d) ∘
  stack_perms (a + b + c) d
    (stack_perms a (b + c) idn (big_swap_perm b c)) idn.
Proof.
  eq_by_WF_perm_eq (a + b + c + d).
  intros k Hk.
  bdestruct (k <? a);
  [|bdestruct (k <? a + b);
  [|bdestruct (k <? a + b + c)]].
  - unfold compose.
    rewrite big_swap_perm_left by lia.
    rewrite stack_perms_left, stack_perms_right by lia.
    rewrite big_swap_perm_right by lia.
    (rewrite_strat innermost stack_perms_left); [|lia].
    (rewrite_strat innermost stack_perms_left); [|lia].
    rewrite stack_perms_left by lia.
    rewrite big_swap_perm_left by lia.
    lia.
  - unfold compose.
    rewrite big_swap_perm_left by lia.
    rewrite stack_perms_right by lia.
    (rewrite_strat innermost stack_perms_left); [|lia].
    (rewrite_strat innermost stack_perms_right); [|lia].
    rewrite big_swap_perm_left by lia.
    rewrite stack_perms_right by lia.
    rewrite big_swap_perm_left by lia.
    lia.
  - unfold compose.
    rewrite big_swap_perm_right by lia.
    rewrite stack_perms_left by lia.
    rewrite stack_perms_left by lia.
    (rewrite_strat innermost stack_perms_left); [|lia].
    (rewrite_strat innermost stack_perms_right); [|lia].
    rewrite big_swap_perm_right by lia.
    rewrite stack_perms_left by lia.
    rewrite big_swap_perm_right by lia.
    lia.
  - unfold compose.
    rewrite big_swap_perm_right by lia.
    rewrite stack_perms_left by lia.
    rewrite stack_perms_right by lia.
    (rewrite_strat innermost stack_perms_right); [|lia].
    (rewrite_strat innermost stack_perms_right); [|lia].
    rewrite big_swap_perm_left by lia.
    rewrite big_swap_perm_right by lia.
    lia.
Qed.

Lemma big_swap_perm_pair_mid_r a b c d : 
  big_swap_perm (c + d) (a + b) ∘ 
  stack_perms (a + c + d) b
  (stack_perms c (a + d) idn (big_swap_perm a d)) idn =
  stack_perms (a + b + c) d
    (stack_perms a (b + c) idn (big_swap_perm c b)) idn ∘
  stack_perms (a + c) (b + d) 
    (big_swap_perm c a) (big_swap_perm d b).
Proof.
  eq_by_WF_perm_eq (a + b + c + d).
  apply (perm_inv_perm_eq_injective
    (stack_perms (a + c + d) b
    (stack_perms c (a + d) idn (big_swap_perm d a)) idn ∘
    big_swap_perm (a + b) (c + d))); [auto_perm|..].
  - rewrite !compose_assoc.
    rewrite_compose_assoc_r @stack_perms_compose; [|auto_perm..].
    rewrite stack_perms_compose by auto_perm.
    rewrite big_swap_perm_invol, 2!stack_perms_idn_idn.
    now rewrite big_swap_perm_invol.
  - rewrite big_swap_perm_pair_mid_l.
    rewrite !compose_assoc.
    rewrite_compose_assoc_r @stack_perms_compose; [|auto_perm..].
    rewrite 2!big_swap_perm_invol, stack_perms_idn_idn.
    rewrite compose_idn_l.
    rewrite 2!stack_perms_compose by auto_perm.
    rewrite big_swap_perm_invol.
    now rewrite 2!stack_perms_idn_idn.
Qed.

(* FIXME: Move to PermutationMatrices *)
Lemma perm_to_matrix_big_swap_perm p q : 
  perm_to_matrix (p + q) (big_swap_perm p q) = 
  kron_comm (2 ^ p) (2 ^ q).
Proof.
  symmetry.
  rewrite kron_comm_pows2_eq_perm_to_matrix_big_swap.
  now rewrite Nat.add_comm.
Qed.

Lemma perm_to_matrix_big_swap_perm' p q pq : pq = p + q ->
  perm_to_matrix pq (big_swap_perm p q) = 
  kron_comm (2 ^ p) (2 ^ q).
Proof.
  intros ->; apply perm_to_matrix_big_swap_perm.
Qed.



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

Lemma kron_comm_perm_2_n_succ p : 
  perm_eq (2 * (S p)) (kron_comm_perm 2 (S p))
  ( stack_perms (p + S p) 1 (stack_perms p (S p) idn (big_swap_perm p 1)) idn
    ∘ stack_perms (2 * p) 2 (kron_comm_perm 2 p) idn).
Proof.
  rewrite 2!kron_comm_perm_defn.
  intros k Hk.
  unfold compose at 1.
  bdestruct (k <? 2 * p).
  - rewrite (stack_perms_left (k := k)) by auto.
    assert (k / 2 < p) by show_moddy_lt.
    assert (Hor : k mod 2 = 0 \/ k mod 2 = 1) by   
      (pose proof (Nat.mod_upper_bound k 2); lia).
    destruct Hor as [Hor | Hor]; rewrite Hor.
    + rewrite 2!Nat.mul_0_l, Nat.add_0_l.
      now rewrite 2!stack_perms_left by lia.
    + rewrite stack_perms_left, stack_perms_right by lia.
      rewrite big_swap_perm_left by lia.
      lia.
  - rewrite (stack_perms_right (k := k)) by lia.
    rewrite Nat.sub_add by lia.
    bdestruct (k =? p * 2).
    + rewrite stack_perms_left, stack_perms_right by lia.
      rewrite big_swap_perm_right by lia.
      subst k.
      rewrite Nat.Div0.mod_mul, Nat.div_mul by lia.
      lia.
    + replace k with (p * 2 + 1) by lia.
      rewrite mod_add_l, Nat.div_add_l by lia.
      rewrite stack_perms_right by lia.
      cbn; lia.
Qed.

Lemma kron_comm_perm_2_n_succ_alt p : 
  perm_eq (2 * (S p)) (kron_comm_perm 2 (S p))
  ( stack_perms 1 (p + S p) idn (stack_perms (S p) p (big_swap_perm 1 p) idn)
    ∘ stack_perms 2 (2 * p) idn (kron_comm_perm 2 p)).
Proof.
  rewrite 2!kron_comm_perm_defn.
  intros k Hk.
  unfold compose at 1.
  bdestruct (k <? 2).
  - rewrite (stack_perms_left (k := k)) by auto.
    rewrite Nat.mod_small, Nat.div_small by auto.
    destruct (ltac:(lia) : k = 0 \/ k = 1) as [-> | ->].
    + rewrite stack_perms_left by lia.
      lia.
    + rewrite stack_perms_right by lia.
      rewrite stack_perms_left by lia.
      rewrite big_swap_perm_left by lia.
      lia.
  - rewrite (stack_perms_right (k := k)) by lia.
    assert (Hkge : 2 <= k) by auto.
    destruct (le_ex_diff_r _ _ Hkge) as [l Hl].
    subst k.
    rewrite add_sub' by lia.
    assert (Hl : l < 2 * p) by lia.
    rewrite (Nat.add_comm 2 l).
    rewrite mod_add_n_r, div_add_n_r by auto.
    assert (l mod 2 < 2) by show_moddy_lt.
    assert (l / 2 < p) by show_moddy_lt.
    assert (l mod 2 * p + l / 2 < 2 * p) by show_moddy_lt.
    rewrite stack_perms_right by lia.
    destruct (ltac:(lia) : l mod 2 = 0 \/ l mod 2 = 1) as [Hlmod | Hlmod];
    rewrite Hlmod.
    + rewrite stack_perms_left by lia.
      rewrite big_swap_perm_right by lia.
      lia.
    + rewrite stack_perms_right by lia.
      lia.
Qed.

Lemma enlarge_permutation_1 n f : 
  perm_eq n (enlarge_permutation n f (fun _ => 1)) (perm_inv' n f).
Proof.
  rewrite <- (Nsum_1 n) at 1.
  rewrite enlarge_permutation_defn.
  rewrite (Nsum_1 n).
  intros k Hk.
  rewrite Nsum_offset_1 by auto.
  rewrite Nsum_1, Nsum_index_1 by auto.
  apply Nat.add_0_r.
Qed.

Lemma enlarge_permutation_constant n f d : 
  enlarge_permutation n f (fun _ => d) = 
  tensor_perms n d (perm_inv' n f) idn.
Proof.
  eq_by_WF_perm_eq (n * d);
  [rewrite Nat.mul_comm, <- times_n_nat, <- big_sum_constant; auto_perm|]. 
  rewrite tensor_perms_defn.
  rewrite Nat.mul_comm, <- times_n_nat, <- big_sum_constant.
  rewrite enlarge_permutation_defn.
  unfold compose.
  rewrite big_sum_constant, times_n_nat.
  intros k Hk.
  rewrite big_sum_constant, times_n_nat, 
    Nsum_index_constant, Nsum_offset_constant by lia.
  lia.
Qed.

Lemma enlarge_permutation_swap dims : 
  enlarge_permutation 2 swap_2_perm dims = 
  big_swap_perm (dims 0) (dims 1).
Proof.
  eq_by_WF_perm_eq _.
  rewrite enlarge_permutation_defn.
  rewrite swap_2_perm_inv'.
  intros k Hk.
  rewrite Nsum_index_succ, Nsum_offset_succ by lia.
  unfold compose.
  bdestruct (k <? dims 0).
  - rewrite big_swap_perm_left by auto.
    cbn.
    lia.
  - rewrite big_swap_perm_right by auto.
    unfold Nsum_offset.
    cbn in *.
    rewrite Tauto.if_same.
    cbn; lia.
Qed.

(* TODO: enlarge_permutation_bipermutation, which (should?) require 
  positive dimensions *)


(* FIXME: Move to Qlib *)
Lemma equal_on_basis_states_implies_equal' : (* FIXME: Replace 
  equal_on_basis_states_implies_equal with this *)
  forall {m dim : nat} (A B : Matrix m (2 ^ dim)),
  WF_Matrix A -> WF_Matrix B ->
  (forall f : nat -> bool, A × f_to_vec dim f = B × f_to_vec dim f) -> 
  A = B.
Proof.
  intros m dim A B HA HB HAB.
  prep_matrix_equivalence.
  intros i j Hi Hj.
  rewrite 2!(get_entry_with_e_i _ i j) by lia.
  rewrite 2!Mmult_assoc.
  rewrite <- (basis_vector_eq_e_i _ j) by assumption.
  rewrite basis_f_to_vec_alt by assumption.
  now rewrite HAB.
Qed.

Lemma equal_on_conj_basis_states_implies_equal {n m} 
  (A B : Matrix (2 ^ n) (2 ^ m)) : WF_Matrix A -> WF_Matrix B -> 
  (forall f g, (f_to_vec n g) ⊤%M × (A × f_to_vec m f) = 
    (f_to_vec n g) ⊤%M × (B × f_to_vec m f)) -> A = B.
Proof.
  intros HA HB HAB.
  apply equal_on_basis_states_implies_equal'; [auto..|].
  intros f.
  apply transpose_matrices.
  apply equal_on_basis_states_implies_equal'; [auto_wf..|].
  intros g.
  apply transpose_matrices.
  rewrite Mmult_transpose, transpose_involutive, HAB.
  rewrite Mmult_transpose, transpose_involutive.
  reflexivity.
Qed.




(* FIXME: Move to Qlib *)
Lemma f_to_vec_transpose_f_to_vec n f g :
  transpose (f_to_vec n f) × f_to_vec n g = 
  b2R (forallb (fun k => eqb (f k) (g k)) (seq 0 n)) .* I 1.
Proof.
  prep_matrix_equivalence.
  intros [] []; [|lia..]; intros _ _.
  rewrite 2!basis_f_to_vec.
  rewrite basis_trans_basis.
  simplify_bools_moddy_lia_one_kernel.
  unfold scale.
  cbn.
  rewrite Cmult_1_r.
  unfold b2R.
  rewrite (if_dist _ _ _ RtoC).
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite Nat.eqb_eq, forallb_seq0, <- funbool_to_nat_eq_iff.
  now setoid_rewrite eqb_true_iff.
Qed.

Lemma f_to_vec_transpose_f_to_vec' n f g :
  transpose (f_to_vec n f) × f_to_vec n g = 
  (if funbool_to_nat n f =? funbool_to_nat n g then  
    C1 else C0) .* I 1.
Proof.
  rewrite f_to_vec_transpose_f_to_vec.
  f_equal.
  unfold b2R.
  rewrite (if_dist R C).
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite forallb_seq0, Nat.eqb_eq.
  setoid_rewrite eqb_true_iff.
  apply funbool_to_nat_eq_iff.
Qed.

Lemma f_to_vec_transpose_self n f :
  transpose (f_to_vec n f) × f_to_vec n f = 
  I 1.
Proof.
  rewrite f_to_vec_transpose_f_to_vec', Nat.eqb_refl.
  now Msimpl_light.
Qed.


Import Setoid.

Definition mat_prop (n m : nat) (A B : Matrix n m) : Prop :=
  exists c : C, A = c .* B /\ c <> 0%R.

Notation "A '[∝]' B" := (mat_prop _ _ A B) (at level 70) : matrix_scope.

Lemma mat_prop_is_general {n m} (A B : Matrix n m) : 
  mat_prop n m A B = 
  (Proportional.proportional_general Datatypes.id Datatypes.id A B).
Proof.
  easy.
Qed.

(* #[global] *) Add Parametric Relation n m : (Matrix n m) (@mat_prop n m) 
  reflexivity proved by ltac:(intros A; 
    apply (Proportional.proportional_general_refl _ n m (fun k => k) A))
  symmetry proved by ltac:(intros A B;
    apply (Proportional.proportional_general_symm
    _ n m _ n m (fun k => k) (fun k => k) A B))
  transitivity proved by ltac:(intros A B C;  
  now apply (Proportional.proportional_general_trans 
    _ n m (fun k => k) A
    _ n m (fun k => k) B
    _ n m (fun k => k) C))
  as mat_prop_Setoid.

(* #[global] *) Add Parametric Morphism n m o : (@Mmult n m o) with signature
  mat_prop n m ==> mat_prop m o ==> mat_prop n o as Mmult_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB) C D (cCD & HCD & HcCD).
  Proportional.prop_exists_nonzero (cAB * cCD)%C.
  2: now apply Cmult_neq_0.
  rewrite HAB, HCD.
  now rewrite Mscale_mult_dist_l, Mscale_mult_dist_r, Mscale_assoc.
Qed.

(* #[global] *) Add Parametric Morphism n m o p : (@kron n m o p) with signature
  mat_prop n m ==> mat_prop o p ==> mat_prop (n*o) (m*p) as kron_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB) C D (cCD & HCD & HcCD).
  Proportional.prop_exists_nonzero (cAB * cCD)%C.
  2: now apply Cmult_neq_0.
  rewrite HAB, HCD.
  now rewrite Mscale_kron_dist_l, Mscale_kron_dist_r, Mscale_assoc.
Qed.

(* #[global] *) Add Parametric Morphism n m c : (@scale n m c) with signature
  mat_prop n m ==> mat_prop n m as Mscale_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB).
  Proportional.prop_exists_nonzero (cAB)%C.
  2: easy.
  rewrite HAB.
  now rewrite 2!Mscale_assoc, Cmult_comm.
Qed.

(* #[global] *) Add Parametric Morphism n m : (@transpose n m) with signature
  mat_prop n m ==> mat_prop m n as transpose_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB).
  Proportional.prop_exists_nonzero (cAB)%C.
  2: easy.
  rewrite HAB.
  now rewrite Mscale_trans.
Qed.

(* #[global] *) Add Parametric Morphism n m k : (@kron_n k n m) with signature
  mat_prop n m ==> mat_prop _ _ as kron_n_mat_prop_proper.
Proof.
  intros A B (cAB & HAB & HcAB).
  Proportional.prop_exists_nonzero (cAB ^ k)%C.
  2: now apply Cpow_nonzero.
  rewrite HAB.
  now rewrite Mscale_kron_n_distr_r.
Qed.

(* Notation "A '[∝]' B" := (mat_prop _ _ A B) (at level 70) : matrix_scope. *)
Notation "A '[∝@' n m ']' B" := (mat_prop n m A B) 
  (at level 70, n at level 0, m at level 0, only parsing) : matrix_scope.

Ltac restore_dims_prop :=
  match goal with 
  |- context[?A [∝] ?B] =>
    let B' := restore_dims_rec B in 
    let A' := restore_dims_rec A in 
    replace A with A' by (unify_matrix_dims restore_dims_tac);
    replace B with B' by (unify_matrix_dims restore_dims_tac)
  end. 

Add Parametric Morphism n m : (@ZX_semantics n m) with signature
  @proportional n m ==> @mat_prop (2^m) (2^n) as 
  ZX_semantics_proportional_to_mat_prop.
Proof. intros ? ? H; exact H. Qed.

(* FIXME: Move *)
Lemma ZX_prop_by_mat_prop {n m} (zx0 zx1 : ZX n m) :
  ⟦ zx0 ⟧ [∝] ⟦ zx1 ⟧ -> zx0 ∝ zx1.
Proof. 
  intros H; exact H.
Qed.

Lemma ZX_prop_to_mat_prop {n m} (zx0 zx1 : ZX n m) :
  zx0 ∝ zx1 -> ⟦ zx0 ⟧ [∝] ⟦ zx1 ⟧.
Proof.
  intros H; exact H.
Qed.




(* FIXME: Move to Qlib *)
Lemma big_kron'_eq_bounded_dims {n ns ns' ms ms'}
  {As : forall k, Matrix (2 ^ ns k) (2 ^ ms k)}
  {Bs : forall k, Matrix (2 ^ ns' k) (2 ^ ms' k)}
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms')
  (HAB : forall k, k < n -> As k = Bs k) :
  big_kron' ns ms As n = big_kron' ns' ms' Bs n.
Proof.
  induction n; [easy|].
  cbn.
  f_equal;
  [f_equal; clear IHn; unfold perm_eq in *;
    try apply big_sum_eq_bounded; auto..| |].
  - unfold perm_eq in *; apply IHn; auto.
  - apply HAB; auto.
Qed.

Lemma kron_mat_prop_proper' {n m o p n' m' o' p' no mp} 
  (A : Matrix n m) (A' : Matrix n' m') 
  (B : Matrix o p) (B' : Matrix o' p') : n = n' -> m = m' -> 
  o = o' -> p = p' -> n * o = no -> m * p = mp ->
  mat_prop n m A A' -> mat_prop o p B B' -> 
  mat_prop no mp (@kron n m o p A B) (@kron n' m' o' p' A' B').
Proof.
  intros; subst; now apply kron_mat_prop_proper.
Qed.

Lemma big_kron'_prop_bounded_dims {n ns ns' ms ms'}
	{As : forall k, Matrix (2 ^ ns k) (2 ^ ms k)}
  {Bs : forall k, Matrix (2 ^ ns' k) (2 ^ ms' k)}
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms') 
  (HAB : forall k, k < n -> As k [∝] Bs k) : 
  big_kron' ns ms As n [∝] big_kron' ns' ms' Bs n.
Proof.
  induction n; [reflexivity|].
  cbn.
  apply kron_mat_prop_proper';
  [unify_pows_two; solve [(apply Hns + apply Hms); auto | 
    apply big_sum_eq_bounded; unfold perm_eq in *; auto]..| |now auto].
  unfold perm_eq in *; auto.
Qed.

Lemma big_kron'_prop_bounded {n ns ms} 
	{As : forall k, Matrix (2 ^ ns k) (2 ^ ms k)}
  {Bs : forall k, Matrix (2 ^ ns k) (2 ^ ms k)}
  (HAB : forall k, k < n -> As k [∝] Bs k) : 
  big_kron' ns ms As n [∝] big_kron' ns ms Bs n.
Proof.
  now apply big_kron'_prop_bounded_dims.
Qed.


Lemma big_kron'_double_kron'_indexed 
  nss mss Bss ns n 
  (HBss : forall k, k < n -> forall l, l < ns k -> WF_Matrix (Bss k l)) :
  big_kron' (fun k => big_sum (nss k) (ns k))
    (fun k => big_sum (mss k) (ns k))
    (fun k => big_kron' (nss k) (mss k) (Bss k) (ns k)) n =
  big_kron'
    (fun k => nss (Nsum_index n ns k) (Nsum_offset n ns k))
    (fun k => mss (Nsum_index n ns k) (Nsum_offset n ns k))
    (fun k => Bss (Nsum_index n ns k) (Nsum_offset n ns k))
    (big_sum ns n).
Proof.
  induction n; [reflexivity|].
  cbn -[Nsum_index].
  rewrite big_kron'_split_add;
  [f_equal; unify_pows_two..|].
  - rewrite big_sum_double_sum_indexed.
    apply big_sum_eq_bounded.
    intros k Hk.
    cbn; rewrite Nsum_offset_succ_defn.
    now simplify_bools_lia_one_kernel.
  - rewrite big_sum_double_sum_indexed.
    apply big_sum_eq_bounded.
    intros k Hk.
    cbn; rewrite Nsum_offset_succ_defn.
    now simplify_bools_lia_one_kernel.
  - apply big_sum_eq_bounded.
    intros k Hk.
    now rewrite Nsum_index_add_big_sum_l, Nsum_offset_add_big_sum_l by lia.
  - apply big_sum_eq_bounded.
    intros k Hk.
    now rewrite Nsum_index_add_big_sum_l, Nsum_offset_add_big_sum_l by lia.
  - rewrite IHn by auto.
    apply (@big_kron'_eq_bounded_dims (big_sum ns n));
    intros k Hk; cbn; rewrite Nsum_offset_succ_defn;
    now simplify_bools_lia_one_kernel.
  - apply big_kron'_eq_bounded_dims;
    intros k Hk; now rewrite Nsum_index_add_big_sum_l, 
      Nsum_offset_add_big_sum_l by lia.
  - intros k Hk.
    apply HBss.
    + apply Nsum_index_bounded; lia.
    + apply Nsum_index_offset_spec; cbn; lia.
Qed.

(* FIXME: Move to Qlib *)
Lemma big_kron'_mult ns ms As n n'
  (HAs : forall k, k < n * n' -> WF_Matrix (As k)) : 
  big_kron' ns ms As (n * n') = 
  big_kron'
    (fun k => big_sum (fun i => (ns (k * n' + i))) n')
    (fun k => big_sum (fun i => (ms (k * n' + i))) n')
    (fun k => 
      big_kron' (fun i => (ns (k * n' + i)))
        (fun i => (ms (k * n' + i)))
        (fun i => As (k * n' + i)) 
        n')
    n.
Proof.
  rewrite big_kron'_double_kron'_indexed by 
    (intros k Hk l Hl; apply HAs; show_moddy_lt).
  rewrite Nsum_constant.
  apply big_kron'_eq_bounded_dims;
  intros k Hk;
  rewrite Nsum_index_constant, Nsum_offset_constant, 
    Nat.mul_comm, <- Nat.div_mod_eq by lia; reflexivity.
Qed.


Lemma big_kron_big_kron' {m n} (As : list (Matrix (2^m) (2^n))) 
  (HAs : Forall WF_Matrix As) : 
  big_kron As = big_kron' (fun _ => m) (fun _ => n) (nth_default Zero As)
    (length As).
Proof.
  induction HAs as [|a As Ha HAs IHAs]; [easy|].
  cbn [big_kron length].
  change (S (length As)) with (1 + length As).
  rewrite big_kron'_split_add.
  - f_equal;
    [rewrite <- 1?Nat.pow_mul_r, 1?Nsum_constant; unify_pows_two.. | |].
    + cbn.
      now rewrite kron_1_l.
    + apply IHAs.
  - intros k Hk. 
    rewrite Forall_forall in HAs.
    destruct k; [easy|].
    apply HAs.
    rewrite nth_default_eq.
    cbn.
    apply nth_In; lia.
Qed.




Lemma kron_n_to_big_kron' {n m} k (A : Matrix (2 ^ n) (2 ^ m)) : 
  kron_n k A = big_kron' (fun _ => n) (fun _ => m) (fun _ => A) k.
Proof.
  induction k; [reflexivity|].
  cbn.
  f_equal;
  [now rewrite Nsum_constant, <- Nat.pow_mul_r; 
  unify_pows_two..|].
  apply IHk.
Qed.

Lemma kron_n_enlarge_permutation_natural {n m} k (A : Matrix (2 ^ n) (2 ^ m))
  f (Hf : permutation k f) (HA : WF_Matrix A) :
  @Mmult (2 ^ (n * k)) (2 ^ (m * k)) (2 ^ (m * k)) 
  (kron_n k A) (perm_to_matrix (m * k) (enlarge_permutation k f (fun _ => m))) =
  perm_to_matrix (n * k) (enlarge_permutation k f (fun _ => n)) × kron_n k A.
Proof.
  rewrite kron_n_to_big_kron'.
  rewrite 2!(Nat.mul_comm _ k), <- 2!(Nsum_constant _ k).
  restore_dims.
  rewrite enlarge_permutation_big_kron'_natural by auto.
  reflexivity.
Qed.









(* Section on VyZX lemmas *)

Lemma fn_cast_eq {A} {n m n' m'} (f : forall {n m}, ZX n m -> A) (zx : ZX n m) 
  prfn prfm : 
  f (cast n' m' prfn prfm zx) = f zx.
Proof.
  now subst.
Qed.

(* FIXME: Move *)
Lemma cast_contract_eq {n0 m0 n1 m1 n2 m2}
  (zx : ZX n0 m0) prfn01 prfm01 prfn12 prfm12 : 
  cast n2 m2 prfn12 prfm12 (cast n1 m1 prfn01 prfm01 zx) = 
  cast n2 m2 (eq_trans prfn12 prfn01) (eq_trans prfm12 prfm01) zx.
Proof.
  now subst.
Qed.

(* FIXME: Move *)
Lemma cast_stack_l_r {n0 m0 n0' m0' n1 m1 n1' m1'}
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfn0 prfm0 prfn1 prfm1 : 
  cast n0' m0' prfn0 prfm0 zx0 ↕
  cast n1' m1' prfn1 prfm1 zx1 ∝
  cast _ _ (f_equal2 (Nat.add) prfn0 prfn1)
    (f_equal2 (Nat.add) prfm0 prfm1)
    (zx0 ↕ zx1).
Proof.
  subst; cbn; now rewrite cast_id.
Qed.

Lemma cast_backwards_fwd {n0 m0 n1 m1 : nat}  
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfn prfm : 
  cast _ _ prfn prfm zx0 ∝ zx1 <->
  zx0 ∝ cast _ _ (eq_sym prfn) (eq_sym prfm) zx1.
Proof.
  now subst.
Qed.

Lemma cast_backwards_rev {n0 m0 n1 m1 : nat}  
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfn prfm : 
  zx0 ∝ cast _ _ prfn prfm zx1 <->
  cast _ _ (eq_sym prfn) (eq_sym prfm) zx0 ∝ zx1.
Proof.
  now subst.
Qed.

Lemma prf_add_cancel_l {a b c d} : a + b = c + d -> a = c -> b = d.
Proof. lia. Qed.

Lemma prf_add_cancel_r {a b c d} : a + b = c + d -> b = d -> a = c.
Proof. lia. Qed.

Lemma cast_stack_distribute_fwd_l {n0 m0 n1 m1 n0' m0' n1' m1'} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfns prfms prfn0 prfm0 :
  cast (n0' + n1') (m0' + m1') prfns prfms (zx0 ↕ zx1) ∝
  cast _ _ prfn0 prfm0 zx0 ↕
  cast _ _ (prf_add_cancel_l prfns prfn0) 
    (prf_add_cancel_l prfms prfm0) zx1.
Proof.
  pose proof (prf_add_cancel_l prfns prfn0).
  pose proof (prf_add_cancel_l prfms prfm0).
  subst; cbn; now rewrite !cast_id.
Qed.

Lemma cast_stack_distribute_fwd_r {n0 m0 n1 m1 n0' m0' n1' m1'} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfns prfms prfn1 prfm1 :
  cast (n0' + n1') (m0' + m1') prfns prfms (zx0 ↕ zx1) ∝
  cast _ _ (prf_add_cancel_r prfns prfn1) 
    (prf_add_cancel_r prfms prfm1) zx0
  ↕ cast _ _ prfn1 prfm1 zx1.
Proof.
  pose proof (prf_add_cancel_r prfns prfn1).
  pose proof (prf_add_cancel_r prfms prfm1).
  subst; cbn; now rewrite !cast_id.
Qed.

(* FIXME: Move, to CastRules? Or maybe ComposeRules? *)
Lemma compose_simplify_casted {n m m' o} 
  (zx0 : ZX n m) (zx1 : ZX m o) (zx0' : ZX n m') (zx1' : ZX m' o) 
  (Hm : m = m') : 
  zx0 ∝ cast _ _ eq_refl Hm zx0' ->
  zx1 ∝ cast _ _ Hm eq_refl zx1' ->
  zx0 ⟷ zx1 ∝ zx0' ⟷ zx1'.
Proof.
  subst.
  now intros -> ->.
Qed.

Lemma compose_simplify_casted_abs {n m m' o : nat} 
  (zx0 : ZX n m) (zx1 : ZX m o) 
  (zx0' : ZX n m') (zx1' : ZX m' o) (Hm : m = m') : 
  (forall Hm', zx0 ∝ cast _ _ eq_refl Hm' zx0') ->
  (forall Hm', zx1 ∝ cast _ _ Hm' eq_refl zx1') ->
  zx0 ⟷ zx1 ∝ zx0' ⟷ zx1'.
Proof.
  subst.
  intros H H'.
  now rewrite (H eq_refl), (H' eq_refl).
Qed.


(* FIXME: Move *)
Lemma stack_empty_r_fwd {n m} (zx : ZX n m) : 
  zx ↕ ⦰ ∝
  cast _ _ (Nat.add_0_r _) (Nat.add_0_r _) zx.
Proof. apply stack_empty_r. Qed.
  
Lemma cast_stack_l_fwd {n0 m0 n0' m0' n1 m1} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfn prfm :
  cast n0' m0' prfn prfm zx0 ↕ zx1 ∝
  cast _ _ (f_equal (fun k => k + n1)%nat prfn)
    (f_equal (fun k => k + m1)%nat prfm)
    (zx0 ↕ zx1).
Proof. now subst. Qed.

Lemma cast_stack_r_fwd {n0 m0 n1 m1 n1' m1'} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfn prfm :
  zx0 ↕ cast n1' m1' prfn prfm zx1 ∝
  cast _ _ (f_equal (Nat.add n0) prfn)
    (f_equal (Nat.add m0) prfm)
    (zx0 ↕ zx1).
Proof. now subst. Qed.

(* FIXME: Move *)
Lemma stack_assoc_fwd {n0 n1 n2 m0 m1 m2} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2) :
  zx0 ↕ zx1 ↕ zx2 ∝ 
  cast _ _ (eq_sym (Nat.add_assoc _ _ _)) 
    (eq_sym (Nat.add_assoc _ _ _))
  (zx0 ↕ (zx1 ↕ zx2)).
Proof. apply stack_assoc. Qed.

Lemma stack_assoc_back_fwd {n0 n1 n2 m0 m1 m2} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2) :
  zx0 ↕ (zx1 ↕ zx2) ∝ 
  cast _ _ (Nat.add_assoc _ _ _)
    (Nat.add_assoc _ _ _)
  (zx0 ↕ zx1 ↕ zx2).
Proof. apply stack_assoc_back. Qed.


(* FIXME: Move *)
Lemma cast_compose_eq_mid_join n m o n' m' o' 
	(Hn : n' = n) (Hm Hm' : m' = m) (Ho : o' = o)
	(zx0 : ZX n m) (zx1 : ZX m o) : 
	cast n' m' Hn Hm zx0 ⟷ cast m' o' Hm' Ho zx1 =
	cast n' o' Hn Ho (zx0 ⟷ zx1).
Proof.
	subst.
	now rewrite (Peano_dec.UIP_nat _ _ Hm' eq_refl).
Qed.

Lemma cast_compose_l_eq_mid {n m o n'} (zx0 : ZX n m) (zx1 : ZX m o) 
  prfn prfm : 
  cast n' m prfn prfm zx0 ⟷ zx1 ∝
  cast n' o prfn eq_refl (zx0 ⟷ zx1).
Proof.
  subst.
  now rewrite cast_id.
Qed.

Lemma cast_compose_r_eq_mid {n m o o'} (zx0 : ZX n m) (zx1 : ZX m o) 
  prfm prfo : 
  zx0 ⟷ cast m o' prfm prfo zx1 ∝
  cast n o' eq_refl prfo (zx0 ⟷ zx1).
Proof.
  subst.
  now rewrite cast_id.
Qed.

Lemma cast_compose_distribute_l_eq_mid {n m o n'} (zx0 : ZX n m) (zx1 : ZX m o)
  prfn prfo : 
  cast n' o prfn prfo (zx0 ⟷ zx1) ∝
  cast n' m prfn eq_refl zx0 ⟷ zx1.
Proof.
  subst; now rewrite cast_id.
Qed.

Lemma cast_compose_distribute_r_eq_mid {n m o o'} (zx0 : ZX n m) (zx1 : ZX m o)
  prfn prfo : 
  cast n o' prfn prfo (zx0 ⟷ zx1) ∝
  zx0 ⟷ cast m o' eq_refl prfo zx1.
Proof.
  subst; now rewrite cast_id.
Qed.




(* FIXME: Move *)
Lemma prop_iff_simplify {n m} (zx0 zx1 zx0' zx1' : ZX n m) : 
  zx0 ∝ zx0' -> zx1 ∝ zx1' ->
  zx0 ∝ zx1 <-> zx0' ∝ zx1'.
Proof.
  now intros -> ->.
Qed.

Lemma prop_iff_simplify_casted {n m n' m'} (zx0 zx1 : ZX n m) 
  (zx0' zx1' : ZX n' m') prfn prfm : 
  zx0 ∝ cast _ _ prfn prfm zx0' -> zx1 ∝ cast _ _ prfn prfm zx1' ->
  zx0 ∝ zx1 <-> zx0' ∝ zx1'.
Proof.
  subst;
  now intros -> ->.
Qed.


Lemma n_stack1_to_n_stack k (zx : ZX 1 1) : 
  n_stack1 k zx ∝ 
  cast _ _ (eq_sym (Nat.mul_1_r _)) (eq_sym (Nat.mul_1_r _))
  (k ⇑ zx).
Proof.
  induction k; [cbn; now rewrite cast_id|].
  cbn.
  clean_eqns rewrite (@cast_stack_distribute 1 1 1 1).
  rewrite cast_id, IHk.
  apply stack_simplify; [reflexivity|].
  cast_irrelevance.
Qed.

Lemma compose_simplify_l {n m o} (zx0 zx1 : ZX n m) (zx2 : ZX m o) : 
  zx0 ∝ zx1 -> zx0 ⟷ zx2 ∝ zx1 ⟷ zx2.
Proof.
  now intros ->.
Qed.

Lemma compose_simplify_r {n m o} (zx0 : ZX n m) (zx1 zx2 : ZX m o) : 
  zx1 ∝ zx2 -> zx0 ⟷ zx1 ∝ zx0 ⟷ zx2.
Proof.
  now intros ->.
Qed.

Lemma stack_simplify_l {n0 m0 n1 m1} (zx0 : ZX n0 m0) (zx1 zx2 : ZX n1 m1) : 
  zx1 ∝ zx2 -> zx0 ↕ zx1 ∝ zx0 ↕ zx2.
Proof.
  now intros ->.
Qed.

Lemma stack_simplify_r {n0 m0 n1 m1} (zx0 zx1 : ZX n0 m0) (zx2 : ZX n1 m1) : 
  zx0 ∝ zx1 -> zx0 ↕ zx2 ∝ zx1 ↕ zx2.
Proof.
  now intros ->.
Qed.




(* FIXME: Move *)
Lemma Z_0_0_is_empty : 
  Z 0 0 0 ∝ ⦰.
Proof.
  prop_exists_nonzero (C2)%C.
  prep_matrix_equivalence.
  unfold scale.
  by_cell.
  rewrite Cexp_0.
  lca.
Qed.

Lemma X_0_0_is_empty : 
  X 0 0 0 ∝ ⦰.
Proof. colorswap_of (Z_0_0_is_empty). Qed.




Lemma compose_box_r {n} (zx0 zx1 : ZX n 1) : 
  zx0 ⟷ □ ∝ zx1 <-> zx0 ∝ zx1 ⟷ □.
Proof.
  split; [intros <- | intros ->]; 
  now rewrite ComposeRules.compose_assoc, box_compose, 
    wire_removal_r.
Qed.

Lemma compose_box_l {n} (zx0 zx1 : ZX 1 n) : 
  □ ⟷ zx0 ∝ zx1 <-> zx0 ∝ □ ⟷ zx1.
Proof.
  split; [intros <- | intros ->]; 
  now rewrite <- ComposeRules.compose_assoc, box_compose, 
    wire_removal_l.
Qed.

Lemma colorswap_is_bihadamard_1_1 (zx : ZX 1 1) : 
  ⊙ zx ∝ □ ⟷ zx ⟷ □.
Proof.
  rewrite colorswap_is_bihadamard.
  cbn. 
  clean_eqns rewrite stack_empty_r, cast_id.
  now rewrite ComposeRules.compose_assoc.
Qed.

Lemma box_decomp_ZXZ : Box ∝
  Z 1 1 (PI / 2) ⟷ X 1 1 (PI / 2) ⟷ Z 1 1 (PI / 2).
Proof.
  rewrite <- wire_removal_r, compose_box_l.
  change (X 1 1 (PI / 2)) with (⊙ (Z 1 1 (PI / 2))).
  rewrite colorswap_is_bihadamard_1_1.
  let zx := constr:(□ ⟷ Z 1 1 (PI / 2)) in
  transitivity (zx ⟷ zx ⟷ zx); [| now rewrite !ComposeRules.compose_assoc].
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


Definition zx_dummy n m : ZX n m :=
  Z n m 0.

Global Opaque zx_dummy.
