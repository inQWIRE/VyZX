(* Require Import ZXCore.
Require Import CoreAutomation.
Require Import CoreRules.
Require Import CastRules.
Require Import PermutationAutomation.
Require Import PermutationFacts.


(*TODO: matrices? *)

Local Open Scope nat.

Definition rel := nat -> nat -> bool.

Fixpoint has_common_below n f g : bool :=
  match n with
  | 0 => false
  | S n' => (f n') && (g n') || has_common_below n' f g
  end.

Definition compose_rels n m o f g :=
  fun i j =>
    if (i <? n) then 
      if (j <? n) then f i j else
      if (j <? n + o) then has_common_below m (fun k => f i (n + k)) (fun k => (g k (m + (j - n))))
      else false
    else if (i <? n + o) then
      if (j <? n) then has_common_below m (fun k => f j (n + k)) (fun k => (g k (m + (i - n)))) else
      if (j <? n + o) then g (m + (i - n)) (m + (j - n))
      else false
    else false.

Notation rel_eq n f g := 
  (forall i j, i < n -> j < n -> f i j = g i j).

Definition stack_rels2 n0 m0 n1 m1 f g : rel :=
  fun i j => 
    if (i <? n0) then (
      (j <? n0) && (f i j) ||
      (n0 + n1 <=? j) && (j <? n0 + n1 + m0) && (f i (j - n1))
    ) else
    if (i <? n0 + n1) then (
      (n0 <=? j) && (j <? n0 + n1) && (g (i - n0) (j - n0)) ||
      (n0 + n1 + m0 <=? j) && (j <? n0 + n1 + m0 + m1) && (g (i - n0) (j - (n0 + m0)))
    ) else
    if (i <? n0 + n1 + m0) then (
      (j <? n0) && (f (i - n1) j) ||
      (n0 + n1 <=? j) && (j <? n0 + n1 + m0) && (f (i - n1) (j - n1))
    ) else
    if (i <? n0 + n1 + m0 + m1) then (
      (n0 <=? j) && (j <? n0 + n1) && (g (i - (n0 + m0)) (j - n0)) ||
      (n0 + n1 + m0 <=? j) && (j <? n0 + n1 + m0 + m1) && (g (i - (n0 + m0)) (j - (n0 + m0)))
    ) else false.

Fixpoint rel_of_zx {n m} (zx : ZX n m) : rel :=
  let conn i j a b := (i =? a) && (j =? b) || (i =? b) && (j =? a) in
  match zx with
  | ⦰ => fun i j => false
  | ⊂ => fun i j => conn i j 0 1
  | ⊃ => fun i j => conn i j 0 1
  | ⨉ => fun i j =>
    conn i j 0 2 || conn i j 1 3
  | — => fun i j => conn i j 0 1
  | □ => fun i j => conn i j 0 1
  | X_Spider n m _ => 
    fun i j => (i <? n) && (n <=? j) && (j <? n + m) 
      || (j <? n) && (n <=? i) && (i <? n + m)
  | Z_Spider n m _ => 
    fun i j => (i <? n) && (n <=? j) && (j <? n + m) 
      || (j <? n) && (n <=? i) && (i <? n + m)
  | @Stack n0 m0 n1 m1 zx0 zx1 => 
    let f := rel_of_zx zx0 in
    let g := rel_of_zx zx1 in (* Note this is backwards! *)
    stack_rels2 n1 m1 n0 m0 g f
  | @Compose n m o zx0 zx1 =>
    let f := rel_of_zx zx0 in
    let g := rel_of_zx zx1 in
    compose_rels n m o f g
  end.

Lemma stack_rels2_sym n0 m0 n1 m1 f g : (forall i j, f i j = f j i) ->
  (forall i j, g i j = g j i) -> forall i j, 
  stack_rels2 n0 m0 n1 m1 f g i j = stack_rels2 n0 m0 n1 m1 f g j i.
Proof.
  intros Hf Hg.
  intros i j.
  unfold stack_rels2.
  bdestructΩ'; simpl; rewrite 2?orb_false_r;
  rewrite 1?Hf, 1?Hg; easy.
Qed.

Lemma compose_rels_sym n m o f g : (forall i j, f i j = f j i) ->
  (forall i j, g i j = g j i) -> forall i j,
  compose_rels n m o f g i j = compose_rels n m o f g j i.
Proof.
  intros Hf Hg i j.
  unfold compose_rels.
  bdestructΩ'.
Qed.

Lemma has_common_below_iff m f g :
  has_common_below m f g = true <-> exists i, i < m /\ f i = true /\ g i = true.
Proof.
  induction m.
  simpl.
  - split; intros H; try discriminate H; try destruct H; lia.
  - simpl.
    split.
    + rewrite orb_true_iff, andb_true_iff.
      intros [[Hf Hg] | Hbelow].
      * exists m. repeat split; [lia|easy|easy].
      * rewrite IHm in Hbelow.
        destruct Hbelow as [i [? [? ?]]].
        exists i. repeat split; [lia|easy|easy].
    + intros [i [Hi [Hf Hg]]].
      bdestruct (i =? m).
      * subst; rewrite Hf, Hg; easy.
      * replace (has_common_below m f g) with true.
        rewrite orb_true_r; easy.
        symmetry.
        rewrite IHm.
        exists i. repeat split; [lia | easy | easy].
Qed.

Lemma rel_of_zx_sym {n m} (zx : ZX n m) : forall i j,
  rel_of_zx zx i j = rel_of_zx zx j i.
Proof.
  induction zx; simpl; auto with bool.
  1,2,4,5: intros i j; rewrite orb_comm; f_equal; rewrite andb_comm; easy.
  1: intros i j; f_equal; rewrite orb_comm; f_equal; rewrite andb_comm; easy.
  1: apply stack_rels2_sym; auto.
  1: apply compose_rels_sym; auto.
Qed.

Inductive ZXrel : forall n m, ZX n m -> Prop :=
  | RelEmpty : ZXrel 0 0 ⦰
  | RelCap : ZXrel 0 2 ⊂
  | RelCup : ZXrel 2 0 ⊃
  | RelSwap : ZXrel 2 2 ⨉
  | RelWire : ZXrel 1 1 —
  | RelStack {n0 m0 n1 m1 zx0 zx1} : 
    (ZXrel n0 m0 zx0) -> (ZXrel n1 m1 zx1) -> ZXrel (n0 + n1) (m0 + m1) (zx0 ↕ zx1)
  | RelComp {n m o zx0 zx1} : 
    (ZXrel n m zx0) -> (ZXrel m o zx1) -> ZXrel n o (zx0 ⟷ zx1).

Notation rel_surj n f :=
  (forall k, k < n -> exists k', k' < n /\ f k' k = true).

(* Notation rel_inj n f :=
  (forall k, k < n -> forall i j, i < n -> j < n -> 
  f k i = true -> f k j = true -> i = j). *)

Notation rel_inj n f :=
  (forall k, k < n -> forall i j, i < n -> j < n -> 
  f i k = true -> f j k = true -> i = j).

Fixpoint rel_inv_func n (f : rel) : nat -> nat :=
  fun k => 
    match n with
    | O => O
    | S n' => if f n' k then n' else rel_inv_func n' f k
    end.

Lemma rel_inv_func_bdd : forall n f i, 0 < n ->
  rel_inv_func n f i < n.
Proof.
  intros n f i Hn.
  destruct n; [easy|].
  clear Hn.
  induction n; simpl; [bdestructΩ'|].
  bdestruct_one; [lia|].
  transitivity (S n); [apply IHn | lia].
Qed.

Lemma rel_func_subrel_of_preim n f : 
  forall k,
  (exists k', k' < n /\ f k' k = true) ->
  f (rel_inv_func n f k) k = true.
Proof.
  intros k.
  induction n; intros [k' [Hk' Hfk'k]]; [easy|].
  simpl.
  destruct (f n k) eqn:E; [easy|].
  apply IHn.
  exists k'.
  split; [|easy].
  bdestruct (k' =? n); [subst|].
  - rewrite Hfk'k in E; easy.
  - lia.
Qed.

Lemma rel_fun_subrel_of_surj n f :
  rel_surj n f -> forall k, k < n -> f (rel_inv_func n f k) k = true.
Proof.
  intros H k Hk.
  apply rel_func_subrel_of_preim, H, Hk.
Qed.

Notation rel_permutation n f :=
  (rel_surj n f /\ rel_inj n f).

Lemma permutation_rel_eq n f : rel_permutation n f ->
  forall i j, i < n -> j < n ->
  f i j = (rel_inv_func n f j =? i).
Proof.
  intros [Hsurj Hinj] i j Hi Hj.
  apply eq_true_iff_eq.
  split.
  - intros Hfij.
    rewrite Nat.eqb_eq.
    apply (Hinj j); try easy.
    apply rel_inv_func_bdd; lia.
    rewrite rel_fun_subrel_of_surj; easy.
  - rewrite Nat.eqb_eq.
    intros; subst.
    rewrite rel_fun_subrel_of_surj; easy.
Qed.


(* Lemma test_rel_cap_cup :
  rel_of_zx (⊂ ⟷ \sups
  ) *)




(* Compute (⟦ — ↕ ⊂ ⟧ 3 0). *)
(* Compute (print_matrix swap). *)
(* Search ((_ -> bool) -> list _ -> bool). *)

Definition sem_of_rel n m (f : rel) : Matrix (2^m) (2^n) :=
  fun j i => if ((2^n <=? i) || (2^m <=? j)) then C0 else 
  if (
    forallb (fun k => ¬ ((if (k <? n) then Nat.testbit i k else Nat.testbit j (k - n)) ⊕ 
    let k' := (rel_inv_func (n + m) f k) in
    (if k' <? n then 
      Nat.testbit i k' else Nat.testbit j (k' - n))))
    (seq 0 (n + m))
  ) then C1 else C0.

Lemma WF_sem_of_rel : forall n m f,
  WF_Matrix (sem_of_rel n m f).
Proof.
  intros n m f i j.
  unfold sem_of_rel.
  intros [Hi | Hj]; bdestructΩ'.
Qed.

#[export] Hint Resolve WF_sem_of_rel : wf_db.

Lemma sem_of_rel_correct_test : 
  sem_of_rel 2 0 (rel_of_zx ⊃) = ⟦ ⊃ ⟧.
Proof.
  unfold sem_of_rel.
  (* apply mat_equiv_eq.
  1: apply WF_sem_of_rel.
  1: apply WF_ZX. *)
  crunch_matrix.
Qed.

Lemma divmod_1m0 : forall n m,
  Nat.divmod n 1 m 0 = (S n / 2 + m, n mod 2).
Proof.
  intros n.
  (* do 8 (try (destruct n; [simpl | ])). *)
  strong induction n; intros m.
  do 2 (destruct n; [simpl; solve_simple_mod_eqns|]).
  simpl Nat.divmod.
  rewrite H by lia.
  rewrite pair_equal_spec; split.
  - simpl. rewrite 2!H by lia. simpl.
    lia.
  - replace (S (S n)) with (n + 1 * 2) by lia.
    rewrite mod_add_n_r.
    easy.
Qed.

Lemma divmod_1m1 : forall n m,
  Nat.divmod n 1 m 1 = (n / 2 + m, (S n) mod 2).
Proof.
  strong induction n; intros m.
  do 2 (destruct n; [easy|]).
  simpl Nat.divmod.
  rewrite H by lia.
  rewrite pair_equal_spec.
  split.
  - simpl.
    rewrite 2!H by lia.
    simpl; lia.
  - replace (S (S (S n))) with (S n + 2) by lia.
    rewrite mod_add_n_r.
    easy.
Qed.

Lemma sem_of_rel_correct_test2 : 
  sem_of_rel 2 2  (rel_of_zx (— ↕ —)) = ⟦ — ↕ — ⟧.
Proof.
  unfold sem_of_rel.
  (* apply mat_equiv_eq.
  1: apply WF_sem_of_rel.
  1: apply WF_ZX. *)
  solve_matrix.
  bdestructΩ'; lca.
Qed.

Lemma test2 : ZXrel 1 3 (⊂ ↕ —).
Proof.
  apply (@RelStack 0 2 1 1); constructor.
Qed.

Ltac is_C0 x :=
  assert (x = C0) by lca.

Ltac is_C1 x :=
  assert (x = C1) by lca.

Ltac print_C x :=
  tryif is_C0 x then idtac "0" else
  tryif is_C1 x then idtac "1" else idtac "X".

Ltac print_LHS_mat :=
  intros;
   (let i := fresh "i" in
	let j := fresh "j" in
    let Hi := fresh "Hi" in
    let Hj := fresh "Hj" in
    intros i j Hi Hj; try solve_end;
     repeat
      (destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
        try solve_end); clear Hi;
     repeat
      (destruct j as [| j]; [  | apply <- Nat.succ_lt_mono in Hj ];
        try solve_end); clear Hj);
  match goal with |- ?x = ?y => simpl x end;
  match goal with
  | |- ?x = _ ?i ?j => idtac i; idtac j; print_C x; idtac ""
  end.

Ltac print_LHS_matU :=
  intros;
    (let i := fresh "i" in
  let j := fresh "j" in
    let Hi := fresh "Hi" in
    let Hj := fresh "Hj" in
    intros i j Hi Hj; try solve_end;
      repeat
      (destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
        try solve_end); clear Hi;
      repeat
      (destruct j as [| j]; [  | apply <- Nat.succ_lt_mono in Hj ];
        try solve_end); clear Hj);
  match goal with |- ?x = ?y ?i ?j => autounfold with U_db; simpl; 
    match goal with
    | |- ?x = _ => idtac i; idtac j; print_C x; idtac ""
    end
  end.

Definition zxrel_sem {n m} (zx : ZX n m) :=
  sem_of_rel n m (rel_of_zx zx).
Local Transparent zxrel_sem.

Local Notation sem_of_rel_correct zx :=
  (zxrel_sem zx = ⟦ zx ⟧).

Local Ltac uzxrel := unfold zxrel_sem, sem_of_rel, rel_of_zx.

Lemma test_swap_swap :
  sem_of_rel_correct (⨉ ⟷ ⨉).
Proof.
  uzxrel.
  crunch_matrix.
Qed.

Lemma test_2wire :
  sem_of_rel_correct ((— ↕ —)).
Proof.
  uzxrel; crunch_matrix.
  bdestructΩ'; lca.
Qed.

Lemma test_2wire_swap :
  sem_of_rel_correct ((— ↕ —) ⟷ ⨉).
Proof.
  unfold zxrel_sem, sem_of_rel, rel_of_zx; simpl.
  (* crunch_matrix. *)
  Admitted.




Lemma testcomposestack : 
  sem_of_rel 3 3 (rel_of_zx ((⨉ ↕ —) ⟷ (— ↕ ⨉))) = ⟦ (⨉ ↕ —) ⟷ (— ↕ ⨉) ⟧.
Proof.

  unfold sem_of_rel, rel_of_zx.
  crunch_matrix.
  Admitted.


Lemma test334 : 
sem_of_rel 1 3 (rel_of_zx ((⊂ ↕ —) ⟷ (— ↕ ⨉))) = ⟦ (⊂ ↕ —) ⟷ (— ↕ ⨉) ⟧.
Proof.
  unfold sem_of_rel, rel_of_zx.
  crunch_matrix.
Qed.

Lemma sem_of_rel_correct_test3 : 
  sem_of_rel 1 3 (rel_of_zx (⊂ ↕ —)) = ⟦ ⊂ ↕ — ⟧.
Proof.
  apply mat_equiv_eq; auto with wf_db; unfold sem_of_rel.
  print_LHS_mat.
  match goal with
  | |- ?x = _ ?i ?j => is_C1 x
  end.
  1: apply WF_sem_of_rel.
  1: apply WF_ZX.
  intros;
   (let i := fresh "i" in
	let j := fresh "j" in
    let Hi := fresh "Hi" in
    let Hj := fresh "Hj" in
    intros i j Hi Hj; try solve_end;
     repeat
      (destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
        try solve_end); clear Hi;
     repeat
      (destruct j as [| j]; [  | apply <- Nat.succ_lt_mono in Hj ];
        try solve_end); clear Hj).
  simpl. unfold kron; cbn. lca.
  simpl. unfold kron; cbn. lca.
  simpl. unfold kron; cbn. lca.
  simpl. unfold kron; cbn. lca.
  simpl. unfold kron; cbn. lca.
  simpl. unfold kron; cbn. lca.
  simpl. unfold kron; cbn. lca.
  simpl. unfold kron; cbn. lca.
  by_cell
  solve_matrix.
  Abort. 

Compute (rel_inv_func 3 (rel_of_zx (— ↕ ⊂)) 3).

Lemma sem_of_rel_correct_test4 : 
  sem_of_rel 1 3 (rel_of_zx (— ↕ ⊂)) = ⟦ — ↕ ⊂ ⟧.
Proof.
  unfold rel_of_zx.
  unfold sem_of_rel.
  simpl rel_inv_func.
  apply mat_equiv_eq.
  1: apply WF_sem_of_rel.
  1: apply WF_ZX.
  by_cell.
  all: unfold kron;
  simpl.
  
  
  Abort. 
(* 
  bdestructΩ'; lca.
Qed. *)


  (* simpl rel_of_zx.
  simpl rel_inv_func.
  Nat.testbit
  intros i j; setoid_rewrite orb_false_r; generalize j i.
  setoid_rewrite orb_false_r.
  by_cell.
  crunch_matrix.
  intros;
   (let i := fresh "i" in
	let j := fresh "j" in
    let Hi := fresh "Hi" in
    let Hj := fresh "Hj" in
    intros i j Hi Hj; try solve_end;
     repeat
      (destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
        try solve_end); clear Hi;
     repeat
      (destruct j as [| j]; [  | apply <- Nat.succ_lt_mono in Hj ];
        try solve_end); clear Hj).
  simpl seq.
  simpl forallb.
  cbn.
  Search "WF".
  crunch_matrix.

  (* fun i j => if ((2^n <=? i) || (2^m <=? j)) then C0 else 
  let bits := nat_to_binlist (j * 2^n + i) in
  forall k < n + m, l < n + m, 
  f k l -> 
  if (k <? n) then Nat.testbit k i else Nat.testbit j (k - n) =?
  if (l <? n) then Nat.testbit l i else Nat.testbit j (l - n)
  (* <-> *)
  forall k < n + m, 
  if (k <? n) then Nat.testbit k i else Nat.testbit j (k - n) =?
  if (rel_inv_func (n + m) f k <? n) then 
    Nat.testbit (rel_inv_func (n + m) f k) i else Nat.testbit j ((rel_inv_func (n + m) f k) - n)
  (* <-> *)
  forallb (fun k => if (k <? n) then Nat.testbit k i else Nat.testbit j (k - n) =?
  if (rel_inv_func (n + m) f k <? n) then 
    Nat.testbit (rel_inv_func (n + m) f k) i else Nat.testbit j ((rel_inv_func (n + m) f k) - n))
  seq 0 (n + m). *)




  (fun k => nth k bits false) = (fun k => nth (rel_inv_func (n + m) f k) )
    if (l <? n) then 
      Nat.testbit k i =? Nat.testbit l i
    else
      Nat.testbit k i =?
      (~~ f k l) || ()
  bits k = bits l
  .

Compute (⟦ ⊃ ⟧ 0 3).

Check (eval compute in ⟦ ⊂ ⟧). *)







(* Lemma rel_of_zx_WF {n m} (zx : ZX n m) : forall i j,
  i  *)

 *)
