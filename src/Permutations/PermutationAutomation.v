Require Export CoreData.ZXCore.
Require Export PermutationDefinitions.
Require Export QuantumLib.Permutations.
Require Export CoreRules.CoreAutomation.

(* TODOs: 
    - Declare databases
    - Remove all these random tactics; replace with the standard ones
*)

Tactic Notation "tryeasylia" :=
  try easy; try lia.

Ltac bdest_lia_replace b0 b1 :=
  replace b0 with b1 by (bdestruct b0; lia).

Ltac show_permutation :=
  repeat first [
    split
  | simpl; solve [auto with perm_db]
  | subst; solve [auto with perm_db]
  | auto with perm_db
  | solve [eauto using permutation_compose with perm_db]
  | easy
  | lia
  ].

Ltac enumerate_value i :=
  destruct i; [|tryif lia then idtac else enumerate_value i].

Ltac enumerate_matrix Hi Hj :=
  match type of Hi with (?i < ?n)%nat =>
  match type of Hj with (?j < ?m)%nat => 
  enumerate_value i; enumerate_value j
  (* repeat first [destruct i; destruct j; try lia] *)
  end end.

  (* by_cell *)

Ltac check_finite_matrix :=
  apply mat_equiv_eq;
  try auto with wf_db;
  intros i j Hi Hj; simpl in *;
  enumerate_matrix Hi Hj;
  try lia;
  try easy.

  (* solve_matrix *)

  

Ltac bdestshoweq := (* goal of form b0 = b1, bools *)
  match goal with 
  | |- ?b0 = ?b1 =>
    bdestruct b0; bdestruct b1; auto; try easy; lia
  end.

Ltac fail_if_iffy H :=
  match H with
  | context[if _ then _ else _] => fail 1
  | _ => idtac
  end.

Ltac destruct_if :=
  match goal with
  | [ |- context[if ?b then _ else _]] 
      => fail_if_iffy b; bdestruct b
  end.

Ltac destruct_if_solve :=
  repeat (destruct_if; subst; tryeasylia);
  tryeasylia.

(* From: http://adam.chlipala.net/cpdt/html/Match.html *)

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.

(* Also from above source *)
Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

Ltac add_mod_bound a n :=
  let Han := fresh "Han" in assert(Han : a mod n < n)
    by solve [apply Nat.mod_upper_bound; tryeasylia]; extend (Han).

Ltac destruct_if_solve_mods :=
  repeat (destruct_if; subst; tryeasylia);
  repeat match goal with
    | [ _ : context[?a mod ?n] |- _] => add_mod_bound a n
    | [ |- context[?a mod ?n]] => add_mod_bound a n
    end;
  tryeasylia.



Ltac apply_f H k :=
  unfold compose in H;
  apply (f_equal (fun x => x k)) in H.


Lemma is_inv_iff_inv_is n f finv :
  (forall k, k < n -> finv k < n /\ f k < n /\ f (finv k) = k /\ finv (f k) = k)%nat
  <-> (forall k, k < n -> f k < n /\ finv k < n /\ finv (f k) = k /\ f (finv k) = k)%nat.
Proof.
  split; intros H k Hk; specialize (H k Hk); easy.
Qed.


#[export] Hint Rewrite is_inv_iff_inv_is : perm_inv_db.

(* Tactic Notation "cleanup_perm_inv" := 
  auto_cast_eqn (autorewrite with perm_inv_db).

Tactic Notation "cleanup_perm" :=
  auto_cast_eqn (autorewrite with perm_inv_db perm_cleanup_db).

Tactic Notation "cleanup_perm_of_zx" :=
  auto_cast_eqn (autorewrite with perm_of_zx_cleanup_db perm_inv_db perm_cleanup_db). *)


Tactic Notation "cleanup_perm_inv" := 
  autorewrite with perm_inv_db.

Tactic Notation "cleanup_perm" :=
  autorewrite with perm_inv_db perm_cleanup_db.

Tactic Notation "cleanup_perm_of_zx" :=
  autorewrite with perm_of_zx_cleanup_db perm_inv_db perm_cleanup_db.

Lemma compose_id_of_compose_idn {f g : nat -> nat} 
  (H : (f ∘ g)%prg = (fun n => n)) {k : nat} : f (g k) = k.
Proof.
  apply_f H k.
  easy.
Qed.

Ltac perm_by_inverse finv :=
  exists finv;
  intros k Hk; repeat split;
  only 3,4 : (try apply compose_id_of_compose_idn; cleanup_perm; tryeasylia) 
            || cleanup_perm; tryeasylia;
  only 1,2 : auto with perm_bdd_db; tryeasylia.




Ltac solve_stack_perm n0 n1 :=
  apply functional_extensionality; intros k;
  unfold stack_perms;
  bdestruct (k <? n0)%nat; [tryeasylia|];
  try bdestruct (k <? n0 + n1)%nat; tryeasylia.
  
Ltac solve_stack_perm_strong n0 n1 :=
  unfold stack_perms; 
  apply functional_extensionality; intros k;
  bdestruct (k <? n0)%nat; [tryeasylia | ]; try bdestruct (k <? n0 + n1);
  destruct_if_solve.
(* ^ REPLACED BY: solve_stack_perm; destruct_if_solve *)


(* TODO: Figure out order of operations on where to put this vs its lemma *)
(* Ltac by_inverse_injective f n :=
  apply (WF_permutation_inverse_injective f n); [
    tryeasylia; auto with perm_db |
    tryeasylia; auto with perm_WF_db |
    try solve [cleanup_perm; auto] |
    try solve [cleanup_perm; auto]]; tryeasylia. *)

