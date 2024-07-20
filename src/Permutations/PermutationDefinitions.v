Require Export QuantumLib.Permutations.
Require Import CoreData.ZXCore.

Declare Scope perm_scope.
Delimit Scope perm_scope with perm.

Section PermutationDefinitions.

Local Open Scope nat_scope.

Definition stack_perms (n0 n1 : nat) (f g : nat -> nat) : nat -> nat :=
  fun n => 
  if (n <? n0) then f n else 
  if (n <? n0 + n1) then (g (n - n0) + n0)%nat else n.

Definition tensor_perms (n0 n1 : nat) (f g : nat -> nat) : nat -> nat :=
  fun n => if (n0 * n1 <=? n) then n else
  (f (n / n1) * n1 + g (n mod n1)).

Definition swap_perm a b n := 
  fun k => if n <=? k then k else 
  if k =? a then b else
  if k =? b then a else k.


(* TODO: Implement things for this *)
Fixpoint insertion_sort_list n f := 
  match n with 
  | 0 => []
  | S n' => let k := (perm_inv (S n') f n') in
      k :: insertion_sort_list n' (Bits.fswap f k n')
  end.

Fixpoint swap_list_spec l : bool :=
  match l with 
  | [] => true
  | k :: ks => (k <? S (length ks)) && swap_list_spec ks
  end.

Fixpoint perm_of_swap_list l :=
  match l with
  | [] => idn
  | k :: ks => let n := length ks in
    (swap_perm k n (S n) ∘ (perm_of_swap_list ks))%prg
  end.

Fixpoint invperm_of_swap_list l :=
  match l with 
  | [] => idn
  | k :: ks => let n := length ks in
    ((invperm_of_swap_list ks) ∘ swap_perm k n (S n))%prg
  end.

Definition perm_inv' n f :=
  fun k => if n <=? k then k else perm_inv n f k.

Definition contract_perm f a :=
  fun k => 
  if k <? a then 
    if f k <? f a then f k else f k - 1
  else
    if f (k + 1) <? f a then f (k + 1) else f (k + 1) - 1.

Definition swap_2_perm : nat -> nat :=
  swap_perm 0 1 2.

Definition rotr n m : nat -> nat :=
	fun k => if n <=? k then k else (k + m) mod n.

Definition rotl n m : nat -> nat :=
	fun k => if n <=? k then k else (k + (n - (m mod n))) mod n.

Definition swap_block_perm padl padm a :=
  fun k => 
  if k <? padl then k else
  if k <? padl + a then k + (a + padm) else
  if k <? padl + a + padm then k else
  if k <? padl + a + padm + a then k - (a + padm) else
  k.

Definition reflect_perm n := 
  fun k => 
  if n <=? k then k else n - S k.

End PermutationDefinitions.

(* Notation "f '=[' n  ']' g" := (perm_eq_upto n f g) 
  (at level 70, no associativity): perm_scope. 

Notation "'perm_bdd' n f" := (forall k, (k < n%nat)%nat -> (f k < n%nat)%nat) 
  (at level 10, n at level 9, f at level 9) : perm_scope. *)
