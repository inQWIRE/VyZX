Require Export QuantumLib.Permutations.
Require Import CoreData.ZXCore.

Notation idn := (fun (k : nat) => k).

Fixpoint perm_inv n f : nat -> nat :=
  fun k => match n with
  | 0 => 0%nat
  | S n' => if f n' =? k then n'%nat else perm_inv n' f k
  end.

Definition stack_perms (n0 n1 : nat) (f g : nat -> nat) : nat -> nat :=
  fun n => 
  if (n <? n0) then f n else 
  if (n <? n0 + n1) then (g (n - n0) + n0)%nat else n.

Definition swap_2_perm : nat -> nat :=
  fun n => if 2 <=? n then n else match n with
    | 0 => 1%nat
    | 1 => 0%nat
    | other => other
  end.

(* TODO: Combine the above and this? *)
Definition swap_perm a b n := 
  fun k => if n <=? k then k else 
  if k =? a then b else
  if k =? b then a else k.

Definition rotr n m : nat -> nat :=
	fun k => if n <=? k then k else (k + m) mod n.

Definition rotl n m : nat -> nat :=
	fun k => if n <=? k then k else (k + (n - (m mod n))) mod n.

(* TODO: Refactor all with perm_WF *)
Notation perm_WF n f := (forall k:nat, (n <= k)%nat -> f k = k).

(* TODO: Implement things for this *)
Fixpoint insertion_sort_list n f := 
  match n with 
  | 0 => []
  | S n' => let k := (perm_inv (S n') f n') in
      k :: insertion_sort_list n' (fswap f k n')
  end.