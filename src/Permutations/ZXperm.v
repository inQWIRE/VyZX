Require Import CoreData.
Require Import PermutationDefinitions.

Open Scope ZX_scope.

(* @nocheck name *)
(* Allowing combination of Z and X; will check before push *)
Inductive ZXperm : forall n, ZX n n -> Prop :=
  | PermEmpty : ZXperm 0 Empty
  | PermWire : ZXperm 1 Wire
  | PermSwap : ZXperm 2 ⨉
  | PermStack {n0 n1 zx0 zx1} : 
      (ZXperm n0 zx0) -> (ZXperm n1 zx1) -> ZXperm _ (zx0 ↕ zx1)
  | PermComp {n zx0 zx1} : 
      (ZXperm n zx0) -> (ZXperm n zx1) -> ZXperm _ (zx0 ⟷ zx1).

(*
TODO: Bring this back here?
Definition stack_perms (n0 n1 : nat) (f g : nat -> nat) : nat -> nat :=
  fun n => if (n <? n0) then f n else 
           if (n <? n0 + n1) then (g (n - n0) + n0)%nat else n.
*)

Fixpoint perm_of_zx {n m} (zx : ZX n m) : (nat -> nat) :=
  let idn := (fun x : nat => x) in
    match zx with 
    | Empty => idn
    | Wire => idn
    | Swap => swap_2_perm
    | @Compose n m o zx0 zx1 =>
        ((perm_of_zx zx0) ∘ (perm_of_zx zx1))%prg
    | @Stack n0 m0 n1 m1 zx0 zx1 =>
        stack_perms n0 n1 (perm_of_zx zx0) (perm_of_zx zx1)
    (* Fake cases: *)
    | Cap => idn
    | Cup => idn
    | Box => idn
    | X_Spider _ _ _ => idn
    | Z_Spider _ _ _ => idn
    end.

Notation zxperm_to_matrix n zx := (perm_to_matrix n (perm_of_zx zx)).

Definition bottom_to_top_perm (n : nat) : nat -> nat :=
	fun k => if n <=? k then k else
        match k with
        | 0 => (n - 1)%nat
        | S k' => k'
        end.

Definition top_to_bottom_perm (n : nat) : nat -> nat :=
	fun k => if n <=? k then k else
	         if k =? (n-1) then 0%nat else (k + 1)%nat.

Definition a_perm (n : nat) : nat -> nat :=
  swap_perm 0 (n-1) n.
