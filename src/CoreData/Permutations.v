Require Import ZXCore.
(* Require Import StrongInduction. *)
(* Require Export QuantumLib.Quantum. *)
Require Export QuantumLib.Permutations.

Open Scope ZX_scope.

Inductive ZXPerm : forall n, ZX n n -> Prop :=
  | PermEmpty : ZXPerm 0 Empty
  | PermWire : ZXPerm 1 Wire
  | PermSwap : ZXPerm 2 ⨉
  | PermStack {n0 n1 zx0 zx1} : (ZXPerm n0 zx0) -> (ZXPerm n1 zx1) -> ZXPerm _ (zx0 ↕ zx1)
  | PermComp {n zx0 zx1} : (ZXPerm n zx0) -> (ZXPerm n zx1) -> ZXPerm _ (zx0 ⟷ zx1)
  | PermCast {n m zx} (_ : ZXPerm m zx) (h : n = m) : ZXPerm n (cast n n h h zx).

Definition swap_permutation : nat -> nat :=
  fun n => match n with
    | 0 => 1%nat
    | 1 => 0%nat
    | other => other
  end.

Definition stack_permutations (n0 n1 : nat) (f g : nat -> nat) : nat -> nat :=
  fun n => if (n <? n0) then f n else 
           if (n <? n0 + n1) then (g (n - n0) + n0)%nat else n.

Fixpoint perm_of_zx {n m} (zx : ZX n m) : (nat -> nat) :=
  let idn := (fun x : nat => x) in
    match zx with 
    | Empty => idn
    | Wire => idn
    | Swap => swap_permutation
    | @Compose n m o zx0 zx1 =>
        ((perm_of_zx zx0) ∘ (perm_of_zx zx1))%prg
    | @Stack n0 m0 n1 m1 zx0 zx1 =>
        stack_permutations n0 n1 (perm_of_zx zx0) (perm_of_zx zx1)
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

Definition rotr n m : nat -> nat :=
	fun k => if n <=? k then k else (k + m) mod n.

Definition rotl n m : nat -> nat :=
	fun k => if n <=? k then k else (k + (n - (m mod n))) mod n.
