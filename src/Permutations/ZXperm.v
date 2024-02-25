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

Lemma zx_to_bot_helper : forall a n, 
  n = (n - a + Init.Nat.min a n)%nat.
Proof. intros a n; lia. Qed.

Definition zx_to_bot (a n : nat) : ZX n n :=
  cast _ _ (zx_to_bot_helper (n-a) n) (zx_to_bot_helper (n-a) n) 
  ((n_wire (n - (n-a))) ↕ a_swap (min (n-a) n)).

Lemma zx_to_bot'_helper a n (H : (a < n)%nat) :
  n = (a + (n - a))%nat.
Proof. lia. Qed.

Definition zx_to_bot' (a n : nat) (H : (a < n)%nat) : ZX n n :=
  cast _ _ (zx_to_bot'_helper a n H) (zx_to_bot'_helper a n H)
  (n_wire a ↕ a_swap (n-a)).

Fixpoint zx_of_swap_list (l : list nat) : ZX (length l) (length l) :=
	match l with 
	| [] as l => cast _ _ eq_refl eq_refl ⦰
	| a::l' => 
		zx_to_bot a (1+length l')
		⟷ (@cast (1+length l') (1+length l') (length l' + 1) (length l' + 1) 
			  (Nat.add_comm _ _) (Nat.add_comm _ _) (zx_of_swap_list l' ↕ —))
	end.

Definition zx_of_perm n f := zx_of_swap_list (insertion_sort_list n (perm_inv n f)).