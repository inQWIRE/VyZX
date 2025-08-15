Require Import ZXCore Swaps.
Require Import QuantumLib.Permutations.

Open Scope ZX_scope.

(* @nocheck name *)
(* Allowing combination of Z and X; will check before push *)
Inductive ZXperm : forall {n m}, ZX n m -> Prop :=
  | PermEmpty : ZXperm Empty
  | PermWire : ZXperm Wire
  | PermSwap : ZXperm ⨉
  | PermStack {n0 m0 n1 m1} (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) : 
      ZXperm zx0 -> ZXperm zx1 -> 
      ZXperm (zx0 ↕ zx1)
  | PermComp {n m o} (zx0 : ZX n m) (zx1 : ZX m o) : 
      ZXperm zx0 -> ZXperm zx1 -> 
      ZXperm (zx0 ⟷ zx1).



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

Lemma zx_to_bot_pf : forall a n, 
  n = (n - a + Init.Nat.min a n)%nat.
Proof. intros a n; lia. Qed.

Definition zx_to_bot (a n : nat) : ZX n n :=
  cast _ _ (zx_to_bot_pf (n-a) n) (zx_to_bot_pf (n-a) n) 
  ((n_wire (n - (n-a))) ↕ a_swap (min (n-a) n)).

Lemma zx_to_bot'_pf a n (H : (a < n)%nat) :
  n = (a + (n - a))%nat.
Proof. lia. Qed.

Definition zx_to_bot' (a n : nat) (H : (a < n)%nat) : ZX n n :=
  cast _ _ (zx_to_bot'_pf a n H) (zx_to_bot'_pf a n H)
  (n_wire a ↕ a_swap (n-a)).

Fixpoint zx_of_swap_list (l : list nat) : ZX (length l) (length l) :=
	match l with 
	| [] as l => cast _ _ eq_refl eq_refl ⦰
	| a::l' => 
		zx_to_bot a (1+length l')
		⟷ (@cast (1+length l') (1+length l') (length l' + 1) (length l' + 1) 
			  (Nat.add_comm _ _) (Nat.add_comm _ _) (zx_of_swap_list l' ↕ —))
	end.

Definition zx_of_perm_uncast n f := 
  zx_of_swap_list (insertion_sort_list n (perm_inv n f)).

(* Need to prove facts about insertion_sort_list first, but in essence:

Definition zx_of_perm n f :=
    $ n, n ::: zx_of_perm_uncast n f $ *)


(* Now that we have facts about insertion_sort_list, we can define: *)

Definition zx_of_perm n f :=
	cast n n 
		(eq_sym (length_insertion_sort_list n (perm_inv n f))) 
		(eq_sym (length_insertion_sort_list n (perm_inv n f)))
	(zx_of_perm_uncast n f).

(* Though redundant with cast, this makes for much better
	 proof statements, e.g. with compose_zx_of_perm_cast. 
	 Since many of our ZXperms are non-square, this is 
	 a common application. *)
Definition zx_of_perm_cast n m f (H : n = m) : ZX n m :=
	cast n m eq_refl (eq_sym H) (zx_of_perm n f).

Arguments zx_of_perm_cast : simpl never.

Notation "'zx_of_perm_cast' n m f '$'" :=
		(zx_of_perm_cast n m f _) 
		(at level 10, n at level 9, m at level 9, f at level 9, 
		only printing) : ZX_scope.


Definition zx_comm p q : (ZX (p + q) (q + p)) :=
	zx_of_perm_cast (p + q) (q + p) (big_swap_perm q p) (Nat.add_comm p q).

Arguments zx_comm : simpl never.


Definition zx_gap_comm p m q : (ZX (p + m + q) (q + m + p)) :=
	cast _ _ eq_refl (eq_sym (Nat.add_assoc _ _ _))
	(zx_comm (p + m) q ⟷ (n_wire q ↕ zx_comm p m)).

Arguments zx_gap_comm : simpl never.


Lemma zx_mid_comm_prf {a b c d : nat} : 
  (a + b + (c + d) = a + (b + c) + d)%nat.
Proof. lia. Qed.
Definition zx_mid_comm n0 n1 m0 m1 : 
  ZX (n0 + n1 + (m0 + m1)) (n0 + m0 + (n1 + m1)) :=
  (cast _ _ zx_mid_comm_prf zx_mid_comm_prf
  (n_wire _ ↕ zx_comm n1 m0 ↕ n_wire m1)).