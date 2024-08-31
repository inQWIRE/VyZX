Require Import ZXCore.
Require CastRules ComposeRules.
Require Export ZXperm.

Create HintDb perm_of_zx_cleanup_db.
Create HintDb zxperm_db.
#[export] Hint Constructors ZXperm : zxperm_db.

Ltac cleanup_perm_of_zx :=
  autounfold with zxperm_db;
  autorewrite with perm_of_zx_cleanup_db perm_inv_db perm_cleanup_db;
  auto with perm_of_zx_cleanup_db perm_inv_db perm_cleanup_db
    perm_db perm_bounded_db WF_Perm_db.

(* Hack to get auto to apply PermStack where it obviously should 
  (like to ZXperm (S n) (— ↕ zx), where zx : ZX n n; it doesn't work 
  here because apply doesn't see that S n = 1 + n, but if we tell it
  to look for 1 + n, it will find S n). *)
Ltac __cleanup_stack_perm zx0 zx1 :=
  match type of zx0 with ZX ?n0 ?n0 =>
  match type of zx1 with ZX ?n1 ?n1 =>
  apply (PermStack (n0:=n0) (n1:=n1))
  end end.

#[export] Hint Extern 0 (ZXperm (?zx0 ↕ ?zx1)) => 
  __cleanup_stack_perm zx0 zx1 : zxperm_db.

#[export] Hint Extern 0 (ZXperm (@Stack ?n0 ?m0 ?n1 ?m1 ?zx0 ?zx1)) => 
  apply (@PermStack n0 m0 n1 m1 zx0 zx1) : zxperm_db.


(* Making proportional_of_eq_perm usable, mostly through a series of tactics to
   deal with the absolute nightmare that is definitional equality casts. *)
Lemma prop_iff_double_cast : forall {n0 m0} n1 m1 (zx0 zx1 : ZX n0 m0) 
  (prfn: n1 = n0) (prfm : m1 = m0),
  Proportional.proportional zx0 zx1 <-> 
  Proportional.proportional (cast n1 m1 prfn prfm zx0) (cast _ _ prfn prfm zx1).
Proof.
  intros.
  subst.
  reflexivity.
Qed.

(* Ltac __cast_prop_sides_to_square :=
  match goal with
  | |- Proportional.proportional ?zx0 ?zx1 =>
    match type of zx0 with 
    | ZX ?n ?n => idtac
    | ZX ?n ?m => 
      let Hm0n := fresh "Hm0n" in 
      assert (Hm0n : n = m) by lia;
      rewrite (prop_iff_double_cast n n zx0 zx1 (eq_refl) (Hm0n))
    end
  end. *)

Lemma cast_compose_eq : forall n0 n1 m o0 o1 (zx0 : ZX n0 m) (zx1 : ZX m o0) Hn0n1 Ho0o1,
  cast n1 o1 Hn0n1 Ho0o1 (zx0 ⟷ zx1) = 
  (cast n1 m Hn0n1 (@eq_refl _ m) zx0) ⟷ (cast m o1 (@eq_refl _ m) Ho0o1 zx1).
Proof.
  intros.
  subst.
  reflexivity.
Qed.

Lemma cast_cast_eq : forall n0 m0 n1 m1 n2 m2 (zx : ZX n0 m0) Hn0n1 Hm0m1 Hn1n2 Hm1m2,
  let Hn0n2 := eq_trans Hn1n2 Hn0n1 in
  let Hm0m2 := eq_trans Hm1m2 Hm0m1 in
  cast n2 m2 Hn1n2 Hm1m2 (cast n1 m1 Hn0n1 Hm0m1 zx) =
  cast n2 m2 Hn0n2 Hm0m2 zx.
Proof.
  intros; subst.
  reflexivity.
Qed.

Lemma cast_id_eq : forall n m (prfn : n = n) (prfm : m = m) zx,
  cast n m prfn prfm zx = zx.
Proof.
  intros; subst.
  rewrite (Eqdep_dec.UIP_refl_nat n prfn). (* Replace prfn with (@eq_refl nat n) *)
  rewrite (Eqdep_dec.UIP_refl_nat m prfm). (* Replace prfn with (@eq_refl nat m) *)
  reflexivity.
Qed.

Lemma zxperm_iff_cast' n m n' m' 
  (zx : ZX n m) (Hn : n' = n) (Hm : m' = m) :
  ZXperm (cast n' m' Hn Hm zx) <-> ZXperm zx.
Proof.
  intros.
  now subst.
Qed.

#[export] Hint Resolve <- zxperm_iff_cast' : zxperm_db.

Ltac simpl_permlike_zx :=
  let simpl_casts_eq := first [
    rewrite cast_id_eq |
    rewrite cast_cast_eq ]
  in
  repeat (match goal with
  | |- context[?zx ⟷ cast ?m' ?o' ?prfm ?prfo (n_wire ?o)] =>
    rewrite (@CastRules.cast_compose_r _ _ _ _ _ prfm prfo zx _);
    rewrite (@ComposeRules.nwire_removal_r o)
  | |- context[cast ?n' ?m' ?prfn ?prfm (n_wire ?n) ⟷ ?zx] =>
    rewrite (@CastRules.cast_compose_l _ _ _ _ _ prfn prfm _ zx);
    rewrite (@ComposeRules.nwire_removal_l n)
  | |- context[@cast ?n' ?m' ?n ?m ?prfn ?prfm ?zx ⟷ cast ?m' ?o' ?prfom ?prfo (n_wire ?o)] =>
    rewrite (@CastRules.cast_compose_l n n' m m' o' prfn prfm zx (cast m' o' prfom prfo (n_wire o)));
    rewrite (cast_cast_eq _ _ _ _ _ _ (n_wire o));
    try rewrite (cast_id_eq _ _ _ _ (zx ⟷ _))
  | |- context[cast ?n ?m' ?prfn ?prfmn (n_wire ?n') ⟷ @cast ?m' ?o' ?m ?o ?prfm ?prfo ?zx] =>
    rewrite (@CastRules.cast_compose_r n m m' o o' prfm prfo (cast n m prfn prfmn (n_wire n')) zx);
    rewrite (cast_cast_eq _ _ _ _ _ _ (n_wire n'));
    try rewrite (cast_id_eq _ _ _ _ (zx ⟷ _))
  | |- context[cast ?n1 ?m _ _ ?zx0 ⟷ cast ?m ?o1 _ _ ?zx1] =>
    rewrite <- (cast_compose_eq _ n1 m _ o1 zx0 zx1)
  | |- context[ @cast ?n1 ?m1 ?n0 ?m0 ?prfn0 ?prfm0 ?zx0 ⟷ cast ?m1 ?o1 ?prfm1 ?prfo1 ?zx1 ] => 
    rewrite (CastRules.cast_compose_mid m0 (eq_sym prfm0) (eq_sym prfm0) (cast n1 m1 prfn0 prfm0 zx0) (cast m1 o1 prfm1 prfo1 zx1));
    rewrite
      (cast_cast_eq _ _ _ _ _ _ zx0), (cast_cast_eq _ _ _ _ _ _ zx1),
      (cast_id_eq _ _ _ _ zx0)
  end; repeat simpl_casts_eq) 
  || (repeat simpl_casts_eq).

#[export] Hint Extern 2 => 
  (repeat first [rewrite cast_id_eq | rewrite cast_cast_eq]) : zxperm_db.

Ltac __one_round_cleanup_zxperm_of_cast :=
  match goal with
  | |- ZXperm _ (cast ?n2 ?m2 ?Hn1n2 ?Hm1m2 (@cast ?n1 ?m1 ?n0 ?m0 ?Hn0n1 ?Hm0m1 ?zx)) => (* idtac "clean_cast_cast"; *)
    rewrite (cast_cast_eq n0 m0 n1 m1 n2 m2 zx Hn0n1 Hm0m1 Hn1n2 Hm1m2)
  | |- ZXperm ?n (@cast ?n ?n ?n ?n _ _ ?zx) => (* idtac "clean_id";  *)
    rewrite (cast_id_eq n n _ _ zx)
  | |- ZXperm ?n (@cast ?n ?n ?n' ?m' _ _ (?zx0 ⟷ ?zx1)) => (* idtac "clean_comp"; *)
    rewrite (cast_compose_eq _ _ _ _ _ zx0 zx1) by lia; 
    apply PermComp
  | |- ZXperm ?n (@cast ?n ?n ?n' ?m' _ _ (?zx0 ↕ ?zx1)) => (* idtac "clean_stack"; *)
    match type of zx0 with ZX ?n0 ?n0 =>
    match type of zx1 with ZX ?n1 ?n1 =>
      rewrite <- (zxperm_iff_cast' (n) (n0 + n1) (ltac:(lia)) (ltac:(lia)))
    end end
  end.

(* #[export] Hint Extern 3 (ZXperm (cast _ _ _ _ _)) => __one_round_cleanup_zxperm_of_cast : zxperm_db. *)

(* Lemma perm_of_cast_compose_each_square : forall n m a b c d
  (zx0 : ZX n n) (zx1 : ZX m m) prfa0 prfb0 prfb1 prfc1 prfd1 prfd2,
  ZXperm n zx0 -> ZXperm m zx1 ->
  ZXperm d (cast d d prfd1 prfd2 
  (cast a b prfa0 prfb0 zx0 ⟷ cast b c prfb1 prfc1 zx1)).
Proof.
  intros.
  subst.
  auto with zxperm_db.
Qed.

#[export] Hint Resolve perm_of_cast_compose_each_square : zxperm_db. *)

(* I don't know if these actually ever help: *)
(* Lemma perm_of_cast_compose_each_square_l : forall n m c d
  (zx0 : ZX n n) (zx1 : ZX m m) prfb1 prfc1 prfd1 prfd2,
  ZXperm n zx0 -> ZXperm m zx1 ->
  ZXperm d (cast d d prfd1 prfd2 
  (zx0 ⟷ cast n c prfb1 prfc1 zx1)).
Proof.
  intros.
  subst.
  auto with zxperm_db.
Qed.

Lemma perm_of_cast_compose_each_square_r : forall n m a d
  (zx0 : ZX n n) (zx1 : ZX m m) prfa0 prfm0 prfd1 prfd2,
  ZXperm n zx0 -> ZXperm m zx1 ->
  ZXperm d (cast d d prfd1 prfd2 
  (cast a m prfa0 prfm0 zx0 ⟷ zx1)).
Proof.
  intros.
  subst.
  auto with zxperm_db.
Qed. *)


(* #[export] Hint Resolve perm_of_cast_compose_each_square_l
    perm_of_cast_compose_each_square_r : zxperm_db. *)


(* This can't be here because proportional_of_eq_perm is defined later, but keeping 
   for reference. (This is put in ZXpermSemantics, right after proportional_of_eq_perm.) *)

(*
Ltac prop_perm_eq :=
  intros;
  simpl_casts;
  simpl_permlike_zx;
  __cast_prop_sides_to_square;
  (* Goal: zx0 ∝ zx1 *)
  apply proportional_of_eq_perm; [
  (* New goals: *)
    (*1: ZXperm _ zx0 *) auto with zxperm_db |
    (*2: ZXperm _ zx1*) auto with zxperm_db |
    (*3: perm_of_zx zx0 = perm_of_zx zx1*) cleanup_perm_of_zx; try easy; try lia
  ].
*)


(* For VyZX lemmas which create a ton of shelved goals, this solves 
   them immediately (and ensures they *are* solvable,
   unlike auto_cast_eqn) *)
Tactic Notation "clean_eqns" tactic(tac) :=
  unshelve (tac); [reflexivity + lia..|].

Ltac print_hyps :=
  try (match reverse goal with | H : ?p |- _ => idtac H ":" p; fail end).

Ltac print_goal := 
  match reverse goal with |- ?P => idtac P; idtac "" end.

Ltac print_state :=
  print_hyps;
  idtac "---------------------------------------------------------";
  print_goal.

(* TODO: Move to QuantumLib *)
Ltac by_perm_cell :=
  let i := fresh "i" in
  let Hi := fresh "Hi" in
  intros i Hi; try solve_end;
   repeat
	(destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
      try solve_end).

Arguments Nat.leb !_ !_ /.

(* FIXME: Move to Qlib *)
Ltac auto_perm_to n := 
  auto n with perm_db perm_bounded_db WF_Perm_db perm_inv_db.

Ltac auto_perm := 
  auto 6 with perm_db perm_bounded_db WF_Perm_db perm_inv_db.

Tactic Notation "auto_perm" int_or_var(n) :=
  auto_perm_to n.

Tactic Notation "auto_perm" :=
  auto_perm 6.

Ltac auto_zxperm_to n :=
  auto n with zxperm_db perm_db perm_bounded_db WF_Perm_db perm_inv_db.

Ltac auto_zxperm n :=
  auto 6 with zxperm_db perm_db perm_bounded_db WF_Perm_db perm_inv_db.

Tactic Notation "auto_zxperm" int_or_var(n) :=
  auto_zxperm_to n.

Tactic Notation "auto_zxperm" :=
  auto_zxperm 6.
