Require Export ZXCore.
Require Export PermutationDefinitions.
Require Export QuantumLib.Permutations.
Require Export CoreRules.CoreAutomation.
Require Export ZXperm.

(* TODOs: 
    - Declare databases
    - Remove all these random tactics; replace with the standard ones
      + partially done! Should check
    - Add cleanup_zx_eq for strict equality
*)

Create HintDb perm_db.
Create HintDb perm_bdd_db.
Create HintDb perm_inv_db.
Create HintDb WF_perm_db.

(* Create HintDb perm_cleanup_db.
Create HintDb perm_of_zx_cleanup_db. *)

Create HintDb zxperm_db.
#[export] Hint Constructors ZXperm : zxperm_db.

(* TODO: Once quantumlib's up, put these things here: *)
(* Create HintDb WF_perm_db. *)
(* #[export] Hint Resolve monotonic_WF_perm compose_WF_perm : WF_perm_db. *)


(* Tactic Notation "tryeasylia" :=
  try easy; try lia. *)



Ltac replace_bool_lia b0 b1 :=
  first [
    replace b0 with b1 by (bdestruct b0; lia || (destruct b1 eqn:?; lia)) |
    replace b0 with b1 by (bdestruct b1; lia || (destruct b0 eqn:?; lia)) |
    replace b0 with b1 by (bdestruct b0; bdestruct b1; lia)
  ].

Ltac show_permutation :=
  repeat first [
    split
  | simpl; solve [auto with perm_db]
  | subst; solve [auto with perm_db]
  | solve [eauto using permutation_compose with perm_db]
  | easy
  | lia
  ].



Ltac bdestruct_one :=
  let fail_if_iffy H :=
    match H with
    | context[if _ then _ else _] => fail 1
    | _ => idtac
    end
  in
  match goal with
  | |- context [ ?a <? ?b ] => fail_if_iffy a; fail_if_iffy b; bdestruct (a <? b)
  | |- context [ ?a <=? ?b ] => fail_if_iffy a; fail_if_iffy b; bdestruct (a <=? b)
  | |- context [ ?a =? ?b ] => fail_if_iffy a; fail_if_iffy b; bdestruct (a =? b)
  | |- context[if ?b then _ else _]
      => fail_if_iffy b; destruct b eqn:?
  end.


Ltac bdestructΩ' :=
  let tryeasylia := try easy; try lia in 
  repeat (bdestruct_one; subst; tryeasylia);
  tryeasylia.

(* From: http://adam.chlipala.net/cpdt/html/Match.html

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
    notHyp t; generalize pf; intro. *)

(* Ltac add_mod_bound a n :=
  let Han := fresh "Han" in assert(Han : a mod n < n)
    by solve [apply Nat.mod_upper_bound; tryeasylia]; extend (Han). *)

(* Ltac bdestructΩ'_mods :=
  repeat (bdestruct_one; subst; tryeasylia);
  repeat match goal with
    | [ _ : context[?a mod ?n] |- _] => add_mod_bound a n
    | [ |- context[?a mod ?n]] => add_mod_bound a n
    end;
  tryeasylia. *)



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
  autounfold with zxperm_db;
  autorewrite with perm_of_zx_cleanup_db perm_inv_db perm_cleanup_db.

Lemma compose_id_of_compose_idn {f g : nat -> nat} 
  (H : (f ∘ g)%prg = (fun n => n)) {k : nat} : f (g k) = k.
Proof.
  apply (f_equal_inv k) in H.
  easy.
Qed.

Ltac perm_by_inverse finv :=
  let tryeasylia := try easy; try lia in 
  exists finv;
  intros k Hk; repeat split;
  only 3,4 : (try apply compose_id_of_compose_idn; cleanup_perm; tryeasylia) 
            || cleanup_perm; tryeasylia;
  only 1,2 : auto with perm_bdd_db; tryeasylia.




Ltac solve_stack_perm n0 n1 :=
  let tryeasylia := try easy; try lia in 
  apply functional_extensionality; intros k;
  unfold stack_perms;
  bdestruct (k <? n0)%nat; [tryeasylia|];
  try bdestruct (k <? n0 + n1)%nat; tryeasylia.
  
Ltac solve_stack_perm_strong n0 n1 :=
  let tryeasylia := try easy; try lia in 
  unfold stack_perms; 
  apply functional_extensionality; intros k;
  bdestruct (k <? n0)%nat; [tryeasylia | ]; try bdestruct (k <? n0 + n1);
  bdestructΩ'.
(* ^ REPLACED BY: solve_stack_perm; bdestructΩ' *)


(* TODO: Figure out order of operations on where to put this vs its lemma *)
(* Ltac perm_eq_by_WF_inv_inj f n :=
  apply (WF_permutation_inverse_injective f n); [
    tryeasylia; auto with perm_db |
    tryeasylia; auto with WF_perm_db |
    try solve [cleanup_perm; auto] |
    try solve [cleanup_perm; auto]]; tryeasylia. *)






Lemma mod_add_n_r : forall m n, 
	(m + n) mod n = m mod n.
Proof.
	intros m n.
	replace (m + n)%nat with (m + 1 * n)%nat by lia.
	destruct n.
	- cbn; easy.
	- rewrite Nat.mod_add;
		lia.
Qed.

Lemma mod_eq_sub : forall m n,
	m mod n = (m - n * (m / n))%nat.
Proof.
	intros m n.
	destruct n.
	- cbn; lia.
	- assert (H: (S n <> 0)%nat) by easy.
		pose proof (Nat.div_mod m (S n) H) as Heq.
		lia.
Qed.

Lemma mod_of_scale : forall m n q, 
	(n * q <= m < n * S q)%nat -> m mod n = (m - q * n)%nat.
Proof.
	intros m n q [Hmq HmSq].
	rewrite mod_eq_sub.
	replace (m/n)%nat with q; [lia|].
	apply Nat.le_antisymm.
	- apply Nat.div_le_lower_bound; lia. 
	- epose proof (Nat.div_lt_upper_bound m n (S q) _ _).
		lia.
		Unshelve.
		all: lia.
Qed.

Lemma mod_n_to_2n : forall m n, 
	(n <= m < 2 * n)%nat -> m mod n = (m - n)%nat.
Proof.
	intros.
	epose proof (mod_of_scale m n 1 _).
	lia.
	Unshelve.
	lia.
Qed.

Lemma mod_n_to_n_plus_n : forall m n, 
	(n <= m < n + n)%nat -> m mod n = (m - n)%nat.
Proof.
	intros.
	apply mod_n_to_2n; lia.
Qed.

Ltac simplify_mods_of a b :=
	first [
		rewrite (Nat.mod_small a b) in * by lia
	| rewrite (mod_n_to_2n a b) in * by lia
	].

Ltac solve_simple_mod_eqns :=
  let __fail_if_has_mods a :=
    match a with
    | context[_ mod _] => fail 1
    | _ => idtac
    end
  in
	match goal with
	| |- context[if _ then _ else _] => fail 1 "Cannot solve equation with if"
	| _ =>
		repeat first [
      easy
	  |	lia
		|	match goal with 
			| |- context[?a mod ?b] => __fail_if_has_mods a; __fail_if_has_mods b; 
					simplify_mods_of a b
			| H: context[?a mod ?b] |- _ => __fail_if_has_mods a; __fail_if_has_mods b; 
					simplify_mods_of a b
			end 
		| match goal with
			| |- context[?a mod ?b] => (* idtac a b; *) bdestruct (a <? b);
					[rewrite (Nat.mod_small a b) by lia 
					| try rewrite (mod_n_to_2n a b) by lia]
			end
		]
	end.

Ltac solve_modular_permutation_equalities :=
  first [cleanup_perm_of_zx | cleanup_perm_inv | cleanup_perm];
  unfold Basics.compose, rotr, rotl, stack_perms, swap_perm,
  (* TODO: remove *) swap_2_perm;
  apply functional_extensionality; let k := fresh "k" in intros k;
  bdestructΩ';
  solve_simple_mod_eqns.



(* Hack to get auto to apply PermStack where it obviously should 
  (like to ZXperm (S n) (— ↕ zx), where zx : ZX n n; it doesn't work 
  here because apply doesn't see that S n = 1 + n, but if we tell it
  to look for 1 + n, it will find S n). *)
Ltac __cleanup_stack_perm zx0 zx1 :=
  match type of zx0 with ZX ?n0 ?n0 =>
  match type of zx1 with ZX ?n1 ?n1 =>
  apply (PermStack (n0:=n0) (n1:=n1))
  end end.

#[export] Hint Extern 0 (ZXperm _ (?zx0 ↕ ?zx1)) => __cleanup_stack_perm zx0 zx1 : zxperm_db.

(* Making proportional_of_eq_perm usable, mostly through a series of tactics to
   deal with the absolute nightmare that is definitional equality casts. *)
Lemma prop_iff_double_cast : forall {n0 m0} n1 m1 (zx0 zx1 : ZX n0 m0) 
  (prfn: n1 = n0) (prfm : m1 = m0),
  Proportional.proportional zx0 zx1 <-> Proportional.proportional (cast n1 m1 prfn prfm zx0) (cast _ _ prfn prfm zx1).
Proof.
    intros.
    subst.
    reflexivity.
Qed.

Ltac __cast_prop_sides_to_square :=
  match goal with
  | |- Proportional.proportional ?zx0 ?zx1 =>
    match type of zx0 with 
    | ZX ?n ?n => idtac
    | ZX ?n ?m => 
      let Hm0n := fresh "Hm0n" in 
      assert (Hm0n : n = m) by lia;
      rewrite (prop_iff_double_cast n n zx0 zx1 (eq_refl) (Hm0n))
    end
  end.

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

Section Isolated.
(* TODO: This is really ugly. Can I get around it? *)
(* Note these next two lemmas are subsumed by the third, but I'm keeping them
   to exemplify how weird doing this is... *)
Lemma nat_equality_proof_equality : forall (n m : nat) (H0 H1 : n = m),
  H0 = H1.
Proof.
  intros n. intros.
  subst n.
  now rewrite Logic.Eqdep_dec.UIP_refl_nat.
Qed.

Lemma cast_proof_independence : forall n0 m0 n1 m1 (zx : ZX n0 m0) prfn1 prfm1 prfn2 prfm2,
  cast n1 m1 prfn1 prfm1 zx = cast n1 m1 prfn2 prfm2 zx.
Proof.
  intros. 
  (* Logic.Eqdep_dec.UIP_refl_nat *)
  (* Search "extensionality". *)
  replace prfn2 with prfn1 by (apply nat_equality_proof_equality).
  replace prfm2 with prfm1 by (apply nat_equality_proof_equality).
  reflexivity.
Qed.
End Isolated.

(* Also, note that this doesn't introduce any new axioms. It's just __weird__. *)
(* Print Assumptions Eqdep_dec.UIP_refl_nat. ("Closed under the global context")*)

Lemma cast_id_eq : forall n m (prfn : n = n) (prfm : m = m) zx,
  cast n m prfn prfm zx = zx.
Proof.
  intros; subst.
  rewrite (Eqdep_dec.UIP_refl_nat n prfn). (* Replace prfn with (@eq_refl nat n) *)
  rewrite (Eqdep_dec.UIP_refl_nat m prfm). (* Replace prfn with (@eq_refl nat m) *)
  reflexivity.
Qed.

Lemma zxperm_iff_cast' : forall n0 n1 zx (H H' : n1 = n0),
  ZXperm n1 (cast n1 n1 H H' zx) <-> ZXperm n0 zx.
Proof.
  intros.
  subst; rewrite cast_id_eq.
  reflexivity.
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
end; repeat simpl_casts_eq) || (repeat simpl_casts_eq).



#[export] Hint Extern 2 => (repeat first [rewrite cast_id_eq | rewrite cast_cast_eq]) : zxperm_db.

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

#[export] Hint Extern 3 (ZXperm _ (cast _ _ _ _ _)) => __one_round_cleanup_zxperm_of_cast : zxperm_db.

Lemma perm_of_cast_compose_each_square : forall n m a b c d
  (zx0 : ZX n n) (zx1 : ZX m m) prfa0 prfb0 prfb1 prfc1 prfd1 prfd2,
  ZXperm n zx0 -> ZXperm m zx1 ->
  ZXperm d (cast d d prfd1 prfd2 
  (cast a b prfa0 prfb0 zx0 ⟷ cast b c prfb1 prfc1 zx1)).
Proof.
  intros.
  subst.
  auto with zxperm_db.
Qed.

#[export] Hint Resolve perm_of_cast_compose_each_square : zxperm_db.

(* I don't know if these actually ever help: *)
Lemma perm_of_cast_compose_each_square_l : forall n m c d
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
Qed.


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
