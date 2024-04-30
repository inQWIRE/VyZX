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

(* Create HintDb perm_cleanup_db.
Create HintDb perm_of_zx_cleanup_db. *)

Create HintDb zxperm_db.
#[export] Hint Constructors ZXperm : zxperm_db.

(* TODO: Once quantumlib's up, put these things here: *)
(* Create HintDb WF_perm_db. *)
(* #[export] Hint Resolve monotonic_WF_perm compose_WF_perm : WF_perm_db. *)


(* Tactic Notation "tryeasylia" :=
  try easy; try lia. *)


Ltac show_permutation :=
  repeat first [
    split
  | simpl; solve [auto with perm_db]
  | subst; solve [auto with perm_db]
  | solve [eauto using permutation_compose with perm_db]
  | easy
  | lia
  ].

Ltac apply_f H k :=
  unfold compose in H;
  apply (f_equal (fun x => x k)) in H.



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
