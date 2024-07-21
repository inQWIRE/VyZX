Require Export ZXCore.
Require Export PermutationDefinitions.
Require Export QuantumLib.Permutations.
Require Export CoreRules.CoreAutomation.
Require Export ZXperm.




Create HintDb perm_cleanup_db.
Create HintDb perm_of_zx_cleanup_db.

Create HintDb zxperm_db.
#[export] Hint Constructors ZXperm : zxperm_db.

#[export] Hint Resolve 
  permutation_is_bounded
  permutation_is_injective
  permutation_is_surjective : perm_db.

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

Ltac cleanup_perm_inv := 
  auto with perm_inv_db perm_db perm_bounded_db WF_Perm_db;
  autorewrite with perm_inv_db; 
  auto with perm_inv_db perm_db perm_bounded_db WF_Perm_db.

Ltac cleanup_perm :=
  auto with perm_inv_db perm_cleanup_db perm_db perm_bounded_db WF_Perm_db;
  autorewrite with perm_inv_db perm_cleanup_db; 
  auto with perm_inv_db perm_cleanup_db perm_db perm_bounded_db WF_Perm_db.

Ltac cleanup_perm_of_zx :=
  autounfold with zxperm_db;
  autorewrite with perm_of_zx_cleanup_db perm_inv_db perm_cleanup_db;
  auto with perm_of_zx_cleanup_db perm_inv_db perm_cleanup_db
    perm_db perm_bounded_db WF_Perm_db.

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
  only 3,4 : 
    (try apply compose_id_of_compose_idn; cleanup_perm; tryeasylia) 
      || cleanup_perm; tryeasylia;
  only 1,2 : auto with perm_bounded_db; tryeasylia.

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


Ltac permutation_eq_by_WF_inv_inj f n :=
  let tryeasylia := (try easy); (try lia) in
  apply (WF_permutation_inverse_injective f n); [
    tryeasylia; auto with perm_db |
    tryeasylia; auto with WF_Perm_db |
    try solve [cleanup_perm; auto] |
    try solve [cleanup_perm; auto]]; 
    tryeasylia.

Lemma perm_inv_perm_eq_injective (f : nat -> nat) (n : nat) 
  {finv finv' : nat -> nat} (Hf : permutation n f) : 
  perm_eq n (finv ∘ f)%prg idn -> 
  perm_eq n (finv' ∘ f)%prg idn -> 
  perm_eq n finv finv'.
Proof.
  apply perm_linv_injective_of_surjective.
  auto with perm_db.
Qed.

Ltac perm_eq_by_inv_inj f n :=
  let tryeasylia := (try easy); (try lia) in
  apply (perm_inv_perm_eq_injective f n); [
    tryeasylia; auto with perm_db |
    try solve [cleanup_perm; auto] |
    try solve [cleanup_perm; auto]]; 
    tryeasylia.

Ltac eq_by_WF_perm_eq n := 
  apply (eq_of_WF_perm_eq n); 
  auto with WF_Perm_db.

Section ComposeLemmas.

Local Open Scope prg.

(* Helpers for rewriting with compose and perm_eq *)
Lemma compose_rewrite_l {f g h : nat -> nat}
  (H : f ∘ g = h) : forall (i : nat -> nat), 
  i ∘ f ∘ g = i ∘ h.
Proof.
  intros; 
  now rewrite compose_assoc, H.
Qed.

Lemma compose_rewrite_l_to_2 {f g h i : nat -> nat}
  (H : f ∘ g = h ∘ i) : forall (j : nat -> nat), 
  j ∘ f ∘ g = j ∘ h ∘ i.
Proof.
  intros; 
  now rewrite !compose_assoc, H.
Qed.

Lemma compose_rewrite_l_to_Id {f g : nat -> nat}
  (H : f ∘ g = idn) : forall (h : nat -> nat), 
  h ∘ f ∘ g = h.
Proof.
  intros; 
  now rewrite compose_assoc, H, compose_idn_r.
Qed.

Lemma compose_rewrite_r {f g h : nat -> nat}
  (H : f ∘ g = h) : forall (i : nat -> nat), 
  f ∘ (g ∘ i) = h ∘ i.
Proof.
  intros; 
  now rewrite <- compose_assoc, H.
Qed.

Lemma compose_rewrite_r_to_2 {f g h i : nat -> nat}
  (H : f ∘ g = h ∘ i) : forall (j : nat -> nat), 
  f ∘ (g ∘ j) = h ∘ (i ∘ j).
Proof.
  intros; 
  now rewrite <- !compose_assoc, H.
Qed.

Lemma compose_rewrite_r_to_Id {f g : nat -> nat}
  (H : f ∘ g = idn) : forall (h : nat -> nat), 
  f ∘ (g ∘ h) = h.
Proof.
  intros; 
  now rewrite <- compose_assoc, H, compose_idn_l.
Qed.

End ComposeLemmas.

Ltac make_compose_assoc_rewrite_l lem :=
  lazymatch type of lem with
  | forall a : ?A, @?f a => 
    constr:(fun a : A => ltac:(
      let r := make_compose_assoc_rewrite_l (lem a) in 
      exact r))
  | (?F ∘ ?G)%prg = idn => 
    constr:(compose_rewrite_l_to_Id lem)
  | (?F ∘ ?G)%prg = (?F' ∘ ?G')%prg => 
    constr:(compose_rewrite_l_to_2 lem)
  | (?F ∘ ?G)%prg = ?H => 
    constr:(compose_rewrite_l lem)
  end.

Ltac make_compose_assoc_rewrite_l' lem :=
  lazymatch type of lem with
  | forall a : ?A, @?f a => 
    constr:(fun a : A => ltac:(
      let r := make_compose_assoc_rewrite_l' (lem a) in 
      exact r))
  | idn = (?F ∘ ?G)%prg => 
    constr:(compose_rewrite_l_to_Id (eq_sym lem))
  | (?F ∘ ?G)%prg = (?F' ∘ ?G')%prg => 
    constr:(compose_rewrite_l_to_2 (eq_sym lem))
  | ?H = (?F ∘ ?G)%prg => 
    constr:(compose_rewrite_l (eq_sym lem))
  end.

Ltac rewrite_compose_assoc_l lem :=
  let lem' := make_compose_assoc_rewrite_l lem in
  rewrite lem' || rewrite lem.

Ltac rewrite_compose_assoc_l' lem :=
  let lem' := make_compose_assoc_rewrite_l' lem in
  rewrite lem' || rewrite <- lem.

Ltac make_compose_assoc_rewrite_r lem :=
  lazymatch type of lem with
  | forall a : ?A, @?f a => 
    constr:(fun a : A => ltac:(
      let r := make_compose_assoc_rewrite_r (lem a) in 
      exact r))
  | (?F ∘ ?G)%prg = idn => 
    constr:(compose_rewrite_r_to_Id lem)
  | (?F ∘ ?G)%prg = (?F' ∘ ?G')%prg => 
    constr:(compose_rewrite_r_to_2 lem)
  | (?F ∘ ?G)%prg = ?H => 
    constr:(compose_rewrite_r lem)
  end.

Ltac make_compose_assoc_rewrite_r' lem :=
  lazymatch type of lem with
  | forall a : ?A, @?f a => 
    constr:(fun a : A => ltac:(
      let r := make_compose_assoc_rewrite_r' (lem a) in 
      exact r))
  | idn = (?F ∘ ?G)%prg => 
    constr:(compose_rewrite_r_to_Id (eq_sym lem))
  | (?F ∘ ?G)%prg = (?F' ∘ ?G')%prg => 
    constr:(compose_rewrite_r_to_2 (eq_sym lem))
  | ?H = (?F ∘ ?G)%prg => 
    constr:(compose_rewrite_r (eq_sym lem))
  end.

Ltac rewrite_compose_assoc_r lem :=
  let lem' := make_compose_assoc_rewrite_r lem in
  rewrite lem' || rewrite lem.

Ltac rewrite_compose_assoc_r' lem :=
  let lem' := make_compose_assoc_rewrite_r' lem in
  rewrite lem' || rewrite <- lem.


Section PermComposeLemmas.

Local Open Scope prg.

Lemma perm_eq_compose_rewrite_l {n} {f g h : nat -> nat}
  (H : perm_eq n (f ∘ g) (h)) : forall (i : nat -> nat), 
  perm_eq n (i ∘ f ∘ g) (i ∘ h). 
Proof.
  intros i k Hk.
  unfold compose in *.
  now rewrite H.
Qed.

Lemma perm_eq_compose_rewrite_l_to_2 {n} {f g h i : nat -> nat}
  (H : perm_eq n (f ∘ g) (h ∘ i)) : forall (j : nat -> nat), 
  perm_eq n (j ∘ f ∘ g) (j ∘ h ∘ i).
Proof.
  intros j k Hk.
  unfold compose in *.
  now rewrite H.
Qed.

Lemma perm_eq_compose_rewrite_l_to_Id {n} {f g : nat -> nat}
  (H : perm_eq n (f ∘ g) idn) : forall (h : nat -> nat), 
  perm_eq n (h ∘ f ∘ g) h.
Proof.
  intros h k Hk.
  unfold compose in *.
  now rewrite H.
Qed.

Lemma perm_eq_compose_rewrite_r {n} {f g h : nat -> nat}
  (H : perm_eq n (f ∘ g) h) : forall (i : nat -> nat), 
  perm_bounded n i ->
  perm_eq n (f ∘ (g ∘ i)) (h ∘ i).
Proof.
  intros i Hi k Hk.
  unfold compose in *.
  now rewrite H by auto.
Qed.

Lemma perm_eq_compose_rewrite_r_to_2 {n} {f g h i : nat -> nat}
  (H : perm_eq n (f ∘ g) (h ∘ i)) : forall (j : nat -> nat), 
  perm_bounded n j ->
  perm_eq n (f ∘ (g ∘ j)) (h ∘ (i ∘ j)).
Proof.
  intros j Hj k Hk.
  unfold compose in *.
  now rewrite H by auto.
Qed.

Lemma perm_eq_compose_rewrite_r_to_Id {n} {f g : nat -> nat}
  (H : perm_eq n (f ∘ g) idn) : forall (h : nat -> nat), 
  perm_bounded n h ->
  perm_eq n (f ∘ (g ∘ h)) h.
Proof.
  intros h Hh k Hk.
  unfold compose in *.
  now rewrite H by auto.
Qed.

End PermComposeLemmas.

Lemma perm_eq_sym {n} {f g : nat -> nat} : 
  perm_eq n f g -> perm_eq n g f.
Proof.
  intros; symmetry; auto.
Qed.

Lemma perm_eq_trans {n} {f g h : nat -> nat} : 
  perm_eq n f g -> perm_eq n g h -> perm_eq n f h.
Proof.
  intros Hfg Hgh **; 
  rewrite Hfg; auto.
Qed.

Ltac make_perm_eq_compose_assoc_rewrite_l lem :=
  lazymatch type of lem with
  | forall l, Nat.lt l ?n -> (?F ∘ ?G)%prg l = idn l => 
    constr:(perm_eq_compose_rewrite_l_to_Id lem)
  | forall l, Nat.lt l ?n -> (?F ∘ ?G)%prg l = (?F' ∘ ?G')%prg l => 
    constr:(perm_eq_compose_rewrite_l_to_2 lem)
  | forall l, Nat.lt l ?n -> (?F ∘ ?G)%prg l = ?H _ => 
    constr:(perm_eq_compose_rewrite_l lem)
  | forall a : ?A, @?f a => 
    constr:(fun a : A => ltac:(
      let r := make_perm_eq_compose_assoc_rewrite_l (lem a) in 
      exact r))
  end.

Ltac make_perm_eq_compose_assoc_rewrite_l' lem :=
  lazymatch type of lem with
  | forall l, Nat.lt l ?n -> idn l = (?F ∘ ?G)%prg l => 
    constr:(perm_eq_compose_rewrite_l_to_Id (perm_eq_sym lem))
  | forall l, Nat.lt l ?n -> (?F ∘ ?G)%prg l = (?F' ∘ ?G')%prg l => 
    constr:(perm_eq_compose_rewrite_l_to_2 (perm_eq_sym lem))
  | forall l, Nat.lt l ?n -> ?H _ = (?F ∘ ?G)%prg l => 
    constr:(perm_eq_compose_rewrite_l (perm_eq_sym lem))
  | forall a : ?A, @?f a => 
    constr:(fun a : A => ltac:(
      let r := make_perm_eq_compose_assoc_rewrite_l' (lem a) in 
      exact r))
  end.

Ltac rewrite_perm_eq_compose_assoc_l lem :=
  let lem' := make_perm_eq_compose_assoc_rewrite_l lem in
  rewrite lem' || rewrite lem.

Ltac rewrite_perm_eq_compose_assoc_l' lem :=
  let lem' := make_perm_eq_compose_assoc_rewrite_l' lem in
  rewrite lem' || rewrite <- lem.

Ltac make_perm_eq_compose_assoc_rewrite_r lem :=
  lazymatch type of lem with
  | forall l, Nat.lt l ?n -> (?F ∘ ?G)%prg l = idn l => 
    constr:(perm_eq_compose_rewrite_r_to_Id lem)
  | forall l, Nat.lt l ?n -> (?F ∘ ?G)%prg l = (?F' ∘ ?G')%prg l => 
    constr:(perm_eq_compose_rewrite_r_to_2 lem)
  | forall l, Nat.lt l ?n -> (?F ∘ ?G)%prg l = ?H _ => 
    constr:(perm_eq_compose_rewrite_r lem)
  | forall a : ?A, @?f a => 
    constr:(fun a : A => ltac:(
      let r := make_perm_eq_compose_assoc_rewrite_r (lem a) in 
      exact r))
  end.

Ltac make_perm_eq_compose_assoc_rewrite_r' lem :=
  lazymatch type of lem with
  | forall l, Nat.lt l ?n -> idn l = (?F ∘ ?G)%prg l => 
    constr:(perm_eq_compose_rewrite_r_to_Id (perm_eq_sym lem))
  | forall l, Nat.lt l ?n -> (?F ∘ ?G)%prg l = (?F' ∘ ?G')%prg l => 
    constr:(perm_eq_compose_rewrite_r_to_2 (perm_eq_sym lem))
  | forall l, Nat.lt l ?n -> ?H _ = (?F ∘ ?G)%prg l => 
    constr:(perm_eq_compose_rewrite_r (perm_eq_sym lem))
  | forall a : ?A, @?f a => 
    constr:(fun a : A => ltac:(
      let r := make_perm_eq_compose_assoc_rewrite_r' (lem a) in 
      exact r))
  end.

Ltac rewrite_perm_eq_compose_assoc_r lem :=
  let lem' := make_perm_eq_compose_assoc_rewrite_r lem in
  rewrite lem' || rewrite lem.

Ltac rewrite_perm_eq_compose_assoc_r' lem :=
  let lem' := make_perm_eq_compose_assoc_rewrite_r' lem in
  rewrite lem' || rewrite <- lem.









Lemma mod_add_n_r : forall m n, 
	(m + n) mod n = m mod n.
Proof.
	intros m n.
	replace (m + n)%nat with (m + 1 * n)%nat by lia.
	destruct n.
	- cbn; easy.
	- apply Nat.Div0.mod_add.
Qed.

Lemma mod_eq_sub : forall m n,
	m mod n = (m - n * (m / n))%nat.
Proof.
	intros m n.
	pose proof (Nat.div_mod_eq m n).
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
	- pose proof (Nat.Div0.div_lt_upper_bound m n (S q)).
		lia.
Qed.

Lemma mod_n_to_2n : forall m n, 
	(n <= m < 2 * n)%nat -> m mod n = (m - n)%nat.
Proof.
	intros.
	pose proof (mod_of_scale m n 1).
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
  (cleanup_perm_of_zx || cleanup_perm_inv || cleanup_perm);
  unfold Basics.compose, rotr, rotl, stack_perms, swap_2_perm, swap_perm;
  try (apply functional_extensionality; 
  let k := fresh "k" in intros k);
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
  Proportional.proportional zx0 zx1 <-> 
  Proportional.proportional (cast n1 m1 prfn prfm zx0) (cast _ _ prfn prfm zx1).
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


Ltac simpl_bools :=
  repeat (simpl; rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r). 

Ltac simplify_bools_lia_one_free :=
  let act_T b := ((replace_bool_lia b true || replace_bool_lia b false); simpl) in 
  let act_F b := ((replace_bool_lia b false || replace_bool_lia b true); simpl) in 
  match goal with
  | |- context[?b && _] => act_F b; rewrite ?andb_true_l, ?andb_false_l
  | |- context[_ && ?b] => act_F b; rewrite ?andb_true_r, ?andb_false_r
  | |- context[?b || _] => act_T b; rewrite ?orb_true_l, ?orb_false_l
  | |- context[_ || ?b] => act_T b; rewrite ?orb_true_r, ?orb_false_r
  | |- context[negb ?b] => act_T b; simpl negb
  | |- context[if ?b then _ else _] => act_T b
  end; simpl_bools.

Ltac simplify_bools_lia_one_kernel :=
  let fail_if_iffy H :=
    match H with
    | context [ if _ then _ else _ ] => fail 1
    | _ => idtac
    end
  in
  let fail_if_compound H := 
    fail_if_iffy H;
    match H with
    | context [ ?a && ?b   ] => fail 1
    | context [ ?a || ?b   ] => fail 1
    | _ => idtac
    end
  in 
  let act_T b := (fail_if_compound b; 
    (replace_bool_lia b true || replace_bool_lia b false); simpl) in 
  let act_F b := (fail_if_compound b; 
    (replace_bool_lia b false || replace_bool_lia b true); simpl) in 
  match goal with
  | |- context[?b && _] => act_F b; rewrite ?andb_true_l, ?andb_false_l
  | |- context[_ && ?b] => act_F b; rewrite ?andb_true_r, ?andb_false_r
  | |- context[?b || _] => act_T b; rewrite ?orb_true_l, ?orb_false_l
  | |- context[_ || ?b] => act_T b; rewrite ?orb_true_r, ?orb_false_r
  | |- context[negb ?b] => act_T b; simpl negb
  | |- context[if ?b then _ else _] => act_T b
  end; simpl_bools.

Ltac simplify_bools_lia_many_kernel :=
  let fail_if_iffy H :=
    match H with
    | context [ if _ then _ else _ ] => fail 1
    | _ => idtac
    end
  in
  let fail_if_compound H := 
    fail_if_iffy H;
    match H with
    | context [ ?a && ?b   ] => fail 1
    | context [ ?a || ?b   ] => fail 1
    | _ => idtac
    end
  in 
  let act_T b := (fail_if_compound b; 
    (replace_bool_lia b true || replace_bool_lia b false); simpl) in 
  let act_F b := (fail_if_compound b; 
    (replace_bool_lia b false || replace_bool_lia b true); simpl) in 
  multimatch goal with
  | |- context[?b && _] => act_F b; rewrite ?andb_true_l, ?andb_false_l
  | |- context[_ && ?b] => act_F b; rewrite ?andb_true_r, ?andb_false_r
  | |- context[?b || _] => act_T b; rewrite ?orb_true_l, ?orb_false_l
  | |- context[_ || ?b] => act_T b; rewrite ?orb_true_r, ?orb_false_r
  | |- context[negb ?b] => act_T b; simpl negb
  | |- context[if ?b then _ else _] => act_T b
  end; simpl_bools.

Ltac simplify_bools_lia_one :=
  simplify_bools_lia_one_kernel || simplify_bools_lia_one_free.

Ltac simplify_bools_lia :=
  repeat simplify_bools_lia_one.

Ltac bdestruct_one_old := 
  let fail_if_iffy H :=
  match H with
  | context [ if _ then _ else _ ] => fail 1
  | _ => idtac
  end
  in
  match goal with
  | |- context [ ?a <? ?b ] =>
      fail_if_iffy a; fail_if_iffy b; bdestruct (a <? b)
  | |- context [ ?a <=? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a <=? b)
  | |- context [ ?a =? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a =? b)
  | |- context [ if ?b then _ else _ ] => fail_if_iffy b; destruct b eqn:?
  end.

Ltac bdestruct_one_new :=
  let fail_if_iffy H :=
    match H with
    | context [ if _ then _ else _ ] => fail 1
    | _ => idtac
    end
  in
  let fail_if_booley H := 
    fail_if_iffy H;
    match H with
    | context [ ?a <? ?b   ] => fail 1
    | context [ ?a <=? ?b  ] => fail 1
    | context [ ?a =? ?b   ] => fail 1
    | context [ ?a && ?b   ] => fail 1
    | context [ ?a || ?b   ] => fail 1
    | context [ negb ?a    ] => fail 1
    | context [ xorb ?a ?b ] => fail 1
    | _ => idtac
    end
  in 
  let rec destruct_kernel H :=
    match H with
    | context [ if ?b then _ else _ ] => destruct_kernel b
    | context [ ?a <? ?b   ] => 
      tryif fail_if_booley a then 
      (tryif fail_if_booley b then bdestruct (a <? b)
       else destruct_kernel b) else (destruct_kernel a)
    | context [ ?a <=? ?b  ] => 
      tryif fail_if_booley a then 
      (tryif fail_if_booley b then bdestruct (a <=? b)
       else destruct_kernel b) else (destruct_kernel a)
    | context [ ?a =? ?b   ] => 
      tryif fail_if_booley a then 
      (tryif fail_if_booley b then bdestruct (a =? b); try subst
       else destruct_kernel b) else (destruct_kernel a)
    | context [ ?a && ?b   ] => 
      destruct_kernel a || destruct_kernel b
    | context [ ?a || ?b   ] => 
      destruct_kernel a || destruct_kernel b
    | context [ xorb ?a ?b ] => 
      destruct_kernel a || destruct_kernel b
    | context [ negb ?a    ] =>
      destruct_kernel a
    | _ => idtac
    end
  in 
  simpl_bools;
  match goal with
  | |- context [ ?a =? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a =? b); try subst
  | |- context [ ?a <? ?b ] =>
      fail_if_iffy a; fail_if_iffy b; bdestruct (a <? b)
  | |- context [ ?a <=? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a <=? b)
  | |- context [ if ?b then _ else _ ] => fail_if_iffy b; destruct b eqn:?
  end;
  simpl_bools.

Ltac bdestruct_one' := bdestruct_one_new || bdestruct_one_old.

Ltac bdestructΩ'simp :=
  let tryeasylia := try easy; try lca; try lia in
  tryeasylia;
  repeat (bdestruct_one'; subst; simpl_bools; simpl; tryeasylia); tryeasylia.

Local Open Scope nat.



Lemma pow2_nonzero n : 2 ^ n <> 0.
Proof.
  apply Nat.pow_nonzero; lia.
Qed.

Ltac show_term_nonzero term :=
  match term with
  | 2 ^ ?a => exact (pow2_nonzero a)
  | ?a ^ ?b => exact (Nat.pow_nonzero a b ltac:(show_term_nonzero a))
  | ?a * ?b => 
    (assert (a <> 0) by (show_term_nonzero a);
    assert (b <> 0) by (show_term_nonzero b);
    lia)
  | ?a + ?b => 
    ((assert (a <> 0) by (show_term_nonzero a) ||
    assert (b <> 0) by (show_term_nonzero b));
    lia)
  | _ => lia
  | _ => nia
  end.

Ltac show_nonzero :=
  match goal with
  | |- ?t <> 0 => show_term_nonzero t
  | |- 0 <> ?t => symmetry; show_term_nonzero t
  | |- 0 < ?t => assert (t <> 0) by (show_term_nonzero t); lia
  | |- ?t > 0 => assert (t <> 0) by (show_term_nonzero t); lia
  | _ => lia
  end.

Ltac get_div_by_pow_2 t pwr :=
  match t with
  | 2 ^ pwr => constr:(1)
  | 2 ^ pwr * ?a => constr:(a)
  | ?a * 2 ^ pwr => constr:(a)
  | ?a * ?b => let ra := get_div_by_pow_2 a pwr in constr:(ra * b)
  | ?a * ?b => let rb := get_div_by_pow_2 b pwr in constr:(a * rb)
  | 2 ^ (?a + ?b) => 
    let val := constr:(2 ^ a * 2 ^ b) in 
    get_div_by_pow_2 val pwr
  | ?a + ?b => 
    let ra := get_div_by_pow_2 a pwr in 
    let rb := get_div_by_pow_2 b pwr in 
    constr:(ra + rb)
  | ?a - 1 => 
    let ra := get_div_by_pow_2 a pwr in 
    constr:(ra - 1)
  end.

Lemma div_mul_l a b : a <> 0 -> 
  (a * b) / a = b.
Proof.
  rewrite Nat.mul_comm;
  apply Nat.div_mul.
Qed.


Ltac show_div_by_pow2_ge t pwr :=
  (* Shows t / 2 ^ pwr <= get_div_by_pwr t pwr *)
  match t with
  | 2 ^ pwr => (* constr:(1) *)
    rewrite (Nat.div_same (2^pwr) (pow2_nonzero pwr));
    apply Nat.le_refl
  | 2 ^ pwr * ?a => (* constr:(a) *)
    rewrite (div_mul_l (2^pwr) a (pow2_nonzero pwr));
    apply Nat.le_refl
  | ?a * 2 ^ pwr => (* constr:(a) *)
    rewrite (Nat.div_mul a (2^pwr) (pow2_nonzero pwr));
    apply Nat.le_refl
  | ?a * (?b * ?c) => 
    let rval := constr:(a * b * c) in 
    show_div_by_pow2_ge rval pwr
  | ?a * ?b => (* b is not right, so... *)
    let rval := constr:(b * a) in 
    show_div_by_pow2_ge rval pwr
  | ?a + ?b => 
    let ra := get_div_by_pow_2 a pwr in 
    let rb := get_div_by_pow_2 b pwr in 
    constr:(ra + rb)
  | ?a - 1 => 
    fail 1 "Case not supported"
  | 2 ^ (?a + ?b) => 
    let val := constr:(2 ^ a * 2 ^ b) in 
    rewrite (Nat.pow_add_r 2 a b);
    show_div_by_pow2_ge val pwr
  
  end.


Ltac get_div_by t val :=
  match t with
  | val => constr:(1)
  | val * ?a => constr:(a)
  | ?a * val => constr:(a)
  | ?a * ?b => let ra := get_div_by a val in constr:(ra * b)
  | ?a * ?b => let rb := get_div_by b val in constr:(a * rb)
  | 2 ^ (?a + ?b) => 
    let val' := constr:(2 ^ a * 2 ^ b) in 
    get_div_by val' val
  | ?a + ?b => 
    let ra := get_div_by a val in 
    let rb := get_div_by b val in 
    constr:(ra + rb)
  | ?a - 1 => 
    let ra := get_div_by a val in 
    constr:(ra - 1)
  end.

Ltac show_div_by_ge t val :=
  (* Shows t / val <= get_div_by t val *)
  match t with
  | val => (* constr:(1) *)
    rewrite (Nat.div_same val ltac:(show_term_nonzero val));
    apply Nat.le_refl
  | val * ?a => (* constr:(a) *)
    rewrite (div_mul_l val a ltac:(show_term_nonzero val));
    apply Nat.le_refl
  | ?a * val => (* constr:(a) *)
    rewrite (Nat.div_mul a val ltac:(show_term_nonzero val));
    apply Nat.le_refl
  | ?a * (?b * ?c) => 
    let rval := constr:(a * b * c) in 
    show_div_by_ge rval val
  | ?a * ?b => (* b is not right, so... *)
    let rval := constr:(b * a) in 
    show_div_by_ge rval val
  | ?a + ?b => 
    let ra := get_div_by a val in 
    let rb := get_div_by b val in 
    constr:(ra + rb)
  | ?a - 1 => 
    nia ||
    fail 1 "Case not supported"
  end.

Ltac get_strict_upper_bound term :=
  match term with
  | ?k mod 0 => let r := get_strict_upper_bound k in constr:(r)
  | ?k mod (2 ^ ?a) => constr:(Nat.pow 2 a)
  | ?k mod (?a ^ ?b) => constr:(Nat.pow a b)
  | ?k mod ?a => 
    let _ := match goal with |- _ => assert (H: a <> 0) by show_nonzero end in
    constr:(a)
  | ?k mod ?a => 
    let _ := match goal with |- _ => assert (H: a = 0) by lia end in
    constr:(k + 1)
  
  | 2 ^ ?a * ?t => let r := get_strict_upper_bound t in 
    constr:(Nat.mul (Nat.pow 2 a) r)
  | ?t * 2 ^ ?a => let r := get_strict_upper_bound t in 
    constr:(Nat.mul r (Nat.pow 2 a))
  | ?a ^ ?b => constr:(Nat.pow a b + 1)

  | ?a + ?b => 
      let ra := get_strict_upper_bound a in 
      let rb := get_strict_upper_bound b in 
      constr:(ra + rb + 1)
  | ?a * ?b => 
      let ra := get_strict_upper_bound a in 
      let rb := get_strict_upper_bound b in 
      constr:(ra * rb + 1)
  | ?a / (?b * (?c * ?d)) => let rval := constr:(a / (b * c * d)) in
    let r := get_strict_upper_bound rval in constr:(r)
  | ?a / (?b * ?c) => let rval := constr:(a / b / c) in
    let r := get_strict_upper_bound rval in constr:(r)
  | ?a / (2 ^ ?b) => 
    let ra := get_strict_upper_bound a in 
    let rr := get_div_by_pow_2 ra b in constr:(rr)

  | ?t => match goal with
    | H : t < ?a |- _ => constr:(a)
    | H : t <= ?a |- _ => constr:(a + 1)
    | _ => constr:(t + 1)
    end
  end.

Ltac get_upper_bound term :=
  match term with
  | ?k mod 0 => let r := get_upper_bound k in constr:(r)
  | ?k mod (2 ^ ?a) => constr:(Nat.sub (Nat.pow 2 a) 1)
  | ?k mod (?a ^ ?b) => constr:(Nat.sub (Nat.pow a b) 1)
  | ?k mod ?a => 
    let H := fresh in 
    let _ := match goal with |- _ => 
      assert (H: a <> 0) by show_nonzero; clear H end in
    constr:(a - 1)
  | ?k mod ?a => 
    let H := fresh in 
    let _ := match goal with |- _ => 
      assert (H: a = 0) by lia; clear H end in
    let rk := get_upper_bound k in
    constr:(rk)
  
  | 2 ^ ?a * ?t => let r := get_upper_bound t in 
    constr:(Nat.mul (Nat.pow 2 a) r)
  | ?t * 2 ^ ?a => let r := get_upper_bound t in 
    constr:(Nat.mul r (Nat.pow 2 a))
  | ?a ^ ?b => constr:(Nat.pow a b)

  | ?a + ?b => 
      let ra := get_upper_bound a in 
      let rb := get_upper_bound b in 
      constr:(ra + rb)
  | ?a * ?b => 
      let ra := get_upper_bound a in 
      let rb := get_upper_bound b in 
      constr:(ra * rb)
  | ?a / (?b * (?c * ?d)) => let rval := constr:(a / (b * c * d)) in
    let r := get_upper_bound rval in constr:(r)
  | ?a / (?b * ?c) => let rval := constr:(a / b / c) in
    let r := get_upper_bound rval in constr:(r)
  | ?a / (2 ^ ?b) => 
    let ra := get_strict_upper_bound a in 
    let rr := get_div_by_pow_2 ra b in constr:(rr - 1)

  | ?a / ?b =>
    let ra := get_strict_upper_bound a in 
    let rr := get_div_by ra b in constr:(rr - 1)

  | ?t => match goal with
    | H : t < ?a |- _ => constr:(a - 1)
    | H : t <= ?a |- _ => constr:(a)
    | _ => t
    end
  end.

Lemma mul_ge_l_of_nonzero p q : q <> 0 ->
  p <= p * q.
Proof.
  nia.
Qed.

Lemma mul_ge_r_of_nonzero p q : p <> 0 ->
  q <= p * q.
Proof.
  nia.
Qed.

Ltac show_pow2_le :=
  rewrite ?Nat.pow_add_r, 
  ?Nat.mul_add_distr_r, ?Nat.mul_add_distr_l,
  ?Nat.mul_sub_distr_r, ?Nat.mul_sub_distr_l,
  ?Nat.mul_1_r, ?Nat.mul_1_l;
  repeat match goal with
  |- context [2 ^ ?a] => 
    tryif assert (2 ^ a <> 0) by assumption 
    then fail 
    else pose proof (pow2_nonzero a)
  end;
  nia || (
  repeat match goal with
  | |- context [?p * ?q] => 
    tryif assert (p <> 0) by assumption 
    then 
      (tryif assert (q <> 0) by assumption 
      then fail 
      else assert (q <> 0) by nia)
    else assert (p <> 0) by nia;
      (tryif assert (q <> 0) by assumption 
      then idtac else assert (q <> 0) by nia)
  end;
  repeat match goal with
  | |- context [?p * ?q] => 
    tryif assert (p <= p * q) by assumption 
    then 
      (tryif assert (q <= p * q) by assumption 
      then fail 
      else pose proof (mul_ge_r_of_nonzero p q ltac:(assumption)))
    else pose proof (mul_ge_l_of_nonzero p q ltac:(assumption));
      (tryif assert (q <= p * q) by assumption 
      then idtac
      else pose proof (mul_ge_r_of_nonzero p q ltac:(assumption)))
  end;
  nia).


Lemma lt_of_le_sub_1 a b : 
  b <> 0 -> a <= b - 1 -> a < b.
Proof. lia. Qed.

Lemma le_sub_1_of_lt a b : 
  a < b -> a <= b - 1.
Proof. lia. Qed.


Ltac show_le_upper_bound term :=
  lazymatch term with
  | ?k mod 0 => 
    rewrite (Nat.mod_0_r k);
    show_le_upper_bound k
  | ?k mod (2 ^ ?a) => 
    exact (le_sub_1_of_lt (k mod (2^a)) (2^a)
      (Nat.mod_upper_bound k (2^a) (pow2_nonzero a)))
  | ?k mod (?a ^ ?b) => 
    exact (le_sub_1_of_lt (k mod (2^a)) (a^b)
      (Nat.mod_upper_bound k (a^b) 
      (Nat.pow_nonzero a b ltac:(show_term_nonzero a))))
  | ?k mod ?a => 
    let H := fresh in 
    let _ := match goal with |- _ => 
      assert (H: a <> 0) by show_nonzero end in
    exact (le_sub_1_of_lt _ _ (Nat.mod_upper_bound k a H))
  | ?k mod ?a => 
    let H := fresh in 
    let _ := match goal with |- _ => 
      assert (H: a = 0) by lia end in
    rewrite H;
    show_le_upper_bound k
  
  | 2 ^ ?a * ?t => let r := get_upper_bound t in 
    apply (Nat.mul_le_mono_l t _ (2^a));
    show_le_upper_bound t
  | ?t * 2 ^ ?a => let r := get_upper_bound t in 
    apply (Nat.mul_le_mono_r t _ (2^a));
    show_le_upper_bound t
  | ?a ^ ?b => 
    apply Nat.le_refl

  | ?a + ?b => 
    apply Nat.add_le_mono;
    [
     (* match goal with |- ?G => idtac G "should be about" a end;  *)
     show_le_upper_bound a | 
     show_le_upper_bound b]
  | ?a * ?b => 
    apply Nat.mul_le_mono;
    [
     (* match goal with |- ?G => idtac G "should be about" a end;  *)
     show_le_upper_bound a | 
     show_le_upper_bound b]
  | ?a / (?b * (?c * ?d)) => 
    let H := fresh in 
    pose proof (f_equal (fun x => a / x) (Nat.mul_assoc b c d) :
      a / (b * (c * d)) = a / (b * c * d)) as H;
    rewrite H;
    clear H;
    let rval := constr:(a / (b * c * d)) in
    show_le_upper_bound rval
  | ?a / (?b * ?c) => 
    let H := fresh in 
    pose proof (eq_sym (Nat.Div0.div_div a b c) :
      a / (b * c) = a / b / c) as H;
    rewrite H;
    clear H;
    let rval := constr:(a / b / c) in
    show_le_upper_bound rval
  | ?a / (2 ^ ?b) => 
    let ra := get_upper_bound a in
    apply (Nat.le_trans (a / (2^b)) (ra / (2^b)) _);
    [apply Nat.Div0.div_le_mono;
     show_le_upper_bound a | 
     tryif show_div_by_pow2_ge ra b then idtac 
     else 
     match goal with
     | |- (?val - 1) / 2 ^ ?pwr <= ?rhs - 1 =>
      apply le_sub_1_of_lt, Nat.Div0.div_lt_upper_bound;
      tryif nia || show_pow2_le then idtac 
      else fail 20 "nia failed" "on (" val "- 1) / 2 ^" pwr "<=" rhs "- 1"
     | |- ?G =>
      tryif nia then idtac else 
     fail 40 "show div failed for" a "/ (2^" b "), ra =" ra 
      "; full goal:" G 
     end]
  | ?a / ?b =>
    let ra := get_upper_bound a in
    apply (Nat.le_trans (a / b) (ra / b) _);
    [apply Nat.Div0.div_le_mono;
     show_le_upper_bound a | 
     tryif show_div_by_ge ra b then idtac 
     else 
     match goal with
     | |- (?val - 1) / ?den <= ?rhs - 1 =>
      apply le_sub_1_of_lt, Nat.Div0.div_lt_upper_bound;
      tryif nia || show_pow2_le then idtac 
      else fail 20 "nia failed" "on (" val "- 1) / " den "<=" rhs "- 1"
     | |- ?G =>
      tryif nia then idtac else 
     fail 40 "show div failed for" a "/ (" b "), ra =" ra 
      "; full goal:" G 
     end]
  | ?t => match goal with
    | _ => nia
    end
  end.

Ltac show_moddy_lt :=
  lazymatch goal with
  | |- Bits.funbool_to_nat ?n ?f < ?b =>
    apply (Nat.lt_le_trans (Bits.funbool_to_nat n f) (2^n) b);
    [apply (Bits.funbool_to_nat_bound n f) | show_pow2_le]
  | |- Nat.b2n ?b < ?a =>
    apply (Nat.le_lt_trans (Nat.b2n b) (2^1) a);
    [destruct b; simpl; lia | show_pow2_le]
  | |- ?a < ?b =>
    let r := get_upper_bound a in
    apply (Nat.le_lt_trans a r b);
    [show_le_upper_bound a | show_pow2_le]
  | |- ?a <= ?b => (* Likely not to work *)
    let r := get_upper_bound a in
    apply (Nat.le_trans a r b);
    [show_le_upper_bound a | show_pow2_le]
  | |- ?a > ?b => 
    change (b < a); show_moddy_lt
  | |- ?a >= ?b => 
    change (b <= a); show_moddy_lt
  | |- (?a <? ?b) = true =>
    apply (proj2 (Nat.ltb_lt a b));
    show_moddy_lt
  | |- true = (?a <? ?b) =>
    symmetry;
    apply (proj2 (Nat.ltb_lt a b));
    show_moddy_lt
  | |- (?a <=? ?b) = false =>
    apply (proj2 (Nat.leb_gt a b));
    show_moddy_lt
  | |- false = (?a <=? ?b) =>
    symmetry;
    apply (proj2 (Nat.leb_gt a b));
    show_moddy_lt
  end.

Ltac try_show_moddy_lt := 
  lazymatch goal with
  | |- Bits.funbool_to_nat ?n ?f < ?b =>
    apply (Nat.le_lt_trans (Bits.funbool_to_nat n f) (2^n) b);
    [apply (Bits.funbool_to_nat_bound n f) | try show_pow2_le]
  | |- Nat.b2n ?b < ?a =>
    apply (Nat.le_lt_trans (Nat.b2n b) (2^1) a);
    [destruct b; simpl; lia | try show_pow2_le]
  | |- ?a < ?b =>
    let r := get_upper_bound a in
    apply (Nat.le_lt_trans a r b);
    [try show_le_upper_bound a | try show_pow2_le]
  | |- ?a <= ?b => (* Likely not to work *)
    let r := get_upper_bound a in
    apply (Nat.le_trans a r b);
    [try show_le_upper_bound a | try show_pow2_le]
  | |- ?a > ?b => 
    change (b < a); try_show_moddy_lt
  | |- ?a >= ?b => 
    change (b <= a); try_show_moddy_lt
  | |- (?a <? ?b) = true =>
    apply (proj2 (Nat.ltb_lt a b));
    try_show_moddy_lt
  | |- true = (?a <? ?b) =>
    symmetry;
    apply (proj2 (Nat.ltb_lt a b));
    try_show_moddy_lt
  | |- (?a <=? ?b) = false =>
    apply (proj2 (Nat.leb_gt a b));
    try_show_moddy_lt
  | |- false = (?a <=? ?b) =>
    symmetry;
    apply (proj2 (Nat.leb_gt a b));
    try_show_moddy_lt
  end.

Ltac replace_bool_moddy_lia b0 b1 :=
  first
    [ replace b0 with b1
      by (show_moddy_lt || bdestruct b0; show_moddy_lt + lia 
        || (destruct b1 eqn:?; lia))
    | replace b0 with b1
      by (bdestruct b1; lia || (destruct b0 eqn:?; lia))
    | replace b0 with b1
      by (bdestruct b0; bdestruct b1; lia) ].

Ltac simpl_bools_nosimpl :=
  repeat (rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r).

Ltac simplify_bools_moddy_lia_one_kernel :=
  let fail_if_iffy H :=
    match H with
    | context [ if _ then _ else _ ] => fail 1
    | _ => idtac
    end
  in
  let fail_if_compound H := 
    fail_if_iffy H;
    match H with
    | context [ ?a && ?b   ] => fail 1
    | context [ ?a || ?b   ] => fail 1
    | _ => idtac
    end
  in 
  let act_T b := (fail_if_compound b; 
    (replace_bool_moddy_lia b true 
    || replace_bool_moddy_lia b false); simpl) in 
  let act_F b := (fail_if_compound b; 
    (replace_bool_moddy_lia b false 
    || replace_bool_moddy_lia b true); simpl) in 
  match goal with
  | |- context[?b && _] => act_F b; rewrite ?andb_true_l, ?andb_false_l
  | |- context[_ && ?b] => act_F b; rewrite ?andb_true_r, ?andb_false_r
  | |- context[?b || _] => act_T b; rewrite ?orb_true_l, ?orb_false_l
  | |- context[_ || ?b] => act_T b; rewrite ?orb_true_r, ?orb_false_r
  | |- context[negb ?b] => act_T b; cbn [negb]
  | |- context[if ?b then _ else _] => act_T b
  end; simpl_bools_nosimpl.

(* For VyZX lemmas which create a ton of shelved goals, this solves 
   them immediately (and ensures they *are* solvable, seemingly
   unlike auto_cast_eqns) *)
Tactic Notation "clean_eqns" tactic(tac) :=
  unshelve (tac); [reflexivity + lia..|].



(* The following originate from ExamplesAutomation from the ViCAR examples*)
Require Import String.

Ltac print_hyps :=
  try (match reverse goal with | H : ?p |- _ => idtac H ":" p; fail end).

Ltac print_goal := 
  match reverse goal with |- ?P => idtac P; idtac "" end.

Ltac print_state :=
  print_hyps;
  idtac "---------------------------------------------------------";
  print_goal.

Ltac is_C0 x := assert (x = C0) by (cbv; lca).

Ltac is_C1 x := assert (x = C1) by (cbv; lca).

Tactic Notation "print_C" constr(x) := (tryif is_C0 x then constr:("0"%string) else
  tryif is_C1 x then constr:("1"%string) else constr:("X"%string)).

Ltac print_LHS_matU :=
  intros;
  (let i := fresh "i" in
  let j := fresh "j" in
  let Hi := fresh "Hi" in
  let Hj := fresh "Hj" in
  intros i j Hi Hj; try solve_end;
    repeat (* Enumerate rows and columns; see `by_cell` *)
    (destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
    try solve_end); clear Hi;
    repeat
    (destruct j as [| j]; [  | apply <- Nat.succ_lt_mono in Hj ];
    try solve_end); clear Hj
  );
  match goal with |- ?x = ?y ?i ?j => autounfold with U_db; simpl; 
  match goal with
  | |- ?x = _ => 
    tryif is_C0 x then idtac "A[" i "," j "] = 0" else
    tryif is_C1 x then idtac "A[" i "," j "] = 1" else
      idtac "A[" i "," j "] = X"
  end
end.

Ltac simplify_mods_one :=
  let __fail_if_has_mods a :=
   match a with
   | context [ _ mod _ ] => fail 1
   | _ => idtac
   end
  in
  match goal with
  | |- context [ ?a mod ?b ] =>
        __fail_if_has_mods a; __fail_if_has_mods b;
        simplify_mods_of a b
  | H:context [ ?a mod ?b ] |- _ =>
        __fail_if_has_mods a; __fail_if_has_mods b;
        simplify_mods_of a b
  end.

Ltac case_mods_one := 
  match goal with
  | |- context [ ?a mod ?b ] =>
        bdestruct (a <? b);
        [ rewrite (Nat.mod_small a b) by lia
        | try rewrite (mod_n_to_2n a b) by lia ]
  end.

#[export] Hint Extern 4 (WF_Matrix (@Mmult ?m ?n ?o ?A ?B)) => (
  match type of A with Matrix ?m' ?n' =>
  match type of B with Matrix ?n'' ?o'' =>
  let Hm' := fresh "Hm'" in let Hn' := fresh "Hn'" in
  let Hn'' := fresh "Hn''" in let Ho'' := fresh "Hoo'" in
  assert (Hm' : m = m') by lia;
  assert (Hn' : n = n') by lia;
  assert (Hn'' : n = n'') by lia;
  assert (Ho' : o = o'') by lia;
  replace (@Mmult m n o A B) with (@Mmult m' n' o A B) 
    by (first [try (rewrite Hm' at 1); try (rewrite Hn' at 1); reflexivity | f_equal; lia]);
  apply WF_mult; [
    auto with wf_db |
    apply WF_Matrix_dim_change;
    auto with wf_db
  ]
  end end) : wf_db.

#[export] Hint Extern 100 (_ < _) =>
  show_moddy_lt || show_pow2_le : perm_bounded_db.