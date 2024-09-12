Require Import CoreRules. 
Require Import ZXpermFacts.
Require Import BipermAux. 
From QuantumLib Require Import Modulus. 
Import Setoid. 


(* Permutation results *)
Import ComposeRules.
Import Modulus. 
Open Scope ZX_scope.
Open Scope prg.
Open Scope nat_scope.

(* FIXME: Move to Qlib *)
Tactic Notation "eq_by_WF_perm_eq" uconstr(n) :=
  eapply (eq_of_WF_perm_eq n); 
  [auto_perm..|].

(* FIXME: Move to Qlib.PermutationAutomation - or to Prelim, so it
  can be used in PermutationsBase / elsewhere *)
Lemma predicate_symmetry : forall A (R : relation A),   (* params *)
  forall (P : forall (a b : A), Prop),                  (* predicates *)
  forall (HP : forall a b, R a b -> P a b)              
    (HPsymm : forall a b, P a b -> P b a),              (* branches *)
  forall a b, (R a b \/ R b a) ->                       (* arguments *)
  P a b.                                                (* conclusion *)
Proof.
  intuition auto.
Qed.

Tactic Notation "by_symmetry" constr(H) "by" tactic3(tac) :=
  match type of H with 
  | ?R ?k ?l \/ ?R ?l ?k => 
    match type of R with 
    | forall (a b : ?T), _ =>
      pattern k, l;
      let G := fresh in 
      match goal with 
      |- ?P k l =>
        set (G := P);
        move H at top;
        gen l; intros l H;
        move H at top;
        gen k; intros k H;
        pattern k, l;
        refine (predicate_symmetry T R _ _ _ k l H);
        [clear k l H; intros k l H;
        intros;
        unfold G; clear G | unfold G; clear G; tac]
      end
    end
  end.

Tactic Notation "by_symmetry" constr(H) :=
  by_symmetry H by idtac.
  
(* FIXME: Move to ZXpermSemantics, near the other induction *)
Lemma zxperm_is_square_induction (P : forall n m, ZX n m -> Prop) : 
  (forall n (zx : ZX n n), ZXperm zx -> P n n zx) ->
  forall n m (zx : ZX n m), ZXperm zx -> P n m zx.
Proof.
  intros HP n m zx Hzx.
  pose proof (zxperm_square zx Hzx) as Heq.
  revert zx Hzx.
  subst m.
  auto.
Qed.





(* FIXME: Move*)

Add Parametric Morphism n : (Nsum_offset n) 
  with signature perm_eq n ==> eq as Nsum_offset_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  apply functional_extensionality; intros k.
  unfold Nsum_offset.
  f_equal.
  bdestruct (n =? 0); [now subst|].
  pose proof (Nsum_index_bounded n g k ltac:(auto)).
  rewrite (Nsum_index_perm_eq_to_eq _ _ _ Hfg).
  apply big_sum_eq_bounded.
  auto with zarith.
Qed.

Lemma Nsum_1 n : big_sum (fun _ => 1) n = n.
Proof.
  rewrite big_sum_constant, times_n_nat; lia.
Qed.

Lemma Nsum_index_1 n k (Hk : k < n) : 
  Nsum_index n (fun _ => 1) k = k.
Proof.
  induction n; [lia|].
  cbn.
  rewrite Nsum_1.
  bdestruct_one; lia.
Qed.

Lemma Nsum_offset_1 n k (Hk : k < n) : 
  Nsum_offset n (fun _ => 1) k = 0.
Proof.
  pose proof (Nsum_index_offset_spec n (fun _ => 1) k).
  rewrite Nsum_1 in H.
  lia.
Qed.

Lemma Nsum_constant d n : 
  big_sum (fun _ => d) n = n * d.
Proof.
  rewrite big_sum_constant, times_n_nat; lia.
Qed.

(* FIXME: generalize to Comm_Group as well, and move to Qlib *)
Lemma Nsum_plus n f g : 
  big_sum (fun k => f k + g k) n = big_sum f n + big_sum g n.
Proof.
  induction n; cbn; lia.
Qed.

(* FIXME: Move *)
Lemma Nsum_le_r n m f : n <= m -> 
  big_sum f n <= big_sum f m.
Proof.
  intros Hle.
  induction Hle; cbn; lia.
Qed.

(* FIXME: Move to Qlib.Summation *)
Lemma big_sum_if_lt {G} {HG : Monoid G} n m (f g : nat -> G) : 
  big_sum (fun k => if k <? n then f k else g (k - n)) (n + m) = 
  (big_sum f n + big_sum g m)%G.
Proof.
  rewrite big_sum_sum.
  f_equal; apply big_sum_eq_bounded; intros k Hk.
  - bdestructΩ'.
  - rewrite add_sub'.
    bdestructΩ'.
Qed.

Lemma Nsum_if_lt n m f g : 
  big_sum (fun k => if k <? n then f k else g (k - n)) (n + m) = 
  big_sum f n + big_sum g m.
Proof. exact (big_sum_if_lt n m f g). Qed.


  Lemma Nsum_index_constant n d k (Hk : k < n * d) : 
  Nsum_index n (fun _ => d) k = k / d.
Proof.
  induction n; [lia|].
  cbn.
  rewrite Nsum_constant.
  bdestructΩ'.
  symmetry.
  apply Kronecker.div_eq_iff; lia.
Qed.

Lemma Nsum_offset_constant n d k (Hk : k < n * d) : 
  Nsum_offset n (fun _ => d) k = k mod d.
Proof.
  pose proof (Nsum_index_offset_spec n (fun _ => d) k 
    ltac:(rewrite Nsum_constant; lia)).
  rewrite Nsum_index_constant, Nsum_constant in H
    by auto.
  pose proof (Nat.div_mod_eq k d).
  lia.
Qed.

Lemma Nsum_index_big n g k (Hk : big_sum g n <= k) : 
  Nsum_index n g k = pred n.
Proof.
  induction n; [reflexivity|].
  cbn in *.
  bdestructΩ'.
Qed.

Lemma Nsum_index_add n m g k (Hk : k < big_sum g (n + m)) : 
  Nsum_index (n + m) g k = 
  if k <? big_sum g n then (Nsum_index n g k)
  else n + (Nsum_index m (fun i => (g (n + i))) (k - big_sum g n)).
Proof.
  induction m.
  - rewrite Nat.add_0_r in *; bdestructΩ'.
  - pose proof (Nsum_le_r n (n + m) g ltac:(lia)).
    pose proof (big_sum_sum n m g) as Hsplit.
    cbn [nat_is_monoid Gplus] in Hsplit.
    rewrite Nat.add_succ_r.
    cbn.
    bdestructΩ'.
Qed.

Lemma Nsum_offset_add n m g k (Hk : k < big_sum g (n + m)) : 
  Nsum_offset (n + m) g k = 
  if k <? big_sum g n then (Nsum_offset n g k)
  else Nsum_offset m (fun i => (g (n + i))) (k - big_sum g n).
Proof.
  unfold Nsum_offset.
  rewrite Nsum_index_add by auto.
  bdestruct (k <? big_sum g n); [auto|].
  rewrite big_sum_sum.
  cbn; lia.
Qed.

Lemma Nsum_index_succ n g k (Hk : k < big_sum g (S n)) : 
  Nsum_index (S n) g k = 
  if k <? g 0 then 0
  else S (Nsum_index n (g ∘ S) (k - g 0)).
Proof.
  exact (Nsum_index_add 1 n g k Hk).
Qed.

Lemma Nsum_offset_succ n g k (Hk : k < big_sum g (S n)) : 
  Nsum_offset (S n) g k = 
  if k <? g 0 then k
  else Nsum_offset n (g ∘ S) (k - g 0).
Proof.
  change (S n) with (1 + n).
  rewrite (Nsum_offset_add 1 n g k Hk).
  apply f_equal_if_precedent_same; [|reflexivity].
  unfold Nsum_offset.
  cbn; simplify_bools_lia_one_kernel; cbn; lia.
Qed.

Lemma Nsum_offset_succ_defn n g k : 
  Nsum_offset (S n) g k = 
  if big_sum g n <=? k then k - big_sum g n else
  Nsum_offset n g k.
Proof.
  unfold Nsum_offset.
  cbn.
  bdestructΩ'.
Qed.






(* FIXME: Move *)
Lemma cast_contract_eq {n0 m0 n1 m1 n2 m2}
  (zx : ZX n0 m0) prfn01 prfm01 prfn12 prfm12 : 
  cast n2 m2 prfn12 prfm12 (cast n1 m1 prfn01 prfm01 zx) = 
  cast n2 m2 (eq_trans prfn12 prfn01) (eq_trans prfm12 prfm01) zx.
Proof.
  now subst.
Qed.

(* FIXME: Move *)
Lemma cast_stack_l_r {n0 m0 n0' m0' n1 m1 n1' m1'}
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfn0 prfm0 prfn1 prfm1 : 
  cast n0' m0' prfn0 prfm0 zx0 ↕
  cast n1' m1' prfn1 prfm1 zx1 ∝
  cast _ _ (f_equal2 (Nat.add) prfn0 prfn1)
    (f_equal2 (Nat.add) prfm0 prfm1)
    (zx0 ↕ zx1).
Proof.
  subst; cbn; now rewrite cast_id.
Qed.

Lemma cast_backwards_fwd {n0 m0 n1 m1 : nat}  
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfn prfm : 
  cast _ _ prfn prfm zx0 ∝ zx1 <->
  zx0 ∝ cast _ _ (eq_sym prfn) (eq_sym prfm) zx1.
Proof.
  now subst.
Qed.

Lemma cast_backwards_rev {n0 m0 n1 m1 : nat}  
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfn prfm : 
  zx0 ∝ cast _ _ prfn prfm zx1 <->
  cast _ _ (eq_sym prfn) (eq_sym prfm) zx0 ∝ zx1.
Proof.
  now subst.
Qed.

Lemma prf_add_cancel_l {a b c d} : a + b = c + d -> a = c -> b = d.
Proof. lia. Qed.

Lemma prf_add_cancel_r {a b c d} : a + b = c + d -> b = d -> a = c.
Proof. lia. Qed.

Lemma cast_stack_distribute_fwd_l {n0 m0 n1 m1 n0' m0' n1' m1'} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfns prfms prfn0 prfm0 :
  cast (n0' + n1') (m0' + m1') prfns prfms (zx0 ↕ zx1) ∝
  cast _ _ prfn0 prfm0 zx0 ↕
  cast _ _ (prf_add_cancel_l prfns prfn0) 
    (prf_add_cancel_l prfms prfm0) zx1.
Proof.
  pose proof (prf_add_cancel_l prfns prfn0).
  pose proof (prf_add_cancel_l prfms prfm0).
  subst; cbn; now rewrite !cast_id.
Qed.

Lemma cast_stack_distribute_fwd_r {n0 m0 n1 m1 n0' m0' n1' m1'} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) prfns prfms prfn1 prfm1 :
  cast (n0' + n1') (m0' + m1') prfns prfms (zx0 ↕ zx1) ∝
  cast _ _ (prf_add_cancel_r prfns prfn1) 
    (prf_add_cancel_r prfms prfm1) zx0
  ↕ cast _ _ prfn1 prfm1 zx1.
Proof.
  pose proof (prf_add_cancel_r prfns prfn1).
  pose proof (prf_add_cancel_r prfms prfm1).
  subst; cbn; now rewrite !cast_id.
Qed.

(* FIXME: Move, to CastRules? Or maybe ComposeRules? *)
Lemma compose_simplify_casted {n m m' o} 
  (zx0 : ZX n m) (zx1 : ZX m o) (zx0' : ZX n m') (zx1' : ZX m' o) 
  (Hm : m = m') : 
  zx0 ∝ cast _ _ eq_refl Hm zx0' ->
  zx1 ∝ cast _ _ Hm eq_refl zx1' ->
  zx0 ⟷ zx1 ∝ zx0' ⟷ zx1'.
Proof.
  subst.
  now intros -> ->.
Qed.



Fixpoint big_stack (ns ms : nat -> nat) 
  (zxs : forall i, ZX (ns i) (ms i)) (n : nat) 
  : ZX (big_sum ns n) (big_sum ms n) :=
  match n with
  | O => ⦰
  | S n' => big_stack ns ms zxs n' ↕ (zxs n')
  end. 

#[export] Hint Resolve WF_big_kron' : wf_db.

Lemma big_stack_semantics ns ms zxs n : 
  ⟦ big_stack ns ms zxs n ⟧ = 
  big_kron' ms ns (fun i => ⟦ zxs i ⟧) n.
Proof.
  induction n;
  now cbn; f_equal.
Qed.

Lemma big_stack_transpose ns ms zxs n : 
  (big_stack ns ms zxs n) ⊤ =
  big_stack ms ns (fun k => (zxs k) ⊤) n.
Proof.
  induction n; cbn; f_equal; easy.
Qed.

Lemma colorswap_big_stack ns ms zxs n : 
  ⊙ (big_stack ns ms zxs n) = 
  big_stack ns ms (fun k => ⊙ (zxs k)) n.
Proof.
  induction n; cbn; now f_equal.
Qed.

#[export] Hint Rewrite colorswap_big_stack : colorswap_db.



(* FIXME: Move to Qlib *)
Lemma big_kron'_eq_bounded_dims {n ns ns' ms ms'}
  {As : forall k, Matrix (2 ^ ns k) (2 ^ ms k)}
  {Bs : forall k, Matrix (2 ^ ns' k) (2 ^ ms' k)}
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms')
  (HAB : forall k, k < n -> As k = Bs k) :
  big_kron' ns ms As n = big_kron' ns' ms' Bs n.
Proof.
  induction n; [easy|].
  cbn.
  f_equal;
  [f_equal; clear IHn; unfold perm_eq in *;
    try apply big_sum_eq_bounded; auto..| |].
  - unfold perm_eq in *; apply IHn; auto.
  - apply HAB; auto.
Qed.

Lemma big_stack_simplify ns ms zx0s zx1s n 
  (Hzxs : forall k, k < n -> zx0s k ∝ zx1s k) : 
  big_stack ns ms zx0s n ∝
  big_stack ns ms zx1s n.
Proof.
  induction n; [easy|].
  cbn.
  apply stack_simplify; [|now apply Hzxs; auto].
  apply IHn.
  auto.
Qed.


Lemma kron_mat_prop_proper' {n m o p n' m' o' p' no mp} 
  (A : Matrix n m) (A' : Matrix n' m') 
  (B : Matrix o p) (B' : Matrix o' p') : n = n' -> m = m' -> 
  o = o' -> p = p' -> n * o = no -> m * p = mp ->
  mat_prop n m A A' -> mat_prop o p B B' -> 
  mat_prop no mp (@kron n m o p A B) (@kron n' m' o' p' A' B').
Proof.
  intros; subst; now apply kron_mat_prop_proper.
Qed.

Lemma big_kron'_prop_bounded_dims {n ns ns' ms ms'}
	{As : forall k, Matrix (2 ^ ns k) (2 ^ ms k)}
  {Bs : forall k, Matrix (2 ^ ns' k) (2 ^ ms' k)}
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms') 
  (HAB : forall k, k < n -> As k [∝] Bs k) : 
  big_kron' ns ms As n [∝] big_kron' ns' ms' Bs n.
Proof.
  induction n; [reflexivity|].
  cbn.
  apply kron_mat_prop_proper';
  [unify_pows_two; solve [(apply Hns + apply Hms); auto | 
    apply big_sum_eq_bounded; unfold perm_eq in *; auto]..| |now auto].
  unfold perm_eq in *; auto.
Qed.

Lemma big_kron'_prop_bounded {n ns ms} 
	{As : forall k, Matrix (2 ^ ns k) (2 ^ ms k)}
  {Bs : forall k, Matrix (2 ^ ns k) (2 ^ ms k)}
  (HAB : forall k, k < n -> As k [∝] Bs k) : 
  big_kron' ns ms As n [∝] big_kron' ns ms Bs n.
Proof.
  now apply big_kron'_prop_bounded_dims.
Qed.

Add Parametric Morphism n m : (@ZX_semantics n m) with signature
  @proportional n m ==> @mat_prop (2^m) (2^n) as 
  ZX_semantics_proportional_to_mat_prop.
Proof. intros ? ? H; exact H. Qed.

(* FIXME: Move *)
Lemma ZX_prop_by_mat_prop {n m} (zx0 zx1 : ZX n m) :
  ⟦ zx0 ⟧ [∝] ⟦ zx1 ⟧ -> zx0 ∝ zx1.
Proof. 
  intros H; exact H.
Qed.

Lemma ZX_prop_to_mat_prop {n m} (zx0 zx1 : ZX n m) :
  zx0 ∝ zx1 -> ⟦ zx0 ⟧ [∝] ⟦ zx1 ⟧.
Proof.
  intros H; exact H.
Qed.

Lemma big_stack_simplify_casted_len ns ms 
  (zxs : forall k, ZX (ns k) (ms k)) ns' ms' 
  (zxs' : forall k, ZX (ns' k) (ms' k)) n n'
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms')
  (Hzxs : forall k (Hk : k < n), zxs k ∝ 
    cast _ _ (Hns k Hk) (Hms k Hk) (zxs' k)) 
  (Hn : n = n') prfns prfms : 
  big_stack ns ms zxs n ∝
  cast _ _ prfns prfms (big_stack ns' ms' zxs' n').
Proof.
  match goal with |- ?A ∝ ?B => 
  change (⟦ A ⟧ [∝] ⟦ B ⟧) end.
  simpl_cast_semantics.
  rewrite 2!big_stack_semantics.
  subst n'.
  apply big_kron'_prop_bounded_dims; [now auto..|].
  intros k Hk.
  rewrite (Hzxs k Hk).
  now simpl_cast_semantics.
Qed.


Lemma big_stack_simplify_casted ns ms zxs ns' ms' zxs' n 
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms')
  (Hzxs : forall k (Hk : k < n), zxs k ∝ 
    cast _ _ (Hns k Hk) (Hms k Hk) (zxs' k)) 
  prfns prfms : 
  big_stack ns ms zxs n ∝
  cast _ _ prfns prfms (big_stack ns' ms' zxs' n).
Proof.
  unshelve (eapply big_stack_simplify_casted_len); easy.
Qed.

Lemma big_stack_simplify_casted_abs ns ms zxs ns' ms' zxs' n 
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms')
  (Hzxs : forall k prfn prfm, k < n -> zxs k ∝ 
    cast _ _ prfn prfm (zxs' k)) 
  prfns prfms : 
  big_stack ns ms zxs n ∝
  cast _ _ prfns prfms (big_stack ns' ms' zxs' n).
Proof.
  unshelve (eapply big_stack_simplify_casted); now auto.
Qed.

Lemma big_stack_simplify_casted_casted_abs ns ms zxs ns' ms' zxs' n 
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms')
  (Hzxs : forall k prfn prfm, k < n -> zxs k ∝ 
    cast _ _ prfn prfm (zxs' k)) 
  n' m' prfns prfms prfns' prfms' : 
  cast n' m' prfns prfms (big_stack ns ms zxs n) ∝
  cast n' m' prfns' prfms' (big_stack ns' ms' zxs' n).
Proof.
  revert prfns prfms.
  intros -> ->.
  rewrite cast_id.
  apply big_stack_simplify_casted_abs; now auto.
Qed.

(* FIXME: Move *)
Definition zx_dummy n m : ZX n m := Z n m 0.
Opaque zx_dummy.

Lemma big_stack_resize {n ns ms ns' ms'}
  (Hns : perm_eq n ns ns') (Hms : perm_eq n ms ms') zxs : 
  big_stack ns ms zxs n ∝
  cast _ _ (big_sum_eq_bounded _ _ n (Hns))
    (big_sum_eq_bounded _ _ n (Hms))
    (big_stack ns' ms' 
    (fun k => 
    match lt_dec k n with
    | left Hk => cast (ns' k) (ms' k) 
      (eq_sym (Hns k Hk)) (eq_sym (Hms k Hk)) (zxs k)
    | right _ => zx_dummy (ns' k) (ms' k)
    end ) n).
Proof.
  apply big_stack_simplify_casted_abs; [now auto..|].
  intros k ? ? Hk.
  destruct (lt_dec k n); [|lia].
  now rewrite cast_contract_eq, cast_id.
Qed.

Lemma big_stack_resize_unbounded {n ns ms ns' ms'}
  (Hns : forall k, ns k = ns' k) (Hms : forall k, ms k = ms' k) zxs : 
  big_stack ns ms zxs n ∝
  cast _ _ (big_sum_eq_bounded _ _ n (fun k _ => Hns k))
    (big_sum_eq_bounded _ _ n (fun k _ => Hms k))
    (big_stack ns' ms' 
    (fun k => cast (ns' k) (ms' k) 
      (eq_sym (Hns k)) (eq_sym (Hms k)) (zxs k)) n).
Proof.
  apply big_stack_simplify_casted_abs; [intros k Hk; now auto..|].
  intros k ? ? Hk.
  now rewrite cast_contract_eq, cast_id.
Qed.

Lemma big_stack_compose ns ms os zx0s zx1s n : 
  big_stack ns ms zx0s n ⟷ big_stack ms os zx1s n ∝
  big_stack ns os (fun k => zx0s k ⟷ zx1s k) n.
Proof.
  induction n; [apply compose_empty_l|].
  cbn.
  rewrite <- stack_compose_distr.
  now rewrite IHn.
Qed.

Lemma big_sum_double_sum_indexed {G} {H : Monoid G} fs ns n :
  big_sum (fun k => big_sum (fs k) (ns k)) n =
  big_sum (fun k => fs (Nsum_index n ns k) (Nsum_offset n ns k)) 
    (big_sum ns n).
Proof.
  induction n; [reflexivity|].
  cbn.
  rewrite big_sum_sum.
  f_equal.
  - rewrite IHn.
    apply big_sum_eq_bounded.
    intros k Hk.
    rewrite Nsum_offset_succ_defn.
    now simplify_bools_lia_one_kernel.
  - apply big_sum_eq_bounded.
    intros k Hk.
    simplify_bools_lia_one_kernel.
    now rewrite Nsum_offset_add_big_sum_l by lia.
Qed.

Lemma big_kron'_double_kron'_indexed 
  nss mss Bss ns n 
  (HBss : forall k, k < n -> forall l, l < ns k -> WF_Matrix (Bss k l)) :
  big_kron' (fun k => big_sum (nss k) (ns k))
    (fun k => big_sum (mss k) (ns k))
    (fun k => big_kron' (nss k) (mss k) (Bss k) (ns k)) n =
  big_kron'
    (fun k => nss (Nsum_index n ns k) (Nsum_offset n ns k))
    (fun k => mss (Nsum_index n ns k) (Nsum_offset n ns k))
    (fun k => Bss (Nsum_index n ns k) (Nsum_offset n ns k))
    (big_sum ns n).
Proof.
  induction n; [reflexivity|].
  cbn -[Nsum_index].
  rewrite big_kron'_split_add;
  [f_equal; unify_pows_two..|].
  - rewrite big_sum_double_sum_indexed.
    apply big_sum_eq_bounded.
    intros k Hk.
    cbn; rewrite Nsum_offset_succ_defn.
    now simplify_bools_lia_one_kernel.
  - rewrite big_sum_double_sum_indexed.
    apply big_sum_eq_bounded.
    intros k Hk.
    cbn; rewrite Nsum_offset_succ_defn.
    now simplify_bools_lia_one_kernel.
  - apply big_sum_eq_bounded.
    intros k Hk.
    now rewrite Nsum_index_add_big_sum_l, Nsum_offset_add_big_sum_l by lia.
  - apply big_sum_eq_bounded.
    intros k Hk.
    now rewrite Nsum_index_add_big_sum_l, Nsum_offset_add_big_sum_l by lia.
  - rewrite IHn by auto.
    apply (@big_kron'_eq_bounded_dims (big_sum ns n));
    intros k Hk; cbn; rewrite Nsum_offset_succ_defn;
    now simplify_bools_lia_one_kernel.
  - apply big_kron'_eq_bounded_dims;
    intros k Hk; now rewrite Nsum_index_add_big_sum_l, 
      Nsum_offset_add_big_sum_l by lia.
  - intros k Hk.
    apply HBss.
    + apply Nsum_index_bounded; lia.
    + apply Nsum_index_offset_spec; cbn; lia.
Qed.

Lemma big_stack_big_stack nss mss zxss ns n : 
  big_stack (fun k => big_sum (nss k) (ns k))
    (fun k => big_sum (mss k) (ns k))
    (fun k => big_stack (nss k) (mss k) (zxss k) (ns k)) n ∝
  cast _ _ (big_sum_double_sum_indexed nss ns n) 
    (big_sum_double_sum_indexed mss ns n)
  (big_stack _ _ (fun k => zxss _ _) _).
Proof.
  apply ZX_prop_by_mat_prop.
  simpl_cast_semantics.
  rewrite 2!big_stack_semantics.
  erewrite big_kron'_eq_bounded;
  [|intros k Hk; apply big_stack_semantics].
  rewrite big_kron'_double_kron'_indexed by (intros; auto_wf).
  reflexivity.
Qed.


Lemma big_stack_stack_prf (n0s n1s : nat -> nat) (n : nat) : 
  big_sum (fun k => n0s k + n1s k) n =
  big_sum(fun k => if k mod 2 =? 0 then n0s (k / 2) else n1s (k / 2)) (n * 2).
Proof.
  change (fun k : nat => n0s k + n1s k) with 
    (fun k => big_sum (fun l => if l =? 0 then n0s k else n1s k) 2).
  now rewrite big_sum_double_sum, Nat.mul_comm.
Qed.

Lemma big_stack_rebound {n n'} (H : n = n') ns ms zxs : 
  big_stack ns ms zxs n ∝
  cast _ _ (f_equal _ H) (f_equal _ H)
    (big_stack ns ms zxs n').
Proof.
  now subst.
Qed.

Lemma big_stack_stack n0s n1s m0s m1s zx0s zx1s n : 
  big_stack (fun k => n0s k + n1s k) (fun k => m0s k + m1s k)
  (fun k => zx0s k ↕ zx1s k) n ∝
  cast _ _ (big_stack_stack_prf n0s n1s n) 
    (big_stack_stack_prf m0s m1s n)
  (big_stack (fun k => if k mod 2 =? 0 then n0s (k / 2) else n1s (k / 2))
    (fun k => if k mod 2 =? 0 then m0s (k / 2) else m1s (k / 2))
    (fun k => 
      if k mod 2 =? 0 as a return 
        ZX (if a then n0s (k / 2) else n1s (k / 2))
           (if a then m0s (k / 2) else m1s (k / 2)) 
      then zx0s (k / 2) else zx1s (k / 2)) (n * 2)). 
Proof.
  rewrite (big_stack_simplify _ _ _ (fun k => 
    big_stack (fun l => if l =? 0 then n0s k else n1s k)
      (fun l => if l =? 0 then m0s k else m1s k)
      (fun l => if l =? 0 as a 
        return ZX (if a then n0s k else n1s k) (if a then m0s k else m1s k) 
        then zx0s k else zx1s k) 2)).
  2: {
    intros k Hk.
    cbn.
    now rewrite stack_empty_l.
  }
  rewrite big_stack_big_stack.
  rewrite (big_stack_rebound (Nsum_constant _ _)).
  rewrite cast_contract_eq.
  apply big_stack_simplify_casted_casted_abs;
  [intros k Hk; now rewrite Nsum_offset_constant, 
    Nsum_index_constant by lia..|].
  intros k prfn prfm Hk; revert prfn prfm.
  rewrite Nsum_offset_constant, Nsum_index_constant by lia.
  intros ? ?; now rewrite cast_id.
Qed.

Lemma big_stack_mult_prf (ns : nat -> nat) n n' :
  big_sum ns (n * n') =
  big_sum (fun k =>
    big_sum (fun i => ns (k * n' + i)) n') n.
Proof.
  rewrite big_sum_double_sum, Nat.mul_comm.
  apply big_sum_eq_bounded.
  intros k Hk.
  f_equal.
  pose proof (Nat.div_mod_eq k n'); lia.
Qed.

(* FIXME: Move to Qlib *)
Lemma big_kron'_mult ns ms As n n'
  (HAs : forall k, k < n * n' -> WF_Matrix (As k)) : 
  big_kron' ns ms As (n * n') = 
  big_kron'
    (fun k => big_sum (fun i => (ns (k * n' + i))) n')
    (fun k => big_sum (fun i => (ms (k * n' + i))) n')
    (fun k => 
      big_kron' (fun i => (ns (k * n' + i)))
        (fun i => (ms (k * n' + i)))
        (fun i => As (k * n' + i)) 
        n')
    n.
Proof.
  rewrite big_kron'_double_kron'_indexed by 
    (intros k Hk l Hl; apply HAs; show_moddy_lt).
  rewrite Nsum_constant.
  apply big_kron'_eq_bounded_dims;
  intros k Hk;
  rewrite Nsum_index_constant, Nsum_offset_constant, 
    Nat.mul_comm, <- Nat.div_mod_eq by lia; reflexivity.
Qed.

Lemma big_stack_mult ns ms zxs n n' : 
  big_stack ns ms zxs (n * n') ∝
  cast _ _ (big_stack_mult_prf ns n n') 
    (big_stack_mult_prf ms n n')
  (big_stack 
    (fun k => big_sum (fun i => (ns (k * n' + i))) n')
    (fun k => big_sum (fun i => (ms (k * n' + i))) n')
    (fun k => 
      big_stack (fun i => (ns (k * n' + i)))
        (fun i => (ms (k * n' + i)))
        (fun i => zxs (k * n' + i)) 
        n')
    n).
Proof.
  prop_exists_nonzero 1%R.
  rewrite Mscale_1_l.
  simpl_cast_semantics.
  rewrite 2!big_stack_semantics.
  rewrite big_kron'_mult by (intros; auto_wf).
  erewrite big_kron'_eq_bounded; [reflexivity|].
  intros k Hk.
  cbn.
  now rewrite big_stack_semantics.
Qed.


Lemma big_stack_split_add ns ms zxs n m :
  big_stack ns ms zxs (n + m) ∝
  cast _ _ (big_sum_sum _ _ _) (big_sum_sum _ _ _)
    (big_stack ns ms zxs n ↕ 
     big_stack (fun k => ns (n + k)) (fun k => ms (n + k))
        (fun k => zxs (n + k)) m).
Proof.
  prop_exists_nonzero 1%R.
  rewrite Mscale_1_l.
  simpl_cast_semantics.
  cbn [ZX_semantics].
  rewrite 3!big_stack_semantics.
  apply big_kron'_split_add.
  intros; auto_wf.
Qed.

Lemma big_stack_join_add ns0 ms0 ns1 ms1 zxs0 zxs1 n m  : 
  big_stack ns0 ms0 zxs0 n ↕
  big_stack ns1 ms1 zxs1 m ∝
  cast _ _ (eq_sym (big_sum_if_lt _ _ _ _)) 
    (eq_sym (big_sum_if_lt _ _ _ _))
    (big_stack (fun k => if k <? n then ns0 k else ns1 (k - n))
      (fun k => if k <? n then ms0 k else ms1 (k - n))
      (fun k => if k <? n as a return 
        (ZX (if a then ns0 k else ns1 (k - n))
         (if a then ms0 k else ms1 (k - n)))
        then zxs0 k else zxs1 (k - n)) (n + m)).
Proof.
  rewrite big_stack_split_add.
  rewrite cast_contract_eq.
  rewrite cast_stack_distribute_fwd_l.
  apply stack_simplify; 
  (apply big_stack_simplify_casted_abs;
  [intros k Hk; bdestruct_one; f_equal; lia..|]).
  - intros k ? ? Hk.
    bdestruct_one; [|lia].
    now rewrite cast_id.
  - intros k ? ? Hk.
    bdestruct_one; [lia|].
    apply ZX_prop_by_mat_prop.
    simpl_cast_semantics.
    now rewrite add_sub'.
Unshelve.
  all: apply big_sum_eq_bounded; 
    intros k Hk; bdestruct_one; f_equal; lia.
Qed.

Lemma big_stack_empty n zxs (Hzxs : forall k, k < n -> zxs k ∝ ⦰) : 
  big_stack (fun _ => 0) (fun _ => 0) zxs n ∝
  cast _ _ (big_sum_0 _ _ (fun k => eq_refl))
    (big_sum_0 _ _ (fun k => eq_refl)) 
    ⦰.
Proof.
  induction n.
  - now rewrite cast_id.
  - cbn.
    rewrite IHn, Hzxs by auto.
    clean_eqns rewrite stack_empty_r, cast_contract_eq.
    cast_irrelevance.
Qed.





















(* Lemma enlarge_permutation_big_kron'_natural_r (ns ms : nat -> nat) 
  As (n : nat) (HAs : forall k, k < n -> WF_Matrix (As k)) 
  f (Hf : permutation n f) : 
  perm_to_matrix (big_sum ns n) 
    (enlarge_permutation n f ns) × 
    big_kron' ns ms As n =
  @Mmult (2^(big_sum ns n)) (2^(big_sum ms n)) (2^(big_sum ms n))
  (big_kron' (ns ∘ perm_inv' n f) (ms ∘ perm_inv' n f) 
    (fun i => As (perm_inv' n f i)) n)
  (perm_to_matrix (big_sum ms n) 
    (enlarge_permutation n f ns)).
Proof.
  apply transpose_matrices.
  rewrite 2!Mmult_transpose.
  rewrite big_kron'_transpose, perm_to_matrix_transpose_eq by auto_perm.
  rewrite <- perm_inv'_eq.
  rewrite enlarge_permutation_inv' by auto. *)

Definition big_zx_of_permutation_l 
  n (f ns : nat -> nat) (Hf : permutation n f) : 
  ZX (big_sum (ns ∘ f) n) (big_sum ns n) :=
  cast _ _ (eq_sym (Nsum_reorder n ns f Hf)) eq_refl 
  (zx_of_perm (big_sum ns n) (enlarge_permutation n f ns)).


Definition big_zx_of_permutation_r
  n (f ns : nat -> nat) (Hf : permutation n f) : 
  ZX (big_sum ns n) (big_sum (ns ∘ f) n) :=
  cast _ _ (Nsum_reorder n ns f Hf) eq_refl
  (zx_of_perm (big_sum (ns ∘ f) n) 
    (enlarge_permutation n (perm_inv' n f) (ns ∘ f))).

Lemma big_zx_of_permutation_l_semantics n f ns Hf : 
  ⟦ big_zx_of_permutation_l n f ns Hf ⟧ =
  perm_to_matrix (big_sum ns n) (enlarge_permutation n f ns).
Proof.
  unfold big_zx_of_permutation_l.
  apply zx_of_perm_casted_semantics.
  auto_perm.
Qed.

Lemma big_zx_of_permutation_r_semantics n f ns Hf : 
  ⟦ big_zx_of_permutation_r n f ns Hf ⟧ =
  perm_to_matrix (big_sum (ns ∘ f) n) 
    (enlarge_permutation n (perm_inv' n f) (ns ∘ f)).
Proof.
  unfold big_zx_of_permutation_r.
  apply zx_of_perm_casted_semantics.
  auto_perm.
Qed.

Open Scope ZX_scope.

Lemma big_zx_of_permutation_l_transpose n ns f Hf : 
  (big_zx_of_permutation_l n f ns Hf) ⊤ ∝
  big_zx_of_permutation_r n f ns Hf.
Proof.
  prop_exists_nonzero 1%R.
  rewrite semantics_transpose_comm, Mscale_1_l, 
  (big_zx_of_permutation_l_semantics n f), 
  (big_zx_of_permutation_r_semantics n f).
  rewrite <- Nsum_reorder by auto.
  rewrite perm_to_matrix_transpose_eq by auto_perm.
  apply perm_to_matrix_eq_of_perm_eq.
  now rewrite enlarge_permutation_inv, perm_inv'_eq.
Qed.

Lemma big_zx_of_permutation_r_transpose n ns f Hf : 
  (big_zx_of_permutation_r n f ns Hf) ⊤ ∝
  big_zx_of_permutation_l n f ns Hf.
Proof.
  rewrite <- (big_zx_of_permutation_l_transpose n ns f Hf).
  now rewrite Proportional.transpose_involutive.
Qed.


Lemma big_zx_of_permutation_l_natural n ns ms zxs f Hf : 
  big_zx_of_permutation_l n f ns Hf ⟷ 
  big_stack ns ms zxs n ∝
  big_stack (ns ∘ f) (ms ∘ f) (fun k => zxs (f k)) n ⟷ 
  big_zx_of_permutation_l n f ms Hf.
Proof.
  prop_exists_nonzero 1%R.
  rewrite Mscale_1_l.
  cbn [ZX_semantics].
  rewrite (big_zx_of_permutation_l_semantics n f).
  rewrite big_stack_semantics.
  restore_dims.
  rewrite enlarge_permutation_big_kron'_natural
    by (assumption + intros; auto_wf).
  rewrite (big_zx_of_permutation_l_semantics n f).
  rewrite big_stack_semantics.
  f_equal;
  now rewrite <- Nsum_reorder by auto.
Qed.

Lemma big_zx_of_permutation_r_natural n ns ms zxs f Hf : 
  big_stack ns ms zxs n ⟷ 
  big_zx_of_permutation_r n f ms Hf ∝
  big_zx_of_permutation_r n f ns Hf ⟷ 
  big_stack (ns ∘ f) (ms ∘ f) (fun k => zxs (f k)) n.
Proof.
  apply transpose_diagrams.
  cbn.
  rewrite 2!big_zx_of_permutation_r_transpose, 2!big_stack_transpose.
  now rewrite big_zx_of_permutation_l_natural.
Qed.


Lemma triangle_number_exact n : 
  n * (n - 1) / 2 * 2 = n * (n - 1).
Proof.
  pose proof (Nat.div_mod_eq (n * (n - 1)) 2).
  enough ((n * (n - 1)) mod 2 = 0) by lia.
  bdestruct (n =? 0); [now subst|].
  bdestruct (n =? 1); [now subst|].
  rewrite <- Nat.eqb_eq.
  rewrite <- even_eqb.
  rewrite Nat.even_mul, Nat.even_sub by lia.
  cbn.
  now destruct (Nat.even n).
Qed.
  

Lemma triangle_number n : 
  big_sum idn n = (n * (n - 1)) / 2.
Proof.
  induction n; [reflexivity|].
  cbn [big_sum nat_is_monoid Gplus].
  rewrite IHn.
  rewrite <- Nat.div_add by lia.
  f_equal.
  nia.
Qed.

Lemma triangle_number' n : 
  big_sum idn (S n) = (n + 1) * n / 2.
Proof.
  rewrite triangle_number.
  f_equal; lia.
Qed.

Lemma Nsum_permutation n f (Hf : permutation n f) : 
  big_sum f n = (n * (n - 1)) / 2.
Proof.
  rewrite <- (compose_idn_l f).
  rewrite <- Nsum_reorder by auto.
  apply triangle_number.
Qed.

Lemma Nsum_reflect_perm n k (Hk : k < n) : 
  big_sum (reflect_perm n) k = 
  n * k - ((k + 1) * k / 2).
Proof.
  replace ((k + 1) * k) with ((S k) * (S k - 1)) by lia.
  rewrite <- triangle_number.
  induction k; [cbn; lia|].
  cbn [big_sum Gplus nat_is_monoid].
  rewrite IHk by lia.
  cbn [big_sum Gplus nat_is_monoid].
  rewrite reflect_perm_defn by lia.
  enough (big_sum idn k + k <= n * k) by nia.
  change (big_sum idn k + k) with (big_sum idn (1 + k)).
  rewrite big_sum_sum.
  rewrite Nat.add_0_l.
  rewrite <- times_n_nat, <- big_sum_constant.
  apply Nsum_le.
  lia.
Qed.



(* Enumerating the edges of the complete graph on n vertices *)
Definition idx_to_edge n k : nat * nat :=
  let i := Nsum_index n (reflect_perm n) k in 
  let j := Nsum_offset n (reflect_perm n) k in
  (i, i + S j).

Definition edge_to_idx n ij : nat := 
  big_sum (reflect_perm n) (fst ij) + (snd ij - S (fst ij)).

Lemma idx_to_edge_to_idx n k (Hk : k < n * (n - 1) / 2) : 
  edge_to_idx n (idx_to_edge n k) = k.
Proof.
  pose proof (Nsum_permutation _ _ (reflect_perm_permutation n)).
  pose proof (Nsum_index_offset_spec n (reflect_perm n) k ltac:(lia)).
  unfold idx_to_edge, edge_to_idx.
  cbn.
  lia.
Qed.

Lemma edge_to_idx_to_edge n ij (Hi : fst ij < snd ij) (Hj : snd ij < n) : 
  idx_to_edge n (edge_to_idx n ij) = ij.
Proof.
  unfold edge_to_idx.
  unfold idx_to_edge.
  rewrite Nsum_index_add_big_sum_l, Nsum_offset_add_big_sum_l 
    by (unfold reflect_perm; bdestructΩ').
  destruct ij.
  cbn in *.
  f_equal.
  lia.
Qed.

Lemma idx_to_edge_spec n k (Hk : k < n * (n - 1) / 2) : 
  fst (idx_to_edge n k) < snd (idx_to_edge n k) /\
  snd (idx_to_edge n k) < n.
Proof.
  unfold idx_to_edge.
  cbn [fst snd].
  split; [lia|].
  assert (n <> 0) by (intros ->; cbn in *; lia).
  pose proof (Nsum_permutation _ _ (reflect_perm_permutation n)).
  pose proof (Nsum_index_offset_spec n (reflect_perm n) k ltac:(lia)).
  pose proof (Nsum_index_bounded n (reflect_perm n) k ltac:(auto)).
  rewrite reflect_perm_defn in * by auto.
  lia.
Qed.

Lemma edge_to_idx_bounded n ij (Hi : fst ij < snd ij) (Hj : snd ij < n) : 
  edge_to_idx n ij < n * (n - 1) / 2.
Proof.
  destruct ij as [i j].
  unfold edge_to_idx.
  cbn [fst snd] in *.
  rewrite <- (Nsum_permutation n (reflect_perm n)) by auto_perm.
  replace (big_sum (reflect_perm n) n) 
    with (big_sum (reflect_perm n) (i + (n - i))) by (f_equal; lia).
  rewrite big_sum_sum.
  cbn [Gplus nat_is_monoid].
  enough ((j - S i) < big_sum (fun k => reflect_perm n (i + k)) (n - i))
    by lia.
  rewrite (big_sum_eq_bounded _ (reflect_perm (n - i))).
  2: {
    intros k Hk.
    rewrite 2!reflect_perm_defn by lia.
    lia.
  }
  rewrite Nsum_permutation by auto_perm.
  bdestruct (i =? n - 2).
  - subst.
    replace j with (n - 1) by lia.
    replace (n - (n - 2)) with 2 by lia.
    cbn; lia.
  - apply (Nat.lt_le_trans _ ((n - i) * ((n - i - 1) / 2))); [|
    apply Nat.div_mul_le; lia].
    apply (Nat.lt_le_trans _ (n - i)); [lia|].
    enough ((n - i - 1) / 2 <> 0) by nia.
    rewrite Nat.div_small_iff by lia.
    lia.
Qed.


Definition wire_to_ordered_edge n k : nat * nat :=
  let i := k / (n - 1) in 
  let j := k mod (n - 1) in 
  if j <? i 
  then (i, j)
  else (i, S j).

Definition ordered_edge_to_wire n ij : nat :=
  if snd ij <? fst ij 
  then fst ij * (n - 1) + snd ij 
  else (fst ij) * (n - 1) + (snd ij - 1).

Lemma wire_to_ordered_edge_to_wire n k (Hk : k < n * (n - 1)) : 
  ordered_edge_to_wire n (wire_to_ordered_edge n k) = k.
Proof.
  unfold wire_to_ordered_edge, ordered_edge_to_wire.
  pose proof (Nat.div_mod_eq k (n - 1)).
  bdestruct_one; cbn; simplify_bools_lia_one_kernel;
  lia.
Qed.

Lemma ordered_edge_to_wire_to_ordered_edge n ij 
  (Hi : fst ij < n) (Hj : snd ij < n) (Hij : fst ij <> snd ij) : 
  wire_to_ordered_edge n (ordered_edge_to_wire n ij) = ij.
Proof.
  unfold ordered_edge_to_wire, wire_to_ordered_edge.
  bdestruct_one;
  rewrite mod_add_l, Nat.div_add_l, Nat.div_small, Nat.mod_small by lia; 
  simplify_bools_lia_one_kernel; 
  destruct ij; 
  cbn [fst snd] in *; f_equal; lia.
Qed.

Lemma wire_to_ordered_edge_spec n k (Hk : k < n * (n - 1)) : 
  fst (wire_to_ordered_edge n k) < n /\
  snd (wire_to_ordered_edge n k) < n /\
  fst (wire_to_ordered_edge n k) <> snd (wire_to_ordered_edge n k). 
Proof.
  assert (2 <= n) by lia.
  unfold wire_to_ordered_edge.
  assert (k / (n - 1) < n) by show_moddy_lt.
  pose proof (Nat.mod_upper_bound k (n - 1) ltac:(lia)).
  bdestruct_one; 
  cbn [fst snd]; lia.
Qed.

Lemma ordered_edge_to_wire_bounded n ij 
  (Hi : fst ij < n) (Hj : snd ij < n) (Hij : fst ij <> snd ij) : 
  ordered_edge_to_wire n ij < n * (n - 1).
Proof.
  unfold ordered_edge_to_wire.
  bdestruct_one; show_moddy_lt.
Qed.

Definition block_to_pairs_perm n := 
  fun k => if n * (n - 1) <=? k then k else
  let ij := wire_to_ordered_edge n k in 
  if fst ij <? snd ij 
  then (* We are the input *)
    (edge_to_idx n ij) * 2 
  else (* We are the output *)
    (edge_to_idx n (snd ij, fst ij)) * 2 + 1.

Definition pairs_to_block_perm n := 
  fun k => if n * (n - 1) <=? k then k else
  let idx := k / 2 in 
  let side := k mod 2 in 
  let ij := idx_to_edge n idx in 
  if side =? 0 then 
    ordered_edge_to_wire n ij
  else
    ordered_edge_to_wire n (snd ij, fst ij).


Lemma block_to_pairs_WF n : 
  WF_Perm (n * (n - 1)) (block_to_pairs_perm n).
Proof.
  intros k Hk.
  unfold block_to_pairs_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma pairs_to_block_WF n : 
  WF_Perm (n * (n - 1)) (pairs_to_block_perm n).
Proof.
  intros k Hk.
  unfold pairs_to_block_perm.
  now simplify_bools_lia_one_kernel.
Qed.

#[export] Hint Resolve block_to_pairs_WF pairs_to_block_WF : WF_Perm_db.


Lemma block_to_pairs_defn n : 
  perm_eq (n * (n - 1)) 
    (block_to_pairs_perm n) 
    (fun k => let ij := wire_to_ordered_edge n k in 
    if fst ij <? snd ij 
    then (edge_to_idx n ij) * 2 
    else (edge_to_idx n (snd ij, fst ij)) * 2 + 1).
Proof.
  intros k Hk.
  unfold block_to_pairs_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma pairs_to_block_defn n : 
  perm_eq (n * (n - 1)) 
    (pairs_to_block_perm n) 
    (fun k => let idx := k / 2 in let side := k mod 2 in 
    let ij := idx_to_edge n idx in 
    if side =? 0 then ordered_edge_to_wire n ij
    else ordered_edge_to_wire n (snd ij, fst ij)).
Proof.
  intros k Hk.
  unfold pairs_to_block_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma block_to_pairs_perm_bounded n : 
  perm_bounded (n * (n - 1))
    (block_to_pairs_perm n).
Proof.
  intros k Hk.
  rewrite block_to_pairs_defn by lia.
  unfold wire_to_ordered_edge.
  assert (k / (n - 1) < n) by show_moddy_lt.
  pose proof (Nat.mod_upper_bound k (n - 1) ltac:(lia)).
  bdestruct_one;
  cbn [fst snd]; simplify_bools_lia_one_kernel.
  - pose proof (edge_to_idx_bounded n (k mod (n - 1), k / (n - 1))
      ltac:(cbn [fst snd]; lia) ltac:(cbn [fst snd]; lia)).
    rewrite <- triangle_number_exact.
    apply (Nat.le_lt_trans _ ((n * (n - 1) / 2 - 1) * 2 + 1)); [|nia].
    apply Nat.add_le_mono_r.
    apply Nat.mul_le_mono_r.
    lia.
  - pose proof (edge_to_idx_bounded n (k / (n - 1), S (k mod (n - 1)))
      ltac:(cbn [fst snd]; lia) ltac:(cbn [fst snd]; lia)).
    rewrite <- triangle_number_exact.
    lia.
Qed.

Lemma pairs_to_block_perm_bounded n : 
  perm_bounded (n * (n - 1))
    (pairs_to_block_perm n).
Proof.
  intros k Hk.
  rewrite pairs_to_block_defn by lia.
  cbn zeta.
  pose proof (idx_to_edge_spec n (k / 2) 
    ltac:(apply Nat.Div0.div_lt_upper_bound; 
      rewrite Nat.mul_comm, triangle_number_exact; lia)).
  bdestruct_one;
  apply ordered_edge_to_wire_bounded; 
  cbn [fst snd]; lia.
Qed.

#[export] Hint Resolve pairs_to_block_perm_bounded
  block_to_pairs_perm_bounded : perm_bounded_db.


Lemma pairs_to_block_to_pairs_inv n : 
  block_to_pairs_perm n ∘ pairs_to_block_perm n = idn.
Proof.
  eq_by_WF_perm_eq (n * (n - 1)).
  rewrite block_to_pairs_defn, pairs_to_block_defn.
  intros k Hk.
  assert (k / 2 < n * (n - 1) / 2) by 
    (apply Nat.Div0.div_lt_upper_bound; 
    rewrite Nat.mul_comm, triangle_number_exact; lia).
  pose proof (idx_to_edge_spec n (k / 2) ltac:(auto)).
  unfold compose.
  bdestruct (k mod 2 =? 0);
  rewrite ordered_edge_to_wire_to_ordered_edge by (cbn [fst snd]; lia);
  cbn [fst snd];
  bdestructΩ'.
  - rewrite idx_to_edge_to_idx by auto.
    pose proof (Nat.div_mod_eq k 2); lia.
  - rewrite <- surjective_pairing.
    rewrite idx_to_edge_to_idx by auto.
    pose proof (Nat.mod_upper_bound k 2).
    pose proof (Nat.div_mod_eq k 2); lia.
Qed.


Lemma pairs_to_block_permutation n : 
  permutation (n * (n - 1)) (pairs_to_block_perm n).
Proof.
  apply permutation_iff_surjective.
  apply surjective_of_injective_and_bounded.
  split; [|auto_perm].
  intros k l Hk Hl.
  intros Heq.
  apply (f_equal (block_to_pairs_perm n)) in Heq.
  pose proof (equal_f (pairs_to_block_to_pairs_inv n) k).
  pose proof (equal_f (pairs_to_block_to_pairs_inv n) l).
  unfold compose in *.
  congruence.
Qed.

#[export] Hint Resolve pairs_to_block_permutation : perm_db.

Lemma pairs_to_block_perm_inv n : 
  perm_eq (n * (n - 1)) 
    (perm_inv (n * (n - 1)) (pairs_to_block_perm n))
    (block_to_pairs_perm n).
Proof.
  rewrite <- (compose_idn_l (perm_inv _ _)).
  rewrite compose_perm_inv_r by auto_perm.
  now rewrite pairs_to_block_to_pairs_inv.
Qed.

Lemma block_to_pairs_permutation n : 
  permutation (n * (n - 1)) (block_to_pairs_perm n).
Proof.
  rewrite <- pairs_to_block_perm_inv.
  auto_perm.
Qed.

#[export] Hint Resolve block_to_pairs_permutation : perm_db.

Lemma block_to_pairs_perm_inv n : 
  perm_eq (n * (n - 1)) 
    (perm_inv (n * (n - 1)) (block_to_pairs_perm n))
    (pairs_to_block_perm n).
Proof.
  rewrite perm_inv_perm_eq_iff by auto_perm.
  now rewrite pairs_to_block_perm_inv.
Qed.

Lemma block_to_pairs_to_block_inv n : 
  pairs_to_block_perm n ∘ block_to_pairs_perm n = idn.
Proof.
  eq_by_WF_perm_eq (n * (n - 1)).
  rewrite <- block_to_pairs_perm_inv.
  auto_perm.
Qed.


Notation "'b2ZX' b n m α" := 
    (if b%bool 
    then X n%nat m%nat α%R 
    else Z n%nat m%nat α%R) 
  (at level 10, b at level 9, n at level 9, 
    m at level 9, α at level 9): ZX_scope.

Lemma ZX_complete_stack_prf_1 n : 
  n = big_sum (fun _ => 1) n.
Proof.
  rewrite big_sum_constant, times_n_nat; lia.
Qed.

Lemma ZX_complete_stack_prf_2 n : 
  n * (n - 1) = big_sum (fun _ => n - 1) n.
Proof.
  rewrite big_sum_constant, times_n_nat; lia.
Qed.

Definition ZX_complete_stack n (αs : nat -> R) (color : nat -> bool) : 
  ZX n (n * (n - 1)) := 
  cast _ _ (ZX_complete_stack_prf_1 n) (ZX_complete_stack_prf_2 n) 
    (big_stack (fun _ => 1) (fun _ => n - 1)
      (fun k => b2ZX (color k) 1 (n - 1) (αs k)) n).

Definition ZX_complete_perm n : ZX (n * (n - 1)) ((n * (n - 1) / 2) * 2) :=
  cast _ _ eq_refl (triangle_number_exact n)
    (zx_of_perm (n * (n - 1)) (pairs_to_block_perm n)).

Lemma ZX_complete_connections_prf_1 n : 
  ((n * (n - 1) / 2) * 2) = big_sum (fun _ => 2) (n * (n - 1) / 2).
Proof.
  rewrite big_sum_constant, times_n_nat; lia.
Qed.

Lemma ZX_complete_connections_prf_2 n : 
  0 = big_sum (fun _ => 0) (n * (n - 1) / 2).
Proof.
  now rewrite big_sum_0.
Qed.

Definition ZX_complete_connections n (deg : nat * nat -> nat) 
  (color : nat -> bool) : ZX ((n * (n - 1) / 2) * 2) 0 :=
  cast _ _ (ZX_complete_connections_prf_1 n)
    (ZX_complete_connections_prf_2 n)
    (big_stack (fun _ => 2) (fun _ => 0)
      (fun k => 
        let ij := idx_to_edge n k in 
        (b2ZX (color (fst ij)) 1 (deg ij) 0) ↕
        (b2ZX (color (snd ij)) 1 (deg ij) 0) ⟷
        n_cup (deg ij)
        )
      (n * (n - 1) / 2)).



Definition ZX_connections_stack n (deg : nat * nat -> nat)
  (color : nat -> bool) : 
  ZX ((n * (n - 1) / 2) * 2) (big_sum (
    Nat.double ∘ deg ∘ (fun k => idx_to_edge n k)) 
    (n * (n - 1) / 2)) :=
  cast _ _ (ZX_complete_connections_prf_1 n)
    eq_refl
    (big_stack (fun _ => 2) (Nat.double ∘ deg ∘ 
      (fun k => idx_to_edge n k))
      (fun k => 
        let ij := idx_to_edge n k in 
        (b2ZX (color (fst ij)) 1 (deg ij) 0) ↕
        (b2ZX (color (snd ij)) 1 (deg ij) 0))
      (n * (n - 1) / 2)).

Definition ZX_caps_stack n (deg : nat * nat -> nat) :  
  ZX (big_sum (Nat.double ∘ deg ∘ (idx_to_edge n)) 
    (n * (n - 1) / 2)) 0 :=
  cast _ _ eq_refl (ZX_complete_connections_prf_2 n)
    (big_stack (Nat.double ∘ deg ∘ (idx_to_edge n))
      (fun _ => 0)
      (fun k => 
        n_cup (deg (idx_to_edge n k)))
      (n * (n - 1) / 2)).


Definition ZX_complete_form n color αs deg : ZX n 0 :=
  ZX_complete_stack n αs color ⟷ 
  ZX_complete_perm n ⟷ ZX_complete_connections n deg color.

(* FIXME: Move this general theory above the graph specifics *)



Lemma enlarge_permutation_1 n f : 
  perm_eq n (enlarge_permutation n f (fun _ => 1)) (perm_inv' n f).
Proof.
  rewrite <- (Nsum_1 n) at 1.
  rewrite enlarge_permutation_defn.
  rewrite (Nsum_1 n).
  intros k Hk.
  rewrite Nsum_offset_1 by auto.
  rewrite Nsum_1, Nsum_index_1 by auto.
  apply Nat.add_0_r.
Qed.

(* FIXME: Move to by definitions *)

Lemma big_zx_of_permutation_l_zxperm n f ns Hf : 
  ZXperm (big_zx_of_permutation_l n f ns Hf).
Proof.
  unfold big_zx_of_permutation_l.
  auto_zxperm.
Qed.

Lemma big_zx_of_permutation_r_zxperm n f ns Hf : 
  ZXperm (big_zx_of_permutation_r n f ns Hf).
Proof.
  unfold big_zx_of_permutation_r.
  auto_zxperm.
Qed.

#[export] Hint Resolve big_zx_of_permutation_l_zxperm
  big_zx_of_permutation_r_zxperm : zxperm_db.

#[export] Hint Extern 0 (ZXperm (big_zx_of_permutation_l ?n ?f ?ns ?Hf)) =>
  exact (big_zx_of_permutation_l_zxperm n f ns Hf) : zxperm_db.



Lemma zxperm_to_big_zx_of_permutation_l {n m} (zx : ZX n m) 
  (Hzx : ZXperm zx) : 
  zx ∝ 
  cast n m (eq_sym (Nsum_1 _)) 
  (eq_sym (eq_trans (Nsum_1 _) (zxperm_square zx Hzx)))
  (big_zx_of_permutation_l n (perm_inv' n (perm_of_zx zx)) (fun _ => 1) 
    (perm_inv'_permutation _ _ (perm_of_zx_permutation zx Hzx))).
Proof.
  pose proof (zxperm_square zx Hzx) as Hnm.
  revert zx Hzx.
  subst m.
  intros zx Hzx.
  unfold big_zx_of_permutation_l.
  rewrite cast_contract_eq.
  by_perm_eq.
  rewrite enlarge_permutation_1.
  rewrite perm_of_zx_of_perm_eq by auto_perm.
  now rewrite perm_inv'_perm_inv by auto_perm.
Qed.

Lemma zxperm_to_big_zx_of_permutation_r {n m} (zx : ZX n m) 
  (Hzx : ZXperm zx) : 
  zx ∝ 
  cast n m (eq_sym (Nsum_1 _)) 
  (eq_sym (eq_trans (Nsum_1 _) (zxperm_square zx Hzx)))
  (big_zx_of_permutation_r n (perm_of_zx zx) (fun _ => 1) 
    (perm_of_zx_permutation zx Hzx)).
Proof.
  pose proof (zxperm_square zx Hzx) as Hnm.
  revert zx Hzx.
  subst m.
  intros zx Hzx.
  unfold big_zx_of_permutation_r.
  rewrite cast_contract_eq.
  by_perm_eq.
  rewrite enlarge_permutation_1.
  rewrite perm_of_zx_of_perm_eq by auto_perm.
  now rewrite perm_inv'_perm_inv by auto_perm.
Qed.

Lemma zx_of_perm_to_big_zx_of_permutation_l n f (Hf : permutation n f) : 
  zx_of_perm n f ∝
  cast n n (eq_sym (Nsum_1 _)) 
  (eq_sym (Nsum_1 _))
  (big_zx_of_permutation_l n (perm_inv' n f) (fun _ => 1) 
    (perm_inv'_permutation _ _ Hf)).
Proof.
  rewrite (zxperm_to_big_zx_of_permutation_l _ (zx_of_perm_zxperm n f)).
  apply cast_simplify.
  by_perm_eq.
Qed.

Lemma zx_of_perm_to_big_zx_of_permutation_r n f (Hf : permutation n f) : 
  zx_of_perm n f ∝
  cast n n (eq_sym (Nsum_1 _)) 
  (eq_sym (Nsum_1 _))
  (big_zx_of_permutation_r n f (fun _ => 1) Hf).
Proof.
  rewrite (zxperm_to_big_zx_of_permutation_r _ (zx_of_perm_zxperm n f)).
  apply cast_simplify.
  unfold big_zx_of_permutation_r.
  apply cast_simplify.
  unfold compose.
  now rewrite perm_of_zx_of_perm_eq by auto.
Qed.



Lemma ZX_connections_stack_alt_prf n deg : 
  big_sum (Nat.double ∘ deg ∘ idx_to_edge n) (n * (n - 1) / 2) =
  big_sum (fun k => deg (idx_to_edge n (k / 2))) (n * (n - 1)).
Proof.
  rewrite Combinators.compose_assoc.
  unfold Nat.double.
  unfold compose at 1.
  rewrite big_stack_stack_prf.
  rewrite triangle_number_exact.
  apply big_sum_eq_bounded.
  intros k Hk.
  now rewrite Tauto.if_same.
Qed.

Lemma ZX_connections_stack_alt n color deg : 
  ZX_connections_stack n deg color ∝ 
  cast _ _ 
  (eq_trans (triangle_number_exact _) (eq_sym (Nsum_1 _)))
  (ZX_connections_stack_alt_prf n deg)
  (big_stack (fun _ => 1)
  (fun k => deg (idx_to_edge n (k / 2)))
  (fun k => 
    let ij := idx_to_edge n (k / 2) in 
   if k mod 2 =? 0 
   then (if color (fst ij) then X 1 (deg ij) 0 else Z 1 (deg ij) 0)
   else (if color (snd ij) then X 1 (deg ij) 0 else Z 1 (deg ij) 0))  
  (n * (n - 1)) ).
Proof.
  unfold ZX_connections_stack.
  change (Nat.double ∘ deg ∘ (fun k => idx_to_edge n k))
    with (fun k => (deg ∘ idx_to_edge n) k + (deg ∘ idx_to_edge n) k).
  etransitivity.
  1: {
    apply cast_mor.
    apply (big_stack_stack (fun _=>1) (fun _=>1)
      (deg ∘ idx_to_edge n) (deg ∘ idx_to_edge n)
      (fun k => if color (fst (idx_to_edge n k))
      then X 1 (deg (idx_to_edge n k)) 0
      else Z 1 (deg (idx_to_edge n k)) 0)
      (fun k => if color (snd (idx_to_edge n k))
      then X 1 (deg (idx_to_edge n k)) 0
      else Z 1 (deg (idx_to_edge n k)) 0)).
  }
  rewrite cast_contract_eq.
  prop_exists_nonzero 1%R.
  rewrite Mscale_1_l.
  simpl_cast_semantics.
  rewrite 2!big_stack_semantics.
  f_equal;
  [apply functional_extensionality_dep; intros k..|apply triangle_number_exact];
  [now rewrite Tauto.if_same..|].
  now destruct (k mod 2 =? 0).
Qed.






Lemma ZX_complete_connections_split n color deg : 
  ZX_complete_connections n deg color ∝ 
  ZX_connections_stack n deg color ⟷ ZX_caps_stack n deg.
Proof.
  unfold ZX_connections_stack, ZX_caps_stack.
  rewrite cast_compose_eq_mid_join.
  rewrite big_stack_compose.
  now apply cast_simplify.
Qed.

Lemma ZX_complete_form_pullthrough_1 n color αs deg : 
  ZX_complete_form n color αs deg ∝ 
  ZX_complete_stack n αs color ⟷
  cast _ _ (eq_sym (Nsum_1 _)) 
  (ZX_connections_stack_alt_prf n deg)
  (big_stack (fun _ => 1)
  ((fun k => deg (idx_to_edge n (k / 2)))
   ∘ perm_inv' (n * (n - 1)) (pairs_to_block_perm n))
  (fun k =>
   (fun k0 : nat =>
    if k0 mod 2 =? 0
    then
     if color (fst (idx_to_edge n (k0 / 2)))
     then X 1 (deg (idx_to_edge n (k0 / 2))) 0
     else Z 1 (deg (idx_to_edge n (k0 / 2))) 0
    else
     if color (snd (idx_to_edge n (k0 / 2)))
     then X 1 (deg (idx_to_edge n (k0 / 2))) 0
     else Z 1 (deg (idx_to_edge n (k0 / 2))) 0)
     (perm_inv' (n * (n - 1)) (pairs_to_block_perm n) k))
  (n * (n - 1))
⟷ big_zx_of_permutation_l (n * (n - 1))
    (perm_inv' (n * (n - 1)) (pairs_to_block_perm n))
    (fun k : nat => deg (idx_to_edge n (k / 2)))
    (perm_inv'_permutation (n * (n - 1)) 
       (pairs_to_block_perm n) (pairs_to_block_permutation n)))
  ⟷ ZX_caps_stack n deg.
Proof.
  unfold ZX_complete_form.
  rewrite compose_assoc.
  rewrite ZX_complete_connections_split.
  rewrite <- (compose_assoc (ZX_complete_perm n)).
  rewrite <- compose_assoc.
  apply compose_simplify; [|reflexivity].
  apply compose_simplify; [reflexivity|].
  unfold ZX_complete_perm.
  rewrite ZX_connections_stack_alt.
  unshelve rewrite zx_of_perm_to_big_zx_of_permutation_l;
  [auto_perm|].
  rewrite cast_contract_eq.
  rewrite cast_compose_eq_mid_join.
  unfold compose.
  apply cast_simplify.
  apply (big_zx_of_permutation_l_natural (n * (n - 1)) (fun _ => 1)).
Qed.


Lemma Z_spider_big_fusion ns ms n n0 α αs 
  (Hns : forall k, k < n -> ns k <> 0) :
  Z n0 _ α ⟷ big_stack ns ms (fun k => Z (ns k) (ms k) (αs k)) n ∝
  Z n0 _ (α + big_sum αs n).
Proof.
  revert n0 α.
  induction n; intros n0 α.
  - cbn.
    rewrite Rplus_0_r.
    now cleanup_zx.
  - cbn.
    rewrite Z_add_r_base_rot.
    rewrite compose_assoc, <- (@stack_compose_distr 1 _ _ 1).
    rewrite IHn by auto.
    pose proof (Hns n ltac:(auto)).
    destruct (ns n); [easy|].
    rewrite Z_absolute_fusion, Rplus_0_l.
    rewrite <- Z_add_r.
    replace (big_sum αs n + α + (0 + αs n))%R
      with (α + (big_sum αs n + αs n))%R by lra.
    reflexivity.
Qed.

Lemma Z_spider_big_fusion_0 ns ms n n0 α 
  (Hns : forall k, k < n -> ns k <> 0) :
  Z n0 _ α ⟷ big_stack ns ms (fun k => Z (ns k) (ms k) 0) n ∝
  Z n0 _ α.
Proof.
  rewrite Z_spider_big_fusion by auto.
  now rewrite (@big_sum_0 R), Rplus_0_r by auto.
Qed.

Lemma Z_spider_big_fusion_0' ns ms Zs n n0 α 
  (Hns : forall k, k < n -> ns k <> 0)
  (HZs : forall k, k < n -> Zs k ∝ Z _ _ 0) : 
  Z n0 _ α ⟷ big_stack ns ms Zs n ∝
  Z n0 _ α.
Proof.
  rewrite (big_stack_simplify ns ms _ _ n HZs).
  apply Z_spider_big_fusion_0.
  auto.
Qed.



Lemma X_spider_big_fusion ns ms n n0 α αs 
  (Hns : forall k, k < n -> ns k <> 0) :
  X n0 _ α ⟷ big_stack ns ms (fun k => X (ns k) (ms k) (αs k)) n ∝
  X n0 _ (α + big_sum αs n).
Proof. colorswap_of (Z_spider_big_fusion ns ms n n0 α αs Hns). Qed.

Lemma X_spider_big_fusion_0 ns ms n n0 α 
  (Hns : forall k, k < n -> ns k <> 0) :
  X n0 _ α ⟷ big_stack ns ms (fun k => X (ns k) (ms k) 0) n ∝
  X n0 _ α.
Proof. colorswap_of (Z_spider_big_fusion_0 ns ms n n0 α Hns). Qed.

Lemma X_spider_big_fusion_0' ns ms Xs n n0 α 
  (Hns : forall k, k < n -> ns k <> 0) 
  (HXs : forall k, k < n -> Xs k ∝ X _ _ 0) :
  X n0 _ α ⟷ big_stack ns ms Xs n ∝
  X n0 _ α.
Proof.
  colorswap_of (Z_spider_big_fusion_0' ns ms 
  (fun k => ⊙ (Xs k)) n n0 α Hns 
  (fun k Hk => colorswap_compat _ _ _ _ (HXs k Hk))). 
Qed.


Lemma b2ZX_spider_big_fusion (b : bool) ns ms n n0 α αs 
  (Hns : forall k, k < n -> ns k <> 0) :
  b2ZX b n0 _ α ⟷ 
    big_stack ns ms (fun k => b2ZX b (ns k) (ms k) (αs k)) n ∝
  b2ZX b n0 _ (α + big_sum αs n).
Proof.
  destruct b; 
  [now apply X_spider_big_fusion
  |now apply Z_spider_big_fusion].
Qed.

Lemma b2ZX_spider_big_fusion_0 (b : bool) ns ms n n0 α 
  (Hns : forall k, k < n -> ns k <> 0) :
  b2ZX b n0 _ α ⟷ 
    big_stack ns ms (fun k => b2ZX b (ns k) (ms k) 0) n ∝
  b2ZX b n0 _ α.
Proof.
  destruct b; 
  [now apply X_spider_big_fusion_0
  |now apply Z_spider_big_fusion_0].
Qed.

Lemma b2ZX_spider_big_fusion_0' (b : bool) ns ms zxs n n0 α 
  (Hns : forall k, k < n -> ns k <> 0) 
  (Hzxs : forall k, k < n -> zxs k ∝ b2ZX b _ _ 0) :
  b2ZX b n0 _ α ⟷ big_stack ns ms zxs n ∝
  b2ZX b n0 _ α.
Proof.
  destruct b; 
  [now apply X_spider_big_fusion_0'
  |now apply Z_spider_big_fusion_0'].
Qed.

Lemma cast_b2ZX_eq {n n' m m'} prfn prfm (b : bool) α : 
  cast n' m' prfn prfm (b2ZX b n m α) = 
  b2ZX b n' m' α.
Proof. now subst. Qed.

Lemma cast_b2ZX {n n' m m'} prfn prfm (b : bool) α : 
  cast n' m' prfn prfm (b2ZX b n m α) ∝
  b2ZX b n' m' α.
Proof. now subst. Qed.

Lemma b2ZX_if_color_dist (b c c' : bool) n m α : 
  (if b then b2ZX c n m α else b2ZX c' n m α) = 
  b2ZX (if b then c else c') n m α.
Proof.
  now destruct b.
Qed.

Lemma b2ZX_simplify (b b' : bool) n m α α' :
  b = b' -> α = α' -> 
  b2ZX b n m α ∝ b2ZX b' n m α'.
Proof.
  now intros [] [].
Qed.

Lemma edge_to_idx_inj n ij ij' 
  (Hi : fst ij < snd ij) (Hj : snd ij < n)
  (Hi' : fst ij' < snd ij') (Hj' : snd ij' < n) :
  edge_to_idx n ij = edge_to_idx n ij' ->
  ij = ij'.
Proof.
  intros Heq.
  pose proof (edge_to_idx_to_edge n ij Hi Hj).
  pose proof (edge_to_idx_to_edge n ij' Hi' Hj').
  congruence.
Qed.



(* Lemma idx_to_edge_decomp_div2_case1 n k k' 
  (Hk : k < n) (Hk' : k' < n - 1) 
  (Hmod : (k * (n - 1) + k') mod 2 = 0) : 
  idx_to_edge n ((k * (n - 1) + k') / 2) = 
  if k <=? k'
  then wire_to_ordered_edge n (k * (n - 1) + k') 
  else (snd (wire_to_ordered_edge n (k * (n - 1) + k')), 
    fst (wire_to_ordered_edge n (k * (n - 1) + k'))).
Proof.
  assert (Hlt : k * (n - 1) + k' < n * (n - 1)) by show_moddy_lt.
  assert (Hlt' : (k * (n - 1) + k') / 2 < n * (n - 1) / 2) 
    by (apply Nat.Div0.div_lt_upper_bound; 
    rewrite (Nat.mul_comm 2), (triangle_number_exact n); lia).
  bdestructΩ'.
  unfold idx_to_edge.
  unfold wire_to_ordered_edge
  apply (edge_to_idx_inj n);
  [now apply idx_to_edge_spec..| | |];
  [unfold wire_to_ordered_edge;
  rewrite mod_add_l, Nat.div_add_l, 
    Nat.div_small, Nat.mod_small by lia; bdestructΩ';
  cbn [fst snd]; try lia.. |].
  rewrite idx_to_edge_to_idx by auto.
  cbv delta [wire_to_ordered_edge] beta.
  rewrite mod_add_l, Nat.div_add_l, 
    (Nat.div_small k'), Nat.mod_small, Nat.add_0_r by lia.
  cbn zeta.
  bdestruct (k <=? k').
  - replace_bool_lia (k' <? k) false.
    unfold edge_to_idx.
    cbn [fst snd].
    match goal with 
    | H : _ <= _ |- _ => 
      destruct (le_ex_diff_r _ _ H) as (d & Hd);
      clear H
    end.
    subst k'.
    replace (k * (n - 1) + (k + d)) with (k * n + d) in * by nia.
    replace (S (k + d) - S k) with d by lia.
    rewrite Nsum_reflect_perm by auto.
    rewrite <- (Nat.mul_cancel_r _ _ 2 ltac:(easy)).
    rewrite Nat.mul_add_distr_r, Nat.mul_sub_distr_r.
    rewrite <- triangle_number', triangle_number, triangle_number_exact.
    pose proof (Nat.div_mod_eq (k * n + d) 2).
    rewrite div_mul_not_exact, Hmod, Nat.sub_0_r by lia.
    
    rewrite triangle_number_exact
    induction k, (fun a : nat => a) using Nat.measure_induction.
    

    rewrite Nsum_reflect_perm.
  


  unfold idx_to_edge.

  ordered_edge_to_wire
*)

Lemma ZX_complete_form_pullthrough_2 n color αs deg : 
  ZX_complete_form n color αs deg ∝ 
  cast _ _ 
    (ZX_complete_stack_prf_1 n)
    (big_stack_mult_prf _ _ _)
    (big_stack (fun _ => 1) (fun k => big_sum (fun i =>
      ((fun k0 => deg (idx_to_edge n (k0 / 2)))
        ∘ perm_inv' (n * (n - 1)) (pairs_to_block_perm n))
        (k * (n - 1) + i)) (n - 1)) 
      (fun k => (b2ZX (color k) 1 _ (αs k))) n)
  ⟷ cast _ _
    eq_refl
    (ZX_connections_stack_alt_prf n deg)
    (big_zx_of_permutation_l (n * (n - 1))
      (perm_inv' (n * (n - 1)) (pairs_to_block_perm n))
      (fun k => deg (idx_to_edge n (k / 2)))
      (perm_inv'_permutation _ _ (pairs_to_block_permutation n)))
  ⟷ ZX_caps_stack n deg.
Proof.
  rewrite ZX_complete_form_pullthrough_1.
  rewrite big_stack_mult.
  unfold ZX_complete_stack.
  rewrite cast_compose_distribute.
  rewrite <- compose_assoc, cast_contract_eq.
  rewrite (big_stack_resize_unbounded 
    (fun _ => Nsum_1 (n - 1)) (fun k => eq_refl)).
  rewrite cast_contract_eq.
  rewrite cast_compose_eq_mid_join.
  rewrite big_stack_compose.
  rewrite (big_stack_simplify _ _ _ 
    (fun k => (b2ZX (color k) 1 _ (αs k)))).
  2: {
    intros k Hk.
    rewrite cast_compose_r, cast_b2ZX.
    rewrite b2ZX_spider_big_fusion_0'; [|easy|].
    2: {
      intros k' Hk'.
      unfold compose.
      rewrite b2ZX_if_color_dist.
      apply b2ZX_simplify; [|easy].
      assert (Hlt : k * (n - 1) + k' < n * (n - 1)) by show_moddy_lt.
      assert (Hlt' : (k * (n - 1) + k') / 2 < n * (n - 1) / 2) 
        by (apply Nat.Div0.div_lt_upper_bound; 
        rewrite (Nat.mul_comm 2), (triangle_number_exact n); lia).
      rewrite perm_inv'_eq by auto.
      rewrite pairs_to_block_perm_inv by auto.
      rewrite block_to_pairs_defn by auto.
      cbv delta [wire_to_ordered_edge] beta.
      rewrite mod_add_l, Nat.div_add_l, (Nat.div_small k'), 
        (Nat.mod_small k'), Nat.add_0_r by lia.
      cbn zeta.
      bdestruct (k' <? k).
      - cbn [fst snd].
        replace_bool_lia (k <? k') false.
        rewrite mod_add_l, if_false by reflexivity.
        rewrite Nat.div_add_l, Nat.add_0_r by lia.
        rewrite edge_to_idx_to_edge by (cbn; lia).
        reflexivity.
      - cbn [fst snd].
        replace_bool_lia (k <? S k') true.
        rewrite Nat.Div0.mod_mul.
        cbn [Nat.eqb].
        rewrite Nat.div_mul by lia.
        rewrite edge_to_idx_to_edge by (cbn; lia).
        reflexivity.
    }
    reflexivity.
  }
  apply compose_simplify; [|reflexivity].
  apply compose_simplify; [|reflexivity].
  cast_irrelevance.
Qed.



Definition ZX_large_stack n (color : nat -> bool) αs deg :=
  cast _ _ 
    (ZX_complete_stack_prf_1 n)
    (big_stack_mult_prf _ _ _)
    (big_stack (fun _ => 1) (fun k => big_sum (fun i =>
      ((fun k0 => deg (idx_to_edge n (k0 / 2)))
        ∘ (block_to_pairs_perm n))
        (k * (n - 1) + i)) (n - 1)) 
      (fun k => (b2ZX (color k) 1 _ (αs k))) n).

Definition ZX_large_perm n deg :=
  cast _ _
    eq_refl
    (ZX_connections_stack_alt_prf n deg)
    (big_zx_of_permutation_l (n * (n - 1))
      (block_to_pairs_perm n)
      (fun k => deg (idx_to_edge n (k / 2)))
      (block_to_pairs_permutation n)).



Definition ZX_large_form n color αs deg : ZX n 0 :=
  ZX_large_stack n color αs deg ⟷ 
  ZX_large_perm n deg ⟷
  ZX_caps_stack n deg.

(* FIXME: Move *)
Lemma pairs_to_block_perm_inv' n : 
  perm_inv' (n * (n - 1)) (pairs_to_block_perm n) = 
  block_to_pairs_perm n.
Proof.
  eq_by_WF_perm_eq (n * (n - 1)).
  rewrite perm_inv'_eq.
  apply pairs_to_block_perm_inv.
Qed.

Lemma block_to_pairs_perm_inv' n : 
  perm_inv' (n * (n - 1)) (block_to_pairs_perm n) = 
  pairs_to_block_perm n.
Proof.
  eq_by_WF_perm_eq (n * (n - 1)).
  rewrite perm_inv'_eq.
  apply block_to_pairs_perm_inv.
Qed.

Lemma ZX_complete_large_form_equiv n color αs deg : 
  ZX_complete_form n color αs deg ∝
  ZX_large_form n color αs deg.
Proof.
  rewrite ZX_complete_form_pullthrough_2.
  apply compose_simplify; [|reflexivity].
  unfold ZX_large_stack, ZX_large_perm.
  unshelve (eapply compose_simplify_casted);
  [now rewrite pairs_to_block_perm_inv'|..].
  - rewrite cast_contract_eq.
    apply big_stack_simplify_casted_casted_abs;
    [reflexivity|now rewrite pairs_to_block_perm_inv'|].
    intros k ? ? Hk.
    now rewrite cast_b2ZX.
  - unfold big_zx_of_permutation_l.
    rewrite !cast_contract_eq.
    apply cast_simplify.
    now rewrite pairs_to_block_perm_inv'.
Qed.


Lemma ZX_complete_stack_zx_of_perm_passthrough n αs color 
  f (Hf : permutation n f) : 
  zx_of_perm n f ⟷ ZX_complete_stack n αs color ∝
  ZX_complete_stack n 
    (αs ∘ (perm_inv' n f)) (color ∘ (perm_inv' n f)) ⟷
  cast _ _ (eq_trans (ZX_complete_stack_prf_2 n)
    (Nsum_reorder n _ _ (perm_inv'_permutation n f Hf))) 
  (ZX_complete_stack_prf_2 n)
    (big_zx_of_permutation_l n (perm_inv' n f)
      (fun _ => n - 1) 
      (perm_inv'_permutation n f Hf)).
Proof.
  rewrite (zx_of_perm_to_big_zx_of_permutation_l n f Hf).
  unfold ZX_complete_stack.
  rewrite cast_compose_eq_mid_join.
  erewrite cast_mor by
  (apply (big_zx_of_permutation_l_natural n (fun _ => 1))).
  unfold compose.
  rewrite (cast_compose_mid _ 
  (ZX_complete_stack_prf_2 n) (ZX_complete_stack_prf_2 n)).
  rewrite cast_compose_distribute.
  rewrite 2!cast_contract_eq.
  apply compose_simplify; cast_irrelevance.
Qed.




Lemma enlarge_permutation_constant n f d : 
  enlarge_permutation n f (fun _ => d) = 
  tensor_perms n d (perm_inv' n f) idn.
Proof.
  eq_by_WF_perm_eq (n * d);
  [rewrite Nat.mul_comm, <- times_n_nat, <- big_sum_constant; auto_perm|]. 
  rewrite tensor_perms_defn.
  rewrite Nat.mul_comm, <- times_n_nat, <- big_sum_constant.
  rewrite enlarge_permutation_defn.
  unfold compose.
  rewrite big_sum_constant, times_n_nat.
  intros k Hk.
  rewrite big_sum_constant, times_n_nat, 
    Nsum_index_constant, Nsum_offset_constant by lia.
  lia.
Qed.

Definition pairs_perm n f := 
  fun k => if n * (n - 1) / 2 <=? k then k else
  let ij := idx_to_edge n k in
  if f (fst ij) <? f (snd ij) then
    edge_to_idx n (f (fst ij), f (snd ij))
  else 
    edge_to_idx n (f (snd ij), f (fst ij)).

Lemma pairs_perm_WF n f : 
  WF_Perm (n * (n - 1) / 2) (pairs_perm n f).
Proof.
  intros k Hk;
  unfold pairs_perm;
  now simplify_bools_lia_one_kernel.
Qed.

#[export] Hint Resolve pairs_perm_WF : WF_Perm_db.

Lemma pairs_perm_defn n f : 
  perm_eq (n * (n - 1) / 2) (pairs_perm n f) 
  (fun k => let ij := idx_to_edge n k in
    if f (fst ij) <? f (snd ij) 
    then edge_to_idx n (f (fst ij), f (snd ij))
    else edge_to_idx n (f (snd ij), f (fst ij))).
Proof.
  intros k Hk;
  unfold pairs_perm;
  now simplify_bools_lia_one_kernel.
Qed.



Add Parametric Morphism n : (pairs_perm n) with signature
  perm_eq n ==> eq as pairs_perm_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  eq_by_WF_perm_eq _.
  rewrite 2!pairs_perm_defn.
  intros k Hk.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  now rewrite 2!Hfg by lia.
Qed.

Lemma pairs_perm_bounded n f (Hf : permutation n f) : 
  perm_bounded (n * (n - 1) / 2) (pairs_perm n f).
Proof.
  intros k Hk.
  rewrite pairs_perm_defn by auto.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  assert (f (fst (idx_to_edge n k)) <> f (snd (idx_to_edge n k)))
    by (intros Heq; apply (permutation_is_injective n f Hf) in Heq; lia).
  bdestruct_one; apply edge_to_idx_bounded; cbn [fst snd]; auto_perm.
Qed.

#[export] Hint Resolve pairs_perm_bounded : perm_bounded_db.

Lemma pairs_perm_compose n f g (Hf : permutation n f) (Hg : permutation n g) :
  pairs_perm n f ∘ pairs_perm n g = pairs_perm n (f ∘ g).
Proof.
  eq_by_WF_perm_eq (n * (n - 1) / 2).
  rewrite 3!pairs_perm_defn.
  intros k Hk.
  cbv delta [compose] beta.
  pose proof (idx_to_edge_spec n k Hk).
  assert (Hne : g (fst (idx_to_edge n k)) <> g (snd (idx_to_edge n k)))
    by (intros Heq; apply (permutation_is_injective n g Hg) in Heq; lia).
  set (ij := idx_to_edge n k) in *.
  cbn zeta.
  bdestruct (g (fst ij) <? g (snd ij)).
  - rewrite edge_to_idx_to_edge; cbn [fst snd]; auto_perm.
  - rewrite edge_to_idx_to_edge; cbn [fst snd]; auto_perm.
    assert (f (g (fst ij)) <> f (g (snd ij)))
    by (intros Heq; apply (permutation_is_injective n f Hf) in Heq; auto_perm).
    bdestruct_all; reflexivity + lia.
Qed.

Lemma pairs_perm_idn n : 
  pairs_perm n idn = idn.
Proof.
  eq_by_WF_perm_eq (n * (n - 1) / 2).
  rewrite pairs_perm_defn.
  intros k Hk.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  rewrite <- surjective_pairing, idx_to_edge_to_idx by lia.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite pairs_perm_compose 
  pairs_perm_idn
  using solve [auto_perm] : perm_cleanup_db.

Lemma pairs_perm_permutation n f (Hf : permutation n f) : 
  permutation (n * (n - 1) / 2) (pairs_perm n f).
Proof.
  rewrite permutation_defn.
  exists (pairs_perm n (perm_inv n f)).
  repeat split; [auto_perm..| |];
  rewrite pairs_perm_compose by auto_perm;
  [rewrite perm_inv_rinv_of_permutation by auto|
  rewrite perm_inv_linv_of_permutation by auto];
  now rewrite pairs_perm_idn.
Qed.

#[export] Hint Resolve pairs_perm_permutation : perm_db.

Lemma pairs_perm_inv n f (Hf : permutation n f) : 
  perm_eq (n * (n - 1) / 2) (perm_inv (n * (n - 1) / 2) (pairs_perm n f))
  (pairs_perm n (perm_inv n f)).
Proof.
  perm_eq_by_inv_inj (pairs_perm n f) (n * (n - 1) / 2).
Qed.

#[export] Hint Rewrite pairs_perm_inv
  using solve [auto_perm] : perm_inv_db.

Lemma pairs_perm_inv' n f (Hf : permutation n f) : 
  perm_inv' (n * (n - 1) / 2) (pairs_perm n f) = 
  pairs_perm n (perm_inv' n f).
Proof.
  eq_by_WF_perm_eq _.
  rewrite 2!perm_inv'_eq, pairs_perm_inv; auto_perm.
Qed.

#[export] Hint Rewrite pairs_perm_inv'
  using solve [auto_perm] : perm_inv_db.


(* Definition pairs_perm_r n f := 
  fun k => if n * (n - 1) / 2 <=? k then k else
  let ij := idx_to_edge n k in
  if fst ij <? f (snd ij) then
    edge_to_idx n (fst ij, f (snd ij))
  else 
    edge_to_idx n (f (snd ij), fst ij).

Lemma pairs_perm_r_WF n f : 
  WF_Perm (n * (n - 1) / 2) (pairs_perm_r n f).
Proof.
  intros k Hk;
  unfold pairs_perm_r;
  now simplify_bools_lia_one_kernel.
Qed.

#[export] Hint Resolve pairs_perm_r_WF : WF_Perm_db.

Lemma pairs_perm_r_defn n f : 
  perm_eq (n * (n - 1) / 2) (pairs_perm_r n f) 
  (fun k => let ij := idx_to_edge n k in
    if f (fst ij) <? snd ij 
    then edge_to_idx n (f (fst ij), snd ij)
    else edge_to_idx n (snd ij, f (fst ij))).
Proof.
  intros k Hk;
  unfold pairs_perm_r;
  now simplify_bools_lia_one_kernel.
Qed.

Add Parametric Morphism n : (pairs_perm_r n) with signature
  perm_eq n ==> eq as pairs_perm_r_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  eq_by_WF_perm_eq _.
  rewrite 2!pairs_perm_r_defn.
  intros k Hk.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  now rewrite Hfg by lia.
Qed.

Lemma pairs_perm_r_bounded n f (Hf : permutation n f) : 
  perm_bounded (n * (n - 1) / 2) (pairs_perm_r n f).
Proof.
  intros k Hk.
  rewrite pairs_perm_r_defn by auto.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  (* assert (f (fst (idx_to_edge n k)) <> f (snd (idx_to_edge n k)))
    by (intros Heq; apply (permutation_is_injective n f Hf) in Heq; lia). *)
  bdestruct_one; apply edge_to_idx_bounded; cbn [fst snd]; auto_perm.
Qed.

#[export] Hint Resolve pairs_perm_bounded : perm_bounded_db.

Lemma pairs_perm_compose n f g (Hf : permutation n f) (Hg : permutation n g) :
  pairs_perm n f ∘ pairs_perm n g = pairs_perm n (f ∘ g).
Proof.
  eq_by_WF_perm_eq (n * (n - 1) / 2).
  rewrite 3!pairs_perm_defn.
  intros k Hk.
  cbv delta [compose] beta.
  pose proof (idx_to_edge_spec n k Hk).
  assert (Hne : g (fst (idx_to_edge n k)) <> g (snd (idx_to_edge n k)))
    by (intros Heq; apply (permutation_is_injective n g Hg) in Heq; lia).
  set (ij := idx_to_edge n k) in *.
  cbn zeta.
  bdestruct (g (fst ij) <? g (snd ij)).
  - rewrite edge_to_idx_to_edge; cbn [fst snd]; auto_perm.
  - rewrite edge_to_idx_to_edge; cbn [fst snd]; auto_perm.
    assert (f (g (fst ij)) <> f (g (snd ij)))
    by (intros Heq; apply (permutation_is_injective n f Hf) in Heq; auto_perm).
    bdestruct_all; reflexivity + lia.
Qed.

Lemma pairs_perm_idn n : 
  pairs_perm n idn = idn.
Proof.
  eq_by_WF_perm_eq (n * (n - 1) / 2).
  rewrite pairs_perm_defn.
  intros k Hk.
  pose proof (idx_to_edge_spec n k Hk).
  cbn zeta.
  rewrite <- surjective_pairing, idx_to_edge_to_idx by lia.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite pairs_perm_compose 
  pairs_perm_idn
  using solve [auto_perm] : perm_cleanup_db.

Lemma pairs_perm_permutation n f (Hf : permutation n f) : 
  permutation (n * (n - 1) / 2) (pairs_perm n f).
Proof.
  rewrite permutation_defn.
  exists (pairs_perm n (perm_inv n f)).
  repeat split; [auto_perm..| |];
  rewrite pairs_perm_compose by auto_perm;
  [rewrite perm_inv_rinv_of_permutation by auto|
  rewrite perm_inv_linv_of_permutation by auto];
  now rewrite pairs_perm_idn.
Qed.

#[export] Hint Resolve pairs_perm_permutation : perm_db.

Lemma pairs_perm_inv n f (Hf : permutation n f) : 
  perm_eq (n * (n - 1) / 2) (perm_inv (n * (n - 1) / 2) (pairs_perm n f))
  (pairs_perm n (perm_inv n f)).
Proof.
  perm_eq_by_inv_inj (pairs_perm n f) (n * (n - 1) / 2).
Qed.

#[export] Hint Rewrite pairs_perm_inv
  using solve [auto_perm] : perm_inv_db.

Lemma pairs_perm_inv' n f (Hf : permutation n f) : 
  perm_inv' (n * (n - 1) / 2) (pairs_perm n f) = 
  pairs_perm n (perm_inv' n f).
Proof.
  eq_by_WF_perm_eq _.
  rewrite 2!perm_inv'_eq, pairs_perm_inv; auto_perm.
Qed.

#[export] Hint Rewrite pairs_perm_inv'
  using solve [auto_perm] : perm_inv_db. *)

Definition big_stack_perms n ns fs :=
  fun k => if big_sum ns n <=? k then k else
  big_sum ns (Nsum_index n ns k) + 
  (fs (Nsum_index n ns k)) (Nsum_offset n ns k).

Lemma big_stack_perms_WF n ns fs : 
  WF_Perm (big_sum ns n) (big_stack_perms n ns fs).
Proof.
  intros k Hk;
  unfold big_stack_perms;
  now simplify_bools_lia_one_kernel.
Qed.

#[export] Hint Resolve big_stack_perms_WF : WF_Perm_db.

Lemma big_stack_perms_defn n ns fs : 
  perm_eq (big_sum ns n) (big_stack_perms n ns fs) 
    (fun k => big_sum ns (Nsum_index n ns k) + 
    (fs (Nsum_index n ns k)) (Nsum_offset n ns k)).
Proof.
  intros k Hk;
  unfold big_stack_perms;
  now simplify_bools_lia_one_kernel.
Qed.



Lemma big_stack_perms_constant n d fs : 
  perm_eq (big_sum (fun _ => d) n)
    (big_stack_perms n (fun _ => d) fs) 
    (fun k => 
    k / d * d + fs (k / d) (k mod d)).
Proof.
  rewrite big_stack_perms_defn.
  rewrite big_sum_constant, times_n_nat.
  intros k Hk.
  now rewrite Nsum_index_constant, 
    Nsum_offset_constant, Nsum_constant by lia.
Qed.

Lemma big_stack_perms_constant_alt n d fs : 
  perm_eq (n * d)
    (big_stack_perms n (fun _ => d) fs) 
    (fun k => 
    k / d * d + fs (k / d) (k mod d)).
Proof.
  rewrite <- Nsum_constant; apply big_stack_perms_constant.
Qed.

Lemma big_stack_perms_succ n ns fs : 
  big_stack_perms (S n) ns fs = 
  stack_perms (big_sum ns n) (ns n) 
    (big_stack_perms n ns fs) (fs n).
Proof.
  eq_by_WF_perm_eq (big_sum ns (S n)).
  rewrite big_stack_perms_defn.
  rewrite big_stack_perms_defn.
  rewrite stack_perms_defn.
  intros k Hk.
  unfold Nsum_offset.
  cbn.
  rewrite Nat.leb_antisym.
  bdestruct (k <? big_sum ns n); cbn; lia. 
Qed.

Lemma big_stack_perms_bounded n ns fs 
  (Hfs : forall k, k < n -> perm_bounded (ns k) (fs k)) : 
  perm_bounded (big_sum ns n) (big_stack_perms n ns fs).
Proof.
  induction n; [easy|].
  rewrite big_stack_perms_succ.
  apply stack_perms_bounded;
  auto_perm.
Qed.

#[export] Hint Resolve big_stack_perms_bounded : perm_bounded_db.

Lemma big_stack_perms_permutation n ns fs 
  (Hfs : forall k, k < n -> permutation (ns k) (fs k)) : 
  permutation (big_sum ns n) (big_stack_perms n ns fs).
Proof.
  induction n; [now exists idn|].
  rewrite big_stack_perms_succ.
  apply stack_perms_permutation;
  auto_perm.
Qed.

#[export] Hint Resolve big_stack_perms_permutation : perm_db.

Lemma big_stack_perms_compose n ns fs gs 
  (Hgs : forall k, k < n -> perm_bounded (ns k) (gs k)) : 
  big_stack_perms n ns fs ∘ big_stack_perms n ns gs = 
  big_stack_perms n ns (fun k => fs k ∘ gs k).
Proof.
  induction n; [now eq_by_WF_perm_eq _|].
  specialize (IHn ltac:(auto)).
  rewrite 3!big_stack_perms_succ.
  rewrite stack_perms_compose by auto_perm.
  now rewrite IHn.
Qed.

Lemma big_stack_perms_inv n ns fs 
  (Hgs : forall k, k < n -> permutation (ns k) (fs k)) : 
  perm_eq (big_sum ns n) 
    (perm_inv (big_sum ns n) (big_stack_perms n ns fs))
    (big_stack_perms n ns (fun k => perm_inv (ns k) (fs k))).
Proof.
  induction n; [easy|].
  specialize (IHn ltac:(auto)).
  rewrite 2!big_stack_perms_succ.
  cbn.
  rewrite perm_inv_stack_perms, IHn by auto_perm.
  reflexivity.
Qed.


Lemma big_stack_perms_inv' n ns fs 
  (Hgs : forall k, k < n -> permutation (ns k) (fs k)) : 
  perm_inv' (big_sum ns n) (big_stack_perms n ns fs) = 
  big_stack_perms n ns (fun k => perm_inv' (ns k) (fs k)).
Proof.
  induction n; [easy|].
  specialize (IHn ltac:(auto)).
  rewrite 2!big_stack_perms_succ.
  cbn.
  rewrite perm_inv'_stack_perms, IHn by auto_perm.
  reflexivity.
Qed.

Hint Rewrite big_stack_perms_inv big_stack_perms_inv' 
  using solve [auto_perm] : perm_cleanup_db.





Lemma pairs_to_block_perm_pullthrough_l n f (Hf : permutation n f) : 
  tensor_perms n (n - 1) f idn ∘ pairs_to_block_perm n =
  big_stack_perms n (fun _ => (n - 1)) (fun k => contract_perm 
  (perm_inv n f) k) ∘ 
  pairs_to_block_perm n ∘ 
  tensor_perms (n * (n - 1) / 2) 2
    (pairs_perm n f) idn ∘
  big_stack_perms (n * (n - 1) / 2) (fun _ => 2)
    (fun k => let ij := idx_to_edge n k in 
    if f (snd ij) <? f (fst ij) then 
    swap_2_perm else idn).
Proof.
  pose proof (triangle_number_exact n) as Htri.
  pose proof (Nsum_constant (n - 1) n) as Hsum.
  pose proof (Nsum_constant 2 (n * (n - 1) / 2)) as Hsum2.
  eq_by_WF_perm_eq (n * (n - 1));
  [rewrite !Combinators.compose_assoc; 
    apply compose_WF_Perm; [rewrite <- Hsum; auto_perm|];
    apply compose_WF_Perm; [auto_perm|];
    apply compose_WF_Perm; [auto_perm|];
    rewrite <- Htri, <- Hsum2 at 1; auto_perm|].
  rewrite tensor_perms_defn, pairs_to_block_defn at 1.
  symmetry.
  assert (Hstack2 : permutation (n * (n - 1))
    (big_stack_perms (n * (n - 1) / 2) (fun _ => 2)
    (fun k => let ij := idx_to_edge n k in
     if f (snd ij) <? f (fst ij) then swap_2_perm else idn))).
  1: {
    eapply permutation_change_dims;
    [|apply big_stack_perms_permutation;
      intros k Hk; cbn zeta; bdestruct_one; auto_perm].
    lia.
    }
  rewrite big_stack_perms_constant_alt, pairs_to_block_defn.
  rewrite <- Htri at 1.
  rewrite <- Htri in Hstack2 at 1.
  rewrite tensor_perms_defn at 1.
  rewrite big_stack_perms_constant_alt.
  rewrite Htri.
  intros k Hk.
  unfold compose.
  rewrite mod_add_l, Nat.Div0.mod_mod, Nat.div_add_l, 
    mod_div, Nat.add_0_r by lia.
  assert (Hk' : k / 2 < n * (n - 1) / 2) 
    by (apply Nat.Div0.div_lt_upper_bound; lia).
  pose proof (idx_to_edge_spec _ _ Hk').
  set (ij := idx_to_edge n (k / 2)) in *.
  assert (f (fst ij) <> f (snd ij))
    by (intros Heq; apply (permutation_is_injective n f Hf) in Heq; lia).
  bdestruct (f (fst ij) <? f (snd ij)).
  - replace_bool_lia (f (snd ij) <? f (fst ij)) false.
    rewrite (Nat.mul_comm (k / 2) 2).
    rewrite <- (Nat.div_mod_eq k 2). 
    rewrite pairs_perm_defn by auto.
    fold ij.
    cbn zeta.
    (* unfold ordered_edge_to_wire. *)
    replace_bool_lia (f (fst ij) <? f (snd ij)) true.
    rewrite edge_to_idx_to_edge by (cbn [fst snd]; auto_perm).
    unfold ordered_edge_to_wire.
    cbn [fst snd].
    replace_bool_lia (f (fst ij) <? f (snd ij)) true.
    replace_bool_lia (f (snd ij) <? f (fst ij)) false.
    replace_bool_lia (snd ij <? fst ij) false.
    replace_bool_lia (fst ij <? snd ij) true.
    bdestruct (k mod 2 =? 0).
    + pose proof (permutation_is_bounded n f Hf) as Hfbdd.
      pose proof (Hfbdd (fst ij) ltac:(lia)).
      pose proof (Hfbdd (snd ij) ltac:(lia)).
      rewrite 2!mod_add_l, 2!Nat.div_add_l, 
        2!(Nat.div_small (_ - _)), 2!(Nat.mod_small (_ - _)), 
        2!Nat.add_0_r by lia.
      unfold contract_perm.
      rewrite Nat.sub_add by lia.
      rewrite 2!perm_inv_is_linv_of_permutation by auto_perm.
      bdestruct_all; lia.
    + pose proof (permutation_is_bounded n f Hf) as Hfbdd.
      pose proof (Hfbdd (fst ij) ltac:(lia)).
      pose proof (Hfbdd (snd ij) ltac:(lia)).
      rewrite 2!mod_add_l, 2!Nat.div_add_l,
        2!Nat.div_small, 2!Nat.mod_small, 
        2!Nat.add_0_r by lia.
      unfold contract_perm.
      rewrite 2!perm_inv_is_linv_of_permutation by auto_perm.
      bdestruct_all; lia.
  - replace_bool_lia (f (snd ij) <? f (fst ij)) true.
    rewrite mod_add_l, Nat.div_add_l by lia.
    rewrite <- even_eqb.
    pose proof (Nat.mod_upper_bound k 2 ltac:(lia)).
    rewrite (Nat.div_small (swap_2_perm _)), Nat.add_0_r by auto_perm.
     
    rewrite pairs_perm_defn by auto.
    fold ij.
    cbn zeta.
    (* unfold ordered_edge_to_wire. *)
    replace_bool_lia (f (fst ij) <? f (snd ij)) false.
    rewrite edge_to_idx_to_edge by (cbn [fst snd]; auto_perm).
    unfold ordered_edge_to_wire.
    cbn [fst snd].
    replace_bool_lia (f (fst ij) <? f (snd ij)) false.
    replace_bool_lia (f (snd ij) <? f (fst ij)) true.
    replace_bool_lia (snd ij <? fst ij) false.
    replace_bool_lia (fst ij <? snd ij) true.
    bdestruct (k mod 2 =? 0).
    + replace (k mod 2) with 0 by auto.
      change (swap_2_perm 0) with 1.
      cbn [Nat.even].
      pose proof (permutation_is_bounded n f Hf) as Hfbdd.
      pose proof (Hfbdd (fst ij) ltac:(lia)).
      pose proof (Hfbdd (snd ij) ltac:(lia)).
      rewrite 2!mod_add_l, 2!Nat.div_add_l, 
        2!(Nat.div_small), 2!(Nat.mod_small), 
        2!Nat.add_0_r by lia.
      unfold contract_perm.
      rewrite 2!perm_inv_is_linv_of_permutation by auto_perm.
      bdestruct_all; lia.
    + replace (k mod 2) with 1 by lia.
      change (swap_2_perm 1) with 0.
      cbn [Nat.even].
      pose proof (permutation_is_bounded n f Hf) as Hfbdd.
      pose proof (Hfbdd (fst ij) ltac:(lia)).
      pose proof (Hfbdd (snd ij) ltac:(lia)).
      rewrite 2!mod_add_l, 2!Nat.div_add_l,
        2!Nat.div_small, 2!Nat.mod_small, 
        2!Nat.add_0_r by lia.
      unfold contract_perm.
      rewrite Nat.sub_add by lia.
      rewrite 2!perm_inv_is_linv_of_permutation by auto_perm.
      bdestruct_all; lia.
Qed.


Lemma zx_of_big_stack_perms n ns fs 
  (Hfs : forall k, k < n -> permutation (ns k) (fs k)) : 
  zx_of_perm (big_sum ns n) (big_stack_perms n ns fs) ∝
  big_stack ns ns (fun k => zx_of_perm (ns k) (fs k)) n.
Proof.
  induction n; [by_perm_eq_nosimpl; cbn; by_perm_cell|].
  cbn.
  rewrite big_stack_perms_succ.
  rewrite <- stack_zx_of_perm by auto_perm.
  now rewrite IHn by auto_perm.
Qed.

Lemma zx_of_enlarge_to_big_zx_of_permutation_l n f ns (Hf : permutation n f) :
  zx_of_perm (big_sum ns n) (enlarge_permutation n f ns) ∝
  cast _ _ (Nsum_reorder n _ _ Hf) eq_refl
    (big_zx_of_permutation_l n f ns Hf).
Proof.
  unfold big_zx_of_permutation_l.
  now rewrite cast_contract_eq, cast_id.
Qed.

(* FIXME: Move *)
Lemma b2ZX_zxperm_absorbtion_right (b : bool) n m o α 
  (zx : ZX m o) (Hzx : ZXperm zx) : 
  b2ZX b n m α ⟷ zx ∝ b2ZX b n o α.
Proof.
  destruct b;
  [now apply X_zxperm_absorbtion_right | 
   now apply Z_zxperm_absorbtion_right].
Qed.

Section temp.
Import Kronecker.

(* FIXME: move to CapCupFacts.v *)
Lemma n_cup_zx_comm_absorbtion n : 
  zx_comm n n ⟷ n_cup n ∝ n_cup n.
Proof.
  prop_exists_nonzero 1%R.
  rewrite Mscale_1_l.
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  cbn [ZX_semantics].
  rewrite f_to_vec_split'_eq.
  rewrite Mmult_assoc.
  rewrite zx_comm_semantics.
  restore_dims.
  rewrite kron_comm_commutes_l by auto_wf.
  rewrite kron_comm_1_l, Mmult_1_r by auto_wf.
  rewrite 2!(kron_split_diag (f_to_vec _ _) (f_to_vec _ _)) by auto_wf.
  restore_dims.
  unify_pows_two. 
  rewrite <- 2!Mmult_assoc.
  rewrite 2!n_cup_f_to_vec_pullthrough_top.
  rewrite 2!kron_1_l by auto_wf.
  apply Mmult_vec_comm; auto_wf.
Qed.
End temp.

Lemma ZX_complete_form_zx_of_perm_absorbtion n color αs deg 
  f (Hf : permutation n f) 
  (Hdeg : forall k l, k < n -> l < n -> deg (k, l) = deg (l, k)) : 
  zx_of_perm n f ⟷ ZX_complete_form n color αs deg ∝
  ZX_complete_form n (color ∘ perm_inv' n f) (αs ∘ perm_inv' n f) 
    (fun ij => deg (perm_inv' n f (fst ij), perm_inv' n f (snd ij))).
Proof.
  unfold ZX_complete_form at 1.
  rewrite <- 2!compose_assoc.
  rewrite (ZX_complete_stack_zx_of_perm_passthrough _ _ _ _ Hf).
  unfold ZX_complete_perm.
  rewrite (compose_assoc (ZX_complete_stack _ _ _)).
  unfold big_zx_of_permutation_l.
  rewrite enlarge_permutation_constant.
  rewrite perm_inv'_perm_inv' by auto.
  rewrite cast_contract_eq.
  rewrite cast_zx_of_perm.
  rewrite cast_compose_r, cast_id.
  rewrite compose_zx_of_perm by auto_perm.
  pose proof (triangle_number_exact n) as Htri.
  rewrite pairs_to_block_perm_pullthrough_l by auto.
  pose proof (fun f => proj1 (permutation_change_dims _ _ 
    (Nsum_constant 2 (n * (n - 1) / 2)) f)).
  pose proof (fun f => proj1 (permutation_change_dims _ _ 
    (Htri) f)).
  pose proof (fun f => proj1 (permutation_change_dims _ _ 
    (Nsum_constant (n - 1) n) f)).
  assert (permutation (n * (n - 1))
    (big_stack_perms n (fun _ => n - 1) 
    (fun k => contract_perm (perm_inv n f) k))) by auto_perm.
  assert (forall n (b : bool) f g, permutation n f -> permutation n g ->
    permutation n (if b then f else g)) by (intros; now destruct b).
  assert (permutation (n * (n - 1))
    (big_stack_perms (n * (n - 1) / 2) (fun _ => 2)
    (fun k => let ij := idx_to_edge n k in
    if f (snd ij) <? f (fst ij) then swap_2_perm else idn))) by auto_perm.
  rewrite <- 3!compose_zx_of_perm by auto_perm. 
  let H := constr:(eq_sym (Nsum_constant (n - 1) n)) in 
  rewrite <- (cast_zx_of_perm _ _ _ H H).
  rewrite zx_of_big_stack_perms by auto_perm.
  assert (Hrw : pairs_perm n f = perm_inv' (n * (n - 1) / 2) 
    (perm_inv' (n * (n - 1) / 2) (pairs_perm n f))) 
    by cleanup_perm_inv.
  rewrite Hrw.
  rewrite <- enlarge_permutation_constant.
  let H := constr:(eq_sym (eq_trans (Nsum_constant 2 (n * (n - 1) / 2)) Htri)) in 
  rewrite <- 2!(cast_zx_of_perm _ _ (_ _ _) H H).
  unshelve (rewrite zx_of_enlarge_to_big_zx_of_permutation_l);
  [auto_perm|].
  rewrite zx_of_big_stack_perms by auto_perm.
  rewrite !cast_compose_distribute, !cast_contract_eq.
  rewrite !compose_assoc.
  unfold ZX_complete_connections.
  rewrite cast_compose_eq_mid_join.
  rewrite big_stack_compose.
  rewrite cast_compose_eq_mid_join.
  rewrite <- !compose_assoc.
  unfold ZX_complete_form.
  rewrite (cast_compose_mid _ Htri Htri).
  apply compose_simplify.
  - rewrite cast_compose_distribute, cast_contract_eq.
    apply compose_simplify; [|unfold ZX_complete_perm; cast_irrelevance].
    unfold ZX_complete_stack.
    rewrite cast_compose_eq_mid_join.
    rewrite big_stack_compose.
    rewrite cast_contract_eq.
    apply cast_simplify.
    apply big_stack_simplify.
    intros k Hk.
    apply b2ZX_zxperm_absorbtion_right; auto_zxperm.
  - rewrite big_zx_of_permutation_l_natural.
    unfold compose.
    let H := constr:(big_sum_0 (fun _ => 0) 
      (n * (n - 1) / 2) (fun _ => eq_refl)) in 
    rewrite (@proportional_of_perm_eq _ _ _ (cast _ _ H H (n_wire 0)))
      by ((rewrite (big_sum_0 (fun _ => 0)) at 1; easy) +
        unfold big_zx_of_permutation_l; auto_zxperm).
    rewrite cast_n_wire, nwire_removal_r.
    unfold ZX_complete_connections.
    rewrite cast_contract_eq.
    apply cast_simplify.
    apply big_stack_simplify.
    intros k Hk.
    rewrite pairs_perm_inv' by auto.
    pattern (idx_to_edge n (pairs_perm n (perm_inv' n f) k)).
    match goal with |- ?p ?k => set (P := p) end.
    rewrite pairs_perm_defn by auto.
    pose proof (idx_to_edge_spec n k Hk) as Hspec.
    set (ij := idx_to_edge n k) in *.
    cbn zeta.
    assert (perm_inv' n f (fst ij) <> perm_inv' n f (snd ij))
      by (clear -Hspec Hf; 
      intros Heq; apply (permutation_is_injective n (perm_inv' n f)) in Heq; 
        lia + auto_perm).
    assert (Hbdd : perm_bounded n (perm_inv' n f)) by auto_perm.
    pose proof (Hbdd (fst ij) ltac:(lia)).
    pose proof (Hbdd (snd ij) ltac:(lia)).
    bdestruct_one;
    rewrite edge_to_idx_to_edge by (cbn [fst snd]; lia);
    unfold P;
    cbn [fst snd]; 
    rewrite 2!perm_inv'_eq, 2!perm_inv_is_rinv_of_permutation by auto_perm.
    + replace_bool_lia (snd ij <? fst ij) false.
      rewrite zx_of_perm_idn, nwire_removal_l.
      easy.
    + replace_bool_lia (fst ij <? snd ij) true.
      change swap_2_perm with (perm_of_zx ⨉).
      rewrite zx_of_perm_of_zx_square by auto_perm.
      rewrite <- compose_assoc.
      rewrite swap_pullthrough_r.
      rewrite compose_assoc.
      rewrite n_cup_zx_comm_absorbtion.
      rewrite Hdeg by auto_perm.
      easy.
Qed.



(* Section on inputs (which we'll turn into outputs with cap/cup wizardry) *)

(* A WF input function to connect m inputs to n spiders*)
Definition WF_input_func m n f := forall i, i < m -> f i < n.

Definition count_func_vals m f k : nat :=
  big_sum (fun i => if f i =? k then 1 else 0) m.

Add Parametric Morphism m : (count_func_vals m) with signature
  perm_eq m ==> eq as count_func_vals_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  apply functional_extensionality.
  intros k.
  unfold count_func_vals.
  apply big_sum_eq_bounded.
  intros i Hi; now rewrite Hfg.
Qed.



Lemma sum_count_func_vals_upto m f n :
  big_sum (count_func_vals m f) n = 
  big_sum (fun k => if f k <? n then 1 else 0) m.
Proof.
  induction n.
  - cbn; now rewrite big_sum_0 by easy.
  - cbn. 
    rewrite IHn.
    unfold count_func_vals.
    rewrite <- Nsum_plus.
    apply big_sum_eq_bounded.
    intros k Hk; bdestruct_all; lia.
Qed.

Lemma sum_count_func_vals m n f (Hf : WF_input_func m n f) :
  big_sum (count_func_vals m f) n = m.
Proof.
  unfold WF_input_func in *.
  induction m.
  - now rewrite big_sum_0 by easy.
  - unfold count_func_vals.
    cbn.
    rewrite Nsum_plus.
    replace (S m) with (m + 1) by lia.
    f_equal.
    + apply IHm; auto.
    + apply big_sum_unique.
      exists (f m).
      split; [auto|];
      split; intros; bdestructΩ'.
Qed.
    

(* Decompose such a func into a perm and direct contractions, 
  realized as a zxperm and a stack of spiders *)
Definition perm_of_input_func m f :=
  fun k => 
  if m <=? k then k else
  big_sum (count_func_vals m f) (f k) +
  big_sum (fun i => if f i =? f k then 1 else 0) k.

Lemma perm_of_input_func_WF m f : WF_Perm m (perm_of_input_func m f).
Proof. intros k Hk. unfold perm_of_input_func. bdestructΩ'. Qed.

#[export] Hint Resolve perm_of_input_func_WF : WF_Perm_db.

Lemma perm_of_input_func_defn m f : 
  perm_eq m (perm_of_input_func m f)
  (fun k => big_sum (count_func_vals m f) (f k) +
  big_sum (fun i => if f i =? f k then 1 else 0) k).
Proof. intros k Hk. unfold perm_of_input_func. bdestructΩ'. Qed.


Add Parametric Morphism m : (perm_of_input_func m) with signature
  perm_eq m ==> eq as perm_of_input_func_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  eq_by_WF_perm_eq m.
  rewrite 2!perm_of_input_func_defn.
  intros k Hk.
  rewrite Hfg by auto.
  rewrite Hfg.
  f_equal.
  apply big_sum_eq_bounded.
  intros i Hi.
  now rewrite Hfg by lia.
Qed.



Lemma perm_of_input_func_bounded' m n f (Hf : WF_input_func m n f) : 
  perm_bounded m (perm_of_input_func m f).
Proof.
  intros k Hk.
  rewrite perm_of_input_func_defn by auto.
  assert (f k < n) by now apply Hf.
  apply (Nat.lt_le_trans _ 
    (big_sum (count_func_vals m f) (f k) + 
     big_sum (fun i => if f i =? f k then 1 else 0) m));
  [rewrite (big_sum_split m k); cbn; bdestructΩ'|].
  change (big_sum (count_func_vals m f) (S (f k)) <= m).
  rewrite <- (sum_count_func_vals m n f Hf) at 2.
  apply Nsum_le_r; lia.
Qed.

Lemma perm_of_input_func_bounded m f : 
  perm_bounded m (perm_of_input_func m f).
Proof.
  apply (perm_of_input_func_bounded' m (S (big_sum f m))).
  intros k Hk.
  enough (f k <= big_sum f m) by lia.
  rewrite (big_sum_split m k _ Hk).
  cbn; lia.
Qed.

#[export] Hint Resolve perm_of_input_func_bounded : perm_bounded_db.



Lemma perm_of_input_func_upper_bound m f :
  forall k, k < m ->
  perm_of_input_func m f k <
  big_sum (count_func_vals m f) (S (f k)).
Proof.
  intros k Hk.
  rewrite perm_of_input_func_defn by auto.
  cbn.
  unfold count_func_vals at 3.
  rewrite (big_sum_split m k _ Hk).
  cbn; bdestructΩ'.
Qed.

Lemma perm_of_input_func_lower_bound m f :
  forall k, k < m ->
  big_sum (count_func_vals m f) (f k) <=
  perm_of_input_func m f k.
Proof.
  intros k Hk.
  rewrite perm_of_input_func_defn by auto.
  lia.
Qed.

Lemma perm_of_input_func_spec m f : 
  forall k, k < m -> 
  big_sum (count_func_vals m f) (f k) <=
  perm_of_input_func m f k <
  big_sum (count_func_vals m f) (S (f k)).
Proof.
  auto using perm_of_input_func_upper_bound, 
    perm_of_input_func_lower_bound.
Qed.


Lemma perm_of_input_func_inj_helper m f :
  forall k l, k < m -> l < m ->
  perm_of_input_func m f k = perm_of_input_func m f l ->
  f k = f l.
Proof.
  intros k l Hk Hl.
  pose proof (perm_of_input_func_spec m f k Hk).
  pose proof (perm_of_input_func_spec m f l Hl).
  pose proof (Nsum_le_r (S (f k)) (f l) (count_func_vals m f)).
  pose proof (Nsum_le_r (S (f l)) (f k) (count_func_vals m f)).
  lia.
Qed.

Lemma perm_of_input_func_inj m f : 
  perm_inj m (perm_of_input_func m f).
Proof.
  intros k l Hk Hl.
  intros Heq.
  pose proof Heq as Heqf.
  apply perm_of_input_func_inj_helper in Heqf; [|auto..].
  revert Heq.
  rewrite 2!perm_of_input_func_defn by auto.
  bdestructΩ (k =? l).
  assert (Hkl : k < l \/ l < k) by lia.
  by_symmetry Hkl by lia.
  rewrite Heqf.
  rewrite (big_sum_split _ _ _ Hkl).
  cbn; bdestructΩ'.
Qed.

Lemma perm_of_input_func_permutation m f : 
  permutation m (perm_of_input_func m f).
Proof.
  apply permutation_iff_surjective,
    surjective_of_injective_and_bounded.
  split; [|auto_perm].
  apply perm_of_input_func_inj.
Qed.

#[export] Hint Resolve perm_of_input_func_permutation : perm_db.

Lemma perm_of_input_func_decomp m n f (Hf : WF_input_func m n f) : 
  perm_eq m 
    (Nsum_index n (count_func_vals m f) ∘
    perm_of_input_func m f) f.
Proof.
  rewrite perm_of_input_func_defn.
  intros k Hk.
  pose proof (sum_count_func_vals m n f Hf).
  unfold compose.
  rewrite Nsum_index_add_big_sum_l;
  [auto | | now apply Hf].
  unfold count_func_vals.
  rewrite (big_sum_split _ _ _ Hk); cbn; bdestructΩ'.
Qed.

Lemma perm_of_input_func_decomp_alt m n f (Hf : WF_input_func m n f) : 
  forall k, k < m ->
    (Nsum_index n (count_func_vals m f)
    (perm_of_input_func m f k)) = f k.
Proof.
  exact (perm_of_input_func_decomp m n f Hf).
Qed.

Lemma perm_of_input_func_enlarge_permutation_l 
  m n f (Hf : WF_input_func m n f) g (Hg : permutation n g) : 
  enlarge_permutation n g (count_func_vals m f) ∘ 
  perm_of_input_func m f = perm_of_input_func m (perm_inv' n g ∘ f).
Proof.
  pose proof (sum_count_func_vals _ _ _ Hf) as Heq.
  assert (forall h, WF_Perm (big_sum (count_func_vals m f) n) h ->
    WF_Perm m h) by (now rewrite Heq).
  eq_by_WF_perm_eq m.
  assert (forall h, perm_bounded m h ->
    perm_bounded (big_sum (count_func_vals m f) n) h) by (now rewrite Heq).
  rewrite <- Heq at 1.
  rewrite enlarge_permutation_defn.
  rewrite Heq.
  rewrite 2!perm_of_input_func_defn.
  intros k Hk.
  unfold compose.
  rewrite Nsum_index_add_big_sum_l, Nsum_offset_add_big_sum_l
    by first [ now apply Hf |
    unfold count_func_vals;
    rewrite (big_sum_split _ _ _ Hk);
    cbn; bdestructΩ'].
  f_equal.
  - apply big_sum_eq_bounded.
    intros i Hi.
    apply big_sum_eq_bounded.
    intros l Hl.
    rewrite perm_inv'_eq by auto.
    assert (perm_inv' n g (f k) < n) by auto_perm.
    now rewrite perm_inv_eqb_iff by auto_perm.
  - apply big_sum_eq_bounded.
    intros l Hl.
    now rewrite (permutation_eqb_iff _ _ 
      (perm_inv'_permutation n g Hg)) by auto with zarith.
Qed.







  



Program Definition nat_max_is_monoid : Monoid nat :=
  {|
    Gzero := 0;
    Gplus := Nat.max
  |}.
Solve All Obligations with lia.

Definition Nmax n f :=
  @big_sum nat nat_max_is_monoid f n.

Add Parametric Morphism n : (Nmax n) with signature
  perm_eq n ==> eq as Nmax_perm_eq_to_eq.
Proof.
  intros f g Hfg.
  induction n; [easy|].
  cbn.
  f_equal; [|auto].
  unfold perm_eq in *; auto.
Qed.

Lemma le_Nmax n f k (Hk : k < n) : 
  f k <= Nmax n f.
Proof.
  unfold Nmax.
  induction n; [easy|].
  cbn.
  bdestruct (k =? n); subst; lia.
Qed.

Lemma Nmax_succ n f : 
  Nmax (S n) f = Nat.max (Nmax n f) (f n).
Proof. reflexivity. Qed.

Lemma Nmax_plus n m f : 
  Nmax (n + m) f = Nat.max (Nmax n f) (Nmax m (fun k => f (n + k))).
Proof.
  exact (big_sum_sum n m f).
Qed.

Lemma Nmax_attained n f (Hn : n <> 0) : 
  exists k, k < n /\ f k = Nmax n f.
Proof.
  induction n; [easy|].
  rewrite Nmax_succ.
  bdestruct (f n <? Nmax n f).
  - destruct (IHn ltac:(intros ->; cbn; easy)) as [k Hk].
    exists k; lia.
  - exists n; lia.
Qed.

Lemma Nmax_defn n f m (Hm : forall k, k < n -> f k <= m) : 
  Nmax n f <= m.
Proof.
  bdestruct (n =? 0); [subst; cbn; lia|].
  destruct (Nmax_attained n f) as (k & Hk & <-); auto.
Qed.

Lemma max_le_l_iff a b c : 
  Nat.max a b <= c <-> (a <= c /\ b <= c).
Proof. lia. Qed.

Lemma max_lt_l_iff a b c : 
  Nat.max a b < c <-> (a < c /\ b < c).
Proof. lia. Qed.

Lemma Nmax_le n f g (Hfg : forall k, k < n -> f k <= g k) : 
  Nmax n f <= Nmax n g.
Proof.
  induction n; [reflexivity|].
  rewrite 2!Nmax_succ.
  apply Nat.max_le_compat; auto.
Qed.

Lemma Nmax_constant n d : 
  Nmax n (fun _ => d) = if n =? 0 then 0 else d.
Proof.
  induction n; [reflexivity|].
  rewrite Nmax_succ, IHn; bdestructΩ'.
Qed.

Lemma Nmax_le_l n m f (Hnm : n <= m) : 
  Nmax n f <= Nmax m f.
Proof.
  replace m with (n + (m - n)) by lia.
  rewrite Nmax_plus.
  auto with arith.
Qed.

Lemma Nmax_max n m f : 
  Nmax (Nat.max n m) f = Nat.max (Nmax n f) (Nmax m f).
Proof.
  pose proof (Nmax_le_l n m f).
  pose proof (Nmax_le_l m n f).
  bdestruct (n <? m); 
  [replace (Nat.max n m) with m by lia |
  replace (Nat.max n m) with n by lia]; lia.
Qed.

Lemma Nmax_max_r n f g :
  Nmax n (fun k => Nat.max (f k) (g k)) = 
  Nat.max (Nmax n f) (Nmax n g).
Proof.
  induction n; [reflexivity|].
  rewrite 3!Nmax_succ, IHn.
  lia.
Qed.

Lemma Nmax_Nmax_l n f g : 
  Nmax (Nmax n g) f =
  Nmax n (fun k => Nmax (g k) f).
Proof.
  induction n; [reflexivity|].
  now rewrite 2!Nmax_succ, Nmax_max, IHn.
Qed.

Lemma Nmax_le_iff n f m : 
  Nmax n f <= m <-> (forall k, k < n -> f k <= m).
Proof.
  induction n; [cbn; split; intros; lia|].
  rewrite Nmax_succ.
  rewrite max_le_l_iff, IHn.
  split.
  - intros [H ?] k Hk; bdestruct (k =? n); subst; auto with zarith.
  - auto.
Qed.

Lemma Nmax_lt_iff n f m (Hn : m <> 0) : 
  Nmax n f < m <-> (forall k, k < n -> f k < m).
Proof.
  induction n; [cbn; split; intros; lia|].
  rewrite Nmax_succ.
  rewrite max_lt_l_iff, IHn.
  split.
  - intros [H ?] k Hk; bdestruct (k =? n); subst; auto with zarith.
  - auto.
Qed.

Lemma WF_input_func_default m n f : 
  WF_input_func m (Nat.max n (S (Nmax m f))) f.
Proof.
  intros k Hk.
  pose proof (le_Nmax m f k Hk).
  lia.
Qed.

(* FIXME: Move *)
Lemma Nsum_max f n m : 
  big_sum f (Nat.max n m) = 
  Nat.max (big_sum f n) (big_sum f m).
Proof.
  pose proof (Nsum_le_r n m f).
  pose proof (Nsum_le_r m n f).
  bdestruct (m <? n);
  [rewrite Nat.max_l | rewrite Nat.max_r]; lia.
Qed.

Lemma ZX_io_stack_prf m n f : 
  n = big_sum (fun k => if k <? n then 1 else 0) (Nat.max n (S (Nmax m f))).
Proof.
  bdestruct (n <? S (Nmax m f)).
  - replace (Nat.max n (S (Nmax m f))) with (n + (S (Nmax m f) - n)) by lia.
    rewrite big_sum_sum.
    rewrite (big_sum_eq_bounded _ (fun _ => 1)) by (intros; bdestructΩ').
    rewrite Nsum_1.
    rewrite big_sum_0 by (intros; bdestructΩ').
    cbn; lia.
  - rewrite Nat.max_l by lia.
    rewrite (big_sum_eq_bounded _ (fun _ => 1)) by (intros; bdestructΩ').
    now rewrite Nsum_1.
Qed.

Definition ZX_io_stack_gen m n f (color : nat -> bool) : ZX m n :=
  cast _ _ 
  (eq_sym (sum_count_func_vals _ _ _ (WF_input_func_default m n f))) 
  (ZX_io_stack_prf m n f)
    (big_stack _ _ (fun k => b2ZX (color k) _ _ 0) _).

Definition ZX_io_stack_WF m n f (color : nat -> bool) 
  (Hf : WF_input_func m n f) : ZX m n :=
  cast _ _ 
  (eq_sym (sum_count_func_vals _ _ _ Hf)) 
  (eq_sym (Nsum_1 n))
    (big_stack _ _ (fun k => b2ZX (color k) _ _ 0) _).

Lemma max_n_S_Nmax_WF m n f (Hf : WF_input_func m n f) 
  (Hn : m <> 0) : 
  Nat.max n (S (Nmax m f)) = n.
Proof.
  apply Nat.max_l.
  change (Nmax m f < n).
  apply Nmax_lt_iff; [|auto with zarith].
  specialize (Hf 0); lia.
Qed.

Lemma max_n_S_Nmax_WF_alt m n f (Hf : WF_input_func m n f) 
  (Hn : n <> 0) : 
  Nat.max n (S (Nmax m f)) = n.
Proof.
  apply Nat.max_l.
  change (Nmax m f < n).
  apply Nmax_lt_iff; auto with zarith.
Qed.

(* FIXME: Move *)
Lemma Z_0_0_is_empty : 
  Z 0 0 0 ∝ ⦰.
Proof.
  prop_exists_nonzero (C2)%C.
  prep_matrix_equivalence.
  unfold scale.
  by_cell.
  rewrite Cexp_0.
  lca.
Qed.

Lemma X_0_0_is_empty : 
  X 0 0 0 ∝ ⦰.
Proof. colorswap_of (Z_0_0_is_empty). Qed.



Lemma b2ZX_0_0_is_empty (b : bool) : 
  b2ZX b 0 0 0 ∝ ⦰.
Proof.
  destruct b;
  [apply X_0_0_is_empty | apply Z_0_0_is_empty].
Qed.

Lemma ZX_io_stack_gen_equiv_WF m n f (color : nat -> bool) 
  (Hf : WF_input_func m n f) : 
  ZX_io_stack_gen m n f color ∝
  ZX_io_stack_WF m n f color Hf.
Proof.
  bdestruct (m =? 0); [bdestruct (n =? 0)|].
  - subst.
    unfold ZX_io_stack_gen, ZX_io_stack_WF.
    cbn.
    rewrite b2ZX_0_0_is_empty.
    rewrite stack_empty_l.
    cast_irrelevance.
  - prop_exists_nonzero 1%R.
    rewrite Mscale_1_l.
    unfold ZX_io_stack_gen, ZX_io_stack_WF.
    simpl_cast_semantics.
    subst.
    cbn.
    rewrite 2!big_stack_semantics.
    rewrite Nat.max_l by lia.
    apply big_kron'_eq_bounded_dims;
    intros k Hk; bdestructΩ'.
  - prop_exists_nonzero 1%R.
    rewrite Mscale_1_l.
    unfold ZX_io_stack_gen, ZX_io_stack_WF.
    simpl_cast_semantics.
    rewrite 2!big_stack_semantics.
    rewrite max_n_S_Nmax_WF by auto.
    apply big_kron'_eq_bounded_dims;
    intros k Hk; bdestructΩ'.
Qed.

Definition ZX_of_io m n f color : ZX m n :=
  zx_of_perm m (perm_inv' m (perm_of_input_func m f)) 
    ⟷ ZX_io_stack_gen m n f color.

(* FIXME: Move to Qlib. Also, TODO: maybe reorder big_kron' arguments to make 
   a Morphism possible *)
Lemma big_kron_big_kron' {m n} (As : list (Matrix (2^m) (2^n))) 
  (HAs : Forall WF_Matrix As) : 
  big_kron As = big_kron' (fun _ => m) (fun _ => n) (nth_default Zero As)
    (length As).
Proof.
  induction HAs as [|a As Ha HAs IHAs]; [easy|].
  cbn [big_kron length].
  change (S (length As)) with (1 + length As).
  rewrite big_kron'_split_add.
  - f_equal;
    [rewrite <- 1?Nat.pow_mul_r, 1?Nsum_constant; unify_pows_two.. | |].
    + cbn.
      now rewrite kron_1_l.
    + apply IHAs.
  - intros k Hk. 
    rewrite Forall_forall in HAs.
    destruct k; [easy|].
    apply HAs.
    rewrite nth_default_eq.
    cbn.
    apply nth_In; lia.
Qed.


(* FIXME: Move *)
Lemma permutation_eqb_iff_WF n f (Hf : permutation n f) (HWFf : WF_Perm n f) 
  a b : 
  (f a =? f b) = (a =? b).
Proof.
  apply eq_iff_eq_true; rewrite 2!Nat.eqb_eq.
  split; [|now intros []].
  pose proof (permutation_is_bounded n f Hf) as Hfbdd.
  pose proof (Hfbdd a).
  pose proof (Hfbdd b).
  pose proof (fun Ha Hb => (proj1 (permutation_eq_iff a b Hf Ha Hb))).
  pose proof (HWFf a).
  pose proof (HWFf b).
  bdestruct (a <? n);
  bdestruct (b <? n); lia.
Qed.
  


(* FIXME: Move, and use in above proof of perm_of_input_func pullthrough *)
Lemma count_func_vals_compose_perm_r m n f g 
  (Hf : WF_input_func m n f) (Hg : permutation n g) : 
  perm_eq n (count_func_vals m f ∘ g)
  (count_func_vals m (perm_inv' n g ∘ f)).
Proof.
  intros k Hk.
  unfold compose.
  apply big_sum_eq_bounded.
  intros l Hl.
  now rewrite perm_inv'_eq, perm_inv_eqb_iff by auto.
Qed.

Lemma ZX_of_io_absorb_zx_of_perm_r m n f color g 
  (Hf : WF_input_func m n f) (Hg : permutation n g) : 
  ZX_of_io m n f color ⟷ zx_of_perm n g ∝
  ZX_of_io m n (perm_inv' n g ∘ f) (color ∘ g).
Proof.
  unfold ZX_of_io.
  rewrite (ZX_io_stack_gen_equiv_WF _ _ _ _ Hf).
  assert (Hg' : perm_bounded n (perm_inv' n g)) by auto_perm.
  rewrite (ZX_io_stack_gen_equiv_WF _ _ (_ ∘ _) 
    _ (fun k => Hg' _ ∘ Hf k)).
  unfold ZX_io_stack_WF.
  rewrite (zx_of_perm_to_big_zx_of_permutation_r n g Hg).
  rewrite compose_assoc.
  rewrite cast_compose_eq_mid_join.
  erewrite cast_mor;
  [|etransitivity;
  [exact (big_zx_of_permutation_r_natural n _ _ _ g Hg)|
  let H := constr:(eq_trans (eq_sym (sum_count_func_vals _ _ _ Hf))
    (Nsum_reorder n _ g Hg)) in 
  exact (cast_compose_mid _ H H _ _)]].
  rewrite cast_compose_distribute, 2!cast_contract_eq.
  rewrite <- compose_assoc.
  apply compose_simplify.
  - unfold big_zx_of_permutation_r.
    rewrite cast_contract_eq, cast_zx_of_perm.
    pose proof (sum_count_func_vals _ _ _ Hf) as Heq.
    pose proof (fun h => proj1 (permutation_change_dims _ _ Heq h)).
    rewrite (Nsum_reorder _ _ g Hg) in H.
    rewrite compose_zx_of_perm by auto_perm.
    erewrite zx_of_perm_eq_of_perm_eq; [reflexivity|].
    rewrite <- enlarge_permutation_inv' by auto.
    rewrite <- (Nsum_reorder _ _ g Hg) in H.
    rewrite Heq.
    rewrite <- perm_inv'_compose by auto_perm.
    rewrite 2!perm_inv'_eq.
    apply perm_inv_perm_eq_proper.
    now rewrite perm_of_input_func_enlarge_permutation_l by auto.
  - rewrite (big_stack_resize (count_func_vals_compose_perm_r m n f g Hf Hg) 
      (perm_eq_refl n (fun _ => 1))), cast_contract_eq.
    apply cast_simplify.
    apply big_stack_simplify.
    intros k Hk.
    destruct (lt_dec k n); [|easy].
    now rewrite cast_b2ZX.
Qed.

Record ZX_graph_core {m : nat} := {
  core_io := m;
  core_spis : nat;
  core_infunc : nat -> nat;
  core_deg : nat * nat -> nat;
  core_color : nat -> bool;
  core_αs : nat -> R;
}.

Arguments ZX_graph_core _ : clear implicits.

Record WF_ZX_graph_core {m} {ZXG : ZX_graph_core m} : Prop := {
  WF_core_sym : forall k l, k < ZXG.(core_spis) -> l < ZXG.(core_spis) -> 
    ZXG.(core_deg) (k, l) = ZXG.(core_deg) (l, k);
  WF_core_infunc : WF_input_func m ZXG.(core_spis) ZXG.(core_infunc)
}.

Arguments WF_ZX_graph_core {_} _.

(* FIXME: Move? *)
Create HintDb WF_ZX_graph_db discriminated.
#[export] Hint Extern 0 (permutation _ _) => 
  solve [auto_perm] : WF_ZX_graph_db.
#[export] Hint Extern 0 (perm_bounded _ _) => 
  solve [auto_perm] : WF_ZX_graph_db.
#[export] Hint Extern 0 (WF_Perm _ _) => 
  solve [auto_perm] : WF_ZX_graph_db.

Definition ZX_of_ZX_graph_core {m} (ZXG : ZX_graph_core m) : ZX m 0 :=
  ZX_of_io m ZXG.(core_spis) ZXG.(core_infunc) ZXG.(core_color) ⟷
  ZX_complete_form ZXG.(core_spis) ZXG.(core_color) 
    ZXG.(core_αs) ZXG.(core_deg).

Definition ZX_of_ZX_graph_core_WF {m} (ZXG : ZX_graph_core m) 
  (HZXG : WF_ZX_graph_core ZXG) : ZX m 0 :=
  zx_of_perm m (perm_inv' m (perm_of_input_func m (ZXG.(core_infunc)))) ⟷
  ZX_io_stack_WF m ZXG.(core_spis) ZXG.(core_infunc) ZXG.(core_color) 
    HZXG.(WF_core_infunc) ⟷
  ZX_complete_form ZXG.(core_spis) ZXG.(core_color) 
    ZXG.(core_αs) ZXG.(core_deg).

Lemma ZX_of_ZX_graph_core_equiv_WF {m} (ZXG : ZX_graph_core m) 
  (HZXG : WF_ZX_graph_core ZXG) : 
  ZX_of_ZX_graph_core ZXG ∝ ZX_of_ZX_graph_core_WF ZXG HZXG.
Proof.
  apply compose_simplify; [|reflexivity].
  apply compose_simplify; [reflexivity|].
  apply ZX_io_stack_gen_equiv_WF.
Qed.

Definition permute_ZX_graph_core {m} (ZXG : ZX_graph_core m) f : 
  ZX_graph_core m := {|
  core_spis := ZXG.(core_spis);
  core_infunc := perm_inv' (ZXG.(core_spis)) f ∘ ZXG.(core_infunc);
  core_deg := ZXG.(core_deg) ∘ (fun ij => (f (fst ij), f (snd ij)));
  core_color := ZXG.(core_color) ∘ f;
  core_αs := ZXG.(core_αs) ∘ f;
|}.

Lemma permute_ZX_graph_core_WF {m} (ZXG : ZX_graph_core m) f 
  (HZXG : WF_ZX_graph_core ZXG) (Hf : permutation ZXG.(core_spis) f) : 
  WF_ZX_graph_core (permute_ZX_graph_core ZXG f).
Proof.
  constructor.
  - cbn.
    unfold compose.
    cbn.
    intros.
    apply WF_core_sym; auto_perm.
  - cbn.
    intros k Hk.
    unfold compose.
    auto using (WF_core_infunc HZXG) with perm_db.
Qed.

#[export] Hint Resolve permute_ZX_graph_core_WF : WF_ZX_graph_db.

(* FIXME: Move these up *)
Lemma ZX_complete_stack_simplify n color αs color' αs' 
  (Hcolor : forall k, k < n -> color k = color' k)
  (Hαs : forall k, k < n -> αs k = αs' k):
  ZX_complete_stack n αs color ∝ 
  ZX_complete_stack n αs' color'.
Proof.
  unfold ZX_complete_stack.
  apply cast_simplify.
  apply big_stack_simplify.
  auto using b2ZX_simplify.
Qed.

Lemma ZX_complete_connections_simplify n color deg color' deg' 
  (Hcolor : forall k, k < n -> color k = color' k)
  (Hdeg : forall k l, k < n -> l < n -> deg (k, l) = deg' (k, l)) :
  ZX_complete_connections n deg color ∝ 
  ZX_complete_connections n deg' color'.
Proof.
  unfold ZX_complete_connections.
  apply cast_simplify.
  apply big_stack_simplify.
  intros k Hk.
  rewrite (surjective_pairing (idx_to_edge n k)).
  cbn [fst snd].
  pose proof (idx_to_edge_spec n k Hk).
  now rewrite 2!Hcolor, Hdeg by lia.
Qed.


Lemma ZX_complete_form_simplify n color αs deg 
  color' αs' deg' 
  (Hcolor : forall k, k < n -> color k = color' k)
  (Hαs : forall k, k < n -> αs k = αs' k)
  (Hdeg : forall k l, k < n -> l < n -> deg (k, l) = deg' (k, l)) :
  ZX_complete_form n color αs deg ∝ 
  ZX_complete_form n color' αs' deg'.
Proof.
  unfold ZX_complete_form.
  auto using compose_simplify, ZX_complete_stack_simplify, 
  ZX_complete_connections_simplify, proportional_refl.
Qed.

Lemma permute_ZX_graph_core_correct {m} (ZXG : ZX_graph_core m)
  (HZXG : WF_ZX_graph_core ZXG) f (Hf : permutation ZXG.(core_spis) f) :
  ZX_of_ZX_graph_core ZXG ∝ 
  ZX_of_ZX_graph_core (permute_ZX_graph_core ZXG f).
Proof.
  unfold ZX_of_ZX_graph_core.
  destruct ZXG as [_ n g deg color αs].
  destruct HZXG as [Hdeg Hg].
  cbn in *.
  rewrite <- (nwire_removal_r (ZX_of_io _ _ _ _)).
  rewrite <- zx_of_perm_idn.
  rewrite <- (perm_inv_rinv_of_permutation n f Hf).
  rewrite <- compose_zx_of_perm by auto_perm.
  rewrite <- perm_inv'_eq.
  rewrite <- compose_assoc.
  rewrite ZX_of_io_absorb_zx_of_perm_r by auto.
  rewrite compose_assoc.
  rewrite ZX_complete_form_zx_of_perm_absorbtion by auto_perm.
  apply compose_simplify; [reflexivity|].
  apply ZX_complete_form_simplify;
  intros; unfold compose; 
  cbn;
  now rewrite 2?perm_inv'_perm_inv' by auto_perm.
Qed.



(* FIXME: Move *)


Lemma idx_to_edge_succ n k (Hk : k < S n * (S n - 1) / 2) : 
  idx_to_edge (S n) k = if k <? n then (0, S k)
  else (fun ij => (S (fst ij), S (snd ij))) (idx_to_edge n (k - n)).
Proof.
  unfold idx_to_edge.
  cbn [fst snd].
  rewrite Nsum_index_succ, Nsum_offset_succ 
    by (rewrite Nsum_permutation; auto_perm).
  replace (reflect_perm (S n) 0) with n by (cbn; lia).
  bdestruct (k <? n); [reflexivity|].
  assert (Hrw : perm_eq n (reflect_perm (S n) ∘ S) (reflect_perm n))
    by (intros l Hl; unfold compose; now rewrite 2!reflect_perm_defn by lia).
  rewrite (Nsum_index_perm_eq_to_eq  _ _ _ Hrw).
  f_equal.
  cbn.
  do 3 f_equal.
  unfold Nsum_offset.
  rewrite (Nsum_index_perm_eq_to_eq  _ _ _ Hrw).
  bdestruct (n =? 0); [now subst|].
  erewrite big_sum_eq_bounded; [reflexivity|].
  intros l Hl.
  pose proof (Nsum_index_bounded n (reflect_perm n) (k - n)).
  apply Hrw; lia.
Qed.

















Definition reps_to_front_perm n :=
  fun k => if n * n <=? k then k else
  if k mod n =? 0 (* is in front of its section *) 
  then k / n 
  else k + n - S (k / n).

Definition reps_from_front_perm n :=
  fun k => if n * n <=? k then k else
  if k <? n (* k / m =? 0 *)
  then n * (k mod n) 
  else k - (n - S ((k - n) / (n - 1))).

Lemma reps_to_front_perm_WF n : WF_Perm (n * n) (reps_to_front_perm n).
Proof. intros k Hk. unfold reps_to_front_perm. bdestructΩ'. Qed.

Lemma reps_from_front_perm_WF n : WF_Perm (n * n) (reps_from_front_perm n).
Proof. intros k Hk. unfold reps_from_front_perm. bdestructΩ'. Qed.

#[export] Hint Resolve reps_to_front_perm_WF 
  reps_from_front_perm_WF : WF_Perm_db. 

Lemma reps_to_front_perm_defn n : 
  perm_eq (n * n)
    (reps_to_front_perm n)
    (fun k => if k mod n =? 0 then k / n else k + n - S (k / n)).
Proof.
  intros k Hk.
  unfold reps_to_front_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma reps_from_front_perm_defn n : 
  perm_eq (n * n)
    (reps_from_front_perm n)
    (fun k => if k <? n then n * (k mod n) else k - (n - S ((k - n) / (n - 1)))).
Proof.
  intros k Hk.
  unfold reps_from_front_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma reps_to_front_perm_bounded n : 
  perm_bounded (n * n) (reps_to_front_perm n).
Proof.
  intros k Hk.
  rewrite reps_to_front_perm_defn by auto.
  bdestruct_one.
  - show_moddy_lt.
  - bdestruct (k <? n * (n - 1)); [lia|].
    enough (k / n >= (n - 1)) by lia.
    apply Nat.div_le_lower_bound; lia.
Qed.

Lemma reps_from_front_perm_bounded n : 
  perm_bounded (n * n) (reps_from_front_perm n).
Proof.
  intros k Hk.
  rewrite reps_from_front_perm_defn by auto.
  bdestruct_one.
  - show_moddy_lt.
  - lia.
Qed.

#[export] Hint Resolve reps_to_front_perm_bounded
  reps_from_front_perm_bounded : perm_bounded_db.

Lemma Nsum_alt_1_sub_1_eq n d (Hn : n <> 0) : 
  big_sum (fun k => if k mod 2 =? 0 then 1 else (n - 1)) (2 * d)
  = d * n.
Proof.
  change (fun k => if k mod 2 =? 0 then 1 else n - 1) with 
    (fun k => (fun (kdiv2 kmod2 : nat) => if kmod2 =? 0 then 1 else n - 1)
      (k / 2) (k mod 2)). 
  rewrite <- big_sum_double_sum.
  rewrite Nsum_constant.
  cbn [big_sum Gplus nat_is_monoid Nat.eqb].
  f_equal; cbn; lia.
Qed.

Lemma Nsum_alt_1_sub_1_eq_total n m (Hn : n <> 0) : 
  big_sum (fun k => if k mod 2 =? 0 then 1 else (n - 1)) m
  = m / 2 * n + (if m mod 2 =? 0 then 0 else 1).
Proof.
  rewrite (Nat.div_mod_eq m 2) at 1.
  rewrite big_sum_sum.
  cbn [Gplus nat_is_monoid].
  rewrite Nsum_alt_1_sub_1_eq by auto.
  f_equal.
  pose proof (Nat.mod_upper_bound m 2 ltac:(lia)).
  bdestruct (m mod 2 =? 0).
  - replace -> (m mod 2).
    reflexivity.
  - replace (m mod 2) with 1 by lia.
    cbn [big_sum].
    rewrite Nat.add_0_r, Nat.mul_comm, Nat.Div0.mod_mul.
    reflexivity.
Qed.

Lemma Nsum_alt_1_sub_1_eq_diag n : 
  big_sum (fun k => if k mod 2 =? 0 then 1 else (n - 1)) (2 * n)
  = n * n.
Proof.
  bdestruct (n =? 0); [subst; reflexivity|].
  now apply Nsum_alt_1_sub_1_eq.
Qed.


Lemma Nsum_index_alt_1_sub_1_eq n d k (Hk : k < d * n) : 
  Nsum_index (2 * d) (fun k => if k mod 2 =? 0 then 1 else (n - 1)) k
  = k / n * 2 + (if k mod n =? 0 then 0 else 1).
Proof.
  revert n Hk; induction d; [lia|]; intros n Hk.
  assert (Hn : n <> 0) by lia.
  assert (HSd : 2 * S d = S (S (2 * d))) by lia.
  rewrite HSd.
  cbn [Nsum_index big_sum Gplus nat_is_monoid].
  pose proof (Nsum_alt_1_sub_1_eq n (S d) Hn) as Hsum.
  rewrite HSd in Hsum.
  cbn [big_sum Gplus nat_is_monoid] in Hsum.
  rewrite mod_2_succ in Hsum.
  rewrite (Nat.mul_comm 2 d) in *.
  rewrite Nat.Div0.mod_mul in *.
  change (1 - 0) with 1 in Hsum.
  cbn [Nat.eqb] in *.
  pose proof Hsum as Hsum'.
  rewrite <- Nat.add_assoc in Hsum'.
  replace (S d * n) with (d * n + n) in Hsum' by lia.
  pose proof (prf_add_cancel_r Hsum' ltac:(lia)) as Hsumn.
  rewrite Hsumn.
  bdestruct (d * n <=? k).
  - replace (k / n) with d by 
      (symmetry; rewrite Kronecker.div_eq_iff by lia; lia).
    bdestruct_one.
    + rewrite if_false; [lia|].
      rewrite Nat.eqb_neq.
      replace k with (d * n + (k - (d * n))) by lia.
      rewrite mod_add_l, Nat.mod_small by lia.
      lia.
    + rewrite if_true; [lia|].
      rewrite Nat.eqb_eq.
      replace k with (d * n) by lia.
      now rewrite Nat.Div0.mod_mul.
  - replace_bool_lia (d * n + 1 <=? k) false.
    now rewrite IHd by lia.
Qed.

Lemma Nsum_offset_alt_1_sub_1_eq n d k (Hk : k < d * n) : 
  Nsum_offset (2 * d) (fun k => if k mod 2 =? 0 then 1 else (n - 1)) k
  = if k mod n =? 0 then 0 else (k mod n - 1).
Proof.
  assert (Hn : n <> 0) by lia.
  pose proof (Nsum_alt_1_sub_1_eq n d Hn) as Hsum.
  unfold Nsum_offset.
  rewrite Nsum_index_alt_1_sub_1_eq by auto.
  rewrite big_sum_sum.
  cbn [Gplus nat_is_monoid].
  rewrite Nat.mul_comm.
  rewrite Nsum_alt_1_sub_1_eq by auto.
  pose proof (Nat.div_mod_eq k n).
  bdestruct (k mod n =? 0);
  cbn [big_sum Gplus nat_is_monoid].
  - lia.
  - rewrite Nat.add_0_r, (Nat.mul_comm 2), Nat.Div0.mod_mul.
    cbn.
    lia.
Qed.

(* FIXME: Move *)
Lemma perm_eq_mono n m (Hnm : n <= m) f g : 
  perm_eq m f g -> perm_eq n f g.
Proof.
  unfold perm_eq; auto with zarith.
Qed.

Lemma alt_1_sub_1_perm_eq n d : 
  perm_eq (2 * d) (fun k => if k mod 2 =? 0 then 1 else n - 1)
  ((fun k => if k <? d then 1 else (n - 1)) ∘ kron_comm_perm 2 d).
Proof.
  rewrite kron_comm_perm_defn.
  intros k Hk.
  unfold compose.
  pose proof (Nat.mod_upper_bound k 2 ltac:(lia)).
  bdestruct (k mod 2 =? 0).
  - replace -> (k mod 2). 
    now simplify_bools_moddy_lia_one_kernel.
  - replace (k mod 2) with 1 by lia.
    now simplify_bools_lia_one_kernel.
Qed.

Lemma alt_1_sub_1_kron_comm_perm_eq n d : 
  perm_eq (2 * d) ((fun k => if k mod 2 =? 0 then 1 else n - 1) ∘ 
  kron_comm_perm d 2)
  (fun k => if k <? d then 1 else (n - 1)).
Proof.
  rewrite alt_1_sub_1_perm_eq.
  rewrite Combinators.compose_assoc, kron_comm_perm_pseudo_invol.
  reflexivity.
Qed.

Lemma edge_to_idx_succ n ij (Hi : fst ij < snd ij) (Hj : snd ij < S n) : 
  edge_to_idx (S n) ij = 
  if fst ij =? 0 then snd ij - 1 else
    n + edge_to_idx n ((fst ij - 1, snd ij - 1)).
Proof.
  destruct ij as [i j].
  unfold edge_to_idx; cbn [fst snd] in *.
  bdestruct (i =? 0).
  - subst. reflexivity. 
  - rewrite 2!Nsum_reflect_perm by lia.
    rewrite <- 2!triangle_number'.
    replace (S (i - 1)) with i by lia.
    cbn.
    enough (big_sum idn i <= n * (i - 1)).
    + rewrite Nat.add_assoc.
      f_equal; [|lia].
      nia.
    + destruct i; [easy|].
      replace (S i - 1) with i by lia.
      change (S i) with (1 + i).
      rewrite big_sum_sum.
      rewrite Nat.add_0_l.
      rewrite Nat.mul_comm, <- Nsum_constant.
      apply Nsum_le.
      lia.
Qed.

(* FIXME: Move to Qlib.Modulus *)
Lemma div_add_n_r a n (Hn : n <> 0) : 
  (a + n) / n = a / n + 1.
Proof.
  pose proof (Nat.div_mod_eq (a + n) n).
  rewrite mod_add_n_r in H.
  pose proof (Nat.div_mod_eq a n).
  nia.
Qed.

Lemma div_sub_n_r a n : 
  (a - n) / n = a / n - 1.
Proof.
  bdestruct (n =? 0); [subst; reflexivity|].
  bdestruct (a <? n).
  - replace (a - n) with 0 by lia.
    now rewrite 2!Nat.div_small by lia.
  - replace (a / n) with (((a - n) + n) / n) by (f_equal; lia).
    rewrite div_add_n_r by auto.
    lia.
Qed.

Lemma mod_sub_n_r a n (Ha : n <= a) : 
  (a - n) mod n = a mod n.
Proof.
  replace (a - n) with (a - 1 * n) by lia.
  now rewrite sub_mul_mod by lia.
Qed.


Lemma block_to_pairs_perm_succ n : 
  perm_eq (S n * (S n - 1))
    (block_to_pairs_perm (S n))
    (stack_perms (n * 2) (n * (n - 1))
    (kron_comm_perm n 2) 
    (block_to_pairs_perm n)
    ∘ stack_perms n (n * n) idn 
      ((enlarge_permutation (2 * n) (kron_comm_perm n 2)
      (fun k => if k mod 2 =? 0 then 1 else (n - 1))))).
Proof.
  pose proof (Nsum_alt_1_sub_1_eq_diag n) as Haltsum.
  rewrite 2!block_to_pairs_defn, kron_comm_perm_defn at 1.
  etransitivity;
  [|symmetry; apply compose_perm_eq_proper_l;
  [eapply perm_eq_dim_change_if_nonzero;
  [apply (stack_perms_defn (n * 2) (n * (n - 1)))|nia]|
  split; [|
  eapply perm_eq_dim_change_if_nonzero;
  [rewrite <- Haltsum, enlarge_permutation_defn, Haltsum;
    apply (stack_perms_defn n (n * n))|lia]];
  rewrite <- Haltsum; auto_perm]].
  intros k Hk.
  assert (Hn : n <> 0) by lia.
  change ((?f ∘ ?g) k) with ((f ∘ idn) (g k)).
  cbv beta.
  bdestruct (k <? n).
  - cbv delta [compose] beta. 
    replace_bool_lia (k <? n * 2) true.
    unfold wire_to_ordered_edge.
    rewrite 2!Nat.mod_small, 2!Nat.div_small by lia.
    cbn [Nat.ltb Nat.leb fst snd].
    simplify_bools_lia_one_kernel.
    rewrite edge_to_idx_succ by (cbn; lia).
    cbn [fst snd].
    rewrite Nat.eqb_refl.
    lia.
  - rewrite kron_comm_perm_inv'_alt.
    rewrite Nsum_index_alt_1_sub_1_eq, Nsum_offset_alt_1_sub_1_eq by lia.
    assert (k - n < n * n) by lia.
    assert ((k - n) / n * 2 + (if (k - n) mod n =? 0 then 0 else 1) < 2 * n) 
      by (bdestruct_one; show_moddy_lt).
    erewrite (big_sum_eq_bounded);
    [|eapply perm_eq_mono; [|apply alt_1_sub_1_kron_comm_perm_eq]; 
      apply Nat.lt_le_incl, kron_comm_perm_bounded; auto].
    rewrite kron_comm_perm_defn by auto.
    rewrite mod_add_l, Nat.div_add_l by lia.
    rewrite (Nat.mod_small (if _ : bool then _ else _)) by (bdestructΩ').
    rewrite (Nat.div_small (if _ : bool then _ else _)) by (bdestructΩ').
    rewrite div_sub_n_r, Nat.add_0_r in *.
    rewrite mod_sub_n_r in * by lia.
    assert (k / n < S n) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (k / n <> 0) by (rewrite Nat.div_small_iff; lia).
    bdestruct (k mod n =? 0).
    + rewrite Nat.add_0_l, Nat.add_0_r.
      erewrite (big_sum_eq_bounded _ (fun _ => 1)) 
        by (intros ? ?; bdestructΩ').
      rewrite Nsum_1.
      cbv delta [compose] beta.
      replace_bool_lia (k / n - 1 + n <? n * 2) true.
      rewrite mod_add_n_r, div_add_n_r by auto. 
      rewrite Nat.mod_small, (Nat.div_small (_ - _)) by lia.
      cbv delta [wire_to_ordered_edge] beta.
      replace (S n - 1) with n by lia.
      replace -> (k mod n).
      cbn zeta.
      replace_bool_lia (0 <? k / n) true.
      cbn [fst snd Nat.ltb Nat.leb].
      rewrite edge_to_idx_succ by (cbn; lia).
      reflexivity.
    + rewrite Nat.mul_1_l.
      rewrite (big_sum_if_lt n _ (fun _ => 1) (fun _ => n - 1)).
      rewrite Nsum_1, Nsum_constant.
      change ((?x + ?y)%G) with (x + y).
      cbv delta [compose] beta.
      replace (n + (k / n - 1) * (n - 1) + 
        (k mod n - 1) + n) with 
        ((k / n - 1) * (n - 1) + 
        (k mod n - 1) + n * 2) by lia.
      replace ((k / n - 1) * (n - 1) + 
        (k mod n - 1) + n * 2 <? n * 2) with false 
        by (generalize ((k / n - 1) * (n - 1)); intros; bdestructΩ').
      rewrite Nat.add_sub.
      cbv delta [wire_to_ordered_edge] beta.
      pose proof (Nat.mod_upper_bound k n Hn).
      replace (S n - 1) with n by lia.
      rewrite Nat.div_add_l, mod_add_l, (Nat.mod_small (_ - _)), 
        (Nat.div_small (_ - _)), Nat.add_0_r by lia.
      lazy zeta.
      replace_bool_lia (k mod n - 1 <? k / n - 1) (k mod n <? k / n).
      bdestruct_one; cbn [fst snd]; do 2 simplify_bools_lia_one_kernel; 
      rewrite edge_to_idx_succ by (cbn; lia);
      cbn [fst snd]; simplify_bools_lia_one_kernel; [lia|].
      replace (S (k mod n - 1)) with (k mod n - 0) by lia.
      lia.
Qed.

(* Notation "'ZXif' b 'then' zx0 'else' zx1" :=
  (if b as a ) *)

Lemma big_stack_stack_kron_nat_r_prf0 (ns0 ns1 : nat -> nat) n : 
  big_sum (fun k => if k mod 2 =? 0 
    then ns0 (k / 2) else ns1 (k / 2)) (n * 2) =
  big_sum ((fun k => if k <? n then ns0 k else ns1 (k - n))
    ∘ kron_comm_perm 2 n) (2 * n).
Proof.
  rewrite <- Nsum_reorder by auto_perm.
  replace (2 * n) with (n + n) by lia.
  rewrite Nsum_if_lt.
  rewrite <- big_stack_stack_prf.
  apply Nsum_plus.
Qed.

Lemma big_stack_stack_kron_nat_r_prf1 (ms0 ms1 : nat -> nat) n : 
  big_sum ((fun k => if k mod 2 =? 0 
    then ms0 (k / 2) else ms1 (k / 2)) ∘ kron_comm_perm n 2) (n * 2) =
  big_sum (fun k => if k <? n then ms0 k else ms1 (k - n)) (2 * n).
Proof.
  rewrite <- Nsum_reorder by auto_perm.
  rewrite big_stack_stack_kron_nat_r_prf0.
  now rewrite <- Nsum_reorder by auto_perm.
Qed.

Lemma kron_comm_perm_div_r p q k (Hk : k < p * q) : 
  kron_comm_perm p q k / q = k mod p.
Proof.
  rewrite kron_comm_perm_defn by auto.
  rewrite Nat.div_add_l by lia.
  rewrite Nat.div_small by show_moddy_lt.
  lia.
Qed.

Lemma kron_comm_perm_mod_r p q k (Hk : k < p * q) : 
  (kron_comm_perm p q k) mod q = k / p.
Proof.
  rewrite kron_comm_perm_defn by auto.
  rewrite mod_add_l by lia.
  now rewrite Nat.mod_small by show_moddy_lt.
Qed.

Lemma kron_comm_perm_n_2_alts_if_mod2_0_r f g n : 
  perm_eq (n * 2) 
    ((fun k => if k mod 2 =? 0 then f k else g k) ∘ kron_comm_perm n 2)
    (fun k => if k <? n then f (kron_comm_perm n 2 k) 
      else g (kron_comm_perm n 2 k)).
Proof.
  rewrite kron_comm_perm_defn.
  intros k Hk.
  unfold compose.
  rewrite mod_add_l, Nat.mod_small by show_moddy_lt.
  pose proof (Nat.div_small_iff k n ltac:(lia)).
  rewrite kron_comm_perm_defn by auto.
  replace_bool_lia (k / n =? 0) (k <? n).
  reflexivity.
Qed.

(* FIXME: Move to Qlib.PermutationAutomation *)
Ltac ereflexivity :=
  lazymatch goal with 
  | |- ?R ?A ?B => 
    let H := fresh in 
    enough (H : A = B) by 
    (first [rewrite H; reflexivity 
      | rewrite H at 1; reflexivity
      | fail 1 "Could not use" A "=" B "to show goal by rewriting" ])
  | _ => fail "Could not recognize goal as a relation"
  end.
  
Lemma kron_comm_perm_n_2_alts_div2_if_mod2_0_r f g n : 
  perm_eq (n * 2) 
    ((fun k => if k mod 2 =? 0 then f (k / 2) else g (k / 2)) 
      ∘ kron_comm_perm n 2)
    (fun k => if k <? n then f k else g (k - n)).
Proof.
  rewrite kron_comm_perm_n_2_alts_if_mod2_0_r.
  intros k Hk.
  rewrite kron_comm_perm_div_r by auto.
  bdestruct (k <? n).
  - now rewrite Nat.mod_small.
  - now rewrite mod_n_to_2n by lia.
Qed.

Lemma big_stack_stack_enlarge_kron_natural_r ns0 ns1 ms0 ms1 
  (zxs0 : forall k, ZX (ns0 k) (ms0 k)) 
  (zxs1 : forall k, ZX (ns1 k) (ms1 k)) n :
  big_stack (fun k => if k mod 2 =? 0 then ns0 (k / 2) else ns1 (k / 2))
    (fun k => if k mod 2 =? 0 then ms0 (k / 2) else ms1 (k / 2))
    (fun k => 
      if k mod 2 =? 0 as a return 
        ZX (if a then ns0 (k / 2) else ns1 (k / 2))
        (if a then ms0 (k / 2) else ms1 (k / 2))
      then zxs0 (k / 2) else zxs1 (k / 2)) (n * 2) ⟷ 
  big_zx_of_permutation_r (n * 2) (kron_comm_perm n 2) _
    (kron_comm_perm_permutation n 2) ∝
  cast _ _ 
    (big_stack_stack_kron_nat_r_prf0 ns0 ns1 n)
    (big_stack_stack_kron_nat_r_prf1 ms0 ms1 n)
  (
    big_zx_of_permutation_l (2 * n) (kron_comm_perm 2 n) _ 
    (kron_comm_perm_permutation 2 n) ⟷
    big_stack (fun k => if k <? n then ns0 k else ns1 (k - n))
      (fun k => if k <? n then ms0 k else ms1 (k - n))
      (fun k => 
      if k <? n as a return 
        ZX (if a then ns0 k else ns1 (k - n))
        (if a then ms0 k else ms1 (k - n))
      then zxs0 k else zxs1 (k - n)) (2 * n)
  ).
Proof.
  rewrite big_zx_of_permutation_r_natural.
  rewrite cast_compose_distribute.
  unshelve (eapply compose_simplify_casted).
  1: {
    apply big_stack_stack_kron_nat_r_prf1.
  }
  - unfold big_zx_of_permutation_r, big_zx_of_permutation_l.
    rewrite 2!cast_contract_eq.
    rewrite cast_zx_of_perm_natural_l.
    symmetry.
    rewrite cast_zx_of_perm_natural_l.
    apply cast_simplify.
    erewrite zx_of_perm_eq_of_perm_eq; [reflexivity|].
    rewrite Nat.mul_comm.
    erewrite enlarge_permutation_perm_eq_to_eq; [reflexivity|..].
    + rewrite kron_comm_perm_inv'_alt. 
      split; auto_perm.
    + rewrite Nat.mul_comm. 
      now rewrite kron_comm_perm_n_2_alts_div2_if_mod2_0_r.
  - rewrite (big_stack_rebound (Nat.mul_comm 2 n)), 2!cast_contract_eq.
    apply big_stack_simplify_casted_abs.
    + now rewrite kron_comm_perm_n_2_alts_div2_if_mod2_0_r.
    + now rewrite kron_comm_perm_n_2_alts_div2_if_mod2_0_r.
    + intros k ? ? Hk.
      apply ZX_prop_by_mat_prop.
      simpl_cast_semantics.
      clear prfn prfm.
      assert ((kron_comm_perm n 2 k mod 2 =? 0) = (k <? n)). 1: {
        apply eq_iff_eq_true.
        rewrite Nat.eqb_eq, Nat.ltb_lt.
        rewrite kron_comm_perm_mod_r by lia.
        apply Nat.div_small_iff; lia.
      }
      unfold compose.
      bdestruct_all.
      * now rewrite kron_comm_perm_div_r, Nat.mod_small by lia.
      * now rewrite kron_comm_perm_div_r, mod_n_to_2n by lia.
Qed.

Require Import Bipermutations NFBiperm ZXbiperm.

(* FIXME: Move *)

Lemma NF_of_zx_stack {n0 m0 n1 m1} (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) 
  (Hzx0 : ZXbiperm zx0) (Hzx1 : ZXbiperm zx1) : 
  NF_of_zx (zx0 ↕ zx1) =
  stack_NF_biperms (NF_of_zx zx0) (NF_of_zx zx1).
Proof.
  now rewrite 3!NF_of_zx_defn by auto with zxbiperm_db.
Qed.

Lemma NF_of_zx_compose {n m o} (zx0 : ZX n m) (zx1 : ZX m o) 
  (Hzx0 : ZXbiperm zx0) (Hzx1 : ZXbiperm zx1) : 
  NF_of_zx (zx0 ⟷ zx1) =
  compose_NF_biperms (NF_of_zx zx0) (NF_of_zx zx1).
Proof.
  now rewrite 3!NF_of_zx_defn by auto with zxbiperm_db.
Qed.

Lemma biperm_of_zx_stack {n0 m0 n1 m1} (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) 
  (Hzx0 : ZXbiperm zx0) (Hzx1 : ZXbiperm zx1) :
  biperm_of_zx (zx0 ↕ zx1) = stack_biperms n0 m0 n1 m1
    (biperm_of_zx zx0) (biperm_of_zx zx1).
Proof.
  eq_by_WF_perm_eq _;
  [cbn; now auto_perm..|].
  rewrite NF_of_zx_stack by auto.
  now rewrite realize_stack_NF_biperms by auto with WF_NF_biperm_db.
Qed.

Lemma biperm_of_zx_WF {n m} (zx : ZX n m) : WF_Perm (n + m) (biperm_of_zx zx).
Proof. exact (realize_NF_biperm_WF (NF_of_zx zx)). Qed.

#[export] Hint Resolve biperm_of_zx_WF : WF_Perm_db.

Lemma biperm_of_zx_eq_of_proportional {n m} (zx0 zx1 : ZX n m) 
  (Hzx0 : ZXbiperm zx0) (Hzx1 : ZXbiperm zx1) : zx0 ∝ zx1 ->
  biperm_of_zx zx0 = biperm_of_zx	zx1.
Proof.
  intros Hzxs.
  eq_by_WF_perm_eq (n + m).
  apply matrix_of_biperm_inj;
  [auto_biperm..|].
  apply matrix_of_biperm_mat_equiv_of_prop.
  rewrite 2!matrix_of_biperm_of_zx by auto.
  exact Hzxs.
Qed.

Lemma biperm_of_zx_eq_of_prop_rw {n m} {zx0 zx1 : ZX n m} (Hzxs : zx0 ∝ zx1)
  (Hzx0 : ZXbiperm zx0) (Hzx1 : ZXbiperm zx1) : 
  biperm_of_zx zx0 = biperm_of_zx zx1.
Proof. now apply biperm_of_zx_eq_of_proportional. Qed.

Lemma biperm_of_zx_cast {n m n' m'} (zx : ZX n m) prfn prfm : 
  biperm_of_zx (cast n' m' prfn prfm zx) = biperm_of_zx zx.
Proof. now subst. Qed.

Lemma kron_comm_perm_2_n_succ p : 
  perm_eq (2 * (S p)) (kron_comm_perm 2 (S p))
  ( stack_perms (p + S p) 1 (stack_perms p (S p) idn (big_swap_perm p 1)) idn
    ∘ stack_perms (2 * p) 2 (kron_comm_perm 2 p) idn).
Proof.
  rewrite 2!kron_comm_perm_defn.
  intros k Hk.
  unfold compose at 1.
  bdestruct (k <? 2 * p).
  - rewrite (stack_perms_left (k := k)) by auto.
    assert (k / 2 < p) by show_moddy_lt.
    assert (Hor : k mod 2 = 0 \/ k mod 2 = 1) by   
      (pose proof (Nat.mod_upper_bound k 2); lia).
    destruct Hor as [Hor | Hor]; rewrite Hor.
    + rewrite 2!Nat.mul_0_l, Nat.add_0_l.
      now rewrite 2!stack_perms_left by lia.
    + rewrite stack_perms_left, stack_perms_right by lia.
      rewrite big_swap_perm_left by lia.
      lia.
  - rewrite (stack_perms_right (k := k)) by lia.
    rewrite Nat.sub_add by lia.
    bdestruct (k =? p * 2).
    + rewrite stack_perms_left, stack_perms_right by lia.
      rewrite big_swap_perm_right by lia.
      subst k.
      rewrite Nat.Div0.mod_mul, Nat.div_mul by lia.
      lia.
    + replace k with (p * 2 + 1) by lia.
      rewrite mod_add_l, Nat.div_add_l by lia.
      rewrite stack_perms_right by lia.
      cbn; lia.
Qed.




(* Basic notion of independence / S^×{n_1, ..., n_k} is 
  f ∼ g :=
  Nsum_index k ns ∘ f =[perm] Nsum_index k ns ∘ g.
  One important theoretical result we would want is that this means
  f ⁻¹ ∘ g ∈ ∏_i S_(ns i), which means exactly that
  forall i, i < k -> 
  permutation (ns i) (fun a => (f ⁻¹ ∘ g) (big_sum ns i + a))
  which should actually be <-> (we can prove this by induction?)
  perm_bounded (ns i) (fun a => (f ⁻¹ ∘ g) (big_sum ns i + a))

  ... all of which culminates in 
  zx_of_perm (Nsum ns n) f ∝
  big_stack ns ns (fun k => zx_of_perm (ns k) 
    (fun a => (f ∘ g ⁻¹) (big_sum ns k + a))) ⟷
  zx_of_perm (Nsum ns n) g.
*)

(* That's a lot of work, though. The basic program should be to just
   take a permutation and reconstruct it as a series of swap_2_to_2_perm's,
   then reduce those swap_2_to_2_perm's to depend only on the 
   spider the edges land in, then show by induction on the edges that, up 
   to some spider absorption, we get back the original perm. We should also
   get permutation of the edges *almost* for free, by showing this 
   only adds some (tensor_perm n 2 perm idn), which (n_stack n ⊃) absorbs. *)

Definition perm_indep_wrt n ns f g :=
  perm_eq (big_sum ns n) 
    (Nsum_index n ns ∘ f) (Nsum_index n ns ∘ g).

Notation "f '~[/' n ns ']' g" := (perm_indep_wrt n%nat ns%prg f%prg g%prg)
  (at level 70, n at level 9, ns at level 9) : ZX_scope.

Lemma perm_indep_wrt_refl n ns f : f ~[/ n ns ] f.
Proof. unfold perm_indep_wrt. reflexivity. Qed.

Lemma perm_indep_wrt_sym n ns f g : f ~[/ n ns ] g -> g ~[/ n ns] f.
Proof. unfold perm_indep_wrt. apply perm_eq_sym. Qed.

Lemma perm_indep_wrt_trans n ns f g h : f ~[/ n ns ] g -> g ~[/ n ns] h ->
  f ~[/ n ns] h.
Proof. unfold perm_indep_wrt. apply perm_eq_trans. Qed.

Add Parametric Relation n ns : (nat -> nat) (perm_indep_wrt n ns) 
  reflexivity proved by (perm_indep_wrt_refl n ns)
  symmetry proved by (perm_indep_wrt_sym n ns)
  transitivity proved by (perm_indep_wrt_trans n ns)
  as perm_indep_wrt_setoid.

(* FIXME: Move *)

Lemma perm_inj_mono n m (Hm : m <= n) (f : nat -> nat) 
  (Hf : perm_inj n f) : perm_inj m f.
Proof. auto with zarith. Qed.

Lemma perm_shift_lower_permutation_iff_bounded n m f 
  (Hf : permutation n f) (Hm : m <= n) : 
  permutation m f <->
  perm_bounded m f.
Proof.
  split; [apply permutation_is_bounded|].
  intros Hbdd.
  rewrite permutation_iff_surjective.
  apply surjective_of_injective_and_bounded.
  split; [apply (perm_inj_mono _ _ Hm)|]; auto_perm.
Qed.

Lemma kron_n_to_big_kron' {n m} k (A : Matrix (2 ^ n) (2 ^ m)) : 
  kron_n k A = big_kron' (fun _ => n) (fun _ => m) (fun _ => A) k.
Proof.
  induction k; [reflexivity|].
  cbn.
  f_equal;
  [now rewrite Nsum_constant, <- Nat.pow_mul_r; 
  unify_pows_two..|].
  apply IHk.
Qed.

Lemma kron_n_enlarge_permutation_natural {n m} k (A : Matrix (2 ^ n) (2 ^ m))
  f (Hf : permutation k f) (HA : WF_Matrix A) :
  @Mmult (2 ^ (n * k)) (2 ^ (m * k)) (2 ^ (m * k)) 
  (kron_n k A) (perm_to_matrix (m * k) (enlarge_permutation k f (fun _ => m))) =
  perm_to_matrix (n * k) (enlarge_permutation k f (fun _ => n)) × kron_n k A.
Proof.
  rewrite kron_n_to_big_kron'.
  rewrite 2!(Nat.mul_comm _ k), <- 2!(Nsum_constant _ k).
  restore_dims.
  rewrite enlarge_permutation_big_kron'_natural by auto.
  reflexivity.
Qed.

(* Lemma Z_semantics_perm_to_matrix_absorbtion_l n m α f (Hf : permutation m f) :
  perm_to_matrix m f × Z_semantics n m α = Z_semantics n m α.
Proof.
  apply equal_on_conj_basis_states_implies_equal; [auto_wf..|].
  intros g h.
*)

Lemma perm_shift_upper_bounded_below_of_lower_bounded n m f 
  (Hf : permutation n f) (Hm : m <= n) : 
  perm_bounded m f -> (forall k, k < (n - m) -> m <= f (m + k)).
Proof.
  assert (Hfbdd : perm_bounded n f) by auto_perm.
  intros Hbdd.
  intros k Hk.
  pose proof (Hfbdd (m + k) ltac:(lia)).
  bdestruct (f (m + k) <? m); [|lia].
  rewrite <- (perm_shift_lower_permutation_iff_bounded n m f) in Hbdd by auto.
  rewrite permutation_iff_surjective in Hbdd.
  destruct (Hbdd (f (m + k)) ltac:(auto)) as (k' & Hk' & Hfk').
  apply (permutation_is_injective n f Hf) in Hfk'; lia.
Qed.



Lemma perm_shift_upper_permutation_of_lower_bounded n m f 
  (Hf : permutation n f) (Hm : m <= n) : 
  perm_bounded m f ->
  permutation (n - m) (fun a => f (m + a) - m).
Proof.
  intros Hbdd.
  assert (permutation m f) as Hperm by 
    now apply (perm_shift_lower_permutation_iff_bounded n m).
  pose proof (perm_shift_upper_bounded_below_of_lower_bounded n m f 
    Hf Hm Hbdd) as Hbelow.
  apply permutation_iff_surjective, surjective_of_injective_and_bounded.
  split.
  - intros k l Hk Hl.
    pose proof (Hbelow k Hk).
    pose proof (Hbelow l Hl).
    pose proof (permutation_is_injective n f Hf (m + k) (m + l)).
    lia.
  - intros k Hk.
    pose proof (permutation_is_bounded n f Hf (m + k)).
    lia.
Qed.

Instance perm_eq_perm_indep_wrt_subrel n ns : 
  subrelation (perm_eq (big_sum ns n)) (perm_indep_wrt n ns).
Proof.
  intros f g Hfg.
  unfold perm_indep_wrt.
  now rewrite Hfg.
Qed.

Add Parametric Morphism n ns : compose with signature
  perm_indep_wrt n ns ==> 
  on_predicate_relation_l
    (fun f => perm_bounded (big_sum ns n) f)
    (perm_eq (big_sum ns n)) ==> 
  perm_indep_wrt n ns as compose_perm_indep_wrt_proper_l.
Proof.
  unfold perm_indep_wrt.
  intros f f' Hf g g' [Hgbdd Hg].
  rewrite <- 2!Combinators.compose_assoc.
  rewrite <- Hg.
  now rewrite Hf.
Qed.

Lemma perm_indep_wrt_diff_idn n ns f g (Hf : permutation (big_sum ns n) f)
  (Hg : permutation (big_sum ns n) g) (Hfg : f ~[/ n ns] g) : 
  f ∘ perm_inv (big_sum ns n) g ~[/ n ns] idn.
Proof.
  unfold perm_indep_wrt in *.
  rewrite <- Combinators.compose_assoc.
  rewrite Hfg, Combinators.compose_assoc.
  now rewrite perm_inv_rinv_of_permutation.
Qed.

Lemma Nsum_index_lt_iff n ns k l (Hl : l < n) :
  Nsum_index n ns k < l <-> k < big_sum ns l.
Proof.
  bdestruct (k <? big_sum ns n).
  - pose proof (Nsum_index_offset_spec n ns k ltac:(auto)).
    split.
    + intros Hlt.
      pose proof (Nsum_le_r (S (Nsum_index n ns k)) l ns).
      cbn in *.
      lia.
    + intros Hlt.
      pose proof (Nsum_index_spec n ns k ltac:(auto)).
      pose proof (Nsum_le_r l (Nsum_index n ns k) ns).
      lia.
  - rewrite Nsum_index_big by auto.
    pose proof (Nsum_le_r l n ns).
    lia.
Qed.

Lemma perm_eq_stack_parts_of_lower_bounded n m f (Hf : permutation n f)
  (Hm : m <= n) (Hbdd : perm_bounded m f) : 
  perm_eq n f 
    (stack_perms m (n - m) f (fun k => f (m + k) - m)).
Proof.
  intros k Hk.
  bdestruct (k <? m).
  - now rewrite stack_perms_left by lia.
  - rewrite stack_perms_right by lia.
    pose proof (perm_shift_upper_bounded_below_of_lower_bounded 
      n m f Hf Hm Hbdd) as Hup.
    generalize (Hup (k - m) ltac:(lia)).
    replace (m + (k - m)) with k by lia.
    lia.
Qed.

Lemma perm_indep_wrt_idn_succ_perm n ns f
  (Hf : permutation (big_sum ns (S n)) f) (Hfidn : f ~[/ (S n) ns] idn) : 
  permutation (big_sum ns n) f.
Proof.
  assert (big_sum ns n <= big_sum ns (S n)) as Hle by (cbn; lia).
  apply (perm_shift_lower_permutation_iff_bounded _ _ f Hf Hle).
  intros k Hk.
  generalize (Hfidn k ltac:(lia)).
  unfold compose.
  assert (Nsum_index (S n) ns k < n) as Hlt
    by (rewrite Nsum_index_lt_iff; lia).
  revert Hlt.
  cbn.
  simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

Lemma perm_indep_wrt_idn_succ_mono n ns f (Hfidn : f ~[/ (S n) ns] idn) : 
  f ~[/ n ns] idn.
Proof.
  intros k Hk.
  generalize (Hfidn k ltac:(cbn;lia)).
  unfold compose.
  cbn.
  pose proof (Nsum_index_bounded n ns k ltac:(intros ->; cbn in *; lia)).
  bdestructΩ'.
Qed.


Lemma perm_indep_wrt_idn_perm_eq_big_stack_perms n ns f
  (Hf : permutation (big_sum ns n) f) (Hfidn : f ~[/ n ns] idn) : 
  perm_eq (big_sum ns n) f
    (big_stack_perms n ns 
    (fun n' => (fun k => f (big_sum ns n' + k) - big_sum ns n'))).
Proof.
  induction n; [easy|].
  rewrite big_stack_perms_succ.
  assert (big_sum ns n <= big_sum ns (S n)) as Hle by (cbn; lia).
  pose proof (perm_indep_wrt_idn_succ_perm n ns f Hf Hfidn) as Hfnperm.
  assert (Hbdd : perm_bounded (big_sum ns n) f) by auto_perm.
  specialize (IHn Hfnperm).
  assert (f ~[/ n ns] idn) by now apply perm_indep_wrt_idn_succ_mono.
  rewrite <- IHn by auto.
  replace (ns n) with (big_sum ns (S n) - big_sum ns n) by (cbn; lia).
  apply perm_eq_stack_parts_of_lower_bounded;
  solve [auto | cbn;lia].
Qed.

Lemma perm_indep_wrt_idn_all_shifts_perms n ns f
  (Hf : permutation (big_sum ns n) f) (Hfidn : f ~[/ n ns] idn) : 
  forall m, m < n -> permutation (ns m) 
    (fun k => f (big_sum ns m + k) - big_sum ns m).
Proof.
  induction n; [easy|].
  intros m Hm.
  assert (big_sum ns n <= big_sum ns (S n)) as Hle by (cbn; lia).
  pose proof (perm_indep_wrt_idn_succ_perm n ns f Hf Hfidn) as Hfnperm.
  assert (f ~[/ n ns] idn) by now apply perm_indep_wrt_idn_succ_mono.
  bdestruct (m <? n); [now apply IHn|].
  replace m with n in * by lia.
  replace (ns n) with (big_sum ns (S n) - big_sum ns n) by (cbn; lia).
  apply perm_shift_upper_permutation_of_lower_bounded; 
  first [cbn; lia | auto_perm].
Qed.

Lemma compose_Nsum_index_l_WF_input_func n ns f : 
  WF_input_func (big_sum ns n) n (Nsum_index n ns ∘ f).
Proof.
  bdestruct (n =? 0); [now subst|].
  intros k Hk.
  unfold compose.
  now apply Nsum_index_bounded.
Qed.

(* FIXME: Move *)
Lemma count_func_vals_reorder m f g (Hg : permutation m g) : 
  count_func_vals m (f ∘ g) = count_func_vals m f.
Proof.
  apply functional_extensionality.
  intros k.
  unfold count_func_vals.
  symmetry.
  exact (Nsum_reorder m _ g Hg).
Qed.

Lemma Nsum_index_eq_iff n ns k l (Hk : k < big_sum ns n) (Hl : l < n) : 
  Nsum_index n ns k = l <-> (big_sum ns l <= k < big_sum ns (S l)).
Proof.
  split.
  - intros; subst l. 
    pose proof (Nsum_index_offset_spec n ns k Hk).
    cbn. 
    lia.
  - intros [Hle Hlt].
    enough (~ Nsum_index n ns k < l /\ Nsum_index n ns k < S l) by lia.
    rewrite Nsum_index_lt_iff by auto.
    split; [lia|].
    bdestruct (S l =? n).
    + replace -> (S l).
      apply Nsum_index_bounded; lia.
    + rewrite Nsum_index_lt_iff by lia.
      auto.
Qed.

Lemma Nsum_index_eqb_iff n ns k l (Hk : k < big_sum ns n) (Hl : l < n) : 
  (Nsum_index n ns k =? l) = 
  (big_sum ns l <=? k) && (k <? big_sum ns (S l)).
Proof.
  apply eq_iff_eq_true; 
  rewrite Nat.eqb_eq, andb_true_iff, Nat.ltb_lt, Nat.leb_le.
  now apply Nsum_index_eq_iff.
Qed.

Lemma count_func_vals_Nsum_index n ns : 
  perm_eq n (count_func_vals (big_sum ns n) (Nsum_index n ns)) ns.
Proof.
  intros l Hl.
  unfold count_func_vals.
  erewrite big_sum_eq_bounded.
  2: {
    intros k Hk.
    rewrite Nsum_index_eqb_iff by lia.
    rewrite Nat.leb_antisym.
    rewrite andb_if, negb_if.
    apply f_equal_if_precedent_same; [reflexivity|].
    rewrite Nat.ltb_nlt.
    intros Hkl.
    cbn [big_sum Gplus nat_is_monoid].
    replace_bool_lia (k <? big_sum ns l + ns l) 
      (k - big_sum ns l <? ns l).
    reflexivity.
  }
  rewrite (big_sum_split n l ns Hl).
  rewrite <- Nat.add_assoc.
  rewrite (Nsum_if_lt (big_sum ns l) _ (fun _ => 0)
    (fun i => if i <? ns l then 1 else 0)).
  rewrite Nsum_constant, Nat.mul_0_r.
  rewrite (Nsum_if_lt (ns l) _ (fun _ => 1) (fun _ => 0)).
  rewrite Nsum_1, Nsum_constant.
  lia.
Qed.



Lemma perm_indep_wrt_perm_of_input_func n ns f 
  (Hf : permutation (big_sum ns n) f) :
  f ~[/ n ns] perm_of_input_func (big_sum ns n) 
  (Nsum_index n ns ∘ f).
Proof.
  unfold perm_indep_wrt.
  symmetry.
  etransitivity;
  [|apply perm_of_input_func_decomp, compose_Nsum_index_l_WF_input_func].
  rewrite count_func_vals_reorder by auto.
  erewrite Nsum_index_perm_eq_to_eq at 1; [reflexivity|].
  now rewrite count_func_vals_Nsum_index.
Qed.

(* FIXME: Generalize, move to top, use for ZX_complete_conenctions_prf_2 *)
Lemma ZX_decomp_like_spider_stack_prf n : 
  0 = big_sum (fun _ => 0) n.
Proof. rewrite Nsum_constant; lia. Qed.

Definition ZX_decomp_like_spider_stack m spis infunc 
  (color : nat -> bool) αs deg 
  (* (Hin : WF_input_func m spis)  *)
  (* (Hdeg : forall k l, k < spis -> l < spis -> deg (k, l) = deg (l, k)) *) :
  (* ZX 0 (m + big_sum (fun i => big_sum (deg i) spis) spis) := *)
  ZX 0 (big_sum (fun i => count_func_vals m infunc i + big_sum (deg i) spis) spis) :=
  cast _ _ (ZX_decomp_like_spider_stack_prf _) eq_refl
    (big_stack (fun _ => 0) _ 
      (fun k => b2ZX (color k) 0 _ (αs k)) spis).

Lemma n_stack_to_big_stack {n m} k (zx : ZX n m) : 
  k ⇑ zx ∝
  cast _ _ (eq_sym (Nsum_constant n k)) (eq_sym (Nsum_constant m k))
  (big_stack _ _ (fun _ => zx) k).
Proof.
  induction k; [cbn; now rewrite cast_id|].
  rewrite (@big_stack_rebound (S k) (1 + k) ltac:(lia)).
  rewrite big_stack_split_add.
  cbn; rewrite !cast_contract_eq.
  clean_eqns rewrite cast_stack_distribute_fwd_l.
  apply stack_simplify.
  - now rewrite stack_empty_l, cast_id.
  - rewrite IHk.
    cast_irrelevance.
Qed.

(* 

Definition ZX_decomp_like_spider_stack_alt m spis infunc 
  (color : nat -> bool) αs deg 
  (* (Hin : WF_input_func m spis)  *)
  (* (Hdeg : forall k l, k < spis -> l < spis -> deg (k, l) = deg (l, k)) *) :
  (* ZX 0 (m + big_sum (fun i => big_sum (deg i) spis) spis) := *)
  ZX 0 (big_sum (count_func_vals m infunc) spis +
    big_sum (fun i => big_sum (deg i) spis) spis) :=
  n_cap (big_sum (fun _ => 1) spis) ⟷
    (big_stack (fun _ => 1) _ (fun k => b2ZX (color k) 1 _ (αs k)) spis
    ↕ big_stack (fun _ => 1) _ (fun k => b2ZX (color k) 1 _ (αs k)) spis).

Lemma ZX_decomp_like_spider_stack_from_alt m spis infunc color αs deg :
  ZX_decomp_like_spider_stack_alt m spis infunc color αs deg ∝
  ZX_decomp_like_spider_stack m spis infunc color αs deg ⟷
  cast _ _ (big_stack_stack_prf _ _ _) 
  (eq_trans (eq_sym (Nsum_plus _ _ _)) (eq_trans
    (big_stack_stack_prf _ _ _) (Nsum_reorder _ _ _ 
      (kron_comm_perm_permutation spis 2))))
  (big_zx_of_permutation_r (spis * 2) (kron_comm_perm spis 2) _
    (kron_comm_perm_permutation spis 2)).
Proof.
  rewrite compose_zxperm_r' by auto_zxperm.
  rewrite cast_transpose.
  rewrite big_zx_of_permutation_r_transpose.
  big_stack_stack_enlarge_kron_natural_r

  big_stack_stack_enlarge_kron_natural_r
  



Definition ZX_graph_core_to_decomp_like m k infunc color αs deg : ZX m 0 :=
  ZX_of_io m ZXG.(core_spis) ZXG.(core_infunc) ZXG.(core_color) ⟷
  ZX_complete_form ZXG.(core_spis) ZXG.(core_color) 
    ZXG.(core_αs) ZXG.(core_deg).




Lemma perm_of_input_func_succ m f :
  perm_eq (S m) (perm_of_input_func (S m) f)
    (stack_perms (count_func_vals (S m) f 0) (S m - count_func_vals (S m) f 0)
      idn (perm_of_input_func m (fun k => S ∘

Definition contract_input_func_0 m n f v :=
  Nsum_index 
  

Definition ZX_graph_core_dec_spis {m} (ZXG : ZX_graph_core m) 
  : ZX_graph_core (m - count_func_vals m ZXG.(core_infunc) 0) :=
  {|
    core_spis := ZXG.(core_spis) - 1;
    core_infunc
  |} *)




Lemma biperm_of_zx_nstack {n m} k (zx : ZX n m) (Hzx : ZXbiperm zx) : 
  perm_eq (k * n + k * m) (biperm_of_zx (k ⇑ zx))
  (tensor_perms k (n + m) idn (biperm_of_zx zx)).
  (* enlarge_permutation_constant *)
  (* (kron_comm_perm (n + m) k 
    ∘ tensor_perms k (n + m) idn (biperm_of_zx zx)
    ∘ kron_comm_perm k (n + m)). *)
Proof.
  bdestruct (k =? 2).
  subst. 
  assert (Hrw : 2 ⇑ zx ∝ @cast (2 * n) (2 * m) (n + n) (m + m) ltac:(lia) ltac:(lia) (zx ↕ zx)).
  cbn.
  clean_eqns rewrite stack_empty_r, cast_stack_r.
  cast_irrelevance.
  rewrite (biperm_of_zx_eq_of_prop_rw Hrw) by auto with zxbiperm_db.
  rewrite biperm_of_zx_cast.
  rewrite biperm_of_zx_stack by auto with zxbiperm_db.
  assert (Hrev : bipermutation (n + m) (biperm_of_zx zx)) 
    by (now apply biperm_of_zx_bipermutation).
  revert Hrev.
  generalize (biperm_of_zx zx).
  intros f Hf.
  eapply perm_eq_dim_change_if_nonzero;
  [rewrite stack_biperms_defn|lia].
  eapply perm_eq_dim_change_if_nonzero;
  [rewrite tensor_perms_defn|lia].
  intros k Hk.
  unfold compose at 1.
  intros k Hk.

  
  rewrite Combinators.compose_assoc, tensor_perms_kron_comm_perm_natural.
  rewrite <- Combinators.compose_assoc
  cbn [n_stack].
  


tensor_perms_kron_comm_perm_natural

















Lemma ZX_complete_form_first_disconnected n color alphas deg 
  (H0 : forall k, k < S n -> k <> 0 -> deg (0, k) = 0) : 
  ZX_complete_form (S n) color alphas deg ∝
  b2ZX (color 0) 1 0 (alphas O) ↕
  ZX_complete_form n (fun k => color (1 + k)) (fun k => alphas (1 + k))
    (fun ij => deg (1 + fst ij, 1 + snd ij)).
Proof.
  rewrite 2!ZX_complete_large_form_equiv.
  unfold ZX_large_form.
  rewrite <- 2!(@compose_empty_r 1).
  rewrite 2!stack_compose_distr, 2!stack_empty_l.
  assert (Heq : big_sum (Nat.double ∘ deg ∘ idx_to_edge (S n)) 
    (S n * (S n - 1) / 2) = 0 + big_sum
    (Nat.double ∘ (fun ij => deg (1 + fst ij, 1 + snd ij))
     ∘ idx_to_edge n) (n * (n - 1) / 2)). 1: {
    rewrite <- triangle_number.
    cbn [big_sum].
    rewrite Nat.add_comm.
    rewrite big_sum_sum.
    cbn [nat_is_monoid Gplus].
    f_equal.
    - rewrite big_sum_0_bounded; [reflexivity|].
      intros k Hk.
      unfold compose.
      assert (Hk' : k < S n * (S n - 1) / 2) by 
        (rewrite <- triangle_number; cbn; lia).
      rewrite idx_to_edge_succ by auto.
      simplify_bools_lia_one_kernel.
      now rewrite H0 by lia.
    - rewrite (Nsum_permutation n) by auto_perm.
      apply big_sum_eq_bounded.
      intros k Hk.
      unfold compose.
      do 2 f_equal.
      rewrite idx_to_edge_succ by 
        (rewrite <- !triangle_number in *; cbn; lia).
      replace_bool_lia (n + k <? n) false.
      now rewrite add_sub'.
  }
  pose proof Heq as Heq'.
  rewrite 2!ZX_connections_stack_alt_prf in Heq'.
  unshelve (eapply compose_simplify_casted); [auto|..].
  1: rewrite cast_compose_distribute.
  1: unshelve (eapply compose_simplify_casted). 1: {
    rewrite <- 2!Nsum_reorder by auto_perm.
    auto.
  }
  - unfold ZX_large_stack.
    rewrite (big_stack_split_add _ _ _ 1 n).
    rewrite 2!cast_contract_eq.
    cbn [big_stack].
    rewrite stack_empty_l.
    prop_exists_nonzero 1%R.
    rewrite Mscale_1_l.
    simpl_cast_semantics.
    cbn [ZX_semantics].
    simpl_cast_semantics.
    rewrite 2!big_stack_semantics.
    assert (Hsum0 : (big_sum (fun i=>((fun k0=>deg(idx_to_edge (S n) (k0/2)))
        ∘ block_to_pairs_perm (S n)) (0 * (S n - 1) + i)) (S n - 1)) = 0).
    1: {
      rewrite big_sum_0_bounded; [reflexivity|].
      intros k Hk.
      rewrite Nat.mul_0_l, Nat.add_0_l.
      unfold compose.
      rewrite block_to_pairs_defn by lia.
      unfold wire_to_ordered_edge.
      rewrite (Nat.mod_small k), (Nat.div_small k) by auto.
      cbn -[Nat.divmod Nat.div].
      replace_bool_lia (0 <=? k) true.
      rewrite Nat.div_mul by lia.
      rewrite idx_to_edge_succ by (rewrite <- triangle_number; cbn; lia).
      simplify_bools_lia_one_kernel.
      apply H0; lia.
    }
    assert (Hsumbig_step1 : perm_eq n (fun k =>
      big_sum (fun i => ((fun k0 => deg (idx_to_edge (S n) (k0 / 2)))
       ∘ block_to_pairs_perm (S n)) ((1 + k) * (S n - 1) + i)) (S n - 1))
      (fun k => big_sum (fun i => ((fun k0 => deg
      (1 + fst (idx_to_edge n (k0 / 2)), 1 + snd (idx_to_edge n (k0 / 2)))) ∘ 
       block_to_pairs_perm n) (k * (n - 1) + i)) (n - 1))). 1: {
    intros k Hk.
    replace (S n - 1) with (S (n - 1)) by lia.
    rewrite (big_sum_sum 1 (n - 1)).
    cbn [Gplus nat_is_monoid].
    etransitivity; [|apply Nat.add_0_l].
    f_equal.
    * cbn [big_sum nat_is_monoid Gplus].
      unfold compose.
      rewrite block_to_pairs_defn by nia.
      rewrite Nat.add_0_r.
      unfold wire_to_ordered_edge.
      replace (S n - 1) with (S (n - 1)) by lia.
      rewrite Nat.Div0.mod_mul, Nat.div_mul by lia.
      replace_bool_lia (0 <? 1 + k) true.
      cbn [fst snd Nat.ltb Nat.leb].
      rewrite Nat.div_add_l, Nat.add_0_r, Nat.add_0_l by lia.
      rewrite edge_to_idx_to_edge by (cbn; lia).
      apply H0; lia.
    * apply big_sum_eq_bounded.
      intros l Hl.
      unfold compose.
      rewrite block_to_pairs_defn by nia.
      cbv delta [wire_to_ordered_edge] beta.
      replace (S n - 1) with (S (n - 1)) by lia.
      rewrite Nat.div_add_l, mod_add_l, 
        (Nat.div_small (1 + _)), (Nat.mod_small (1 + _)) by lia.
      rewrite Nat.add_0_r.
      cbn zeta.
      change (1 + l <? 1 + k) with (l <? k).
      bdestruct (l <? k); cbn [fst snd].
      --replace_bool_lia (1 + k <? 1 + l) false.
        rewrite Nat.div_add_l, Nat.add_0_r, edge_to_idx_to_edge by (cbn; lia).
        rewrite block_to_pairs_defn by nia.
        cbv delta [wire_to_ordered_edge] beta.
        rewrite Nat.div_add_l, mod_add_l, 
          (Nat.div_small l), (Nat.mod_small l), Nat.add_0_r by lia.
        cbn zeta.
        replace_bool_lia (l <? k) true.
        cbn [fst snd].
        replace_bool_lia (k <? l) false.
        rewrite Nat.div_add_l, Nat.add_0_r, edge_to_idx_to_edge by (cbn; lia).
        reflexivity.
      --replace_bool_lia (1 + k <? S (1 + l)) true.
        rewrite Nat.div_mul, edge_to_idx_to_edge by (cbn; lia).
        rewrite block_to_pairs_defn by nia.
        cbv delta [wire_to_ordered_edge] beta.
        rewrite Nat.div_add_l, mod_add_l, 
          (Nat.div_small l), (Nat.mod_small l), Nat.add_0_r by lia.
        cbn zeta.
        replace_bool_lia (l <? k) false.
        cbn [fst snd].
        replace_bool_lia (k <? S l) true.
        rewrite Nat.div_mul, edge_to_idx_to_edge by (cbn; lia).
        reflexivity.
    }

    assert (Hsumbig : big_sum (fun k => big_sum (fun i =>
      ((fun k0 => deg (idx_to_edge (S n) (k0 / 2)))
        ∘ block_to_pairs_perm (S n)) ((1 + k) * (S n - 1) + i))
        (S n - 1)) n =
      big_sum ((fun k0 => deg (1 + fst (idx_to_edge n (k0 / 2)),
        1 + snd (idx_to_edge n (k0 / 2)))) ∘ block_to_pairs_perm n)
        (n * (n - 1))).
    1: {
      rewrite big_stack_mult_prf.
      apply big_sum_eq_bounded.
      apply Hsumbig_step1.
    }
    f_equal; cbn [big_sum Gplus nat_is_monoid]; rewrite ?Hsum0; [auto|..].
    + now rewrite Hsumbig.
    + now rewrite Nsum_1.
    + reflexivity.
    + apply big_kron'_eq_bounded_dims; [auto_perm..|].
      intros k Hk.
      now rewrite Hsumbig_step1 by auto.
  - unfold ZX_large_perm, big_zx_of_permutation_l.
    rewrite !cast_contract_eq.
    rewrite cast_zx_of_perm_natural_l.
    symmetry.
    rewrite cast_zx_of_perm_natural_l.
    apply cast_simplify.
    erewrite zx_of_perm_perm_eq_to_eq_proper; [reflexivity|].
    rewrite <- Nsum_reorder by auto_perm.
    symmetry.
    rewrite enlarge_permutation_defn.
    rewrite Heq', Nat.add_0_l.
    rewrite enlarge_permutation_defn.
    intros k Hk.
    rewrite 2!block_to_pairs_perm_inv'.
    assert (Hsmall : big_sum (fun k0 => 
      deg (idx_to_edge (S n) (k0 / 2))) (n * 2) = 0). 1:{
      rewrite big_sum_0_bounded; [reflexivity|].
      intros l Hl.
      assert (l / 2 < n) by show_moddy_lt.
      rewrite idx_to_edge_succ by (rewrite <- triangle_number;
        cbn -[Nat.div]; lia). 
      replace_bool_lia (l / 2 <? n) true.
      apply H0; lia.
    }
    assert (Hbig : perm_eq (n * (n - 1))
      (fun i => deg (idx_to_edge (S n) ((n * 2 + i) / 2)))
      (fun k0 => deg (1 + fst (idx_to_edge n (k0 / 2)), 
      1 + snd (idx_to_edge n (k0 / 2))))). 1: {
      intros l Hl.
      rewrite idx_to_edge_succ by (apply Nat.Div0.div_lt_upper_bound;
        rewrite (Nat.mul_comm 2), triangle_number_exact; nia).
      rewrite Nat.div_add_l by lia.
      replace_bool_lia (n + l / 2 <? n) false.
      now rewrite add_sub'.
    }
    f_equal; cycle 1.
    + replace (S n * (S n - 1)) with ((n*2) + n * (n - 1)) by (nia).
      rewrite Nsum_offset_add 
        by (replace (n*2+n*(n-1)) with (S n*(S n-1)) by nia; lia).
      rewrite Hsmall.
      cbn [Nat.ltb Nat.leb].
      rewrite Nat.sub_0_r.
      apply equal_f.
      now rewrite Hbig.
    + replace (S n * (S n - 1)) with ((n*2) + n * (n - 1)) by (nia).
      rewrite Nsum_index_add 
        by (replace (n*2+n*(n-1)) with (S n*(S n-1)) by nia; lia).
      rewrite Hsmall.
      cbn [Nat.ltb Nat.leb].
      rewrite Nat.sub_0_r.
      bdestruct (n =? 0); [subst; cbn in *; lia|].
      etransitivity;
      [apply (f_equal2 big_sum); [reflexivity|]|
        apply big_sum_eq_bounded].
      Abort.

(* Old: *)


(* Definition reps_to_front_perm n :=
  fun k => if n * n <=? k then k else
  if k mod n =? 0 (* is in front of its section *) 
  then k / n 
  else k + n - S (k / n).

Definition reps_from_front_perm n :=
  fun k => if n * n <=? k then k else
  if k <? n (* k / m =? 0 *)
  then n * (k mod n) 
  else k - (n - S ((k - n) / (n - 1))).

Lemma reps_to_front_perm_WF n : WF_Perm (n * n) (reps_to_front_perm n).
Proof. intros k Hk. unfold reps_to_front_perm. bdestructΩ'. Qed.

Lemma reps_from_front_perm_WF n : WF_Perm (n * n) (reps_from_front_perm n).
Proof. intros k Hk. unfold reps_from_front_perm. bdestructΩ'. Qed.

#[export] Hint Resolve reps_to_front_perm_WF 
  reps_from_front_perm_WF : WF_Perm_db. 

Lemma reps_to_front_perm_defn n : 
  perm_eq (n * n)
    (reps_to_front_perm n)
    (fun k => if k mod n =? 0 then k / n else k + n - S (k / n)).
Proof.
  intros k Hk.
  unfold reps_to_front_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma reps_from_front_perm_defn n : 
  perm_eq (n * n)
    (reps_from_front_perm n)
    (fun k => if k <? n then n * (k mod n) else k - (n - S ((k - n) / (n - 1)))).
Proof.
  intros k Hk.
  unfold reps_from_front_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma reps_to_front_perm_bounded n : 
  perm_bounded (n * n) (reps_to_front_perm n).
Proof.
  intros k Hk.
  rewrite reps_to_front_perm_defn by auto.
  bdestruct_one.
  - show_moddy_lt.
  - bdestruct (k <? n * (n - 1)); [lia|].
    enough (k / n >= (n - 1)) by lia.
    apply Nat.div_le_lower_bound; lia.
Qed.

Lemma reps_from_front_perm_bounded n : 
  perm_bounded (n * n) (reps_from_front_perm n).
Proof.
  intros k Hk.
  rewrite reps_from_front_perm_defn by auto.
  bdestruct_one.
  - show_moddy_lt.
  - lia.
Qed.

#[export] Hint Resolve reps_to_front_perm_bounded
  reps_from_front_perm_bounded : perm_bounded_db.

(* Lemma reps_from_front_perm_spec n : 
  perm_eq (n * n) (reps_to_front_perm n) 
    (enlarge_permutation (2 * n) (kron_comm_perm n 2)
      (fun k => if k mod 2 =? 0 then 1 else (n - 1))).
Proof.
  bdestruct (n =? 0); [subst; intros k Hk; lia|].
  assert (Heq : big_sum (fun k => if k mod 2 =? 0 then 1 else (n - 1)) (2 * n)
   = n * n).
  1: {
    change (fun k => if k mod 2 =? 0 then 1 else n - 1) with 
      (fun k => (fun (kdiv2 kmod2 : nat) => if kmod2 =? 0 then 1 else n - 1)
        (k / 2) (k mod 2)). 
    rewrite <- big_sum_double_sum.
    rewrite big_sum_constant.
    simpl.
    rewrite times_n_nat.
    nia.
  }
  rewrite reps_to_front_perm_defn.
  rewrite <- Heq.
  rewrite enlarge_permutation_defn.
  rewrite Heq.
  intros k Hk. *)

Lemma reps_to_from_front_inv n : 
  reps_to_front_perm n ∘ reps_from_front_perm n = idn.
Proof.
  eq_by_WF_perm_eq (n * n).
  rewrite reps_to_front_perm_defn, reps_from_front_perm_defn.
  intros k Hk.
  unfold compose.
  bdestruct (k <? n).
  - rewrite Nat.mul_comm, Nat.Div0.mod_mul by lia.
    cbn [Nat.eqb].
    rewrite Nat.div_mul by lia.
    apply Nat.mod_small; lia.
  - assert (n <> 1) by lia.
    assert (2 <= n) by lia.
    assert ((k - n) / (n - 1) < n) by  
      (apply Nat.Div0.div_lt_upper_bound; lia).
    replace (k - (n - S ((k - n) / (n - 1)))) with 
      (((k - n) / (n - 1)) * n + ((k - n) mod (n - 1) + 1))
      by (pose proof (Nat.div_mod_eq (k - n) (n - 1)); lia).
    rewrite if_false.
    + rewrite Nat.div_add_l by lia.
      rewrite (Nat.div_small (_ + 1)) 
        by (pose proof (Nat.mod_upper_bound (k - n) (n - 1)); lia).
      rewrite Nat.add_0_r.
      pose proof (Nat.div_mod_eq (k - n) (n - 1)); lia.
    + rewrite Nat.eqb_neq.
      rewrite mod_add_l.
      rewrite (Nat.mod_small (_ + 1)) 
        by (pose proof (Nat.mod_upper_bound (k - n) (n - 1)); lia).
      lia.
Qed.

Lemma reps_from_front_permutation n : 
  permutation (n * n) (reps_from_front_perm n).
Proof.
  apply permutation_iff_surjective.
  apply surjective_of_injective_and_bounded.
  split; [|auto_perm].
  intros k l Hk Hl.
  intros Heq.
  apply (f_equal (reps_to_front_perm n)) in Heq.
  pose proof (equal_f (reps_to_from_front_inv n) k).
  pose proof (equal_f (reps_to_from_front_inv n) l).
  unfold compose in *.
  congruence.
Qed.

#[export] Hint Resolve reps_from_front_permutation : perm_db.

Lemma reps_from_front_perm_inv n : 
  perm_eq (n * n) 
    (perm_inv (n * n) (reps_from_front_perm n))
    (reps_to_front_perm n).
Proof.
  rewrite <- (compose_idn_l (perm_inv _ _)).
  rewrite compose_perm_inv_r by auto_perm.
  now rewrite reps_to_from_front_inv.
Qed.

Lemma reps_to_front_permutation n : 
  permutation (n * n) (reps_to_front_perm n).
Proof.
  rewrite <- reps_from_front_perm_inv.
  auto_perm.
Qed.

#[export] Hint Resolve reps_to_front_permutation : perm_db.

Lemma reps_to_front_perm_inv n : 
  perm_eq (n * n) 
    (perm_inv (n * n) (reps_to_front_perm n))
    (reps_from_front_perm n).
Proof.
  rewrite perm_inv_perm_eq_iff by auto_perm.
  now rewrite reps_from_front_perm_inv.
Qed.

Lemma reps_from_to_front_inv n : 
  reps_from_front_perm n ∘ reps_to_front_perm n = idn.
Proof.
  eq_by_WF_perm_eq (n * n).
  rewrite <- reps_from_front_perm_inv.
  auto_perm.
Qed.



Fixpoint block_to_pairs_perm n := 
  match n with 
  | O => idn
  | S n' => 
    stack_perms (n' * 2) (n' * (n' - 1))
      (kron_comm_perm n' 2) 
      (block_to_pairs_perm n')
    ∘ stack_perms n' (n' * n') idn 
      (reps_to_front_perm n')
  end.

Lemma block_to_pairs_permutation n : 
  permutation (n * (n - 1)) (block_to_pairs_perm n).
Proof.
  induction n; [cbn; auto_perm|].
  cbn [block_to_pairs_perm].
  assert (S n * (S n - 1) = n * 2 + n * (n - 1)) by nia.
  auto_perm.
Qed.

#[export] Hint Resolve block_to_pairs_permutation : perm_db.

Lemma block_to_pairs_perm_spec n i j (Hi : i < j) (Hj : j < n) : 
  {(k, l) : nat * nat | k < n * (n - 1) /\ l < n * (n - 1) /\
  k / (n - 1) = i /\ l / (n - 1) = j /\
  block_to_pairs_perm n k + 1 = block_to_pairs_perm n l }.
Proof.
  induction n; [|destruct n];
  [lia..|].



 *)
