Require Import CoreData.CoreData.

Require Import SpiderInduction.

Open Scope ZX_scope.

(** Rules for manipulating casts *)

Lemma cast_id_eq {n m} prfn prfm (zx : ZX n m) : 
  cast n m prfn prfm zx = zx.
Proof.
  rewrite (UIP_nat m _ _ eq_refl), (UIP_nat _ _ _ eq_refl).
  reflexivity.
Qed.

Lemma cast_id : forall {n m} prfn prfm (zx : ZX n m),
  cast n m prfn prfm zx ∝= zx.
Proof.
  intros.
  now rewrite cast_id_eq.
Qed.

Lemma cast_simplify_zx :
  forall {n n' m m'} prfn0 prfm0 prfn1 prfm1  (zx0 zx1 : ZX n m),
  zx0 = zx1 ->
  cast n' m' prfn0 prfm0 zx0 = cast n' m' prfn1 prfm1 zx1.
Proof.
  intros; subst.
  f_equal; apply UIP_nat.
Qed.

Lemma cast_simplify_eq :
  forall {n n' m m'} prfn0 prfm0 prfn1 prfm1  (zx0 zx1 : ZX n m),
  zx0 ∝= zx1 ->
  cast n' m' prfn0 prfm0 zx0 ∝= cast n' m' prfn1 prfm1 zx1.
Proof.
  intros.
  now subst; rewrite 2!cast_id.
Qed.

Lemma cast_simplify_by :
  forall {n n' m m'} prfn0 prfm0 prfn1 prfm1  (zx0 zx1 : ZX n m) c,
  zx0 ∝[c] zx1 ->
  cast n' m' prfn0 prfm0 zx0 ∝[c] cast n' m' prfn1 prfm1 zx1.
Proof.
  intros.
  now subst; rewrite 2!cast_id.
Qed.

Lemma cast_simplify :
  forall {n n' m m'} prfn0 prfm0 prfn1 prfm1  (zx0 zx1 : ZX n m),
  zx0 ∝ zx1 ->
  cast n' m' prfn0 prfm0 zx0 ∝ cast n' m' prfn1 prfm1 zx1.
Proof.
  intros.
  subst.
  now rewrite 2!cast_id.
Qed.

Lemma cast_simplify_zx_rev :
  forall {n n' m m'} prfn0 prfm0 prfn1 prfm1  (zx0 zx1 : ZX n m),
  cast n' m' prfn0 prfm0 zx0 = cast n' m' prfn1 prfm1 zx1 ->
  zx0 = zx1.
Proof.
  intros.
  now subst; rewrite 2!cast_id_eq in *.
Qed.

Lemma cast_simplify_eq_rev :
  forall {n n' m m'} prfn0 prfm0 prfn1 prfm1  (zx0 zx1 : ZX n m),
  cast n' m' prfn0 prfm0 zx0 ∝= cast n' m' prfn1 prfm1 zx1 ->
  zx0 ∝= zx1.
Proof.
  intros.
  now subst; rewrite 2!cast_id in *.
Qed.

Lemma cast_simplify_by_rev  :
  forall {n n' m m'} prfn0 prfm0 prfn1 prfm1  (zx0 zx1 : ZX n m) c,
  cast n' m' prfn0 prfm0 zx0 ∝[c] cast n' m' prfn1 prfm1 zx1 ->
  zx0 ∝[c] zx1.
Proof.
  intros.
  now subst; rewrite 2!cast_id_eq in *.
Qed.

Lemma cast_simplify_rev :
  forall {n n' m m'} prfn0 prfm0 prfn1 prfm1  (zx0 zx1 : ZX n m),
  cast n' m' prfn0 prfm0 zx0 ∝ cast n' m' prfn1 prfm1 zx1 ->
  zx0 ∝ zx1.
Proof.
  intros.
  now subst; rewrite 2!cast_id in *.
Qed.

(** On a goal [$ n', m' ::: zx0 $ (R) $ n', m' ::: zx1 $] where 
  [zx0] and [zx1] have the same dimensions, replace the goal 
  with [zx0 (R) zx1]. 
  Here, [(R)] is one of [=], [∝=], [∝[c]], and [∝]. *)
Ltac cast_irrelevance := 
  first [apply cast_simplify 
    | apply cast_simplify_by 
    | apply cast_simplify_eq 
    | apply cast_simplify_zx]; try easy.

(** Given a hypothesis [H : $ n', m' ::: zx0 $ (R) $ n', m' ::: zx1 $] where 
  [zx0] and [zx1] have the same dimensions, 
  replace the type of [H] with [zx0 (R) zx1]. 
  Here, [(R)] is one of [=], [∝=], [∝[c]], and [∝]. *)
Ltac cast_irrelevance_in H := 
  first [apply cast_simplify in H 
    | apply cast_simplify_by in H
    | apply cast_simplify_eq in H
    | apply cast_simplify_zx in H].

(** Run a tactic [tac], solving as many side-conditions as possible with [lia]
  and shelving any others. *)
Ltac auto_cast_eqn tac :=
  unshelve tac; try lia; shelve_unifiable.

(** Run a tactic [tac], solving as many side-conditions as possible with [lia]
  and shelving any others. *)
Tactic Notation "auto_cast_eqn" tactic3(tac) := 
  auto_cast_eqn tac.

#[export] Hint Rewrite @cast_id : cast_simpl_db.

(** Simplify casts in the goal by [autorewrite with cast_simpl_db],
  solving as many side conditions as possible with [lia], finally
  removing as many outer casts as possible with [cast_irrelevance]. 
  NB if [cast_simpl_db] is not maintained carefully, this tactic may
  leave unsolvable side-conditions. *)
Ltac simpl_casts := 
  auto_cast_eqn (autorewrite with cast_simpl_db); repeat cast_irrelevance.

(** Simplify casts in [H] by [autorewrite with cast_simpl_db],
  solving as many side conditions as possible with [lia], finally
  removing as many outer casts as possible with [cast_irrelevance_in]. 
  NB if [cast_simpl_db] is not maintained carefully, this tactic may
  leave unsolvable side-conditions. *)
Tactic Notation "simpl_casts_in" hyp(H) := 
  auto_cast_eqn (autorewrite with cast_simpl_db in H); 
  cast_irrelevance_in H.


Lemma cast_stack_l_eq {nTop nTop' mTop mTop' nBot mBot} 
  prfnTop prfmTop prfn prfm (zxTop : ZX nTop mTop) (zxBot : ZX nBot mBot) : 
  (cast nTop' mTop' prfnTop prfmTop zxTop) ↕ zxBot =
  cast (nTop' + nBot) (mTop' + mBot) prfn prfm (zxTop ↕ zxBot).
Proof.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_stack_l : forall {nTop nTop' mTop mTop' nBot mBot} prfnTop prfmTop prfn prfm
                          (zxTop : ZX nTop mTop) (zxBot : ZX nBot mBot),
  (cast nTop' mTop' prfnTop prfmTop zxTop) ↕ zxBot ∝= 
  cast (nTop' + nBot) (mTop' + mBot) prfn prfm (zxTop ↕ zxBot).
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_stack_r_eq : forall {nTop mTop nBot nBot' mBot mBot'} prfnBot prfmBot prfn prfm
                          (zxTop : ZX nTop mTop) (zxBot : ZX nBot mBot),
  zxTop ↕ (cast nBot' mBot' prfnBot prfmBot zxBot) = 
  cast (nTop + nBot') (mTop + mBot') prfn prfm (zxTop ↕ zxBot).
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_stack_r : forall {nTop mTop nBot nBot' mBot mBot'} prfnBot prfmBot prfn prfm
                          (zxTop : ZX nTop mTop) (zxBot : ZX nBot mBot),
  zxTop ↕ (cast nBot' mBot' prfnBot prfmBot zxBot) ∝=
  cast (nTop + nBot') (mTop + mBot') prfn prfm (zxTop ↕ zxBot).
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_stack_distribute_eq : 
  forall {n n' m m' o o' p p'} prfn prfm prfo prfp prfno prfmp 
    (zx0 : ZX n m) (zx1 : ZX o p),
  cast (n' + o') (m' + p') prfno prfmp (zx0 ↕ zx1) =
  cast n' m' prfn prfm zx0 ↕ cast o' p' prfo prfp zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_stack_distribute : 
  forall {n n' m m' o o' p p'} prfn prfm prfo prfp prfno prfmp 
    (zx0 : ZX n m) (zx1 : ZX o p),
  cast (n' + o') (m' + p') prfno prfmp (zx0 ↕ zx1) ∝=
  cast n' m' prfn prfm zx0 ↕ cast o' p' prfo prfp zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.


#[export] Hint Rewrite @cast_stack_l @cast_stack_r : cast_simpl_db.


Lemma cast_contract_eq : 
  forall {n0 m0 n1 m1 n2 m2} prfn01 prfm01 prfn12 prfm12 prfn prfm (zx : ZX n0 m0),
    cast n2 m2 prfn12 prfm12 
      (cast n1 m1 prfn01 prfm01
        zx) =
    cast n2 m2 prfn prfm zx.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.


Lemma cast_contract : 
  forall {n0 m0 n1 m1 n2 m2} prfn01 prfm01 prfn12 prfm12 prfn prfm (zx : ZX n0 m0),
    cast n2 m2 prfn12 prfm12 
      (cast n1 m1 prfn01 prfm01
        zx) ∝=
    cast n2 m2 prfn prfm zx.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.


#[export] Hint Rewrite @cast_contract : cast_simpl_db.

Lemma cast_symm :
  forall {n0 m0 n1 m1} prfn prfm prfn' prfm' (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
    cast n1 m1 prfn prfm zx0 ∝ zx1 <->
    zx0 ∝ cast n0 m0 prfn' prfm' zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.


Lemma cast_contract_l_eq : forall {n m n0 m0 n1 m1} prfn0 prfm0 prfn1 prfm1 prfn prfm
                                       (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  cast n m prfn0 prfm0 zx0 ∝= cast n m prfn1 prfm1 zx1 <->
  cast n1 m1 prfn prfm zx0 ∝= zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_contract_l_by : forall {n m n0 m0 n1 m1} prfn0 prfm0 prfn1 prfm1 prfn prfm
                                       (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) c,
  cast n m prfn0 prfm0 zx0 ∝[c] cast n m prfn1 prfm1 zx1 <->
  cast n1 m1 prfn prfm zx0
    ∝[c] zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_contract_l : forall {n m n0 m0 n1 m1} prfn0 prfm0 prfn1 prfm1 prfn prfm
                                       (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  cast n m prfn0 prfm0 zx0 ∝ cast n m prfn1 prfm1 zx1 <->
  cast n1 m1 prfn prfm zx0
    ∝ zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

#[export] Hint Rewrite @cast_contract_l_eq @cast_contract_l_by 
  @cast_contract_l : cast_simpl_db.


Lemma cast_contract_r : forall {n m n0 m0 n1 m1} prfn0 prfm0 prfn1 prfm1 prfn prfm
                                       (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  cast n m prfn0 prfm0 zx0 ∝ cast n m prfn1 prfm1 zx1 <->
  zx0 ∝ cast n0 m0 prfn prfm zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_compose_distribute :
  forall n n' m o o' prfn prfo (zx0 : ZX n m) (zx1 : ZX m o),
  cast n' o' prfn prfo (zx0 ⟷ zx1) =
  cast n' m prfn eq_refl zx0 ⟷ cast m o' eq_refl prfo zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_compose_l :
  forall {n n' m m' o} prfn prfm (zx0 : ZX n m) (zx1 : ZX m' o),
    cast n' m' prfn prfm zx0 ⟷ zx1 =
      cast n' o prfn eq_refl (zx0 ⟷ cast m o (eq_sym prfm) eq_refl zx1).
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_compose_r :
  forall {n m m' o o'} prfm prfo (zx0 : ZX n m') (zx1 : ZX m o),
  zx0 ⟷ cast m' o' prfm prfo zx1 = 
    cast n o' eq_refl prfo (cast n m eq_refl (eq_sym prfm) zx0 ⟷ zx1).
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_compose_mid :
  forall {n m o} m' prfm prfm' (zx0 : ZX n m) (zx1 : ZX m o),
  zx0 ⟷ zx1 = cast n m' eq_refl prfm zx0 ⟷ cast m' o prfm' eq_refl zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_compose_mid_contract :
  forall {n m o} n' m' o' prfn prfn' prfm prfm' prfo prfo' (zx0 : ZX n m) (zx1 : ZX m o),
  cast n' o' prfn prfo (zx0 ⟷ zx1) = cast n' m' prfn' prfm zx0 ⟷ cast m' o' prfm' prfo' zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_compose_partial_contract_r : forall {n m o} n' m' o' o'' prfn prfm prfo prfo' prfo'' prfo''' (zx0 : ZX n m') (zx1 : ZX m o),
  cast n' o' prfn prfo (zx0 ⟷ cast m' o' prfm prfo' zx1) = cast n' o' prfn prfo'' (zx0 ⟷ cast m' o'' prfm prfo''' zx1).
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_compose_partial_contract_l : forall {n m o} n' n'' m' o' prfn prfn' prfn'' prfn''' prfm prfo (zx0 : ZX n m) (zx1 : ZX m' o),
  cast n' o' prfn prfo (cast n' m' prfn' prfm zx0 ⟷ zx1) = cast n' o' prfn'' prfo (cast n'' m' prfn''' prfm zx0 ⟷ zx1).
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma change_cast :
  forall {n m} n' m' n'' m'' {prfn prfm prfn' prfm' prfn'' prfm''} (zx : ZX n m),
  cast n' m' prfn prfm zx =
  cast n' m' prfn' prfm' (cast n'' m'' prfn'' prfm'' zx).
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_backwards :
  forall {n0 m0 n1 m1} prfn prfm prfn' prfm' (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  cast n1 m1 prfn prfm zx0 ∝ zx1 <->
  cast n0 m0 prfn' prfm' zx1 ∝ zx0.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_backwards_eq :
  forall {n0 m0 n1 m1} prfn prfm prfn' prfm' (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  cast n1 m1 prfn prfm zx0 ∝= zx1 <->
  cast n0 m0 prfn' prfm' zx1 ∝= zx0.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_zx :
  forall {n m} n' m' prfn prfm (zx0 zx1 : ZX n m),
  cast n' m' prfn prfm zx0 = cast n' m' prfn prfm zx1 ->
  zx0 = zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq in *.
Qed.

Lemma cast_diagrams_eq :
  forall {n m} n' m' prfn prfm (zx0 zx1 : ZX n m),
  cast n' m' prfn prfm zx0 ∝= cast n' m' prfn prfm zx1 ->
  zx0 ∝= zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq in *.
Qed.

Lemma cast_diagrams_by :
  forall {n m} n' m' prfn prfm (zx0 zx1 : ZX n m) c,
  cast n' m' prfn prfm zx0 ∝[c] cast n' m' prfn prfm zx1 ->
  zx0 ∝[c] zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq in *.
Qed.

Lemma cast_diagrams :
  forall {n m} n' m' prfn prfm (zx0 zx1 : ZX n m),
  cast n' m' prfn prfm zx0 ∝ cast n' m' prfn prfm zx1 ->
  zx0 ∝ zx1.
Proof.
  intros.
  now subst; rewrite !cast_id_eq in *.
Qed.


Lemma cast_transpose : forall {n m n' m'} prfn prfm (zx : ZX n m),
  (cast n' m' prfn prfm zx) ⊤ = cast m' n' prfm prfn (zx ⊤). 
Proof.
  intros.
  now subst; rewrite !cast_id_eq in *.
Qed.

Lemma cast_conj : forall {n m n' m'} prfn prfm (zx : ZX n m),
  (cast n' m' prfn prfm zx) ⊼ = cast n' m' prfn prfm (zx ⊼). 
Proof.
  intros.
  now subst; rewrite !cast_id_eq in *.
Qed.

Lemma cast_adj : forall {n m n' m'} prfn prfm (zx : ZX n m),
  (cast n' m' prfn prfm zx) † = cast m' n' prfm prfn (zx †). 
Proof.
  intros.
  now subst; rewrite !cast_id_eq in *.
Qed.

Lemma cast_colorswap : forall {n m n' m'} prfn prfm (zx : ZX n m),
  ⊙ (cast n' m' prfn prfm zx) = cast n' m' prfn prfm (⊙ zx). 
Proof.
  intros.
  now subst; rewrite !cast_id_eq in *.
Qed.

#[export] Hint Rewrite 
  @cast_transpose 
  @cast_conj 
  @cast_adj 
  @cast_colorswap : cast_simpl_db.

Lemma cast_fn : forall {n n' m m'} prfn prfm (f : forall n m : nat, ZX n m), 
  cast n' m' prfn prfm (f n m) = f n' m'.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_fn_eq_dim : forall {n n'} prfn prfn' (f : forall n : nat, ZX n n), 
  cast n' n' prfn prfn' (f n) = f n'.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_Z :
  forall {n n' m m'} prfn prfm α,
  cast n' m' prfn prfm (Z n m α) = Z n' m' α.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_X :
  forall {n n' m m'} prfn prfm α,
  cast n' m' prfn prfm (X n m α) = X n' m' α.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

#[export] Hint Rewrite @cast_Z @cast_X: cast_simpl_db.

Lemma cast_Z_to_refl_r n m α {m' o' o} (zx : ZX m' o') Hm Ho : 
	Z n m α ⟷ cast m o Hm Ho zx = 
	Z n m' α ⟷ cast m' o eq_refl Ho zx.
Proof. now subst. Qed.

Lemma cast_X_to_refl_r n m α {m' o' o} (zx : ZX m' o') Hm Ho : 
	X n m α ⟷ cast m o Hm Ho zx = 
	X n m' α ⟷ cast m' o eq_refl Ho zx.
Proof. now subst. Qed.

Lemma cast_Z_contract_r n m α {m' o' o} (zx : ZX m' o') Hm Ho : 
	Z n m α ⟷ cast m o Hm Ho zx = 
	cast n o eq_refl Ho (Z n m' α ⟷ zx).
Proof. now subst. Qed.

Lemma cast_X_contract_r n m α {m' o' o} (zx : ZX m' o') Hm Ho : 
	X n m α ⟷ cast m o Hm Ho zx = 
	cast n o eq_refl Ho (X n m' α ⟷ zx).
Proof. now subst. Qed.

Lemma cast_n_stack1 : forall {n n'} prfn prfm (zx : ZX 1 1),
  cast n' n' prfn prfm (n ↑ zx) = n' ↑ zx.
Proof.
  intros.
  now subst; rewrite !cast_id_eq.
Qed.

Lemma cast_n_wire : forall {n n'} prfn prfm,
  cast n' n' prfn prfm (n_wire n) = n_wire n'.
Proof.
  intros.
  apply cast_n_stack1.
Qed.

Lemma cast_n_box : forall {n n'} prfn prfm,
  cast n' n' prfn prfm (n_box n) = n_box n'.
Proof.
  intros.
  apply cast_n_stack1.
Qed.


#[export] Hint Rewrite @cast_n_stack1 @cast_n_wire @cast_n_box : cast_simpl_db.


Lemma cast_compose_eq_mid_join n m o n' m' o' 
	(Hn : n' = n) (Hm Hm' : m' = m) (Ho : o' = o)
	(zx0 : ZX n m) (zx1 : ZX m o) : 
	cast n' m' Hn Hm zx0 ⟷ cast m' o' Hm' Ho zx1 =
	cast n' o' Hn Ho (zx0 ⟷ zx1).
Proof.
	subst.
	now rewrite (Peano_dec.UIP_nat _ _ Hm' eq_refl).
Qed.

Lemma cast_compose_l_eq_mid {n m o n'} (zx0 : ZX n m) (zx1 : ZX m o) 
  prfn prfm : 
  cast n' m prfn prfm zx0 ⟷ zx1 ∝=
  cast n' o prfn eq_refl (zx0 ⟷ zx1).
Proof.
  subst.
  now rewrite cast_id.
Qed.

Lemma cast_compose_r_eq_mid {n m o o'} (zx0 : ZX n m) (zx1 : ZX m o) 
  prfm prfo : 
  zx0 ⟷ cast m o' prfm prfo zx1 ∝=
  cast n o' eq_refl prfo (zx0 ⟷ zx1).
Proof.
  subst.
  now rewrite cast_id.
Qed.

Lemma cast_compose_distribute_l_eq_mid {n m o n'} (zx0 : ZX n m) (zx1 : ZX m o)
  prfn prfo : 
  cast n' o prfn prfo (zx0 ⟷ zx1) ∝=
  cast n' m prfn eq_refl zx0 ⟷ zx1.
Proof.
  subst; now rewrite cast_id.
Qed.

Lemma cast_compose_distribute_r_eq_mid {n m o o'} (zx0 : ZX n m) (zx1 : ZX m o)
  prfn prfo : 
  cast n o' prfn prfo (zx0 ⟷ zx1) ∝=
  zx0 ⟷ cast m o' eq_refl prfo zx1.
Proof.
  subst; now rewrite cast_id.
Qed.

Lemma cast_contract_eq' {n0 m0 n1 m1 n2 m2}
  (zx : ZX n0 m0) prfn01 prfm01 prfn12 prfm12 : 
  cast n2 m2 prfn12 prfm12 (cast n1 m1 prfn01 prfm01 zx) = 
  cast n2 m2 (eq_trans prfn12 prfn01) (eq_trans prfm12 prfm01) zx.
Proof.
  now subst.
Qed.

Lemma compose_simplify_casted {n m m' o} 
  (zx0 : ZX n m) (zx1 : ZX m o) (zx0' : ZX n m') (zx1' : ZX m' o) 
  (Hm : m = m') : 
  zx0 ∝= cast _ _ eq_refl Hm zx0' ->
  zx1 ∝= cast _ _ Hm eq_refl zx1' ->
  zx0 ⟷ zx1 ∝= zx0' ⟷ zx1'.
Proof.
  subst.
  now intros -> ->.
Qed.

Lemma compose_simplify_casted_abs {n m m' o : nat} 
  (zx0 : ZX n m) (zx1 : ZX m o) 
  (zx0' : ZX n m') (zx1' : ZX m' o) (Hm : m = m') : 
  (forall Hm', zx0 ∝= cast _ _ eq_refl Hm' zx0') ->
  (forall Hm', zx1 ∝= cast _ _ Hm' eq_refl zx1') ->
  zx0 ⟷ zx1 ∝= zx0' ⟷ zx1'.
Proof.
  subst.
  intros H H'.
  now rewrite (H eq_refl), (H' eq_refl).
Qed.