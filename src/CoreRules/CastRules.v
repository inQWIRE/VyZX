Require Import CoreData.CoreData.

Require Import SpiderInduction.

Open Scope ZX_scope.

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

Ltac cast_irrelevance := 
  first [apply cast_simplify 
    | apply cast_simplify_by 
    | apply cast_simplify_eq 
    | apply cast_simplify_zx]; try easy.

Ltac cast_irrelevance_in H := 
  first [apply cast_simplify in H 
    | apply cast_simplify_by in H
    | apply cast_simplify_eq in H
    | apply cast_simplify_zx in H].

Ltac auto_cast_eqn tac :=
  unshelve tac; try lia; shelve_unifiable.

Tactic Notation "auto_cast_eqn" tactic3(tac) := 
  auto_cast_eqn tac.

#[export] Hint Rewrite @cast_id : cast_simpl_db.
Ltac simpl_casts := 
  auto_cast_eqn (autorewrite with cast_simpl_db); repeat cast_irrelevance.
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