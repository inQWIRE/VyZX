Require Import CoreData.CoreData.

Require Import SpiderInduction.

Open Scope ZX_scope.

Lemma cast_id :
forall {n m} prfn prfm (zx : ZX n m),
  cast n m prfn prfm zx ∝ zx.
Proof.
  intros; subst.
  prop_exists_nonzero 1.
  rewrite cast_semantics.
  simpl; lma.
Qed.

#[export] Hint Rewrite @cast_id : cast_simpl_db.
Ltac simpl_casts := (autorewrite with cast_simpl_db). 


Lemma cast_stack_l : forall {nTop nTop' mTop mTop' nBot mBot} prfnTop prfmTop 
                          (zxTop : ZX nTop mTop) (zxBot : ZX nBot mBot),
  (cast nTop' mTop' prfnTop prfmTop zxTop) ↕ zxBot ∝ 
  cast (nTop' + nBot) (mTop' + mBot)  
       (f_equal2_plus _ _ _ _ (prfnTop) eq_refl)
       (f_equal2_plus _ _ _ _ (prfmTop) eq_refl)
       (zxTop ↕ zxBot).
Proof.
  intros.
  subst.
  simpl_casts.
  reflexivity.
Qed.

Lemma cast_stack_r : forall {nTop mTop nBot nBot' mBot mBot'} prfnBot prfmBot 
                          (zxTop : ZX nTop mTop) (zxBot : ZX nBot mBot),
  zxTop ↕ (cast nBot' mBot' prfnBot prfmBot zxBot) ∝ 
  cast (nTop + nBot') (mTop + mBot')  
       (f_equal2_plus _ _ _ _ eq_refl prfnBot)
       (f_equal2_plus _ _ _ _ eq_refl prfmBot)
       (zxTop ↕ zxBot).
Proof.
  intros.
  subst.
  simpl_casts.
  reflexivity.
Qed.

Lemma cast_stack_distribute : 
  forall {n n' m m' o o' p p'} prfn prfm prfo prfp prfno prfmp 
    (zx0 : ZX n m) (zx1 : ZX o p),
  cast (n' + o') (m' + p') prfno prfmp (zx0 ↕ zx1) ∝
  cast n' m' prfn prfm zx0 ↕ cast o' p' prfo prfp zx1.
Proof.
  intros.
  subst.
  simpl_casts.
  easy.
Qed.


#[export] Hint Rewrite @cast_stack_l @cast_stack_r : cast_simpl_db.


Lemma cast_contract : 
  forall {n0 m0 n1 m1 n2 m2} prfn01 prfm01 prfn12 prfm12 (zx : ZX n0 m0),
    cast n2 m2 prfn12 prfm12 
      (cast n1 m1 prfn01 prfm01
        zx) ∝
    cast n2 m2 (eq_trans prfn12 prfn01) (eq_trans prfm12 prfm01) 
      zx.
Proof.
  intros; subst.
  prop_exists_nonzero 1.
  simpl; lma.
Qed.


#[export] Hint Rewrite @cast_contract : cast_simpl_db.

Lemma cast_symm :
  forall {n0 m0 n1 m1} prfn prfm prfn' prfm' (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
    cast n1 m1 prfn prfm zx0 ∝ zx1 <->
    zx0 ∝ cast n0 m0 prfn' prfm' zx1.
Proof.
  intros.
  split; intros.
  - subst.
    simpl_casts.
    rewrite cast_id in H.
    easy.
  - subst.
    simpl_casts.
    rewrite cast_id in H.
    easy.
Qed.


Lemma cast_contract_l : forall {n m n0 m0 n1 m1} prfn0 prfm0 prfn1 prfm1 
                                       (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  cast n m prfn0 prfm0 zx0 ∝ cast n m prfn1 prfm1 zx1 <->
  cast n1 m1 (eq_trans (eq_sym prfn1) prfn0) (eq_trans (eq_sym prfm1) prfm0) zx0
    ∝ zx1.
Proof.
  intros; split; intros.
  - rewrite <- cast_symm in H.
    rewrite cast_contract in H.
    exact H.
  - rewrite <- cast_symm.
    simpl_casts.
    exact H.
Qed.

#[export] Hint Rewrite @cast_contract_l : cast_simpl_db.


Lemma cast_contract_r : forall {n m n0 m0 n1 m1} prfn0 prfm0 prfn1 prfm1 
                                       (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  cast n m prfn0 prfm0 zx0 ∝ cast n m prfn1 prfm1 zx1 <->
  zx0 ∝ cast n0 m0 (eq_trans (eq_sym prfn0) prfn1) 
                   (eq_trans (eq_sym prfm0) prfm1) zx1.
Proof.
  intros; split; intros.
  - rewrite cast_symm in H.
    rewrite cast_contract in H.
    exact H.
  - simpl_casts.
    rewrite cast_symm.
    exact H.
Qed.

(* Reverse lemmas so you don't need complex proof structure within the stacks *)

Lemma add_same_l : forall (n n' m : nat) (prfn : (n + m = n' + m)%nat), 
  (n = n')%nat.
Proof. intros. lia. Qed.

Lemma cast_stack_top : forall {n0 n0' n1 m0 m0' m1} prfn prfm 
                            (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  cast (n0' + n1) (m0' + m1) prfn prfm (zx0 ↕ zx1) ∝ 
  ((cast n0' m0' (add_same_l n0' n0 n1 prfn) (add_same_l m0' m0 m1 prfm)) zx0 
    ↕ zx1).
Proof.
  intros.
  simpl_casts.
  easy.
Qed.

Lemma add_same_r : forall (n m m' : nat) (prfn : (n + m = n + m')%nat), 
  (m = m')%nat.
Proof. intros. lia. Qed.

Lemma cast_stack_bot : forall {n0 n1 n1' m0 m1 m1'} prfn prfm 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  cast (n0 + n1') (m0 + m1') prfn prfm (zx0 ↕ zx1) ∝ 
  (zx0 ↕ 
    (cast n1' m1' (add_same_r n0 n1' n1 prfn) (add_same_r m0 m1' m1 prfm)) zx1).
Proof.
  intros.
  simpl_casts.
  easy.
Qed.

Lemma cast_compose_distribute :
  forall n n' m o o' prfn prfo (zx0 : ZX n m) (zx1 : ZX m o),
  cast n' o' prfn prfo (zx0 ⟷ zx1) ∝
  cast n' m prfn eq_refl zx0 ⟷ cast m o' eq_refl prfo zx1.
Proof.
  intros.
  subst.
  simpl_casts.
  reflexivity.
Qed.

Lemma cast_compose_l :
  forall {n n' m m' o} prfn prfm (zx0 : ZX n m) (zx1 : ZX m' o),
    cast n' m' prfn prfm zx0 ⟷ zx1 ∝ 
      cast n' o prfn eq_refl (zx0 ⟷ cast m o (eq_sym prfm) eq_refl zx1).
Proof.
  intros.
  subst.
  simpl_casts.
  reflexivity.
Qed.

Lemma cast_compose_r :
  forall {n m m' o o'} prfm prfo (zx0 : ZX n m') (zx1 : ZX m o),
  zx0 ⟷ cast m' o' prfm prfo zx1 ∝ 
    cast n o' eq_refl prfo (cast n m eq_refl (eq_sym prfm) zx0 ⟷ zx1).
Proof.
  intros. subst. simpl_casts. reflexivity.
Qed.

Lemma cast_compose_mid :
  forall {n m o} m' prfm (zx0 : ZX n m) (zx1 : ZX m o),
  zx0 ⟷ zx1 ∝ cast n m' eq_refl prfm zx0 ⟷ cast m' o prfm eq_refl zx1.
Proof.
  intros.
  subst.
  simpl_casts.
  reflexivity.
Qed.

Lemma cast_simplify :
  forall {n n' m m'} prfn0 prfm0 prfn1 prfm1  (zx0 zx1 : ZX n m),
  zx0 ∝ zx1 ->
  cast n' m' prfn0 prfm0 zx0 ∝ cast n' m' prfn1 prfm1 zx1.
Proof.
  intros.
  simpl_casts.
  easy.
Qed.

Lemma cast_backwards :
  forall {n0 m0 n1 m1} prfn prfm prfn' prfm' (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  cast n1 m1 prfn prfm zx0 ∝ zx1 <->
  cast n0 m0 prfn' prfm' zx1 ∝ zx0.
Proof.
  intros.
  split; symmetry; subst;
  simpl_casts; [rewrite H | rewrite <- H]; 
  simpl_casts; easy.
Qed.

Lemma cast_diagrams :
  forall {n m} n' m' prfn prfm (zx0 zx1 : ZX n m),
  cast n' m' prfn prfm zx0 ∝ cast n' m' prfn prfm zx1 ->
  zx0 ∝ zx1.
Proof.
  intros.
  subst.
  repeat rewrite cast_id in H.
  easy.
Qed.


Lemma cast_transpose : forall {n m n' m'} prfn prfm (zx : ZX n m),
  (cast n' m' prfn prfm zx) ⊤ ∝ cast m' n' prfm prfn (zx ⊤). 
Proof.
  intros.
  destruct prfn, prfm.
  simpl_casts.
  easy.
Qed.

Lemma cast_conj : forall {n m n' m'} prfn prfm (zx : ZX n m),
  (cast n' m' prfn prfm zx) ⊼ ∝ cast n' m' prfn prfm (zx ⊼). 
Proof.
  intros.
  destruct prfn, prfm.
  simpl_casts.
  easy.
Qed.

Lemma cast_adj : forall {n m n' m'} prfn prfm (zx : ZX n m),
  (cast n' m' prfn prfm zx) † ∝ cast m' n' prfm prfn (zx †). 
Proof.
  intros.
  subst.
  simpl.
  easy.
Qed.

Lemma cast_colorswap : forall {n m n' m'} prfn prfm (zx : ZX n m),
  ⊙ (cast n' m' prfn prfm zx) ∝ cast n' m' prfn prfm (⊙ zx). 
Proof.
  intros.
  destruct prfn, prfm.
  simpl_casts.
  easy.
Qed.

#[export] Hint Rewrite 
  @cast_transpose 
  @cast_conj 
  @cast_adj 
  @cast_colorswap : cast_simpl_db.

Lemma cast_fn : forall {n n' m m'} prfn prfm (f : forall n m : nat, ZX n m), cast n' m' prfn prfm (f n m) ∝ f n' m'.
Proof. 
  intros.
  destruct prfn, prfm.
  simpl_casts.
  easy.
Qed.

Lemma cast_fn_eq_dim : forall {n n'} prfn (f : forall n : nat, ZX n n), cast n' n' prfn prfn (f n) ∝ f n'.
Proof. 
  intros.
  destruct prfn.
  simpl_casts.
  easy.
Qed.

Lemma cast_Z :
  forall {n n' m m'} prfn prfm α,
  cast n' m' prfn prfm (𝒵 n m α) ∝ 𝒵 n' m' α.
Proof.
  intros.
  rewrite (cast_fn prfn prfm (fun n m => 𝒵 n m α)).
  easy.
Qed.

Lemma cast_X :
  forall {n n' m m'} prfn prfm α,
  cast n' m' prfn prfm (𝒳 n m α) ∝ 𝒳 n' m' α.
Proof.
  intros.
  rewrite (cast_fn prfn prfm (fun n m => 𝒳 n m α)).
  easy.
Qed.

#[export] Hint Rewrite @cast_Z @cast_X: cast_simpl_db.

Lemma cast_n_stack1 : forall {n n'} prfn (zx : ZX 1 1),
  cast n' n' prfn prfn (n ↑ zx) ∝ n' ↑ zx.
Proof.
  intros.
  rewrite (cast_fn_eq_dim prfn (fun n => n_stack1 n zx)).
  easy.
Qed.

Lemma cast_n_wire : forall {n n'} prfn,
  cast n' n' prfn prfn (n_wire n) ∝ n_wire n'.
Proof.
  intros.
  apply cast_n_stack1.
Qed.

Lemma cast_n_box : forall {n n'} prfn,
  cast n' n' prfn prfn (n_wire n) ∝ n_wire n'.
Proof.
  intros.
  apply cast_n_stack1.
Qed.


#[export] Hint Rewrite @cast_n_stack1 @cast_n_wire @cast_n_box : cast_simpl_db.