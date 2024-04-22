Require Import ComposeRules.
Require Import CastRules.
Require Import StackRules.
Require Import WireRules.
Require Import StackComposeRules.

Ltac wire_to_n_wire_safe_aux zx :=
  match zx with
  | ?n ↑ — => idtac (* Guards from recursively unfolding n_wire into (n ↑ (n_wire 1)) *)
  | ?n ↑ ?zx => wire_to_n_wire_safe_aux zx
  | ?zx1 ↕ ?zx2 => wire_to_n_wire_safe_aux zx1; wire_to_n_wire_safe_aux zx2
  | ?zx1 ⟷ ?zx2 => wire_to_n_wire_safe_aux zx1; wire_to_n_wire_safe_aux zx2
  | — => rewrite wire_to_n_wire
  | cast _ _ _ _ ?zx => wire_to_n_wire_safe_aux zx
  | _ => idtac
  end.

Ltac wire_to_n_wire_safe := 
match goal with 
  | [ |- ?zx1 ∝ ?zx2] => try (wire_to_n_wire_safe_aux zx1); try (wire_to_n_wire_safe_aux zx2); repeat rewrite n_stack_n_wire_1_n_wire
end.

Tactic Notation "bundle_wires" := wire_to_n_wire_safe; (* change wires to n_wires *)
                                  repeat rewrite n_wire_stack; (* stack n_wire *)
                                  repeat rewrite <- wire_to_n_wire. (* restore *)

#[export] Hint Rewrite 
  (fun n => @compose_empty_l n)
  (fun n => @compose_empty_r n)
  (fun n => @stack_empty_l n)
  (fun n => @stack_empty_r n) 
  (fun n => @nwire_removal_l n) 
  (fun n => @nwire_removal_r n)
  @wire_removal_l
  @wire_removal_r
  X_0_is_wire
  Z_0_is_wire
  box_compose
  (fun n m o p => @nwire_stack_compose_topleft n m o p)
  (fun n m o p => @nwire_stack_compose_botleft n m o p)
  : cleanup_zx_db.
Tactic Notation "cleanup_zx" := auto_cast_eqn (autorewrite with cleanup_zx_db).

#[export] Hint Rewrite
  (fun n m o p => @cast_colorswap n m o p)
  (fun n => @n_wire_colorswap n)
  (fun n => @n_stack1_colorswap n)
  (fun n m o => @n_stack_colorswap n m o)
  : colorswap_db.

#[export] Hint Rewrite
  (fun n m o p => @cast_transpose n m o p)
  (fun n => @n_wire_transpose n)
  (fun n => @n_stack1_transpose n)
  (fun n => @n_stack_transpose n)
  : transpose_db.

#[export] Hint Rewrite
  (fun n m o p => @cast_adj n m o p)
  : adjoint_db.

Ltac transpose_of H := intros; apply transpose_diagrams; repeat (simpl; autorewrite with transpose_db); apply H.
Ltac adjoint_of H := intros; apply adjoint_diagrams; repeat (simpl; autorewrite with adjoint_db); apply H.
Ltac colorswap_of H := intros; apply colorswap_diagrams; repeat (simpl; autorewrite with colorswap_db); apply H.


Lemma cast_split_l :
  forall {n n' m} prfn prfm (zx : ZX n m),
  cast n' m prfn prfm zx 
  ∝ cast n' n prfn eq_refl (n_wire n) ⟷ zx.
Proof.
  intros.
  subst.
  now rewrite 2!cast_id, nwire_removal_l.
Qed.

Lemma cast_split_r :
  forall {n m m'} prfn prfm (zx : ZX n m),
  cast n m' prfn prfm zx 
  ∝ zx ⟷ cast m m' eq_refl prfm (n_wire m).
Proof.
  intros.
  subst.
  now rewrite 2!cast_id, nwire_removal_r.
Qed.

Lemma cast_split_lr : 
  forall {n n' m m'} prfn prfm (zx : ZX n m),
  cast n' m' prfn prfm zx 
  ∝ cast n' n prfn eq_refl (n_wire n) ⟷ zx 
  ⟷ cast m m' eq_refl prfm (n_wire m).
Proof.
  intros. 
  subst.
  now rewrite 3!cast_id, nwire_removal_l, nwire_removal_r.
Qed.

(* Returns t if t is an atomic ZX, otherwise return the value of tac t *)
Ltac __pass_ZX_atomics_constr t tac :=
  lazymatch t with
  | Empty => constr:(t)
  | Cap => constr:(t)
  | Cup => constr:(t)
  | Swap => constr:(t)
  | Wire => constr:(t)
  | Box => constr:(t)
  | X_Spider _ _ _ => constr:(t)
  | Z_Spider _ _ _ => constr:(t)
  | _ => let res := tac t in constr:(res)
  end.

Ltac __pass_ZX_atomics_constr_no_nwire t tac :=
  lazymatch t with
  | Empty => constr:(t)
  | Cap => constr:(t)
  | Cup => constr:(t)
  | Swap => constr:(t)
  | Wire => constr:(t)
  | Box => constr:(t)
  | X_Spider _ _ _ => constr:(t)
  | Z_Spider _ _ _ => constr:(t)
  | n_wire _ => constr:(t)
  | _ => let res := tac t in constr:(res)
  end.

Ltac __pass_ZX_atomics_constr_walk t tac :=
  let rec proc t :=
    lazymatch t with
    | Empty => constr:(t)
    | Cap => constr:(t)
    | Cup => constr:(t)
    | Swap => constr:(t)
    | Wire => constr:(t)
    | Box => constr:(t)
    | X_Spider _ _ _ => constr:(t)
    | Z_Spider _ _ _ => constr:(t)

    | Stack ?zx0 ?zx1 =>
        let res0 := proc zx0 in
        let res1 := proc zx1 in
        constr:(Stack res0 res1)
    | Compose ?zx0 ?zx1 =>
        let res0 := proc zx0 in
        let res1 := proc zx1 in
        constr:(Compose res0 res1)
    | _ => let res := tac t in constr:(res)
    end
  in proc t.

Ltac __pass_ZX_atomics_constr_walk_no_nwire t tac :=
  let rec proc t :=
    lazymatch t with
    | Empty => constr:(t)
    | Cap => constr:(t)
    | Cup => constr:(t)
    | Swap => constr:(t)
    | Wire => constr:(t)
    | Box => constr:(t)
    | X_Spider _ _ _ => constr:(t)
    | Z_Spider _ _ _ => constr:(t)
    | n_wire _ => constr:(t)

    | Stack ?zx0 ?zx1 =>
        let res0 := proc zx0 in
        let res1 := proc zx1 in
        constr:(Stack res0 res1)
    | Compose ?zx0 ?zx1 =>
        let res0 := proc zx0 in
        let res1 := proc zx1 in
        constr:(Compose res0 res1)
    | _ => let res := tac t in constr:(res)
    end
  in proc t.

Ltac split_casts_in t :=
  let pass t tac := 
    __pass_ZX_atomics_constr_walk_no_nwire t tac in
  let rec proc t := 
    lazymatch t with
    | @cast ?n ?m ?n ?m ?prfn ?prfm ?zx =>
        let res := pass zx proc in
        constr:(res)
    | @cast ?n ?m ?n' ?m ?prfn ?prfm ?zx =>
        let res := pass zx proc in 
        constr:(Compose 
                  (cast n n' prfn eq_refl (n_wire n'))
                  res)
    | @cast ?n ?m ?n ?m' ?prfn ?prfm ?zx =>
        let res := pass zx proc in 
        constr:(Compose 
                  res
                  (cast m' m eq_refl prfm (n_wire m')))
    | @cast ?n ?m ?n' ?m' ?prfn ?prfm ?zx =>
        let res := pass zx proc in 
        constr:(Compose 
                (Compose 
                  (cast n n' prfn eq_refl (n_wire n'))
                  res)
                (cast m' m eq_refl prfm (n_wire m')))
    | _ => constr:(t)
    end
  in __pass_ZX_atomics_constr_walk_no_nwire t proc.

Fixpoint zx_app {n m o : nat} (zx0 : ZX n m) : forall (zx1 : ZX m o), ZX n o :=
  match zx0 with
  | zx00 ⟷ zx01 => fun zx1 => zx00 ⟷ zx_app zx01 zx1
  | a => fun zx1 => a ⟷ zx1
  end.

Fixpoint distr_id_compose_chain_bot {n m : nat} (nBot : nat)
  (zxTop : ZX n m) : ZX (n + nBot) (m + nBot) :=
  match zxTop with
  | zx0 ⟷ zx1 => zx0 ↕ n_wire nBot ⟷ (distr_id_compose_chain_bot nBot zx1)
  | zxTop => zxTop ↕ n_wire nBot
  end.

Fixpoint distr_id_compose_chain_top {n m : nat} (nTop : nat)
  (zxBot : ZX n m) : ZX (nTop + n) (nTop + m) :=
  match zxBot with
  | zx0 ⟷ zx1 => n_wire nTop ↕ zx0 ⟷ (distr_id_compose_chain_top nTop zx1)
  | zxTop => n_wire nTop ↕ zxTop
  end.

(* Takes (zx ⟷ (zx' ⟷ ⋯)) and (zy ⟷ (zy' ⟷ ⋯)) to 
  (zx ↕ n_wire _ ⟷ (zx' ↕ n_wire _ ⟷ (⋯ ⟷ (n_wire _ ↕ zy ⟷ (n_wire _ ↕ zy' ⟷ ⋯)*)
Definition unfold_stack_compose {n0 m0 n1 m1 : nat} 
  (zxTop : ZX n0 m0) (zxBot : ZX n1 m1) : ZX (n0 + n1) (m0 + m1) :=
  zx_app (distr_id_compose_chain_bot n1 zxTop)
    (distr_id_compose_chain_top m0 zxBot).

Fixpoint zx_rassoc {n m : nat} (zx : ZX n m) : ZX n m :=
  match zx with
  | zx0 ⟷ zx1 => zx_app (zx_rassoc zx0) (zx_rassoc zx1)
  | a => a
  end.

Fixpoint foliate {n m : nat} (zx : ZX n m) : ZX n m := 
  match zx with
  | Empty => Empty
  | Cap => Cap
  | Cup => Cup
  | Swap => Swap
  | Wire => Wire
  | Box => Box
  | X_Spider n m α => X_Spider n m α
  | Z_Spider n m α => Z_Spider n m α
  | Stack zx0 zx1 => 
      unfold_stack_compose (foliate zx0) (foliate zx1)
  | Compose zx0 zx1 => 
      zx_app (foliate zx0) (foliate zx1)
  end.


Lemma zx_app_assoc {n m o p : nat} (zx0 : ZX n m) (zx1 : ZX m o) (zx2 : ZX o p) :
  zx_app (zx_app zx0 zx1) zx2 = zx_app zx0 (zx_app zx1 zx2).
Proof.
  (* revert zx1 zx2. *)
  induction zx0; try easy.
  simpl.
  f_equal.
  easy.
Qed.

Lemma foliate_zx_app {n m o : nat} (zx0 : ZX n m) (zx1 : ZX m o) : 
  foliate (zx_app zx0 zx1) = zx_app (foliate zx0) (foliate zx1).
Proof.
  induction zx0; try easy.
  simpl.
  rewrite zx_app_assoc.
  f_equal; easy.
Qed.

Lemma foliate_assoc {n m : nat} (zx : ZX n m) : 
  foliate zx = foliate (zx_rassoc zx).
Proof.
  induction zx; try easy.
  simpl.
  rewrite foliate_zx_app.
  f_equal; easy.
Qed.

Lemma distr_id_compose_chain_bot_propto {n m : nat} (nBot : nat) (zx : ZX n m) : 
  distr_id_compose_chain_bot nBot zx ∝ zx ↕ n_wire nBot.
Proof.
  induction zx; try easy.
  simpl.
  rewrite IHzx2, <- stack_compose_distr, nwire_removal_l.
  easy.
Qed.

Lemma distr_id_compose_chain_top_propto {n m : nat} (nTop : nat) (zx : ZX n m) : 
  distr_id_compose_chain_top nTop zx ∝ n_wire nTop ↕ zx.
Proof.
  induction zx; try easy.
  simpl.
  rewrite IHzx2, <- stack_compose_distr, nwire_removal_l.
  easy.
Qed.

Lemma zx_app_propto {n m o : nat} (zx0 : ZX n m) (zx1 : ZX m o) : 
  zx_app zx0 zx1 ∝ zx0 ⟷ zx1.
Proof.
  induction zx0; try easy.
  simpl.
  rewrite compose_assoc, IHzx0_2.
  easy.
Qed.


Lemma unfold_stack_compose_propto {n0 m0 n1 m1 : nat} 
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) : 
  unfold_stack_compose zx0 zx1 ∝ zx0 ↕ zx1.
Proof.
  unfold unfold_stack_compose.
  rewrite zx_app_propto, distr_id_compose_chain_bot_propto,
    distr_id_compose_chain_top_propto.
  rewrite nwire_stack_compose_botleft.
  easy.
Qed.

Lemma foliate_propto {n m : nat} (zx : ZX n m) :
  foliate zx ∝ zx.
Proof.
  induction zx; try easy; simpl.
  - now rewrite unfold_stack_compose_propto, IHzx1, IHzx2.
  - now rewrite zx_app_propto, IHzx1, IHzx2.
Qed.


Section Testing.

Local Ltac apply_to_LHS tac :=
  lazymatch goal with |- (?LHS ∝ ?RHS)%ZX => tac LHS end.

Local Ltac apply_to_RHS tac := 
  lazymatch goal with |- (?LHS ∝ ?RHS)%ZX => tac RHS end.

Local Ltac apply_to_LRHS tac := 
  lazymatch goal with |- (?LHS ∝ ?RHS)%ZX => 
  (try tac LHS); (try tac RHS) end.

Local Tactic Notation "LHS" tactic(tac) := apply_to_LHS tac.
Local Tactic Notation "RHS" tactic(tac) := apply_to_RHS tac.
Local Tactic Notation "LRHS" tactic(tac) := apply_to_LRHS tac.

Section test_split_casts_in.

Local Lemma test_cast_stack_l : forall {nTop nTop' mTop mTop' nBot mBot} 
  prfnTop prfmTop prfn prfm
  (zxTop : ZX nTop mTop) (zxBot : ZX nBot mBot),
  (cast nTop' mTop' prfnTop prfmTop zxTop) ↕ zxBot ∝ 
  cast (nTop' + nBot) (mTop' + mBot) prfn prfm (zxTop ↕ zxBot).
Proof.
  intros.
  match goal with
  |- ?LHSt ↕ _ ∝ ?RHS => 
    let res := split_casts_in LHSt in idtac (* res *)
  end.
  match goal with
  |- ?LHS ∝ ?RHS => 
    let res := split_casts_in LHS in idtac (* res *)
  end.
  Abort.

End test_split_casts_in.

End Testing.


