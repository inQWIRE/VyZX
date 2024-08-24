(** The definition of a certain (pseudo) normal form for bipermutations.
  This form allows us to define composition and prove its semantics, 
  and gives a more efficient way*)

Require Import CoreRules.
Import CoreData CoreAutomation.
Import CastRules.
From QuantumLib Require Import Bits.
Require Export QuantumLib.Permutations.
Import QuantumLib.VectorStates Modulus Kronecker.
Require Export Bipermutations.
Require Export BipermutationMatrices.

Open Scope prg.
Open Scope nat_scope.


(* Section NFBiperm.v *)

Definition realize_biperm_data (lperm rperm : nat -> nat) 
  (nid ncup ncap : nat) :=
  biperm_compose_perm_l (ncap + ncap + nid) (ncup + ncup + nid)
    (biperm_compose_perm_r (ncap + ncap + nid) (ncup + ncup + nid)
    (stack_biperms  nid nid (ncap + ncap) (ncup + ncup)
      (idn_biperm nid) (n_m_cup_cap ncup ncap))
    (reflect_perm (ncup + ncup + nid) ∘ 
      perm_inv (ncup + ncup + nid) lperm ∘
      reflect_perm (ncup + ncup + nid))%prg)
    (reflect_perm (ncap + ncap + nid) ∘ 
      rperm ∘
      reflect_perm (ncap + ncap + nid))%prg.

Lemma realize_biperm_data_bipermutation {lperm rperm} {nid ncup ncap} 
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  bipermutation ((ncup + ncup + nid) + (ncap + ncap + nid))
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  unfold realize_biperm_data.
  rewrite Nat.add_comm.
  apply biperm_compose_perm_l_biperm; [|auto with perm_db].
  apply biperm_compose_perm_r_biperm; [|auto with perm_db].
  eapply bipermutation_change_dims;
  [|auto with biperm_db].
  lia.
Qed.

Lemma realize_biperm_data_WF lperm rperm nid ncup ncap :
  WF_Perm (ncup + ncup + nid + (ncap + ncap + nid))
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  unfold realize_biperm_data.
  rewrite Nat.add_comm.
  apply biperm_compose_perm_l_WF.
Qed.

#[export] Hint Resolve realize_biperm_data_WF : WF_Perm_db.

(* FIX ME: Is there any good way to write the realization explicitly?
Definition realize_biperm_data_alt lperm rperm nid ncup ncap :=
  fun k => 
  if k <? ncup + ncup + nid then 
    if rperm (cnup + cnupk <? ncup + ncup then 
     *)


Lemma matrix_of_realize_biperm_data {lperm rperm} {nid ncup ncap} 
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid)
    (realize_biperm_data lperm rperm nid ncup ncap) =
  perm_to_matrix (ncap + ncap + nid) rperm × 
  (matrix_of_biperm (ncup + ncup) (ncap + ncap) (n_m_cup_cap ncup ncap)
    ⊗ I (2^nid)) ×
    perm_to_matrix (ncup + ncup + nid) lperm.
Proof.
  apply mat_equiv_eq; auto with wf_db.
  unfold realize_biperm_data.
  rewrite matrix_of_biperm_compose_perm_r by auto with biperm_db.
  rewrite matrix_of_biperm_compose_perm_l by auto with biperm_db.
  rewrite 2!(Nat.add_comm _ nid) in *.
  rewrite matrix_of_stack_biperms by auto with biperm_db.
  rewrite matrix_of_idn_biperm.
  rewrite <- Mmult_assoc.
  repeat apply mmult_mat_equiv_morph; try easy.
  - apply perm_to_matrix_perm_eq.
    intros k Hk.
    unfold Basics.compose.
    now rewrite 2!reflect_perm_invol.
  - apply perm_to_matrix_perm_eq.
    intros k Hk.
    unfold Basics.compose.
    rewrite 2!perm_inv_compose_alt by auto with perm_db perm_bounded_db.
    rewrite !reflect_perm_inv by auto with perm_bounded_db.
    rewrite 2!reflect_perm_invol.
    now apply perm_inv_perm_inv.
Qed.

Lemma matrix_of_realize_biperm_data' {lperm rperm : nat -> nat} 
  {nid ncup ncap : nat} insize outsize : 
  insize = ncup + ncup + nid ->
  outsize = ncap + ncap + nid ->
  permutation insize lperm ->
  permutation outsize rperm ->
  matrix_of_biperm insize outsize
    (realize_biperm_data lperm rperm nid ncup ncap) =
  perm_to_matrix (ncap + ncap + nid) rperm
  × (matrix_of_biperm (ncup + ncup) (ncap + ncap) (n_m_cup_cap ncup ncap)
    ⊗ I (2 ^ nid)) × perm_to_matrix (ncup + ncup + nid) lperm.
Proof.
  intros -> ->.
  apply matrix_of_realize_biperm_data.
Qed.

Record NF_biperm := {
  lperm' : nat -> nat;
  rperm' : nat -> nat;
  nid' : nat;
  ncup' : nat;
  ncap' : nat
}.

Local Notation NF_insize b := (ncup' b + ncup' b + nid' b).
Local Notation NF_outsize b := (ncap' b + ncap' b + nid' b).

Definition uncurry_NF_biperm 
  {A : (nat -> nat) -> (nat -> nat) -> nat -> nat -> nat -> Type} 
  (f : forall lperm rperm nid ncup ncap, A lperm rperm nid ncup ncap) :
  forall bp : NF_biperm, 
  A bp.(lperm') bp.(rperm') bp.(nid') bp.(ncup') bp.(ncap') :=
  fun bp => 
  f bp.(lperm') bp.(rperm') bp.(nid') bp.(ncup') bp.(ncap').

Definition curry_NF_biperm {A : NF_biperm -> Type} 
  (f : forall bp : NF_biperm, A bp) :
  forall lperm rperm nid ncup ncap, 
    A (Build_NF_biperm lperm rperm nid ncup ncap) :=
  fun lperm rperm nid ncup ncap => 
  f (Build_NF_biperm lperm rperm nid ncup ncap).

Lemma curry_uncurry_NF_biperm {A} f : 
  forall lperm rperm nid ncup ncap, 
  curry_NF_biperm (@uncurry_NF_biperm A f) 
    lperm rperm nid ncup ncap = f lperm rperm nid ncup ncap.
Proof.
  reflexivity.
Qed.

Lemma uncurry_curry_NF_biperm {A} f : 
  forall bp,
  uncurry_NF_biperm (@curry_NF_biperm (fun _ => A) f) bp = 
    f bp.
Proof.
  intros [];
  reflexivity.
Qed.

Lemma curry_uncurry_NF_biperm_eq {A} f :  
  curry_NF_biperm (@uncurry_NF_biperm A f) = f.
Proof.
  do 5 (apply functional_extensionality_dep; intros).
  apply curry_uncurry_NF_biperm.
Qed.

Lemma uncurry_curry_NF_biperm_eq {A} f :  
  uncurry_NF_biperm (@curry_NF_biperm (fun _ => A) f) = f.
Proof.
  apply functional_extensionality_dep; intros;
  apply uncurry_curry_NF_biperm.
Qed.

Definition WF_NF_biperm (b : NF_biperm) :=
  permutation (b.(ncup') + b.(ncup') + b.(nid')) b.(lperm') /\
  permutation (b.(ncap') + b.(ncap') + b.(nid')) b.(rperm').


(* TODO : Do we need (all of?) these? *)
Local Arguments Nat.sub : simpl never.
Local Arguments Nat.div : simpl never.
Local Arguments Nat.divmod : simpl never.
Local Arguments Nat.modulo : simpl never.
Local Arguments perm_inv : simpl never.



Definition realize_NF_biperm : NF_biperm -> nat -> nat :=
  uncurry_NF_biperm realize_biperm_data.

Lemma realize_NF_biperm_constructor lperm rperm nid ncup ncap : 
  realize_NF_biperm {|lperm':=lperm; rperm':=rperm; 
    nid':=nid; ncup':=ncup; ncap':=ncap|} = 
  realize_biperm_data lperm rperm nid ncup ncap.
Proof. easy. Qed.

Lemma realize_NF_biperm_bipermutation (b : NF_biperm) (Hb : WF_NF_biperm b) :
  bipermutation (NF_outsize b + NF_insize b) 
    (realize_NF_biperm b).
Proof.
  destruct b, Hb; cbn in *.
  rewrite realize_NF_biperm_constructor.
  rewrite Nat.add_comm.
  now apply realize_biperm_data_bipermutation.
Qed.

Lemma realize_NF_biperm_bipermutation_alt (b : NF_biperm) (Hb : WF_NF_biperm b) :
  bipermutation (NF_insize b + NF_outsize b) 
    (realize_NF_biperm b).
Proof.
  rewrite Nat.add_comm.
  now apply realize_NF_biperm_bipermutation.
Qed.

#[export] Hint Resolve realize_NF_biperm_bipermutation : biperm_db.
#[export] Hint Resolve realize_NF_biperm_bipermutation_alt : biperm_db.

Definition matrix_of_NF_biperm (b : NF_biperm) := 
  matrix_of_biperm (ncup' b + ncup' b + nid' b) 
    (ncap' b + ncap' b + nid' b) (realize_NF_biperm b).

Lemma matrix_of_NF_biperm_WF b : 
  WF_Matrix (matrix_of_NF_biperm b).
Proof.
  apply matrix_of_biperm_WF.
Qed.

#[export] Hint Resolve matrix_of_NF_biperm_WF : wf_db.

Lemma matrix_of_realize_NF_biperm' insize outsize (b : NF_biperm) : 
  insize = ncup' b + ncup' b + nid' b ->
  outsize = ncap' b + ncap' b + nid' b ->
  WF_NF_biperm b ->
  matrix_of_biperm insize outsize
    (realize_NF_biperm b) =
  perm_to_matrix (ncap' b + ncap' b + nid' b) (rperm' b)
  × (matrix_of_biperm (ncup' b + ncup' b) (ncap' b + ncap' b) 
    (n_m_cup_cap (ncup' b) (ncap' b))
    ⊗ I (2 ^ nid' b)) × perm_to_matrix (ncup' b + ncup' b + nid' b) (lperm' b).
Proof.
  intros -> ->.
  intros [].
  now apply matrix_of_realize_biperm_data.
Qed.

Lemma matrix_of_WF_NF_biperm (b : NF_biperm) (Hb : WF_NF_biperm b) : 
  matrix_of_NF_biperm b = 
  perm_to_matrix (NF_outsize b) (rperm' b) ×
  (matrix_of_biperm (ncup' b + ncup' b) (ncap' b + ncap' b)
   (n_m_cup_cap (ncup' b) (ncap' b)) ⊗ I (2 ^ (nid' b))) ×
  perm_to_matrix (NF_insize b) (lperm' b).
Proof.
  now rewrite <- matrix_of_realize_NF_biperm'.
Qed.


(*  The definition of b being a representative of f, a 
    bipermutation with n inputs and m outputs. *)
Definition is_NF_representative (n m : nat) 
  (b : NF_biperm) (f : nat -> nat) : Prop :=
  WF_NF_biperm b /\ NF_insize b = n /\ NF_outsize b = m /\ 
  perm_eq (m + n) (realize_NF_biperm b) f.

(* TODO: Check if this is used in the development; remove if not
  (don't want to clutter instances) *)
Add Parametric Morphism n m b : (is_NF_representative n m b) with signature
  perm_eq (m + n) ==> iff as is_NF_representative_perm_eq.
Proof.
  intros f g Hfg.
  unfold is_NF_representative.
  now rewrite Hfg.
Qed.



Definition empty_NF_biperm : NF_biperm :=
  {|
    lperm' := idn; rperm' := idn;
    ncup' := 0; ncap' := 0; nid' := 0
  |}.

Lemma empty_NF_biperm_WF : WF_NF_biperm empty_NF_biperm.
Proof.
  split; cbn; 
  auto with perm_db.
Qed.

Lemma empty_is_NF_rep_0_0 f : 
  is_NF_representative 0 0 empty_NF_biperm f.
Proof.
  repeat split; cbn; auto with perm_db.
  intros k Hk; easy.
Qed.

Definition add_cup_to_NF (b : NF_biperm) : NF_biperm :=
  {|
    lperm' := stack_perms 2 (NF_insize b) idn (lperm' b);
    rperm' := rperm' b;
    ncup' := 1 + ncup' b;
    ncap' := ncap' b;
    nid' := nid' b;
  |}.

Definition add_cap_to_NF (b : NF_biperm) : NF_biperm :=
  {|
    lperm' := lperm' b;
    rperm' := stack_perms 2 (NF_outsize b) idn (rperm' b);
    ncup' := ncup' b;
    ncap' := 1 + ncap' b;
    nid' := nid' b;
  |}.

Definition add_id_to_NF (b : NF_biperm) : NF_biperm :=
  {|
    lperm' := stack_perms (NF_insize b) 1 (lperm' b) idn;
    rperm' := stack_perms (NF_outsize b) 1 (rperm' b) idn;
    ncup' := ncup' b;
    ncap' := ncap' b;
    nid' := nid' b + 1;
  |}.

Lemma NF_insize_add_cup_to_NF b : 
  NF_insize (add_cup_to_NF b) = 2 + NF_insize b.
Proof. cbn; lia. Qed.

Lemma NF_outsize_add_cup_to_NF b : 
  NF_outsize (add_cup_to_NF b) = NF_outsize b.
Proof. easy. Qed.

Lemma NF_insize_add_cap_to_NF b : 
  NF_insize (add_cap_to_NF b) = NF_insize b.
Proof. easy. Qed.

Lemma NF_outsize_add_cap_to_NF b : 
  NF_outsize (add_cap_to_NF b) = 2 + NF_outsize b.
Proof. cbn; lia. Qed.

Lemma NF_insize_add_id_to_NF b : 
  NF_insize (add_id_to_NF b) = NF_insize b + 1.
Proof. cbn; lia. Qed.

Lemma NF_outsize_add_id_to_NF b : 
  NF_outsize (add_id_to_NF b) = NF_outsize b + 1.
Proof. cbn; lia. Qed.

Lemma add_cup_to_NF_WF b (Hb : WF_NF_biperm b) : 
  WF_NF_biperm (add_cup_to_NF b).
Proof.
  unfold WF_NF_biperm in *.
  destruct Hb.
  rewrite NF_insize_add_cup_to_NF, NF_outsize_add_cup_to_NF.
  cbn.
  auto with perm_db.
Qed.

Lemma add_cap_to_NF_WF b (Hb : WF_NF_biperm b) : 
  WF_NF_biperm (add_cap_to_NF b).
Proof.
  unfold WF_NF_biperm in *.
  destruct Hb.
  rewrite NF_insize_add_cap_to_NF, NF_outsize_add_cap_to_NF.
  cbn.
  auto with perm_db.
Qed.

Lemma add_id_to_NF_WF b (Hb : WF_NF_biperm b) : 
  WF_NF_biperm (add_id_to_NF b).
Proof.
  unfold WF_NF_biperm in *.
  destruct Hb.
  rewrite NF_insize_add_id_to_NF, NF_outsize_add_id_to_NF.
  cbn.
  auto with perm_db.
Qed.

Lemma realize_add_cap_to_NF (b : NF_biperm) (Hb : WF_NF_biperm b) :
  perm_eq ((2 + NF_outsize b) + NF_insize b) 
    (realize_NF_biperm (add_cap_to_NF b))
    (stack_biperms (NF_outsize b) (NF_insize b) 2 0
      (realize_NF_biperm b) (n_m_cup_cap 1 0)).
Proof.
  rewrite Nat.add_comm.
  apply matrix_of_biperm_inj.
  - rewrite <- NF_outsize_add_cap_to_NF, <- NF_insize_add_cap_to_NF.
    apply realize_NF_biperm_bipermutation_alt.
    apply add_cap_to_NF_WF, Hb.
  - replace (NF_insize b) with (NF_insize b + 0) at 1 by lia.
    rewrite (Nat.add_comm 2).
    auto with biperm_db.
  - rewrite (matrix_of_realize_NF_biperm' (NF_insize b) (2 + (NF_outsize b)))
      by (cbn; lia + apply add_cap_to_NF_WF, Hb).
    rewrite NF_outsize_add_cap_to_NF, NF_insize_add_cap_to_NF.
    rewrite matrix_of_stack_biperms' by (lia + auto with biperm_db).
    cbn -[Nat.add].
    change (n_m_cup_cap (ncup' b)) with (n_m_cup_cap (0 + ncup' b)).
    rewrite (Nat.add_comm 0), (Nat.add_comm 1 (ncap' b)).
    rewrite n_m_cup_cap_comm, n_m_cup_cap_plus_plus_decomp.
    rewrite matrix_of_stack_biperms' by (lia + auto with biperm_db).
    rewrite matrix_of_realize_NF_biperm' by easy.
    rewrite perm_to_matrix_of_stack_perms by (apply Hb + auto with perm_db).
    restore_dims.
    rewrite kron_assoc by auto_wf.
    restore_dims.
    rewrite kron_mixed_product' by unify_pows_two.
    rewrite perm_to_matrix_idn, Mmult_1_l by auto_wf.
    rewrite <- (Mmult_1_r _ _ (matrix_of_biperm 0 2 (n_m_cup_cap 1 0))) 
      by auto_wf.
    rewrite <- kron_mixed_product, kron_1_l by auto_wf.
    restore_dims.
    cbn [Nat.add].
    rewrite (n_m_cup_cap_comm (ncap' b)).
    reflexivity.
Qed.

Lemma realize_add_cup_to_NF (b : NF_biperm) (Hb : WF_NF_biperm b) :
  perm_eq ((NF_outsize b) + (2 + NF_insize b)) 
    (realize_NF_biperm (add_cup_to_NF b))
    (stack_biperms (NF_outsize b) (NF_insize b) 0 2
      (realize_NF_biperm b) (n_m_cup_cap 0 1)).
Proof.
  rewrite Nat.add_comm.
  apply matrix_of_biperm_inj.
  - rewrite <- NF_outsize_add_cup_to_NF, <- NF_insize_add_cup_to_NF.
    apply realize_NF_biperm_bipermutation_alt.
    apply add_cup_to_NF_WF, Hb.
  - replace (NF_outsize b) with (NF_outsize b + 0) at 1 by lia.
    rewrite (Nat.add_comm 2).
    auto with biperm_db.
  - rewrite (matrix_of_realize_NF_biperm' (2 + NF_insize b) (NF_outsize b))
      by (cbn; lia + apply add_cup_to_NF_WF, Hb).
    rewrite NF_outsize_add_cup_to_NF, NF_insize_add_cup_to_NF.
    rewrite matrix_of_stack_biperms' by (lia + auto with biperm_db).
    cbn -[Nat.add].
    change (n_m_cup_cap ?x (ncap' b)) with (n_m_cup_cap x (0 + ncap' b)).
    rewrite (Nat.add_comm 0), (Nat.add_comm 1 (ncup' b)).
    rewrite n_m_cup_cap_comm, n_m_cup_cap_plus_plus_decomp.
    rewrite matrix_of_stack_biperms' by (lia + auto with biperm_db).
    rewrite matrix_of_realize_NF_biperm' by easy.
    rewrite perm_to_matrix_of_stack_perms by (apply Hb + auto with perm_db).
    restore_dims.
    rewrite kron_assoc by auto_wf.
    rewrite Mmult_assoc.
    restore_dims.
    rewrite kron_mixed_product' by unify_pows_two.
    rewrite perm_to_matrix_idn, Mmult_1_r by auto_wf.
    rewrite <- (Mmult_1_l _ _ (matrix_of_biperm 2 0 (n_m_cup_cap 0 1))) 
      by auto_wf.
    rewrite Mmult_assoc.
    rewrite <- kron_mixed_product, kron_1_l by auto_wf.
    restore_dims.
    rewrite (n_m_cup_cap_comm (ncup' b)).
    reflexivity.
Qed.

Lemma realize_add_id_to_NF (b : NF_biperm) (Hb : WF_NF_biperm b) :
  perm_eq ((NF_outsize b + 1) + (NF_insize b + 1)) 
    (realize_NF_biperm (add_id_to_NF b))
    (stack_biperms 1 1 (NF_outsize b) (NF_insize b)
      (idn_biperm 1) (realize_NF_biperm b)).
Proof.
  rewrite Nat.add_comm.
  apply matrix_of_biperm_inj.
  - rewrite <- NF_outsize_add_id_to_NF, <- NF_insize_add_id_to_NF.
    apply realize_NF_biperm_bipermutation_alt.
    apply add_id_to_NF_WF, Hb.
  - rewrite 2!(Nat.add_comm _ 1). 
    auto with biperm_db.
  - rewrite (matrix_of_realize_NF_biperm' (NF_insize b + 1) (NF_outsize b + 1))
      by (cbn; lia + apply add_id_to_NF_WF, Hb).
    rewrite NF_outsize_add_id_to_NF, NF_insize_add_id_to_NF.
    rewrite matrix_of_stack_biperms' by (lia + auto with biperm_db).
    cbn -[Nat.add].
    rewrite (Nat.pow_add_r 2 (nid' b) 1).
    rewrite <- id_kron.
    rewrite 2!perm_to_matrix_of_stack_perms by (apply Hb + auto with perm_db).
    rewrite <- kron_assoc by auto_wf.
    restore_dims. 
    rewrite 2!kron_mixed_product' by unify_pows_two.
    rewrite perm_to_matrix_idn, matrix_of_idn_biperm.
    rewrite !Mmult_1_l by auto_wf.
    rewrite matrix_of_realize_NF_biperm' by easy.
    restore_dims.
    easy.
Qed.

Definition compose_perm_l_NF_biperm 
  (g : nat -> nat) (f : NF_biperm) : NF_biperm :=
  {|
    lperm' := g ∘ lperm' f;
    rperm' := rperm' f;
    ncup' := ncup' f;
    ncap' := ncap' f;
    nid' := nid' f
  |}.

Lemma compose_perm_l_NF_biperm_WF f g 
  (Hf : WF_NF_biperm f) (Hg : permutation (NF_insize f) g) :
  WF_NF_biperm (compose_perm_l_NF_biperm g f).
Proof.
  split; [|apply Hf].
  apply permutation_compose; [apply Hg|apply Hf].
Qed.

Lemma matrix_of_compose_perm_l_NF_biperm f g 
  (Hf : WF_NF_biperm f) (Hg : permutation (NF_insize f) g) :
  matrix_of_NF_biperm (compose_perm_l_NF_biperm g f) = 
  matrix_of_NF_biperm f × perm_to_matrix (NF_insize f) g.
Proof.
  rewrite matrix_of_WF_NF_biperm by now apply compose_perm_l_NF_biperm_WF.
  rewrite matrix_of_WF_NF_biperm by easy.
  cbn.
  pose proof Hf as [].
  rewrite perm_to_matrix_compose by auto with perm_db.
  now rewrite <- Mmult_assoc.
Qed.

Definition compose_perm_r_NF_biperm 
  (g : nat -> nat) (b : NF_biperm) : NF_biperm := 
  {|
    lperm' := lperm' b;
    rperm' := rperm' b ∘ g;
    ncup' := ncup' b;
    ncap' := ncap' b;
    nid' := nid' b;
  |}.

Lemma compose_perm_r_NF_biperm_WF (b : NF_biperm) (g : nat -> nat)
  (Hb : WF_NF_biperm b) (Hg : permutation (NF_outsize b) g) : 
  WF_NF_biperm (compose_perm_r_NF_biperm g b).
Proof.
  split; [apply Hb|].
  apply permutation_compose; [apply Hb|apply Hg].
Qed.

Lemma matrix_of_compose_perm_r_NF_biperm f g 
  (Hf : WF_NF_biperm f) (Hg : permutation (NF_outsize f) g) :
  matrix_of_NF_biperm (compose_perm_r_NF_biperm g f) = 
  perm_to_matrix (NF_outsize f) g × matrix_of_NF_biperm f.
Proof.
  rewrite matrix_of_WF_NF_biperm by now apply compose_perm_r_NF_biperm_WF.
  rewrite matrix_of_WF_NF_biperm by easy.
  cbn.
  pose proof Hf as [].
  (* TODO : FIX! *)
  Abort.
  (* rewrite perm_to_matrix_compose by auto with perm_db.
  now rewrite <- Mmult_assoc.
Qed. *)

Lemma realize_compose_perm_l_NF_biperm g b 
  (Hb : WF_NF_biperm b) (Hg : permutation (NF_insize b) g) : 
  perm_eq (NF_outsize b + NF_insize b) 
    (realize_NF_biperm (compose_perm_l_NF_biperm g b))
    (biperm_compose_perm_r (NF_outsize b) (NF_insize b)
      (realize_NF_biperm b) (
        reflect_perm (NF_insize b) ∘ 
        perm_inv' (NF_insize b) g ∘ reflect_perm (NF_insize b))).
Proof.
  unfold compose_perm_l_NF_biperm.
  destruct b; unfold WF_NF_biperm in Hb; cbn in *.
  destruct Hb as [Hl Hr].
  rewrite 2!realize_NF_biperm_constructor.
  unfold realize_biperm_data.
  rewrite 2!biperm_compose_perm_l_r_swap_eq by auto with biperm_db.
  rewrite biperm_compose_perm_r_compose_eq by auto with biperm_db.
  intros k Hk.
  apply f_equal_gen; [|easy].
  apply biperm_compose_perm_r_eq_of_perm_eq;
  split; easy || auto with biperm_db.
  rewrite <- compose_assoc.
  apply perm_eq_compose_proper; [cleanup_perm_inv| | easy].
  rewrite !compose_assoc.
  apply perm_eq_compose_proper; [cleanup_perm_inv| easy |].
  rewrite_compose_assoc_r reflect_perm_invol_eq.
  rewrite perm_inv'_eq.
  auto with perm_inv_db.
Qed.

Lemma realize_compose_perm_r_NF_biperm g b 
  (Hb : WF_NF_biperm b) (Hg : permutation (NF_outsize b) g) : 
  perm_eq (NF_outsize b + NF_insize b) 
    (realize_NF_biperm (compose_perm_r_NF_biperm g b))
    (biperm_compose_perm_l (NF_outsize b) (NF_insize b)
      (realize_NF_biperm b) (
        reflect_perm (NF_outsize b) ∘ 
         g ∘ reflect_perm (NF_outsize b))).
Proof.
  unfold compose_perm_r_NF_biperm.
  destruct b; unfold WF_NF_biperm in Hb; cbn in *.
  destruct Hb as [Hl Hr].
  rewrite 2!realize_NF_biperm_constructor.
  unfold realize_biperm_data.
  rewrite biperm_compose_perm_l_compose_eq by auto with biperm_db.
  rewrite !compose_assoc.
  rewrite_compose_assoc_r reflect_perm_invol_eq.
  easy.
Qed.

Definition stack_NF_biperms (b c : NF_biperm) : NF_biperm :=
  {|
    lperm' := 
      stack_perms (NF_insize b) (NF_insize c) (lperm' b) (lperm' c) ∘
      stack_perms (ncup' b + ncup' b + (ncup' c + ncup' c) + nid' b) (nid' c)
        (stack_perms (ncup' b + ncup' b) ((ncup' c + ncup' c) + nid' b)
          idn (big_swap_perm (ncup' c + ncup' c) (nid' b))) idn;
    rperm' := 
      stack_perms (ncap' b + ncap' b + (ncap' c + ncap' c) + nid' b) (nid' c)
        (stack_perms (ncap' b + ncap' b) ((ncap' c + ncap' c) + nid' b)
          idn (big_swap_perm (nid' b) (ncap' c + ncap' c))) idn
      ∘ stack_perms (NF_outsize b) (NF_outsize c) (rperm' b) (rperm' c);
    ncup' := ncup' b + ncup' c;
    ncap' := ncap' b + ncap' c;
    nid' := nid' b + nid' c;
  |}.

Lemma NF_insize_stack_NF_biperms b c : 
  NF_insize (stack_NF_biperms b c) = NF_insize b + NF_insize c.
Proof. cbn; lia. Qed.

Lemma NF_outsize_stack_NF_biperms b c : 
  NF_outsize (stack_NF_biperms b c) = NF_outsize b + NF_outsize c.
Proof. cbn; lia. Qed.

Lemma stack_NF_biperms_WF b c (Hb : WF_NF_biperm b) (Hc : WF_NF_biperm c) : 
  WF_NF_biperm (stack_NF_biperms b c).
Proof.
  destruct Hb, Hc.
  split; cbn; auto with perm_db.
Qed.

Lemma realize_stack_NF_biperms b c (Hb : WF_NF_biperm b) (Hc : WF_NF_biperm c) : 
  perm_eq (NF_outsize (stack_NF_biperms b c) 
    + NF_insize (stack_NF_biperms b c)) 
    (realize_NF_biperm (stack_NF_biperms b c))
    (stack_biperms (NF_outsize c) (NF_insize c) (NF_outsize b) (NF_insize b)
      (realize_NF_biperm c) (realize_NF_biperm b)).
Proof.
  rewrite Nat.add_comm.
  apply matrix_of_biperm_inj.
  - rewrite Nat.add_comm; 
    now apply realize_NF_biperm_bipermutation, stack_NF_biperms_WF.
  - rewrite Nat.add_comm; 
    rewrite NF_outsize_stack_NF_biperms, NF_insize_stack_NF_biperms.
    rewrite (Nat.add_comm (NF_outsize b)), (Nat.add_comm (NF_insize b)).
    apply stack_biperms_bipermutation;
    now apply realize_NF_biperm_bipermutation.
  - rewrite matrix_of_realize_NF_biperm'
      by (auto using stack_NF_biperms_WF).
    rewrite matrix_of_stack_biperms' 
      by (rewrite Nat.add_comm; cbn;
      auto using realize_NF_biperm_bipermutation with zarith).
    rewrite 2!matrix_of_realize_NF_biperm' by easy.
    cbn.
    rewrite n_m_cup_cap_comm, (Nat.add_comm (ncap' b)), 
      (Nat.add_comm (ncup' b)),
      n_m_cup_cap_plus_plus_decomp.
    rewrite matrix_of_stack_biperms' by auto with biperm_db zarith.
    rewrite (Nat.pow_add_r 2 (nid' b)), <- id_kron.
    destruct Hb, Hc.
    rewrite 2!perm_to_matrix_compose by cleanup_perm_inv.
    rewrite 6!perm_to_matrix_of_stack_perms' by auto with perm_db zarith.
    rewrite <- kron_comm_pows2_eq_perm_to_matrix_big_swap.
    restore_dims.
    rewrite (Nat.add_comm (ncup' c + ncup' c) (nid' b)).
    rewrite <- kron_comm_pows2_eq_perm_to_matrix_big_swap.
    rewrite !perm_to_matrix_idn.
    rewrite <- 2!kron_mixed_product.
    rewrite !Mmult_assoc.
    (* restore_dims. *)
    (* unify_pows_two. *)
    apply mmult_mat_equiv_morph; [easy|].
    rewrite <- !Mmult_assoc.
    restore_dims.
    rewrite <- kron_assoc, (kron_assoc _ _ (I (2^ nid' b))) by auto_wf.
    restore_dims.
    rewrite 2!kron_mixed_product' by unify_pows_two.
    rewrite Mmult_1_l, Mmult_1_r by auto_wf.
    rewrite kron_comm_commutes_l by auto_wf.
    rewrite <- Mmult_assoc, 2!kron_mixed_product.
    rewrite Mmult_assoc, kron_comm_mul_inv, 3!Mmult_1_r by auto_wf.
    rewrite <- !kron_assoc by auto_wf.
    restore_dims.
    rewrite 2!(n_m_cup_cap_comm (ncap' _)).
    reflexivity.
Qed.

(* TODO : 
Lemma realize_stack_NF_biperms (Hb : WF_NF_biperm b) (Hc : WF_NF_biperm c) : 
  matrix_of_NF_biperm (stack_NF_biperms b c) = 
  matrix_of_NF_biperm b ⊗ matrix_of_NF_biperm c.
*)

Local Open Scope prg.

Lemma biperm_NF_absorb_tensor_2_idn_perm_l lperm rperm nid ncup ncap f
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  (Hf : permutation ncup f) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data (lperm ∘ tensor_perms ncup 2 f idn)
      rperm nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  replace (tensor_perms ncup 2 f idn) with 
    (stack_perms (ncup + ncup) nid (tensor_perms ncup 2 f idn) idn) 
    by cleanup_perm.
  rewrite 2!matrix_of_realize_biperm_data by auto with perm_db.
  rewrite perm_to_matrix_compose by auto with perm_db.
  rewrite <- Mmult_assoc.
  f_equal.
  rewrite Mmult_assoc.
  f_equal.
  rewrite perm_to_matrix_of_stack_perms, 
    perm_to_matrix_idn by auto with perm_db.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_r by auto with wf_db.
  f_equal.
  rewrite matrix_of_biperm_Mmult_perm_r_eq by auto with biperm_db.
  rewrite <- 2!biperm_compose_perm_r_compose_eq by auto with biperm_db.
  rewrite n_m_cup_cap_comm.
  rewrite n_m_cup_cap_absorb_reflect_perm_l.
  assert (H2cup : ncup + ncup = ncup * 2) by lia. 
  rewrite H2cup.
  rewrite tensor_perms_inv' by auto with perm_db.
  rewrite <- H2cup.
  rewrite idn_inv'.
  rewrite n_m_cup_cap_absorb_tensor_2_idn_perm_l_eq by auto with perm_db.
  now rewrite n_m_cup_cap_absorb_reflect_perm_l.
Qed.

Lemma biperm_NF_absorb_tensor_2_idn_perm_l' lperm rperm nid ncup ncap f
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  (Hf : permutation ncup f) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data (lperm ∘ 
      stack_perms (ncup + ncup) nid (tensor_perms ncup 2 f idn) idn)
      rperm nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  rewrite stack_perms_WF_idn by cleanup_perm.
  now apply biperm_NF_absorb_tensor_2_idn_perm_l.
Qed.

Lemma biperm_NF_absorb_l_perm_r_perm_inv' lperm rperm nid ncup ncap f
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  (Hf : permutation nid f) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data 
      (lperm ∘ stack_perms (ncup + ncup) nid idn f)
      (stack_perms (ncap + ncap) nid idn (perm_inv' nid f) ∘ rperm) 
      nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  rewrite 2!matrix_of_realize_biperm_data by auto with perm_db.
  rewrite !perm_to_matrix_compose by auto with perm_db.
  rewrite <- Mmult_assoc.
  f_equal.
  rewrite !Mmult_assoc.
  f_equal.
  rewrite !perm_to_matrix_of_stack_perms, 
    !perm_to_matrix_idn by auto with perm_db.
  restore_dims.
  rewrite 2!kron_mixed_product, !Mmult_1_l, Mmult_1_r by auto with wf_db.
  f_equal.
  rewrite <- perm_to_matrix_transpose_eq' by auto.
  apply perm_mat_transpose_linv; auto with perm_db.
Qed.

Lemma biperm_NF_absorb_l_r_perm_invs lperm rperm nid ncup ncap f g
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  (Hf : permutation nid f) (Hg : permutation nid g) 
  (Hfg : perm_eq nid (f ∘ g) idn) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data 
      (lperm ∘ stack_perms (ncup + ncup) nid idn f)
      (stack_perms (ncap + ncap) nid idn g ∘ rperm) 
      nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  rewrite 2!matrix_of_realize_biperm_data by auto with perm_db.
  rewrite !perm_to_matrix_compose by auto with perm_db.
  rewrite <- Mmult_assoc.
  f_equal.
  rewrite !Mmult_assoc.
  f_equal.
  rewrite !perm_to_matrix_of_stack_perms, 
    !perm_to_matrix_idn by auto with perm_db.
  restore_dims.
  rewrite 2!kron_mixed_product, !Mmult_1_l, Mmult_1_r by auto with wf_db.
  f_equal.
  rewrite <- perm_to_matrix_compose, 
    (perm_to_matrix_eq_of_perm_eq _ _ _ Hfg) by auto with perm_db.
  apply perm_to_matrix_idn.
Qed.

(* #[export] Hint Extern 20 (permutation ?n (swap_perm ?a ?b ?n')) =>
  apply (fun H => proj1 (permutation_change_dims n' n H _));
  []
  solve [auto with zarith *)

(* #[export] Hint Extern 100 (permutation ?n ?f) => 
  is_ground n;
  lazymatch f with 
  | compose _ _ => 
    idtac "hit compose:";
    print_goal;
    apply permutation_compose
  | stack_perms ?k ?l => 
    replace n with (k + l) by lia;
    apply stack_perms_permutation
  | _ => 
    idtac "hit WF";
    print_goal; 
    eapply permutation_of_le_permutation_WF;
    print_goal;
    fail;
    solve [auto with perm_db WF_Perm_db zarith]
  end : perm_db. *)



Lemma biperm_NF_absorb_swap_0_1_perm_l lperm rperm nid ncup ncap f g
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  (Hf : permutation nid f) (Hg : permutation nid g) 
  (Hfg : perm_eq nid (f ∘ g) idn) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data (lperm ∘ 
      stack_perms (ncup + ncup) nid (swap_perm 0 1 (ncup + ncup)) idn)
      rperm nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  bdestruct (ncup =? 0);
  [now rewrite swap_perm_big_eq, stack_perms_idn_idn, compose_idn_r by lia|].
  assert (permutation (ncup + ncup) (swap_perm 0 1 (ncup + ncup))) 
    by (auto with perm_db zarith).
  rewrite 2!matrix_of_realize_biperm_data by auto with perm_db.
  rewrite !perm_to_matrix_compose by auto with perm_db.
  rewrite <- Mmult_assoc.
  f_equal.
  rewrite !Mmult_assoc.
  f_equal.
  rewrite !perm_to_matrix_of_stack_perms, 
    !perm_to_matrix_idn by auto with perm_db.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_l by auto with wf_db.
  f_equal.
  rewrite matrix_of_biperm_Mmult_perm_r_eq by auto with biperm_db.
  rewrite swap_perm_inv' by lia.
  rewrite swap_perm_conj_reflect_eq by lia.
  rewrite swap_perm_comm.
  replace (ncup + ncup - 1) with (S (ncup + ncup - 2)) by lia.
  now rewrite n_m_cup_cap_comm, n_m_cup_cap_absorb_perm_swap_even_S_l by
    (now rewrite Nat.even_sub, even_add_same by lia).
Qed.



Lemma biperm_NF_absorb_swap_even_S_perm_l lperm rperm nid ncup ncap a
  (Ha : Nat.even a = true)
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data (lperm ∘ 
      swap_perm a (S a) (ncup + ncup))
      rperm nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  assert (permutation (ncup + ncup) (swap_perm a (S a) (ncup + ncup)))
    by (apply swap_perm_even_S_even_permutation; easy + apply even_add_same).
  replace (swap_perm a (S a) (ncup + ncup)) with
    (stack_perms (ncup + ncup) nid (swap_perm a (S a) (ncup + ncup)) idn)
    by cleanup_perm.
  
  bdestruct (ncup + ncup <=? a);
  [now rewrite swap_perm_big_eq, stack_perms_idn_idn, compose_idn_r by lia|].
  pose proof (succ_even_lt_even a (ncup + ncup) 
    Ha (even_add_same _) ltac:(easy)).
  rewrite 2!matrix_of_realize_biperm_data by auto with perm_db.
  rewrite !perm_to_matrix_compose by auto with perm_db.
  rewrite <- Mmult_assoc.
  f_equal.
  rewrite !Mmult_assoc.
  f_equal.
  rewrite !perm_to_matrix_of_stack_perms, 
    !perm_to_matrix_idn by auto with perm_db.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_l by auto with wf_db.
  f_equal.
  rewrite matrix_of_biperm_Mmult_perm_r_eq by auto with biperm_db.
  
  rewrite swap_perm_inv' by lia.
  rewrite swap_perm_conj_reflect_eq by lia.
  rewrite swap_perm_comm.
  replace (ncup + ncup - S a) with (S (ncup + ncup - S (S a))) by lia.
  now rewrite n_m_cup_cap_comm, n_m_cup_cap_absorb_perm_swap_even_S_l by
    (now rewrite Nat.even_sub, even_add_same, Nat.even_succ_succ, Ha by lia).
Qed.

Lemma biperm_NF_absorb_swap_even_S_perm_l' lperm rperm nid ncup ncap a
  (Ha : Nat.even a = true)
  (Hlperm : permutation (ncup + ncup + nid) lperm) 
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data (lperm ∘ 
      stack_perms (ncup + ncup) nid (swap_perm a (S a) (ncup + ncup)) idn)
      rperm nid ncup ncap) = 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid) 
    (realize_biperm_data lperm rperm nid ncup ncap).
Proof.
  rewrite stack_perms_WF_idn by cleanup_perm.
  now apply biperm_NF_absorb_swap_even_S_perm_l.
Qed.





(* Computes normal form for the bipermutation given by composing to
  the bipermutation whose normal form is (lperm, nid, ncup, ncap, rperm)
  a cap (⊂) at position padl (so S padl < nid + ncup). There are 3 cases:
  - Both legs of the cap end up in the cups. 2 subcases:
    + If the legs end up at the same cup, we simply contract lperm along
      both legs and decrement ncup
    + If the legs up at different cups we permute lperm with swap_block_perm
      so that the legs end up at the first and second cup. Then, we 
      contract lperm along both legs and decrement ncup (note we don't 
      need to worry about swapping at the destination caps, though for 
      maximal 'visual' clarity we could swap so that the legs of the cap
      end up adjacent, i.e. at indices 1 and 2 / 2nd and 3rd from the top)
  - Both legs of the cap end up in the ids. In this case, we 'WLOG' swap 
    after lperm / before rperm symmetrically so that the legs end up at
    the first two ids, then contract lperm along both legs of the cap and
    increment ncap
  - One leg of the cap lands in the ids while one lands in the cups. In 
    this case, we permute with swap_block_perm to make one leg land at the
    last cup, then 'WLOG' swap after lperm / before rperm symmetrically 
    so that the other leg lands at the first id. Then, we simply contract
    lperm along both legs. (This ensures the other input to the target cup
    ends up at the first id, as is correct.)
*)

Definition prep_compose_cap_NF_l (lperm_init rperm : nat -> nat) 
  (nid ncup ncap padl : nat) :=
  let lperm := perm_inv (ncup + ncup + nid) lperm_init in
  if (lperm padl <? ncup + ncup) && (lperm (S padl) <? ncup + ncup) then
    (* First case, both in cups *)
    if lperm padl / 2 =? lperm (S padl) / 2 then
      let cup := lperm padl / 2 in 
      (* First subcase, same cup *)
      let lperm_alt := lperm_init ∘ tensor_perms ncup 2 (swap_perm 0 cup ncup) idn in
      let lperm_alt_1 := 
        if lperm padl <? lperm (S padl) then lperm_alt 
        else lperm_alt ∘ swap_perm 0 1 (ncup + ncup) (* Ensure first goes to first *)
        in
      (* let lperm' := contract_perm (contract_perm lperm (S padl)) padl in *)
      Build_NF_biperm lperm_alt_1 rperm nid (ncup(*  - 1 *)) ncap
    else 
      (* Second subcase, different cups *)
      let cup1 := lperm padl / 2 in let cup2 := lperm (S padl) / 2 in
      let lperm_alt := 
          lperm_init ∘ 
          tensor_perms ncup 2 (swap_2_to_2_perm 0 1 cup1 cup2 ncup) idn in
      let lperm_alt_1 :=
        if Nat.even (lperm padl) then 
        lperm_alt ∘ swap_perm 0 1 (ncup + ncup)
        else lperm_alt
        in
      let lperm_alt_2 :=
        if Nat.even (lperm (S padl)) then 
        lperm_alt_1
        else lperm_alt_1 ∘ swap_perm 2 3 (ncup + ncup)
        in
      (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
      Build_NF_biperm lperm_alt_2 rperm nid (ncup(*  - 1 *)) ncap
  else if (lperm padl <? ncup + ncup) (* && (lperm (S padl) <? ncup + ncup) *) then
    (* Third case, first orientation (first leg in cup) *)
    let cup1 := lperm padl / 2 in let id2 := lperm (S padl) - (ncup + ncup) in
    let lperm_alt := 
      lperm_init ∘ stack_perms (ncup + ncup) nid 
        (tensor_perms ncup 2 (swap_perm cup1 (ncup - 1) ncup) idn)
        idn in
    let lperm_alt_1 := 
      if Nat.even (lperm padl) then 
      lperm_alt ∘ swap_perm (ncup + ncup - 2) (ncup + ncup - 1) (ncup + ncup)  
      else lperm_alt in
    let lperm_alt_1' :=
      lperm_alt_1 ∘ stack_perms (ncup + ncup) nid idn (swap_perm 0 id2 nid) in
    let rperm' := 
      stack_perms (ncap + ncap) nid idn (swap_perm 0 id2 nid) ∘ rperm in
    (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
    Build_NF_biperm lperm_alt_1' rperm' nid (ncup(*  - 1 *)) ncap
  else if (* (lperm padl <? ncup + ncup) && *) (lperm (S padl) <? ncup + ncup) then
    (* Third case, second orientation (second leg in cup) *)
    let id1 := lperm padl - (ncup + ncup) in let cup2 := lperm (S padl) / 2 in
    let lperm_alt := 
      lperm_init ∘ stack_perms (ncup + ncup) nid 
        (tensor_perms ncup 2 (swap_perm cup2 (ncup - 1) ncup) idn)
        idn in
    let lperm_alt_1 := 
      if Nat.even (lperm (S padl)) then 
      lperm_alt ∘ swap_perm (ncup + ncup - 2) (ncup + ncup - 1) (ncup + ncup) 
      else lperm_alt
      in
    let lperm_alt_1' :=
      lperm_alt_1 ∘ stack_perms (ncup + ncup) nid idn (swap_perm 0 id1 nid) in
    let rperm' := 
      stack_perms (ncap + ncap) nid idn (swap_perm 0 id1 nid) ∘ rperm in
    (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
    Build_NF_biperm lperm_alt_1' rperm' nid (ncup(*  - 1 *)) ncap
  else (* if (lperm padl <? ncup + ncup) && (lperm (S padl) <? ncup + ncup) then *)
    (* Second case, both legs in ids *)
    let id1 := lperm padl - (ncup + ncup) in 
    let id2 := lperm (S padl) - (ncup + ncup) in
    let id2' := swap_perm 0 id1 nid id2 in
    let lperm_alt :=
      lperm_init ∘ stack_perms (ncup + ncup) nid idn
        (swap_2_to_2_perm 0 1 id1 id2 nid)
        (* (swap_perm 0 id1 nid ∘ swap_perm 1 id2' nid) *) in
    let rperm' := 
      stack_perms (ncap + ncap) nid idn 
        (perm_inv nid (swap_2_to_2_perm 0 1 id1 id2 nid))
        (* (swap_perm 1 id2' nid ∘ swap_perm 0 id1 nid)  *)
      ∘ rperm in
    (* let lperm' := contract_perm (contract_perm lperm_alt (S padl)) padl in *)
    Build_NF_biperm lperm_alt rperm' nid ncup (ncap(*  + 1 *)).





Lemma prep_compose_cap_NF_l_case_2 lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm padl)  
  (HSpadl :  ncup + ncup <= perm_inv (ncup + ncup + nid) lperm (S padl)) 
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup) = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup + 1) = S padl.
Proof.
  pose proof (perm_inv_bounded (ncup+ncup+nid) lperm) as Hlinvbdd.
  pose proof (Hlinvbdd (padl) ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  pattern (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup))
    false.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup))
    false.
  simpl.
  assert (perm_inv (ncup + ncup + nid) lperm padl <> 
    perm_inv (ncup + ncup + nid) lperm (S padl))
    by (intros Hfalse; 
    apply (ltac:(lia) : (padl <> S padl));
    apply (permutation_is_injective (ncup + ncup + nid)
    (perm_inv (ncup + ncup + nid) lperm)); auto with perm_db zarith).
  unfold Pred; clear Pred.
  unfold compose.
  rewrite 2!stack_perms_right by lia.
  rewrite Nat.sub_diag, add_sub'.
  rewrite swap_2_to_2_perm_first, swap_2_to_2_perm_second by lia.
  split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
Qed.

Lemma prep_compose_cap_NF_l_case_3_2 lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm padl)  
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup - 1) = S padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup) = padl.
Proof.
  pose proof (perm_inv_bounded (ncup+ncup+nid) lperm) as Hlinvbdd.
  pose proof (Hlinvbdd (padl) ltac:(lia)).
  pattern (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup))
    false.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup))
    true.
  simpl.
  rewrite !even_eqb.
  bdestructΩ'; unfold Pred; clear Pred.
  - unfold compose at 1 4.
    rewrite stack_perms_left, stack_perms_right by lia.
    rewrite Nat.sub_diag.
    rewrite swap_perm_left, Nat.sub_add by lia.
    unfold compose at 1 3.
    rewrite swap_perm_right, swap_perm_neither by lia.
    unfold compose, tensor_perms.
    rewrite stack_perms_left, stack_perms_right by lia.
    simplify_bools_lia_one_kernel.
    replace (ncup + ncup - 2) with ((ncup - 1)*2) by lia.
    rewrite Nat.div_mul, Nat.Div0.mod_mul by lia.
    rewrite swap_perm_right by lia.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose at 1 3.
    rewrite stack_perms_left, stack_perms_right by lia.
    rewrite Nat.sub_diag.
    rewrite swap_perm_left, Nat.sub_add by lia.
    unfold compose, tensor_perms.
    rewrite stack_perms_left, stack_perms_right by lia.
    simplify_bools_lia_one_kernel.
    replace (ncup + ncup - 1) with ((ncup - 1)*2 + 1) by lia.
    rewrite Nat.div_add_l, mod_add_l by lia.
    rewrite Nat.add_0_r.
    rewrite swap_perm_right by lia.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.mod_upper_bound 
      (perm_inv (ncup + ncup + nid) lperm (S padl)) 2 ltac:(lia)).
    change (1 mod 2) with 1.
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
Qed.


Lemma prep_compose_cap_NF_l_case_3_1 lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm (S padl))  
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup - 1) = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup) = S padl.
Proof.
  pose proof (perm_inv_bounded (ncup+ncup+nid) lperm) as Hlinvbdd.
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  pattern (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup))
    true.
  replace_bool_lia ((perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup))
    false.
  simpl.
  rewrite !even_eqb.
  bdestructΩ'; unfold Pred; clear Pred.
  - unfold compose at 1 4.
    rewrite stack_perms_left, stack_perms_right by lia.
    rewrite Nat.sub_diag.
    rewrite swap_perm_left, Nat.sub_add by lia.
    unfold compose at 1 3.
    rewrite swap_perm_right, swap_perm_neither by lia.
    unfold compose, tensor_perms.
    rewrite stack_perms_left, stack_perms_right by lia.
    simplify_bools_lia_one_kernel.
    replace (ncup + ncup - 2) with ((ncup - 1)*2) by lia.
    rewrite Nat.div_mul, Nat.Div0.mod_mul by lia.
    rewrite swap_perm_right by lia.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose at 1 3.
    rewrite stack_perms_left, stack_perms_right by lia.
    rewrite Nat.sub_diag.
    rewrite swap_perm_left, Nat.sub_add by lia.
    unfold compose, tensor_perms.
    rewrite stack_perms_left, stack_perms_right by lia.
    simplify_bools_lia_one_kernel.
    replace (ncup + ncup - 1) with ((ncup - 1)*2 + 1) by lia.
    rewrite Nat.div_add_l, mod_add_l by lia.
    rewrite Nat.add_0_r.
    rewrite swap_perm_right by lia.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound 
      (perm_inv (ncup + ncup + nid) lperm (padl)) 2 ltac:(lia)).
    change (1 mod 2) with 1.
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
Qed.

Lemma prep_compose_cap_NF_l_case_1_2 lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hdiff : perm_inv (ncup + ncup + nid) lperm padl / 2 <> 
    perm_inv (ncup + ncup + nid) lperm (S padl) / 2) 
  (Hlperm : permutation (ncup + ncup + nid) lperm):
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 1 = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 2 = S padl.
Proof.
  pattern (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  replace ((perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup) 
    && (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup)) 
    with true by bdestructΩ'.
  simplify_bools_lia_one_kernel.
  pose proof (diff_divs_lower_bound 
    (perm_inv (ncup + ncup + nid) lperm padl)
    (perm_inv (ncup + ncup + nid) lperm (S padl))
    2 (ncup + ncup) ltac:(easy) ltac:(easy) ltac:(easy)).
  rewrite !even_eqb.
  bdestructΩ'; unfold Pred; clear Pred.
  - unfold compose at 1 3.
    rewrite swap_perm_right, swap_perm_neither by lia.
    unfold compose, tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (0 / 2) with 0.
    change (2 / 2) with 1.
    rewrite swap_2_to_2_perm_first, swap_2_to_2_perm_second by lia.
    change (2 mod 2) with 0.
    change (0 mod 2) with 0.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose, tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (1 / 2) with 0.
    change (2 / 2) with 1.
    rewrite swap_2_to_2_perm_first, swap_2_to_2_perm_second by lia.
    change (2 mod 2) with 0.
    change (1 mod 2) with 1.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose at 1 4.
    rewrite swap_perm_neither, swap_perm_left by lia.
    unfold compose at 1 3.
    rewrite swap_perm_right, swap_perm_neither by lia.
    unfold compose, tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (0 / 2) with 0.
    change (3 / 2) with 1.
    rewrite swap_2_to_2_perm_first, swap_2_to_2_perm_second by lia.
    change (3 mod 2) with 1.
    change (0 mod 2) with 0.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose at 1 3.
    rewrite swap_perm_neither, swap_perm_left by lia.
    unfold compose, tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (1 / 2) with 0.
    change (3 / 2) with 1.
    rewrite swap_2_to_2_perm_first, swap_2_to_2_perm_second by lia.
    change (3 mod 2) with 1.
    change (1 mod 2) with 1.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
Qed.

Lemma prep_compose_cap_NF_l_case_1_1 lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hsame : perm_inv (ncup + ncup + nid) lperm padl / 2 = 
    perm_inv (ncup + ncup + nid) lperm (S padl) / 2) 
  (Hlperm : permutation (ncup + ncup + nid) lperm):
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 0 = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 1 = S padl.
Proof.
  pattern (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  replace ((perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup) 
    && (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup)) 
    with true by bdestructΩ'.
  simplify_bools_lia_one_kernel.
  bdestructΩ'; unfold Pred; clear Pred.
  - unfold compose.
    unfold tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (0 / 2) with 0.
    change (1 / 2) with 0.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    pose proof (Nat.mod_upper_bound (perm_inv 
      (ncup + ncup + nid) lperm (S padl)) 2 ltac:(lia)).
    assert (Hpadmod2 : perm_inv (ncup + ncup + nid) 
      lperm (padl) mod 2 = 0) by lia.
    assert (HSpadmod2 : perm_inv (ncup + ncup + nid) 
      lperm (S padl) mod 2 = 1) by lia.
    rewrite 2!Nat.mod_small by lia.
    unfold swap_perm.
    simplify_bools_lia_one_kernel.
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
  - unfold compose at 1 3.
    unfold swap_perm at 2 4; simpl.
    do 2 simplify_bools_lia_one_kernel.
    unfold compose, tensor_perms.
    do 2 simplify_bools_lia_one_kernel.
    change (0 / 2) with 0.
    change (1 / 2) with 0.
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (S padl)) 2).
    pose proof (Nat.div_mod_eq (perm_inv (ncup + ncup + nid) lperm (padl)) 2).
    assert (perm_inv (ncup + ncup + nid) lperm padl <> 
      perm_inv (ncup + ncup + nid) lperm (S padl)) by
      (intros Hfalse; generalize (f_equal lperm Hfalse); 
      cleanup_perm; lia).
    pose proof (Nat.mod_upper_bound (perm_inv 
      (ncup + ncup + nid) lperm (padl)) 2 ltac:(lia)).
    assert (Hpadmod2 : perm_inv (ncup + ncup + nid) 
      lperm (padl) mod 2 = 1) by lia.
    assert (HSpadmod2 : perm_inv (ncup + ncup + nid) 
      lperm (S padl) mod 2 = 0) by lia.
    rewrite 2!Nat.mod_small by lia.
    unfold swap_perm.
    simplify_bools_lia_one_kernel.
    split; symmetry; rewrite <- (perm_inv_eq_iff Hlperm); lia.
Qed.

Lemma prep_compose_cap_NF_l_correct lperm rperm nid ncup ncap padl 
  (Hpadl : S padl < ncup + ncup + nid)
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  realize_NF_biperm 
    (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) =
  realize_biperm_data lperm rperm nid ncup ncap.
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  unfold prep_compose_cap_NF_l.
  pose proof (stack_perms_WF_idn (ncup + ncup) nid) as mkWF.
  rewrite <- (mkWF (tensor_perms ncup 2 (swap_perm 0 (perm_inv 
    (ncup + ncup + nid) lperm padl / 2) ncup) idn)) by cleanup_perm.
  rewrite <- (mkWF (tensor_perms ncup 2 (swap_2_to_2_perm 0 1
       (perm_inv (ncup + ncup + nid) lperm padl / 2)
       (perm_inv (ncup + ncup + nid) lperm (S padl) / 2) ncup) idn)) 
       by cleanup_perm.
  rewrite <- (mkWF (swap_perm 0 1 (ncup + ncup))) by cleanup_perm.
  rewrite <- (mkWF (swap_perm 2 3 (ncup + ncup))) by cleanup_perm.
  rewrite <- (mkWF (swap_perm (ncup + ncup - 2) (ncup + ncup - 1)
    (ncup + ncup))) by cleanup_perm.
  bdestruct (perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup);
    [assert (perm_inv (ncup + ncup + nid) lperm padl / 2 < ncup)   
    by (apply Nat.Div0.div_lt_upper_bound; lia)|];
  (bdestruct (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup); 
    [assert (perm_inv (ncup + ncup + nid) lperm (S padl) / 2 < ncup) 
    by (apply Nat.Div0.div_lt_upper_bound; lia)|]);
  cbn [andb];
  [bdestruct (perm_inv (ncup + ncup + nid) lperm padl / 2 
    =? perm_inv (ncup + ncup + nid) lperm (S padl) / 2)|..];
  rewrite realize_NF_biperm_constructor.
  - apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|].
    apply matrix_of_biperm_inj; 
      [apply realize_biperm_data_bipermutation; auto 6 with perm_db zarith;
      bdestruct_one; auto 6 with perm_db zarith..|].
    bdestruct (perm_inv (ncup + ncup + nid) lperm padl <? 
      perm_inv (ncup + ncup + nid) lperm (S padl)).
    + now rewrite biperm_NF_absorb_tensor_2_idn_perm_l' by 
        auto with perm_db zarith.
    + rewrite biperm_NF_absorb_swap_even_S_perm_l'
        by (auto with perm_db zarith).
      now rewrite biperm_NF_absorb_tensor_2_idn_perm_l' by 
        auto with perm_db zarith.
  - apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
      [auto with WF_Perm_db..|].
    apply matrix_of_biperm_inj;
    [apply realize_biperm_data_bipermutation; 
      bdestructΩ'; auto 10 with perm_db zarith..|].
    destruct 
      (Nat.even (perm_inv (ncup + ncup + nid) lperm (S padl))) eqn:HSpadle, 
      (Nat.even (perm_inv (ncup + ncup + nid) lperm padl)) eqn:Hpadle;
    rewrite 2?biperm_NF_absorb_swap_even_S_perm_l'
        by (auto 10 with perm_db zarith);
    now rewrite 2?biperm_NF_absorb_tensor_2_idn_perm_l'
        by (auto with perm_db zarith).
  - replace (ncup + ncup - 1) with (S (ncup + ncup - 2)) by lia.
    apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|]. 
    apply matrix_of_biperm_inj;
      [apply realize_biperm_data_bipermutation; auto 10 with perm_db zarith..|];
      [bdestructΩ'; auto 10 with perm_db zarith|..]. 
    destruct (Nat.even (perm_inv (ncup + ncup + nid) lperm padl)) eqn:Hpadle;
    rewrite biperm_NF_absorb_l_r_perm_invs
      by (auto 10 with perm_db zarith; cleanup_perm);
    [rewrite biperm_NF_absorb_swap_even_S_perm_l'
      by ((now rewrite Nat.even_sub, even_add_same by lia) 
        + auto 10 with perm_db zarith)|];
    now rewrite 2?biperm_NF_absorb_tensor_2_idn_perm_l'
        by (auto with perm_db zarith).
  - replace (ncup + ncup - 1) with (S (ncup + ncup - 2)) by lia.
    apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|]. 
    apply matrix_of_biperm_inj;
      [apply realize_biperm_data_bipermutation; auto 10 with perm_db zarith..|];
      [bdestructΩ'; auto 10 with perm_db zarith|..].
    destruct (Nat.even (perm_inv (ncup + ncup + nid) lperm (S padl))) eqn:Hpadle;
    rewrite biperm_NF_absorb_l_r_perm_invs
      by (auto 10 with perm_db zarith; cleanup_perm);
    [rewrite biperm_NF_absorb_swap_even_S_perm_l'
        by ((now rewrite Nat.even_sub, even_add_same by lia) 
          + auto 10 with perm_db zarith)|];
    now rewrite 2?biperm_NF_absorb_tensor_2_idn_perm_l'
        by (auto with perm_db zarith).
  - apply (eq_of_WF_perm_eq (ncup + ncup + nid + (ncap + ncap + nid)));
    [auto with WF_Perm_db..|]. 
    apply matrix_of_biperm_inj;
      [apply realize_biperm_data_bipermutation; auto 10 with perm_db zarith..|].
    rewrite biperm_NF_absorb_l_r_perm_invs;
    [easy|auto with perm_db zarith..].
    apply perm_inv_rinv_of_permutation.
    auto with perm_db zarith.
Qed.



Local Open Scope prg.

(* TODO: Do these lemmas belong in Qlib? *)

Lemma perm_to_matrix_cap_straight_pullthrough_r {n f} (Hf : permutation n f) 
  padl (Hpadl : S padl < n) (Hfpadl : f padl = padl) 
  (HfSpadl : f (S padl) = S padl) :
  @Mmult (2^n) (2^n) (2^(n-2)) (perm_to_matrix n f)
  ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl)))) =
  @Mmult (2^n) (2^(n-2)) (2^(n-2))
  ((I (2^ padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm f (S padl)) padl)).
Proof. Abort. (* Aborted for performance. Do we need this? *) (*
  pose proof (permutation_is_bounded _ _ Hf) as Hfbdd.
  pose proof (Hfbdd padl ltac:(lia)).
  pose proof (Hfbdd (S padl) Hpadl).
  apply mat_equiv_eq; auto with wf_db.
  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite <- Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits_l by easy.
  rewrite 3!Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits by
    (replace (n-2) with ((n - 1) - 1) by lia;
      apply contract_perm_bounded; try lia;
      auto with perm_db).
  replace (f_to_vec n) with
    (f_to_vec (padl + 2 + (n - (2 + padl)))) by (f_equal; lia).
  replace (f_to_vec (n-2)) with 
    (f_to_vec (padl + 0 + (n - (2 + padl)))) by (f_equal; lia).
  rewrite !f_to_vec_split'_eq.
  rewrite !(fun x y => kron_transpose' _ _ x y).

  rewrite !(fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z) by
    (now rewrite <- ?Nat.pow_add_r; lia + (f_equal; lia)).
  unfold kron.
  rewrite !Nat.mod_1_r, !Nat.Div0.div_0_l.
  rewrite Cmult_comm.
  symmetry.
  rewrite Cmult_comm, !Cmult_assoc.
  f_equal.
  - rewrite !basis_f_to_vec, <- !Mmult_assoc.
    rewrite !matrix_conj_basis_eq_lt by apply funbool_to_nat_bound.
    unfold I.
    do 4 match goal with
    |- context [funbool_to_nat ?k ?f <? 2 ^ ?k] => 
      replace (funbool_to_nat k f <? 2 ^ k) with true by
      (pose proof (funbool_to_nat_bound k f); bdestructΩ')
    end.
    rewrite 2!Cmult_if_if_1_l, 4!andb_true_r.
    apply f_equal_if; [|easy..].
    apply eq_iff_eq_true.
    rewrite 2!andb_true_iff, !Nat.eqb_eq, <- !funbool_to_nat_eq_iff.
    split.
    + intros [Hhigh Hlow].
      split.
      * intros k Hk.
        bdestruct (perm_inv n f (padl + 2 + k) <? padl).
        --generalize (Hlow (perm_inv n f (padl + 2 + k)) ltac:(easy)).
          intros ->.
          f_equal.
          unfold contract_perm.
          do 2 simplify_bools_lia_one_kernel.
          rewrite perm_inv_is_rinv_of_permutation, Hfpadl, HfSpadl 
            by easy + lia.
          bdestructΩ'.
        --assert (perm_inv n f (padl + 2 + k) <> padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          assert (perm_inv n f (padl + 2 + k) <> S padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          pose proof (perm_inv_bounded n f (padl + 2 + k)).
          generalize (Hhigh (perm_inv n f (padl + 2 + k) - (padl + 2)) 
            ltac:(lia)).
          rewrite Nat.add_sub_assoc, add_sub' by lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 4 simplify_bools_lia_one_kernel.
          replace (padl + 0 + (perm_inv n f (padl + 2 + k) 
            - (padl + 2)) + 1 + 1) with
            (perm_inv n f (padl + 2 + k)) by lia.
          rewrite perm_inv_is_rinv_of_permutation by easy + lia.
          bdestructΩ'.
      * intros k Hk.
        bdestruct (perm_inv n f k <? padl).
        --generalize (Hlow (perm_inv n f k) ltac:(easy)).
          intros ->.
          f_equal.
          unfold contract_perm.
          do 2 simplify_bools_lia_one_kernel.
          rewrite perm_inv_is_rinv_of_permutation, Hfpadl, HfSpadl 
            by easy + lia.
          bdestructΩ'.
        --assert (perm_inv n f k <> padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          assert (perm_inv n f k <> S padl) by
            (rewrite perm_inv_eq_iff by easy + lia; lia).
          pose proof (perm_inv_bounded n f k).
          generalize (Hhigh (perm_inv n f k - (padl + 2)) 
            ltac:(lia)).
          rewrite Nat.add_sub_assoc, add_sub' by lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 4 simplify_bools_lia_one_kernel.
          replace (padl + 0 + (perm_inv n f k
            - (padl + 2)) + 1 + 1) with
            (perm_inv n f k) by lia.
          rewrite perm_inv_is_rinv_of_permutation by easy + lia.
          bdestructΩ'.
    + intros [Hhigh Hlow].
      split.
      * intros k Hk.
        bdestruct (f (padl + 2 + k) <? padl).
        --generalize (Hlow (f (padl + 2 + k)) ltac:(easy)).
          rewrite perm_inv_is_linv_of_permutation by easy + lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 4 simplify_bools_lia_one_kernel.
          replace (padl+0+k+1+1) with (padl+2+k) by lia.
          bdestructΩ'.
        --assert (f (padl + 2 + k) <> padl) by 
            (pose proof (permutation_is_injective n f Hf 
              padl (padl + 2 + k)); lia).
          assert (f (padl + 2 + k) <> S padl) by 
            (pose proof (permutation_is_injective n f Hf 
              (S padl) (padl + 2 + k)); lia).
          pose proof (Hfbdd (padl + 2 + k) ltac:(lia)).
          generalize (Hhigh (f (padl + 2 + k) - (padl + 2)) ltac:(lia)).
          rewrite Nat.add_sub_assoc, add_sub' by lia.
          rewrite perm_inv_is_linv_of_permutation by easy + lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 4 simplify_bools_lia_one_kernel.
          replace (padl + 0 + k + 1 + 1) with (padl + 2 + k) by lia.
          bdestructΩ'.
      * intros k HK.
        bdestruct (f k <? padl).
        --generalize (Hlow (f k) ltac:(easy)).
          rewrite perm_inv_is_linv_of_permutation by easy + lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 5 simplify_bools_lia_one_kernel.
          bdestructΩ'.
        --assert (f k <> padl) by 
            (pose proof (permutation_is_injective n f Hf padl k); lia).
          assert (f k <> S padl) by 
            (pose proof (permutation_is_injective n f Hf (S padl) k); lia).
          pose proof (Hfbdd k ltac:(lia)).
          generalize (Hhigh (f k - (padl + 2)) ltac:(lia)).
          rewrite Nat.add_sub_assoc, add_sub' by lia.
          rewrite perm_inv_is_linv_of_permutation by easy + lia.
          intros ->.
          f_equal.
          unfold contract_perm.
          do 5 simplify_bools_lia_one_kernel.
          bdestructΩ'.
  - set (s := ⟦⊂⟧).
    unfold Mmult;
    simpl.
    replace (padl + 0) with (f padl) by lia. 
    replace (padl + 1) with (f (S padl)) by lia. 
    rewrite 2!perm_inv_is_linv_of_permutation by easy + lia.
    now rewrite Hfpadl, HfSpadl.
Qed.*)

(* TODO: Replace with general? *)
Lemma perm_to_matrix_cap_pullthrough_r {n f} (Hf : permutation n f) 
  padl (Hpadl : S padl < n) (HfSpadl : f (S padl) = S (f padl)) :
  @Mmult (2^n) (2^n) (2^(n-2)) (perm_to_matrix n f)
  ((I (2^ f padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + f padl)))) =
  @Mmult (2^n) (2^(n-2)) (2^(n-2))
  ((I (2^ padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm f (S padl)) padl)).
Proof.
  pose proof (permutation_is_bounded _ _ Hf) as Hfbdd.
  pose proof (Hfbdd padl ltac:(lia)).
  pose proof (Hfbdd (S padl) Hpadl).
  pose proof (perm_inv_bounded n f) as Hfinvbdd.
  pose proof (Hfinvbdd padl ltac:(lia)).
  pose proof (Hfinvbdd (S padl) Hpadl).
  replace (perm_to_matrix n f) with 
   (perm_to_matrix n (
    stack_perms (2 + f padl) (n - (2 + f padl))
      (rotr (2 + f padl) (f padl)) idn ∘
    stack_perms (2 + f padl) (n - (2 + f padl))
      (rotl (2 + f padl) (f padl)) idn
    ∘ f ∘
    stack_perms (2 + padl) (n - (2 + padl))
      (rotr (2 + padl) padl) idn ∘
    stack_perms (2 + padl) (n - (2 + padl))
      (rotl (2 + padl) padl) idn)) by
    (f_equal; cleanup_perm; rewrite compose_assoc; cleanup_perm).
  pose proof (fun g => proj1 (permutation_change_dims 
    (2 + f padl + (n - (2 + f padl))) n ltac:(lia) g)) as Hch1.
  pose proof (fun g => proj1 (permutation_change_dims 
    (2 + padl + (n - (2 + padl))) n ltac:(lia) g)) as Hch2.
  rewrite perm_to_matrix_compose by 
    (do 3 (try (apply compose_perm_bounded; [|auto with perm_db]));
    auto with perm_db).
  replace (perm_to_matrix n) with 
    (perm_to_matrix (2 + padl + (n - (2 + padl))))
     by (f_equal; lia).
  rewrite perm_to_matrix_of_stack_perms by auto with perm_db.
  rewrite <- rotr_inv', <- perm_to_matrix_transpose_eq'
    by auto with perm_db.
  rewrite Nat.add_comm.
  rewrite perm_to_matrix_rotr_eq_kron_comm.
  restore_dims.
  replace (@transpose (2 ^ (padl + 2)) (2 ^ (padl + 2)))
  with (@transpose (2^2 * 2 ^ (padl)) (2^(padl) * 2^2))
    by (f_equal; show_pow2_le).
  rewrite kron_comm_transpose, perm_to_matrix_idn.
  rewrite !compose_assoc.
  rewrite (Nat.add_comm (padl) 2).
  replace (perm_to_matrix (2 + padl + (n - (2 + padl)))) with
    (perm_to_matrix n) by (f_equal; lia).
  rewrite perm_to_matrix_compose by auto with perm_db.
  replace (perm_to_matrix n) with
    (perm_to_matrix (2 + f padl + (n - (2 + f padl))))
    by (f_equal; lia).
  rewrite perm_to_matrix_of_stack_perms by auto with perm_db.
  rewrite (Nat.add_comm 2 (f padl)).
  rewrite perm_to_matrix_rotr_eq_kron_comm, 
    perm_to_matrix_idn.
  rewrite !Mmult_assoc.
  restore_dims.
  rewrite Mmult_assoc.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite Mmult_1_r, kron_comm_commutes_l by auto with wf_db.
  rewrite kron_comm_1_l.
  restore_dims.
  rewrite Mmult_1_r by auto with wf_db.
  rewrite (Nat.add_comm (f padl) 2).
  replace (perm_to_matrix (2 + padl + (n - (2 + padl)))) with
    (perm_to_matrix n) by (f_equal; lia).
  assert (Hpeq : perm_eq 2 
    ((stack_perms (2 + f padl) (n - (2 + f padl))
    (rotl (2 + f padl) (f padl)) idn ∘ (f
     ∘ stack_perms (2 + padl) (n - (2 + padl))
         (rotr (2 + padl) padl) idn))) idn).
  1:{
    rewrite <- compose_assoc.
    intros k Hk.
    rewrite rotr_add_r_eq.
      unfold compose at 1.
      rewrite stack_perms_left by lia.
      rewrite rotl_eq_rotr_sub, Nat.mod_small, Nat.add_sub by lia.
      unfold compose at 1.
      replace_bool_lia (2 + padl <=? k) false.
      replace_bool_lia (k <? 2) true.
      rewrite stack_perms_left by (destruct k as [|[]]; simpl; lia).
      rewrite rotr_add_l_eq.
      destruct k; [|replace k with 0 by lia];
      simpl Nat.add; bdestructΩ'.
  }
  pose proof ((fun G => perm_eq_of_small_eq_idn 2 n 
    _ ltac:(lia) G Hpeq) ltac:(auto with perm_db)) as Hrw.
  replace (perm_to_matrix (2 + f padl + (n - (2 + f padl))))
    with (perm_to_matrix n) by (f_equal; lia).
  rewrite (perm_to_matrix_eq_of_perm_eq _ _ _ Hrw).
  replace (perm_to_matrix n) 
    with (perm_to_matrix (2 + (n - 2))) by (f_equal; lia).
  rewrite perm_to_matrix_of_stack_perms; [|auto with perm_db|
  apply perm_shift_permutation_of_small_eq_idn; auto with perm_db zarith].
  rewrite kron_assoc, id_kron, 
    <- (Nat.pow_add_r 2 (f padl)) by auto with wf_db.
  replace (f padl + (n - (2 + f padl))) with (n - 2) by lia.
  rewrite perm_to_matrix_idn.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite <- Mmult_1_comm, Mmult_1_comm by auto with wf_db.
  rewrite <- kron_mixed_product.
  replace (I (2 ^ (n - 2))) with (I (2 ^ (padl + (n - (2 + padl)))))
    by (do 2 f_equal; lia).
  rewrite (Nat.pow_add_r 2 (padl)), <- id_kron.
  restore_dims.
  rewrite <- kron_assoc by auto with wf_db.
  restore_dims.
  rewrite <- Mmult_assoc.
  rewrite kron_mixed_product.
  rewrite kron_comm_commutes_l, kron_comm_1_r by auto with wf_db.
  restore_dims.
  rewrite 2!Mmult_1_r by auto with wf_db.
  rewrite kron_1_l by auto with wf_db.
  restore_dims.
  f_equal.
  apply perm_to_matrix_eq_of_perm_eq.
  intros k Hk.
  rewrite <- compose_assoc.
  rewrite rotl_eq_rotr_sub, Nat.mod_small, Nat.add_sub by lia.
  unfold compose at 1.
  unfold contract_perm at 1.
  replace (contract_perm f (S padl) padl) with (f padl) 
    by (unfold contract_perm; bdestructΩ').
  Local Arguments Nat.add : simpl never.
  bdestruct (k <? padl).
  - rewrite stack_perms_left by lia.
    rewrite rotr_add_r_eq.
    do 2 simplify_bools_lia_one_kernel.
    rewrite Nat.add_sub.
    assert (f k <> f padl) by (intros Heq; 
      apply (permutation_is_injective n f Hf) in Heq; lia).
    assert (f k <> f (S padl) ) by (intros Heq; 
      apply (permutation_is_injective n f Hf) in Heq; lia).
    unfold compose.
    bdestruct (f k <? f padl).
    + rewrite stack_perms_left by lia.
      rewrite rotr_add_l_eq.
      do 2 simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub.
      unfold contract_perm.
      bdestructΩ'.
    + pose proof (Hfbdd k ltac:(lia)).
      rewrite stack_perms_right by lia.
      unfold contract_perm; bdestructΩ'.
  - rewrite stack_perms_right by lia.
    rewrite Nat.sub_add by lia.
    unfold compose.
    assert (f (k + 2) <> f padl) by (intros Heq; 
      apply (permutation_is_injective n f Hf) in Heq; lia).
    assert (f (k + 2) <> f (S padl) ) by (intros Heq; 
      apply (permutation_is_injective n f Hf) in Heq; lia).
    bdestruct (f (k + 2) <? f padl).
    + rewrite stack_perms_left by lia.
      rewrite rotr_add_l_eq.
      do 2 simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub.
      unfold contract_perm at 1.
      simplify_bools_lia_one_kernel.
      unfold contract_perm.
      replace (k + 1 + 1) with (k + 2) by lia.
      bdestructΩ'.
    + pose proof (Hfbdd (k + 2) ltac:(lia)).
      rewrite stack_perms_right by lia.
      rewrite Nat.sub_add by lia.
      unfold contract_perm.
      replace (k + 1 + 1) with (k + 2) by lia.
      bdestructΩ'.
Qed.

Local Arguments Nat.add : simpl nomatch.

Lemma perm_to_matrix_cap_pullthrough_r_gen {n f} (Hf : permutation n f) 
  padl (Hpadl : S padl < n)
  (HfSpadl : perm_inv n f (S padl) = S (perm_inv n f padl)) :
  @Mmult (2^n) (2^n) (2^(n-2)) (perm_to_matrix n f)
  ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl)))) =
  @Mmult (2^n) (2^(n-2)) (2^(n-2))
  ((I (2^ perm_inv n  f padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + perm_inv n f padl))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm 
    f (S (perm_inv n f padl))) (perm_inv n f padl))).
Proof.
  pose proof (permutation_is_bounded n f Hf) as Hfbdd. 
  pose proof (Hfbdd padl ltac:(lia)).
  pose proof (perm_inv_bounded n f) as Hfinvbdd.
  replace ((2 ^ padl)) with ((2 ^ (f (perm_inv n f padl)))) by cleanup_perm.
  replace ((2 ^ (n - (2 + padl)))) with 
    ((2 ^ (n - (2 + f (perm_inv n f padl))))) by cleanup_perm.
  
  apply perm_to_matrix_cap_pullthrough_r; [auto |..].
  - pose proof (Hfinvbdd (S padl) Hpadl). 
    lia.
  - rewrite <- HfSpadl.
    cleanup_perm.
Qed.

Lemma perm_to_matrix_cap_pullthrough_r_gen_alt {n f} (Hf : permutation n f) 
  padl padl_in (Hpadl : S padl < n) (Hpadl_in : S padl_in < n)
  (Hfpadl : f padl_in = padl)
  (HfSpadl : f (S padl_in) = S padl) :
  @Mmult (2^n) (2^n) (2^(n-2)) (perm_to_matrix n f)
  ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl)))) =
  @Mmult (2^n) (2^(n-2)) (2^(n-2))
  ((I (2^ padl_in) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl_in))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm 
    f (S padl_in)) padl_in)).
Proof.
  replace (S padl_in) with (perm_inv n f (S padl)) by
    (rewrite perm_inv_eq_iff; cleanup_perm).
  replace padl_in with (perm_inv n f padl) by
    (rewrite perm_inv_eq_iff; cleanup_perm).
  assert (Hkey : perm_inv n f (S padl) = S (perm_inv n f padl)). 
  1: {
    rewrite <- HfSpadl.
    cleanup_perm.
    f_equal.
    symmetry.
    rewrite perm_inv_eq_iff; cleanup_perm.
  }
  rewrite perm_to_matrix_cap_pullthrough_r_gen; [|easy..].
  f_equal.
  now rewrite Hkey.
Qed.

Lemma perm_to_matrix_cap_pullthrough_r_gen_alt_swapped 
  {n f} (Hf : permutation n f) 
  padl padl_in (Hpadl : S padl < n) (Hpadl_in : S padl_in < n)
  (Hfpadl : f padl_in = S padl)
  (HfSpadl : f (S padl_in) = padl) :
  @Mmult (2^n) (2^n) (2^(n-2)) (perm_to_matrix n f)
  ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl)))) =
  @Mmult (2^n) (2^(n-2)) (2^(n-2))
  ((I (2^ padl_in) ⊗ ⟦⊂⟧) ⊗ I (2^(n-(2 + padl_in))))
  (perm_to_matrix (n - 2) (contract_perm (contract_perm 
    f (S padl_in)) padl_in)).
Proof.
  replace (perm_to_matrix n f) with 
    (perm_to_matrix n 
      (swap_perm padl (S padl) n ∘ swap_perm padl (S padl) n ∘ f))
    by (f_equal; cleanup_perm).
  rewrite compose_assoc.
  rewrite perm_to_matrix_compose by auto with perm_db.
  restore_dims.
  rewrite perm_to_matrix_swap_perm_S by easy.
  rewrite Mmult_assoc.
  change (2*2) with (2^2).
  rewrite (fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z) by
    (rewrite <- ?Nat.pow_add_r; f_equal; lia).
  rewrite kron_mixed_product.
  rewrite 2!Mmult_1_l by auto with wf_db.
  change (2^2) with (2*2).
  rewrite swap_cup.
  pose proof ((fun H => @perm_to_matrix_cap_pullthrough_r_gen_alt n
    (swap_perm padl (S padl) n ∘ f) H padl padl_in)
    ltac:(auto with perm_db)
    ltac:(lia) ltac:(lia)
    ltac:(unfold compose; rewrite Hfpadl, swap_perm_right; lia)
    ltac:(unfold compose; rewrite HfSpadl, swap_perm_left; lia)) as e.
  restore_dims in e.
  restore_dims.
  rewrite e.
  f_equal.
  apply perm_to_matrix_eq_of_perm_eq.
  intros k Hk.
  unfold contract_perm at 1 3.
  assert (HcSp : contract_perm (swap_perm padl (S padl) n ∘ f) 
    (S padl_in) padl_in = padl) by
    (unfold contract_perm, compose;
    rewrite Hfpadl, HfSpadl, swap_perm_left, swap_perm_right by lia;
    bdestructΩ').
  assert (Hcp : contract_perm (f) (S padl_in) padl_in = padl) by
    (unfold contract_perm; 
    rewrite Hfpadl, HfSpadl;
    bdestructΩ').
  rewrite HcSp, Hcp.
  bdestruct (k <? padl_in).
  - unfold contract_perm.
    simplify_bools_lia_one_kernel.
    unfold compose.
    rewrite HfSpadl, swap_perm_left by lia.
    assert (f k <> padl) by (intros HF; 
      rewrite <- HfSpadl in HF;
      generalize (f_equal (perm_inv n f) HF);
      cleanup_perm; lia).
    assert (f k <> S padl) by (intros HF; 
      rewrite <- Hfpadl in HF;
      generalize (f_equal (perm_inv n f) HF);
      cleanup_perm; lia).
    rewrite swap_perm_neither by lia.
    bdestructΩ'.
  - assert (f (k + 1 + 1) <> S padl) by (intros HF; 
      rewrite <- Hfpadl in HF;
      generalize (f_equal (perm_inv n f) HF);
      cleanup_perm; lia).
    assert (f (k + 1 + 1) <> padl) by (intros HF; 
      rewrite <- HfSpadl in HF;
      generalize (f_equal (perm_inv n f) HF);
      cleanup_perm; lia).
    unfold contract_perm.
    simplify_bools_lia_one_kernel.
    unfold compose.
    rewrite HfSpadl.
    rewrite swap_perm_left, swap_perm_neither by lia.
    bdestructΩ'.
Qed.





Lemma lperm_prep_compose_cap_NF_l_permutation lperm rperm nid ncup ncap padl 
  (Hpadl : S padl < ncup + ncup + nid) 
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  permutation (ncup + ncup + nid) 
  (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  (* pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd. *)
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ lperm').
  unfold lperm'.
  pose proof (stack_perms_WF_idn (ncup + ncup) nid) as mkWF.
  rewrite <- (mkWF (tensor_perms ncup 2 (swap_perm 0 (perm_inv 
    (ncup + ncup + nid) lperm padl / 2) ncup) idn)) by cleanup_perm.
  rewrite <- (mkWF (tensor_perms ncup 2 (swap_2_to_2_perm 0 1
       (perm_inv (ncup + ncup + nid) lperm padl / 2)
       (perm_inv (ncup + ncup + nid) lperm (S padl) / 2) ncup) idn)) 
       by cleanup_perm.
  rewrite <- (mkWF (swap_perm 0 1 (ncup + ncup))) by cleanup_perm.
  rewrite <- (mkWF (swap_perm 2 3 (ncup + ncup))) by cleanup_perm.
  rewrite <- (mkWF (swap_perm (ncup + ncup - 2) (ncup + ncup - 1)
    (ncup + ncup))) by cleanup_perm.
  bdestruct (perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup);
    [assert (perm_inv (ncup + ncup + nid) lperm padl / 2 < ncup)   
    by (apply Nat.Div0.div_lt_upper_bound; lia)|];
  (bdestruct (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup); 
    [assert (perm_inv (ncup + ncup + nid) lperm (S padl) / 2 < ncup) 
    by (apply Nat.Div0.div_lt_upper_bound; lia)|]);
  cbn [andb];
  bdestructΩ'; auto 10 with perm_db zarith.
Qed.

#[export] Hint Resolve lperm_prep_compose_cap_NF_l_permutation : perm_db.

Lemma prep_compose_cap_NF_l_case_2_pull lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm padl)  
  (HSpadl :  ncup + ncup <= perm_inv (ncup + ncup + nid) lperm (S padl)) 
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  (* lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup) = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup + 1) = S padl. *)
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2))
    (perm_to_matrix (ncup + ncup + nid) 
    (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)))
    ((I (2^padl) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - (2 + padl)))) =
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2)) (2^(ncup+ncup+nid-2))
  ((I (2 ^ (ncup + ncup)) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (nid - 2))) 
  (perm_to_matrix (ncup + ncup + nid - 2) 
    (contract_perm (contract_perm 
      (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl))
      (ncup + ncup + 1)) (ncup + ncup))).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  rewrite (fun H => perm_to_matrix_cap_pullthrough_r_gen_alt H _ (ncup + ncup));
  [|auto with perm_db|lia|lia|
  replace (S (ncup + ncup)) with (ncup + ncup + 1) by lia;
  now apply prep_compose_cap_NF_l_case_2..].
  do 2 f_equal; repeat (f_equal; try lia).
Qed.

Lemma prep_compose_cap_NF_l_case_3_2_pull lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm padl)  
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  (* lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup - 1) = S padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup) = padl. *)
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2))
    (perm_to_matrix (ncup + ncup + nid) 
    (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)))
    ((I (2^padl) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - (2 + padl)))) =
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2)) (2^(ncup+ncup+nid-2))
  ((I (2 ^ (ncup + ncup - 1)) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (nid - 1))) 
  (perm_to_matrix (ncup + ncup + nid - 2) 
    (contract_perm (contract_perm 
      (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl))
      (ncup + ncup)) (ncup + ncup - 1))).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  rewrite (fun H => perm_to_matrix_cap_pullthrough_r_gen_alt_swapped 
    H _ (ncup + ncup - 1));
  [|auto with perm_db|lia|lia|
  replace (S (ncup + ncup - 1)) with (ncup + ncup) by lia;
  now apply prep_compose_cap_NF_l_case_3_2..].
  do 2 f_equal; repeat (f_equal; try lia).
Qed.

Lemma prep_compose_cap_NF_l_case_3_1_pull lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : ncup + ncup <= perm_inv (ncup + ncup + nid) lperm (S padl))  
  (Hlperm : permutation (ncup + ncup + nid) lperm) :
  (* lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 
    (ncup + ncup - 1) = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)
    (ncup + ncup) = S padl. *)
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2))
    (perm_to_matrix (ncup + ncup + nid) 
    (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)))
    ((I (2^padl) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - (2 + padl)))) =
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2)) (2^(ncup+ncup+nid-2))
  ((I (2 ^ (ncup + ncup - 1)) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (nid - 1))) 
  (perm_to_matrix (ncup + ncup + nid - 2) 
    (contract_perm (contract_perm 
      (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl))
      (ncup + ncup)) (ncup + ncup - 1))).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  rewrite (fun H => perm_to_matrix_cap_pullthrough_r_gen_alt
    H _ (ncup + ncup - 1));
  [|auto with perm_db|lia|lia|
  replace (S (ncup + ncup - 1)) with (ncup + ncup) by lia;
  now apply prep_compose_cap_NF_l_case_3_1..].
  do 2 f_equal; repeat (f_equal; try lia).
Qed.


Lemma prep_compose_cap_NF_l_case_1_2_pull lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hdiff : perm_inv (ncup + ncup + nid) lperm padl / 2 <> 
    perm_inv (ncup + ncup + nid) lperm (S padl) / 2) 
  (Hlperm : permutation (ncup + ncup + nid) lperm):
  (* lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 1 = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 2 = S padl. *)
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2))
    (perm_to_matrix (ncup + ncup + nid) 
    (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)))
    ((I (2^padl) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - (2 + padl)))) =
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2)) (2^(ncup+ncup+nid-2))
  ((I (2 ^ 1) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - 3))) 
  (perm_to_matrix (ncup + ncup + nid - 2) 
    (contract_perm (contract_perm 
      (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl))
      2) 1)).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  pose proof (diff_divs_lower_bound 
    (perm_inv (ncup + ncup + nid) lperm padl)
    (perm_inv (ncup + ncup + nid) lperm (S padl))
    2 (ncup + ncup) ltac:(easy) ltac:(easy) ltac:(easy)).
  rewrite (fun H => perm_to_matrix_cap_pullthrough_r_gen_alt
    H _ (1));
  [|auto with perm_db|lia|lia|
  now apply prep_compose_cap_NF_l_case_1_2..].
  do 2 f_equal; repeat (f_equal; try lia).
Qed.


Lemma prep_compose_cap_NF_l_case_1_1_pull lperm rperm nid ncup ncap padl 
  (Hsmall : S padl < ncup + ncup + nid)
  (Hpadl : perm_inv (ncup + ncup + nid) lperm padl < ncup + ncup) 
  (HSpadl : perm_inv (ncup + ncup + nid) lperm (S padl) < ncup + ncup) 
  (Hsame : perm_inv (ncup + ncup + nid) lperm padl / 2 = 
    perm_inv (ncup + ncup + nid) lperm (S padl) / 2) 
  (Hlperm : permutation (ncup + ncup + nid) lperm):
  (* lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 0 = padl /\
  lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) 1 = S padl. *)
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2))
    (perm_to_matrix (ncup + ncup + nid) 
    (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)))
    ((I (2^padl) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - (2 + padl)))) =
  @Mmult (2^(ncup+ncup+nid)) (2^(ncup+ncup+nid-2)) (2^(ncup+ncup+nid-2))
  ((I (2 ^ 0) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (ncup + ncup + nid - 2))) 
  (perm_to_matrix (ncup + ncup + nid - 2) 
    (contract_perm (contract_perm 
      (lperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl))
      1) 0)).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  (* pose proof (diff_divs_lower_bound 
    (perm_inv (ncup + ncup + nid) lperm padl)
    (perm_inv (ncup + ncup + nid) lperm (S padl))
    2 (ncup + ncup) ltac:(easy) ltac:(easy) ltac:(easy)). *)
  rewrite (fun H => perm_to_matrix_cap_pullthrough_r_gen_alt
    H _ 0);
  [|auto with perm_db|lia|lia|
  now apply prep_compose_cap_NF_l_case_1_1..].
  easy.
Qed.

(* FIXME: Move these towards the start *)
Definition contract_lperm_NF (b : NF_biperm) v : NF_biperm :=
  {|
    lperm' := contract_perm (lperm' b) v;
    rperm' := rperm' b;
    nid'   := nid' b;
    ncup'  := ncup' b;
    ncap'  := ncap' b;
  |}.

Definition dec_ncup_NF (b : NF_biperm) : NF_biperm :=
  {|
    lperm' := lperm' b;
    rperm' := rperm' b;
    nid'   := nid' b;
    ncup'  := ncup' b - 1;
    ncap'  := ncap' b;
  |}.

Definition dec_dec_nid_NF (b : NF_biperm) : NF_biperm :=
  {|
    lperm' := lperm' b;
    rperm' := rperm' b;
    nid'   := nid' b - 2;
    ncup'  := ncup' b;
    ncap'  := ncap' b;
  |}.


Definition incr_ncap_NF (b : NF_biperm) : NF_biperm :=
  {|
    lperm' := lperm' b;
    rperm' := rperm' b;
    nid'   := nid' b;
    ncup'  := ncup' b;
    ncap'  := 1 + ncap' b;
  |}.

Definition compose_cap_NF_l (lperm_init rperm : nat -> nat) 
  (nid ncup ncap padl : nat) :=
  let lperm := perm_inv (ncup + ncup + nid) lperm_init in
  if (lperm padl <? ncup + ncup) && (lperm (S padl) <? ncup + ncup) then
    (* First case, both in cups *)
    if lperm padl / 2 =? lperm (S padl) / 2 then
      (* First subcase, same cup *)
      dec_ncup_NF (contract_lperm_NF (contract_lperm_NF 
        (prep_compose_cap_NF_l lperm_init rperm nid ncup ncap padl)
        1) 0)
    else 
      (* Second subcase, different cups *)
    dec_ncup_NF (contract_lperm_NF (contract_lperm_NF 
      (prep_compose_cap_NF_l lperm_init rperm nid ncup ncap padl)
      2) 1)
  else if (lperm padl <? ncup + ncup) (* && (lperm (S padl) <? ncup + ncup) *) then
    (* Third case, first orientation (first leg in cup) *)
    dec_ncup_NF (contract_lperm_NF (contract_lperm_NF 
      (prep_compose_cap_NF_l lperm_init rperm nid ncup ncap padl)
      (ncup + ncup)) (ncup + ncup - 1))
  else if (* (lperm padl <? ncup + ncup) && *) (lperm (S padl) <? ncup + ncup) then
    (* Third case, second orientation (second leg in cup) *)
    dec_ncup_NF (contract_lperm_NF (contract_lperm_NF 
      (prep_compose_cap_NF_l lperm_init rperm nid ncup ncap padl)
      (ncup + ncup)) (ncup + ncup - 1))
  else (* if (lperm padl <? ncup + ncup) && (lperm (S padl) <? ncup + ncup) then *)
    (* Second case, both legs in ids *)
    incr_ncap_NF (dec_dec_nid_NF (contract_lperm_NF (contract_lperm_NF 
      (prep_compose_cap_NF_l lperm_init rperm nid ncup ncap padl)
      (ncup + ncup + 1)) (ncup + ncup))).

Lemma dec_contract_contract_WF (b : NF_biperm) (Hb : WF_NF_biperm b) 
  v v' (Hv : v < ncup' b + ncup' b + nid' b) 
  (Hv' : v' < ncup' b + ncup' b + nid' b - 1) 
  (Hncup' : ncup' b <> 0) : 
  WF_NF_biperm (dec_ncup_NF (contract_lperm_NF (contract_lperm_NF b v) v')).
Proof.
  unfold WF_NF_biperm in *. simpl. 
  split; [|easy].
  replace (ncup' b - 1 + (ncup' b - 1) + nid' b) with 
    (ncup' b + ncup' b + nid' b - 1 - 1) by lia.
  apply contract_perm_permutation; [|easy].
  apply contract_perm_permutation; easy.
Qed.

Lemma incr_dec_dec_contract_contract_WF (b : NF_biperm) (Hb : WF_NF_biperm b) 
  v v' (Hv : v < ncup' b + ncup' b + nid' b) 
  (Hv' : v' < ncup' b + ncup' b + nid' b - 1) 
  (Hnid' : 1 < nid' b) : 
  WF_NF_biperm (
    incr_ncap_NF (dec_dec_nid_NF 
      (contract_lperm_NF (contract_lperm_NF b v) v'))).
Proof.
  unfold WF_NF_biperm in *. simpl.
  split.
  - replace (ncup' b + ncup' b + (nid' b - 2)) with 
      (ncup' b + ncup' b + nid' b - 1 - 1) by lia.
    apply contract_perm_permutation; [|easy].
    apply contract_perm_permutation; easy.
  - replace (S (ncap' b + S (ncap' b) + (nid' b - 2))) with 
      (ncap' b + ncap' b + nid' b) by lia.
    easy.
Qed.

Lemma nid_prep_compose_cap_NF_l lperm rperm nid ncup ncap padl : 
  nid' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) = nid.
Proof.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ nid').
  simpl.
  now rewrite !Tauto.if_same.
Qed.

Lemma ncup_prep_compose_cap_NF_l lperm rperm nid ncup ncap padl : 
  ncup' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) = ncup.
Proof.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ ncup').
  simpl.
  now rewrite !Tauto.if_same.
Qed.

Lemma ncap_prep_compose_cap_NF_l lperm rperm nid ncup ncap padl : 
  ncap' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl) = ncap.
Proof.
  unfold prep_compose_cap_NF_l.
  rewrite !(if_dist _ _ _ ncap').
  simpl.
  now rewrite !Tauto.if_same.
Qed.

Lemma rperm_prep_compose_cap_NF_l_permutation lperm rperm nid ncup ncap padl 
  (Hpadl : S padl < ncup + ncup + nid)
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) : 
  permutation (ncap + ncap + nid) 
  (rperm' (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl)).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  unfold prep_compose_cap_NF_l; 
  rewrite !(if_dist _ _ _ rperm'); simpl.
  bdestructΩ'; auto with perm_db zarith.
Qed.

#[export] Hint Resolve rperm_prep_compose_cap_NF_l_permutation : perm_db.

Lemma prep_compose_cap_NF_l_WF (lperm rperm : nat -> nat) 
  (nid ncup ncap padl : nat) (Hpadl : S padl < ncup + ncup + nid)
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  WF_NF_biperm (prep_compose_cap_NF_l lperm rperm nid ncup ncap padl).
Proof.
  split;
  rewrite ?nid_prep_compose_cap_NF_l, 
    ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
    auto with perm_db zarith.
Qed.

(* TODO: Can the cases at the end of this lemma use the preceding lemma? *)
Lemma compose_cap_NF_l_WF (lperm rperm : nat -> nat) 
  (nid ncup ncap padl : nat) (Hpadl : S padl < ncup + ncup + nid)
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) :
  WF_NF_biperm (compose_cap_NF_l lperm rperm nid ncup ncap padl).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  unfold compose_cap_NF_l.
  bdestruct (perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup);
    [assert (perm_inv (ncup + ncup + nid) lperm padl / 2 < ncup)   
    by (apply Nat.Div0.div_lt_upper_bound; lia)|];
  (bdestruct (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup); 
    [assert (perm_inv (ncup + ncup + nid) lperm (S padl) / 2 < ncup) 
    by (apply Nat.Div0.div_lt_upper_bound; lia)|]);
  cbn [andb];
  [bdestruct (perm_inv (ncup + ncup + nid) lperm padl / 2 
    =? perm_inv (ncup + ncup + nid) lperm (S padl) / 2)|..].
  - apply dec_contract_contract_WF; [split|..];
    rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
      auto with perm_db zarith.
  - apply dec_contract_contract_WF; [split|..];
    rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
      auto with perm_db zarith.
  - apply dec_contract_contract_WF; [split|..];
    rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
      auto with perm_db zarith.
  - apply dec_contract_contract_WF; [split|..];
    rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
      auto with perm_db zarith.
  - apply incr_dec_dec_contract_contract_WF; [split|..];
    rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
      auto with perm_db zarith.
Qed.

Lemma compose_cap_NF_l_correct {lperm rperm} {nid ncup ncap} 
  (Hlperm : permutation (ncup + ncup + nid) lperm)
  (Hrperm : permutation (ncap + ncap + nid) rperm) 
  padl (Hpadl : S padl < ncup + ncup + nid) : 
  matrix_of_biperm (ncup + ncup + nid) (ncap + ncap + nid)
    (realize_biperm_data lperm rperm nid ncup ncap)
  × ((I (2^padl) ⊗ ⟦⊂⟧) ⊗ I (2^(ncup + ncup + nid - (2 + padl)))) 
  [∝]
  matrix_of_biperm (ncup + ncup + nid - 2) (ncap + ncap + nid)
    (realize_NF_biperm 
      (compose_cap_NF_l lperm rperm nid ncup ncap padl)).
Proof.
  pose proof (perm_inv_permutation _ _ Hlperm) as Hlinv.
  pose proof (permutation_is_bounded _ _ Hlperm) as Hlbdd.
  pose proof (permutation_is_bounded _ _ Hrperm) as Hrbdd.
  pose proof (permutation_is_injective _ _ Hlperm) as Hlinj.
  pose proof (permutation_is_bounded _ _ Hlinv) as Hlinvbdd.
  pose proof (permutation_is_injective _ _ Hlinv) as Hlinvinj.
  assert (Hlpadne : lperm padl <> lperm (S padl)) by 
    (pose proof (Hlinj padl (S padl)); lia).
  assert (Hlinvpadne : perm_inv (ncup+ncup+nid) lperm padl 
    <> perm_inv (ncup+ncup+nid) lperm (S padl)) by 
    (pose proof (Hlinvinj padl (S padl)); lia).
  pose proof (Hlbdd padl ltac:(lia)).
  pose proof (Hlbdd (S padl) ltac:(lia)).
  pose proof (Hlinvbdd padl ltac:(lia)).
  pose proof (Hlinvbdd (S padl) ltac:(lia)).
  set (cval := if 
  (perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup) && 
  (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup) &&
  (perm_inv (ncup + ncup + nid) lperm padl / 2 
    =? perm_inv (ncup + ncup + nid) lperm (S padl) / 2)
  then 2%R else 1%R
  ).
  exists cval.
  split; [|unfold cval; match goal with 
  |- context[if ?b then _ else _] => destruct b end; 
  auto using C2_nonzero, C1_nonzero].
  rewrite <- (prep_compose_cap_NF_l_correct lperm rperm nid ncup ncap padl)
    by easy.
  rewrite (matrix_of_realize_NF_biperm' (ncup+ncup+nid) (ncap+ncap+nid));
  [|now rewrite ?nid_prep_compose_cap_NF_l, 
    ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l..|
    now apply prep_compose_cap_NF_l_WF].
  rewrite (matrix_of_realize_NF_biperm' (ncup+ncup+nid-2) (ncap+ncap+nid));
  [| 
    unfold compose_cap_NF_l;
    rewrite !(if_dist NF_biperm nat);
    simpl; rewrite ?nid_prep_compose_cap_NF_l, 
      ?ncup_prep_compose_cap_NF_l, ?ncap_prep_compose_cap_NF_l;
    bdestructΩ'..
  | now apply compose_cap_NF_l_WF].
  
  rewrite nid_prep_compose_cap_NF_l, 
    ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
  pattern (compose_cap_NF_l lperm rperm nid ncup ncap padl).
  match goal with 
  |- ?P ?x => set (Pred := P)
  end.
  unfold compose_cap_NF_l.
  bdestruct (perm_inv (ncup + ncup + nid) lperm padl <? ncup + ncup);
    [assert (perm_inv (ncup + ncup + nid) lperm padl / 2 < ncup)   
    by (apply Nat.Div0.div_lt_upper_bound; lia)|];
  (bdestruct (perm_inv (ncup + ncup + nid) lperm (S padl) <? ncup + ncup); 
    [assert (perm_inv (ncup + ncup + nid) lperm (S padl) / 2 < ncup) 
    by (apply Nat.Div0.div_lt_upper_bound; lia)|]);
  cbn [andb];
  [bdestruct (perm_inv (ncup + ncup + nid) lperm padl / 2 
    =? perm_inv (ncup + ncup + nid) lperm (S padl) / 2)|..].
  - unfold Pred.
    cbn -[ZX_semantics].
    rewrite 2!Mmult_assoc.
    rewrite prep_compose_cap_NF_l_case_1_1_pull by easy.

    rewrite nid_prep_compose_cap_NF_l, 
      ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
    restore_dims.
    rewrite <- Mscale_mult_dist_l, <- Mscale_mult_dist_r.
    rewrite Mmult_assoc.
    restore_dims.
    f_equal; [f_equal; lia|].
    rewrite kron_1_l by auto with wf_db.
    restore_dims.
    replace (2^(ncup + ncup) * 2 ^ nid) with (2^2 * 2 ^ (ncup+ncup+nid-2)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- Mmult_assoc.
    restore_dims.
    f_equal; [rewrite <- ?Nat.pow_add_r; f_equal; lia.. | | f_equal; lia].
    replace (2^(ncup+ncup+nid-2)) with (2^(ncup+ncup-2)*(2^nid)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- id_kron, <- kron_assoc by auto with wf_db.
    restore_dims.
    rewrite kron_mixed_product' by (rewrite <- ?Nat.pow_add_r; f_equal; lia).
    rewrite Mmult_1_l by auto with wf_db.
    rewrite <- Mscale_kron_dist_l.
    f_equal; [rewrite <- !Nat.pow_add_r; f_equal; lia|].
    apply n_m_cup_cap_times_cup_r; lia.
  - unfold Pred.
    cbn -[ZX_semantics].
    rewrite 2!Mmult_assoc.
    rewrite prep_compose_cap_NF_l_case_1_2_pull by easy.
    rewrite nid_prep_compose_cap_NF_l, 
      ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
    restore_dims.
    rewrite Mscale_1_l.
    rewrite Mmult_assoc.
    restore_dims.
    f_equal; [f_equal; lia|].
    replace (2^(ncup + ncup) * 2 ^ nid) with (2^1*2^2*2^(ncup+ncup+nid-3)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- Mmult_assoc.
    restore_dims.
    f_equal; [rewrite <- ?Nat.pow_add_r; f_equal; lia.. | | f_equal; lia].
    replace (2^(ncup+ncup+nid-3)) with (2^(ncup+ncup-3)*(2^nid)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- id_kron, <- kron_assoc by auto with wf_db.
    restore_dims.
    rewrite kron_mixed_product' by (rewrite <- ?Nat.pow_add_r; f_equal; lia).
    rewrite Mmult_1_l by auto with wf_db.
    f_equal; [rewrite <- !Nat.pow_add_r; f_equal; lia|].
    apply n_m_cup_cap_times_up_cup_r; lia.
  - unfold Pred.
    cbn -[ZX_semantics].
    rewrite Mscale_1_l.
    rewrite 2!Mmult_assoc.
    rewrite prep_compose_cap_NF_l_case_3_1_pull by easy.
    rewrite nid_prep_compose_cap_NF_l, 
      ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
    restore_dims.
    rewrite Mmult_assoc.
    restore_dims.
    f_equal; [f_equal; lia|].
    replace (2^(ncup + ncup) * 2 ^ nid) with (2^(ncup+ncup-1)*2^2*2^(nid-1)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- Mmult_assoc.
    restore_dims.
    f_equal; [rewrite <- ?Nat.pow_add_r; f_equal; lia.. | | f_equal; lia].
    apply n_m_cup_cap_yank_one_r; lia.
  - unfold Pred.
    cbn -[ZX_semantics].
    rewrite Mscale_1_l.
    rewrite 2!Mmult_assoc.
    rewrite prep_compose_cap_NF_l_case_3_2_pull by easy.
    rewrite nid_prep_compose_cap_NF_l, 
      ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
    restore_dims.
    rewrite Mmult_assoc.
    restore_dims.
    f_equal; [f_equal; lia|].
    replace (2^(ncup + ncup) * 2 ^ nid) with (2^(ncup+ncup-1)*2^2*2^(nid-1)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- Mmult_assoc.
    restore_dims.
    f_equal; [rewrite <- ?Nat.pow_add_r; f_equal; lia.. | | f_equal; lia].
    apply n_m_cup_cap_yank_one_r; lia.
  - unfold Pred.
    cbn -[ZX_semantics Nat.add].
    rewrite Mscale_1_l.
    rewrite 2!Mmult_assoc.
    rewrite prep_compose_cap_NF_l_case_2_pull by easy.
    rewrite nid_prep_compose_cap_NF_l, 
      ncup_prep_compose_cap_NF_l, ncap_prep_compose_cap_NF_l.
    restore_dims.
    rewrite Mmult_assoc.
    f_equal; [f_equal; lia..|].
    rewrite kron_assoc by auto with wf_db.
    replace (2^(ncup + ncup) * 2 ^ nid) with (2^(ncup+ncup)*2^2*2^(nid-2)) by 
      (rewrite <- !Nat.pow_add_r; f_equal; lia).
    rewrite <- Mmult_assoc.
    restore_dims.
    f_equal; [rewrite <- ?Nat.pow_add_r; f_equal; lia.. | | f_equal; lia].
    replace (2 ^ nid) with (2 ^ 2 * 2 ^ (nid - 2))
      by (rewrite <- Nat.pow_add_r; f_equal; lia).
    rewrite <- id_kron.
    rewrite <- !kron_assoc by auto with wf_db.
    restore_dims.
    rewrite kron_mixed_product, Mmult_1_r by auto with wf_db.
    f_equal; [rewrite <- Nat.pow_add_r; f_equal; lia..|].
    rewrite kron_mixed_product, Mmult_1_r, Mmult_1_l by auto with wf_db.
    replace (n_m_cup_cap ncup (1 + ncap)) with 
      (n_m_cup_cap (0 + ncup) (1 + ncap)) by (f_equal; lia).
    rewrite (n_m_cup_cap_comm (_ + _)), n_m_cup_cap_plus_plus_decomp.
    replace (matrix_of_biperm (ncup + ncup) (1 + ncap + (1 + ncap)))
      with (matrix_of_biperm ((0 + 0) + (ncup + ncup)) ((1 + 1) + (ncap + ncap)))
      by (f_equal; lia).
    rewrite matrix_of_stack_biperms by auto with biperm_db.
    f_equal; [now rewrite n_m_cup_cap_comm|].
    rewrite matrix_of_biperm_n_m_cup_cap_0_l.
    now rewrite kron_n_1 by auto with wf_db.
Qed.

Fixpoint compose_n_caps_NF_l (b : NF_biperm) (num_caps : nat) :=
  match num_caps with 
  | 0 => b
  | S k => 
    uncurry_NF_biperm compose_cap_NF_l (compose_n_caps_NF_l b k) 0
  end.

(* TODO: Replace with NF_insize, NF_outsize *)
Lemma ncup_ncup_nid_uncurry_compose_cap_NF_l (b : NF_biperm) 
  (Hb : WF_NF_biperm b) n (Hn : S n < ncup' b + ncup' b + nid' b) : 
  ncup' (uncurry_NF_biperm compose_cap_NF_l b n) + 
  ncup' (uncurry_NF_biperm compose_cap_NF_l b n) + 
  nid' (uncurry_NF_biperm compose_cap_NF_l b n) = 
  ncup' b + ncup' b + nid' b - 2.
Proof.
  destruct Hb.
  unfold uncurry_NF_biperm.
  unfold compose_cap_NF_l.
  rewrite !(if_dist NF_biperm nat).
  simpl.
  rewrite !Tauto.if_same.
  rewrite ncup_prep_compose_cap_NF_l, nid_prep_compose_cap_NF_l.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (S n) 
    < ncup' b + ncup' b + nid' b) by auto with perm_bounded_db.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (n) 
    < ncup' b + ncup' b + nid' b) by auto with perm_bounded_db.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (n) 
    <> perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (S n))
    by (intros Hfalse; 
    apply (permutation_is_injective (ncup' b + ncup' b + nid' b)) in Hfalse;
    auto with perm_db zarith).
  bdestructΩ'.
Qed.

Lemma ncap_ncap_nid_uncurry_compose_cap_NF_l (b : NF_biperm) 
  (Hb : WF_NF_biperm b) n (Hn : S n < ncup' b + ncup' b + nid' b) : 
  ncap' (uncurry_NF_biperm compose_cap_NF_l b n) + 
  ncap' (uncurry_NF_biperm compose_cap_NF_l b n) + 
  nid' (uncurry_NF_biperm compose_cap_NF_l b n) = 
  ncap' b + ncap' b + nid' b.
Proof.
  destruct Hb.
  unfold uncurry_NF_biperm.
  unfold compose_cap_NF_l.
  rewrite !(if_dist NF_biperm nat).
  simpl.
  rewrite !Tauto.if_same.
  rewrite ncap_prep_compose_cap_NF_l, nid_prep_compose_cap_NF_l.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (S n) 
    < ncup' b + ncup' b + nid' b) by auto with perm_bounded_db.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (n) 
    < ncup' b + ncup' b + nid' b) by auto with perm_bounded_db.
  assert (perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (n) 
    <> perm_inv (ncup' b + ncup' b + nid' b) (lperm' b) (S n))
    by (intros Hfalse; 
    apply (permutation_is_injective (ncup' b + ncup' b + nid' b)) in Hfalse;
    auto with perm_db zarith).
  bdestructΩ'.
Qed.

Lemma ncup_ncup_nid_ncap_ncap_nid_WF_compose_n_caps_NF_l (b : NF_biperm) 
  (Hb : WF_NF_biperm b) (num_caps : nat) 
  (Hnum_caps : num_caps + num_caps <= ncup' b + ncup' b + nid' b) :
  ncap' (compose_n_caps_NF_l b num_caps) + 
  ncap' (compose_n_caps_NF_l b num_caps) + 
  nid' (compose_n_caps_NF_l b num_caps) = 
  ncap' b + ncap' b + nid' b /\
  ncup' (compose_n_caps_NF_l b num_caps) + 
  ncup' (compose_n_caps_NF_l b num_caps) + 
  nid' (compose_n_caps_NF_l b num_caps) = 
  ncup' b + ncup' b + nid' b - (num_caps + num_caps)
  /\ WF_NF_biperm (compose_n_caps_NF_l b num_caps).
Proof.
  induction num_caps.
  - simpl; split; [|split]; [lia.. | easy].
  - simpl.
    destruct (IHnum_caps ltac:(lia)) as [Hcups HWF].
    rewrite ncup_ncup_nid_uncurry_compose_cap_NF_l, 
      ncap_ncap_nid_uncurry_compose_cap_NF_l by (easy + lia).
    repeat split; try lia;
    (apply compose_cap_NF_l_WF; [lia|apply HWF..]).
Qed.


Lemma compose_n_caps_NF_l_WF (b : NF_biperm) (num_caps : nat)
  (Hnum_caps : num_caps + num_caps <= ncup' b + ncup' b + nid' b) 
  (Hb : WF_NF_biperm b) :
  WF_NF_biperm (compose_n_caps_NF_l b num_caps).
Proof.
  now apply ncup_ncup_nid_ncap_ncap_nid_WF_compose_n_caps_NF_l.
Qed.

Lemma ncup_ncup_nid_compose_n_caps_NF_l (b : NF_biperm) (num_caps : nat)
  (Hnum_caps : num_caps + num_caps <= ncup' b + ncup' b + nid' b) 
  (Hb : WF_NF_biperm b) :
  ncup' (compose_n_caps_NF_l b num_caps) +
  ncup' (compose_n_caps_NF_l b num_caps) +
  nid' (compose_n_caps_NF_l b num_caps) = 
  ncup' b + ncup' b + nid' b - (num_caps + num_caps).
Proof.
  now apply ncup_ncup_nid_ncap_ncap_nid_WF_compose_n_caps_NF_l.
Qed.

Lemma ncap_ncap_nid_compose_n_caps_NF_l (b : NF_biperm) (num_caps : nat)
  (Hnum_caps : num_caps + num_caps <= ncup' b + ncup' b + nid' b) 
  (Hb : WF_NF_biperm b) :
  ncap' (compose_n_caps_NF_l b num_caps) +
  ncap' (compose_n_caps_NF_l b num_caps) +
  nid' (compose_n_caps_NF_l b num_caps) = 
  ncap' b + ncap' b + nid' b.
Proof.
  now apply ncup_ncup_nid_ncap_ncap_nid_WF_compose_n_caps_NF_l.
Qed.



Lemma uncurry_compose_cap_NF_l_correct (b : NF_biperm) 
  (Hb : WF_NF_biperm b) (padl : nat) 
  (Hpadl : S padl < ncup' b + ncup' b + nid' b) : 
  (@Mmult _ _ (ncup' b + ncup' b + nid' b - 2)
  (matrix_of_NF_biperm b)
  (I (2 ^ padl) ⊗ (⟦ ⊂ ⟧)
    ⊗ I (2 ^ (ncup' b + ncup' b + nid' b - (2 + padl)))))
  [∝@ (2^(ncap' b + ncap' b + nid' b))
    (2^(ncup' b + ncup' b + nid' b - 2))] 
    matrix_of_NF_biperm (uncurry_NF_biperm compose_cap_NF_l b padl).
Proof.
  unfold matrix_of_NF_biperm.
  rewrite ncup_ncup_nid_uncurry_compose_cap_NF_l,
    ncap_ncap_nid_uncurry_compose_cap_NF_l by easy.
  unfold uncurry_NF_biperm.
  apply compose_cap_NF_l_correct; easy + apply Hb.
Qed.

(* Lemma uncurry_compose_cap_NF_l_correct_alt (b : NF_biperm) 
  (Hb : WF_NF_biperm b) (padl : nat) 
  (Hpadl : S padl < ncup' b + ncup' b + nid' b) : 
  (@Mmult _ _ (ncup' b + ncup' b + nid' b - 2)
  (matrix_of_NF_biperm b)
  (I (2 ^ padl) ⊗ (⟦ ⊂ ⟧)
    ⊗ I (2 ^ (ncup' b + ncup' b + nid' b - (2 + padl)))))
  [∝@ (2^(ncap' b + ncap' b + nid' b))
    (2^(ncup' b + ncup' b + nid' b - 2))] 
    matrix_of_NF_biperm (uncurry_NF_biperm compose_cap_NF_l b padl).
Proof.
  unfold matrix_of_NF_biperm.
  rewrite ncup_ncup_nid_uncurry_compose_cap_NF_l,
    ncap_ncap_nid_uncurry_compose_cap_NF_l by easy.
  unfold uncurry_NF_biperm.
  apply compose_cap_NF_l_correct; easy + apply Hb.
Qed. *)




Lemma compose_n_caps_NF_l_correct (b : NF_biperm) 
  (Hb : WF_NF_biperm b) (num_caps : nat) 
  (Hnum_caps : num_caps + num_caps <= ncup' b + ncup' b + nid' b) :
  @Mmult (2^(ncap' b + ncap' b + nid' b) )
    (2^((ncup' b + ncup' b + nid' b))) 
    (2^((ncup' b + ncup' b + nid' b - (num_caps + num_caps)))) 
    (matrix_of_NF_biperm b)
    ((matrix_of_biperm 0 (num_caps + num_caps) (n_m_cup_cap num_caps 0)
    ⊗ (I (2 ^ (ncup' b + ncup' b + nid' b - (num_caps + num_caps))))))
  [∝]
  matrix_of_NF_biperm (compose_n_caps_NF_l b num_caps).
Proof.
  induction num_caps.
  - simpl.
    rewrite matrix_of_biperm_0_0.
    rewrite id_kron.
    restore_dims.
    now rewrite Mmult_1_r by auto with wf_db.
  - cbn [compose_n_caps_NF_l]. 
    rewrite <- uncurry_compose_cap_NF_l_correct by
      ((apply compose_n_caps_NF_l_WF + 
        rewrite ncup_ncup_nid_compose_n_caps_NF_l); easy + lia).
    progress restore_dims.
    rewrite ncup_ncup_nid_compose_n_caps_NF_l, 
      ncap_ncap_nid_compose_n_caps_NF_l by easy + lia.
    rewrite <- IHnum_caps by lia.
    rewrite Mmult_assoc.
    rewrite kron_assoc by auto with wf_db.
    restore_dims.
    rewrite kron_mixed_product' by restore_dims_tac.
    rewrite Mmult_1_l, Mmult_1_r by auto with wf_db.
    restore_dims.
    replace (2 ^ (ncup' b + ncup' b + nid' b - 
      (num_caps + num_caps) - (2 + 0))) 
      with (2 ^ (ncup' b + ncup' b + nid' b - 
      (S num_caps + S num_caps))) by restore_dims_tac.
    rewrite !Nat.mul_1_l.
    apply Mmult_mat_prop_proper; [easy|].
    restore_dims.
    rewrite <- kron_assoc by auto with wf_db.
    now rewrite 2!(n_m_cup_cap_comm _ 0), 2!matrix_of_biperm_n_m_cup_cap_0_l.
Qed.

Definition compose_n_cups_NF_l (b : NF_biperm) (num_cups : nat) : NF_biperm :=
  {|
    lperm' := stack_perms (num_cups + num_cups) (NF_insize b) idn (lperm' b);
    rperm' := rperm' b;
    nid' := nid' b;
    ncup' := num_cups + ncup' b;
    ncap' := ncap' b;
  |}.

Lemma compose_n_cups_NF_l_WF b k (Hb : WF_NF_biperm b) : 
  WF_NF_biperm (compose_n_cups_NF_l b k).
Proof.
  split; [|apply Hb].
  simpl.
  rewrite double_add, <- Nat.add_assoc.
  destruct Hb.
  auto with perm_db.
Qed.

Lemma NF_insize_compose_n_cups_NF_l b k : 
  NF_insize (compose_n_cups_NF_l b k) = k + k + NF_insize b.
Proof.
  simpl; lia.
Qed.

Lemma NF_outsize_compose_n_cups_NF_l b k : 
  NF_outsize (compose_n_cups_NF_l b k) = NF_outsize b.
Proof.
  easy.
Qed.

Lemma compose_n_cups_NF_l_correct (b : NF_biperm) 
  (Hb : WF_NF_biperm b) (num_cups : nat) : 
  matrix_of_NF_biperm b × 
  (matrix_of_biperm (num_cups + num_cups) 0 (n_m_cup_cap num_cups 0)
  ⊗ I (2 ^ (NF_insize b))) =
  matrix_of_NF_biperm (compose_n_cups_NF_l b num_cups).
Proof.
  rewrite 2!matrix_of_WF_NF_biperm by 
    (try apply compose_n_cups_NF_l_WF; easy).
  rewrite !Mmult_assoc.
  f_equal.
  simpl.
  rewrite <- (kron_1_l _ _ (perm_to_matrix _ (lperm' b))) by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_l, Mmult_1_r by 
    auto using WF_Matrix_dim_change with wf_db.
  rewrite perm_to_matrix_of_stack_perms' 
    by (apply Hb + lia + auto with perm_db).
  restore_dims.
  rewrite (kron_split_diag (perm_to_matrix _ _) (perm_to_matrix _ _)), 
    (kron_split_diag _ (perm_to_matrix _ _)) by auto with wf_db.
  restore_dims.
  rewrite double_add.
  rewrite (Nat.pow_add_r 2 _ (ncup' b + ncup' b)), 
    (Nat.pow_add_r 2 (ncup' b + ncup' b)), !Nat.mul_assoc, !Nat.mul_1_l.
  rewrite <- !Mmult_assoc.
  f_equal.
  restore_dims.
  rewrite perm_to_matrix_idn, id_kron.
  restore_dims.
  rewrite Mmult_1_r by auto with wf_db.
  rewrite <- id_kron, <- kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product' by restore_dims_tac.
  rewrite Mmult_1_r by auto with wf_db.
  restore_dims.
  f_equal; [restore_dims_tac|].
  rewrite <- (kron_1_l _ _ (matrix_of_biperm _ _ (n_m_cup_cap (ncup' b) _)))
    by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product.
  restore_dims.
  rewrite Mmult_1_l, Mmult_1_r by auto with wf_db.
  rewrite <- matrix_of_stack_biperms by auto with biperm_db.
  change (stack_biperms ?n0 ?n1 0) with (stack_biperms n0 n1 (0 + 0)).
  rewrite (n_m_cup_cap_comm (ncup' b)), (n_m_cup_cap_comm num_cups).
  rewrite <- n_m_cup_cap_plus_plus_decomp.
  rewrite 2!Nat.add_0_r.
  now rewrite n_m_cup_cap_comm, (Nat.add_comm (_ + _)), 
    (Nat.add_comm num_cups (ncup' b)).
Qed.



Definition compose_NF_biperms (g f : NF_biperm) :=
  compose_perm_l_NF_biperm (lperm' g)
  (compose_n_cups_NF_l (
    compose_n_caps_NF_l (compose_perm_l_NF_biperm (rperm' g) f
    ) (ncap' g)
  ) (ncup' g)).

Lemma compose_NF_biperms_WF_step_1 (f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) : 
  WF_NF_biperm (compose_perm_l_NF_biperm (rperm' g) f).
Proof.
  apply compose_perm_l_NF_biperm_WF; (apply Hf + rewrite Hfg; apply Hg).
Qed.

Lemma compose_NF_biperms_WF_step_2 (f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) : 
  WF_NF_biperm (compose_n_caps_NF_l (
      compose_perm_l_NF_biperm (rperm' g) f
      ) (ncap' g)
    ).
Proof. 
  apply compose_n_caps_NF_l_WF;
  [cbn; lia|].
  now apply compose_NF_biperms_WF_step_1.
Qed.

Lemma compose_NF_biperms_WF_step_3 (f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) : 
  WF_NF_biperm (compose_n_cups_NF_l (
    compose_n_caps_NF_l (
      compose_perm_l_NF_biperm (rperm' g) f
      ) (ncap' g)
    ) (ncup' g)).
Proof. 
  now apply compose_n_cups_NF_l_WF, compose_NF_biperms_WF_step_2.
Qed.

Lemma compose_NF_biperms_WF_step_4  (f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) : 
  permutation (NF_insize (compose_n_cups_NF_l
    (compose_n_caps_NF_l (compose_perm_l_NF_biperm (rperm' g) f) 
    (ncap' g)) (ncup' g))) 
  (lperm' g).
Proof.
  rewrite NF_insize_compose_n_cups_NF_l.
  rewrite ncup_ncup_nid_compose_n_caps_NF_l by 
    ((now apply compose_NF_biperms_WF_step_1) + cbn; lia).
  eapply permutation_change_dims; [|apply Hg].
  cbn.
  lia.
Qed.

Lemma compose_NF_biperms_WF (f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) : 
  WF_NF_biperm (compose_NF_biperms g f).
Proof.
  unfold compose_NF_biperms.
  apply compose_perm_l_NF_biperm_WF.
  - now apply compose_NF_biperms_WF_step_3.
  - now apply compose_NF_biperms_WF_step_4.
Qed.

Lemma compose_NF_biperms_correct (f g : NF_biperm) 
  (Hf : WF_NF_biperm f) (Hg : WF_NF_biperm g) 
  (Hfg : NF_insize f = NF_outsize g) :
  matrix_of_NF_biperm (compose_NF_biperms g f) [∝]
  @Mmult (2^(NF_outsize f)) (2^(NF_insize f)) (2^(NF_insize g))
   (matrix_of_NF_biperm f) (matrix_of_NF_biperm g).
Proof.
  unfold compose_NF_biperms.
  rewrite matrix_of_compose_perm_l_NF_biperm by 
    (now apply compose_NF_biperms_WF_step_3 + 
     apply compose_NF_biperms_WF_step_4).
  
  rewrite NF_insize_compose_n_cups_NF_l,
    ncup_ncup_nid_compose_n_caps_NF_l by 
    ((now apply compose_NF_biperms_WF_step_1) + cbn; lia).
  cbn.
  rewrite <- compose_n_cups_NF_l_correct by 
    ((now apply compose_NF_biperms_WF_step_2)).
  rewrite <- compose_n_caps_NF_l_correct by
    ((now apply compose_NF_biperms_WF_step_1) + cbn; lia).
  rewrite matrix_of_compose_perm_l_NF_biperm by 
    (apply Hf + rewrite Hfg; apply Hg).
  rewrite ncup_ncup_nid_compose_n_caps_NF_l, 
    ncap_ncap_nid_compose_n_caps_NF_l by 
    ((now apply compose_NF_biperms_WF_step_1) + cbn; lia).
  cbn.
  rewrite double_add, <- (Nat.add_assoc (_ + _)).
  rewrite ncup_ncup_nid_compose_n_caps_NF_l by 
    ((now apply compose_NF_biperms_WF_step_1) + cbn; lia).
  cbn.
  rewrite Hfg, add_sub'.
  rewrite !Mmult_assoc.
  apply Mmult_mat_prop_proper; [easy|].
  rewrite matrix_of_WF_NF_biperm by easy.
  rewrite Mmult_assoc.
  apply Mmult_mat_prop_proper; [easy|].
  rewrite <- Mmult_assoc.
  apply Mmult_mat_prop_proper; [|easy].
  restore_dims_prop.
  rewrite kron_mixed_product, Mmult_1_r by auto_wf.
  rewrite matrix_of_biperm_n_m_cup_cap_split, n_m_cup_cap_comm.
  easy.
Qed.




Lemma biperm_contract_case_1_biperm m n (f : nat -> nat)
  (Hf : bipermutation (m + n) f) : 0 < m -> f 0 < m ->
  bipermutation (m + n)
    (swap_perm 1 (f 0) m ∘ f ∘ swap_perm 1 (f 0) m).
Proof.
  intros Hm Hf0.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  rewrite <- (stack_perms_WF_idn m n (swap_perm 1 (f 0) m)) by cleanup_perm.
  pose proof (Hfne 0 ltac:(lia)).
  assert (1 < m) by lia.
  rewrite <- swap_perm_inv at 1 by lia.
  rewrite <- biperm_compose_perm_l_spec.
  auto with biperm_db.
Qed.

Lemma biperm_contract_case_1_small_idn m n (f : nat -> nat)
  (Hf : bipermutation (m + n) f) : 0 < m -> f 0 < m ->
  perm_eq 2
    (swap_perm 1 (f 0) m ∘ f ∘ swap_perm 1 (f 0) m) swap_2_perm.
Proof.
  intros Hm Hf0.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (Hfne 0 ltac:(lia)).
  unfold compose.
  ZXpermAutomation.by_perm_cell.
  - now rewrite (swap_perm_neither _ _ _ 0), swap_perm_right by lia.
  - now rewrite swap_perm_left, Hfeq, swap_perm_neither by lia.
Qed.


Lemma biperm_contract_case_1_bipermutation n (f : nat -> nat) 
  (Hf : bipermutation n f) : n <> 0 ->
  f 0 = 1 -> 
  bipermutation (n - 2) (contract_biperm 0 (f 0) f).
Proof.
  intros Hmn Hf0.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (fun i j Hi Hj => proj1 (bipermutation_injective Hf i j Hi Hj)) 
    as Hfinj.
  pose proof (Hfbdd 0 ltac:(lia)).
  assert (Hf1: f 1 = 0) by (now rewrite <- Hf0, Hfeq by lia).
  rewrite contract_biperm_bipermutation_iff by (easy + lia).
  intros k Hk.
  unfold contract_biperm.
  rewrite Hf0.
  cbn.
  rewrite Hf0, Hf1.
  cbn. 
  simplify_bools_lia_one_kernel.
  unfold contract_perm.
  rewrite Hf1.
  cbn.
  simplify_bools_lia_one_kernel.
  pose proof (Hfinj (k + 1 + 1) 0).
  pose proof (Hfinj (k + 1 + 1) 1).
  pose proof (Hfne (k + 1 + 1)).
  lia.
Qed.

Lemma biperm_contract_case_2_bipermutation m n (f : nat -> nat)
  (Hf : bipermutation (m + n) f) : (m + n) <> 0 ->
  f 0 = m + n - 1 ->
  bipermutation (m + n - 2) (contract_biperm 0 (f 0) f).
Proof.
  intros Hm Hf0.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (Hfne 0 ltac:(lia)).
  apply contract_biperm_bipermutation_iff; 
  [auto|lia|].
  intros a Ha.
  unfold contract_biperm.
  bdestructΩ'.
  unfold contract_perm.
  rewrite Hfeq by lia.
  simpl.
  simplify_bools_lia_one_kernel.
  pose proof (Hfne (a + 1)).
  bdestructΩ'.
  - enough (f (a + 1) <> 0) by lia.
    rewrite (bipermutation_eq_iff _ _ Hf) by lia.
    lia.
  - pose proof (Hfbdd (a + 1)).
    assert (Heq : f (a + 1) = f 0) by lia.
    rewrite (bipermutation_injective Hf) in Heq; lia.
Qed.

Lemma biperm_contract_case_3_bipermutation m n (f : nat -> nat)
  (Hf : bipermutation (m + n) f) : m + n <> 0 ->
  f (m + n - 2) = m + n - 1 ->
  bipermutation (m + n - 2) 
  (contract_biperm (m + n - 2) (m + n - 1) f).
Proof. Abort. (* Removed for declutter. Do we need this?
  Should we keep it, combining m+n into one variable and 
  moving it into the general lemmas? *) (*
  intros Hmn Hbig.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  assert (Hbig' : f (m + n - 1) = m + n - 2) by 
    (rewrite <- Hbig, Hfeq; lia).
  rewrite <- Hbig.
  rewrite contract_biperm_bipermutation_iff by (easy + lia).
  intros a Ha.
  rewrite Hbig.
  unfold contract_biperm.
  bdestructΩ'.
  unfold contract_perm.
  do 2 simplify_bools_lia_one_kernel.
  rewrite Hbig'.
  pose proof (proj1 (bipermutation_injective Hf a (m + n - 2)
    ltac:(lia) ltac:(lia))) as Hinj1.
  rewrite Hbig in Hinj1.
  pose proof (proj1 (bipermutation_injective Hf a (m + n - 1)
    ltac:(lia) ltac:(lia))) as Hinj2.
  rewrite Hbig' in Hinj2.
  pose proof (Hfbdd a ltac:(lia)).
  bdestructΩ'.
  apply Hfne; lia.
Qed.*)

Lemma biperm_contract_case_1_bipermutation' n (f : nat -> nat) 
  (Hf : bipermutation n f) : n <> 0 -> f 0 = 1 -> 
  bipermutation (n - 2) (contract_biperm 0 1 f).
Proof.
  intros Hn Hf0.
  rewrite <- Hf0 at 2.
  now apply biperm_contract_case_1_bipermutation.
Qed.

Lemma biperm_contract_case_2_bipermutation' m n (f : nat -> nat)
  (Hf : bipermutation (m + n) f) : (m + n) <> 0 ->
  f 0 = m + n - 1 ->
  bipermutation (m + n - 2) (contract_biperm 0 (m + n - 1) f).
Proof.
  intros Hn Hf0.
  rewrite <- Hf0.
  now apply biperm_contract_case_2_bipermutation.
Qed.

Lemma biperm_contract_case_1_eq n f (Hf : bipermutation n f) 
  (Hf0 : f 0 = 1) (Hn : n <> 0) : 
    perm_eq (n - 2) 
    (contract_biperm 0 (f 0) f) 
    (fun k => f (k + 2) - 2).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (Hfbdd 0).
  assert (Hf1 : f 1 = 0) by (now rewrite <- Hf0, Hfeq by lia). 
  intros k Hk.
  unfold contract_biperm.
  rewrite Hf0.
  cbn.
  rewrite Hf0, Hf1.
  cbn.
  rewrite Nat.sub_diag.
  cbn.
  unfold contract_perm.
  do 2 simplify_bools_lia_one_kernel.
  replace (k + 1 + 1) with (k + 2) by lia.
  enough (f (k + 2) <> 0 /\ f (k + 2) <> 1) by lia.
  rewrite 2!(bipermutation_eq_iff _ _ Hf) by lia.
  lia.
Qed.

Lemma biperm_contract_case_2_eq n f (Hf : bipermutation n f) 
  (Hf0 : f 0 = n - 1) (Hn : n <> 0) : 
    perm_eq (n - 2) 
    (contract_biperm 0 (f 0) f) 
    (fun k => f (k + 1) - 1).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (bipermutation_injective Hf) as Hfinj.
  pose proof (Hfbdd 0).
  assert (Hf1 : f (n - 1) = 0) by (now rewrite <- Hf0, Hfeq by lia). 
  intros k Hk.
  unfold contract_biperm.
  rewrite Hf0.
  simplify_bools_lia_one_kernel.
  unfold contract_perm at 1.
  cbn.
  unfold contract_perm.
  do 3 simplify_bools_lia_one_kernel.
  rewrite Hf1, Hf0.
  cbn.
  pose proof (proj1 (Hfinj (k + 1) 0 ltac:(lia) ltac:(lia))).
  pose proof (proj1 (Hfinj (k + 1) (n - 1) ltac:(lia) ltac:(lia))).
  pose proof (Hfbdd (k + 1)).
  simplify_bools_lia_one_kernel.
  easy.
Qed.

(* realize_biperm_data lperm rperm nid ncup ncap looks like:
  m+n-1    m⁻¹                            m    m-1
  m+n-2    r    ncup ⨂ ⊃    ncap ⨂ ⊂    r    m-2
  ...      e                              e    ...
  m+1      p          n_wire nid          p    1
  m        l                              r    0

Say n = ncup + ncup + nid inputs (left), 
m = ncap + ncap + nid outputs (right)
*)

(* 
  Define how to change a biperm to make it compatible
  with above shrinking lemmas. We will show, in particular, 
  that it always gives a biperm and has an inverse. The program 
  is to show it has generally nice properties on all functions
  then to use its relation to f to describe its value at f, 
  specifically relating that to contract_biperm 0 (f 0) f . *)
Definition change_fun_to_shrink_biperm (n m : nat) (f : nat -> nat)
  : ((nat -> nat) -> (nat -> nat)) :=
  if m =? 0 then (* no inputs; simple case *)
    (
      if n <? 2 then (* no outputs; done *)
        (fun g => g)
      else (* make 0 go to 1*)
        (fun g => (swap_perm 1 (f 0) n ∘ g ∘ swap_perm 1 (f 0) n))
        (* = (fun g => 
          biperm_compose_perm_l m n g (swap_perm 1 (f 0) m)) *)
      )
  (* if (n =? 0) || (m =? 0) then (fun g => g) else *)
  else if (f 0 <? m) then (* we want to prep to add a cap by moving f 0 to 1 *)
    (fun g => (swap_perm 1 (f 0) m ∘ g ∘ swap_perm 1 (f 0) m))
    (* = (fun g => 
      biperm_compose_perm_l m n g (swap_perm 1 (f 0) m)) *)
  (* Can assume f 0 < m + n and, OLD: to lessen case analysis, won't add a check *)
  (* NEW: We want this check to make it have a better proper condition *)
  else if (f 0 <? m + n) then 
    (* make 0 go to m + n - 1 *)
    (fun g => swap_perm (m + n - 1) (f 0) (m + n) ∘ g 
      ∘ swap_perm (m + n - 1) (f 0) (m + n))
  else (fun g => g).

Add Parametric Morphism n m : (change_fun_to_shrink_biperm n m) with signature 
  (perm_eq (m + n)) ==> (perm_eq (m + n)) ==> perm_eq (m + n) 
  as change_fun_to_shrink_biperm_perm_eq_of_perm_eq.
Proof.
  Abort.


Add Parametric Morphism n m f (Hf : bipermutation (m + n) f) : 
  (change_fun_to_shrink_biperm n m f) 
  with signature (perm_eq (m + n)) ==> perm_eq (m + n) as 
  change_fun_to_shrink_biperm_perm_eq_of_perm_eq.
Proof.
  intros g g' Hg.
  unfold change_fun_to_shrink_biperm.
  bdestruct (m =? 0); bdestructΩ'.
  - pose proof (Hf 0).
    now rewrite Hg.
  - pose proof (Hf 0).
    rewrite <- (stack_perms_WF_idn m n (swap_perm 1 _ _)) by cleanup_perm_inv.
    now rewrite Hg.
  - pose proof (Hf 0).
    now rewrite Hg.
Qed.

Lemma change_fun_to_shrink_biperm_preserves_biperm n m f g
  (Hf : bipermutation (m + n) f) (Hg : bipermutation (m + n) g) :
  (* NB Hf is almost certainly stronger than we need *)
  bipermutation (m + n) (change_fun_to_shrink_biperm n m f g).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  unfold change_fun_to_shrink_biperm.
  bdestruct (m =? 0); bdestruct_all; try easy.
  - subst. cbn.
    replace (swap_perm 1 (f 0) n) with 
      (stack_perms 0 n idn (swap_perm 1 (f 0) n))
      by (eq_by_WF_perm_eq (0 + n); 
      rewrite stack_perms_defn; cbn;
      intros k Hk;
      now rewrite Nat.sub_0_r, Nat.add_0_r).
    pose proof (Hfbdd 0 ltac:(lia)).
    pose proof (bipermutation_dim_ne_1 Hf).
    rewrite <- swap_perm_inv at 1 by lia.
    rewrite <- biperm_compose_perm_r_spec by auto with biperm_db.
    change (bipermutation n) with (bipermutation (0 + n)).
    apply biperm_compose_perm_r_biperm; [easy|].
    auto with perm_db zarith.
  - rewrite <- (stack_perms_WF_idn m n (swap_perm 1 (f 0) m)) by cleanup_perm.
    pose proof (Hfne 0 ltac:(lia)).
    assert (1 < m) by lia.
    rewrite <- swap_perm_inv at 1 by lia.
    rewrite <- biperm_compose_perm_l_spec.
    auto with biperm_db.
  - pose proof (Hfbdd 0 ltac:(lia)). 
    replace (swap_perm (m + n - 1) (f 0) (m + n)) with 
    (stack_perms m n idn (swap_perm (n - 1) (f 0 - m) n)).
    + rewrite <- swap_perm_inv at 1 by lia.
      rewrite <- biperm_compose_perm_r_spec by auto with biperm_db.
      apply biperm_compose_perm_r_biperm; [easy|].
      auto with perm_db zarith.
    + eq_by_WF_perm_eq (m + n).
      rewrite 2!swap_perm_defn by lia.
      rewrite stack_perms_defn.
      intros k Hk.
      bdestructΩ'.
Qed.

Lemma change_fun_to_shrink_biperm_involutive n m f g
  (Hf : bipermutation (m + n) f) :
  (* NB Hf is almost certainly stronger than we need *)
  change_fun_to_shrink_biperm n m f (change_fun_to_shrink_biperm n m f g)
  = g.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  unfold change_fun_to_shrink_biperm.
  pose proof (Hfbdd 0).
  pose proof (Hfne 0).
  bdestructΩ';
  rewrite !compose_assoc;
  rewrite swap_perm_invol by lia;
  rewrite compose_idn_r, <- !compose_assoc;
  rewrite swap_perm_invol by lia;
  apply compose_idn_l.
Qed.



(* 
  Parallel to change_fun_to_shrink_biperm, defines the function to 
  grow a NF_biperm to match a given input function. Specifically, 
  it has the properties of preserving WF_NF_biperm b and that if 
    realize_NF_biperm b ≡ change_fun_to_shrink_biperm n m f f
  then 
    realize_NF_biperm (change_NF_from_shrink_biperm n m f b)
    ≡ f.
  (More precisely, 
    realize_NF_biperm (change_NF_from_shrink_biperm n m f b) ≡
    change_fun_to_shrink_biperm n m f (realize_NF_biperm b) 
    given appropriate bipermutation / WF_NF_biperm conditions.)
  NB that we need to account for realize_NF_biperm (intentionally)
  reflecting lperm' and rperm', hence the difference in inputs
  for the respective swap_perm's. Fortunately swap_perm is invariant
  under inverse, so this is not an issue.
*)
Definition change_NF_from_shrink_biperm (n m : nat) (f : nat -> nat)
  (b : NF_biperm) : NF_biperm :=
  if m =? 0 then (* no inputs; simple case *)
    (
      if n =? 0 then (* no outputs; done *)
        b
      else (* make 0 go to 1*)
        compose_perm_l_NF_biperm (swap_perm (n - S 1) (n - S (f 0)) n) b
      )
  (* if (n =? 0) || (m =? 0) then (fun g => g) else *)
  else if (f 0 <? m) then (* we want to prep to add a cap by moving f 0 to 1 *)
    compose_perm_r_NF_biperm (swap_perm (m - S 1) (m - S (f 0)) m) b
  (* Can assume f 0 < m + n and, to lessen case analysis, won't add a check *)
  else (* make 0 go to m + n - 1 *)
    compose_perm_l_NF_biperm (swap_perm (n - S (n - 1)) (n - S (f 0 - m)) n) b.


Lemma change_NF_from_shrink_biperm_WF n m f b 
  (Hf : bipermutation (m + n) f) (HbWF : WF_NF_biperm b)
  (Hbin : NF_insize b = n) (Hbout : NF_outsize b = m) :
  WF_NF_biperm (change_NF_from_shrink_biperm n m f b).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (Hfne 0).
  pose proof (Hfbdd 0).
  unfold change_NF_from_shrink_biperm.
  pose proof (bipermutation_dim_ne_1 Hf).
  bdestruct (m =? 0); bdestruct_all; try easy;
  [apply compose_perm_l_NF_biperm_WF; [easy|] |
   apply compose_perm_r_NF_biperm_WF; [easy|] |
   apply compose_perm_l_NF_biperm_WF; [easy|]];
   rewrite ?Hbin, ?Hbout;
   apply swap_perm_permutation; lia.
Qed.  

Lemma realize_change_NF_from_shrink_biperm n m f b 
  (Hf : bipermutation (m + n) f) (HbWF : WF_NF_biperm b)
  (Hbin : NF_insize b = n) (Hbout : NF_outsize b = m) : 
  perm_eq (m + n) 
    (realize_NF_biperm (change_NF_from_shrink_biperm n m f b))
    (change_fun_to_shrink_biperm n m f (realize_NF_biperm b)).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (Hfne 0).
  pose proof (Hfbdd 0).
  pose proof (bipermutation_dim_ne_1 Hf).
  unfold change_NF_from_shrink_biperm, change_fun_to_shrink_biperm.
  assert (bipermutation (NF_outsize b + NF_insize b) (realize_NF_biperm b))
    by (rewrite Nat.add_comm; 
    apply realize_biperm_data_bipermutation; apply HbWF).
  bdestruct (m =? 0); bdestruct_all.
  - subst; easy.
  - rewrite <- Hbin, <- Hbout in *.
    rewrite realize_compose_perm_l_NF_biperm by 
      (easy || auto with perm_db zarith).
    rewrite biperm_compose_perm_r_spec by auto with perm_bounded_db.
    apply perm_eq_compose_proper; 
    [auto with perm_bounded_db|..].
    + rewrite swap_perm_inv' by lia.
      rewrite swap_perm_conj_reflect_eq by lia.
      rewrite !sub_S_sub_S by lia.
      apply perm_eq_compose_proper; [cleanup_perm_inv| | easy].
      rewrite swap_perm_inv by lia.
      intros k Hk.
      rewrite Hbin, Hbout.
      replace m with 0 by congruence.
      unfold stack_perms.
      cbn.
      simplify_bools_lia_one_kernel.
      now rewrite Nat.sub_0_r, Nat.add_0_r.
    + rewrite swap_perm_inv' by lia.
      rewrite swap_perm_conj_reflect_eq by lia.
      rewrite !sub_S_sub_S by lia.
      intros k Hk.
      rewrite Hbin, Hbout.
      replace m with 0 by congruence.
      unfold stack_perms.
      cbn.
      simplify_bools_lia_one_kernel.
      now rewrite Nat.sub_0_r, Nat.add_0_r.
  - rewrite <- Hbin, <- Hbout in *. 
    assert (1 < NF_outsize b) by lia.
    rewrite <- (stack_perms_WF_idn (NF_outsize b) (NF_insize b)
      (swap_perm 1 (f 0) _)) by cleanup_perm_inv.
    rewrite <- (swap_perm_inv 1 (f 0) (NF_outsize b)) at 1 by lia.
    rewrite <- biperm_compose_perm_l_spec.
    rewrite realize_compose_perm_r_NF_biperm by auto with perm_db zarith.
    erewrite biperm_compose_perm_l_eq_of_perm_eq; [reflexivity|..];
    (split; [auto with perm_bounded_db|]); [easy|].
    rewrite swap_perm_conj_reflect_eq by lia.
    rewrite !sub_S_sub_S by lia.
    easy.
  - replace (swap_perm (m + n - 1) (f 0) (m + n)) with 
    (stack_perms m n idn (swap_perm (n - 1) (f 0 - m) n)).
    + rewrite <- Hbin, <- Hbout in *. 
      rewrite <- (swap_perm_inv (NF_insize b - 1)) at 1 by lia.
      rewrite <- biperm_compose_perm_r_spec by 
        auto with perm_bounded_db zarith.
      rewrite realize_compose_perm_l_NF_biperm by auto with perm_db zarith.
      erewrite biperm_compose_perm_r_eq_of_perm_eq; [reflexivity|..];
      (split; [auto with perm_bounded_db|]); [easy|].
      rewrite swap_perm_inv' by lia.
      rewrite swap_perm_conj_reflect_eq by lia.
      now rewrite !sub_S_sub_S by lia.
    + eq_by_WF_perm_eq (m + n).
      rewrite 2!swap_perm_defn, stack_perms_defn by lia.
      intros k Hk.
      bdestruct_all; lia.
Qed.



(*  The definition of b being a representative of f 
    once f is shrunken by our procedure. We will prove this
    implies that b is grown to a NF_biperm satisfying 
    is_NF_representative n m f b *)
Definition is_shrunken_representative (n m : nat) 
  (b : NF_biperm) (f : nat -> nat) : Prop :=
  if m =? 0 then (* no inputs; simple case *)
    (
      if n =? 0 then (* no outputs; done *)
        is_NF_representative n m b f
        (* Equivalently, 
        WF_NF_biperm b /\ NF_insize b = 0 /\ NF_outsize b = 0 *)
      else (* make 0 go to 1 *)
      is_NF_representative (n - 2) m b
        (contract_biperm 0 1 (change_fun_to_shrink_biperm n m f f))
      )
  (* if (n =? 0) || (m =? 0) then (fun g => g) else *)
  else if (f 0 <? m) then (* we want to prep to add a cap by moving f 0 to 1 *)
    is_NF_representative n (m - 2) b
      (contract_biperm 0 1 (change_fun_to_shrink_biperm n m f f))
  (* Can assume f 0 < m + n and, to lessen case analysis, won't add a check *)
  else (* make 0 go to m + n - 1 *)
    is_NF_representative (n - 1) (m - 1) b
      (contract_biperm 0 (m + n - 1) (change_fun_to_shrink_biperm n m f f)).





(* 
  Finally, define how to extend the NF_biperm corresponding to 
    contract_biperm 0 (f 0) (change_fun_to_shrink_biperm n m f f)
  to a NF_biperm corresponding to 
    (change_fun_to_shrink_biperm n m f f). 
  Hence, the key property is 
    is_shrunken_representative n m b f ->
    is_NF_representative n m 
       (grow_NF_of_shrunken_biperm n m f b)
       (change_fun_to_shrink_biperm n m f f) 
  *)
  Definition grow_NF_of_shrunken_biperm (n m : nat) 
  (f : nat -> nat) (b : NF_biperm) : NF_biperm :=
  if m =? 0 then (* no inputs; simple case *)
    (
      if n =? 0 then (* no outputs; done *)
        b (* trivial / base case *)
      else (* make 0 go to 1 *)
        (* Have f 0 = 1 (better (f (m + 0) = m + 1
          in the inputs, so need to extend with a 
          new cup and move it to the bottom of the ids *)
        compose_perm_l_NF_biperm 
          (big_swap_perm 2 (NF_insize b))
          (add_cup_to_NF b)
      )
  (* if (n =? 0) || (m =? 0) then (fun g => g) else *)
  else if (f 0 <? m) then (* we want to prep to add a cap by moving f 0 to 1 *)
    (* Have f 0 = 1 (in the outputs), so need to extend with a 
      new cap and move it to the bottom of the ids *)
    compose_perm_r_NF_biperm 
      (big_swap_perm (NF_outsize b) 2)
      (add_cap_to_NF b)
  (* Can assume f 0 < m + n and, to lessen case analysis, won't add a check *)
  else (* make 0 go to m + n - 1 *)
    compose_perm_l_NF_biperm
      (big_swap_perm (NF_insize b) 1)
      (add_id_to_NF b).

Lemma grow_NF_of_shrunken_biperm_WF (n m : nat) f b (Hb : WF_NF_biperm b) :
  WF_NF_biperm (grow_NF_of_shrunken_biperm n m f b).
Proof.
  unfold grow_NF_of_shrunken_biperm.
  bdestruct (m =? 0); bdestructΩ'.
  - apply compose_perm_l_NF_biperm_WF.
    + now apply add_cup_to_NF_WF.
    + rewrite NF_insize_add_cup_to_NF.
      auto with perm_db.
  - apply compose_perm_r_NF_biperm_WF.
    + now apply add_cap_to_NF_WF.
    + rewrite NF_outsize_add_cap_to_NF.
      auto with perm_db.
  - apply compose_perm_l_NF_biperm_WF.
    + now apply add_id_to_NF_WF.
    + rewrite NF_insize_add_id_to_NF.
      auto with perm_db.
Qed.



Lemma grow_NF_of_shrunken_representative (n m : nat) 
  (f : nat -> nat) (b : NF_biperm) (Hf : bipermutation (m + n) f)
  (Hb : is_shrunken_representative n m b f) : 
  is_NF_representative n m 
    (grow_NF_of_shrunken_biperm n m f b) 
    (change_fun_to_shrink_biperm n m f f).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (Hfne 0).
  pose proof (Hfbdd 0).
  repeat split; cycle 4.
  - revert Hb.
    unfold grow_NF_of_shrunken_biperm, 
      is_shrunken_representative,
      change_fun_to_shrink_biperm.
    bdestruct (m =? 0); bdestruct_all; subst; try easy; cycle 1.
    + intros (HbWF & Hbin & Hbout & Heq).
      eapply perm_eq_dim_change_if_nonzero;
      [rewrite realize_compose_perm_r_NF_biperm|cbn; lia];
      [|now apply add_cap_to_NF_WF|
      rewrite NF_outsize_add_cap_to_NF; auto with perm_db].
      rewrite biperm_compose_perm_l_spec.
      rewrite big_swap_perm_conj_reflect_eq' by (cbn; lia).
      rewrite NF_outsize_add_cap_to_NF.
      rewrite big_swap_perm_inv_change_dims by lia.
      rewrite realize_add_cap_to_NF by easy.
      rewrite (stack_biperms_eq_of_perm_eq Heq (perm_eq_refl 2 _))
        by lia.
      rewrite NF_insize_add_cap_to_NF, Hbin.
      rewrite Hbout.
      clear dependent b.
      replace (2 + (m - 2)) with m by lia.
      rewrite 2!stack_perms_WF_idn by auto with WF_Perm_db.
      set (g := swap_perm 1 (f 0) m ∘ f ∘ swap_perm 1 (f 0) m).
      assert (Hg : bipermutation (m + n) g). {
        unfold g.
        apply biperm_contract_case_1_biperm; easy + lia.
      }
      assert (Hg0 : g 0 = 1). {
        unfold g, compose.
        rewrite (swap_perm_neither _ _ _ 0), swap_perm_right by lia.
        easy.
      }
      pose proof (fun i Hi => proj1 (Hg i Hi)) as Hgbdd.
      pose proof (fun i Hi => proj1 (proj2 (Hg i Hi))) as Hgne.
      pose proof (fun i Hi => proj2 (proj2 (Hg i Hi))) as Hgeq.
      pose proof (Hgne 0 ltac:(lia)).
      pose proof (Hgbdd 0 ltac:(lia)).
      assert (Hg1 : g 1 = 0) by (now rewrite <- Hg0, Hgeq by lia).
      (* Subproof :/ *)
      {
        gen g.
        assert (Hm : 1 < m) by lia.
        clear -Hm.
        intros g Hg Hg0 Hgbdd Hgne Hgeq Hgne0 Hgbdd0 Hg1.
        replace (contract_biperm 0 1) with (contract_biperm 0 (g 0))
          by (now rewrite Hg0).
        pose proof (biperm_contract_case_1_bipermutation _ g Hg
          ltac:(lia) Hg0) as Hgc.
        pose proof (bipermutation_is_bounded _ _ Hgc) as Hgcbdd.
        intros k Hk.
        rewrite (stack_biperms_eq_of_perm_eq 
          (biperm_contract_case_1_eq _ g Hg ltac:(lia) ltac:(lia))
          (perm_eq_refl 2 _)) by lia.
        bdestruct (k <? 2).
        - unfold compose.
          unfold big_swap_perm at 2.
          simplify_bools_lia_one_kernel.
          unfold stack_biperms.
          do 3 simplify_bools_lia_one_kernel.
          rewrite Nat.add_sub.
          change (?x <? 2) with (x <? 1 + 1).
          rewrite n_m_cup_cap_ltb_double by lia.
          simplify_bools_lia_one_kernel.
          unfold big_swap_perm.
          simplify_bools_lia_one_kernel.
          destruct k as [|[]]; [..|lia];
          cbn; bdestructΩ'.
        - unfold compose.
          unfold big_swap_perm at 2.
          simplify_bools_lia_one_kernel.
          replace (S (S (m - 2))) with m by lia.
          bdestruct (k <? m).
          + unfold stack_biperms.
            do 2 simplify_bools_lia_one_kernel.
            rewrite Nat.sub_add by lia.
            pose proof (Hgbdd k).
            unfold big_swap_perm.
            bdestructΩ'.
            enough (g k <> 0 /\ g k <> 1) by lia.
            rewrite 2!(bipermutation_eq_iff _ _ Hg) by lia.
            lia.
          + unfold stack_biperms.
            do 2 simplify_bools_lia_one_kernel.
            rewrite 2!Nat.sub_add by lia.
            pose proof (Hgbdd k).
            unfold big_swap_perm.
            bdestructΩ';
            enough (g k <> 0 /\ g k <> 1) by lia;
            rewrite 2!(bipermutation_eq_iff _ _ Hg) by lia;
            lia.
      } 
    + intros (HbWF & Hbin & Hbout & Heq).
      eapply perm_eq_dim_change_if_nonzero;
      [rewrite realize_compose_perm_l_NF_biperm|cbn; lia];
      [|now apply add_id_to_NF_WF|
      rewrite NF_insize_add_id_to_NF; auto with perm_db].
      rewrite biperm_compose_perm_r_spec; 
      [| now apply bipermutation_is_bounded, 
        realize_NF_biperm_bipermutation, add_id_to_NF_WF | 
        auto with perm_bounded_db].
      rewrite big_swap_perm_inv'_change_dims by (cbn; lia).
      rewrite big_swap_perm_conj_reflect_eq' by (cbn; lia).
      rewrite NF_insize_add_id_to_NF, NF_outsize_add_id_to_NF.
      rewrite big_swap_perm_inv_change_dims by lia.
      rewrite realize_add_id_to_NF by easy.
      rewrite (stack_biperms_eq_of_perm_eq (perm_eq_refl 2 _) Heq)
        by lia.
      rewrite Hbin.
      rewrite Hbout.
      clear dependent b.
      rewrite 2!Nat.sub_add by lia.
      set (g := swap_perm (m + n - 1) (f 0) (m + n) ∘ f 
        ∘ swap_perm (m + n - 1) (f 0) (m + n)).
      
      assert (Hg : bipermutation (m + n) g). {
        unfold g.
        replace (swap_perm (m + n - 1) (f 0) (m + n))
          with (stack_perms m n idn (swap_perm (n - 1) (f 0 - m) n)).
        - rewrite <- swap_perm_inv at 1 by lia.
          rewrite <- biperm_compose_perm_r_spec by 
            auto with perm_bounded_db.
          apply biperm_compose_perm_r_biperm; [easy|].
          auto with perm_db zarith.
        - eq_by_WF_perm_eq (m + n).
          rewrite 2!swap_perm_defn by lia.
          rewrite stack_perms_defn.
          intros k Hk.
          bdestructΩ'.
      } 
      assert (Hg0 : g 0 = (m + n - 1)). {
        unfold g, compose.
        rewrite (swap_perm_neither _ _ _ 0), swap_perm_right by lia.
        easy.
      }
      pose proof (fun i Hi => proj1 (Hg i Hi)) as Hgbdd.
      pose proof (fun i Hi => proj1 (proj2 (Hg i Hi))) as Hgne.
      pose proof (fun i Hi => proj2 (proj2 (Hg i Hi))) as Hgeq.
      pose proof (Hgne 0 ltac:(lia)).
      pose proof (Hgbdd 0 ltac:(lia)).
      assert (Hg1 : g (m + n - 1) = 0) by (now rewrite <- Hg0, Hgeq by lia).
      (* Subproof :/ *)
      {
        gen g.
        assert (Hn : n <> 0) by lia.
        assert (Hm : m <> 0) by lia.
        clear -Hm Hn.
        intros g Hg Hg0 Hgbdd Hgne Hgeq Hgne0 Hgbdd0 Hg1.
        pose proof (fun i j Hi Hj =>
          (proj1 (bipermutation_injective Hg i j Hi Hj))) as Hginj.
        rewrite <- Hg0.
        pose proof (biperm_contract_case_2_bipermutation m n g Hg
          ltac:(lia) Hg0) as Hgc.
        pose proof (bipermutation_is_bounded _ _ Hgc) as Hgcbdd.
        intros k Hk.
        rewrite (stack_biperms_eq_of_perm_eq (perm_eq_refl 2 _)
          (biperm_contract_case_2_eq _ g Hg ltac:(lia) ltac:(lia))) by lia.
        bdestruct (k =? 0); [|bdestruct (k =? m + n - 1)].
        - unfold compose.
          subst k.
          rewrite (stack_perms_left (k:=0)) by lia.
          unfold stack_biperms.
          cbn.
          rewrite Nat.sub_add by lia.
          unfold stack_perms.
          do 2 simplify_bools_lia_one_kernel.
          rewrite Nat.sub_diag.
          cbn.
          lia.
        - unfold compose.
          rewrite (stack_perms_right (k:=k)) by lia.
          unfold big_swap_perm at 2.
          do 2 simplify_bools_lia_one_kernel.
          replace (k - m - (n - 1) + m) with m by lia.
          unfold stack_biperms.
          do 4 simplify_bools_lia_one_kernel.
          unfold idn_biperm.
          do 3 simplify_bools_lia_one_kernel.
          rewrite stack_perms_left by lia.
          subst.
          lia.
        - unfold compose.
          unfold stack_perms at 2.
          simplify_bools_lia_one_kernel.
          bdestruct (k <? m).
          + unfold stack_biperms.
            do 3 simplify_bools_lia_one_kernel.
            rewrite Nat.sub_add by lia.
            unfold stack_perms.
            pose proof (Hgbdd k Hk).
            pose proof (Hginj k 0 ltac:(lia) ltac:(lia)).
            rewrite Hg0 in *.
            pose proof (Hginj k (m + n - 1) ltac:(lia) ltac:(lia)).
            rewrite Hg1 in *.
            bdestructΩ'.
            unfold big_swap_perm.
            bdestructΩ'.
          + unfold big_swap_perm at 2.
            simplify_bools_lia_one_kernel.
            replace (k - m + 1 + m) with (k + 1) by lia.
            unfold stack_biperms.
            rewrite Nat.sub_add by lia.
            cbn.
            do 4 simplify_bools_lia_one_kernel.
            replace (k + 1 - 2 + 1) with k by lia.
            unfold stack_perms.
            unfold stack_perms.
            pose proof (Hgbdd k Hk).
            pose proof (Hginj k 0 ltac:(lia) ltac:(lia)).
            rewrite Hg0 in *.
            pose proof (Hginj k (m + n - 1) ltac:(lia) ltac:(lia)).
            rewrite Hg1 in *.
            bdestructΩ'.
            unfold big_swap_perm.
            bdestructΩ'.
      } 
    + intros (HbWF & Hbin & Hbout & Heq).
      eapply perm_eq_dim_change_if_nonzero;
      [rewrite realize_compose_perm_l_NF_biperm|cbn; lia];
      [|now apply add_cup_to_NF_WF|
      rewrite NF_insize_add_cup_to_NF; auto with perm_db].
      rewrite biperm_compose_perm_r_spec; 
      [|now apply bipermutation_is_bounded, 
        realize_NF_biperm_bipermutation, add_cup_to_NF_WF|
        auto with perm_bounded_db].
      
      rewrite big_swap_perm_inv'_change_dims by (cbn; lia).
      rewrite big_swap_perm_conj_reflect_eq' by (cbn; lia).
      rewrite NF_insize_add_cup_to_NF, NF_outsize_add_cup_to_NF.
      rewrite big_swap_perm_inv_change_dims by lia.
      rewrite realize_add_cup_to_NF by easy.
      rewrite (stack_biperms_eq_of_perm_eq Heq (perm_eq_refl 2 _))
        by lia.
      rewrite Hbin.
      rewrite Hbout.
      clear dependent b.
      rewrite ?Nat.add_0_l in *.
      set (g := swap_perm 1 (f 0) n ∘ f ∘ swap_perm 1 (f 0) n).
      assert (Hg : bipermutation (0 + n) g). {
        unfold g.
        rewrite Nat.add_comm.
        apply biperm_contract_case_1_biperm; 
        [rewrite ?Nat.add_0_r|..]; try easy + lia.
      }
      assert (Hg0 : g 0 = 1). {
        unfold g, compose.
        rewrite (swap_perm_neither _ _ _ 0), swap_perm_right by lia.
        easy.
      }
      pose proof (fun i Hi => proj1 (Hg i Hi)) as Hgbdd.
      pose proof (fun i Hi => proj1 (proj2 (Hg i Hi))) as Hgne.
      pose proof (fun i Hi => proj2 (proj2 (Hg i Hi))) as Hgeq.
      pose proof (Hgne 0 ltac:(lia)).
      pose proof (Hgbdd 0 ltac:(lia)).
      assert (Hg1 : g 1 = 0) by (now rewrite <- Hg0, Hgeq by lia).
      (* Subproof :/ *)
      {
        gen g.
        assert (Hn : 1 < n) by lia.
        clear -Hn.
        intros g Hg Hg0 Hgbdd Hgne Hgeq Hgne0 Hgbdd0 Hg1.
        replace (contract_biperm 0 1) with (contract_biperm 0 (g 0))
          by (now rewrite Hg0).
        pose proof (biperm_contract_case_1_bipermutation _ g Hg
          ltac:(lia) Hg0) as Hgc.
        pose proof (bipermutation_is_bounded _ _ Hgc) as Hgcbdd.
        intros k Hk.
        rewrite (stack_biperms_eq_of_perm_eq 
          (biperm_contract_case_1_eq _ g Hg ltac:(lia) ltac:(lia))
          (perm_eq_refl 2 _)) by lia.
        bdestruct (k <? 2).
        - unfold compose.
          rewrite (stack_perms_right (k:=k)) by lia.
          rewrite Nat.sub_0_r, Nat.add_0_r.
          unfold big_swap_perm at 2.
          simplify_bools_lia_one_kernel.
          unfold stack_biperms.
          do 2 simplify_bools_lia_one_kernel.
          rewrite Nat.add_sub.
          rewrite stack_perms_right, Nat.sub_0_r by 
            (destruct k as [|[]]; cbn; lia).
          unfold big_swap_perm.
          simplify_bools_lia_one_kernel.
          destruct k as [|[]]; [..|lia];
          cbn; bdestructΩ'.
        - unfold compose.
          rewrite (stack_perms_right (k:=k)) by lia.
          rewrite Nat.sub_0_r, Nat.add_0_r.
          unfold big_swap_perm at 2.
          do 2 simplify_bools_lia_one_kernel.
          unfold stack_biperms.
          do 2 simplify_bools_lia_one_kernel.
          rewrite Nat.sub_0_r, Nat.sub_add by lia.
          pose proof (Hgbdd k ltac:(lia)).
          rewrite stack_perms_right, Nat.sub_0_r, Nat.add_0_r by lia.
          unfold big_swap_perm.
          simplify_bools_lia_one_kernel.
          enough (g k <> 0 /\ g k <> 1) by lia.
          rewrite 2!(bipermutation_eq_iff _ _ Hg) by lia.
          lia.
      } 
  - revert Hb.
    unfold grow_NF_of_shrunken_biperm, 
      is_shrunken_representative,
      change_fun_to_shrink_biperm.
    bdestruct (m =? 0); bdestructΩ'; 
    intros ([Hl Hr] & Hbin & Hbout & Heq); 
    cbn; auto with perm_db.
  - revert Hb.
    unfold grow_NF_of_shrunken_biperm, 
      is_shrunken_representative,
      change_fun_to_shrink_biperm.
    bdestruct (m =? 0); bdestructΩ'; 
    intros ([Hl Hr] & Hbin & Hbout & Heq); 
    cbn; auto with perm_db.
  - revert Hb.
    unfold grow_NF_of_shrunken_biperm, 
      is_shrunken_representative,
      change_fun_to_shrink_biperm.
    bdestruct (m =? 0); bdestructΩ'; 
    intros ([Hl Hr] & Hbin & Hbout & Heq); 
    cbn; lia.
  - revert Hb.
    unfold grow_NF_of_shrunken_biperm, 
      is_shrunken_representative,
      change_fun_to_shrink_biperm.
    bdestruct (m =? 0); bdestructΩ'; 
    intros ([Hl Hr] & Hbin & Hbout & Heq); 
    cbn; lia.
Qed.



Fixpoint NF_of_biperm_rec (fuel : nat) (n m : nat) (f : nat -> nat) : 
  NF_biperm := 
  match fuel with 
  | 0 => empty_NF_biperm
  | S fuel' => 
    if m =? 0 then (* no inputs; simple case *)
    (
      if n =? 0 then (* no outputs; done *)
        empty_NF_biperm
      else (* make 0 go to 1 *)
        (* Have f 0 = 1 (better, f (m + 0) = m + 1) *)
        change_NF_from_shrink_biperm n m f ( 
        grow_NF_of_shrunken_biperm n m f (NF_of_biperm_rec fuel' (n - 2) 0
          (contract_biperm 0 1 (change_fun_to_shrink_biperm n m f f))))
      )
  (* if (n =? 0) || (m =? 0) then (fun g => g) else *)
  else if (f 0 <? m) then (* we want to prep to add a cap by moving f 0 to 1 *)
    (* Have f 0 = 1 (in the outputs), so need to extend with a 
      new cap and move it to the bottom of the ids *)
      change_NF_from_shrink_biperm n m f ( 
      grow_NF_of_shrunken_biperm n m f (NF_of_biperm_rec fuel' n (m - 2)
        (contract_biperm 0 1 (change_fun_to_shrink_biperm n m f f))))
  (* Can assume f 0 < m + n and, to lessen case analysis, won't add a check *)
  else (* make 0 go to m + n - 1 *)
    change_NF_from_shrink_biperm n m f ( 
    grow_NF_of_shrunken_biperm n m f (NF_of_biperm_rec fuel' (n - 1) (m - 1) 
      (contract_biperm 0 (m + n - 1) (change_fun_to_shrink_biperm n m f f))))
  end.


Lemma change_NF_from_shrink_biperm_is_rep n m f b 
  (Hf : bipermutation (m + n) f) 
  (Hb : is_NF_representative n m b (change_fun_to_shrink_biperm n m f f)) :
  is_NF_representative n m (change_NF_from_shrink_biperm n m f b) f.
Proof.
  split; [|split; [|split]].
  - apply change_NF_from_shrink_biperm_WF; 
    [apply Hf | apply Hb..].
  - unfold change_NF_from_shrink_biperm.
    bdestruct (m =? 0); bdestructΩ'; cbn; 
    apply Hb.
  - unfold change_NF_from_shrink_biperm.
    bdestruct (m =? 0); bdestructΩ'; cbn; 
    apply Hb.
  - rewrite realize_change_NF_from_shrink_biperm by (apply Hf + apply Hb).
    destruct Hb as (HbWF & Hbin & Hbout & Heq).
    erewrite change_fun_to_shrink_biperm_perm_eq_of_perm_eq by 
      (apply Heq + easy).
    now rewrite change_fun_to_shrink_biperm_involutive.
Qed.



Lemma NF_of_biperm_rec_spec fuel n m : 
  n + m <= 2 * fuel -> forall f, 
  bipermutation (m + n) f -> 
  is_NF_representative n m (NF_of_biperm_rec fuel n m f) f.
Proof.
  revert n m.
  induction fuel.
  1: {
    intros n m Hnm'.
    replace m with 0 by lia;
    replace n with 0 by lia.
    intros f Hf.
    apply empty_is_NF_rep_0_0.
  }
  intros n m Hnm f Hf.
  cbn.
  bdestruct (m =? 0); bdestructΩ'.
  - apply empty_is_NF_rep_0_0.
  - apply change_NF_from_shrink_biperm_is_rep; [easy|].
    apply grow_NF_of_shrunken_representative; [easy|].
    unfold is_shrunken_representative.
    do 2 simplify_bools_lia_one_kernel.
    apply IHfuel; [lia|].
    rewrite Nat.add_0_l.
    apply biperm_contract_case_1_bipermutation'; [|easy|].
    + apply (change_fun_to_shrink_biperm_preserves_biperm n 0); easy.
    + unfold change_fun_to_shrink_biperm. 
      do 2 simplify_bools_lia_one_kernel.
      pose proof (Hf 0).
      unfold compose.
      now rewrite (swap_perm_neither _ _ _ 0), swap_perm_right by lia.
  - apply change_NF_from_shrink_biperm_is_rep; [easy|].
    apply grow_NF_of_shrunken_representative; [easy|].
    unfold is_shrunken_representative.
    do 2 simplify_bools_lia_one_kernel.
    pose proof (Hf 0).
    apply IHfuel; [lia|].
    replace (m - 2 + n) with (m + n - 2) by lia.
    apply biperm_contract_case_1_bipermutation'; [|lia|].
    + now apply change_fun_to_shrink_biperm_preserves_biperm.
    + unfold change_fun_to_shrink_biperm.
      do 2 simplify_bools_lia_one_kernel.
      unfold compose.
      now rewrite (swap_perm_neither _ _ _ 0), swap_perm_right by lia.
  - apply change_NF_from_shrink_biperm_is_rep; [easy|].
    apply grow_NF_of_shrunken_representative; [easy|].
    unfold is_shrunken_representative.
    do 2 simplify_bools_lia_one_kernel.
    pose proof (Hf 0).
    apply IHfuel; [lia|].
    replace (m - 1 + (n - 1)) with (m + n - 2) by lia.
    apply biperm_contract_case_2_bipermutation'; [|lia|].
    + now apply change_fun_to_shrink_biperm_preserves_biperm.
    + unfold change_fun_to_shrink_biperm.
      do 3 simplify_bools_lia_one_kernel.
      unfold compose.
      now rewrite (swap_perm_neither _ _ _ 0), swap_perm_right by lia.
Qed.

Definition NF_of_biperm n m f :=
  NF_of_biperm_rec (n + m) n m f.

Lemma NF_of_biperm_spec n m f (Hf : bipermutation (m + n) f) : 
  is_NF_representative n m (NF_of_biperm n m f) f.
Proof.
  apply NF_of_biperm_rec_spec; [lia|easy].
Qed.

Lemma NF_of_biperm_WF n m f (Hf : bipermutation (m + n) f) : 
  WF_NF_biperm (NF_of_biperm n m f).
Proof. now apply NF_of_biperm_spec. Qed.

Lemma NF_insize_NF_of_biperm n m f (Hf : bipermutation (m + n) f) : 
  NF_insize (NF_of_biperm n m f) = n.
Proof. now apply NF_of_biperm_spec. Qed.

Lemma NF_outsize_NF_of_biperm n m f (Hf : bipermutation (m + n) f) : 
  NF_outsize (NF_of_biperm n m f) = m.
Proof. now apply NF_of_biperm_spec. Qed.

Lemma realize_NF_of_biperm n m f (Hf : bipermutation (m + n) f) : 
  perm_eq (m + n) (realize_NF_biperm (NF_of_biperm n m f)) f.
Proof. now apply NF_of_biperm_spec. Qed.
