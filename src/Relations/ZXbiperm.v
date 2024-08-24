Require Import Setoid.
Require Import CoreRules.
Import CoreData CoreAutomation.
Import CastRules.
From QuantumLib Require Import Bits.
Require Export QuantumLib.Permutations.
Import QuantumLib.VectorStates Modulus Kronecker.
Require Import NFBiperm.


(* Section ZX_biperm_foundations_extras *)

(* Not making these instances for performance and because these 
   definitions arefully internal and should not be used externally *)
Lemma change_NF_from_shrink_biperm_eq_of_perm_eq {n m} {f g} 
  (Hfg : perm_eq (m + n) f g) b : 
  change_NF_from_shrink_biperm n m f b = 
  change_NF_from_shrink_biperm n m g b.
Proof.
  unfold change_NF_from_shrink_biperm.
  repeat (apply f_equal_if_precedent_same; 
    rewrite ?Nat.eqb_eq, ?Nat.eqb_neq; intros; 
    rewrite ?Hfg by lia;
    try reflexivity).
Qed.

Lemma grow_NF_of_shrunken_biperm_eq_of_perm_eq {n m} {f g} 
  (Hfg : perm_eq (m + n) f g) b : 
  grow_NF_of_shrunken_biperm n m f b = 
  grow_NF_of_shrunken_biperm n m g b.
Proof.
  unfold grow_NF_of_shrunken_biperm.
  repeat (apply f_equal_if_precedent_same; 
    rewrite ?Nat.eqb_eq, ?Nat.eqb_neq; intros; 
    rewrite ?Hfg by lia;
    try reflexivity).
Qed.

(* TODO: Redefine change_fun_to_shrink_biperm 
  defensively to remove the bipermutation condition. 
  Should be sufficient to just test f 0 =? 0. *)
Lemma change_fun_to_shrink_biperm_perm_eq_of_perm_eq_perm_eq {n m}
  {f f'} (Hf : perm_eq (m + n) f f') {g g'} (Hg : perm_eq (m + n) g g') 
  (Hfbiperm : bipermutation (m + n) f) :
  perm_eq (m + n) (change_fun_to_shrink_biperm n m f g)
    (change_fun_to_shrink_biperm n m f' g').
Proof.
  unfold change_fun_to_shrink_biperm.
  bdestruct (m =? 0).
  - bdestructΩ'.
    pose proof (Hfbiperm 0 ltac:(lia)).
    rewrite <- Hf by lia.
    rewrite 2!compose_assoc.
    now rewrite Hg.
  - rewrite <- Hf by lia.
    bdestructΩ';
    rewrite 2!compose_assoc;
    pose proof (Hfbiperm 0 ltac:(lia)).
    + rewrite <- (stack_perms_WF_idn m n (swap_perm 1 _ _))
        by cleanup_perm_inv.
      now rewrite Hg.
    + now rewrite Hg.
Qed.

Lemma NF_of_biperm_rec_eq_of_perm_eq fuel : forall n m f g, 
  perm_eq (m + n) f g -> bipermutation (m + n) f ->
  NF_of_biperm_rec fuel n m f = NF_of_biperm_rec fuel n m g.
Proof.
  induction fuel; [easy|].
  intros n m f g Hfg Hf.
  cbn.
  bdestruct (m =? 0).
  - apply f_equal_if_precedent_same; [easy|].
    rewrite Nat.eqb_neq; intros Hn.
    rewrite (change_NF_from_shrink_biperm_eq_of_perm_eq Hfg).
    f_equal.
    rewrite (grow_NF_of_shrunken_biperm_eq_of_perm_eq Hfg).
    f_equal.
    apply IHfuel.
    + rewrite Nat.add_0_l.
      replace (n - 2) with (n - 1 - 1) by lia.
      bdestruct (n =? 1); [subst; intros k Hk; lia|].
      apply contract_perm_perm_eq_of_perm_eq; [lia|].
      apply contract_perm_perm_eq_of_perm_eq; [lia|].
      subst. 
      now apply (change_fun_to_shrink_biperm_perm_eq_of_perm_eq_perm_eq Hfg).
    (* + pose proof  *)
    Admitted.

    
    


(* Add Parametric Morphism n m : (NF_of_biperm n m)
  with signature perm_eq (m + n) ==> eq as NF_of_biperm_eq_of_perm_eq.
Proof.
  intros f g H *)


































