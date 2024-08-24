(** Matrix semantics of bipermutations and facts about them **)

(* Require Import ZXCore. *)
Require Import CoreRules.
Import CoreData CoreAutomation.
Import CastRules.
From QuantumLib Require Import Bits.
Require Export QuantumLib.Permutations.
Import QuantumLib.VectorStates Modulus Kronecker.
Require Export Bipermutations.

Open Scope prg.
Open Scope nat_scope.

(* Section BipermutationMatrices.v *)

Section VyZX_lemmas.

Import CoreData.

Lemma cap_semantics i j : 
  ⟦ ⊂ ⟧ i j =
  if j =? 0 then if i =? 0 then C1 else if i =? 3 then C1 else C0 else C0.
Proof.
  simpl.
  do 5 (try destruct i);
  destruct j; cbn; easy + destruct j; easy.
Qed.

Lemma cup_semantics i j : 
  ⟦ ⊃ ⟧ i j =
  if i =? 0 then if j =? 0 then C1 else if j =? 3 then C1 else C0 else C0.
Proof.
  simpl.
  do 5 (try destruct j);
  destruct i; cbn; easy + destruct i; easy.
Qed.

Lemma swap_cup : swap × (⟦ ⊂ ⟧) = (⟦ ⊂ ⟧).
Proof.
  change (2*2) with (2^2).
  apply mat_equiv_eq; [auto with wf_db..|].
  by_cell; cbn; lca.
Qed.

Lemma cap_times_cup : 
  (⟦ ⊃ ⟧) × (⟦ ⊂ ⟧) = 2%R .* I (2^0).
Proof.
  apply mat_equiv_eq; [auto with wf_db..].
  unfold scale.
  by_cell; cbv; lca.
Qed.

Lemma cap_cup_yank_eq : 
  I (2 ^ 1) ⊗ (⟦ ⊃ ⟧) × 
  ((⟦ ⊂ ⟧) ⊗ I (2 ^ 1)) = I (2^1).
Proof.
  apply mat_equiv_eq; [auto with wf_db..].
  rewrite kron_I_l, kron_I_r.
  by_cell; cbv; lca.
Qed.

Lemma cap_cap_cup_yank_eq : 
  (⟦ ⊃ ⟧) ⊗ (⟦ ⊃ ⟧) × 
  (I (2 ^ 1) ⊗ (⟦ ⊂ ⟧) ⊗ I (2 ^ 1)) = (⟦ ⊃ ⟧).
Proof.
  apply mat_equiv_eq; [auto using WF_Matrix_dim_change with wf_db..].
  rewrite kron_I_l, kron_I_r.
  by_cell; cbv; lca.
Qed.

Lemma cap_cup_yank_eq_alt : 
  (⟦ ⊃ ⟧) ⊗ I (2 ^ 1) × 
  (I (2 ^ 1) ⊗ (⟦ ⊂ ⟧)) = I (2^1).
Proof.
  apply mat_equiv_eq; [auto with wf_db..].
  rewrite kron_I_l, kron_I_r.
  by_cell; cbv; lca.
Qed.

End VyZX_lemmas.





Definition number_preserved (i : nat) (f : nat -> nat) (bound : nat) :=
  forallb (fun k => eqb (Nat.testbit i k) 
    (Nat.testbit i (f k))) (seq 0 bound).


Lemma number_preserved_iff_all_lt_eq ji nm f : 
  number_preserved ji f nm = true <->
  forall s, s < nm -> 
  Nat.testbit ji s = Nat.testbit ji (f s).
Proof.
  unfold number_preserved.
  rewrite <- Forall_forallb.
  2: (intros a; apply eq_eqb_iff). 
  rewrite Forall_seq.
  easy.
Qed.

Lemma number_preserved_iff j i n m (Hi : i < 2^n) f : 
  number_preserved (j * 2^n + i) f (n + m) = true <->
  forall s, s < (n + m) -> 
  if s <? n then
    if (f s) <? n then 
      Nat.testbit i s = Nat.testbit i (f s)
    else 
      Nat.testbit i s = Nat.testbit j (f s - n)
  else 
    if (f s) <? n then 
      Nat.testbit j (s - n) = Nat.testbit i (f s)
    else 
      Nat.testbit j (s - n) = Nat.testbit j (f s - n).
Proof.
  rewrite number_preserved_iff_all_lt_eq.
  apply forall_iff.
  intros s. 
  rewrite impl_iff.
  intros Hs.
  rewrite 2!testbit_add_pow2_split by easy.
  bdestructΩ'; easy.
Qed.

Lemma number_preserved_iff' i j n m (Hi : i < 2 ^ n) f : 
  number_preserved (j * 2 ^ n + i) f (m + n) = true <->
  (forall s : nat,
  s < m + n ->
  if s <? n
  then if f s <? n
    then Nat.testbit i s = Nat.testbit i (f s)
    else Nat.testbit i s = Nat.testbit j (f s - n)
  else if f s <? n
    then Nat.testbit j (s - n) = Nat.testbit i (f s)
    else Nat.testbit j (s - n) = Nat.testbit j (f s - n)).
Proof.
  rewrite (Nat.add_comm m n).
  now apply number_preserved_iff.
Qed.

(* TODO: Convert to perm_eq *)
Lemma number_preserved_eq_of_eq_on (ij n : nat) f g : 
  (forall i, i < n -> f i = g i) ->
  number_preserved ij f n = number_preserved ij g n.
Proof.
  intros Hfg.
  apply eq_iff_eq_true.
  rewrite 2!number_preserved_iff_all_lt_eq.
  apply forall_iff; intros s; apply impl_iff; intros Hs.
  setoid_rewrite Hfg; easy.
Qed.

Lemma number_preserved_funbool_to_nat f g n 
  (Hf : perm_bounded n f) : 
  number_preserved (funbool_to_nat n g) f n =
  forallb (fun k => eqb (g (n - S k)) (g (n - S (f k)))) (seq 0 n).
Proof.
  apply eq_iff_eq_true.
  rewrite forallb_seq0, number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_funbool_to_nat.
  setoid_rewrite <- eq_eqb_iff.
  apply forall_iff; intros s; apply impl_iff.
  intros Hs.
  replace_bool_lia (s <? n) true.
  specialize (Hf s Hs).
  replace_bool_lia (f s <? n) true.
  easy.
Qed.

Lemma number_preserved_idn (n : nat) {i j} (Hi : i < 2^n) (Hj : j < 2^n) : 
  number_preserved (j * 2 ^ n + i) (idn_biperm n) (n + n) = (i =? j).
Proof.
  rewrite eq_iff_eq_true.
  rewrite number_preserved_iff by easy.
  unfold idn_biperm.
  rewrite Nat.eqb_eq.
  split.
  - intros H.
    apply (bits_inj_upto_small i j n Hi Hj).
    intros s Hs.
    specialize (H s ltac:(lia)).
    revert H.
    bdestructΩ'.
    now rewrite add_sub'.
  - intros -> s Hs.
    bdestructΩ'; 
    now rewrite add_sub'.
Qed.



(* ORDERING: Bottom to top, outputs first. I.e., 
7  \/ —     3
6  /\ \/    2
5  —  /\ ╲  1
4  —  —  ╱  0
*)

Open Scope matrix_scope.

Definition matrix_of_biperm (n m : nat) (f : nat -> nat) : Matrix (2^m) (2^n) :=
  fun i j =>
  if 2^m <=? i then C0 else if 2^n <=? j then C0 else
  if number_preserved (j * 2^m + i) 
  (f) (n + m) then C1 else C0.
  (* this order works experimentally... :/ *)

Lemma matrix_of_biperm_WF n m f : 
  WF_Matrix (matrix_of_biperm n m f).
Proof.
  unfold matrix_of_biperm.
  intros i j.
  bdestructΩ'.
Qed.

Hint Resolve matrix_of_biperm_WF : wf_db.

(* TODO: Add Morphism instance *)
Lemma matrix_of_biperm_eq_of_perm_eq {n m f g}
  (H : perm_eq (n + m) f g) : 
  matrix_of_biperm n m f = matrix_of_biperm n m g.
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold matrix_of_biperm.
  do 2 simplify_bools_lia_one_kernel.
  now rewrite (number_preserved_eq_of_eq_on _ _ _ _ H).
Qed.

Lemma matrix_of_biperm_funbool_conj f g h n m :
  ((f_to_vec m g) ⊤ × matrix_of_biperm n m f × f_to_vec n h) 0 0 = 
  (if number_preserved (funbool_to_nat (n + m)
    (fun k => if k <? n then h k else g (k - n)))
    f (n + m) then 1%R else 0%R).
Proof.
  rewrite 2!basis_f_to_vec.
  rewrite matrix_conj_basis_eq_lt by apply funbool_to_nat_bound.
  unfold matrix_of_biperm.
  rewrite funbool_to_nat_add_pow2_join.
  pose proof (funbool_to_nat_bound m g).
  pose proof (funbool_to_nat_bound n h).
  bdestructΩ'.
Qed.

Lemma matrix_of_biperm_transpose n m f (Hf : bipermutation (n + m) f) : 
  (matrix_of_biperm m n f) ⊤ ≡
  (matrix_of_biperm n m (flip_biperm n m f)).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  intros i j Hi Hj.
  unfold Matrix.transpose.
  unfold matrix_of_biperm.
  do 2 simplify_bools_lia_one_kernel.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite 2!number_preserved_iff_all_lt_eq.
  setoid_rewrite testbit_add_pow2_split; [|easy..].
  split.
  - intros H s Hs.
    unfold flip_biperm.
    simplify_bools_lia_one_kernel.
    bdestruct (s <? m).
    + generalize (H (s + n) ltac:(lia)).
      pose proof (Hfbdd (s + n) ltac:(lia)).
      do 2 simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub.
      intros ->.
      bdestructΩ'.
      f_equal; lia.
    + generalize (H (s - m) ltac:(lia)).
      simplify_bools_lia_one_kernel.
      intros ->.
      pose proof (Hfbdd (s - m) ltac:(lia)).
      simplify_bools_lia_one_kernel.
      bdestructΩ'; f_equal; lia.
  - intros H s Hs.
    bdestruct (s <? n).
    + generalize (H (s + m) ltac:(lia)).
      pose proof (Hfbdd (s) ltac:(lia)).
      unfold flip_biperm.
      do 2 simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub.
      intros ->.
      bdestructΩ'.
      f_equal; lia.
    + generalize (H (s - n) ltac:(lia)).
      simplify_bools_lia_one_kernel.
      intros ->.
      pose proof (Hfbdd (s) ltac:(lia)).
      unfold flip_biperm.
      simplify_bools_lia_one_kernel.
      rewrite Nat.sub_add by lia.
      bdestructΩ'; f_equal; lia.
Qed.

Lemma matrix_of_biperm_transpose_eq n m f (Hf : bipermutation (n + m) f) : 
  (matrix_of_biperm m n f) ⊤ =
  (matrix_of_biperm n m (flip_biperm n m f)).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  now apply matrix_of_biperm_transpose.
Qed.

Lemma matrix_of_biperm_compose_perm_l n m f g
  (Hf : bipermutation (m + n) f)
  (Hg : permutation n g) : 
  matrix_of_biperm n m (biperm_compose_perm_r m n f g) ≡
  matrix_of_biperm n m f × 
  perm_to_matrix n (reflect_perm n ∘ perm_inv n g ∘ reflect_perm n)%prg.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (biperm_compose_perm_r_biperm _ _ f g Hf Hg) as Hfg.
  rewrite (Nat.add_comm m n) in *.
  pose proof (fun i Hi => proj1 (Hfg i Hi)) as Hfgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hfg i Hi))) as Hfgne.
  pose proof (fun i Hi => proj2 (proj2 (Hfg i Hi))) as Hfgeq.
  pose proof (perm_inv_permutation n g Hg) as Hginv.
  pose proof (perm_inv_bounded n g) as Hginvbdd.
  pose proof (perm_inv_is_linv_of_permutation n g Hg) as Hglinv.
  pose proof (perm_inv_is_rinv_of_permutation n g Hg) as Hgrinv.
  pose proof (permutation_compose _ _ _ 
    (permutation_compose _ _ _ (reflect_perm_permutation n) Hginv)
    (reflect_perm_permutation n)) as Hgreflperm.
  pose proof (permutation_is_bounded _ _ Hgreflperm) as Hgreflbdd.
  unfold Basics.compose in *.

  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite matrix_of_biperm_funbool_conj.
  rewrite 2!Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits by easy.
  rewrite <- Mmult_assoc.
  rewrite matrix_of_biperm_funbool_conj.
  apply f_equal_if; [|easy..].
  rewrite <- 2!funbool_to_nat_add_pow2_join.
  rewrite (Nat.add_comm n m).
  apply eq_iff_eq_true; 
  rewrite 2!number_preserved_iff by apply funbool_to_nat_bound. 
  rewrite (Nat.add_comm m n).
  rewrite !nat_to_funbool_inverse by easy.
  do 3 setoid_rewrite testbit_funbool_to_nat.
  etransitivity.
  1: {
    apply forall_iff; intros s.
    apply impl_iff; intros Hs.
    instantiate (1 := (if s <? m then if f s <? m then _ else _ 
      else if f (m + g (s - m)) <? m then _ else _)).
    bdestruct (s <? m).
    - rewrite biperm_compose_perm_r_ltb_small by easy.
      bdestruct (f s <? m); unfold biperm_compose_perm_r; simplify_bools_lia;
      rewrite ?add_sub'; reflexivity.
    - rewrite biperm_compose_perm_r_ltb_big by lia.
      bdestruct (f (m + g (s - m)) <? m); unfold biperm_compose_perm_r; 
      simplify_bools_lia; rewrite ?add_sub'; reflexivity.
  }
  etransitivity.
  2: {
    symmetry.
    apply forall_iff; intros s.
    apply impl_iff; intros Hs.
    instantiate (1 := (if s <? m then if f s <? m then _ else _ 
      else if f s <? m then _ else _)).
    bdestruct (s <? m).
    - rewrite nat_to_funbool_eq.
      bdestruct (f s <? m); [reflexivity|].
      pose proof (Hfbdd s Hs).
      unfold reflect_perm.
      simplify_bools_lia.
      match goal with
      |- context[ n - S (n - S ?k) ] => 
        replace (n - S (n - S k)) with k by lia
      end.
      pose proof (Hginvbdd (f s - m) ltac:(lia)).
      do 2 simplify_bools_lia_one_kernel.
      match goal with
      |- context[ n - S (n - S ?k) ] => 
        replace (n - S (n - S k)) with k by lia
      end.
      reflexivity.
    - rewrite 2!nat_to_funbool_eq'.
      unfold reflect_perm.
      simplify_bools_lia.
      pose proof (Hfbdd s Hs).
      do 2 match goal with
      |- context[ n - S (n - S ?k) ] => 
        replace (n - S (n - S k)) with k by lia
      end.
      pose proof (Hginvbdd (s - m)).
      pose proof (Hginvbdd (f s - m)).
      do 5 simplify_bools_lia_one_kernel.
      do 2 match goal with
      |- context[ n - S (n - S ?k) ] => 
        replace (n - S (n - S k)) with k by lia
      end.
      reflexivity.
  } 
  split.
  - intros H s Hs.
    pose proof (Hfbdd s Hs).
    bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'.
    + generalize (H (f s) (Hfbdd s Hs)).
      bdestructΩ'; rewrite ?Hfeq in * by lia; try lia.
      easy.
    + generalize (H (perm_inv n g (s - m) + m) 
      ltac:(pose (Hginvbdd (s - m)); lia)).
      simplify_bools_lia.
      rewrite Nat.add_sub.
      rewrite Hgrinv by lia.
      rewrite Nat.add_sub_assoc, add_sub' by lia.
      now simplify_bools_lia_one_kernel.
  - intros H s Hs.
    pose proof (Hfbdd s Hs).
    bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'.
    + pose proof (Hgbdd (s - m) ltac:(lia)).
      pose proof (Hfbdd (m + g (s - m)) ltac:(lia)).
      generalize (H (f (m + g (s - m))) ltac:(easy)).
      bdestructΩ'; rewrite ?Hfeq in * by lia; try lia.
      rewrite add_sub', Hglinv by lia.
      easy.
    + pose proof (Hgbdd (s - m) ltac:(lia)).
      generalize (H (m + g (s - m)) ltac:(lia)).
      simplify_bools_lia.
      rewrite add_sub'.
      now rewrite Hglinv by lia.
Qed.

Lemma matrix_of_biperm_compose_perm_r n m f g
  (Hf : bipermutation (m + n) f)
  (Hg : permutation m g) : 
  matrix_of_biperm n m (biperm_compose_perm_l m n f g) ≡
  perm_to_matrix m (reflect_perm m ∘ g ∘ reflect_perm m)%prg ×
  matrix_of_biperm n m f.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (permutation_is_bounded _ _ Hg) as Hgbdd.
  pose proof (biperm_compose_perm_l_biperm _ _ f g Hf Hg) as Hfg.
  rewrite (Nat.add_comm m n) in *.
  pose proof (fun i Hi => proj1 (Hfg i Hi)) as Hfgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hfg i Hi))) as Hfgne.
  pose proof (fun i Hi => proj2 (proj2 (Hfg i Hi))) as Hfgeq.
  pose proof (perm_inv_permutation m g Hg) as Hginv.
  pose proof (perm_inv_bounded m g) as Hginvbdd.
  pose proof (perm_inv_is_linv_of_permutation m g Hg) as Hglinv.
  pose proof (perm_inv_is_rinv_of_permutation m g Hg) as Hgrinv.
  pose proof (permutation_compose _ _ _ 
    (permutation_compose _ _ _ (reflect_perm_permutation m) Hg)
    (reflect_perm_permutation m)) as Hgreflperm.
  pose proof (permutation_is_bounded _ _ Hgreflperm) as Hgreflbdd.
  unfold Basics.compose in *.

  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite 2!basis_f_to_vec_alt by easy.
  rewrite matrix_of_biperm_funbool_conj.
  rewrite <- Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits_l by easy.
  erewrite f_to_vec_eq.
  2: {
    intros k Hk.
    rewrite perm_inv_compose_alt by 
      (try apply permutation_compose; auto with perm_db).
    rewrite perm_inv_compose_alt by auto with perm_db perm_bounded_db.
    rewrite (reflect_perm_inv m k) by easy.
    rewrite reflect_perm_inv by auto with perm_db perm_bounded_db.
    reflexivity.
  }
  rewrite matrix_of_biperm_funbool_conj.
  apply f_equal_if; [|easy..].
  rewrite <- funbool_to_nat_add_pow2_join.
  rewrite <- (funbool_to_nat_add_pow2_join _ _ (
    fun x => nat_to_funbool m i (reflect_perm m 
      (perm_inv m g (reflect_perm m x)))
  )).
  rewrite (Nat.add_comm n m).
  apply eq_iff_eq_true; 
  rewrite 2!number_preserved_iff by apply funbool_to_nat_bound. 
  rewrite (Nat.add_comm m n).
  rewrite !nat_to_funbool_inverse by easy.
  do 3 setoid_rewrite testbit_funbool_to_nat.
  etransitivity.
  1: {
    apply forall_iff; intros s.
    apply impl_iff; intros Hs.
    instantiate (1 := (if s <? m then if f (g s) <? m then _ else _ 
      else if f s <? m then _ else _)).
    bdestruct (s <? m).
    - rewrite biperm_compose_perm_l_ltb_small by easy.
      bdestruct (f (g s) <? m); unfold biperm_compose_perm_l; simplify_bools_lia;
      reflexivity.
    - rewrite biperm_compose_perm_l_ltb_big by lia.
      bdestruct (f s <? m); unfold biperm_compose_perm_l; 
      simplify_bools_lia; reflexivity.
  }
  etransitivity.
  2: {
    symmetry.
    apply forall_iff; intros s.
    apply impl_iff; intros Hs.
    instantiate (1 := (if s <? m then if f s <? m then _ else _ 
      else if f s <? m then _ else _)).
    bdestruct (s <? m).
    - rewrite nat_to_funbool_eq.
      unfold reflect_perm.
      do 2 simplify_bools_lia_one_kernel.
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      pose proof (Hginvbdd s ltac:(lia)).
      do 2 simplify_bools_lia_one_kernel.
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      bdestruct (f s <? m); [|reflexivity].
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      pose proof (Hginvbdd (f s)) ltac:(lia).
      do 2 simplify_bools_lia_one_kernel.
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      reflexivity.
    - rewrite nat_to_funbool_eq'.
      bdestruct (f s <? m); [|reflexivity].
      unfold reflect_perm.
      simplify_bools_lia.
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      pose proof (Hginvbdd (f s)).
      do 2 simplify_bools_lia_one_kernel.
      match goal with
      |- context[ m - S (m - S ?k) ] => 
        replace (m - S (m - S k)) with k by lia
      end.
      reflexivity.
  } 
  split.
  - intros H s Hs.
    pose proof (Hfbdd s Hs).
    bdestruct (s <? m).
    + pose proof (Hginvbdd s ltac:(lia)).
      generalize (H (perm_inv m g s) ltac:(lia)).
      rewrite Hgrinv by lia.
      bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'. 
  - intros H s Hs.
    pose proof (Hfbdd s Hs).
    bdestruct (s <? m).
    + pose proof (Hgbdd s ltac:(lia)).
      generalize (H (g s) ltac:(lia)).
      rewrite Hglinv by lia.
      bdestructΩ'.
    + generalize (H s Hs).
      bdestructΩ'.
Qed.

Local Open Scope prg.

Lemma matrix_of_biperm_compose_perm_l_eq n m f g 
  (Hf : bipermutation (m + n) f)
  (Hg : permutation n g) : 
  matrix_of_biperm n m (biperm_compose_perm_r m n f g) = 
  matrix_of_biperm n m f × 
    perm_to_matrix n (reflect_perm n ∘ perm_inv' n g ∘ reflect_perm n).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  rewrite matrix_of_biperm_compose_perm_l by easy.
  Morphisms.f_equiv.
  apply perm_to_matrix_eq_of_perm_eq.
  apply perm_eq_compose_proper;
  cleanup_perm.
Qed.

Lemma matrix_of_biperm_compose_perm_r_eq n m f g 
  (Hf : bipermutation (m + n) f)
  (Hg : permutation m g) : 
  matrix_of_biperm n m (biperm_compose_perm_l m n f g) = 
  perm_to_matrix m (reflect_perm m ∘ g ∘ reflect_perm m) 
    × matrix_of_biperm n m f.
Proof.
  apply mat_equiv_eq; auto with wf_db.
  now apply matrix_of_biperm_compose_perm_r.
Qed.

Lemma matrix_of_biperm_Mmult_perm_r_eq n m f g 
  (Hf : bipermutation (m + n) f)
  (Hg : permutation n g) : 
  matrix_of_biperm n m f × perm_to_matrix n g = 
  matrix_of_biperm n m 
    (biperm_compose_perm_r m n f 
      (reflect_perm n ∘ perm_inv' n g ∘ reflect_perm n)).
Proof.
  rewrite matrix_of_biperm_compose_perm_l_eq by auto with perm_db.
  f_equal.
  rewrite !perm_inv'_compose by auto with perm_db.
  apply perm_to_matrix_eq_of_perm_eq.
  rewrite !compose_assoc.
  cleanup_perm.
Qed.


Lemma matrix_of_biperm_pow_2_l n m f 
  (Hf : bipermutation (n + m) f) k : 
  matrix_of_biperm n m f 0 (2^k) = 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  unfold matrix_of_biperm.
  simplify_bools_moddy_lia_one_kernel.
  bdestruct_one; [easy|].
  apply if_false.
  rewrite <- Nat.pow_add_r, Nat.add_0_r.
  rewrite <- not_true_iff_false.
  rewrite number_preserved_iff_all_lt_eq.
  intros Hcontra.
  bdestruct (k <? n); 
  [|pose proof (Nat.pow_le_mono_r 2 n k); lia].
  specialize (Hcontra (k + m) ltac:(lia)).
  rewrite 2!Nat.pow2_bits_eqb in Hcontra.
  pose proof (Hfne (k + m) ltac:(lia)).
  revert Hcontra.
  bdestructΩ'.
Qed.

Lemma matrix_of_biperm_pow_2_r n m f 
  (Hf : bipermutation (n + m) f) k : 
  matrix_of_biperm n m f (2^k) 0 = 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  unfold matrix_of_biperm.
  simplify_bools_moddy_lia_one_kernel.
  bdestruct_one; [easy|].
  apply if_false.
  rewrite <- not_true_iff_false.
  rewrite number_preserved_iff_all_lt_eq.
  intros Hcontra.
  bdestruct (k <? m); 
  [|pose proof (Nat.pow_le_mono_r 2 m k); lia].
  specialize (Hcontra (k) ltac:(lia)).
  rewrite 2!Nat.pow2_bits_eqb in Hcontra.
  pose proof (Hfne (k) ltac:(lia)).
  revert Hcontra.
  bdestructΩ'.
Qed.



Lemma matrix_of_biperm_sum_pows_2_l_l n m f 
  (Hf : bipermutation (n + m) f) k l : k < n -> l < n ->
  matrix_of_biperm n m f 0 (2^k + 2^l) =
  if f (m + k) =? m + l then C1 else 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  intros Hk Hl.
  bdestruct (k =? l).
  1:{
    replace (2 ^ k + 2 ^ l) with (2 ^ (S k)) by (cbn; subst; lia).
    rewrite matrix_of_biperm_pow_2_l by easy. 
    pose proof (Hfne (m + l)); bdestructΩ'.
  }
  unfold matrix_of_biperm.
  simplify_bools_moddy_lia_one_kernel.
  bdestruct_one.
  - pose proof (Nat.pow_le_mono_r 2 k (n - 1) ltac:(lia) ltac:(lia)).
    pose proof (Nat.pow_le_mono_r 2 l (n - 1) ltac:(lia) ltac:(lia)).
    destruct n; [easy|].
    simpl in *.
    rewrite Nat.sub_0_r, Nat.add_0_r in *.
    assert (Hkl : 2 ^ k = 2 ^ l) by lia.
    apply (f_equal (Nat.log2)) in Hkl.
    rewrite 2!Nat.log2_pow2 in Hkl by lia.
    pose proof (Hfne k).
    bdestructΩ'.
  - apply f_equal_if; [|easy..].
    apply eq_iff_eq_true.
    rewrite (Nat.add_comm n m), number_preserved_iff by show_nonzero.
    rewrite Nat.eqb_eq.
    split.
    + intros Hall.
      generalize (Hall (m + k) ltac:(lia)).
      simplify_bools_lia.
      rewrite add_sub'.
      rewrite !testbit_sum_pows_2_ne by easy.
      rewrite Nat.bits_0.
      pose proof (Hfne (m + k) ltac:(lia)).
      bdestructΩ'simp.
    + intros Hfmk.
      pose proof (proj1 (bipermutation_eq_iff (m+k) (m+l) Hf
        ltac:(lia) ltac:(lia)) ltac:(lia)) as Hfml.
      intros s Hs.
      rewrite !testbit_sum_pows_2_ne by easy.
      rewrite !Nat.bits_0.
      bdestruct (s <? m); bdestruct (f s <? m);
      [pose proof (bipermutation_eq_iff s (m+l) Hf ltac:(lia) ltac:(lia)); 
        pose proof (bipermutation_eq_iff (m+k) s Hf ltac:(lia) ltac:(lia));
      bdestructΩ'..|].
      replace_bool_lia (f s - m =? k) (f s =? m + k).
      replace_bool_lia (f s - m =? l) (f s =? m + l).
      rewrite 2!(bipermutation_eqb_iff _ _ Hf) by lia.
      rewrite Hfmk, <- Hfml.
      bdestructΩ'.
Qed.



Lemma matrix_of_biperm_sum_pows_2_r_r n m f 
  (Hf : bipermutation (n + m) f) k l : k < m -> l < m ->
  matrix_of_biperm n m f (2^k + 2^l) 0 =
  if f k =? l then C1 else 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  intros Hk Hl.
  bdestruct (k =? l).
  1:{
    replace (2 ^ k + 2 ^ l) with (2 ^ (S k)) by (cbn; subst; lia).
    rewrite matrix_of_biperm_pow_2_r by easy. 
    pose proof (Hfne k); bdestructΩ'.
  }
  unfold matrix_of_biperm.
  simplify_bools_moddy_lia_one_kernel.
  pose proof (sum_ne_pows_2_lt_pow_2_S m k l).
  simplify_bools_lia_one_kernel.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite (Nat.add_comm n m), number_preserved_iff_all_lt_eq.
  rewrite Nat.eqb_eq.
  split.
  - intros Hall.
    generalize (Hall k ltac:(lia)).
    simplify_bools_lia.
    rewrite !testbit_sum_pows_2_ne by easy.
    pose proof (Hfne (k) ltac:(lia)).
    bdestructΩ'simp.
  - intros Hfmk.
    pose proof (proj1 (bipermutation_eq_iff (k) (l) Hf
      ltac:(lia) ltac:(lia)) ltac:(lia)) as Hfml.
    intros s Hs.
    rewrite !testbit_sum_pows_2_ne by easy.
    rewrite 2!(bipermutation_eqb_iff _ _ Hf) by lia.
    bdestructΩ'.
Qed.

Lemma matrix_of_biperm_sum_pows_2_l_r n m f 
  (Hf : bipermutation (n + m) f) k l : k < m -> l < n ->
  matrix_of_biperm n m f (2^k) (2^l) =
  if f k =? m + l then C1 else 0%R.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  intros Hk Hl.
  unfold matrix_of_biperm.
  pose proof (Nat.pow_lt_mono_r 2 k m ltac:(lia) ltac:(lia)).
  pose proof (Nat.pow_lt_mono_r 2 l n ltac:(lia) ltac:(lia)).
  do 2 simplify_bools_lia_one_kernel.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite (Nat.add_comm n m), number_preserved_iff by easy.
  rewrite Nat.eqb_eq.
  split.
  - intros Hall.
    generalize (Hall k ltac:(lia)).
    simplify_bools_lia.
    rewrite !Nat.pow2_bits_eqb.
    pose proof (Hfne (k) ltac:(lia)).
    bdestructΩ'simp.
  - intros Hfmk.
    pose proof (proj1 (bipermutation_eq_iff (k) (m+l) Hf
      ltac:(lia) ltac:(lia)) ltac:(lia)) as Hfml.
    intros s Hs.
    rewrite !Nat.pow2_bits_eqb by easy.
    pose proof (bipermutation_eq_iff s (m+l) Hf ltac:(lia) ltac:(lia)).
    pose proof (bipermutation_eq_iff k s Hf ltac:(lia) ltac:(lia)).
    bdestructΩ'.
Qed.

Lemma matrix_of_biperm_inj n m f g 
  (Hf : bipermutation (n + m) f) (Hg : bipermutation (n + m) g) : 
  matrix_of_biperm n m f ≡ matrix_of_biperm n m g ->
  perm_eq (n + m) f g.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (fun i Hi => proj1 (Hg i Hi)) as Hgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hg i Hi))) as Hgne.
  pose proof (fun i Hi => proj2 (proj2 (Hg i Hi))) as Hgeq.
  intros Hequiv k Hk.
  bdestruct (k <? m); bdestruct (f k <? m).
  - pose proof (Hfne k Hk).
    generalize (Hequiv (2^k + 2^(f k)) 0 
      ltac:(apply sum_ne_pows_2_lt_pow_2_S; lia) ltac:(show_nonzero)).
    rewrite 2!matrix_of_biperm_sum_pows_2_r_r by easy.
    simplify_bools_lia_one_kernel.
    bdestructΩ'.
    pose proof C1_nonzero. congruence.
  - pose proof (Hfbdd k Hk).
    generalize (Hequiv (2^k) (2^(f k - m))
      ltac:(apply Nat.pow_lt_mono_r; lia) 
      ltac:(apply Nat.pow_lt_mono_r; lia)).
    rewrite 2!matrix_of_biperm_sum_pows_2_l_r by easy + lia.
    bdestructΩ'.
    pose proof C1_nonzero; congruence.
  - pose proof (Hfbdd k Hk).
    generalize (Hequiv (2^(f k)) (2^(k - m))
      ltac:(apply Nat.pow_lt_mono_r; lia) 
      ltac:(apply Nat.pow_lt_mono_r; lia)).
    rewrite 2!matrix_of_biperm_sum_pows_2_l_r by easy + lia.
    replace (m + (k - m)) with k by lia.
    rewrite Hfeq by lia.
    rewrite (bipermutation_eqb_iff _ _ Hg) by lia.
    bdestructΩ'; 
    pose proof C1_nonzero; congruence.
  - pose proof (Hfne k Hk).
    pose proof (Hfbdd k Hk).
    generalize (Hequiv 0 (2^(k-m) + 2^(f k - m))
      ltac:(show_nonzero) ltac:(apply sum_ne_pows_2_lt_pow_2_S; lia)).
    rewrite 2!matrix_of_biperm_sum_pows_2_l_l by easy + lia.
    replace (m + (k - m)) with k by lia.
    replace (m + (f k - m)) with (f k) by lia.
    bdestructΩ'.
    pose proof C1_nonzero. 
    congruence.
Qed.

Lemma matrix_of_stack_biperms n0 m0 n1 m1 f g 
  (Hf : bipermutation (n0 + m0) f)
  (Hg : bipermutation (n1 + m1) g) : 
  matrix_of_biperm (n0 + n1) (m0 + m1) (stack_biperms m0 n0 m1 n1 f g) =
  matrix_of_biperm n1 m1 g ⊗ matrix_of_biperm n0 m0 f.
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  pose proof (fun i Hi => proj1 (Hg i Hi)) as Hgbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hg i Hi))) as Hgne.
  pose proof (fun i Hi => proj2 (proj2 (Hg i Hi))) as Hgeq.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold kron.
  unfold matrix_of_biperm.
  do 6 simplify_bools_moddy_lia_one_kernel.
  rewrite Cmult_if_if_1_l.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true;
  rewrite andb_true_iff.
  rewrite !number_preserved_iff' by show_moddy_lt.
  split.
  - intros H.
    split.
    + intros s Hs.
      rewrite !testbit_div_pow2.
      bdestruct (s <? m1).
      * generalize (H (m0 + s) ltac:(lia)).
        simplify_bools_lia_one_kernel.
        unfold stack_biperms.
        rewrite add_sub'.
        do 3 simplify_bools_lia_one_kernel.
        pose proof (Hgbdd s ltac:(lia)).
        bdestructΩ'; intros ->; f_equal; lia.
      * generalize (H (m0 + n0 + s) ltac:(lia)).
        simplify_bools_lia_one_kernel.
        unfold stack_biperms.
        rewrite add_sub'.
        do 4 simplify_bools_lia_one_kernel.
        replace (m0 + n0 + s - (m0 + m1)) with (n0 + s - m1) by lia.
        rewrite Nat.add_sub_assoc by lia.
        bdestructΩ'; intros ->; f_equal; lia.
    + intros s Hs.
      rewrite !testbit_mod_pow2.
      bdestruct (s <? m0).
      * generalize (H (s) ltac:(lia)).
        simplify_bools_lia_one_kernel.
        unfold stack_biperms.
        do 2 simplify_bools_lia_one_kernel.
        pose proof (Hfbdd s ltac:(lia)).
        bdestructΩ'; intros ->; f_equal; lia.
      * simplify_bools_lia_one_kernel.
        generalize (H (m1+s) ltac:(lia)).
        simplify_bools_lia_one_kernel.
        unfold stack_biperms.
        do 4 simplify_bools_lia_one_kernel.
        rewrite add_sub'.
        replace (m1 + s - (m0 + m1)) with (s - m0) by lia.
        pose proof (Hfbdd s).
        bdestructΩ'; intros ->; f_equal; lia.
  - intros [Hhigh Hlow].
    intros s Hs.
    bdestruct (s <? m0 + m1);
    [bdestruct (s <? m0) | bdestruct (s <? m0 + m1 + n0)].
    + generalize (Hlow s ltac:(lia)).
      rewrite !testbit_mod_pow2.
      simplify_bools_lia_one_kernel.
      pose proof (Hfbdd s).
      bdestruct_one; intros ->; 
      unfold stack_biperms; bdestructΩ'; f_equal; lia.
    + generalize (Hhigh (s - m0) ltac:(lia)).
      rewrite !testbit_div_pow2.
      simplify_bools_lia_one_kernel.
      rewrite Nat.add_sub_assoc, add_sub' by lia.
      pose proof (Hgbdd (s - m0)).
      bdestruct_one; intros ->; 
      unfold stack_biperms; bdestructΩ'; f_equal; lia.
    + generalize (Hlow (s - m1) ltac:(lia)).
      rewrite !testbit_mod_pow2.
      do 2 simplify_bools_lia_one_kernel.
      replace (s - m1 - m0) with (s - (m0 + m1)) by lia.
      pose proof (Hfbdd (s - m1)).
      bdestruct_one; intros ->; 
      unfold stack_biperms; bdestructΩ'; f_equal; lia.
    + generalize (Hhigh (s - (n0 + m0)) ltac:(lia)).
      rewrite !testbit_div_pow2.
      simplify_bools_lia_one_kernel.
      replace (n0 + (s - (n0 + m0) - m1)) with (s - (m0 + m1)) by lia.
      pose proof (Hgbdd (s - (m0 + n0))).
      bdestruct_one; intros ->;
      unfold stack_biperms; bdestructΩ';
      rewrite ?(Nat.add_comm n0 m0) in *; f_equal; lia.
Qed.

Lemma matrix_of_stack_biperms' (n0 m0 n1 m1 n01 m01 : nat) (f g : nat -> nat)
  (Hf : bipermutation (n0 + m0) f)
  (Hg : bipermutation (n1 + m1) g)
  (Hn01 : n0 + n1 = n01) (Hm01 : m01 = m0 + m1) :
  matrix_of_biperm n01 m01 (stack_biperms m0 n0 m1 n1 f g) =
  matrix_of_biperm n1 m1 g ⊗ matrix_of_biperm n0 m0 f.
Proof.
  subst.
  now apply matrix_of_stack_biperms.
Qed.

Lemma matrix_of_idn_biperm n : 
  matrix_of_biperm n n (idn_biperm n) = I (2 ^ n).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold matrix_of_biperm, I.
  simplify_bools_lia.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite Nat.eqb_eq, <- bits_inj_upto_small by eauto.
  rewrite number_preserved_iff by easy.
  split.
  - intros H s Hs.
    generalize (H s ltac:(lia)).
    unfold idn_biperm.
    simplify_bools_lia.
    intros ->; f_equal; lia.
  - intros H s Hs.
    unfold idn_biperm.
    simplify_bools_lia.
    bdestructΩ'; rewrite H; f_equal; lia.
Qed.

Lemma matrix_of_biperm_0_0 f : 
  matrix_of_biperm 0 0 f = I 1.
Proof.
  apply mat_equiv_eq; auto with wf_db.
  simpl.
  intros [] [] Hi Hj; (easy + lia).
Qed.

Lemma matrix_of_biperm_n_m_cup_cap_0_l ncap : 
  matrix_of_biperm 0 (ncap + ncap) (n_m_cup_cap 0 ncap) =
  (ncap ⨂ ⟦⊂⟧).
Proof.
  induction ncap; [simpl; now rewrite matrix_of_biperm_0_0|].
  rewrite n_m_cup_cap_comm.
  change 0 with (0 + 0) at 5.
  replace (S ncap + S ncap) with ((1 + 1) + (ncap + ncap)) by lia.
  replace (S ncap) with (1 + ncap) by lia.
  rewrite n_m_cup_cap_plus_plus_decomp.
  rewrite 2!(n_m_cup_cap_comm _ 0).
  pose proof (matrix_of_stack_biperms (0+0) (1+1) (0+0) (ncap + ncap)
    (n_m_cup_cap 0 1) (n_m_cup_cap 0 ncap)
    ltac:(auto with biperm_db)
    ltac:(auto with biperm_db)) as Hrw.
  change 0 with (0 + 0 + (0 + 0)) at 6.
  rewrite Hrw.
  clear Hrw.
  change (1 + ncap) with (S ncap).
  cbn [kron_n].
  f_equal;
  [rewrite <- Nat.pow_mul_r; f_equal; lia..|apply IHncap |].
  apply mat_equiv_eq; auto with wf_db.
  by_cell; reflexivity.
Qed.

Lemma matrix_of_biperm_n_m_cup_cap_0_r ncup : 
  matrix_of_biperm (ncup + ncup) 0 (n_m_cup_cap ncup 0) =
  (ncup ⨂ ⟦⊃⟧).
Proof.
  induction ncup; [simpl; now rewrite matrix_of_biperm_0_0|].
  rewrite n_m_cup_cap_comm.
  change 0 with (0 + 0) at 5.
  replace (S ncup + S ncup) with ((1 + 1) + (ncup + ncup)) by lia.
  replace (S ncup) with (1 + ncup) by lia.
  rewrite n_m_cup_cap_plus_plus_decomp.
  (* rewrite 2!(n_m_cup_cap_comm 0 _). *)
  pose proof (matrix_of_stack_biperms (1+1) (0+0) (ncup + ncup) (0+0)
    (n_m_cup_cap 0 1) (n_m_cup_cap 0 ncup)
    ltac:(auto with biperm_db)
    ltac:(auto with biperm_db)) as Hrw.
  change 0 with (0 + 0 + (0 + 0)) at 8.
  rewrite Hrw.
  clear Hrw.
  change (1 + ncup) with (S ncup).
  cbn [kron_n].
  f_equal;
  [rewrite <- Nat.pow_mul_r; f_equal; lia..|
    rewrite n_m_cup_cap_comm; apply IHncup |].
  apply mat_equiv_eq; auto with wf_db.
  by_cell; reflexivity.
Qed.

Lemma matrix_of_biperm_n_m_cup_cap_split ncup ncap : 
  matrix_of_biperm (ncup + ncup) (ncap + ncap) (n_m_cup_cap ncup ncap) =
  matrix_of_biperm 0 (ncap + ncap) (n_m_cup_cap 0 ncap) ×
  matrix_of_biperm (ncup + ncup) 0 (n_m_cup_cap ncup 0).
Proof.
  rewrite n_m_cup_cap_stack_biperms_decomp.
  pose proof (matrix_of_stack_biperms 0 (ncap + ncap) (ncup + ncup) 0
    (n_m_cup_cap 0 ncap) (n_m_cup_cap ncup 0) 
    ltac:(auto with biperm_db)
    ltac:(auto with biperm_db)) as Hrw.
  rewrite Nat.add_0_r, Nat.add_0_l in Hrw.
  rewrite Hrw.
  clear Hrw.
  rewrite kron_split_antidiag by auto with wf_db.
  change (2^0) with 1.
  now rewrite kron_1_l, kron_1_r by (change 1 with (2^0); auto with wf_db).
Qed.

Lemma matrix_of_biperm_n_m_cup_cap ncup ncap : 
  matrix_of_biperm (ncup + ncup) (ncap + ncap) (n_m_cup_cap ncup ncap) =
  @Mmult (2^(ncap + ncap)) (2^0) (2^(ncup + ncup)) 
    (ncap ⨂ ⟦⊂⟧) (ncup ⨂ ⟦⊃⟧).
Proof.
  rewrite matrix_of_biperm_n_m_cup_cap_split.
  now rewrite 
    matrix_of_biperm_n_m_cup_cap_0_l,
    matrix_of_biperm_n_m_cup_cap_0_r.
Qed.

Lemma n_m_cup_cap_times_cup_r n m (Hn : n <> 0) : 
  matrix_of_biperm (n + n) (m + m) (n_m_cup_cap n m) 
  × (⟦ ⊂ ⟧ ⊗ I (2 ^ (n + n - 2))) = 2%R .*
  matrix_of_biperm ((n - 1) + (n - 1)) (m + m) (n_m_cup_cap (n-1) m).
Proof.
  rewrite n_m_cup_cap_comm.
  replace (n_m_cup_cap m n) with 
    (n_m_cup_cap (m + 0) ((n - 1) + 1)) by (f_equal; lia).
  rewrite n_m_cup_cap_plus_plus_decomp.
  replace (matrix_of_biperm (n + n) (m + m)) with
    (matrix_of_biperm ((n-1 + (n-1)) + (1 + 1)) ((m + m) + (0 + 0)))
    by (f_equal; lia).
  rewrite matrix_of_stack_biperms by auto with biperm_db.
  restore_dims.
  rewrite kron_mixed_product' by (f_equal; lia).
  rewrite n_m_cup_cap_comm.
  rewrite matrix_of_biperm_n_m_cup_cap_0_r.
  rewrite kron_n_1 by auto with wf_db.
  restore_dims.
  rewrite cap_times_cup, Mmult_1_r by auto with wf_db.
  rewrite Mscale_kron_dist_l.
  rewrite kron_1_l by auto with wf_db.
  restore_dims.
  now rewrite n_m_cup_cap_comm.
Qed.

Lemma n_m_cup_cap_times_up_cup_r n m (Hn : 1 < n) : 
  matrix_of_biperm (n + n) (m + m) (n_m_cup_cap n m) 
  × ((I (2 ^ 1) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (n + n - 3))) =
  matrix_of_biperm ((n - 1) + (n - 1)) (m + m) (n_m_cup_cap (n-1) m).
Proof.
  rewrite n_m_cup_cap_comm.
  replace (n_m_cup_cap m n) with 
    (n_m_cup_cap (m + 0) ((n - 2) + 2)) by (f_equal; lia).
  rewrite n_m_cup_cap_plus_plus_decomp.
  replace (matrix_of_biperm (n + n) (m + m)) with
    (matrix_of_biperm ((n-2 + (n-2)) + (2 + 2)) ((m + m) + (0 + 0)))
    by (f_equal; lia).
  rewrite matrix_of_stack_biperms by auto with biperm_db.
  replace (I (2 ^ (n + n - 3))) with (I (2^1 * 2^(n + n - 4))) by 
    (rewrite <- Nat.pow_add_r; do 2 f_equal; lia).
  rewrite <- id_kron.
  restore_dims.
  rewrite <- kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product' by (reflexivity + f_equal; lia).
  rewrite n_m_cup_cap_comm.
  rewrite matrix_of_biperm_n_m_cup_cap_0_r.
  rewrite kron_n_S.
  rewrite kron_n_1 by auto with wf_db.
  restore_dims.
  rewrite cap_cap_cup_yank_eq, Mmult_1_r by auto with wf_db.
  rewrite <- (kron_n_1 (⟦⊃⟧)) by auto with wf_db.
  rewrite <- matrix_of_biperm_n_m_cup_cap_0_r.
  restore_dims.
  rewrite <- matrix_of_stack_biperms by auto with biperm_db.
  replace (stack_biperms (m + m) (n-2+(n-2)) 0 (1 + 1)) 
    with (stack_biperms (m + m) (n-2+(n-2)) (0+0) (1+1)) 
    by (f_equal; lia).
  rewrite (n_m_cup_cap_comm 1 0).
  rewrite <- n_m_cup_cap_plus_plus_decomp.
  rewrite Nat.add_0_r.
  rewrite <- double_add.
  replace (n-2+1) with (n-1) by lia.
  f_equal.
  rewrite n_m_cup_cap_comm.
  f_equal; lia.
Qed.

Lemma n_m_cup_cap_yank_one_r n m p (Hn : n <> 0) (Hp : p <> 0) : 
  matrix_of_biperm (n + n) (m + m) (n_m_cup_cap n m) ⊗ I (2 ^ p)
  × ((I (2 ^ (n + n - 1)) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (p - 1))) =
  matrix_of_biperm ((n - 1) + (n - 1)) (m + m) (n_m_cup_cap (n-1) m) ⊗ I (2^p).
Proof.
  rewrite n_m_cup_cap_comm.
  replace (n_m_cup_cap m n) with 
    (n_m_cup_cap (0 + m) (1 + (n - 1))) by (f_equal; lia).
  rewrite n_m_cup_cap_plus_plus_decomp.
  replace (matrix_of_biperm (n + n) (m + m)) with
    (matrix_of_biperm ((1 + 1) + (n-1 + (n-1))) ((0 + 0) + (m + m)))
    by (f_equal; lia).
  rewrite matrix_of_stack_biperms by auto with biperm_db.
  replace (2^ (n+n-1)) with (2 ^ (n-1+(n-1)) * (2^1)) by 
    (rewrite <- Nat.pow_add_r; f_equal; lia).
  rewrite <- id_kron.
  restore_dims.
  rewrite 3!kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product' by 
    (rewrite <-?Nat.pow_add_r;f_equal;lia).
  rewrite Mmult_1_r by auto with wf_db.
  restore_dims.
  f_equal; [rewrite <-?Nat.pow_add_r;f_equal;lia..
  |now rewrite n_m_cup_cap_comm|].
  replace (2 ^ p) with (2 ^ 1 * 2 ^ (p - 1)) 
    by (rewrite <- Nat.pow_add_r; f_equal; lia).
  rewrite <- id_kron.
  rewrite <- 2!kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product, Mmult_1_r by auto with wf_db.
  rewrite n_m_cup_cap_comm.
  rewrite matrix_of_biperm_n_m_cup_cap_0_r.
  rewrite kron_n_1 by auto with wf_db.
  f_equal.
  apply cap_cup_yank_eq_alt.
Qed.