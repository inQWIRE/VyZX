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



(* FIXME: Move, probably to Qlib *)
Lemma forall_lt_iff n (P Q : nat -> Prop) 
  (HPQ : forall k, k < n -> P k <-> Q k) :
  (forall k, k < n -> P k) <-> (forall k, k < n -> Q k).
Proof.
  apply forall_iff; intros k.
  apply impl_iff; intros Hk.
  auto.
Qed.

Lemma forall_lt_iff_permute n f (Hf : permutation n f) 
  (P : nat -> Prop) : 
  (forall k, k < n -> P k) <-> (forall k, k < n -> P (f k)).
Proof.
  split; intros HP.
  - intros k Hk.
    apply HP.
    auto with perm_bounded_db.
  - intros k Hk.
    generalize (HP (perm_inv n f k) (perm_inv_bounded n f k Hk)).
    now rewrite perm_inv_is_rinv_of_permutation by easy.
Qed.

Lemma forall_lt_iff_of_permute_l n f (Hf : permutation n f) 
  (P Q : nat -> Prop) (HPQ : forall k, k < n -> P (f k) <-> Q k) :
  (forall k, k < n -> P k) <-> (forall k, k < n -> Q k).
Proof.
  rewrite (forall_lt_iff_permute n f Hf).
  apply forall_iff; intros k.
  apply impl_iff; intros Hk.
  now apply HPQ.
Qed.

Lemma forall_lt_iff_of_permute_r n f (Hf : permutation n f) 
  (P Q : nat -> Prop) (HPQ : forall k, k < n -> P k <-> Q (f k)) :
  (forall k, k < n -> P k) <-> (forall k, k < n -> Q k).
Proof.
  symmetry.
  apply (forall_lt_iff_of_permute_l n f Hf).
  intros k Hk.
  now rewrite HPQ.
Qed.

(* FIXME: Move to Qlib.PermutationInstances *)
Lemma big_swap_perm_ltb_r n m k : 
  big_swap_perm n m k <? m = ((¬ k <? n) && (k <? n + m)).
Proof.
  unfold big_swap_perm.
  bdestructΩ'.
Qed.

(* FIXME: Move to Qlib *)
Lemma nat_to_funbool_add_pow2_split i j n m 
  (Hi : i < 2 ^ n) (Hj : j < 2 ^ m) : 
  nat_to_funbool (n + m) (i * 2 ^ m + j) =
  (fun s => 
    if s <? n then nat_to_funbool n i s
    else nat_to_funbool m j (s - n)).
Proof.
  apply functional_extensionality; intros s.
  rewrite !nat_to_funbool_eq.
  rewrite testbit_add_pow2_split by easy.
  bdestructΩ'; try (f_equal; lia).
  - replace n with 0 in * by lia.
    replace m with 0 in * by lia.
    destruct i, j; [|cbn in Hi, Hj; lia..].
    easy.
  - replace m with 0 in * by lia.
    destruct j; [|cbn in Hj; lia].
    easy.
Qed.

(* FIXME: Move to Qlib *)
Lemma nat_to_funbool_inj_upto_small i j n (Hi : i < 2^n) (Hj : j < 2^n) :
  (forall s, s < n -> nat_to_funbool n i s = nat_to_funbool n j s) <->
  i = j.
Proof.
  split; [|now intros ->].
  intros Hij.
  rewrite <- (bits_inj_upto_small i j n) by assumption.
  intros s Hs.
  generalize (Hij (n - S s) ltac:(lia)).
  rewrite 2!nat_to_funbool_eq.
  simplify_bools_lia_one_kernel.
  now rewrite sub_S_sub_S.
Qed.

(* FIXME: Move to Qlib *)
Lemma equal_on_basis_states_implies_equal' : (* FIXME: Replace 
  equal_on_basis_states_implies_equal with this *)
  forall {m dim : nat} (A B : Matrix m (2 ^ dim)),
  WF_Matrix A -> WF_Matrix B ->
  (forall f : nat -> bool, A × f_to_vec dim f = B × f_to_vec dim f) -> 
  A = B.
Proof.
  intros m dim A B HA HB HAB.
  prep_matrix_equivalence.
  intros i j Hi Hj.
  rewrite 2!(get_entry_with_e_i _ i j) by lia.
  rewrite 2!Mmult_assoc.
  rewrite <- (basis_vector_eq_e_i _ j) by assumption.
  rewrite basis_f_to_vec_alt by assumption.
  now rewrite HAB.
Qed.

Lemma equal_on_conj_basis_states_implies_equal {n m} 
  (A B : Matrix (2 ^ n) (2 ^ m)) : WF_Matrix A -> WF_Matrix B -> 
  (forall f g, (f_to_vec n g) ⊤%M × (A × f_to_vec m f) = 
    (f_to_vec n g) ⊤%M × (B × f_to_vec m f)) -> A = B.
Proof.
  intros HA HB HAB.
  apply equal_on_basis_states_implies_equal'; [auto..|].
  intros f.
  apply transpose_matrices.
  apply equal_on_basis_states_implies_equal'; [auto_wf..|].
  intros g.
  apply transpose_matrices.
  rewrite Mmult_transpose, transpose_involutive, HAB.
  rewrite Mmult_transpose, transpose_involutive.
  reflexivity.
Qed.


Definition funbool_preserved g f bound :=
  funbool_to_nat bound g =? funbool_to_nat bound (g ∘ f)%prg.

Lemma funbool_preserved_eq_of_bounded_eq {bound g g'} 
  (Hg : forall k, k < bound -> g k = g' k) 
  f (Hf : perm_bounded bound f) : 
  funbool_preserved g f bound = funbool_preserved g' f bound.
Proof.
  unfold funbool_preserved.
  rewrite (funbool_to_nat_eq _ _ _ Hg).
  f_equal.
  apply funbool_to_nat_eq.
  intros k Hk.
  apply Hg, Hf, Hk.
Qed.

Lemma funbool_preserved_eq_of_perm_eq {bound f f'} 
  (Hf : perm_eq bound f f') g :
  funbool_preserved g f bound = funbool_preserved g f' bound.
Proof.
  unfold funbool_preserved, compose.
  f_equal.
  apply funbool_to_nat_eq.
  intros k Hk.
  f_equal.
  apply Hf, Hk.
Qed.

Lemma funbool_preserved_iff_all_lt_eq g f bound : 
  funbool_preserved g f bound = true <->
  (forall k, k < bound -> g k = g (f k)).
Proof.
  unfold funbool_preserved.
  rewrite Nat.eqb_eq.
  symmetry.
  apply funbool_to_nat_eq_iff.
Qed.

Definition number_preserved i f bound :=
  funbool_preserved (nat_to_funbool bound i) f bound.

Lemma number_preserved_funbool_to_nat g f bound (Hf : perm_bounded bound f) : 
  number_preserved (funbool_to_nat bound g) f bound =
  funbool_preserved g f bound.
Proof.
  unfold number_preserved.
  apply funbool_preserved_eq_of_bounded_eq; [|easy].
  intros k Hk.
  apply funbool_to_nat_inverse, Hk.
Qed.

Definition number_preserved_old (i : nat) (f : nat -> nat) (bound : nat) :=
  forallb (fun k => eqb (Nat.testbit i k) 
    (Nat.testbit i (f k))) (seq 0 bound).

Lemma number_preserved_old_is_swapped i f bound 
  (Hf : perm_bounded bound f) : 
  number_preserved_old i f bound = 
  number_preserved (funbool_to_nat bound 
    (nat_to_funbool bound i ∘ reflect_perm bound)) f bound.
Proof.
  apply eq_iff_eq_true.
  unfold number_preserved_old.
  rewrite forallb_seq0.
  setoid_rewrite eqb_true_iff.
  rewrite number_preserved_funbool_to_nat by easy.
  rewrite funbool_preserved_iff_all_lt_eq.
  apply forall_iff; intros k.
  apply impl_iff; intros Hk.
  unfold compose.
  pose proof (Hf k Hk).
  unfold reflect_perm.
  do 2 simplify_bools_lia_one_kernel.
  rewrite nat_to_funbool_eq.
  do 2 simplify_bools_lia_one_kernel.
  rewrite 2!sub_S_sub_S by easy.
  easy.
Qed.

(* Lemma number_preserved_iff_all_lt_eq ji nm f : 
  number_preserved ji f nm = true <->
  forall s, s < nm -> 
  Nat.testbit ji s = Nat.testbit ji (f s). *)
Lemma number_preserved_iff_all_lt_eq ji nm f : 
  number_preserved ji f nm = true <->
  forall s, s < nm -> 
  nat_to_funbool nm ji s = nat_to_funbool nm ji (f s).
Proof.
  apply funbool_preserved_iff_all_lt_eq.
Qed.

(* Lemma number_preserved_iff j i n m (Hi : i < 2^n) f : 
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
      Nat.testbit j (s - n) = Nat.testbit j (f s - n). *)
(* Proof.
  rewrite number_preserved_iff_all_lt_eq.
  apply forall_iff.
  intros s. 
  rewrite impl_iff.
  intros Hs.
  rewrite 2!testbit_add_pow2_split by easy.
  bdestructΩ'; easy.
Qed. *)



Lemma number_preserved_iff j i n m 
  (Hi : i < 2 ^ n) (Hj : j < 2 ^ m) f : 
  number_preserved (i * 2 ^ m + j) f (n + m) = true <->
  forall s, s < (n + m) -> 
  if s <? n then
    if (f s) <? n then 
      nat_to_funbool n i s = nat_to_funbool n i (f s)
    else 
      nat_to_funbool n i s = nat_to_funbool m j (f s - n)
  else 
    if (f s) <? n then 
      nat_to_funbool m j (s - n) = nat_to_funbool n i (f s)
    else 
      nat_to_funbool m j (s - n) = nat_to_funbool m j (f s - n).
Proof.
  rewrite number_preserved_iff_all_lt_eq.
  apply forall_iff.
  intros s. 
  rewrite impl_iff.
  intros Hs.
  rewrite nat_to_funbool_add_pow2_split by easy.
  bdestructΩ'.
Qed.


(* Lemma number_preserved_iff' i j n m (Hi : i < 2 ^ n) f : 
  number_preserved (j * 2 ^ n + i) f (m + n) = true <->
  (forall s : nat,
  s < m + n ->
  if s <? n
  then if f s <? n
    then Nat.testbit i s = Nat.testbit i (f s)
    else Nat.testbit i s = Nat.testbit j (f s - n)
  else if f s <? n
    then Nat.testbit j (s - n) = Nat.testbit i (f s)
    else Nat.testbit j (s - n) = Nat.testbit j (f s - n)). *)
(* Proof.
  rewrite (Nat.add_comm m n).
  now apply number_preserved_iff.
Qed. *)


(* TODO: Do we want to Add Parametric Morphism here? *)
Lemma number_preserved_eq_of_perm_eq {n f f'}
  (Hf : perm_eq n f f') ij : 
  number_preserved ij f n = number_preserved ij f' n.
Proof.
  apply funbool_preserved_eq_of_perm_eq, Hf.
Qed.

Lemma number_preserved_eq_of_eq_on (ij n : nat) f g : 
  (forall i, i < n -> f i = g i) ->
  number_preserved ij f n = number_preserved ij g n.
Proof.
  intros.
  now apply number_preserved_eq_of_perm_eq.
Qed.

(* Lemma number_preserved_funbool_to_nat f g n 
  (Hf : perm_bounded n f) : 
  number_preserved (funbool_to_nat n g) f n =
  forallb (fun k => eqb (g (n - S k)) (g (n - S (f k)))) (seq 0 n). *)
(* Proof.
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
Qed. *)

(* Lemma number_preserved_idn (n : nat) {i j} (Hi : i < 2^n) (Hj : j < 2^n) : 
  number_preserved (j * 2 ^ n + i) (idn_biperm n) (n + n) = (i =? j). *)



Lemma number_preserved_idn (n : nat) {i j} (Hi : i < 2^n) (Hj : j < 2^n) : 
  number_preserved (i * 2 ^ n + j) (idn_biperm n) (n + n) = (i =? j).
Proof.
  rewrite (number_preserved_eq_of_perm_eq (idn_biperm_defn n)).
  apply eq_iff_eq_true.
  rewrite number_preserved_iff by easy.
  rewrite Nat.eqb_eq.
  split.
  - intros H.
    apply (nat_to_funbool_inj_upto_small i j n Hi Hj).
    intros s Hs.
    specialize (H s ltac:(lia)).
    revert H.
    unfold idn_biperm.
    do 2 simplify_bools_lia_one_kernel.
    now rewrite Nat.add_sub.
  - intros -> s Hs.
    unfold idn_biperm.
    bdestructΩ'; 
    now rewrite Nat.add_sub.
Qed.


Lemma funbool_preserved_compose_perm_biperm n f g h 
  (Hg : permutation n g) : 
  funbool_preserved h (compose_perm_biperm n f g) n =
  funbool_preserved (h ∘ g) (f) n.
Proof.
  apply eq_iff_eq_true.
  rewrite 2!funbool_preserved_iff_all_lt_eq.
  rewrite (forall_lt_iff_permute n g) by auto.
  apply forall_lt_iff.
  intros k Hk.
  rewrite compose_perm_biperm_defn by auto_perm.
  unfold compose.
  now rewrite perm_inv_is_linv_of_permutation.
Qed.  

(* OLD ORDERING: Bottom to top, outputs first. I.e., 
7  \/ —     3
6  /\ \/    2
5  —  /\ ╲  1
4  —  —  ╱  0
*)

(* NEW ORDERING: Top to bottom, inputs first. I.e., 
0  \/ —     4
1  /\ \/    5
2  —  /\ ╲  6
3  —  —  ╱  7
*)


Open Scope matrix_scope.

Definition matrix_of_biperm (n m : nat) (f : nat -> nat) : Matrix (2^m) (2^n) :=
  make_WF (fun i j =>
  if number_preserved (j * 2^m + i) f (n + m) then C1 else C0).
  (* this order works experimentally... :/ *)

Lemma matrix_of_biperm_WF n m f : 
  WF_Matrix (matrix_of_biperm n m f).
Proof.
  unfold matrix_of_biperm.
  auto_wf.
Qed.

#[export] Hint Resolve matrix_of_biperm_WF : wf_db.

Lemma matrix_of_biperm_defn n m f : 
  matrix_of_biperm n m f ≡ (fun i j =>
  if number_preserved (j * 2^m + i) f (n + m) then C1 else C0).
Proof.
  apply make_WF_equiv.
Qed.

Lemma matrix_of_biperm_eq_of_perm_eq {n m f g}
  (H : perm_eq (n + m) f g) : 
  matrix_of_biperm n m f = matrix_of_biperm n m g.
Proof.
  apply mat_equiv_eq; [auto_wf..|].
  rewrite 2!matrix_of_biperm_defn.
  intros i j Hi Hj.
  now rewrite (number_preserved_eq_of_eq_on _ _ _ _ H).
Qed.

Add Parametric Morphism n m : (matrix_of_biperm n m) with signature
  perm_eq (n + m) ==> eq as matrix_of_biperm_perm_eq_to_eq_proper.
Proof.
  intros.
  now apply matrix_of_biperm_eq_of_perm_eq.
Qed.

Lemma matrix_of_biperm_funbool_conj_eq f g h n m (Hf : perm_bounded (n + m) f) : 
  ((f_to_vec m g) ⊤ × matrix_of_biperm n m f × f_to_vec n h) = 
  (if funbool_preserved (fun k => if k <? n then h k else g (k - n)) 
      f (n + m) then C1 else C0) .* I (2 ^ 0).
Proof.
  prep_matrix_equivalence.
  rewrite 2!basis_f_to_vec.
  rewrite matrix_of_biperm_defn.
  by_cell.
  rewrite matrix_conj_basis_eq_lt by apply funbool_to_nat_bound.
  unfold scale; cbn; rewrite Cmult_1_r.
  apply f_equal_if; [|easy..].
  unfold number_preserved.
  rewrite nat_to_funbool_add_pow2_split by apply funbool_to_nat_bound.
  apply funbool_preserved_eq_of_bounded_eq; [|easy].
  intros k Hk.
  bdestructΩ';
  rewrite funbool_to_nat_inverse; reflexivity + lia.
Qed.

Lemma matrix_of_biperm_funbool_conj f g h n m (Hf : perm_bounded (n + m) f) :
  ((f_to_vec m g) ⊤ × matrix_of_biperm n m f × f_to_vec n h) 0 0 = 
  (if funbool_preserved (fun k => if k <? n then h k else g (k - n))
    f (n + m) then C1 else C0).
Proof.
  rewrite matrix_of_biperm_funbool_conj_eq by easy.
  apply Cmult_1_r.
Qed.

  

Lemma matrix_of_biperm_transpose n m f (Hf : bipermutation (n + m) f) : 
  (matrix_of_biperm n m f) ⊤ ≡
  (matrix_of_biperm m n (flip_biperm n m f)).
Proof.
  pose proof (fun i Hi => proj1 (Hf i Hi)) as Hfbdd.
  pose proof (fun i Hi => proj1 (proj2 (Hf i Hi))) as Hfne.
  pose proof (fun i Hi => proj2 (proj2 (Hf i Hi))) as Hfeq.
  rewrite 2!matrix_of_biperm_defn.
  intros i j Hi Hj.
  unfold transpose.
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite 2!number_preserved_iff by easy.
  rewrite (Nat.add_comm m n).
  apply (forall_lt_iff_of_permute_r (n + m) (big_swap_perm n m));
  [auto with perm_db|].
  intros k Hk.
  rewrite flip_biperm_defn by auto_perm.
  change ((?g ∘ f ∘ ?h)%prg (?g k)) with ((g ∘ f ∘ (h ∘ g))%prg k).
  rewrite big_swap_perm_invol, compose_idn_r.
  rewrite big_swap_perm_ltb_r.
  simplify_bools_lia_one_kernel.
  unfold compose.
  rewrite big_swap_perm_ltb_r.
  pose proof (Hfbdd k Hk).
  simplify_bools_lia_one_kernel.
  rewrite 2!big_swap_perm_defn by auto. 
  rewrite 3!negb_if.
  bdestructΩ'; now rewrite !Nat.add_sub.
Qed.

Lemma matrix_of_biperm_transpose_eq n m f (Hf : bipermutation (n + m) f) : 
  (matrix_of_biperm n m f) ⊤ =
  (matrix_of_biperm m n (flip_biperm n m f)).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  now apply matrix_of_biperm_transpose.
Qed.

Lemma matrix_of_biperm_compose_perm_l_eq n m f g
  (Hf : bipermutation (n + m) f)
  (Hg : permutation n g) : 
  matrix_of_biperm n m (biperm_compose_perm_l n m f g) =
  matrix_of_biperm n m f × 
  perm_to_matrix n g.
Proof.
  unfold biperm_compose_perm_l.
  apply equal_on_conj_basis_states_implies_equal; [auto_wf..|].
  intros l r.
  rewrite Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits by cleanup_perm_inv.
  rewrite <- !Mmult_assoc.
  rewrite 2!matrix_of_biperm_funbool_conj_eq by 
    auto using compose_perm_bipermutation with biperm_db.
  f_equal.
  apply f_equal_if; [|easy..].
  rewrite funbool_preserved_compose_perm_biperm by auto with perm_db.
  apply funbool_preserved_eq_of_bounded_eq; [|auto_perm].
  rewrite stack_perms_f_idn.
  intros k Hk.
  unfold compose.
  assert (k < n -> g k < n) by auto_perm.
  bdestructΩ'.
Qed.

Lemma matrix_of_biperm_compose_perm_r_eq n m f g
  (Hf : bipermutation (n + m) f)
  (Hg : permutation m g) : 
  matrix_of_biperm n m (biperm_compose_perm_r n m f g) =
  perm_to_matrix m g × matrix_of_biperm n m f.
Proof.
  unfold biperm_compose_perm_r.
  apply equal_on_conj_basis_states_implies_equal; [auto_wf..|].
  intros l r.
  rewrite <- !Mmult_assoc.
  rewrite perm_to_matrix_permutes_qubits_l by cleanup_perm_inv.
  rewrite 2!matrix_of_biperm_funbool_conj_eq by 
    auto using compose_perm_bipermutation with biperm_db.
  f_equal.
  apply f_equal_if; [|easy..].
  rewrite funbool_preserved_compose_perm_biperm by auto with perm_db.
  apply funbool_preserved_eq_of_bounded_eq; [|auto_perm].
  intros k Hk.
  rewrite stack_perms_idn_f.
  unfold compose.
  bdestructΩ'.
  now rewrite Nat.add_sub.
Qed.

Lemma matrix_of_biperm_Mmult_perm_r_eq n m f g 
  (Hf : bipermutation (n + m) f)
  (Hg : permutation n g) : 
  matrix_of_biperm n m f × perm_to_matrix n g = 
  matrix_of_biperm n m (biperm_compose_perm_l n m f g).
Proof.
  now rewrite matrix_of_biperm_compose_perm_l_eq by auto_perm.
Qed.


Lemma matrix_of_biperm_pow_2_l n m f 
  (Hf : bipermutation (n + m) f) k : 
  matrix_of_biperm n m f 0 (2^k) = 0%R.
Proof.
  bdestruct (2 ^ k <? 2 ^ n); 
  [|apply matrix_of_biperm_WF; lia].
  rewrite matrix_of_biperm_defn by show_moddy_lt.
  apply if_false.
  rewrite <- Nat.pow_add_r, Nat.add_0_r.
  rewrite <- not_true_iff_false.
  rewrite number_preserved_iff_all_lt_eq.
  intros Hcontra.
  bdestruct (k <? n); 
  [|pose proof (Nat.pow_le_mono_r 2 n k); lia].
  generalize (Hcontra (n + m - S (k + m)) ltac:(lia)).
  rewrite nat_to_funbool_eq.
  pose proof (Hf (n + m - S (k + m))).
  do 2 simplify_bools_lia_one_kernel.
  rewrite 2!Nat.pow2_bits_eqb.
  bdestructΩ'.
Qed.

Lemma matrix_of_biperm_pow_2_r n m f 
  (Hf : bipermutation (n + m) f) k : 
  matrix_of_biperm n m f (2^k) 0 = 0%R.
Proof.
  bdestruct (2 ^ k <? 2 ^ m); 
  [|apply matrix_of_biperm_WF; lia].
  rewrite matrix_of_biperm_defn by show_moddy_lt.
  apply if_false.
  rewrite Nat.mul_0_l, Nat.add_0_l.
  rewrite <- not_true_iff_false.
  rewrite number_preserved_iff_all_lt_eq.
  intros Hcontra.
  bdestruct (k <? m); 
  [|pose proof (Nat.pow_le_mono_r 2 m k); lia].
  generalize (Hcontra (n + m - S k) ltac:(lia)).
  rewrite nat_to_funbool_eq.
  pose proof (Hf (n + m - S k)).
  do 2 simplify_bools_lia_one_kernel.
  rewrite 2!Nat.pow2_bits_eqb.
  bdestructΩ'.
Qed.

Lemma nat_to_funbool_sum_pows_2_ne n k l 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) : 
  nat_to_funbool n (2 ^ k + 2 ^ l) =
  (fun s => (s =? n - S k) || (s =? n - S l)).
Proof.
  apply functional_extensionality.
  intros s.
  rewrite nat_to_funbool_eq.
  bdestruct (s <=? n - 1); [|bdestructΩ'].
  rewrite testbit_sum_pows_2_ne by easy.
  f_equal;
  apply eq_iff_eq_true;
  rewrite 2!Nat.eqb_eq; lia.
Qed.

Lemma number_preserved_sum_pows_2 n f k l 
  (Hk : k < n) (Hl : l < n) (Hkl : k <> l) (Hf : bipermutation n f) : 
  number_preserved (2 ^ k + 2 ^ l) f n = 
  (f (n - S k) =? n - S l).
Proof.
  apply eq_iff_eq_true.
  rewrite Nat.eqb_eq.
  rewrite number_preserved_iff_all_lt_eq.
  split.
  - intros Hs.
    generalize (Hs (n - S k) ltac:(lia)).
    rewrite nat_to_funbool_sum_pows_2_ne by easy.
    rewrite 2!(bipermutation_eqb_iff _ _ Hf) by lia.
    simplify_bools_lia_one_kernel.
    pose proof (Hf (n - S k) ltac:(lia)).
    bdestructΩ'.
    intros _.
    rewrite (bipermutation_eq_iff _ _ Hf); lia.
  - intros Hfkl.
    assert (Hflk : f (n - S l) = n - S k) by (rewrite <- Hfkl; apply Hf; lia).
    intros s Hs.
    rewrite nat_to_funbool_sum_pows_2_ne by easy.
    rewrite 2!(bipermutation_eqb_iff _ _ Hf) by lia.
    rewrite Hfkl, Hflk.
    apply orb_comm.
Qed.

Lemma matrix_of_biperm_sum_pows_2_l_l n m f 
  (Hf : bipermutation (n + m) f) k l : k < n -> l < n ->
  matrix_of_biperm n m f 0 (2^k + 2^l) =
  if f (n - S k) =? n - S l then C1 else 0%R.
Proof.
  intros Hk Hl.
  bdestruct (k =? l).
  1:{
    replace (2 ^ k + 2 ^ l) with (2 ^ (S k)) by (cbn; subst; lia).
    rewrite matrix_of_biperm_pow_2_l by easy. 
    pose proof (Hf (n - S l)); bdestructΩ'.
  }
  assert (2 ^ k < 2 ^ n) by (apply Nat.pow_lt_mono_r; lia).
  assert (2 ^ l < 2 ^ n) by (apply Nat.pow_lt_mono_r; lia).
  pose proof (sum_ne_pows_2_lt_pow_2_S n k l Hk Hl ltac:(auto)).
  rewrite matrix_of_biperm_defn by show_nonzero.
  apply f_equal_if; [|easy..].
  replace (n - S k) with (n + m - (S (k + m))) by lia.
  replace (n - S l) with (n + m - (S (l + m))) by lia.
  rewrite <- number_preserved_sum_pows_2 by (auto with zarith).
  f_equal.
  show_pow2_le.
Qed.



Lemma matrix_of_biperm_sum_pows_2_r_r n m f 
  (Hf : bipermutation (n + m) f) k l : k < m -> l < m ->
  matrix_of_biperm n m f (2^k + 2^l) 0 =
  if f (n + m - S k) =? (n + m - S l) then C1 else 0%R.
Proof.
  intros Hk Hl.
  bdestruct (k =? l).
  1:{
    replace (2 ^ k + 2 ^ l) with (2 ^ (S k)) by (cbn; subst; lia).
    rewrite matrix_of_biperm_pow_2_r by easy. 
    pose proof (Hf (n + m - S k)); bdestructΩ'.
  }
  pose proof (sum_ne_pows_2_lt_pow_2_S m k l Hk Hl ltac:(auto)).
  rewrite matrix_of_biperm_defn by show_nonzero.
  rewrite Nat.mul_0_l, Nat.add_0_l.
  apply f_equal_if; [|easy..].
  apply number_preserved_sum_pows_2; auto with zarith.
Qed.

Lemma matrix_of_biperm_sum_pows_2_l_r n m f 
  (Hf : bipermutation (n + m) f) k l : k < m -> l < n ->
  matrix_of_biperm n m f (2^k) (2^l) =
  if f (n - S l) =? n + m - S k then C1 else 0%R.
Proof.
  intros Hk Hl.
  pose proof (Nat.pow_lt_mono_r 2 k m ltac:(lia) ltac:(lia)).
  pose proof (Nat.pow_lt_mono_r 2 l n ltac:(lia) ltac:(lia)).
  rewrite matrix_of_biperm_defn by auto.
  apply f_equal_if; [|easy..].
  rewrite <- Nat.pow_add_r.
  replace (n - S l) with (n + m - S (l + m)) by lia.
  apply number_preserved_sum_pows_2; auto with zarith.
Qed.

Lemma b2C_eq_iff (b c : bool) : 
  (if b then C1 else C0) = (if c then C1 else C0) <-> b = c.
Proof.
  pose proof C1_nonzero.
  destruct b, c; split; easy + congruence.
Qed.

Lemma funbool_preserved_orb_eqb n k l f (Hk : k < n) (Hl : l < n) 
  (Hf : bipermutation n f) : 
  funbool_preserved (fun a => (a =? k) || (a =? l)) f n =
  (f k =? l).
Proof.
  apply eq_iff_eq_true.
  rewrite Nat.eqb_eq, funbool_preserved_iff_all_lt_eq.
  split.
  - intros Hall.
    specialize (Hall k Hk).
    revert Hall.
    simplify_bools_lia_one_kernel.
    pose proof (Hf k Hk).
    bdestructΩ'.
  - intros Heq.
    intros a Ha.
    rewrite 2!(bipermutation_eqb_iff _ _ Hf) by lia.
    rewrite Heq, <- Heq, (bipermutation_involutive _ Hf), Heq by auto.
    apply orb_comm.
Qed.

Lemma funbool_preserved_eq_orb_eqb n k l f g (Hk : k < n) (Hl : l < n) 
  (Hf : bipermutation n f) 
  (Hg : forall a, a < n -> g a = (a =? k) || (a =? l)) : 
  funbool_preserved g f n =
  (f k =? l).
Proof.
  rewrite <- (funbool_preserved_orb_eqb n) by auto.
  apply funbool_preserved_eq_of_bounded_eq; auto_perm.
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
  intros Hequiv.
  (* unfold perm_eq. *)
  (* rewrite (forall_lt_iff_permute _ _ (reflect_perm_permutation _)). *)
  intros k Hk.
  (* rewrite reflect_perm_defn by auto. *)
  assert (Heq : forall l r, 
    (f_to_vec m r) ⊤ × matrix_of_biperm n m f × f_to_vec n l ≡
    (f_to_vec m r) ⊤ × matrix_of_biperm n m g × f_to_vec n l) by 
    (intros l r; now rewrite Hequiv).
  pose proof (fun l r => Heq l r 0 0 
    ltac:(constructor) ltac:(constructor)) as Heq'.
  setoid_rewrite matrix_of_biperm_funbool_conj in Heq'; [|auto..].
  setoid_rewrite b2C_eq_iff in Heq'.
  bdestruct (k <? n); bdestruct (f k <? n).
  - specialize (Heq' (fun a => (a =? k) || (a =? f k)) (fun _ => false)).
    revert Heq'.
    rewrite 2!(funbool_preserved_eq_orb_eqb (n + m) k (f k) _ _ 
      ltac:(lia) ltac:(lia)) by (assumption + intros; bdestructΩ').
    rewrite Nat.eqb_refl.
    bdestructΩ'.
  - specialize (Heq' (fun a => (a =? k)) (fun a => (a =? f k - n))).
    revert Heq'.
    pose proof (Hf k ltac:(lia)).
    rewrite 2!(funbool_preserved_eq_orb_eqb (n + m) k (f k) _ _ 
      ltac:(lia) ltac:(lia)) by (assumption + intros; bdestructΩ').
    rewrite Nat.eqb_refl.
    bdestructΩ'.
  - specialize (Heq' (fun a => (a =? f k)) (fun a => (a =? k - n))).
    revert Heq'.
    pose proof (Hf k ltac:(lia)).
    rewrite 2!(funbool_preserved_eq_orb_eqb (n + m) k (f k) _ _ 
      ltac:(lia) ltac:(lia)) by (assumption + intros; bdestructΩ').
    rewrite Nat.eqb_refl.
    bdestructΩ'.
  - specialize (Heq' (fun _ => false) (fun a => 
      (a =? k - n) || (a =? f k - n))).
    revert Heq'.
    pose proof (Hf k ltac:(lia)).
    rewrite 2!(funbool_preserved_eq_orb_eqb (n + m) k (f k) _ _ 
      ltac:(lia) ltac:(lia)) by (assumption + intros; bdestructΩ').
    rewrite Nat.eqb_refl.
    bdestructΩ'.
Qed.

(* Lemma funbool_preserved_stack_biperms n0 m0 n1 m1 f g l r 
  (Hf : bipermutation (n0 + m0) f)
  (Hg : bipermutation (n1 + m1) g) : 
  funbool_preserved
    (fun k : nat =>
    if k <? n1 + n0 then l k else r (k - (n1 + n0)))
    (compose_perm_biperm (n0 + n1 + (m0 + m1))
      (stack_perms (n0 + m0) (n1 + m1) f g)
      (stack_perms (n0 + m0 + n1) m1
          (stack_perms n0 (m0 + n1) idn (big_swap_perm m0 n1))
          idn)) (n0 + n1 + (m0 + m1)) =
  funbool_preserved
    (fun k : nat => if k <? n1 then l k else r (k - n1)) g
    (n1 + m1) &&
  funbool_preserved
    (fun k : nat =>
    if k <? n0 then l (n1 + k) else r (m1 + (k - n0))) f
    (n0 + m0).
Proof.
  apply eq_iff_eq_true.
  unfold stack_biperms.
  (* rewrite funbool_preserved_compose_perm_biperm by auto_perm. *)
  rewrite big_swap_perm_defn.
  rewrite stack_perms_f_idn, stack_perms_idn_f.
  rewrite andb_true_iff, 3!funbool_preserved_iff_all_lt_eq.
  split.
  - intros Hstack.
    split.
    + intros k Hk.
      bdestruct (k <? n1).
      * generalize (Hstack (k + (n0 + m0)) ltac:(lia)).
        rewrite stack_perms_right by lia.
        rewrite Nat.add_sub.
        unfold compose.
        do 4 simplify_bools_lia_one_kernel.
        pose proof (Hg k ltac:(lia)).
        bdestructΩ'.
        simplify_bools_lia_one_kernel. *)
  

Lemma matrix_of_stack_biperms n0 m0 n1 m1 f g 
  (Hf : bipermutation (n0 + m0) f)
  (Hg : bipermutation (n1 + m1) g) : 
  matrix_of_biperm (n0 + n1) (m0 + m1) (stack_biperms n0 m0 n1 m1 f g) =
  matrix_of_biperm n0 m0 f ⊗ matrix_of_biperm n1 m1 g.
Proof.
  apply equal_on_conj_basis_states_implies_equal; [auto_wf..|].
  intros l r.
  rewrite <- 2!Mmult_assoc.
  rewrite matrix_of_biperm_funbool_conj_eq by auto_biperm.
  rewrite 2!f_to_vec_split'_eq.
  restore_dims.
  change ((?A ⊗ ?B) ⊤) with (A ⊤ ⊗ B ⊤).
  restore_dims.
  rewrite 2!kron_mixed_product.
  rewrite 2!matrix_of_biperm_funbool_conj_eq by auto_biperm.
  restore_dims.
  distribute_scale.
  rewrite kron_1_r.
  f_equal.
  rewrite Cmult_if_if_1_l.
  apply f_equal_if; [|easy..].
  (* Subproof :/ *)
  apply eq_iff_eq_true.
  unfold stack_biperms.
  rewrite funbool_preserved_compose_perm_biperm by auto_perm.
  rewrite big_swap_perm_defn.
  rewrite stack_perms_f_idn, stack_perms_idn_f.
  rewrite andb_true_iff, 3!funbool_preserved_iff_all_lt_eq.
  split.
  - intros Hstack.
    split.
    + intros k Hk.
      generalize (Hstack (k) ltac:(lia)).
      rewrite stack_perms_left by lia.
      unfold compose.
      do 2 simplify_bools_lia_one_kernel.
      bdestruct (k <? n0).
      * cbn [negb]. 
        simplify_bools_lia_one_kernel. 
        intros ->.
        pose proof (Hf k ltac:(lia)).
        bdestructΩ'.
        f_equal; lia.
      * cbn [negb]. 
        do 2 simplify_bools_lia_one_kernel.
        replace (k - n0 + n1 + n0 - (n0 + n1)) with (k - n0) by lia.
        intros ->.
        pose proof (Hf k ltac:(lia)).
        bdestructΩ'.
        f_equal; lia.
    + intros k Hk.
      generalize (Hstack (k + (n0 + m0)) ltac:(lia)).
      rewrite stack_perms_right by lia.
      rewrite Nat.add_sub.
      unfold compose.
      do 4 simplify_bools_lia_one_kernel.
      bdestruct (k <? n1).
      * cbn [negb]. 
        do 3 simplify_bools_lia_one_kernel.
        replace (k + (n0 + m0) - n0 - m0 + n0) with (n0 + k) by lia. 
        intros ->.
        pose proof (Hg k ltac:(lia)).
        bdestructΩ';
        f_equal; lia.
      * cbn [negb]. 
        do 2 simplify_bools_lia_one_kernel.
        replace (k + (n0 + m0) - (n0 + n1)) with (m0 + (k - n1)) by lia.
        intros ->.
        pose proof (Hg k ltac:(lia)).
        bdestructΩ';
        f_equal; lia.
  - intros [Hfk Hgk].
    intros k Hk.
    bdestruct (k <? (n0 + m0)).
    + rewrite stack_perms_left by lia.
      generalize (Hfk k ltac:(lia)).
      unfold compose.
      do 2 simplify_bools_lia_one_kernel.
      bdestruct (k <? n0).
      * cbn [negb].
        simplify_bools_lia_one_kernel. 
        intros ->.
        pose proof (Hf k ltac:(lia)).
        bdestructΩ'.
        f_equal; lia.
      * cbn [negb]. 
        do 2 simplify_bools_lia_one_kernel.
        replace (k - n0 + n1 + n0 - (n0 + n1)) with (k - n0) by lia.
        intros ->.
        pose proof (Hf k ltac:(lia)).
        bdestructΩ'.
        f_equal; lia.
    + rewrite stack_perms_right by lia.
      generalize (Hgk (k - (n0 + m0)) ltac:(lia)).
      unfold compose.
      do 4 simplify_bools_lia_one_kernel.
      bdestruct (k <? n0 + m0 + n1).
      * do 3 simplify_bools_lia_one_kernel.
        replace (n0 + (k - (n0 + m0))) with (k - n0 - m0 + n0) by lia.
        intros ->.
        pose proof (Hg (k - (n0 + m0)) ltac:(lia)).
        bdestructΩ';
        f_equal; lia.
      * do 2 simplify_bools_lia_one_kernel.
        replace (m0 + (k - (n0 + m0) - n1)) with (k - (n0 + n1)) by lia.
        intros ->.
        pose proof (Hg (k - (n0 + m0)) ltac:(lia)).
        bdestructΩ';
        f_equal; lia.
Qed.

Lemma matrix_of_stack_biperms' (n0 m0 n1 m1 n01 m01 : nat) (f g : nat -> nat)
  (Hf : bipermutation (n0 + m0) f)
  (Hg : bipermutation (n1 + m1) g)
  (Hn01 : n0 + n1 = n01) (Hm01 : m01 = m0 + m1) :
  matrix_of_biperm n01 m01 (stack_biperms n0 m0 n1 m1 f g) =
  matrix_of_biperm n0 m0 f ⊗ matrix_of_biperm n1 m1 g.
Proof.
  subst.
  now apply matrix_of_stack_biperms.
Qed.

(* FIXME: Move to Qlib *)
Lemma f_to_vec_transpose_f_to_vec n f g :
  transpose (f_to_vec n f) × f_to_vec n g = 
  b2R (forallb (fun k => eqb (f k) (g k)) (seq 0 n)) .* I 1.
Proof.
  prep_matrix_equivalence.
  intros [] []; [|lia..]; intros _ _.
  rewrite 2!basis_f_to_vec.
  rewrite basis_trans_basis.
  simplify_bools_moddy_lia_one_kernel.
  unfold scale.
  cbn.
  rewrite Cmult_1_r.
  unfold b2R.
  rewrite (if_dist _ _ _ RtoC).
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite Nat.eqb_eq, forallb_seq0, <- funbool_to_nat_eq_iff.
  now setoid_rewrite eqb_true_iff.
Qed.

Lemma f_to_vec_transpose_f_to_vec' n f g :
  transpose (f_to_vec n f) × f_to_vec n g = 
  (if funbool_to_nat n f =? funbool_to_nat n g then  
    C1 else C0) .* I 1.
Proof.
  rewrite f_to_vec_transpose_f_to_vec.
  f_equal.
  unfold b2R.
  rewrite (if_dist R C).
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite forallb_seq0, Nat.eqb_eq.
  setoid_rewrite eqb_true_iff.
  apply funbool_to_nat_eq_iff.
Qed.

Lemma f_to_vec_transpose_self n f :
  transpose (f_to_vec n f) × f_to_vec n f = 
  I 1.
Proof.
  rewrite f_to_vec_transpose_f_to_vec', Nat.eqb_refl.
  now Msimpl_light.
Qed.

Lemma matrix_of_idn_biperm n : 
  matrix_of_biperm n n (idn_biperm n) = I (2 ^ n).
Proof.
  prep_matrix_equivalence.
  rewrite matrix_of_biperm_defn.
  intros i j Hi Hj.
  unfold I.
  simplify_bools_lia_one_kernel.
  apply f_equal_if; [|easy..].
  rewrite number_preserved_idn by auto.
  apply Nat.eqb_sym.
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
  change 0 with (0 + 0) at 5.
  replace (S ncap + S ncap) with ((1 + 1) + (ncap + ncap)) by lia.
  replace (S ncap) with (1 + ncap) by lia.
  rewrite n_m_cup_cap_plus_plus_decomp.
  (* pose proof (matrix_of_stack_biperms (0+0) (1+1) (0+0) (ncap + ncap)
    (n_m_cup_cap 0 1) (n_m_cup_cap 0 ncap)
    ltac:(auto with biperm_db)
    ltac:(auto with biperm_db)) as Hrw. *)
  change 0 with (0 + 0 + (0 + 0)) at 6.
  rewrite matrix_of_stack_biperms by auto_biperm.
  change (1 + ncap) with (S ncap).
  rewrite kron_n_assoc by auto_wf.
  f_equal;
  [rewrite <- Nat.pow_mul_r; f_equal; lia..| |apply IHncap].
  prep_matrix_equivalence.
  by_cell; reflexivity.
Qed.

(* FIXME: Move *)
Lemma flip_n_m_cup_cap n m : 
  flip_biperm (n + n) (m + m) (n_m_cup_cap n m) = n_m_cup_cap m n.
Proof.
  eq_by_WF_perm_eq ((m + m) + (n + n));
  [apply compose_perm_biperm_WF..|].
  rewrite flip_biperm_defn.
  rewrite n_m_cup_cap_stack_biperms_decomp'.
  rewrite compose_assoc, stack_perms_big_swap_natural by 
    (apply (n_m_cup_cap_bounded 0)).
  rewrite <- compose_assoc, big_swap_perm_invol.
  now rewrite (n_m_cup_cap_stack_biperms_decomp' m n).
Qed.

Lemma matrix_of_biperm_n_m_cup_cap_0_r ncup : 
  matrix_of_biperm (ncup + ncup) 0 (n_m_cup_cap ncup 0) =
  (ncup ⨂ ⟦⊃⟧).
Proof.
  apply transpose_matrices.
  rewrite matrix_of_biperm_transpose_eq 
    by (change 0 with (0 + 0) at 1; auto_biperm).
  simpl_rewrite (flip_n_m_cup_cap ncup 0).
  symmetry.
  etransitivity; [apply (kron_n_transpose _ _ ncup (⟦ ⊃ ⟧))|].
  rewrite matrix_of_biperm_n_m_cup_cap_0_l.
  rewrite <- semantics_transpose_comm.
  easy.
Qed.

(* FIXME: Move to Bipermutations.v *)
#[export] Hint Extern 5 (bipermutation ?nnmm (n_m_cup_cap ?n ?m)) => 
  apply (bipermutation_change_dims nnmm (n + n + (m + m))
    (n_m_cup_cap n m) ltac:(lia) (n_m_cup_cap_bipermutation n m)) : biperm_db.

Lemma matrix_of_biperm_n_m_cup_cap_split ncup ncap : 
  matrix_of_biperm (ncup + ncup) (ncap + ncap) (n_m_cup_cap ncup ncap) =
  matrix_of_biperm 0 (ncap + ncap) (n_m_cup_cap 0 ncap) ×
  matrix_of_biperm (ncup + ncup) 0 (n_m_cup_cap ncup 0).
Proof.
  rewrite n_m_cup_cap_comm.
  rewrite n_m_cup_cap_stack_biperms_decomp.
  rewrite (n_m_cup_cap_comm ncap), (n_m_cup_cap_comm 0).
  rewrite matrix_of_stack_biperms' by (lia + auto_biperm).
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
  replace (n_m_cup_cap n m) with 
    (n_m_cup_cap (1 + (n - 1)) (0 + m)) by (f_equal; lia).
  rewrite n_m_cup_cap_plus_plus_decomp.
  rewrite matrix_of_stack_biperms' by (lia + auto_biperm).
  restore_dims.
  rewrite kron_mixed_product' by (f_equal; lia).
  rewrite matrix_of_biperm_n_m_cup_cap_0_r.
  rewrite kron_n_1 by auto_wf.
  restore_dims.
  rewrite cap_times_cup, Mmult_1_r by auto with wf_db.
  rewrite Mscale_kron_dist_l.
  rewrite kron_1_l by auto_wf.
  easy.
Qed.

Lemma n_m_cup_cap_times_up_cup_r n m (Hn : 1 < n) : 
  matrix_of_biperm (n + n) (m + m) (n_m_cup_cap n m) 
  × ((I (2 ^ 1) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (n + n - 3))) =
  matrix_of_biperm ((n - 1) + (n - 1)) (m + m) (n_m_cup_cap (n-1) m).
Proof.
  replace (n_m_cup_cap n m) with 
    (n_m_cup_cap (2 + (n - 2)) (0 + m)) by (f_equal; lia).
  rewrite n_m_cup_cap_plus_plus_decomp.
  rewrite matrix_of_stack_biperms' by (lia + auto_biperm).
  replace (I (2 ^ (n + n - 3))) with (I (2^1 * 2^(n + n - 4))) by 
    (rewrite <- Nat.pow_add_r; do 2 f_equal; lia).
  rewrite <- id_kron.
  restore_dims.
  rewrite <- kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product' by (reflexivity + f_equal; lia).
  (* rewrite n_m_cup_cap_comm. *)
  rewrite matrix_of_biperm_n_m_cup_cap_0_r.
  rewrite kron_n_S.
  rewrite kron_n_1 by auto with wf_db.
  restore_dims.
  rewrite cap_cap_cup_yank_eq, Mmult_1_r by auto with wf_db.
  rewrite <- (kron_n_1 (⟦⊃⟧)) by auto with wf_db.
  rewrite <- matrix_of_biperm_n_m_cup_cap_0_r.
  restore_dims.
  rewrite <- matrix_of_stack_biperms by auto with biperm_db.
  simpl.
  simpl_rewrite' (n_m_cup_cap_plus_plus_decomp 1 (n - 2) 0 m).
  f_equal; [lia|f_equal; lia].
Qed.

Lemma n_m_cup_cap_yank_one_r n m p (Hn : n <> 0) (Hp : p <> 0) : 
  matrix_of_biperm (n + n) (m + m) (n_m_cup_cap n m) ⊗ I (2 ^ p)
  × ((I (2 ^ (n + n - 1)) ⊗ ⟦ ⊂ ⟧) ⊗ I (2 ^ (p - 1))) =
  matrix_of_biperm ((n - 1) + (n - 1)) (m + m) (n_m_cup_cap (n-1) m) ⊗ I (2^p).
Proof.
  replace (n_m_cup_cap n m) with 
    (n_m_cup_cap ((n - 1) + 1) (m + 0)) by (f_equal; lia).
  rewrite n_m_cup_cap_plus_plus_decomp.
  rewrite matrix_of_stack_biperms' by (lia + auto_biperm).
  replace (2^ (n+n-1)) with (2 ^ (n-1+(n-1)) * (2^1)) by 
    (rewrite <- Nat.pow_add_r; f_equal; lia).
  rewrite <- id_kron.
  restore_dims.
  rewrite 3!kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product' by unify_pows_two.
  rewrite Mmult_1_r by auto with wf_db.
  restore_dims.
  f_equal; [unify_pows_two..|].
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