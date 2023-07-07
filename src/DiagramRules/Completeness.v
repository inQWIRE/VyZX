Require Import CoreData.

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_SUP : forall α, ((Z 0 1 α) ↕ (Z 0 1 (α + PI))) ⟷ (X 2 1 0) ∝ Z 0 2 (2 *α + PI) ⟷ X 2 1 0.
Proof.
  intros.
  prop_exists_nonzero 1;
  simpl;
  unfold X_semantics.
  solve_matrix.
  - C_field_simplify; [ | split; nonzero ].
    repeat rewrite Cexp_add.
    autorewrite with Cexp_db.
    C_field_simplify.
    repeat rewrite <- Cexp_add.
    replace ((R1 + R1)%R, (R0 + R0)%R) with C2 by lca.
    apply Cplus_simplify; try easy.
    rewrite <- 3 Cmult_assoc.
    apply Cmult_simplify; try easy.
    rewrite Cmult_assoc.
    rewrite <- Cexp_add.
    replace (α + α)%R with (2 * α)%R by lra.
    lca.
  - C_field_simplify; [ | split; nonzero ].
    repeat rewrite Cexp_add.
    autorewrite with Cexp_db.
    C_field_simplify.
    repeat rewrite <- Cexp_add.
    lca.
Qed.  

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_C : forall α β γ,
  (Z 1 2 0) ⟷ 
  (X 1 2 0 ↕ X 1 2 PI) ⟷ 
  (Z 1 0 α ↕ Z 1 2 α ↕ Z 1 2 β ↕ Z 1 0 β) ⟷ 
  (X 1 2 (- γ) ↕ X 2 1 γ ↕ —) ⟷ (— ↕ Z 2 1 0 ↕ —) ∝ 
    (Z 1 2 0) ⟷ 
    (X 1 2 PI ↕ X 1 2 0) ⟷ 
    (Z 1 0 β ↕ Z 1 2 β ↕ Z 1 2 α ↕ Z 1 0 α) ⟷ 
    (— ↕ X 2 1 (- γ) ↕ X 1 2 γ) ⟷ 
    (— ↕ Z 2 1 0 ↕ —).
Proof. (* solve matrix takes forever *)
Abort.

(* @nocheck name *)
(* Conventional name *)
Lemma completeness_BW :
  (Z 0 1 (PI / 4) ↕ Z 1 2 0 ↕ Z 0 1 (PI / 4)) ⟷ 
  (X 2 1 0 ↕ X 2 1 0) ⟷
  (Z 1 1 (- PI / 2) ↕ (Z 1 0 (PI / 4))) ⟷
  (X 1 2 0) ⟷
  (Z 1 0 (PI / 4) ↕ Z 1 2 0 ↕ (Z 0 1 (PI / 4))) ⟷
  (— ↕ X 2 1 0) ⟷
  (— ↕ Z 1 0 (PI / 4)) ∝
  (X 1 1 (PI / 2)) ⟷
  (Z 1 1 (PI / 4)) ⟷
  (X 1 2 PI) ⟷ 
  (Z 1 0 (PI / 4) ↕ Z 1 2 0 ↕ (Z 0 1 (PI / 4))) ⟷
  (— ↕ X 2 1 0) ⟷
  (— ↕ Z 1 0 (PI / 4)).
Proof. (* solve matrix takes forever *)
Abort.