Require Import ZXCore.
From VyZX Require Import Proportional.

Local Open Scope ZX_scope.

(** Gate Definitions in the ZX Calculus *)

Notation "'_S_'" := (Z 1 1 (PI / 2)) (at level 40).
Notation "'_T_'" := (Z 1 1 (PI / 4)) (at level 40).
Notation "'_Z_'" := (Z 1 1 PI) (at level 40).
Notation "'_X_'" := (X 1 1 PI) (at level 40).
Notation "'_Y_'" := (_Z_ ⟷ _X_) (at level 40).

Notation "'_H_'" := 
    ((Z 1 1 (PI/2)) ⟷ (X 1 1 (PI/2)) ⟷ (Z 1 1 (PI/2)))
    (at level 40).

Notation "'_CNOT_'" :=
  ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 0)).

Notation "'_CNOT_R'" :=
  ((— ↕ X 1 2 0) ⟷ (Z 2 1 0 ↕ —)).

Notation "'_NOTC_'" :=
  ((— ↕ Z 1 2 0 ) ⟷ (X 2 1 0 ↕ —)).

Notation "'_NOTC_R'" :=
  ((X 1 2 0 ↕ —) ⟷ (— ↕ Z 2 1 0 )).

(** Gate rewriting rules *)

Lemma _H_is_Box : _H_ ∝ □.
Proof.
  prep_proportional.
  prop_exists_nonzero (Cexp (PI/4)).
  simpl.
  unfold X_semantics, Z_semantics.
  Msimpl.
  solve_matrix;
  field_simplify_eq [Cexp_PI2 Cexp_PI4 Ci2 Csqrt2_sqrt2_inv Csqrt2_inv]; 
  try apply c_proj_eq; try simpl; try R_field_simplify; try reflexivity; (try split; try apply RtoC_neq; try apply sqrt2_neq_0; try auto).
Qed.

Lemma _H_H_is_wire : □ ⟷ □ ∝ —.
Proof.
  prep_proportional.
  prop_exists_nonzero 1; Msimpl; simpl.
  apply MmultHH.
Qed.

Lemma _CNOT_equiv :
  _CNOT_R ∝ _CNOT_.
Proof.
  prep_proportional.
  prop_exists_nonzero 1.
  simpl.
  Msimpl.
  restore_dims.
  
  rewrite (kron_mixed_product (Z_semantics 2 1 0) (I 2) (I 2) (X_semantics 1 2 0)).
  

