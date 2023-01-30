Require Import ZXCore.
From VyZX Require Import Proportional.

Local Open Scope ZX_scope.

(** Gate Definitions in the ZX Calculus *)

Notation "'_Z_'" := (Z 1 1 PI) (at level 40).
Notation "'_X_'" := (X 1 1 PI) (at level 40).
Definition _Rz_ α : ZX 1 1 := Z 1 1 α.

Notation "'_H_'" := 
    ((Z 1 1 (PI/2)) ⟷ (X 1 1 (PI/2)) ⟷ (Z 1 1 (PI/2)))
    (at level 40).

Notation "'_CNOT_'" :=
  ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 0)).

Notation "'_CNOT_inv_'" := ((2 ↑ □) ⟷ _CNOT_ ⟷ (2 ↑ □)).

Notation "'_CNOT_R'" :=
  ((— ↕ X 1 2 0) ⟷ (Z 2 1 0 ↕ —)).

Notation "'_NOTC_'" :=
  ((— ↕ Z 1 2 0 ) ⟷ (X 2 1 0 ↕ —)).

Notation "'_NOTC_R'" :=
  ((X 1 2 0 ↕ —) ⟷ (— ↕ Z 2 1 0 )).


  

