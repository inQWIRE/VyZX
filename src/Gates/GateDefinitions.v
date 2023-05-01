Require Import ZXCore.
From VyZX Require Import Proportional.

Local Open Scope ZX_scope.

(** Gate Definitions in the ZX Calculus *)

Notation "'_Z_'" := (𝒵 1 1 PI) (at level 40).
Notation "'_X_'" := (𝒳 1 1 PI) (at level 40).
Definition _Rz_ α : ZX 1 1 := 𝒵 1 1 α.

Notation "'_H_'" := 
    ((𝒵 1 1 (PI/2)) ⟷ (𝒳 1 1 (PI/2)) ⟷ (𝒵 1 1 (PI/2)))
    (at level 40).

Notation "'_CNOT_'" :=
  ((𝒵 1 2 0 ↕ —) ⟷ (— ↕ 𝒳 2 1 0)).

Notation "'_CNOT_inv_'" := ((2 ↑ □) ⟷ _CNOT_ ⟷ (2 ↑ □)).

Notation "'_CNOT_R'" :=
  ((— ↕ 𝒳 1 2 0) ⟷ (𝒵 2 1 0 ↕ —)).

Notation "'_NOTC_'" :=
  ((— ↕ 𝒵 1 2 0 ) ⟷ (𝒳 2 1 0 ↕ —)).

Notation "'_NOTC_R'" :=
  ((𝒳 1 2 0 ↕ —) ⟷ (— ↕ 𝒵 2 1 0 )).

Notation "'_3_CNOT_SWAP_'" :=
  (_CNOT_ ⟷ _NOTC_ ⟷ _CNOT_).
  

