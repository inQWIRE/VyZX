Require Import externals.QuantumLib.Quantum.
Require Export ZX.

Local Open Scope ZX_scope.

Definition ZX_H := 
    (Z_Spider 1 1 (PI/2)) ⟷ (X_Spider 1 1 (PI/2)) ⟷ (Z_Spider 1 1 (PI/2)).
Global Opaque ZX_H.

Notation nH := (fun n => nStack1 n ZX_H).

Definition ZX_CNOT_l : ZX 2 2 :=  
        ((Z_Spider 1 2 0%R) ↕ Wire) ⟷ (Wire ↕ (X_Spider 2 1 0%R)).
Global Opaque ZX_CNOT_l.

Definition ZX_CNOT_r : ZX 2 2 := 
    (Wire ↕ (X_Spider 1 2 0%R)) ⟷ ((Z_Spider 2 1 0%R) ↕ Wire).
Global Opaque ZX_CNOT_r.

Definition ZX_S : ZX 1 1 := Z_Spider 1 1 (PI / 2).
Definition ZX_T : ZX 1 1 := Z_Spider 1 1 (PI / 4).
Definition ZX_Z : ZX 1 1 := Z_Spider 1 1 PI.
Definition ZX_X : ZX 1 1 := X_Spider 1 1 PI.
Definition ZX_Y : ZX 1 1 := ZX_Z ⟷ ZX_X.
Global Opaque ZX_Z.
Global Opaque ZX_X.
Global Opaque ZX_Y.

Notation ZX_CNOT := ZX_CNOT_l.
Global Opaque ZX_CNOT.

Definition ZX_FLIPPED_CNOT := 
    (Wire ↕ (Z_Spider 1 2 0%R)) ⟷ ((X_Spider 2 1 0%R) ↕ Wire).
   
Definition ZX_SWAP : ZX 2 2 :=
    ZX_CNOT ⟷ ZX_FLIPPED_CNOT ⟷ ZX_CNOT.
Global Opaque ZX_SWAP.

Local Close Scope ZX_scope.
