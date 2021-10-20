Require Import externals.QuantumLib.Quantum.
Require Export ZX.

Definition ZX_H := 
    (Compose 
        (Z_Spider 1 1 (PI/2)) 
        (Compose 
            (X_Spider 1 1(PI/2)) 
            (Z_Spider 1 1 (PI/2)))).

Definition ZX_CNOT_l : ZX 2 2 := 
    (Compose 
        (Stack 
            (Z_Spider 1 2 0%R) 
            Wire) 
        (Stack 
            Wire 
            (X_Spider 2 1 0%R))).

Definition ZX_CNOT_r : ZX 2 2 := 
    (Compose 
        (Stack 
            Wire 
            (X_Spider 1 2 0%R))
        (Stack 
            (Z_Spider 2 1 0%R) 
            Wire)).

Definition ZX_S : ZX 1 1 := Z_Spider 1 1 (PI / 2).
Definition ZX_T : ZX 1 1 := Z_Spider 1 1 (PI / 4).

Notation ZX_CNOT := ZX_CNOT_l.
