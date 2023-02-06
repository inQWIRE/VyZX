Require Export ZX.
Require Import externals.QuantumLib.Quantum.

Local Open Scope ZX_scope.

Definition braKetNM (bra: Matrix 2 1) (ket : Vector 2) n m : Matrix (2^n) (2^m) := 
  (n ⨂ ket) × (m ⨂ bra).
Transparent braKetNM.  

Local Open Scope matrix_scope.
Definition spiderSemanticsImpl (zx : ZXDiagram) (bra0 bra1 : Matrix 2 1) (ket0 ket1 : Vector 2) (α : R) (n m : nat) : Matrix (2 ^ n) (2 ^ m) :=
  (braKetNM bra0 ket0 n m) .+ (Cexp α) .* (braKetNM bra1 ket1 n m). 
Transparent spiderSemanticsImpl. 

Definition spiderSemantics (zx : ZXDiagram) nodeIdx := 
  let v := getZXNMap zx nodeIdx in
  let n := getInputCount zx nodeIdx in
  let m := getOutputCount zx nodeIdx in
  match v with
  | Z_Spider α => spiderSemanticsImpl zx (bra 0) (bra 1) (ket 0) (ket 1) α n m
  | X_Spider α => spiderSemanticsImpl zx (hadamard × (bra 0)) (hadamard × (bra 1)) (hadamard × (ket 0)) (hadamard × (ket 1)) α n m
  end.


Local Close Scope matrix_scope.
Local Close Scope ZX_scope.
