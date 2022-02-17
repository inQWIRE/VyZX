Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.VectorStates.
Require Export ZX.
Require Export ZX_G_2.
Require Export Gates.
Require Export GateRules.
Require Export Rules.
Require Export VyZX.Proportional.
Require Import Setoid.

Local Open Scope R_scope.
Inductive A_G2_ZX : nat (* #inputs *) -> nat (* #outputs *) -> nat (* node id *) -> Type :=
  | A_G2_Empty n : A_G2_ZX 0 0 n
  | A_G2_Z_Spider_1_0 n (α : R) : A_G2_ZX 1 0 n
  | A_G2_Z_Spider_0_1 n (α : R) : A_G2_ZX 0 1 n
  | A_G2_Z_Spider_1_1 n (α : R) : A_G2_ZX 1 1 n (* Required to build wire construct *)
  | A_G2_Z_Spider_1_2 n (α : R) : A_G2_ZX 1 2 n
  | A_G2_Z_Spider_2_1 n (α : R) : A_G2_ZX 2 1 n
  | A_G2_Cap n : A_G2_ZX 0 2 n
  | A_G2_Cup n : A_G2_ZX 2 0 n
  | A_G2_Stack {nIn0 nIn1 nOut0 nOut1 n0 n1} (zx0 : A_G2_ZX nIn0 nOut0 n0) (zx1 : A_G2_ZX nIn1 nOut1 n1) n :
         A_G2_ZX (nIn0 + nIn1) (nOut0 + nOut1) n
  | A_G2_Compose {nIn nMid nOut n0 n1} (zx0 : A_G2_ZX nIn nMid n0) (zx1 : A_G2_ZX nMid nOut n1) n : A_G2_ZX nIn nOut n.
Local Close Scope R_scope.

Notation "⦰AG2" := A_G2_Empty. (* \revemptyset *)
Notation "⊂AG2" := A_G2_Cap. (* \subset *)
Notation "⊃AG2" := A_G2_Cup. (* \supset *)

Fixpoint A_G2_ZX_semantics {nIn nOut n} (zx : A_G2_ZX nIn nOut n) : 
  Matrix (2 ^ nOut) (2 ^nIn) := 
  match zx with
  | ⦰AG2 _ => G2_ZX_semantics ⦰G2
  | A_G2_Z_Spider_1_0 _ α => G2_ZX_semantics (G2_Z_Spider_1_0 α)
  | A_G2_Z_Spider_0_1 _ α => G2_ZX_semantics (G2_Z_Spider_0_1 α)
  | A_G2_Z_Spider_1_1 _ α => G2_ZX_semantics (G2_Z_Spider_1_1 α)
  | A_G2_Z_Spider_1_2 _ α => G2_ZX_semantics (G2_Z_Spider_1_2 α)
  | A_G2_Z_Spider_2_1 _ α => G2_ZX_semantics (G2_Z_Spider_2_1 α)
  | A_G2_Cap _ => G2_ZX_semantics (G2_Cap)
  | A_G2_Cup _ => G2_ZX_semantics (G2_Cup)
  | A_G2_Stack zx0 zx1  _=> (A_G2_ZX_semantics zx0) ⊗ (A_G2_ZX_semantics zx1)
  | @A_G2_Compose _ nMid _ _ _ zx0 zx1 _ => (A_G2_ZX_semantics zx1) × (nMid ⨂ hadamard) × (A_G2_ZX_semantics zx0)
  end.

Fixpoint A_G2_ZX_to_G2_ZX {nIn nOut n} (zx : A_G2_ZX nIn nOut n) : G2_ZX nIn nOut :=
  match zx with
  | ⦰AG2 _ => ⦰G2
  | A_G2_Z_Spider_1_0 _ α => G2_Z_Spider_1_0 α
  | A_G2_Z_Spider_0_1 _ α => G2_Z_Spider_0_1 α
  | A_G2_Z_Spider_1_1 _ α => G2_Z_Spider_1_1 α
  | A_G2_Z_Spider_1_2 _ α => G2_Z_Spider_1_2 α
  | A_G2_Z_Spider_2_1 _ α => G2_Z_Spider_2_1 α
  | A_G2_Cap _ => G2_Cap
  | A_G2_Cup _ => G2_Cup
  | A_G2_Stack zx0 zx1 _ => (A_G2_ZX_to_G2_ZX zx0) ↕G2 (A_G2_ZX_to_G2_ZX zx1)
  | A_G2_Compose zx0 zx1 _ => (A_G2_ZX_to_G2_ZX zx0) ⟷G2 (A_G2_ZX_to_G2_ZX zx1)
  end.

Fixpoint G2_ZX_to_A_G2_ZX_helper base {nIn nOut} (zx : G2_ZX nIn nOut) : (A_G2_ZX nIn nOut base) * nat :=
  match zx with
  | ⦰G2 => (⦰AG2 base, S base)
  | G2_Z_Spider_1_0 α => (A_G2_Z_Spider_1_0 base α, S base)
  | G2_Z_Spider_0_1 α => (A_G2_Z_Spider_0_1 base α, S base)
  | G2_Z_Spider_1_1 α => (A_G2_Z_Spider_1_1 base α, S base)
  | G2_Z_Spider_1_2 α => (A_G2_Z_Spider_1_2 base α, S base)
  | G2_Z_Spider_2_1 α => (A_G2_Z_Spider_2_1 base α, S base)
  | G2_Cap => (A_G2_Cap base, S base)
  | G2_Cup => (A_G2_Cup base, S base)
  | G2_Stack zx0 zx1 => let (zx0', base') := (G2_ZX_to_A_G2_ZX_helper (S base) zx0) in 
                      let (zx1', ret) := (G2_ZX_to_A_G2_ZX_helper base' zx1) in (A_G2_Stack zx0' zx1' base, S ret) 
  | G2_Compose zx0 zx1 => let (zx0', base') := (G2_ZX_to_A_G2_ZX_helper (S base) zx0) in 
                      let (zx1', ret) := (G2_ZX_to_A_G2_ZX_helper base' zx1) in (A_G2_Compose zx0' zx1' base, S ret) 
  end.

Definition G2_ZX_to_A_G2_ZX {nIn nOut} (zx : G2_ZX nIn nOut) := fst (G2_ZX_to_A_G2_ZX_helper 0 zx).

(* Todo: 
   - State/Prove no collisions
   - Add maps from node id -> [node id] * [node id] (i.e. map to connected spider/cap/cup) 
*)

Fixpoint collect_ids {nIn nOut n} (zx : A_G2_ZX nIn nOut n) : list nat :=
  match zx with
  | ⦰AG2 n => [n]
  | A_G2_Z_Spider_1_0 n _ => [n]
  | A_G2_Z_Spider_0_1 n _ => [n]
  | A_G2_Z_Spider_1_1 n _ => [n]
  | A_G2_Z_Spider_1_2 n _ => [n]
  | A_G2_Z_Spider_2_1 n _ => [n]
  | A_G2_Cap n => [n]
  | A_G2_Cup n => [n]
  | A_G2_Stack zx0 zx1 n => n :: (collect_ids zx0 ++ collect_ids zx1)
  | A_G2_Compose zx0 zx1 n => n :: (collect_ids zx0 ++ collect_ids zx1)
  end.

Definition WF_A_G2_ZX {nIn nOut n} (zx : A_G2_ZX nIn nOut n) := NoDup (collect_ids zx).
