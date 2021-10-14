Require Export Node.
Require Export AdjMatrix.
Require Import Relations.
Require Import RelationClasses.
Require Import externals.QuantumLib.Quantum.

Definition SourceMap (nsrc : nat) : Type := nat -> 
                                            option nat. 
(* Represents source index -> node that is pointed to *)

Definition SinkMap (nsink : nat) : Type :=  nat -> 
                                            option nat. 
(* Represents node sink index ->  node that points to sink *)

(* The option types are used for easier ZX fusion,
   i.e. None corresponds to a src/sink still being 
   available *)

Definition emptySourceMap {n : nat} : SourceMap n :=
  fun _ => None.

Definition emptySinkMap {n : nat} : SourceMap n :=
  fun _ => None.

Inductive ZXDiagram : Type := 
  | ZX {n nsrc nsink} (adj : AdjMatrix n) (nmap : NodeMap n) (srcmap : SourceMap nsrc) 
        (sinkmap : SinkMap nsink): ZXDiagram.

Definition getZXSize (zx : ZXDiagram) :=
  match zx with
  | @ZX n _ _ _ _ _ _ => n
  end.

Definition getZXSrcSize (zx : ZXDiagram) :=
  match zx with
  | @ZX _ nsrc _ _ _ _ _ => nsrc
  end.

Definition getZXSinkSize (zx : ZXDiagram) :=
  match zx with
  | @ZX _ _ nsink _ _ _ _ => nsink
  end.

Definition getZXAdj (zx : ZXDiagram) := 
  match zx with 
  | ZX a _ _ _=> a 
  end.

Definition getZXNMap (zx : ZXDiagram) := 
  match zx with 
  | ZX _ nmap _ _  => nmap
  end.

Definition getZXSrcMap (zx : ZXDiagram) := 
  match zx with 
  | ZX _ _ srcmap _ => srcmap
  end.

Definition getZXSinkMap (zx : ZXDiagram) := 
  match zx with 
  | ZX _ _ _ sinkmap => sinkmap
  end.

Definition isConnected (map : nat -> option nat) nodeIdx srcIdx := 
  match (map srcIdx) with
  | None => false
  | Some nodeIdx' => nodeIdx =? nodeIdx
  end.
Transparent isConnected.

Fixpoint getSourceSinkConnectionHelper (map : nat -> option nat) nodeIdx n : nat := 
  match n with
  | 0 => if isConnected map nodeIdx 0 then 1 else 0
  | S n' => (if isConnected map nodeIdx n then 1 else 0) + (getSourceSinkConnectionHelper map nodeIdx n')
  end.

Definition getSourceInput (zx : ZXDiagram) nodeIdx := getSourceSinkConnectionHelper (getZXSrcMap zx) nodeIdx (getZXSrcSize zx).

Definition getInputCount (zx : ZXDiagram) nodeIdx := 
  let v := getZXNMap zx nodeIdx in
  let adj := (getZXAdj zx) in
  let adjSize := getZXSize zx in
  ((getSourceInput zx nodeIdx) + (@colSum adjSize nodeIdx adj))%nat.

Definition getSinkOutput (zx : ZXDiagram) nodeIdx := getSourceSinkConnectionHelper (getZXSinkMap zx) nodeIdx (getZXSinkSize zx).

Definition getOutputCount (zx : ZXDiagram) nodeIdx := 
  let v := getZXNMap zx nodeIdx in
  let adj := (getZXAdj zx) in
  let adjSize := getZXSize zx in
  ((getSinkOutput zx nodeIdx) + (@rowSum adjSize nodeIdx adj))%nat.
