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

Definition spiderSemantics (n : nat) (m : nat) := .

