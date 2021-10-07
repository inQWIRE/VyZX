Require Export Node.
Require Export AdjMatrix.
Require Import Relations.
Require Import RelationClasses.

Definition SourceMap (nsrc : nat) : Type := nat -> nat. (* Represents source index -> node that is pointed to *)

Definition SinkMap (nsink : nat) : Type := nat -> nat. (* Represents node that is exiting -> sink iindex*)

Inductive ZXDiagram : Type := 
  | ZX {n nsrc nsink} (adj : AdjMatrix n) (nmap : NodeMap n) (srcmap : SourceMap nsrc) (sinkmap : SinkMap nsink): ZXDiagram.

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