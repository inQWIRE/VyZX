Require Export Node.
Require Export AdjMatrix.
Require Import Relations.
Require Import RelationClasses.

Inductive ZXDiagram : Type := 
  | ZX n (adj : AdjMatrix n) (nmap : NodeMap n) : ZXDiagram.

Definition getZXAdj (zx : ZXDiagram) := 
  match zx with 
  | ZX _ a _ => a 
  end.

Definition getZXNMap (zx : ZXDiagram) := 
  match zx with 
  | ZX _ _ nmap => nmap
  end.
