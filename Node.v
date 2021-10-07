Require Export Reals.

Inductive Node : Set :=
| X_Spider : R -> Node
| Z_Spider : R -> Node.

Definition NodeMap (n : nat) : Type := nat -> Node.