Require Export Reals.

Inductive Node : Set :=
| Source : nat -> Node 
| Sink : nat -> Node
| X_Spider : R -> Node
| Z_Spider : R -> Node.

Definition isSpider (v : Node) : bool :=
match v with
| Source _ => false
| Sink _ => false
| _ => true
end.

Definition isSpiderP (v : Node) : Prop :=
exists r, v = X_Spider r \/ v = Z_Spider r.

Definition isNotTerminus (v : Node) : Prop :=
forall n, v <> Source n /\ v <> Sink n.

Lemma isSpiderPropToBool (v : Node) : isSpiderP v -> isSpider v = true.
Proof.
intros.
destruct H.
destruct H; rewrite H; trivial.
Qed.

Lemma isSpiderBoolToProp (v : Node) : isSpider v = true -> isSpiderP v.
Proof.
intros.
destruct v; try discriminate (* Source/Sink *).
- exists r. left. trivial.
- exists r. right. trivial.
Qed.

Definition NodeMap (n : nat) : Type := nat -> Node.
