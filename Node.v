Require Export Reals.

Inductive Node : Set :=
| Terminus : Node
| X_Spider : R -> Node
| Z_Spider : R -> Node.

Definition isSpider (v : Node) : bool :=
match v with
| Terminus => false
| _ => true
end.

Definition isSpiderP (v : Node) : Prop :=
exists r, v = X_Spider r \/ v = Z_Spider r.

Definition isNotTerminus (v : Node) : Prop :=
v <> Terminus.

Lemma isSpiderPropToBool (v : Node) : isSpiderP v -> isSpider v = true.
Proof.
intros.
destruct H.
destruct H; rewrite H; trivial.
Qed.

Lemma isSpiderBoolToProp (v : Node) : isSpider v = true -> isSpiderP v.
Proof.
intros.
destruct v.
- discriminate.
- exists r. left. trivial.
- exists r. right. trivial.
Qed.

Definition NodeMap (n : nat) := nat -> Node.
