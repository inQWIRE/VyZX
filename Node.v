
Inductive Node : Set :=
| Terminus : Node
| X_Spider : C -> Node
| Z_Spider : C -> Node.

Definition isSpider (v : Node) : bool :=
match v with
| Terminus => false
| _ => true
end.

Definition isSpiderP (v : Node) : Prop :=
exists c, v = X_Spider c \/ v = Z_Spider c.

Definition isNotTerminus (v : Node) : Prop :=
v <> Terminus.

Lemma isSpiderPropToBool (v : Node) : isSpiderP v -> isSpider v = true.
Proof.
intros.
destruct H0.
destruct H0; rewrite H0; trivial.
Qed.

Lemma isSpiderBoolToProp (v : Node) : isSpider v = true -> isSpiderP v.
Proof.
intros.
destruct v.
- discriminate.
- exists c. left. trivial.
- exists c. right. trivial.
Qed.

Definition NodeMap (n : nat) := nat -> Node.
