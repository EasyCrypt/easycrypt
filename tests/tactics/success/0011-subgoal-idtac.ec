require Logic.
lemma foo : true /\ true.
proof.
 split;[ | ].
 split.
 split.
qed.

lemma foo1 : true /\ true.
proof.
 split;[ | split].
 split.
qed.

lemma foo2 : true /\ true.
proof.
 split;[ split | ].
 split.
qed.

lemma foo3 : true /\ true /\ true.
proof.
 split;[ | split];[split | split | split].
qed.

lemma foo4 : true /\ true /\ true.
proof.
 split;[ | split];[split | | split].
 split.
qed.

lemma foo5 : true /\ true /\ true.
proof.
 split;[ | split];[split | | ].
 split.
 split.
qed.

lemma foo6 : true /\ true /\ true.
proof.
 split;[ | split];[ | | ].
 split.
 split.
 split.
qed.

