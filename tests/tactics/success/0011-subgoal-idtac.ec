require Logic.
lemma foo : true /\ true
proof.
 split;[ | ].
 split.
 split.
save.

lemma foo1 : true /\ true
proof.
 split;[ | split].
 split.
save.

lemma foo2 : true /\ true
proof.
 split;[ split | ].
 split.
save.

lemma foo3 : true /\ true /\ true
proof.
 split;[ | split];[split | split | split].
save.

lemma foo4 : true /\ true /\ true
proof.
 split;[ | split];[split | | split].
 split.
save.

lemma foo5 : true /\ true /\ true
proof.
 split;[ | split];[split | | ].
 split.
 split.
save.

lemma foo6 : true /\ true /\ true
proof.
 split;[ | split];[ | | ].
 split.
 split.
 split.
save.

