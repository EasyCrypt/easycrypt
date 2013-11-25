op p : bool.
op q : bool.

axiom A : p.

theory T.
  axiom A : q.

  lemma L : p.
  proof. by apply Top.A. qed.
end T.
