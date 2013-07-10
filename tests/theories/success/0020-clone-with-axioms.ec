theory T.
  axiom L : true.
  type t.
end T.

clone T as U proof L.
realize L. proof. admit. save.

op x : U.t.
