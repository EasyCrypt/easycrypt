section.
    declare type t.

    theory T.
        op foo : t.
    end T.

    op bar : t = T.foo.
end section.

lemma L (y x : unit): (idfun bar = y) =>
idfun T.foo = x /\ idfun bar = y.
proof.
move => yP.
rewrite yP.
abort.