import why3 "option" "Option".

op proj : 'a option -> 'a.

axiom proj_def : forall(x : 'a), proj(Some x) = x.