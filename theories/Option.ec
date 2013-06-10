import why3 "option" "Option".

(* NOTE: This assumes that all types are inhabited and
   interacts very badly with Coq. It should be discussed. *)
op proj:'a option -> 'a.
axiom proj_def: forall (x:'a), proj (Some x) = x.
