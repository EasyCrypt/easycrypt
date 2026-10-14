(* A single-target theory alias `theory X = T` inside a theory `W` is a
   component of `W` that names `T`: qualified names through it, such as
   `W.X.u`, resolve to the objects of `T`. They used to be unknown, as
   was the theory `W.X` itself. *)

require import AllCore.

theory T.
  type u.
  op o : u.

  theory Sub.
    type v.
  end Sub.
end T.

theory W.
  theory X = T.

  theory V.
    theory Y = T.Sub.
  end V.

  op inside : X.u = X.o.
end W.

op q1 : W.X.u = W.X.o.

lemma q1E : q1 = T.o by rewrite /q1.

(* through an alias nested deeper, and through a sub-theory of the
   target *)
op q2 : W.V.Y.v.
op q3 : W.X.Sub.v.

lemma inside_o : W.inside = T.o by rewrite /W.inside.

(* the alias as a theory name *)
expect "
theory T.
  (* import *) type u.
  
  (* import *) op o : u.
  
  (* import *) theory Sub.
                 (* import *) type v.
               end Sub.
end T.
" by print theory W.X.

(* an alias to a theory that contains an alias *)
theory W2.
  theory Z = W.
end W2.

op q4 : W2.Z.X.u = T.o.
