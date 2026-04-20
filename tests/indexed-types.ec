(* -------------------------------------------------------------------- *)
(* Phase-3 Slice A — concrete syntax for indexed types.
   Indices live in [...] (no apostrophe); applications use <:...:>. *)

(* Bare indexed type (no type parameters). *)
type [n] vec0.

(* Indexed and parametric. *)
type [n] 'a vec.

(* Multiple indices, multiple type parameters. *)
type [n m] ('a, 'b) mat.

(* Fully-applied (no free index variable): integer literals. *)
type three_vec = int vec<:3>.

(* Index expressions: + and *. The polynomial fragment is not yet
   reduced to canonical form at the surface, but Phase-1 ensures the
   resulting ty is hashconsed canonically. *)
type tagged    = int vec<:1+1>.
type two_three = int vec<:2*3>.

(* Index variables in scope, used in the body. *)
type [n] 'a my_vec  = 'a vec<:n>.
type [n m] 'a my_pair = 'a vec<:n+m>.

(* Phase-3 Slice B — indices on operator / predicate / axiom binders.
   Indexed application at use sites is not yet supported (it would
   need TIUnivar-based index inference); the binders themselves
   parse and typecheck. *)
op  ix_op  [n 'a] (xs : 'a vec<:n>) : 'a vec<:n+1>.
pred ix_pr [n 'a] : 'a vec<:n>.
axiom ix_ax [n 'a] : true.
