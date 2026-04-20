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

(* Phase-3.5 — index inference at op-application sites.
   Allocates fresh TIUnivars for each idxvar of the op being called
   and unifies them against the call site via polynomial-normal-form
   equality. *)
op concat [n m 'a] (xs : 'a vec<:n>) (ys : 'a vec<:m>) : 'a vec<:n+m>.
op cons   [n 'a]   (x : 'a) (xs : 'a vec<:n>) : 'a vec<:n+1>.

(* Direct call: ?u_n in cons unifies with caller's n. *)
op single [n 'a] (x : 'a) (ys : 'a vec<:n>) : 'a vec<:n+1> = cons x ys.

(* Annotated result type identical to the inferred one. *)
op test1 [n m 'a] (x : 'a) (ys : 'a vec<:n>) (zs : 'a vec<:m>)
  : 'a vec<:(n+1)+m>
  = concat (cons x ys) zs.

(* Same body, but the annotated result type differs by associativity:
   (n+1)+m vs n+(1+m). Polynomial normalisation makes them equal. *)
op test2 [n m 'a] (x : 'a) (ys : 'a vec<:n>) (zs : 'a vec<:m>)
  : 'a vec<:n+(1+m)>
  = concat (cons x ys) zs.
