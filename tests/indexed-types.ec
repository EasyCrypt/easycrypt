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

(* Phase 4 — cloning with index instantiation.
   `clone with type [k] 'a vec = body` substitutes every occurrence of
   the indexed type, binding the source's idxvars to the call-site
   index expressions when the body references them. *)
type [k] 'a coll.

theory ClonedT.
  type [n] 'a target.
end ClonedT.

(* Drop the index, use a non-indexed type. *)
clone ClonedT as Erased with
  type [k] 'a target = int.

(* Propagate the index through to another indexed type. *)
clone ClonedT as Forwarded with
  type [k] 'a target = 'a coll<:k>.

(* Use a polynomial of the binder. *)
clone ClonedT as Bumped with
  type [k] 'a target = 'a coll<:k+1>.

(* Gap A — explicit index instantiation at op call sites.
   Syntax: f[:idx, ...] for indices, optionally followed by <:ty>. *)
op size [n 'a] (xs : 'a vec<:n>) : int.
op count [n 'a] : int.

(* index inferred from xs's type *)
op a_test1 [n 'a] (xs : 'a vec<:n>) : int = size xs.

(* index supplied explicitly *)
op a_test2 ['a] (xs : 'a vec<:5>) : int = size[:5] xs.

(* both index and type explicit (no inference path for either) *)
op a_test3 : int = count[:5]<:int>.

(* Gap B — polynomial unification beyond naked TIUnivar.
   The unifier can solve any equation where exactly one TIUnivar
   appears with coefficient ±1 and the residual stays non-negative. *)

op tail [n 'a] (xs : 'a vec<:n+1>) : 'a vec<:n>.

(* Caller passes a vector of length 5; n must be inferred so that
   n+1 = 5, i.e. n = 4. The naked-univar special case used to fail
   here because ?u_n was not on its own. *)
op b_test1 ['a] (xs : 'a vec<:5>) : 'a vec<:4> = tail xs.

(* Unification of [?u_n + 1] against [m + 5] forces ?u_n = m + 4. *)
op b_test2 [m 'a] (xs : 'a vec<:m+5>) : 'a vec<:m+4> = tail xs.

(* Symmetric form: univar on the rhs of the equation. *)
op head [n 'a] (xs : 'a vec<:n+1>) : 'a.
op b_test3 ['a] (xs : 'a vec<:7>) : 'a = head xs.
