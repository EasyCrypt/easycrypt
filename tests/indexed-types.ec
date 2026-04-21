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

(* Gap C — non-refining indexed datatypes and records. *)

(* Indexed datatype: constructor result type carries the index;
   index unification at constructor application sites recovers it. *)
type [n] 'a ivec = [ INil | ICons of 'a & 'a ivec<:n> ].

op c_test1 : int ivec<:0> = INil.
op c_test2 (x : int) (xs : int ivec<:5>) : int ivec<:5> = ICons x xs.

(* Plain match expression on indexed datatype. *)
op c_test3 (xs : int ivec<:5>) : int =
  match xs with
  | INil      => 0
  | ICons y _ => y
  end.

(* Matchfix on indexed datatype with index binder on the op itself. *)
op c_test4 [n] (d : int) (xs : int ivec<:n>) : int =
  with xs = INil      => d
  with xs = ICons y _ => y.

(* Indexed record. Auto-generated constructor [mk_irec] and projectors
   [`ivalue], [`idummy] all carry the index. *)
type [n] 'a irec = { ivalue : 'a; idummy : 'a ivec<:n> }.

op c_test5 (x : int) (xs : int ivec<:0>) : int irec<:0> =
  {| ivalue = x; idummy = xs |}.

op c_test6 (r : int irec<:7>) : int = r.`ivalue.

(* Gap F — SMT translation via per-index monomorphisation.
   Concrete indices turn `vec<:3>` into a fresh Why3 sort `vec_3`.
   Goals that mention only concrete indices make it through to SMT;
   goals with free index variables still fall cleanly into the
   [CanNotTranslate] skip (no crash, no proof, per-goal skip). *)

op vfn [n] : int vec<:n>.

lemma f_test1 : vfn[:5] = vfn[:5].
proof. smt(). qed.

lemma f_test2 : c_test1 = c_test1.
proof. smt(). qed.

(* Two distinct concrete indices get distinct Why3 sorts. *)
op f_vec3 : int vec<:3>.
op f_vec5 : int vec<:5>.

lemma f_test3 : f_vec3 = f_vec3 /\ f_vec5 = f_vec5.
proof. smt(). qed.
