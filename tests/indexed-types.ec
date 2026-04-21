(* -------------------------------------------------------------------- *)
(* Phase-3 Slice A — concrete syntax for indexed types.
   Index binders use `{...}` and come first; type-variable binders
   stay in `[...]`. Type-application indices use `<:...>`. *)

(* Bare indexed type (no type parameters). *)
type {n} vec0.

(* Indexed and parametric. *)
type {n} 'a vec.

(* Multiple indices, multiple type parameters. *)
type {n m} ('a, 'b) mat.

(* Fully-applied (no free index variable): integer literals. *)
type three_vec = int vec<:3>.

(* Index expressions: + and *. The polynomial fragment is not yet
   reduced to canonical form at the surface, but Phase-1 ensures the
   resulting ty is hashconsed canonically. *)
type tagged    = int vec<:1+1>.
type two_three = int vec<:2*3>.

(* Index variables in scope, used in the body. *)
type {n}   'a my_vec  = 'a vec<:n>.
type {n m} 'a my_pair = 'a vec<:n+m>.

(* Phase-3 Slice B — indices on operator / predicate / axiom binders. *)
op  ix_op  {n} ['a] (xs : 'a vec<:n>) : 'a vec<:n+1>.
pred ix_pr {n} ['a] : 'a vec<:n>.
axiom ix_ax {n} ['a] : true.

(* Phase-3.5 — index inference at op-application sites. *)
op concat {n m} ['a] (xs : 'a vec<:n>) (ys : 'a vec<:m>) : 'a vec<:n+m>.
op cons   {n}   ['a] (x : 'a) (xs : 'a vec<:n>) : 'a vec<:n+1>.

(* Direct call: ?u_n in cons unifies with caller's n. *)
op single {n} ['a] (x : 'a) (ys : 'a vec<:n>) : 'a vec<:n+1> = cons x ys.

(* Annotated result type identical to the inferred one. *)
op test1 {n m} ['a] (x : 'a) (ys : 'a vec<:n>) (zs : 'a vec<:m>)
  : 'a vec<:(n+1)+m>
  = concat (cons x ys) zs.

(* Same body, but the annotated result type differs by associativity:
   (n+1)+m vs n+(1+m). Polynomial normalisation makes them equal. *)
op test2 {n m} ['a] (x : 'a) (ys : 'a vec<:n>) (zs : 'a vec<:m>)
  : 'a vec<:n+(1+m)>
  = concat (cons x ys) zs.

(* Phase 4 — cloning with index instantiation. *)
type {k} 'a coll.

theory ClonedT.
  type {n} 'a target.
end ClonedT.

(* Drop the index, use a non-indexed type. *)
clone ClonedT as Erased with
  type {k} 'a target = int.

(* Propagate the index through to another indexed type. *)
clone ClonedT as Forwarded with
  type {k} 'a target = 'a coll<:k>.

(* Use a polynomial of the binder. *)
clone ClonedT as Bumped with
  type {k} 'a target = 'a coll<:k+1>.

(* Gap A — explicit index instantiation at op call sites.
   Syntax: f[:idx, ...] for indices, optionally followed by <:ty>. *)
op size  {n} ['a] (xs : 'a vec<:n>) : int.
op count {n} ['a] : int.

(* index inferred from xs's type *)
op a_test1 {n} ['a] (xs : 'a vec<:n>) : int = size xs.

(* index supplied explicitly *)
op a_test2 ['a] (xs : 'a vec<:5>) : int = size[:5] xs.

(* both index and type explicit (no inference path for either) *)
op a_test3 : int = count[:5]<:int>.

(* Gap B — polynomial unification beyond naked TIUnivar. *)
op tail {n} ['a] (xs : 'a vec<:n+1>) : 'a vec<:n>.

(* Caller passes a vector of length 5; n must be inferred so that
   n+1 = 5, i.e. n = 4. *)
op b_test1 ['a] (xs : 'a vec<:5>) : 'a vec<:4> = tail xs.

(* Unification of [?u_n + 1] against [m + 5] forces ?u_n = m + 4. *)
op b_test2 {m} ['a] (xs : 'a vec<:m+5>) : 'a vec<:m+4> = tail xs.

(* Symmetric form: univar on the rhs of the equation. *)
op head {n} ['a] (xs : 'a vec<:n+1>) : 'a.
op b_test3 ['a] (xs : 'a vec<:7>) : 'a = head xs.

(* Gap C — non-refining indexed datatypes and records. *)
type {n} 'a ivec = [ INil | ICons of 'a & 'a ivec<:n> ].

op c_test1 : int ivec<:0> = INil.
op c_test2 (x : int) (xs : int ivec<:5>) : int ivec<:5> = ICons x xs.

(* Plain match expression on indexed datatype. *)
op c_test3 (xs : int ivec<:5>) : int =
  match xs with
  | INil      => 0
  | ICons y _ => y
  end.

(* Matchfix on indexed datatype with index binder on the op itself. *)
op c_test4 {n} (d : int) (xs : int ivec<:n>) : int =
  with xs = INil      => d
  with xs = ICons y _ => y.

(* Indexed record. *)
type {n} 'a irec = { ivalue : 'a; idummy : 'a ivec<:n> }.

op c_test5 (x : int) (xs : int ivec<:0>) : int irec<:0> =
  {| ivalue = x; idummy = xs |}.

op c_test6 (r : int irec<:7>) : int = r.`ivalue.

(* Gap F — SMT translation via per-index monomorphisation. *)
op vfn {n} : int vec<:n>.

lemma f_test1 : vfn[:5] = vfn[:5].
proof. smt(). qed.

lemma f_test2 : c_test1 = c_test1.
proof. smt(). qed.

(* Two distinct concrete indices get distinct Why3 sorts. *)
op f_vec3 : int vec<:3>.
op f_vec5 : int vec<:5>.

lemma f_test3 : f_vec3 = f_vec3 /\ f_vec5 = f_vec5.
proof. smt(). qed.

(* Lemmas accept the same `{n} ['a]` binder syntax as ops. SMT
   translation skips goals with bound (non-closed) indices, so these
   are discharged with [trivial] rather than [smt()]. *)
lemma f_test4 {n} ['a] (x : 'a) (xs : 'a vec<:n>) :
  cons x xs = cons x xs.
proof. trivial. qed.

lemma f_test5 {n} ['a] :
  forall (x : 'a) (xs : 'a vec<:n>), cons x xs = cons x xs.
proof. move => x xs; trivial. qed.

(* Index binders come AFTER the operator name, like type binders.
   No ambiguity with the leading [opaque] tag bracket because indices
   use a different bracket family. *)
op "_.[_]" {n} (w : int vec<:n>) (_ : int) : bool.

(* Tags use the existing leading bracket. *)
op [opaque] g_const : int = 42.
op [opaque smt_opaque] g_const2 : int = 7.

(* Bound idxvars are visible as int-typed formula locals in the body
   of axioms / lemmas / ops / preds / abbreviations. The same ident
   plays both roles: index in `vec<:n>` positions, and integer term
   in the surrounding formula. *)
require import AllCore List.

op id_bits {n} : int vec<:n> -> int list.

axiom id_size {n} (v : int vec<:n>) :
  size (id_bits[:n] v) = n + 0.

(* Rewrite tactic on indexed lemmas: opening an indexed lemma must
   substitute through both type-univars AND index-univars in its
   stored body, otherwise residual TIUnivars leak into operator
   signatures and the matcher sees two distinct nodes that print
   identically but fail to unify. *)
op cat_words {m n} (wm : int vec<:m>) (wn : int vec<:n>) : int vec<:m+n>.

axiom cat_words_self {m n} (wm : int vec<:m>) (wn : int vec<:n>) :
  cat_words wm wn = cat_words wm wn.

lemma cat_test {m n} (wm : int vec<:m>) (wn : int vec<:n>) :
  cat_words wm wn = cat_words wm wn.
proof. rewrite cat_words_self. trivial. qed.

(* Op unfolding propagates idxvar substitution into nested op
   signatures. Without this, the body's nested-op f_types still
   reference the unfolded op's bound idxvar (instead of the call-site
   value), and a follow-up rewrite cannot match those nested ops.
   Mirrors the user's [(_.[_])] / [(++)] / [bits_cat] case. *)
op size_of {n} (xs : int vec<:n>) : int.

(* Op whose body uses [size_of], itself indexed. Unfolding [via_size]
   must rewrite [size_of]'s f_ty to use the call-site index. *)
op via_size {n} (xs : int vec<:n>) : int = size_of xs.

axiom size_of_self {n} (xs : int vec<:n>) :
  size_of xs = size_of xs.

lemma unfold_then_rewrite {n} (xs : int vec<:n>) :
  via_size xs = via_size xs.
proof. move=> @/via_size. rewrite size_of_self. trivial. qed.

(* When a lemma's body uses an idxvar [n] both as a tindex and as an
   int term (via Phase-2's shared namespace), opening the lemma must
   substitute BOTH the tindex side ([TIVar n_lem]) and the formula-
   local side ([Flocal n_lem]). Otherwise the rewrite leaves a
   dangling [Flocal n_lem] in the goal. *)
op size_v {n} (xs : int vec<:n>) : int.
axiom size_v_eq_n {n} (xs : int vec<:n>) : size_v xs = n.

lemma rewrite_with_int_form {m n} (wm : int vec<:m>) (wn : int vec<:n>) :
  size_v wm = m.
proof. rewrite size_v_eq_n. trivial. qed.

(* `have := lemma[:idx]` with explicit index instantiation must
   substitute the idxvar in BOTH tindex positions and formula-locals.
   The explicit-index path is process_named_pterm, distinct from the
   no-index pt_of_uglobal_r path. *)
op vec_at {n} (xs : int vec<:n>) (i : int) : int.

axiom vec_at_n_int {n} (xs : int vec<:n>) :
  vec_at xs 0 = n + n.

lemma test_have {m n} (wm : int vec<:m>) (wn : int vec<:n>) :
  true.
proof. have := vec_at_n_int[:m + n]. trivial. qed.

(* Bare [rewrite L] (no explicit index) on an indexed lemma whose
   pattern is a single-univar Fop application (e.g. mk[:?u]): the
   matcher's Fop case must attempt index unification so [?u] gets
   bound to the goal's index polynomial. *)
op build {n} : int -> int vec<:n>.
op extract {n} : int vec<:n> -> int.

axiom buildK {n} (k : int) : extract (build[:n] k) = k.

lemma test_bare_rewrite {m n} (wm : int vec<:m>) (wn : int vec<:n>) :
  extract (build[:m + n] 42) = 42.
proof. rewrite buildK. trivial. qed.

(* When [Ax.instantiate] / [Op.reduce] is invoked with idxs that
   still contain unresolved [TIUnivar]s (because matching hasn't
   pinned them yet), [f_of_tindex_opt] returns [None] and the form-
   side binding is silently skipped — the form-side stays
   unsubstituted and gets resolved later via [pte_idx_link]. The
   asserting variant of [f_of_tindex] used to crash here. *)
op midx {n} (xs : int vec<:n>) (k : int) : int.

axiom midx_self {n} (xs : int vec<:n>) (k : int) :
  midx xs k = midx xs k.

lemma test_chain {m n} (wm : int vec<:m>) (wn : int vec<:n>) :
  midx wm 1 = midx wm 1.
proof. rewrite midx_self. rewrite midx_self. trivial. qed.

(* Each idxvar is a non-negative integer by Phase-2 design. The proof
   goal is wrapped (inside the lemma's [pa_vars] forall) with one
   [0 <= n_i =>] implication per idxvar; the user introduces them
   on demand via [move=>]. The implications never leak into the
   saved [ax_spec] — only the proof goal sees them. *)
lemma idx_ge0_simple {n} : 0 <= n.
proof. move=> Hn. trivial. qed.

lemma idx_ge0_smt {m n} : 0 <= m + n.
proof. move=> Hm Hn. smt(). qed.

(* Backward compat: [pa_vars] auto-intro still works because the
   implications are pushed inside the forall, not at the top. *)
lemma idx_with_args {n} (xs : int vec<:n>) : 0 <= n.
proof. move=> Hn. trivial. qed.
