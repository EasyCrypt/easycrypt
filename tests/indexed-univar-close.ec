(* Close boundaries must resolve BOTH univar kinds (the closing API
   returns a combined substitution; a type-only close is no longer
   expressible). Regressions: dangling index univars used to persist
   in abbrev bodies, checked proc bodies, and have-hypotheses. *)

type {n} 'a vec.
op vinit {n} ['a] : 'a -> 'a vec<:n>.
op vsize {n} ['a] (v : 'a vec<:n>) : int = n.

(* abbrev: the body's inferred index links to the binder *)
abbrev vz {n} : int vec<:n> = vinit 0.

expect "* In [operators, predicates or exceptions]:

abbrev vz {n}  : int vec<:n> = vinit[:n] 0." by print vz.

(* proc bodies persist with resolved indices *)
module M = {
  proc f () : int vec<:3> = {
    var a : int vec<:3>;
    a <- vinit 0;
    return a;
  }
}.

(* have-hypotheses store resolved indices and remain usable *)
lemma t (w : int vec<:5>) : vsize w = 5.
proof.
have h : vsize[:5]<:int> w = 5 by trivial.
apply h.
qed.
