(* Index-carrying AST nodes at desugaring sites, and chained index
   univars in proof terms.

   - LvMap: the map-set assignment [a.[e] <- v] must persist the set
     operator WITH its inferred indices;
   - records: constructor / projection nodes carry the record's
     instance indices (as does the datatype-match desugar);
   - proof terms: an applied lemma argument may link the lemma's index
     univar to the argument's own univar (a chain); concretization
     must chase the chain, including into compound indices. *)

require import AllCore IArray.

(* LvMap (finding: index-erased set operator persisted) *)
module M = {
  proc f (a : int array<:4>) : int array<:4> = {
    a.[0] <- 7;
    return a;
  }
}.

lemma lvmap_wp (a0 : int array<:4>) :
  hoare [M.f : a = a0 ==> res = a0.[0 <- 7]].
proof. proc. wp. skip. by move => &m ->. qed.

(* indexed records: nodes carry indices; conversion works *)
type {n} 'a vec.
op mk {n} ['a] : 'a vec<:n>.
type {n} 'a r = { fld : 'a vec<:n> }.

op build : int r<:5> = {| fld = mk |}.

lemma build_fld : build.`fld = mk[:5]<:int>.
proof. by rewrite /build. qed.

(* SMT on indexed records degrades cleanly (no sound erased encoding
   yet: CanNotTranslate, not a Why3 arity anomaly) *)
lemma build_fld_smt : build.`fld = mk[:5]<:int>.
proof.
fail smt().
by rewrite /build.
qed.

(* chained index univars through proof-term application *)
op vinit {n} ['a] : 'a -> 'a vec<:n>.
op vsize {n} ['a] (v : 'a vec<:n>) : int = n.

lemma vsz {n} ['a] (v : 'a vec<:n>) : vsize v = n.
proof. by rewrite /vsize. qed.

lemma chained : vsize (vinit[:7]<:int> 0) = 7.
proof. apply (vsz (vinit 0)). qed.

(* compound resolved index through the link (n+1 shape) *)
lemma chained2 {m} (w : int vec<:m>) : vsize (vinit[:m+1]<:int> 0) = m + 1.
proof. apply (vsz (vinit 0)). qed.
