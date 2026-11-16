(* Named (possibly partial) index instantiation, and its interaction
   with named type-variable instantiation: `f[:n = 3, m = 4]<:'a = int>`.
   The index and type sides are independent: each may be positional
   or named. *)

type {n} 'a vec.

op f {n m} ['a, 'b] : 'a -> 'b -> bool.
op cat {n m} ['a] : 'a vec<:n> -> 'a vec<:m> -> 'a vec<:n+m>.

(* both sides named *)
op g1 = f[:n = 3, m = 4]<:'a = int, 'b = real>.

(* named indices, positional types *)
op g2 = f[:n = 3, m = 4]<:int, real>.

(* positional indices, named types (rejected by the parser before) *)
op g3 = f[:3, 4]<:'a = int, 'b = real>.

(* named indices need not follow declaration order *)
op g4 = f[:m = 4, n = 3]<:int, real>.

(* partial named instantiation: [m] is inferred from the arguments *)
op g5 (u : int vec<:3>) (v : int vec<:5>) : int vec<:8> =
  cat[:n = 3] u v.

(* lemma-side named instantiation *)
lemma vec_refl {n} ['a] (u : 'a vec<:n>) : u = u.
proof. trivial. qed.

lemma t1 (u : int vec<:7>) : u = u.
proof. apply (vec_refl[:n = 7]<:'a = int>). qed.

(* partial named instantiation on a lemma: [n] inferred *)
lemma t2 (u : bool vec<:5>) : u = u.
proof. apply (vec_refl<:'a = bool>). qed.

(* ------------------------------------------------------------------ *)
(* error paths                                                        *)

(* duplicate named index *)
expect fail "an index variable appears at least twice: `n'"
op b1 = f[:n = 1, n = 2]<:int, real>.

(* unknown index name on a lemma *)
lemma t3 (u : int vec<:7>) : u = u.
proof.
expect fail "unknown index variable: p"
apply (vec_refl[:p = 7]<:'a = int>).
apply (vec_refl[:n = 7]<:'a = int>).
qed.

(* wrong positional index arity on a lemma *)
lemma t4 (u : int vec<:7>) : u = u.
proof.
expect fail "wrong number of index parameters (2, expecting 1)"
apply (vec_refl[:1, 2]<:'a = int>).
apply (vec_refl[:n = 7]<:'a = int>).
qed.

(* unknown named type variable on a lemma (pre-existing check) *)
lemma t5 (u : int vec<:7>) : u = u.
proof.
expect fail "unknown type variable: 'c"
apply (vec_refl[:n = 7]<:'c = int>).
apply (vec_refl[:n = 7]<:'a = int>).
qed.

(* ------------------------------------------------------------------ *)
(* printing: explicit indices survive in printed bodies (#1065, c2)   *)

expect "* In [operators, predicates or exceptions]:

op g1 : int -> real -> bool = f[:3, 4]<:int, real>." by print g1.

(* index inferable from the arguments: annotation stays suppressed *)
op vhead {n} ['a] : 'a vec<:n+1> -> 'a.
op vuse (u : int vec<:8>) : int = vhead u.

expect "* In [operators, predicates or exceptions]:

op vuse (u : int vec<:8>) : int = vhead u." by print vuse.

(* index not inferable from arguments: printed *)
op vzero {n} ['a] : 'a vec<:n>.
op z5 : int vec<:5> = vzero.

expect "* In [operators, predicates or exceptions]:

op z5 : int vec<:5> = vzero[:5]<:int>." by print z5.

(* ------------------------------------------------------------------ *)
(* diagnostics for bad instantiations (#1065, c3/c4): incompatible    *)
(* explicit instantiations are classified per candidate instead of    *)
(* degenerating to "unknown variable or constant"                     *)

(* omitted indices: uninferrable index univars at declaration close.
   (The message is `cannot infer all index parameters of this operator;
   supply them explicitly (e.g. \`f[:n = 3]')' -- raised through hierror,
   whose printed form embeds the location, so only failure is asserted.) *)
fail op b3 = f<:int, real>.

(* same condition through the tactic path (tyerror prints bare) *)
lemma t6 : true.
proof.
expect fail "cannot infer all index parameters in this expression; supply them explicitly (e.g. `f[:n = 3]')"
have ? : f<:int, int> 0 0.
trivial.
qed.

(* indices under +/* in an argument type are NOT recoverable from the
   argument and must stay printed (review finding: goal display
   collapsed distinct instantiations of compound-index ops) *)
op g {n m} (v : int vec<:n + m>) : int.
op v7 : int vec<:7>.
op p1 : int = g[:3, 4] v7.

expect "* In [operators, predicates or exceptions]:

op p1 : int = Top.g[:3, 4] v7." by print p1.

(* diagnostics: index mismatches report honestly *)
op vv3 : int vec<:3>.

expect fail "incompatible index arguments: `5' vs `3'"
module DM = {
  proc f () : unit = {
    var a : int vec<:5>;
    a <- vv3;
  }
}.

(* subtraction in index position: dedicated parse error with hint
   (`index expressions range over the naturals: subtraction is not
   available') -- asserted manually; parse errors embed locations *)

(* ------------------------------------------------------------------ *)
(* named index instantiation at TYPE applications (`t<:n = 3>`),
   mirroring the op-site `f[:n = 3]` form: any order, partial. *)
type {tn tm} ('a, 'b) tmat.

op tm1 : (int, bool) tmat<:tn = 3, tm = 5>.
op tm2 : (int, bool) tmat<:tm = 5, tn = 3> = tm1.  (* swapped order *)
op tm3 : (int, bool) tmat<:3, 5>            = tm2. (* = positional  *)
op tm4 : (int, bool) tmat<:tn = 3>          = tm3. (* partial: tm inferred *)

expect fail "type `tmat' has no index parameter named `tk'"
op tbad1 : (int, bool) tmat<:tk = 3, tm = 5>.

expect fail "an index variable appears at least twice: `tn'"
op tbad2 : (int, bool) tmat<:tn = 3, tn = 5>.

(* ------------------------------------------------------------------ *)
(* both annotation orders are accepted: `f[:3]<:int>' and
   `f<:int>[:3]', in positional and named form *)
op both {bn} ['a] : int.
op bo1 = both[:3]<:int>.
op bo2 = both<:int>[:3].
op bo3 = both<:int>[:bn = 3].
op bo4 = both[:bn = 3]<:'a = int>.
lemma bo_all : bo1 = bo2 /\ bo2 = bo3 /\ bo3 = bo4.
proof. by rewrite /bo1 /bo2 /bo3 /bo4. qed.

(* mixed positional/named lists are rejected intentionally, on both
   sides, with located messages (asserted manually -- parse errors
   cannot be caught by [fail]):
     g[:3, m = 4]        -> "cannot mix positional and named index arguments"
     h<:int, 'b = bool>  -> "cannot mix positional and named type arguments" *)
