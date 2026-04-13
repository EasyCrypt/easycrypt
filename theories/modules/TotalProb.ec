(*^ This theory proves a module-based law of total probability for
    distributions with finite support, and then specializes it to
    `DBool.dbool`, `drange` and `duniform`. ^*)

require import AllCore List StdOrder StdBigop Distr DBool Finite.
require EventPartitioning.
import RealOrder Bigreal BRA.

(*& General abstract theory &*)

abstract theory TotalGeneral.

(*& theory parameter: additional input &*)

type input.

(*& theory parameter: type of distribution &*)

type t.

(*& A module with a `main` procedure taking in an input plus
    a value of type `t`, and returning a boolean result. &*)

module type T = {
  proc main(i : input, x : t) : bool
}.

(*& For a module `M` with module type `T` and a distribution `dt` for
    `t` plus an input `i`, `Rand(M).f(dt, i)` samples a value `x` from
    `dt`, passes it to `M.main` along with `i`, and returns the
    boolean `M.main` returns. &*)

module Rand(M : T) = {
  proc f(dt : t distr, i : input) : bool = {
    var b : bool; var x : t;
    x <$ dt;
    b <@ M.main(i, x);
    return b;
  }
}.

(* skip to end of section for main lemma *)

section.

declare module M <: T.

local module RandAux = {
  var x : t  (* a global variable *)

  proc f(dt : t distr, i : input) : bool = {
    var b : bool;
    x <$ dt;
    b <@ M.main(i, x);
    return b;
  }
}.

local clone EventPartitioning as EP with
  type input <- t distr * input,
  type output <- bool
proof *.

local clone EP.ListPartitioning as EPL with
  type partition <- t
proof *.

local op x_of_glob_RA (g : (glob RandAux)) : t = g.`2.
local op phi (_ : t distr * input) (g : glob RandAux) (_ : bool) : t =
  x_of_glob_RA g.
local op E (_ : t distr * input) (_ : glob RandAux) (o : bool) : bool = o.

local lemma RandAux_partition_eq (dt' : t distr) (i' : input) (x' : t) &m :
  Pr[RandAux.f(dt', i') @ &m : res /\ x_of_glob_RA (glob RandAux) = x'] =
  mu1 dt' x' * Pr[M.main(i', x') @ &m : res].
proof.
byphoare
  (:
   dt = dt' /\ i = i' /\ (glob M) = (glob M){m} ==>
   res /\ x_of_glob_RA (glob RandAux) = x') => //.
proc; rewrite /x_of_glob_RA /=.
seq 1 :
  (RandAux.x = x')
  (mu1 dt' x')
  Pr[M.main(i', x') @ &m : res]
  (1%r - mu1 dt x')
  0%r
  (i = i' /\ (glob M) = (glob M){m}) => //.
+ by auto.
+ by rnd (pred1 x'); auto.
+ call (: i = i' /\ x = x' /\ glob M = (glob M){m} ==> res).
  + bypr => &hr [#] -> -> glob_eq.
    by byequiv (: ={i, x, glob M} ==> ={res}) => //; sim.
+ by auto.
by hoare; call (: true); auto; smt().
qed.

lemma total_prob' (supp : t list) (dt' : t distr) (i' : input) &m :
  is_finite_for (support dt') supp =>
  Pr[Rand(M).f(dt', i') @ &m : res] =
  big predT
  (fun x' => mu1 dt' x' * Pr[M.main(i', x') @ &m : res])
  supp.
proof.
move => [uniq_supp supp_iff]. 
have ->:
  Pr[Rand(M).f(dt', i') @ &m : res] = Pr[RandAux.f(dt', i') @ &m : res].
  + by byequiv (_ : ={dt, i, glob M} ==> ={res}) => //; proc; sim.
rewrite (EPL.list_partitioning RandAux (dt', i') E phi supp &m) //.
have -> /= :
  Pr[RandAux.f(dt', i') @ &m: res /\ ! (x_of_glob_RA (glob RandAux) \in supp)] =
  0%r.
+ byphoare (: dt = dt' /\ i = i' ==> _) => //; proc.
  seq 1 :
    (RandAux.x \in supp)
    1%r
    0%r
    0%r
    1%r => //.
  + by hoare; call (: true); auto; smt().
  by rnd pred0; auto; smt(mu0).
by congr; apply fun_ext => x'; rewrite RandAux_partition_eq.
qed.

end section.

(*& total probability lemma for distributions with finite support &*)

lemma total_prob (M <: T) (supp : t list) (dt : t distr) (i : input) &m :
  is_finite_for (support dt) supp =>
  Pr[Rand(M).f(dt, i) @ &m : res] =
  big predT
  (fun (x : t) => mu1 dt x * Pr[M.main(i, x) @ &m : res])
  supp.
proof. exact: (total_prob' M). qed.

end TotalGeneral.

(*& Specialization to `DBool.dbool` &*)

abstract theory TotalBool.

clone include TotalGeneral with
  type t <- bool
proof *.

(*& total probability lemma for `DBool.dbool` &*)

lemma total_prob_bool (M <: T) (i : input) &m :
  Pr[Rand(M).f(DBool.dbool, i) @ &m : res] =
  Pr[M.main(i, true) @ &m : res]  / 2%r +
  Pr[M.main(i, false) @ &m : res] / 2%r.
proof.
rewrite (total_prob M [true; false]) //.
+ smt(supp_dbool).
by rewrite 2!big_cons big_nil /= 2!dbool1E.
qed.

end TotalBool.

(*& Specialization to `drange` &*)

abstract theory TotalRange.

clone include TotalGeneral with
  type t <- int
proof *.

(*& total probability lemma for `drange` &*)

lemma total_prob_drange (M <: T) (m n : int) (i : input) &m :
  m < n =>
  Pr[Rand(M).f(drange m n, i) @ &m : res] =
  bigi predT
  (fun (j : int) => Pr[M.main(i, j) @ &m : res] / (n - m)%r)
  m n.
proof.
move => lt_m_n; rewrite (total_prob M (range m n)).
+ by rewrite /is_finite_for; smt(range_uniq mem_range supp_drange).
by apply: eq_big_seq=> |> y; rewrite drange1E mem_range=> ->.
qed.

end TotalRange.

(*& Specialization to `duniform` &*)

abstract theory TotalUniform.

(*& theory parameter: type &*)

type t.

clone include TotalGeneral with
  type t <- t
proof *.

(*& total probability lemma for `duniform` &*)

lemma total_prob_uniform (M <: T) (xs : t list) (i : input) &m :
  uniq xs => xs <> [] =>
  Pr[Rand(M).f(duniform xs, i) @ &m : res] =
  big predT
  (fun (x : t) => Pr[M.main(i, x) @ &m : res] / (size xs)%r)
  xs.
proof.
move => uniq_xs xs_ne_nil; rewrite (total_prob M xs).
+ smt(supp_duniform).
by apply: eq_big_seq=> |> x; rewrite duniform1E_uniq=> // ->.
qed.

end TotalUniform.
