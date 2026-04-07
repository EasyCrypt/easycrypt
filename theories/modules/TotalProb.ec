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
  (_ :
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
auto.
rnd (pred1 x'); auto.
call (_ : i = i' /\ x = x' /\ glob M = (glob M){m} ==> res).
bypr => &hr [#] -> -> glob_eq.
byequiv (_ : ={i, x, glob M} ==> ={res}) => //; sim.
auto.
hoare; call (_ : true); auto; smt().
qed.

lemma total_prob' (dt' : t distr) (supp : t list) (i' : input) &m :
  is_lossless dt' => is_finite_for (support dt') supp =>
  Pr[Rand(M).f(dt', i') @ &m : res] =
  big predT
  (fun x' => mu1 dt' x' * Pr[M.main(i', x') @ &m : res])
  supp.
proof.
move => dt'_ll [uniq_supp supp_iff]. 
have -> :
  Pr[Rand(M).f(dt', i') @ &m : res] = Pr[RandAux.f(dt', i') @ &m : res].
  byequiv (_ : ={dt, i, glob M} ==> ={res}) => //; proc; sim.
rewrite (EPL.list_partitioning RandAux (dt', i') E phi supp &m) //.
have -> /= :
  Pr[RandAux.f(dt', i') @ &m: res /\ ! (x_of_glob_RA (glob RandAux) \in supp)] =
  0%r.
  byphoare (_ : dt = dt' /\ i = i' ==> _) => //; proc.
  seq 1 :
    (RandAux.x \in supp)
    1%r
    0%r
    0%r
    1%r => //.
  auto.
  hoare; call (_ : true); auto; smt().
  rnd pred0; auto; smt(mu0).
congr; apply fun_ext => x'; by rewrite RandAux_partition_eq.
qed.

end section.

(*& total probability lemma for distributions with finite support &*)

lemma total_prob (M <: T) (dt : t distr) (supp : t list) (i : input) &m :
  is_lossless dt => is_finite_for (support dt) supp =>
  Pr[Rand(M).f(dt, i) @ &m : res] =
  big predT
  (fun (x : t) => mu1 dt x * Pr[M.main(i, x) @ &m : res])
  supp.
proof.
move => dt_ll iff_supp_dt_supp.
by apply (total_prob' M).
qed.

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
rewrite (total_prob M DBool.dbool [true; false]) //.
rewrite dbool_ll.
smt(supp_dbool).
by rewrite 2!big_cons big_nil /= /predT /predF /= 2!dbool1E.
qed.

end TotalBool.

(*& Specialization to `drange` &*)

abstract theory TotalRange.

clone include TotalGeneral with
  type t <- int
proof *.

lemma big_weight_simp (M <: T) (m n : int, i : input, ys : int list) &m :
  (forall y, y \in ys => m <= y < n) =>
  big predT
  (fun (x : int) => mu1 (drange m n) x * Pr[M.main(i, x) @ &m : res])
  ys =
  big predT
  (fun (x : int) => Pr[M.main(i, x) @ &m : res] / (n - m)%r)
  ys.
proof.
elim ys => [// | y ys IH mem_impl].
rewrite 2!big_cons (_ : predT y) //=.
rewrite drange1E (_ : m <= y < n) 1:mem_impl //=.
rewrite IH => [z z_in_ys | //].
by rewrite mem_impl /= z_in_ys.
qed.

(*& total probability lemma for `drange` &*)

lemma total_prob_drange (M <: T) (m n : int, i : input) &m :
  m < n =>
  Pr[Rand(M).f(drange m n, i) @ &m : res] =
  bigi predT
  (fun (j : int) => Pr[M.main(i, j) @ &m : res] / (n - m)%r)
  m n.
proof.
move => lt_m_n.
rewrite (total_prob M (drange m n) (range m n)).
by rewrite drange_ll.
rewrite /is_finite_for.
smt(range_uniq mem_range supp_drange).
rewrite (big_weight_simp M) //; by move => j /mem_range.
qed.

end TotalRange.

(*& Specialization to `duniform` &*)

abstract theory TotalUniform.

(*& theory parameter: type &*)

type t.

clone include TotalGeneral with
  type t <- t
proof *.

lemma big_weight_simp (M <: T) (xs : t list, i : input, ys : t list) &m :
  uniq xs =>
  (forall y, y \in ys => y \in xs) =>
  big predT
  (fun (x : t) => mu1 (duniform xs) x * Pr[M.main(i, x) @ &m : res])
  ys =
  big predT
  (fun (x : t) => Pr[M.main(i, x) @ &m : res] / (size xs)%r)
  ys.
proof.
move => uniq_xs.
elim ys => [// | y ys IH mem_impl].
rewrite 2!big_cons (_ : predT true) //=.
rewrite duniform1E_uniq // (_ : y \in xs) 1:mem_impl //=.
rewrite IH => [z z_in_ys | //]; by rewrite mem_impl /= z_in_ys.
qed.

(*& total probability lemma for `duniform` &*)

lemma total_prob_uniform (M <: T) (xs : t list, i : input) &m :
  uniq xs => xs <> [] =>
  Pr[Rand(M).f(duniform xs, i) @ &m : res] =
  big predT
  (fun (x : t) => Pr[M.main(i, x) @ &m : res] / (size xs)%r)
  xs.
proof.
move => uniq_xs xs_ne_nil.
rewrite (total_prob M (duniform xs) xs).
by rewrite duniform_ll.
smt(supp_duniform).
by rewrite (big_weight_simp M).
qed.

end TotalUniform.
