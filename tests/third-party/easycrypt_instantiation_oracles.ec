(* An instantiation example involving adversaries using oracles.
   To make this work, we introduce a very limited form of
   functions as parameters -- used when declaring adversaries. *)
(* Adapted from an example by Alley Stoughton *)

require import Int.
require import Distr. import Dinter.
require import Prime_field.
require import Cyclic_group_prime.
require import Set.
require        RandOrcl.

cnst gDistr: group distr.

(* I think this type is the one that gets instantiated in the main experiment *)
type t.

(* TODO: Once type-checking is fixed for this, fold the two clones into one *)
clone RandOrcl as RO with
  type from = t,
  type to = group,
  cnst default = g.
import RO. (* Maybe we should let users "clone import X as Y"? *)

(* An adversary with a function using two oracles *)
module type Adversary(O1:Oracle, O2:Oracle) = {
  fun main():bool
}.

(* Experiment *)
require import Map.

module Experiment(O1:Oracle, O2:Oracle, A:Adversary) = {
  module A = A(O1,O2)

  fun main(): bool = {
    var b:bool;
    (* Setup Phase *)
    O1.init(); O2.init();
    (* Adversary Call *)
    b := A.main();
    return b;
  }
}.

(* The oracles *)
(* We clone two random oracles of the same type for H and R *)
clone RO.ROM as RO1.
module H = RO1.RO.

clone RO.ROM as RO2.
module R = RO2.RO.

(* F is built on top of H *)
module F = {
  var k:gf_q

  fun init(): unit = {
    var k':int;
    k' = $dinter 0 (q - 1);
    k = i_to_gf_q k';
  }

  fun f(x:t): group = {
    var y:group;
    y := H.o(x);
    y = y ^ k;
    return y;
  }
}.

(* The claims *)
require import Real.

cnst epsilon: real.

axiom Adv_def: forall &m (A <: Adversary),
  `| Pr[ Experiment(H,F,A).main() @ &m: res ] -
     Pr[ Experiment(H,R,A).main() @ &m: res ] | <= epsilon.

(*
adversary type B = {
  B1 : () -> t list { t -> group }
  B2 : group list -> bool {t -> group}
}.

adversary A(B : B): A = {
  (* See the following comment for how to interpret {O : t -> group} *)

  fun Process{O : t -> group}(xs : t list) : group list = {
    var ys : group list;
    var y : group;
    var x : t;
    ys = [];
    while (xs <> []) {
      x = hd(xs);
      xs = tl(xs);
      y = O(x);
      ys = ys ++ [y];
    }
    return ys;
  }

  (* Because the function A of adversary type A uses two oracles, the
     syntax for declaring A must include these oracles as parameters.
     We're using { ... } for these parameters, mirroring the notation
     used when declaring an adversary's type, as well as when calling
     an adversary *)

  fun A{H : t -> group, O : t -> group}() : bool = {
    var xs : t list;
    var gs : group list;
    var b : bool;
    xs = B.B1{H}();
    gs = Process{O}(xs);
    b = B.B2{H}(gs);
    return b;
  }
}.

game G0_A = G0(A).
game G1_A = G1(A).

(* As an instance of the above axiom, we have: *)

claim G0_G1_A : | G0_A.Main[res] - G0_A.Main[res] | <= epsilon.

(* If we do the first instantiation by hand, we get:

game G0_A(B : B) = {
  var hState : (t, group)map

  fun InitH() : unit = {
    hState = empty_map;
  }

  fun H(x : t) : group = {
    var y : group;
    if (!in_dom(x, hState)) {
      y = rand();
      hState[x] = y;
    }
    return hState[x];
  }

  var k : int

  fun F(x : t) : group = {
    var y : group;
    y = H(x);
    y = y ^ k;
    return y;
  }

  fun Process{O : t -> group}(xs : t list) : group list = {
    var ys : group list;
    var y : group;
    var x : t;
    ys = [];
    while (xs <> []) {
      x = hd(xs);
      xs = tl(xs);
      y = O(x);
      ys = ys ++ [y];
    }
    return ys;
  }

  fun A{H : t -> group, O : t -> group}() : bool = {
    var xs : t list;
    var gs : group list;
    var b : bool;
    xs = B.B1{H}();
    gs = Process{O}(xs);
    b = B.B2{H}(gs);
    return b;
  }

  fun Main() : bool = {
    var b : bool;
    k = [0 .. ord - 1];  (* F depends on k *)
    InitH();
    b = A{H, F}();
    return b;
  }
}.

And, doing the second instantiation by hand, we get:

game G1_A(B : B) = {
  var hState : (t, group)map

  fun InitH() : unit = {
    hState = empty_map;
  }

  fun H(x : t) : group = {
    var y : group;
    if (!in_dom(x, hState)) {
      y = rand();
      hState[x] = y;
    }
    return hState[x];
  }

  var rState : (t, group)map

  fun InitR() : unit = {
    rState = empty_map;
  }

  fun R(x : t) : group = {
    var y : group;
    if (!in_dom(x, rState)) {
      y = rand();
      rState[x] = y;
    }
    return rState[x];
  }

  fun Process{O : t -> group}(xs : t list) : group list = {
    var ys : group list;
    var y : group;
    var x : t;
    ys = [];
    while (xs <> []) {
      x = hd(xs);
      xs = tl(xs);
      y = O(x);
      ys = ys ++ [y];
    }
    return ys;
  }

  fun A{H : t -> group, O : t -> group}() : bool = {
    var xs : t list;
    var gs : group list;
    var b : bool;
    xs = B.B1{H}();
    gs = Process{O}(xs);
    b = B.B2{H}(gs);
    return b;
  }

  fun Main() : bool = {
    var b : bool;
    InitH(); InitR();
    b = A{H, R}();
    return b;
  }
}.

*)
*)
