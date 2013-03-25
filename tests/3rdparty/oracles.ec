(* An instantiation example involving adversaries using oracles.
   To make this work, we introduce a very limited form of
   functions as parameters -- used when declaring adversaries. *)

require import Cyclic_group_prime.

type t.

type group.

cnst ord : int.  (* order of group *)

op [^] : (group, int) -> group as group_pow.

pop rand : () -> group.

(* an adversary with a function using two oracles *)

adversary type A = {
  A : () -> bool { t -> group; t -> group }
}.

game G0(A : A) = {
  (* H is a random oracle from t to group *)

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

  (* F is an oracle from t to group: F(x) = H(x) ^ k,
     where k is a global variable set in the Main function *)

  var k : int

  fun F(x : t) : group = {
    var y : group;
    y = H(x);
    y = y ^ k;
    return y;
  }

  fun Main() : bool = {
    var b : bool;
    k = [0 .. ord - 1];  (* F depends on k *)
    InitH();
    (* when we call A.A, we pass it the oracles it uses, along
       with its usual arguments (none in this case); the { ... } notation
       mirrors that of the declarations of adversary types *)
    b = A.A{H, F}();
    return b;
  }
}.

game G1(A : A) = {
  (* H is as in G0 *)

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

  (* R is another random oracle -- just like H *)

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

  fun Main() : bool = {
    var b : bool;
    InitH(); InitR();
    b = A.A{H, R}();
    return b;
  }
}.

cnst epsilon : real.

(* This seems simpler than using the "theory" notation: *)

axiom claim G0G1 :
  forall (A : A), 
  | G0(A).Main[res] - G1(A).Main[res] | <= epsilon.

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
