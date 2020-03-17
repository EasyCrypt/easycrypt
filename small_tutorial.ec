require import Int CHoareTactic StdBigop.
import Bigint IntExtra.

(*********************)
(* Expression's cost *)
(*********************)

(* Integer constants are free. *)
lemma free_int : cost(_:{})[true : 1] = 0 by auto.

(* Variable lookups are free. *)
lemma free_var : cost(_:{x : int})[true : x] = 0 by auto.

(* Same for global variables. *)
module A = { var x : int }.
lemma free_var_g : cost(_:{})[true : A.x] = 0 by auto.

(* And logical variables. *)
lemma free_var_logical (a : int) : cost(_:{})[true : a] = 0 by auto.

(* Everything else has a cost, that must be given by the user through 
   schemata. A schema allow to quantify over *expressions*, as in: *)
schema cost_plus {e e' : int}: 
  cost[true : e + e'] = cost[true : e] + cost[true : e'] + 1.

schema cost_times {e e' : int}: 
  cost[true : e * e'] = cost[true : e] + cost[true : e'] + 1.

(* It can be instantiated manually with the [instantiate] tactic. *)
(* Syntax: 
   instantiate intro_pat := (schema_name memorytype expr1 : expr2 : ...) *)
lemma foo_cost : cost(_:{})[true : 1 + 2] = 1.
proof.
instantiate -> := (cost_plus {} 1 : 2).
auto.
qed.

(* Instantiating manually can be avoided using simplification hints.  *)
hint simplify cost_plus.
hint simplify cost_times.

lemma foo_cost2 : cost(_:{})[true : 1 + 2] = 1 by auto.

(* Schemata can have type variables, e.g. for lists. *)
require import List.
schema cost_cons ['a] {e : 'a} {l : 'a list} : 
    cost[true : e :: l] =   
    cost[true : e] + cost[true : l] + 1.

schema cost_nil ['a] : cost[true : [<:'a>]] = 1.

hint simplify cost_cons.
hint simplify cost_nil.
lemma foo_list : cost(_:{})[true: [1;2;3;4]] = 5 by auto.


(****************************)
(* Modules and restrictions *)
(****************************)


module B = { 
  proc g (x, y) : int = {
    var r : int;
    r <- x + y;
    r <- r * x;
    return r * r;
  }

  proc f (x : int) : int = {
    var a : int;
    a <- x + 1;
    a <@ g(a,x);
  return a;
  }
}.

(* Assignements are free, only the variable evaluation has a cost. *)
lemma foo : choare[B.g : true ==> true] time [3].
proof.
  proc; auto => * /=.
qed.

(* Procedure calls are also free. *)
lemma foo3 : choare[B.f : true ==> true] time [4].
proof.
  proc; call foo; auto.
qed.

module C = { 
  proc f (x, y) : int = {
    var r : int;
    if (y < x) {
      r <- 1 + 1;
      r <- 1 + 1;
     } else {
      r <- 2 + 1;
      r <- 2 + 1;
    }
    return r;
  }
}.

schema cost_lt {e e' : int}: 
  cost[true : e < e'] = cost[true : e] + cost[true : e'] + 1.
hint simplify cost_lt.

(* For if statements, to keep cost expressions simpler, we do not use
    a max. Instead, we add the cost of both branches. *)
lemma foo4 : choare[C.f : true ==> true] time [5].
proof.
proc; auto.
qed.

module D = { 
  var g : int

  proc f (x, y) : int = {
    while (x < y) {
      x <- x + 1;
    }
    return x;
  }
}.

lemma foo5 : forall (a : int) (b : int), 
0 <= a <= b =>
choare[D.f : x = a /\ y = b /\ x < y ==> true] time [2 * (b - a) + 1].
proof.
move => *.
proc => /=.
(* The [while] tactic takes the following parameters:
   - invariant, 
   - increasing quantity starting from zero
   - number of loop iterations
   - cost of one loop body, given using a lambda. *)
while (x <= y /\ y = b) (x - a) (b - a) [fun _ => 1] => *.

(* prove that the loop body preserves the invariant, and cost what was stated. *)
auto => * /=; by smt ().

(* prove that the invariant and loop condition implies that we have not reached 
  the maximal number of steps.  *)
by smt ().

(* We prove that the invariant implies the post, and that the cost of all
  iterations is smaller than the final cost. *)
skip => * => /=; split; [1: by smt].
rewrite !big_constz !count_predT !size_range; by smt ().
qed.



(**************************************************)
(* Bonus: expression's cost using a free operator *)
(**************************************************)

op free ['a] (x : 'a) : 'a.

axiom free_id ['a] (x : 'a) : free(x) = x.

schema free_id ['a] {e : 'a} : cost[true : free(e)] = 0.

schema plus_cost_f {e e' : int}: cost[true : free(e) + free(e')] = 1.

(* The schema below is valid for any operator with a call-by-value semantics. *)
schema plus_cost_e {e e' : int}: 
  cost[true : e + e'] = 
  cost[true : free(e) + free(e')] +
  cost[true : e] + cost[true : e'].

schema free_beta ['a, 'b] {f : 'a -> 'b} {k : 'a} :
  cost[true : (fun x => f x) k] = 
  cost[true : f (free k)] + cost[true : k] + 1.

lemma foo_p_f : cost(_:{})[true : 1 + 2] = 1.
proof.
instantiate -> := (plus_cost_e {} 1 : 2).
instantiate -> := (plus_cost_f {} 1 : 2) => //.
qed.

(* Remark: we cannot use hints there, because plus_cost_e is not terminating. *)

