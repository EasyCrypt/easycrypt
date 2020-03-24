require import Int CHoareTactic StdBigop.
import Bigint IntExtra.

module V = { var v : int }.

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
schema cost_plus `{P} {e e' : int}: 
  cost[P : e + e'] = cost[P : e] + cost[P : e'] + 1.

schema cost_plus_true {e e' : int}: 
  cost[true : e + e'] = cost[true : e] + cost[true : e'] + 1.

schema cost_times `{P} {e e' : int}: 
  cost[P : e * e'] = cost[P : e] + cost[P : e'] + 1.

(* It can be instantiated manually with the [instantiate] tactic. *)
(* Syntax, where for every i, Pi can use memory mhm:
   instantiate intro_pat := 
   (sc_name memtype '(P1) ... '(Pn) expr1 ... exprm) *)
lemma foo_cost : cost(_:{})[true : 1 + 2] = 1.
proof.
instantiate H  := (cost_plus_true {} 1 2).
instantiate H0 := (cost_plus      {} `(true) 1 2).
instantiate H2 := (cost_plus      {} `(_:true) 1 2).

(* We can also explicitely give the memory name, as follows: *)
instantiate H3 := (cost_plus      {} `(&mem: V.v = 2) 1 2). 
instantiate H4 := (cost_plus      {} `(&mem: V.v{mem} = 2) 1 2).

instantiate -> := (cost_plus      {} `(_:true) 1 2).
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

schema cost_lt `{P} {e e' : int}: 
  cost[P : e < e'] = cost[P : e] + cost[P : e'] + 1.
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
   - deacreasing quantity qdec
   - number of loop iterations
   - cost of one loop body, when (qdec = k), given using a lambda. *)
while (x <= y /\ y = b) (b - x) (b - a) [fun _ => 1].

(* prove that the loop body preserves the invariant, and cost what was stated. *)
move => z; auto => * /=; by smt ().

(* prove that the if the invariant holds, and if the decreasing quantity is less 
   or equal to zero, then we exit the loop. *)
move => &hr; by smt ().

(* We prove that the invariant implies the post, that the decreasing quantity
   is initially smaller than the number of loop iterations, and that the cost
   of all iterations is smaller than the final cost. *)
skip => * => /=; split; [1: by smt].
rewrite !big_constz !count_predT !size_range; by smt ().
qed.


(*********************)
(* Lemma application *)
(*********************)

module type H = { proc o () : unit }.

module type Adv (H0 : H) = { proc a () : unit }.

module (MyAdv : Adv) (H0 : H) = {
  proc a () = {
    var y;
    y <- 1 + 1 + 1;
    H0.o();
    H0.o();
  }
}.

lemma advcompl
    (H0   <: H) : 
    choare[MyAdv(H0).a : true ==> true] 
      time [2; H0.o : 2].
proof.
  proc; do !(call(_: true; time)); auto => /=.
qed.

module (MyH : H) = { 
  proc o () = {
    var z;
    z <- 1+1;
  }
}.

lemma advcompl_inst :
    choare[MyAdv(MyH).a : true ==> true] 
      time [4].
proof.
  (* Next two tactics should fail, as lemma application to choare judgement is not yet implemented. *)
  (* have h := (advcompl MyH). *)
  (* apply h. *)
  admit.
qed.


module Inv (Adv0 : Adv) (H0 : H) = {
  module Adv1 = Adv0(H0)

  proc i () = {
    var z;
    z <- 1 + 1;
    Adv1.a();
  }
}.


lemma invcompl
    (k : int)
    (Adv0 <: Adv [a : {#H0.o : k}]) 
    (H0   <: H) : 
    0 <= k =>
    choare[Inv(Adv0, H0).i : true ==> true] 
      time [1; Adv0.a : 1; H0.o : k ].
proof.    
  move => hk; proc. 
  call(_: true; time (H0.o : [fun _ => 0; H0.o : fun _ => 1])).
  move => * /=; proc*; call(_: true; time); auto => /=.
  auto => /=.
  rewrite !big_constz !count_predT !size_range. by smt ().
qed.

lemma incompl_inst
    (H0   <: H) : 
    choare[Inv(MyAdv, H0).i : true ==> true] 
      time [1; H0.o : 2 ].
proof.
  (* have h := (invcompl 2 MyAdv H0). *)
  admit.
qed.

lemma invcompl2
    (H0   <: H)
    (Adv1 <: Adv [a : {#H0.o : 2}]) :
    choare[Inv(Adv1, H0).i : true ==> true]
      time [1; H0.o : 2 ].
proof.
  have h := (invcompl 2 Adv1 H0).
  admit.
qed.

(**************************************************)

module type AB (H0 : H) = {
  proc a () : unit { H0.o : 1 }
}.

print AB.
section.
 declare module H0 : H.
 declare module AB0 : AB.

 print AB0.
 local module AB1 = AB0(H0).
 print AB1.

 local module E = { 
   proc e () = {
     AB1.a();
   }
 }.
   
 print E.


(**************************************************)
 module type MAB (H1 : H) (H2 : H)  = {
   proc a () : unit {H2.o}
 }.

 print MAB.

 local module (MAB0 : MAB) (H1 : H) (H2 : H) = {
   proc a () = {
     H2.o();
     H0.o();
   }
 }.

 local module MAB1 = MAB0(H0).
 print MAB1.

 local module MAB2 = MAB0(H0, H0).
 print MAB2.                    

end section.

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
instantiate -> := (plus_cost_e {} 1 2).
instantiate -> := (plus_cost_f {} 1 2) => //.
qed.

(* Remark: we cannot use hints there, because plus_cost_e is not terminating. *)

