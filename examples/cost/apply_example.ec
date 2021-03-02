require import AllCore Int CHoareTactic StdBigop.
import Bigint.

schema cost_plus `{P} {e e' : int}: 
  cost[P : e + e'] = cost[P : e] + cost[P : e'] + N 1.

schema cost_times `{P} {e e' : int}: 
  cost[P : e * e'] = cost[P : e] + cost[P : e'] + N 1.

hint simplify cost_plus.
hint simplify cost_times.

(*********************)
(* Lemma application *)
(*********************)

module type H = { 
  proc o1 () : unit
  proc o2 () : unit  
}.

module type Adv (H0 : H) (H1 : H) = { proc a () : unit }.

module (MyAdv : Adv) (H0 : H) (H1 : H) = {
  proc a () = {
    var y;
    y <- 1 + 1 + 1 + 1;
    H0.o1();
    H1.o2();
    H0.o2();
  }
}.

lemma MyAdv_compl (k01 k02 k11 k12 : int)
    (H0 <: H [o1 : `{N k01}, o2 : `{N k02}])
    (H1 <: H [o1 : `{N k11}, o2 : `{N k12}]) : 
    choare[MyAdv(H0, H1).a] 
      time [N 3; H0.o1 : 1; H0.o2 : 1; H1.o2 : 1].
proof.
  proc; do !(call(_: true)); auto => /=.
qed.

print MyAdv_compl.

module (MyH : H) = { 
  proc o1 () = {
    var z;
    z <- 1 + 1;
  }

  proc o2 () = {
    var z;
    z <- 1 + 1 + 1;
  }
}.

lemma MyH_compl1 : choare[MyH.o1] time [N 1] by proc; auto.
lemma MyH_compl2 : choare[MyH.o2] time [N 2] by proc; auto.
lemma MyH_compl : choare[MyH.o1] time [N 1] /\ choare[MyH.o2] time [N 2] 
    by split; [apply MyH_compl1 | apply MyH_compl2].

lemma advcompl_inst : choare[MyAdv(MyH, MyH).a] time [N 8].
proof.
  apply (MyAdv_compl _ _ _ _ 
              MyH MyH_compl1 MyH_compl2
              MyH MyH_compl1 MyH_compl2). 
qed.
