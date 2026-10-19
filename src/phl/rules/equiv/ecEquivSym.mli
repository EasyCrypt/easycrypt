(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_equivS_sym] — exchange of the two sides:

     equiv [c' ~ c : P[&2/&1, &1/&2] ==> Q[&2/&1, &1/&2]]
     ----------------------------------------------------
                 equiv [c ~ c' : P ==> Q]

   The two statements and the types of their memories are exchanged; the
   relations [P] and [Q] are kept, with their two memories swapped (a
   simultaneous substitution [&1 := &2, &2 := &1]). No side condition.

   Node: [REquivSSym]. Checker: "equivS-sym". *)
val t_equivS_sym : backward

(* [t_equivF_sym] — same for procedures:

     equiv [f' ~ f : P[&2/&1, &1/&2] ==> Q[&2/&1, &1/&2]]
     ----------------------------------------------------
                 equiv [f ~ f' : P ==> Q]

   In [Q], [res{1}] and [res{2}] are exchanged along with the memories.

   Node: [REquivFSym]. Checker: "equivF-sym". *)
val t_equivF_sym : backward
