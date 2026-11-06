(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type ehoare_transform = {
  ehtr_tr : EcPlTransform.transform;   (* the transformation, resolved *)
}

(* [t_ehoare_transform { ehtr_tr = t }] — program transformation, with
   [t(c) = (c', [O_1; ...; O_n])] computed by the catalogue entry of [t]
   (see [EcPlTransform]) on [c], in the memory of the goal:

       O_1 ... O_n      ehoare [c' : P ==> Q]
     -----------------------------------------
                ehoare [c : P ==> Q]

   where [c'] may live in an extended memory (fresh program variables),
   and the entry is given the program variables read by [Q]. Each
   obligation becomes a premise (first, in order):
   - [OPrefixPost (hd, cond)]:  hoare [hd : P_bool ==> cond]
     where [P] is [P_bool `|` f] (otherwise fails with "the pre should
     have the form \"_ `|` _\"").
   Side condition: [t] applies to [c] (otherwise fails with its message).

   No catalogue entry is used on ehoare goals yet (there is no ehoare
   [rndsem]).

   Node: [REHoareTransform { ehtr_tr = t }]. Checker: "ehoare-transform"
   (it re-runs the entry on the goal's program). *)
val t_ehoare_transform : ehoare_transform -> backward
