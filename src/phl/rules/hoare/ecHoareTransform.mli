(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_transform = {
  htr_tr : EcPlTransform.transform;   (* the transformation, resolved *)
}

(* [t_hoare_transform { htr_tr = t }] — program transformation, with
   [t(c) = (c', [O_1; ...; O_n])] computed by the catalogue entry of [t]
   (see [EcPlTransform]) on [c], in the memory of the goal:

       O_1 ... O_n      hoare [c' : P ==> Q | E]
     --------------------------------------------
               hoare [c : P ==> Q | E]

   where [c'] may live in an extended memory (fresh program variables),
   and the entry is given the goal's hypotheses and the program variables
   read by [Q | E]. Each obligation becomes a premise (first, in order):
   - [OPrefixPost (hd, cond)]:  hoare [hd : P ==> cond | E]
     (the exceptional postconditions [E] of the goal are kept);
   - [OLossless ks]:  phoare [ks : true ==> true] = 1
     (in the memory of [c]);
   - [OExprEq (xs, e, e')]:  forall &m, forall xs, e = e'
     ([&m] the memory of [c'], named after the goal's);
   - [OLocalEquiv (xs, s, s', R, W, M)]:
       forall xs, equiv [s ~ s' : ={R} /\ F{1} ==> ={W}]
     (left: the memory of [c], right: that of [c']), the frame [F] being
     the conjunction of the top-level conjuncts of [P] that only mention
     the memory of [c] and are independent from [M]
     ([EcPlTransform.frame]).
   Side condition: [t] applies to [c] (otherwise fails with its message).

   Node: [RHoareTransform { htr_tr = t }]. Checker: "hoare-transform" (it
   re-runs the entry on the goal's program). *)
val t_hoare_transform : hoare_transform -> backward
