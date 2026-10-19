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
   and the entry is given the goal's hypotheses and the program variables
   read by [Q]. Each obligation becomes a premise (first, in order):
   - [OPrefixPost (hd, cond)]:  hoare [hd : P_bool ==> cond]
     where [P] is [P_bool `|` f] (otherwise fails with "the pre should
     have the form \"_ `|` _\"");
   - [OLossless ks]:  phoare [ks : true ==> true] = 1
     (in the memory of [c]);
   - [OExprEq (xs, e, e')]:  forall &m, forall xs, e = e'
     ([&m] the memory of [c'], named after the goal's);
   - [OLocalEquiv (xs, s, s', R, W, M)]:
       forall xs, equiv [s ~ s' : ={R} /\ F{1} ==> ={W}]
     (left: the memory of [c], right: that of [c']), the frame [F] being
     the conjunction of the top-level conjuncts of [P_bool] that only
     mention the memory of [c] and are independent from [M]
     ([EcPlTransform.frame]) when [P] is [P_bool `|` f], and no frame
     otherwise.
   Side condition: [t] applies to [c] (otherwise fails with its message).

   Node: [REHoareTransform { ehtr_tr = t }]. Checker: "ehoare-transform"
   (it re-runs the entry on the goal's program). *)
val t_ehoare_transform : ehoare_transform -> backward
