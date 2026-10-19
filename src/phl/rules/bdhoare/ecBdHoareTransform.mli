(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_transform = {
  btr_tr : EcPlTransform.transform;   (* the transformation, resolved *)
}

(* [t_bdhoare_transform { btr_tr = t }] — program transformation, with
   [t(c) = (c', [O_1; ...; O_n])] computed by the catalogue entry of [t]
   (see [EcPlTransform]) on [c], in the memory of the goal, and [~] the
   goal's comparison:

       O_1 ... O_n      phoare [c' : P ==> Q] ~ d
     ---------------------------------------------
                phoare [c : P ==> Q] ~ d

   where [c'] may live in an extended memory (fresh program variables),
   and the entry is given the goal's hypotheses and the program variables
   read by [Q]. Each obligation becomes a premise (first, in order):
   - [OPrefixPost (hd, cond)]:  hoare [hd : P ==> cond];
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
   The variables read by the bound [d] are not given to the entry: [d] is
   evaluated in the initial memory.
   Side condition: [t] applies to [c] (otherwise fails with its message).

   Node: [RBdHoareTransform { btr_tr = t }]. Checker: "bdhoare-transform"
   (it re-runs the entry on the goal's program). *)
val t_bdhoare_transform : bdhoare_transform -> backward
