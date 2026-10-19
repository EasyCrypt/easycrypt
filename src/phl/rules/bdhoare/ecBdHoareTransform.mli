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
   and the entry is given the program variables read by [Q]. Each
   obligation becomes a premise (first, in order):
   - [OPrefixPost (hd, cond)]:  hoare [hd : P ==> cond];
   - [OLossless ks]:  phoare [ks : true ==> true] = 1
     (in the memory of [c]).
   Side condition: [t] applies to [c] (otherwise fails with its message).

   Node: [RBdHoareTransform { btr_tr = t }]. Checker: "bdhoare-transform"
   (it re-runs the entry on the goal's program). *)
val t_bdhoare_transform : bdhoare_transform -> backward
