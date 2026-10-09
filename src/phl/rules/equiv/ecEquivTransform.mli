(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_transform = {
  etr_side : side;                     (* transformed side *)
  etr_tr   : EcPlTransform.transform;  (* the transformation, resolved *)
}

(* [t_equiv_transform { etr_side = `Left; etr_tr = t }] — program
   transformation of one side, with [t(c) = (c', [O_1; ...; O_n])]
   computed by the catalogue entry of [t] (see [EcPlTransform]) on [c], in
   the memory [&1] of that side:

       O_1 ... O_n      equiv [c' ~ d : P ==> Q]
     --------------------------------------------
                equiv [c ~ d : P ==> Q]

   (symmetrically for [`Right]; the other program and memory are
   unchanged), where [c'] may live in an extended memory (fresh program
   variables), and the entry is given the goal's hypotheses and the
   program variables of [&1] read by [Q]. Each obligation becomes a
   premise (first, in order):
   - [OPrefixPost (hd, cond)]:
       forall &2, hoare [hd : P ==> cond]
     ([P] read as an assertion on [&1], the other memory [&2] being
     universally quantified);
   - [OLossless ks]:  phoare [ks : true ==> true] = 1
     (in the memory [&1] of [c], the other memory not involved);
   - [OExprEq (xs, e, e')]:  forall &1, forall xs, e = e'
     ([&1] over the memory type of [c'], the other memory not involved);
   - [OLocalEquiv (xs, s, s', R, W, M)]:
       forall xs, equiv [s ~ s' : ={R} /\ F{1} ==> ={W}]
     (left: the memory of [c], right: that of [c']), the frame [F] being
     the conjunction of the top-level conjuncts of [P] that only mention
     [&1] (not [&2]) and are independent from [M]
     ([EcPlTransform.frame]).
   Side condition: [t] applies to [c] (otherwise fails with its message).

   Node: [REquivTransform { etr_side; etr_tr = t }]. Checker:
   "equiv-transform" (it re-runs the entry on the goal's program). *)
val t_equiv_transform : equiv_transform -> backward
