(* -------------------------------------------------------------------- *)
open EcPath
open EcParsetree
open EcAst
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type fel_rule = {
  felr_at    : codegap1;                 (* end k of the initialization *)
  felr_cntr  : ss_inv;                   (* counter cntr *)
  felr_asg   : form;                     (* bound of a step, h : int -> real *)
  felr_q     : form;                     (* maximal counter value q *)
  felr_event : ss_inv;                   (* failure event F *)
  felr_specs : (xpath * ss_inv) list;    (* oracle preconditions P_o *)
  felr_inv   : ss_inv;                   (* invariant I *)
}

(* [t_bdhoare_fel { felr_at = k; felr_cntr = cntr; felr_asg = h;
                    felr_q = q; felr_event = F; felr_specs = Ps;
                    felr_inv = I }]
   — the failure-event lemma: the probability that a run of [f] ends in
   the failure event [F] is bounded by the sum of the probabilities that
   each oracle call, the counter [cntr] being [c], triggers [F]. With
   [f] the (defined) procedure of the goal, its body [c = c1; c2],
   [c1 = c[0..k)], [args] the arguments of [f] and [G] the global
   variables [f] reads:

     (B) big predT h (range 0 q) <= bd
     (E) forall &m, ev => I => F /\ cntr <= q
     (H) hoare [c1 : (params = args /\ (x = x{m0})_{x in G}) ==>
                     !F /\ cntr = 0 /\ I]
     for each oracle o in O, P_o its precondition in Ps (true if none):
       (O1) phoare [o : (0 <= cntr < q /\ !F) /\ I /\ P_o ==> F] <= h cntr
       (O2) forall c, hoare [o : P_o /\ c = cntr /\ I ==> c < cntr /\ I]
       (O3) forall b c, hoare [o : !P_o /\ F = b /\ cntr = c /\ I
                                   ==> (F = b /\ c <= cntr) /\ I]
     ----------------------------------------------------------------
                    Pr[f(args) @ &m0 : ev] <= bd

   where [ev], [F], [cntr] and [I] are read in the final memory of [f] in
   (E), and the counter, event and invariant are in the memory of [f] in
   (H) and of the oracle in (O1-3). [O] is computed from the program: the
   procedures called by [c2] (transitively, through the procedures that do
   not write the variables of [cntr], [F] and [I] themselves) that write
   them. Side condition: [c2], outside of the calls to the oracles of [O],
   does not write the variables of [cntr], [F] and [I] (otherwise fails).
   Premises, in order: (B), (E), (H), then (O1), (O2), (O3) for each
   oracle of [O], in the order of their paths. Trivial conjuncts [true]
   are simplified away.

   The rule is stated on the whole body of [f] (an implicit seq at [k]):
   its conclusion is a probability, for which there is no seq rule, and
   restating it through a judgement on [c2] would change its premises.

   Node: [RBdHoareFel { feln_at = k (resolved index); feln_cntr;
                        feln_asg; feln_q; feln_event; feln_specs;
                        feln_inv }] (the oracles are recomputed).
   Checker: "bdhoare-fel". *)
val t_bdhoare_fel : fel_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [fel k cntr h q F [o1 : P_1; ...] : I] on a [Pr[f(args) @ &m : ev] <=
   bd] goal, the [FelTactic] theory being loaded: [cntr], [F], [I]
   (default [true]) are typed in a fresh memory, [P_i] in the memory of
   [o_i], [h] and [q] in [&m]. Applies [t_bdhoare_fel]. *)
val process_bdhoare_fel : pcodegap1 -> fel_info -> backward

