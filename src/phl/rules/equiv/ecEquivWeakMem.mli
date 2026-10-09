(* -------------------------------------------------------------------- *)
open EcParsetree
open EcAst
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_weakmem = {
  ewm_side : side;              (* weakened side *)
  ewm_vars : ovariable list;    (* the variables, typed *)
}

(* [t_equiv_weakmem { ewm_side = `Left; ewm_vars = xs }] — weakening of
   the memory of one side:

        equiv [c ~ d : P ==> Q]  (memories m1, m2)
     -----------------------------------------------  m1' = m1 + xs
        equiv [c ~ d : P ==> Q]  (memories m1', m2)

   (symmetrically for [`Right]; the other memory is unchanged), where
   [m1 + xs] is [m1] in which the local program variables [xs] are
   declared ([EcMemory.bindall]). Side conditions (re-checked by
   [EcPlWeakMem.restrict], otherwise fails): [xs] are the last variables
   declared in the memory [m1'] of the goal, each fresh in [m1], and none
   of them is read or written by [c] nor occurs, on [&1], in [P] or [Q]
   (the premise is well-formed in [m1]).

   Node: [REquivWeakMem { ewm_side; ewm_vars = xs }]. Checker:
   "equiv-weakmem". *)
val t_equiv_weakmem : equiv_weakmem -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equiv_weakmem_hyp h side xs] — on any goal [G], [h] being the
   hypothesis [equiv [c ~ d : P ==> Q]] (memories [m1], [m2]), with [H']
   the same judgement with [xs] declared in the memory of [side] (in both
   memories when [side] is [None]):
   1. [EcLowGoal.t_cut] [H'], giving
        (a) H',
        (b) H' => G                           — left open;
   2. [t_equiv_weakmem] on each weakened side reduces (a) to [h], closed
      by [h].
   Visible goal: (b). Raises [EcMemory.DuplicatedMemoryBinding] (before
   acting) when a variable of [xs] is already declared in a weakened
   memory (the right one checked first). Emits no node of its own. *)
val t_equiv_weakmem_hyp :
  EcIdent.t -> oside -> ovariable list -> backward
