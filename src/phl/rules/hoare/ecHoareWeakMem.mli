(* -------------------------------------------------------------------- *)
open EcAst
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_weakmem = {
  hwm_vars : ovariable list;   (* the variables, typed *)
}

(* [t_hoare_weakmem { hwm_vars = xs }] — weakening of the memory:

        hoare [c : P ==> Q | E]  (memory m)
     ------------------------------------------  m' = m + xs
        hoare [c : P ==> Q | E]  (memory m')

   where [m + xs] is [m] in which the local program variables [xs] are
   declared ([EcMemory.bindall]). Side conditions (re-checked by
   [EcPlWeakMem.restrict], otherwise fails): [xs] are the last variables
   declared in the memory [m'] of the goal, each fresh in [m], and none
   of them is read or written by [c] nor occurs in [P], [Q] or [E] (the
   premise is well-formed in [m]).

   Node: [RHoareWeakMem { hwm_vars = xs }]. Checker: "hoare-weakmem". *)
val t_hoare_weakmem : hoare_weakmem -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoare_weakmem_hyp h { hwm_vars = xs }] — on any goal [G], [h] being
   the hypothesis [hoare [c : P ==> Q | E]] (memory [m]), with
   [H' := hoare [c : P ==> Q | E]] (memory [m + xs]):
   1. [EcLowGoal.t_cut] [H'], giving
        (a) H',
        (b) H' => G                           — left open;
   2. [t_hoare_weakmem] reduces (a) to [h], closed by [h].
   Visible goal: (b). Raises [EcMemory.DuplicatedMemoryBinding] (before
   acting) when a variable of [xs] is already declared in [m]. Emits no
   node of its own. *)
val t_hoare_weakmem_hyp : EcIdent.t -> hoare_weakmem -> backward
