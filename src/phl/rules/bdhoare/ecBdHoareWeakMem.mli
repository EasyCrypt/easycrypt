(* -------------------------------------------------------------------- *)
open EcAst
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_weakmem = {
  bwm_vars : ovariable list;   (* the variables, typed *)
}

(* [t_bdhoare_weakmem { bwm_vars = xs }] — weakening of the memory:

        phoare [c : P ==> Q] <> b  (memory m)
     ------------------------------------------  m' = m + xs
        phoare [c : P ==> Q] <> b  (memory m')

   ([<>] any of [<=], [=], [>=]), where [m + xs] is [m] in which the
   local program variables [xs] are declared ([EcMemory.bindall]). Side
   conditions (re-checked by [EcPlWeakMem.restrict], otherwise fails):
   [xs] are the last variables declared in the memory [m'] of the goal,
   each fresh in [m], and none of them is read or written by [c] nor
   occurs in [P], [Q] or [b] (the premise is well-formed in [m]).

   Node: [RBdHoareWeakMem { bwm_vars = xs }]. Checker: "bdhoare-weakmem". *)
val t_bdhoare_weakmem : bdhoare_weakmem -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_weakmem_hyp h { bwm_vars = xs }] — on any goal [G], [h] being
   the hypothesis [phoare [c : P ==> Q] <> b] (memory [m]), with
   [H' := phoare [c : P ==> Q] <> b] (memory [m + xs]):
   1. [EcLowGoal.t_cut] [H'], giving
        (a) H',
        (b) H' => G                           — left open;
   2. [t_bdhoare_weakmem] reduces (a) to [h], closed by [h].
   Visible goal: (b). Raises [EcMemory.DuplicatedMemoryBinding] (before
   acting) when a variable of [xs] is already declared in [m]. Emits no
   node of its own. *)
val t_bdhoare_weakmem_hyp : EcIdent.t -> bdhoare_weakmem -> backward
