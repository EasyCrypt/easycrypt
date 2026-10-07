(* -------------------------------------------------------------------- *)
open EcEnv
open EcTypes
open EcModules
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_fission = {
  trfi_at   : nm_codepos;   (* position of the loop (resolved, maybe nested) *)
  trfi_init : int;          (* length n of the prelude *)
  trfi_d1   : int;          (* first break offset d1 in the body *)
  trfi_d2   : int;          (* second break offset d2 in the body *)
}

(* [TrFission { trfi_at = p; trfi_init = n; trfi_d1 = d1; trfi_d2 = d2 }]
   — splits a loop into two loops, at the (possibly nested) position [p],
   the loop being preceded by a prelude [init] of [n] instructions (in the
   same block), its body being cut at the offsets [d1 <= d2]:

     c = ...; init; while b do { c1; c2; c3 }; ...
       ~~>
     c' = ...; init; while b do { c1; c3 }; init; while b do { c2; c3 }; ...

   where [c1 = body[0..d1)], [c2 = body[d1..d2)], [c3 = body[d2..)]. Side
   conditions ([check_side_conditions]):
   (1) [init] and [c3] are made of assignments, conditionals and matches
       only (deterministic, free of loops, calls and [raise]), and [c1],
       [c2] contain no [raise] and, when the judgement observes exceptions
       (the context's [trc_exn]), no call to a procedure that may raise
       ([EcLowPhlGoal.s_may_raise]);
   (2) [b] and [c3] read no variable written by [c1] or [c2];
   (3) [c1] reads no variable written by [c2] and conversely, and they
       write disjoint sets of variables;
   (4) [c3] only writes variables written by [init];
   (5) [init] reads no variable written by [init], [c1] or [c3], and
       writes no variable written by [c1].
   Then the number of iterations and what [c3] writes only depend on the
   state after [init], the [c1] part and the [c2; c3] part of the fused
   loop exchange no information, and the second [init] restores the state
   after the first one but on what [c1] writes, which it does not touch.
   No obligation, the memory is unchanged.

   Fails, in this order, with "invalid code position" (when [p] is not a
   position of [c]), "in loop-fission, second break offset must not be
   lower than the first one", "code position does not lead to a
   while-loop", "while-loop is not headed by <n> intructions", "in loop
   fission, invalid offsets range", "independence check failed" / "epilog
   must only write variables written by the prelude", "prelude must be
   deterministic and loop/procedure-call free", "epilog must be ...",
   "loop body must not raise exceptions", "loop body must not call
   procedures that may raise exceptions when the postcondition constrains
   exceptions". *)
type EcPlTransform.transform += TrFission of tr_fission

(* -------------------------------------------------------------------- *)
(* The side conditions of the loop fission, shared with the loop fusion
   ([EcTrFusion]); they raise [EcPlTransform.InvalidTransform]. *)

(* [check_side_conditions ~exn env b init c1 c2 c3]: the conditions
   (1)-(5) above, [exn] telling whether the judgement observes
   exceptions. *)
val check_side_conditions :
  exn:bool -> env -> expr -> instr list -> instr list -> instr list -> instr list -> unit
