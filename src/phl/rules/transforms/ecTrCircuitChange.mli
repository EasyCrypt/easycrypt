(* -------------------------------------------------------------------- *)
open EcAst
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_circuit_change = {
  trcc_at    : nm_codepos;       (* position of the first replaced
                                    instruction (resolved, possibly
                                    nested) *)
  trcc_len   : int;              (* number n of replaced instructions *)
  trcc_binds : ovariable list;   (* the fresh locals, as requested *)
  trcc_stmt  : stmt;             (* the new statement [b'], typed in the
                                    memory extended with them *)
}

(* [TrCircuitChange { trcc_at = p; trcc_len = n; trcc_binds = vs;
   trcc_stmt = b' }] — replaces the [n] instructions [b] at position [p]
   (in the block of [p], possibly nested) by [b'], in the memory extended
   with the fresh program variables [vs] (bound one by one with
   [EcMemory.bind_fresh]: a variable is renamed apart when its name is
   already bound; deterministic), provided that [b] and [b'] are
   circuit-equivalent on the variables [K] to keep:

     c = C[b; tl]   ~~>   c' = C[b'; tl]

   [K] is the set of the variables read by the code that may run after
   [b] ([tl], the instructions following each enclosing instruction, and,
   for each enclosing loop, its guard and its whole body: [EcPV.zpr_pv
   `Read `After]), by the postcondition (the context's [trc_post], for
   hoare including the exceptional postconditions) and, when [b] is in a
   loop, by both [b] and [b'], restricted to the variables read or written
   by [b] or [b']. The check is [EcCircuits.instrs_equiv] (under the
   context's [trc_hyps]): [b] and [b'] only contain assignments to local
   variables (no call, sampling, conditional, loop or [raise]), only
   access local variables, and end, from every state, in states agreeing
   on [K]. No obligation.

   Fails with "invalid code position" when [p] is not a position of [c],
   "cannot find n consecutive instructions at given position" when the
   block has fewer than [n] instructions from [p], "circuit-equivalence
   checker error: ..." when the checker fails, and "statements are not
   circuit-equivalent" when it does not establish the equivalence. *)
type EcPlTransform.transform += TrCircuitChange of tr_circuit_change
