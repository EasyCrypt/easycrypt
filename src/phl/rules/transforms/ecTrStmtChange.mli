(* -------------------------------------------------------------------- *)
open EcAst
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_stmt_change = {
  trsc_range : nm_codegap_range;   (* the range [p : [s..f)] to replace
                                      (resolved, possibly nested) *)
  trsc_binds : ovariable list;     (* the fresh locals, as requested *)
  trsc_stmt  : stmt;               (* the new statement [b'], typed in the
                                      memory extended with them *)
}

(* [TrStmtChange { trsc_range = r; trsc_binds = vs; trsc_stmt = b' }] —
   replaces the instructions [b] of the range [r] (of a possibly nested
   block) by [b'], in the memory extended with the fresh program variables
   [vs] ([EcMemory.bindall_fresh vs]: a variable is renamed apart when its
   name is already bound; deterministic, so that the statement typed by
   the tactic in that memory and the checker agree):

     c = C[b]   ~~>   c' = C[b']

   with [Before] / [After] the code other than [b] that may run before /
   after [b] ([EcPV.zpr_pv]: the instructions around [b] in its block and
   the enclosing ones, and for each enclosing loop, its guard and its
   whole body):
   - [M]: the variables written [Before] [b], and, when [b] is in a loop,
     by [b] itself (its previous runs);
   - [R]: the variables read by both [b] and [b'];
   - [O]: the variables read [After] [b], by the postcondition (the
     context's [trc_post]: for hoare including the exceptional
     postconditions, for phoare not the bound, evaluated in the initial
     memory), and, when [b] is in a loop, [R];
   - [W]: the variables written by [b] or [b'] that are in [O].
   One obligation, [OLocalEquiv { ole_locals = xs; ole_orig = b;
   ole_new = b'; ole_reads = R; ole_writes = W; ole_modi = M }], [xs]
   being the match-arm locals in scope at [b] (which [b] may mention:
   the local equivalence holds for all their values).

   Soundness: the original and new programs are related by "the states
   agree on [O]" (they are equal before the first run of [b]). The code
   after [b] only reads [O], so it preserves this relation. When reaching
   [b], the relation implies [={R}] ([R] is in [O] in a loop; outside,
   [b] runs once, from equal states), the frame holds on the original
   side as no code run so far writes its variables ([M]), and the local
   equivalence re-establishes the relation: the observable variables that
   are written are equal, and the other ones are unchanged. The fresh
   variables are read by no code but [b'], and are not constrained by
   the local equivalence.

   Fails with "invalid code position" when [r] is not a range of [c]. *)
type EcPlTransform.transform += TrStmtChange of tr_stmt_change
