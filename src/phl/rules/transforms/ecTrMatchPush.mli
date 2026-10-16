(* -------------------------------------------------------------------- *)

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

(* [TrMatchPush] — push the continuation of a [match] into its branches:

     c = match e with | C_i xs_i => b_i end; c0
       ~~>
     c' = match e with | C_i xs_i' => { b_i[xs_i'/xs_i]; c0 } end

   The [match] is the first instruction of [c], and [c'] is a single
   instruction. No parameter, no obligation, the memory is unchanged.
   Fails with "the first instruction is not a match" otherwise.

   Capture: the pattern variables [xs_i] are local identifiers (not
   program variables) bound in [b_i] only, while [c0] is outside of their
   scope and may mention local identifiers free (e.g. the logical
   variables introduced by a two-sided [match]). Moving [c0] under the
   binders [xs_i] would capture such an occurrence. The entry therefore
   renames the binders of a branch to fresh identifiers [xs_i'] when one of
   them occurs free in [c0] (and keeps them, [xs_i' = xs_i], otherwise), so
   that [c0] keeps its meaning in every branch: each run of [c'] executes
   the branch selected by the value of [e], with the same bindings, then
   [c0], as [c] does. Program variables read or written by [c0] (even when
   named like a pattern variable) are not affected. *)
type EcPlTransform.transform += TrMatchPush
