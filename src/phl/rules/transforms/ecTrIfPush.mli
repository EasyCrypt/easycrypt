(* -------------------------------------------------------------------- *)

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

(* [TrIfPush] — push the continuation of a conditional into its branches:

     c = if b then c1 else c2; c0   ~~>   c' = if b then { c1; c0 }
                                                 else { c2; c0 }

   The conditional is the first instruction of [c], and [c'] is a single
   instruction. No parameter, no obligation, the memory is unchanged.
   Fails with "the first instruction is not a conditional" otherwise. *)
type EcPlTransform.transform += TrIfPush
