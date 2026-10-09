(* -------------------------------------------------------------------- *)
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_rmatch = {
  trrm_at   : nm_codepos1;   (* position k of the match (resolved) *)
  trrm_ctor : int;           (* index j of the constructor C *)
}

(* [TrRMatch { trrm_at = k; trrm_ctor = j }] — decides the match
   [i = c[k] = match e with ... | C xs => b | ...] in favour of its [j]-th
   constructor [C], with [c = hd; i; tl] and [hd = c[0..k)]:

     c = hd; i; tl   ~~>   c' = hd; ys <- oget (get_as_C e); b[ys/xs]; tl

   where [ys] are fresh program variables, added to the memory (no
   assignment when [C] has no argument). One obligation:
   [OPrefixPost (hd, exists xs, e = C xs)], in the memory of [c]. Fails
   with "the targetted instruction is not a match" when [i] is not a
   [match], "invalid constructor index" when it has no [j]-th branch (see
   [EcPlRCond.rmatch_select]).

   This is the unframed form of [match C k]; its framed form changes the
   precondition, and is a rule of each logic ([Ec<Logic>RMatch]). *)
type EcPlTransform.transform += TrRMatch of tr_rmatch
