(* -------------------------------------------------------------------- *)
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_fusion = {
  trfu_at   : nm_codepos;   (* position of the 1st loop (resolved,
                               maybe nested) *)
  trfu_init : int;          (* length n of the preludes *)
  trfu_d1   : int;          (* length d1 of the 1st body, epilog excluded *)
  trfu_d2   : int;          (* length d2 of the 2nd body, epilog excluded *)
}

(* [TrFusion { trfu_at = p; trfu_init = n; trfu_d1 = d1; trfu_d2 = d2 }]
   — merges two loops with the same condition, prelude and epilog, the
   first one at the (possibly nested) position [p], both preceded by a
   prelude of [n] instructions (in the same block):

     c = ...; init; while b do { c1; c3 }; init'; while b' do { c2; c3' }; ...
       ~~>
     c' = ...; init; while b do { c1; c2; c3 }; ...

   where [c1] (resp. [c2]) is made of the first [d1] (resp. [d2])
   instructions of its body, and [init] and [init'] (resp. [c3] and [c3'],
   [b] and [b']) are equal (up to [EcReduction.EqTest]). Side conditions:
   those of the fission, of which this is the inverse
   ([EcTrFission.check_side_conditions ~exn b init c1 c2 c3]). No obligation,
   the memory is unchanged.

   Fails, in this order, with "invalid code position" (when [p] is not a
   position of [c]), "code position does not lead to a while-loop", "1st
   while-loop is not headed by <n> intruction(s)", "1st first-loop is not
   followed by <n> instruction(s)", "cannot find the 2nd while-loop", "in
   loop-fusion, body is less than <d1> instruction(s)" (then <d2>), "in
   loop-fusion, preludes do not match", "in loop-fusion, epilogs do not
   match", "in loop-fusion, while conditions do not match", then the
   failures of the fission's side conditions. *)
type EcPlTransform.transform += TrFusion of tr_fusion
