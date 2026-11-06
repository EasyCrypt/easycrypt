(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_seq_rule = {
  hsr_at  : codegap1;   (* split position k *)
  hsr_mid : ss_inv;     (* intermediate assertion R *)
}

(* [t_hoare_seq { hsr_at = k; hsr_mid = R }] — sequence:

       hoare [c1 : P ==> R | E]      hoare [c2 : R ==> Q | E]
     ----------------------------------------------------------  c = c1; c2
                    hoare [c : P ==> Q | E]                     (c1 = c[0..k))

   where [E] are the exceptional postconditions of the goal, kept unchanged
   in both premises.

   Node: [RHoareSeq { hsn_at = k (resolved index); hsn_mid = R }].
   Checker: "hoare-seq". *)
val t_hoare_seq : hoare_seq_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [seq k : R] on a [hoareS] goal: no side, no bound information, a single
   position and a single assertion. Applies [t_hoare_seq]. *)
val process_hoare_seq : seq_info -> backward
