(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type ehoare_seq_rule = {
  ehsr_at  : codegap1;   (* split position k *)
  ehsr_mid : ss_inv;     (* intermediate expectation R *)
}

(* [t_ehoare_seq { ehsr_at = k; ehsr_mid = R }] — sequence:

       ehoare [c1 : P ==> R]      ehoare [c2 : R ==> Q]
     --------------------------------------------------  c = c1; c2
                   ehoare [c : P ==> Q]                 (c1 = c[0..k))

   Node: [REHoareSeq { ehsn_at = k (resolved index); ehsn_mid = R }].
   Checker: "ehoare-seq". *)
val t_ehoare_seq : ehoare_seq_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [seq k : R] on an [eHoareS] goal: no side, no bound information, a single
   position and a single (xreal) expectation. Applies [t_ehoare_seq]. *)
val process_ehoare_seq : seq_info -> backward
