(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* -------------------------------------------------------------------- *)
(* Parameters of the ehoare [seq] rule. *)
type ehoare_seq_rule = {
  ehsr_at  : codegap1;   (* split position *)
  ehsr_mid : ss_inv;     (* intermediate assertion *)
}

(* Ehoare [seq] rule (TCB): split the statement per [r]. Emits a recheckable
   proof-node. *)
val t_ehoare_seq : ehoare_seq_rule -> backward

(* Elaboration entry for a goal already known to be an [eHoareS]: validates
   the seq surface syntax, types the assertion and split position, then
   applies [t_ehoare_seq]. Takes the parse-tree [seq_info] record directly. *)
val process_ehoare_seq : seq_info -> backward
