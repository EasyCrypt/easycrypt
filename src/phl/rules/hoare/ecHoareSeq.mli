(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* -------------------------------------------------------------------- *)
(* Parameters of the hoare [seq] rule (recorded in the proof-node). *)
type hoare_seq_rule = {
  hsr_at  : codegap1;   (* split position *)
  hsr_mid : ss_inv;     (* intermediate assertion *)
}

(* Hoare [seq] rule (TCB): split the statement per [r]. Emits a recheckable
   proof-node. *)
val t_hoare_seq : hoare_seq_rule -> backward

(* Elaboration entry for a goal already known to be a [hoareS]: validates the
   seq surface syntax, types the assertion and split position, then applies
   [t_hoare_seq]. Takes the parse-tree [seq_info] record directly. *)
val process_hoare_seq : seq_info -> backward
