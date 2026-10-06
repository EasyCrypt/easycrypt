(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv [seq] rule. *)
type equiv_seq_rule = {
  esr_at  : codegap1 pair;   (* split positions (left, right) *)
  esr_mid : ts_inv;          (* intermediate relation *)
}

(* Equiv [seq] rule (TCB): split both statements per [r]. Emits a recheckable
   proof-node. *)
val t_equiv_seq : equiv_seq_rule -> backward

(* One-sided equiv [seq] (derived): split the [side] statement at the given
   position, with one-sided intermediate assertions [pre] / [post]. *)
val t_equiv_seq_onesided : side -> codegap1 -> ss_inv -> ss_inv -> backward

(* Elaboration entry for a goal already known to be an [equivS]: handles both
   the one-sided and two-sided surface forms. Takes the parse-tree [seq_info]
   record directly. *)
val process_equiv_seq : seq_info -> backward
