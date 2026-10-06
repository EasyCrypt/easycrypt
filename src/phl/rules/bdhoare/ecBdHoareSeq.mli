(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [seq] rule: the prefix is split on the event
   [bsr_r], with prefix bounds [bsr_f1] / [bsr_g1] (for [r] / [!r]), suffix
   bounds [bsr_f2] / [bsr_g2], and invariant [bsr_phi] after the prefix. *)
type bdhoare_seq_rule = {
  bsr_at  : codegap1;   (* split position *)
  bsr_phi : ss_inv;     (* invariant after the prefix *)
  bsr_r   : ss_inv;     (* event splitting the prefix *)
  bsr_f1  : ss_inv;
  bsr_f2  : ss_inv;
  bsr_g1  : ss_inv;
  bsr_g2  : ss_inv;
}

(* Bdhoare [seq] rule (TCB): split the statement per [r]. Emits a recheckable
   proof-node. Leaves the non-modification subgoal open. *)
val t_bdhoare_seq : bdhoare_seq_rule -> backward

(* Derived: [t_bdhoare_seq], then a best-effort discharge of the
   non-modification subgoal. *)
val t_bdhoare_seq_full : bdhoare_seq_rule -> backward

(* Elaboration entry for a goal already known to be a [bdHoareS]: validates
   the seq surface syntax, types the event, bound information and split
   position, then applies [t_bdhoare_seq_full]. Takes the parse-tree
   [seq_info] record directly. *)
val process_bdhoare_seq : seq_info -> backward
