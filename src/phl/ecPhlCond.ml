(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* The [if] and [match] rules live, one module per logic, in
   [rules/<logic>/]. This module only keeps the legacy entry points:
   adapters onto the derived tactics there (the push transformation, then
   the rule on the conditional alone), so that external callers and this
   module's interface are unchanged. *)

(* -------------------------------------------------------------------- *)
let t_hoare_cond   = EcHoareIf.t_hoare_if_head
let t_ehoare_cond  = EcEHoareIf.t_ehoare_if_head
let t_bdhoare_cond = EcBdHoareIf.t_bdhoare_if_head
let t_equiv_cond   = EcEquivIf.t_equiv_if_head

(* -------------------------------------------------------------------- *)
let t_hoare_match   = EcHoareMatch.t_hoare_match_head
let t_bdhoare_match = EcBdHoareMatch.t_bdhoare_match_head
let t_equiv_match   = EcEquivMatch.t_equiv_match_head
