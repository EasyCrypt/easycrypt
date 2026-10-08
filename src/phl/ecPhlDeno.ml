(* -------------------------------------------------------------------- *)
open EcParsetree

(* -------------------------------------------------------------------- *)
(* The [deno] rules live in [rules/<logic>/] (bdhoare, ehoare, equiv),
   with their derived forms and elaboration. This module only keeps the
   dispatcher and the legacy entry points. *)
let t_phoare_deno pre post =
  EcBdHoareDeno.(t_bdhoare_deno_full { bdd_pre = pre; bdd_post = post; })

let t_equiv_deno pre post =
  EcEquivDeno.(t_equiv_deno { eqd_pre = pre; eqd_post = post; })

(* -------------------------------------------------------------------- *)
type denoff = deno_ppterm * bool * pformula option

let process_deno mode ((info, _, _) as denoff : denoff) tc =
  match mode with
  | `PHoare -> EcBdHoareDeno.process_bdhoare_deno info tc
  | `EHoare -> EcEHoareDeno.process_ehoare_deno info tc
  | `Equiv  -> EcEquivDeno.process_equiv_deno denoff tc
