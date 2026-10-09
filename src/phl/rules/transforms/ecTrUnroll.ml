(* -------------------------------------------------------------------- *)
open EcAst
open EcModules
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the [unroll] transformation, resolved: the position of
   the loop is a normalized (possibly nested) code position. *)
type tr_unroll = {
  trun_at : EcMatching.Position.nm_codepos;
}

type EcPlTransform.transform += TrUnroll of tr_unroll

(* -------------------------------------------------------------------- *)
(* Replace the loop at [p] by its first iteration, guarded by the loop
   condition, followed by the loop itself. *)
let unroll (p : tr_unroll) (ctxt : tr_ctxt) (s : stmt) =
  let unroll1 (i : instr) =
    match i.i_node with
    | Swhile (e, sw) -> ((), [i_if (e, sw, stmt []); i])
    | _ ->
        raise (InvalidTransform "cannot find a while loop at given position") in

  let (), s =
    let cpos = EcMatching.Position.cpos_of_nm_cpos p.trun_at in
    try  Zpr.map ctxt.trc_env cpos unroll1 s
    with EcMatching.Position.InvalidCPos ->
      raise (InvalidTransform "invalid code position") in

  { trr_me = ctxt.trc_me; trr_s = s; trr_obl = []; }

let () =
  register (function
    | TrUnroll p -> Some (unroll p)
    | _ -> None)
