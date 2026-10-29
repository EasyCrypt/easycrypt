(* -------------------------------------------------------------------- *)
open EcTypes
open EcAst
open EcModules
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the [splitwhile] transformation, resolved: the position
   of the loop is a normalized (possibly nested) code position, the
   additional condition a typed expression. *)
type tr_splitwhile = {
  trsw_at   : EcMatching.Position.nm_codepos;
  trsw_cond : expr;
}

type EcPlTransform.transform += TrSplitWhile of tr_splitwhile

(* -------------------------------------------------------------------- *)
(* Precede the loop at [p] by the same loop, also guarded by [b]. *)
let splitwhile (p : tr_splitwhile) (ctxt : tr_ctxt) (s : stmt) =
  let split1 (i : instr) =
    match i.i_node with
    | Swhile (e, sw) ->
        let op_ty  = toarrow [tbool; tbool] tbool in
        let op_and = e_op EcCoreLib.CI_Bool.p_and [] op_ty in
        let e = e_app op_and [e; p.trsw_cond] tbool in
        ((), [i_while (e, sw); i])

    | _ ->
        raise (InvalidTransform "cannot find a while loop at given position") in

  let (), s =
    let cpos = EcMatching.Position.cpos_of_nm_cpos p.trsw_at in
    try  Zpr.map ctxt.trc_env cpos split1 s
    with EcMatching.Position.InvalidCPos ->
      raise (InvalidTransform "invalid code position") in

  { trr_me = ctxt.trc_me; trr_s = s; trr_obl = []; }

let () =
  register (function
    | TrSplitWhile p -> Some (splitwhile p)
    | _ -> None)
