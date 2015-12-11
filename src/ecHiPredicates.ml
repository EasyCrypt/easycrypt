(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcTypes
open EcParsetree

module TT = EcTyping

(* -------------------------------------------------------------------- *)
type tperror =
| TPE_Typing of EcTyping.tyerror
| TPE_TyNotClosed

exception TransPredError of EcLocation.t * EcEnv.env * tperror

let tperror loc env e = raise (TransPredError (loc, env, e))

(* -------------------------------------------------------------------- *)
let trans_preddecl_r (env : EcEnv.env) (pr : ppredicate located) =
  let pr = pr.pl_desc and loc = pr.pl_loc in
  let ue = TT.transtyvars env (loc, pr.pp_tyvars) in
  let tp = TT.tp_relax in

  let dom, body =
    match pr.pp_def with
    | PPabstr ptys ->
        (List.map (TT.transty tp env ue) ptys, None)

    | PPconcr (bd, pe) ->
        let env, xs = TT.transbinding env ue bd in
        let body = TT.trans_prop env ue pe in
        let dom = List.map snd xs in
        let xs = List.map (fun (x,ty) -> x, EcFol.GTty ty) xs in
        let lam = EcFol.f_lambda xs body in
        (dom, Some lam)
  in

  if not (EcUnify.UniEnv.closed ue) then
    tperror loc env TPE_TyNotClosed;

  let uni     = EcUnify.UniEnv.close ue in
  let body    = body |> omap (EcFol.Fsubst.uni uni) in
  let dom     = List.map (Tuni.offun uni) dom in
  let tparams = EcUnify.UniEnv.tparams ue in

  EcDecl.mk_pred tparams dom body

(* -------------------------------------------------------------------- *)
let trans_preddecl (env : EcEnv.env) (pr : ppredicate located) =
  try  trans_preddecl_r env pr
  with TT.TyError (loc, env, e) -> tperror loc env (TPE_Typing e)
