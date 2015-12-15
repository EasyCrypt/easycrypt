(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcLocation
open EcParsetree
open EcTypes
open EcEnv

module TT = EcTyping

(* -------------------------------------------------------------------- *)
type nterror =
| NTE_Typing        of EcTyping.tyerror
| NTE_TyNotClosed
| NTE_DupIdent
| NTE_UnknownBinder of symbol
| NTE_AbbrevIsVar

exception NotationError of EcLocation.t * EcEnv.env * nterror

let nterror loc env e = raise (NotationError (loc, env, e))

(* -------------------------------------------------------------------- *)
let trans_notation_r (env : env) (nt : pnotation located) =
  let nt = nt.pl_desc and gloc = nt.pl_loc in
  let ue = TT.transtyvars env (gloc, nt.nt_tv) in

  (* Translate bound idents and their types *)
  let bd = List.mapi (fun i (x, pty) ->
    let id = EcIdent.create (unloc x) in
    let ty = TT.transty TT.tp_relax env ue pty in
    (unloc x, (i, (id, ty)))) nt.nt_bd in

  if not (List.is_unique ~eq:(fun (x, _) (y, _) -> sym_equal x y) bd) then
    nterror gloc env NTE_DupIdent;

  let bd = Msym.of_list bd in

  let getident x =
    try  Msym.find (unloc x) bd
    with Not_found -> nterror (loc x) env (NTE_UnknownBinder (unloc x))
  in

  (* Translate formal arguments and theiry types *)
  let abd, xs = List.split (List.map (fun (x, (xbd, ty)) ->
    let dty = fun () -> mk_loc (loc x) (PTunivar) in
    let arg = ([mk_loc (loc x) (Some x)], ofdfl dty ty) in
    (List.map getident xbd, arg)) nt.nt_args) in

  let xs = List.map2 (fun xty (aid, aty) ->
    (aid, toarrow (List.map (snd |- snd) xty) aty))
    abd (snd (TT.trans_binding env ue xs)) in

  let benv  = EcEnv.Var.bind_locals xs env in
  let codom = TT.transty TT.tp_relax env ue nt.nt_codom in
  let body  = TT.transexpcast benv `InOp ue codom nt.nt_body in

  if not (EcUnify.UniEnv.closed ue) then
    nterror gloc env NTE_TyNotClosed;

  ignore body; ()

(* -------------------------------------------------------------------- *)
let trans_notation (env : EcEnv.env) (nt : pnotation located) =
  try  trans_notation_r env nt
  with TT.TyError (loc, env, e) -> nterror loc env (NTE_Typing e)

(* -------------------------------------------------------------------- *)
let trans_abbrev_r (env : env) (at : pabbrev located) =
  let at = at.pl_desc and gloc = at.pl_loc in
  let ue = TT.transtyvars env (gloc, at.ab_tv) in
  let benv, xs = TT.trans_binding env ue at.ab_args in
  let codom = TT.transty TT.tp_relax env ue (fst at.ab_def) in
  let body = TT.transexpcast benv `InOp ue codom (snd at.ab_def) in

  if not (EcUnify.UniEnv.closed ue) then
    nterror gloc env NTE_TyNotClosed;

  let uni     = EcUnify.UniEnv.close ue in
  let body    = e_mapty (Tuni.offun uni) body in
  let codom   = Tuni.offun uni codom in
  let xs      = List.map (snd_map (Tuni.offun uni)) xs in
  let tparams = EcUnify.UniEnv.tparams ue in
  let tyat    = EcDecl.mk_abbrev tparams xs (codom, body) in

  if EcTypes.is_local body then
    nterror gloc env NTE_AbbrevIsVar;

  (unloc at.ab_name, tyat)

(* -------------------------------------------------------------------- *)
let trans_abbrev (env : EcEnv.env) (nt : pabbrev located) =
  try  trans_abbrev_r env nt
  with TT.TyError (loc, env, e) -> nterror loc env (NTE_Typing e)
