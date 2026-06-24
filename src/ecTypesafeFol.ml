(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcDecl
open EcTypes
open EcFol
open EcUnify
open EcEnv

module UE = EcUnify.UniEnv

(* -------------------------------------------------------------------- *)
let f_op_app
   (env      : env)
  ?(typarams : ty_params option)
  ?(rty      : ty option)
   (op       : EcPath.path)
   (args     : form list)
=
  let ue = UE.create typarams in
  let opdecl = EcEnv.Op.by_path op env in
  let opty, tvars = UE.openty ue opdecl.op_tparams None opdecl.op_ty in

  let rty = ofdfl (fun () -> UE.fresh ue) rty in
  let fty = toarrow (List.map (fun f -> f.f_ty) args) rty in

  begin
    try
      EcUnify.unify env ue fty opty
    with UnificationFailure _ -> assert false
  end;

  if not (UE.closed ue) then
    assert false;

  let subst = EcCoreSubst.Tuni.subst (UE.assubst ue) in
  let rty   = EcCoreSubst.ty_subst subst rty in
  let opty  = EcCoreSubst.ty_subst subst opty in
  let tvars = List.map (EcCoreSubst.ty_subst subst) tvars in

  f_app (f_op op tvars opty) args rty
  
(* -------------------------------------------------------------------- *)
let f_app
  ?(redmode : EcReduction.reduction_info = EcReduction.full_red)
   (hyps    : LDecl.hyps)
   (f        : form)
   (args     : form list)
: form =
  let env = LDecl.toenv hyps in
  (* type of [f] applied to its first [n] arguments *)
  let rec result_ty (n : int) (ty : ty) : ty =
    if n <= 0 then ty
    else match (ty_hnorm ty env).ty_node with
      | Tfun (_, codom) -> result_ty (n - 1) codom
      | _ -> assert false
  in
  let rty = result_ty (List.length args) f.f_ty in
  f_app f args rty |> EcReduction.h_red_until redmode hyps
