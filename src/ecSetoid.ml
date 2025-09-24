(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcPath
open EcAst
open EcTypes
open EcFol
open EcEnv
open EcMatching

(* -------------------------------------------------------------------- *)
type instance = {
  relation : path * ty list;
  params   : form list;
}

(* -------------------------------------------------------------------- *)
let as_instance (env : env) ((oppath, optyargs), args) =
  let exception NotASetoid in

  try
    let op = EcEnv.Op.by_path oppath env in
    let _rel = oget ~exn:NotASetoid (EcEnv.Setoid.get_relation env oppath) in

    let nparams = List.length (fst (tyfun_flat op.op_ty)) - 2 in

    if List.length args <> nparams + 2 then
      raise NotASetoid;

    let f1, f2 = as_seq2 (List.drop nparams args) in
    let params = List.take nparams args in
    Some ({ relation = (oppath, optyargs); params; }, (f1, f2))

  with NotASetoid -> None

(* -------------------------------------------------------------------- *)
let valid_setoid_context (env : env) (instance : instance) (ctxt : FPosition.ctxt) =
  let eqvp = fst (instance.relation) in
  let eqv = oget (EcEnv.Setoid.get_relation env eqvp) in

  let accept (ineqv : bool) (ctxt1 : FPosition.ctxt1) =
    match ctxt1.ctxt with
    | CT_AppArg ({ f_node = Fop (p, _)}, (_, rargs)) when List.length rargs < 2 && EcPath.p_equal p eqvp ->
      true
    | CT_AppArg ({ f_node = Fop (p, _)}, (largs, _)) when ineqv -> begin
      match Mp.find_opt p eqv.morphisms with
      | None ->
        false
      | Some mph ->
        Mint.mem (1 + List.length largs) mph
      end
    | _ ->
      false in

  List.fold_left accept false ctxt

