open EcUtils
open EcTypes
open EcParsetree
open EcTypedtree
open EcTypesmod
open EcPrinting

let pp_ident fmt id = 
  Format.fprintf fmt "%s" (EcIdent.name id)  (* FIXME *)

let pp_tydecl fmt (p,td) =
  let vmap = EcUidgen.NameGen.create () in
  let pp_params fmt = function
    | [] -> ()
    | [id] -> pp_ident fmt id
    | lid -> Format.fprintf fmt "(%a)" (pp_list ~sep:(", ") pp_ident) lid  in
  let pp_body fmt = function
    | None -> ()
    | Some ty -> Format.fprintf fmt " = %a" (pp_type ~vmap) ty in 
  Format.fprintf fmt "type %a%a%a." 
    pp_params td.tyd_params pp_path p pp_body td.tyd_type

let pp_optyparams fmt lid = 
  Format.fprintf fmt "[%a]" (pp_list ~sep:(", ") pp_ident) lid
  
let pp_opdecl fmt (p,d) =
  let str_kind op =
    if op.op_ctnt then "cnst" 
    else if op.op_prob then "pop" else "op" in
  let vmap = EcUidgen.NameGen.create () in
  let pp_type = pp_type ~vmap in
  let pp_tparams fmt = function
    | [] -> Format.fprintf fmt "()"
    | [t] -> pp_type fmt t
    | lt -> Format.fprintf fmt "(%a)" (pp_list ~sep:(", ") pp_type) lt in
  let pp_decl fmt d =
  (*  match body with
    | None -> *) (* FIXME *)
        if d.op_ctnt then 
          Format.fprintf fmt ": %a" pp_type (snd d.op_sig)
        else 
          Format.fprintf fmt ": %a -> %a" 
            pp_tparams (fst d.op_sig) pp_type (snd d.op_sig)
(*    | Some (id,e) ->
        if d.op_ctnt then
          Format.fprintf fmt ": %a = %a" pp_type (snd d.op_sig)
            pp
        Format.fprintf fmt
           *) in
  Format.fprintf fmt "%s %a%a %a."
      (str_kind d) pp_optyparams d.op_params pp_path p
      pp_decl d
  
(* -------------------------------------------------------------------- *)
let pp_typerror =
  let pp fmt = function
    | UnknownVariable name
        -> Format.fprintf fmt "Unknown variable: %a" pp_qsymbol name
  
    | UnknownFunction name
        -> Format.fprintf fmt "Unknown function: %a" pp_qsymbol name
  
    | UnknownTypeName name
        -> Format.fprintf fmt "Unknown type name: %a" pp_qsymbol name
  
    | UnknownOperatorForSig (name, tys)
        -> Format.fprintf fmt "Cannot find operator %a with signature %a" 
            pp_qsymbol name
            pp_dom tys
  
    | InvalidNumberOfTypeArgs (name, n, i)
        -> Format.fprintf fmt 
            "The type %a is applied to %i paramaters while %i is excepted"
            pp_qsymbol name i n
  
    | ApplInvalidArity
        -> Format.fprintf fmt "Wrong number of arguments"
  
    | UnboundTypeParameter name
        -> Format.fprintf fmt "Unbound type parameter: %s" name
  
    | OpNotOverloadedForSig (name, _)   (* FIXME / DUPLICATED *)
        -> Format.fprintf fmt "Cannot find operator %a" pp_qsymbol name
  
    | UnexpectedType (ty1, ty2, t1, t2)
        ->
          let pp_type = pp_type ~vmap:(EcUidgen.NameGen.create()) in
          Format.fprintf fmt "@[the expression has type %a@\nit is expected to have type %a.@\n Can not unify %a and %a@]"
            pp_type ty1 pp_type ty2 pp_type t1 pp_type t2
  
    | NonLinearPattern _
        -> Format.fprintf fmt "Non-linear pattern"
  
    | DuplicatedLocals
        -> Format.fprintf fmt "DuplicatedLocals"
  
    | ProbaExpressionForbidden
        -> Format.fprintf fmt "ProbaExpressionForbidden"
  
    | PatternForbiden
        -> Format.fprintf fmt "PatternForbiden"
  
    | ModApplToNonFunctor
        -> Format.fprintf fmt "ModApplToNonFunctor"
  
    | ModApplInvalidArity
        -> Format.fprintf fmt "Wrong number of module parameters"
  
    | ModApplInvalidArgInterface
        -> Format.fprintf fmt "ModApplInvalidArgInterface"
  
    | PropExpected pf
        -> Format.fprintf fmt "PropExpected"
  
    | TermExpected pf
        -> Format.fprintf fmt "TermExpected"
  in
    fun fmt exn ->
      Format.fprintf fmt "%a\n%!" pp exn
