(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcParsetree
open EcTypedtree
open EcDecl
open EcTypesmod
open EcPrinting

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
            Format.fprintf fmt "@[the expression has type %a@\n" pp_type ty1;
            Format.fprintf fmt "It is expected to have type %a.@\n" pp_type ty2;
            Format.fprintf fmt "Can not unify %a and %a@]" pp_type t1 pp_type t2
  
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

(* -------------------------------------------------------------------- *)
let pp_exn fmt exn =
  match exn with
  | EcEnv.LookupFailure (`Path p) ->
      Format.fprintf fmt "cannot find path: %a@."
        EcPrinting.pp_path p

  | EcEnv.LookupFailure (`QSymbol qname) ->
      Format.fprintf fmt "cannot find symbol: %a@."
        EcPrinting.pp_qsymbol qname

  | _ -> try Why3.Exn_printer.exn_printer fmt exn with _ -> ()

