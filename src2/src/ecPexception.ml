open EcUtils
open EcTypes
open EcParsetree
open EcTypedtree
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
  
    | UnknownOperatorForSig (name, _)
        -> Format.fprintf fmt "Cannot find operator %a" pp_qsymbol name (* FIXME *)
  
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
  
    | UnexpectedType (ty1, ty2)
        -> Format.fprintf fmt ""
  
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
