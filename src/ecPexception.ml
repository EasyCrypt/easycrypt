(* -------------------------------------------------------------------- *)

(* cut and paste from WHY3 *)

type exn_printer = Format.formatter -> exn -> unit

let exn_printers =
  (Stack.create () : (Format.formatter -> exn -> unit) Stack.t)

let register exn_printer = Stack.push exn_printer exn_printers

let default = 
  let all_exn_printer fmt exn =
    Format.fprintf fmt "anomaly: %s, please report" (Printexc.to_string exn) in
  ref all_exn_printer 

let set_default exn_pr = 
  default := exn_pr

exception Exit_loop

let exn_printer fmt exn =
  let test f =
    try
      Format.fprintf fmt "@[%a@]@." f exn;
      raise Exit_loop
    with
      | Exit_loop -> raise Exit_loop
      | _ -> ()
  in
  try Stack.iter test exn_printers; test !default
  with Exit_loop -> ()

(* End cut and paste WHY3 *)

(* -------------------------------------------------------------------- *)
(*let pp_typerror =
  let pp fmt = function
    | UnknownVariable name
        -> Format.fprintf fmt "Unknown variable: %a" pp_qsymbol name
  
    | UnknownFunction name
        -> Format.fprintf fmt "Unknown function: %a" pp_qsymbol name
  
    | UnknownTypeName name
        -> Format.fprintf fmt "Unknown type name: %a" pp_qsymbol name

    | UnknownModName name
        -> Format.fprintf fmt "Unknown module name: %a" pp_qsymbol name
  
    | UnknownTyModName name
        -> Format.fprintf fmt "Unknown module type name: %a" pp_qsymbol name

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
  
    | DuplicatedLocals None
        -> Format.fprintf fmt "DuplicatedLocals"

    | DuplicatedLocals (Some s)
        -> Format.fprintf fmt "A symbol %s already declared at %s"
            s.pl_desc (Location.tostring s.pl_loc)
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

    | TypeVariableNotAllowed 
        -> Format.fprintf fmt "Type variable not allowed"

    | UnificationVariableNotAllowed 
        -> Format.fprintf fmt "unification variable not allowed"

    | RandomExprNotAllowed 
        -> Format.fprintf fmt "random expression not allowed"

    | UnNamedTypeVariable 
        -> Format.fprintf fmt "unnamed type variable"

    | UnusedTypeVariable 
        -> Format.fprintf fmt "unused type variable"
        
  in
    fun fmt exn ->
      Format.fprintf fmt "%a\n%!" pp exn

let _ = register (fun fmt exn ->
  match exn with
  | TyError (loc,exn) ->
      EcPrinting.pp_located loc pp_typerror fmt exn
  | _ -> raise exn)
      
(* -------------------------------------------------------------------- *)

let pp_exn fmt exn =
  match exn with
  | EcUnify.UnificationFailure(ty1,ty2) -> 
      let vmap = EcUidgen.NameGen.create () in
      Format.fprintf fmt "Unification Failure %a and %a"
        (pp_type ~vmap) ty1 (pp_type ~vmap) ty2
  | EcEnv.LookupFailure (`Path p) ->
      Format.fprintf fmt "cannot find path: %a@."
        pp_path p

  | EcEnv.LookupFailure (`QSymbol qname) ->
      Format.fprintf fmt "cannot find symbol: %a@."
        pp_qsymbol qname
  | _ -> raise exn 

let _ = register pp_exn
*)



