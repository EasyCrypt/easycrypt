(* -------------------------------------------------------------------- *)
open Utils
open Symbols
open Parsetree
open Types
open Typesexpr
open Typesmod

(* -------------------------------------------------------------------- *)
type tyerror =
  | UnknownTypeName          of qsymbol
  | UnknownOperatorForSig    of qsymbol * ty list
  | InvalidNumberOfTypeArgs  of qsymbol * int * int
  | UnboundTypeParameter     of symbol
  | OpNotOverloadedForSig    of Scope.Op.op * ty list
  | UnexpectedType           of ty * ty
  | ProbaExpressionForbidden
  | PatternForbiden

exception TyError of tyerror

let tyerror x = raise (TyError x)

(* -------------------------------------------------------------------- *)
type typolicy =
  | TyDecl  of symbol list
  | TyAnnot of UidGen.uidmap

let transty (scope : Scope.scope) (policy : typolicy) =
  let rec transty = function
      (* Base types *)
    | Punit        -> Tbase Tunit
    | Pbool        -> Tbase Tbool
    | Pint         -> Tbase Tint
    | Preal        -> Tbase Treal
    | Ptuple tys   -> Ttuple (Parray.fmap transty tys)

    | Pnamed name -> begin
      match Scope.Ty.resolve scope name with (* FIXME *)
        | None -> tyerror (UnknownTypeName name)
        | Some (i, p) ->
          if i <> 0 then
            tyerror (InvalidNumberOfTypeArgs (name, 0, i));
          Tconstr (p, Parray.empty)
    end

    | Papp (name, tyargs) -> begin
      match Scope.Ty.resolve scope name with
        | None -> tyerror (UnknownTypeName name)
        | Some (i, p) ->
          let nargs = List.length tyargs in
            if i <> List.length tyargs then
              tyerror (InvalidNumberOfTypeArgs (name, i, nargs));
            let tyargs = Parray.fmap transty tyargs in
              Tconstr (p, tyargs)
    end

    | Pvar a -> begin
      match policy with
        | TyDecl tyvars -> begin
          match List.index a tyvars with
            | None   -> tyerror (UnboundTypeParameter a)
            | Some i -> Trel (a, i)
        end

        | TyAnnot uidmap -> Tvar (a, (UidGen.forsym uidmap a))
    end
  in
    fun ty -> transty ty

(* -------------------------------------------------------------------- *)
type epolicy = {
  epl_prob : bool;
}

(* -------------------------------------------------------------------- *)
let transexp (scope : Scope.scope) =
  let uidmap = ref UidGen.Muid.empty in

  let unify ty1 ty2 =
    try  uidmap := (Unify.unify scope !uidmap ty1 ty2); true
    with Unify.CanNotUnify _ -> false
  in

  let rec transexp (env : Env.env) (policy : epolicy) = function
    | PEunit   -> (Eunit  , tunit ())
    | PEbool b -> (Ebool b, tbool ())
    | PEint  i -> (Eint  i, tint  ())

    | PEapp (name, es) -> begin
      let es   = List.map (transexp env policy) es in
      let esig = snd (List.split es) in

        match Scope.Op.resolve scope name esig with
          | None    -> tyerror (UnknownOperatorForSig (name, esig))
          | Some op -> (Eapp (op.Scope.Op.op_path, List.map fst es), tunit ()) (* FIXME *)
    end

    | PElet (p, e1, e2) -> begin
      let e1, ty1 = transexp env policy e1 in
      let e2, ty2 =
        match p with
          | LPSymbol x  -> transexp (Env.bind_value x ty1 env) policy e2
          | LPTuple  xs ->
            let tyvars = Parray.fmap (fun _ -> mkunivar ()) xs in
              if not (unify (Ttuple tyvars) ty1) then
                tyerror (UnexpectedType (Ttuple tyvars, ty1));
              transexp
                (Env.bind_values (List.combine xs (Parray.to_list tyvars)) env)
                policy e2
      in
        (Elet (p, e1, e2), ty2)
    end

    | PEtuple es ->
      let es, tys =
        Parray.split (Parray.fmap (transexp env policy) es)
      in
        (Etuple (Parray.to_list es), Ttuple tys)

    | PEif (c, e1, e2) ->
      let c, tyc = transexp env policy c in
        if not (unify tyc (tbool ())) then
          tyerror (UnexpectedType (tyc, (tbool ())));
        let e1, ty1 = transexp env policy e1 in
        let e2, ty2 = transexp env policy e2 in
          if not (unify ty1 ty2) then
            tyerror (UnexpectedType (ty1, ty2));
          (Eif (c, e1, e2), ty1)

    | PErnd re ->
      if not policy.epl_prob then
        tyerror ProbaExpressionForbidden;
      let re, ty = transrexp env policy re in
        (Ernd re, ty)

  and transrexp (env : Env.env) (policy : epolicy) = function
    | PRbool -> (Rbool, tbool ())

    | _ -> assert false                 (* FIXME *)

  (*
    | PRinter (e1, e2) ->
    let e1, ty1 = transexp e1 in
    let e2, ty2 = transexp e2 in
    

  (* flip               *)
    | PRinter    of expr * expr             (* interval sampling  *)
    | PRbitstr   of expr                    (* bitstring sampling *)
    | PRexcepted of rexpr * expr            (* restriction        *)
    | PRapp      of symbol * expr list      (* p-op. application  *)
  *)
  in
    transexp                            (* FIXME: close type *)

(* -------------------------------------------------------------------- *)
exception DuplicatedSigItemName   of psignature
exception DuplicatedArgumentsName of pfunction_decl

let name_of_sigitem = function
  | `VariableDecl v -> v.pvd_name
  | `FunctionDecl f -> f.pfd_name

let transsig (scope : Scope.scope) (env : Env.env) (is : psignature) =
  let transsig1 = function
    | `VariableDecl x ->
        let name  = x.pvd_name in
        let type_ = transty scope (TyDecl []) x.pvd_type in
          Tys_variable (name, type_)

    | `FunctionDecl f ->
        let name   = f.pfd_name in
        let tyargs =
          List.map                      (* FIXME: continuation *)
            (fun (x, ty) -> (x, transty scope (TyDecl []) ty))
            f.pfd_tyargs in
        let resty  = transty scope (TyDecl []) f.pfd_tyresult in

          if not (List.uniq (List.map fst f.pfd_tyargs)) then
            raise (DuplicatedArgumentsName f);
          Tys_function
            { fs_name = name;
              fs_sig  = (tyargs, resty);
              fs_uses = []; }

  in

  let items = List.map transsig1 is in
  let names = List.map name_of_sigitem is in

    if not (List.uniq names) then
      raise (DuplicatedSigItemName is)
    else
      items
