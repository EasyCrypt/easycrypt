(* -------------------------------------------------------------------- *)
open Utils
open Symbols
open Parsetree
open Types

(* -------------------------------------------------------------------- *)
type local = symbol * int

type tyexpr =
  | Eunit                                   (* unit literal      *)
  | Ebool   of bool                         (* bool literal      *)
  | Eint    of int                          (* int. literal      *)
  | Elocal  of local * ty                   (* local variable    *)
  | Eident  of Path.path * ty               (* symbol            *)
  | Eapp    of Path.path * tyexpr list      (* op. application   *)
  | Elet    of lpattern * tyexpr * tyexpr   (* let binding       *)
  | Etuple  of tyexpr list                  (* tuple constructor *)
  | Eif     of tyexpr * tyexpr * tyexpr     (* _ ? _ : _         *)
  | Ernd    of tyrexpr                      (* random expression *)

and tyrexpr =
  | Rbool                                   (* flip               *)
  | Rinter    of tyexpr * tyexpr            (* interval sampling  *)
  | Rbitstr   of tyexpr                     (* bitstring sampling *)
  | Rexcepted of tyrexpr * tyexpr           (* restriction        *)
  | Rapp      of Path.path * tyexpr list    (* p-op. application  *)

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
    | Ptuple tys   -> Ttuple (List.map transty tys)

    | Pnamed name -> begin
      match Scope.Ty.resolve scope name with (* FIXME *)
        | None -> tyerror (UnknownTypeName name)
        | Some (i, p) ->
          if i <> 0 then
            tyerror (InvalidNumberOfTypeArgs (name, 0, i));
          Tconstr (p, [])
    end

    | Papp (name, tyargs) -> begin
      match Scope.Ty.resolve scope name with
        | None -> tyerror (UnknownTypeName name)
        | Some (i, p) ->
          let nargs = List.length tyargs in
            if i <> List.length tyargs then
              tyerror (InvalidNumberOfTypeArgs (name, i, nargs));
            let tyargs = List.map transty tyargs in
              Tconstr (p, tyargs)
    end

    | Pvar a -> begin
      match policy with
        | TyDecl tyvars -> begin
          match List.index a tyvars with
            | None   -> tyerror (UnboundTypeParameter a)
            | Some i -> Trel i
        end

        | TyAnnot uidmap -> Tvar (UidGen.forsym uidmap a)
    end
  in
    fun ty -> transty ty

(* -------------------------------------------------------------------- *)
module Env = struct
  type env = (symbol * ty) list

  let empty = []

  let bind (_ : symbol * ty) (e : env) = (failwith "" : env)

  let bindall (_ : (symbol * ty) list) (e : env) = (failwith "" : env)
end

type epolicy = {
  epl_prob : bool;
}

(* -------------------------------------------------------------------- *)
let transexp (scope : Scope.scope) =
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
          | LPSymbol x  -> transexp (Env.bind (x, ty1) env) policy e2
          | LPTuple  xs ->
            let tyvars = List.map (fun _ -> mkunivar ()) xs in
              if not (Unify.unify (Ttuple tyvars) ty1) then
                tyerror (UnexpectedType (Ttuple tyvars, ty1));
              transexp (Env.bindall (List.combine xs tyvars) env) policy e2
      in
        (Elet (p, e1, e2), ty2)
    end

    | PEtuple es ->
      let es, tys =
        List.split (List.map (transexp env policy) es)
      in
        (Etuple es, Ttuple tys)

    | PEif (c, e1, e2) ->
      let c, tyc = transexp env policy c in
        if not (Unify.unify tyc (tbool ())) then
          tyerror (UnexpectedType (tyc, (tbool ())));
        let e1, ty1 = transexp env policy e1 in
        let e2, ty2 = transexp env policy e2 in
          if not (Unify.unify ty1 ty2) then
            tyerror (UnexpectedType (ty1, ty2));
          (Eif (c, e1, e2), ty1)

    | PErnd re ->
      if not policy.epl_prob then
        tyerror ProbaExpressionForbidden;
      let re, ty = transrexp env policy re in
        (Ernd re, ty)

  and transrexp (env : Env.env) (policy : epolicy) = function
    | PRbool -> (Rbool, tbool ())

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
    transexp

