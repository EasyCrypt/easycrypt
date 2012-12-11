(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcDecl
open EcTypesmod

(* -------------------------------------------------------------------- *)
type scope = EcPath.path option

type env = {
  env_scope  : EcPath.path option;
  mc_used_th : EcIdent.Sid.t;
  env_root   : mcomponents;
}

and mcomponents = {
  mc_variables  : (EcPath.path * EcTypes.ty)           EcIdent.Map.t;
  mc_functions  : (EcPath.path * EcTypesmod.funsig)    EcIdent.Map.t;
  mc_modules    : (EcPath.path * EcTypesmod.tymod)     EcIdent.Map.t;
  mc_modtypes   : (EcPath.path * EcTypesmod.tymod)     EcIdent.Map.t;
  mc_typedecls  : (EcPath.path * EcDecl.tydecl)        EcIdent.Map.t;
  mc_operators  : (EcPath.path * EcDecl.operator)      EcIdent.Map.t;
  mc_axioms     : (EcPath.path * EcDecl.axiom)         EcIdent.Map.t;
  mc_theories   : (EcPath.path * EcTypesmod.theory)    EcIdent.Map.t;
  mc_components : (EcPath.path * mcomponents Lazy.t)   EcIdent.Map.t;
  mc_history    : (EcPath.path * mchistory) list;
}

and mchistory =
| MC_Variable  of EcTypes.ty
| MC_Function  of EcTypesmod.funsig
| MC_Module    of EcTypesmod.tymod * (mcomponents Lazy.t)
| MC_Modtype   of EcTypesmod.tymod
| MC_Typedecl  of EcDecl.tydecl
| MC_Operator  of EcDecl.operator
| MC_Axiom     of EcDecl.axiom
| MC_Theory    of EcTypesmod.theory 
| MC_use       of EcPath.path        (* full path *)
| MC_import    of EcPath.path        (* full path *)

(* -------------------------------------------------------------------- *)
let emcomponents = {
  mc_variables  = EcIdent.Map.empty;
  mc_functions  = EcIdent.Map.empty;
  mc_modules    = EcIdent.Map.empty;
  mc_modtypes   = EcIdent.Map.empty;
  mc_typedecls  = EcIdent.Map.empty;
  mc_operators  = EcIdent.Map.empty;
  mc_axioms     = EcIdent.Map.empty;
  mc_theories   = EcIdent.Map.empty;
  mc_components = EcIdent.Map.empty;
  mc_history    = [];
}

let empty =
  { env_scope = None;
    mc_used_th    = EcIdent.Sid.empty;
    env_root  = emcomponents; }



(* -------------------------------------------------------------------- *)
let root (env : env) = env.env_scope

exception UnknownPath of EcPath.path

module IM = EcIdent.Map

let lookup_p on p env = 
  let rec aux mc p l = 
    match l with
    | [] -> assert false
    | [x] -> 
        begin match IM.byident x (on mc) with
        | None -> raise (UnknownPath (EcPath.extend p x))
        | Some (_,v) -> v
        end
    | x::l -> 
        let p' = EcPath.extend p x in
        match IM.byident x mc.mc_components with
        | None -> 
            Format.printf "ICI2@\n";
            raise (UnknownPath p')
        | Some (_, mc') -> aux (Lazy.force mc') (Some p') l in
  aux env.env_root None (EcPath.tolist p)
(* -------------------------------------------------------------------- *)
let enter (name : symbol) (env : env) =
  let name = EcIdent.create name in
  let path =
    match env.env_scope with
    | None   -> EcPath.Pident name
    | Some p -> EcPath.Pqname (p, name)
  in
    (name, { env with env_scope = Some path })

(* -------------------------------------------------------------------- *)
exception LookupFailure

let try_lf (f : unit -> 'a) =
  try Some (f ()) with LookupFailure _ -> None

(* -------------------------------------------------------------------- *)
module type S = sig
  type t

  val bind        : EcIdent.t -> t -> env -> env
  val bindall     : (EcIdent.t * t) list -> env -> env
  val lookup_p    : EcPath.path -> env -> t        (* full path *)
  val trylookup_p : EcPath.path -> env -> t option (* full path *)
  val lookup      : qsymbol -> env -> EcPath.path * t
  val trylookup   : qsymbol -> env -> (EcPath.path * t) option
  val exists    : qsymbol -> env -> bool
end

(* -------------------------------------------------------------------- *)

module MC = struct

  let mc_history mitem mc =
    { mc with mc_history = mitem :: mc.mc_history }

  let mc_bind_variable path ty mc =
    let x = EcPath.basename path in
      { mc with
          mc_variables = IM.add x (path, ty) mc.mc_variables; }

  let mc_bind_function path fsig mc =
    let x = EcPath.basename path in
      { mc with
          mc_functions = IM.add x (path, fsig) mc.mc_functions; }

  let mc_bind_module path tymod comps mc =
    let x = EcPath.basename path in
      { mc with
          mc_modules    = IM.add x (path, tymod) mc.mc_modules;
          mc_components = IM.add x (path, comps) mc.mc_components; }

  let mc_bind_modtype path tymod mc =
    let x = EcPath.basename path in
      { mc with
          mc_modtypes = IM.add x (path, tymod) mc.mc_modtypes; }

  let mc_bind_typedecl path tydecl mc =
    let x = EcPath.basename path in
      { mc with
          mc_typedecls = IM.add x (path, tydecl) mc.mc_typedecls; }

  let mc_bind_op path op mc =
    let x = EcPath.basename path in
      { mc with
          mc_operators = IM.add x (path, op) mc.mc_operators; }

  let mc_bind_ax path ax mc =
    let x = EcPath.basename path in
      { mc with
        mc_axioms  = IM.add x (path, ax) mc.mc_axioms; }

  let mc_bind_theory path th mc =
    let x = EcPath.basename path in
      { mc with
        mc_theories   = IM.add x (path, th) mc.mc_theories; }

  let mc_bind_component env path mc = 
    let rec add mc p l mcl =
      match l with
      | [] -> assert false
      | [x] -> 
          let p = EcPath.extend p x in
          { mc with mc_components = IM.add x (p,mcl) mc.mc_components }
      | x::l ->
          let p' = EcPath.extend p x in
          match IM.byident x mc.mc_components with
          | None ->  raise (UnknownPath p')
          | Some(pp,mc') ->
              let mc' = add (Lazy.force mc') (Some p') l mcl in
              { mc with 
                mc_components = IM.add (*FIXME:rebind?*) x (pp,lazy mc') mc.mc_components } in
    { env with 
      env_root = add env.env_root None (EcPath.tolist path) mc;
      mc_used_th = EcIdent.Sid.add (EcPath.basename path) env.mc_used_th
    }
    
  let rec mc_of_module (_env : env) (_ : tymod) =
    lazy (failwith "")

  let lookup_mc_p = lookup_p (fun mc -> mc.mc_components) 
 
  let rec mc_of_theory (env : env) path th =
    List.fold_left (mc_of_theory_item (Some path)) (env, emcomponents) th
  and mc_of_theory_item path (env,mc) = function 
    | Th_type (id,td) -> env, mc_bind_typedecl (EcPath.extend path id) td mc
    | Th_operator(id,op) -> env, mc_bind_op (EcPath.extend path id) op mc
    | Th_axiom(id,ax) -> env, mc_bind_ax (EcPath.extend path id) ax mc
    | Th_modtype(id,tm) -> env, mc_bind_modtype (EcPath.extend path id) tm mc
    | Th_module _ -> assert false (* FIXME *)
    | Th_theory(id,th) -> env, mc_bind_theory (EcPath.extend path id) th mc
    | Th_export p      -> assert false (* FIXME *)
    | Th_use    p      -> mc_use env p, mc
  and mc_use_th env (path,th) = 
    let base = EcPath.basename path in
    if EcIdent.Sid.mem base env.mc_used_th then env
    else 
      let env, mc = mc_of_theory env path th in
      (* FIXME *)
      mc_bind_component env (EcPath.Pident base)  (lazy mc)
  and mc_use env path = 
    let th = lookup_p (fun mc -> mc.mc_theories) path env in 
    mc_use_th env (path, th)

  let bind_variable (scope, x) ty _env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Variable ty)
        (mc_bind_variable path ty mc)

  let bind_function (scope, x) fsig _env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Function fsig)
        (mc_bind_function path fsig mc)

  let bind_module (scope, x) tymod env mc =
    let comps = mc_of_module env tymod in
    let path  = EcPath.extend scope x in
      mc_history (path, MC_Module (tymod, comps))
        (mc_bind_module path tymod comps mc)

  let bind_modtype (scope, x) tymod _env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Modtype tymod)
        (mc_bind_modtype path tymod mc)

  let bind_typedecl (scope, x) tydecl _env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Typedecl tydecl)
        (mc_bind_typedecl path tydecl mc)

  let bind_op (scope, x) op _env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Operator op)
        (mc_bind_op path op mc)

  let bind_ax (scope, x) ax _env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Axiom ax)
        (mc_bind_ax path ax mc)

  let bind_theory (scope, x) th _env mc =
    let path  = EcPath.extend scope x in
    mc_history (path, MC_Theory th)
      (mc_bind_theory path th mc)

  let lookup_mc1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_components

  let lookup_variable1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_variables

  let lookup_function1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_functions

  let lookup_module1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_modules

  let lookup_modtype1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_modtypes

  let lookup_typedecl1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_typedecls

  let lookup_op1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_operators

  let lookup_all_op1 (name : symbol) (mc : mcomponents) =
    IM.allbyname name mc.mc_operators

  let lookup_ax1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_axioms

  let lookup_theory1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_theories

  let rec lookup_mc (qn : symbols) (mc : mcomponents) =
    match qn with
    | []         -> Some mc
    | name :: qn ->
        obind
          (lookup_mc1 name mc)
          (fun (_, mc) -> lookup_mc qn (Lazy.force mc))




end

(* -------------------------------------------------------------------- *)
let bind f x v env =
  { env with env_root = f (env.env_scope, x) v env env.env_root }

(* -------------------------------------------------------------------- *)
let lookup_mcomponents ((scope, id) : qsymbol) (env : env) =
  obind
    (MC.lookup_mc scope env.env_root)
    (MC.lookup_mc1 id)

(* -------------------------------------------------------------------- *)
module Var = struct
  type t = EcTypes.ty

  let bind x ty env =
    bind MC.bind_variable x ty env

  let bindall xtys env =
    List.fold_left
      (fun env (x, ty) -> bind x ty env)
      env xtys

  let lookup_p = 
    lookup_p (fun mc -> mc.mc_variables)

  let trylookup_p p mc = 
    try Some (lookup_p p mc) with _ -> None

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_variable1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)

  let exists x env = (trylookup x env <> None)
end

(* -------------------------------------------------------------------- *)
module Fun = struct
  type  t = funsig

  let bind x fsig env =
    bind MC.bind_function x fsig env

  let bindall xtys env =
    List.fold_left
      (fun env (x, ty) -> bind x ty env)
      env xtys

  let lookup_p = 
    lookup_p (fun mc -> mc.mc_functions)

  let trylookup_p p mc = 
    try Some (lookup_p p mc) with _ -> None

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
      (MC.lookup_function1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)

  let exists x env = (trylookup x env <> None)
end

(* -------------------------------------------------------------------- *)
module Ty = struct
  type t = tydecl

  let bind x tydecl env =
    bind MC.bind_typedecl x tydecl env

  let bindall xtys env =
    List.fold_left
      (fun env (x, tydecl) -> bind x tydecl env)
      env xtys

  let lookup_p = 
    lookup_p (fun mc -> mc.mc_typedecls)

  let trylookup_p p mc = 
    try Some (lookup_p p mc) with _ -> None

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_typedecl1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)

  let defined (name : EcPath.path) (env : env) =
    let name = EcPath.basename name in

    (* FIXME: refactor *)
    match IM.byident name env.env_root.mc_typedecls with
    | None -> false
    | Some (_, tydecl) -> tydecl.tyd_type <> None

  let unfold (name : EcPath.path) (args : EcTypes.ty list) (env : env) =
    match trylookup_p name env with
    | None
    | Some { tyd_type = None } -> assert false
    | Some ({ tyd_type = Some body } as tyd) ->
        EcTypes.inst_var (EcTypes.init_substvar tyd.tyd_params args) body

  let exists x env = (trylookup x env <> None)
end

(* -------------------------------------------------------------------- *)
module Op = struct
  type t = operator

  let bind x operator env =
    bind MC.bind_op x operator env

  let bindall ops env =
    List.fold_left
      (fun env (x, tydecl) -> bind x tydecl env)
      env ops

  let lookup_p = 
    lookup_p (fun mc -> mc.mc_operators)

  let trylookup_p p mc = 
    try Some (lookup_p p mc) with _ -> None

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_op1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)

  let all ((scope, id) : qsymbol) env =
    odfl []
      (omap
         (MC.lookup_mc scope env.env_root)
         (MC.lookup_all_op1 id))

  let exists x env = (trylookup x env <> None)
end

(* -------------------------------------------------------------------- *)


(* -------------------------------------------------------------------- *)
module Ax = struct
  type t = axiom

  let bind x axiom env =
    bind MC.bind_ax x axiom env

  let bindall axs env =
    List.fold_left
      (fun env (x, ax) -> bind x ax env)
      env axs

  let lookup_p = 
    lookup_p (fun mc -> mc.mc_axioms)

  let trylookup_p p mc = 
    try Some (lookup_p p mc) with _ -> None

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_ax1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)

  let exists x env = (trylookup x env <> None)
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  type t = tymod

  let bind x tymod env =
    bind MC.bind_module x tymod env

  let bindall xtys env =
    List.fold_left
      (fun env (x, tymod) -> bind x tymod env)
      env xtys

  let lookup_p = 
    lookup_p (fun mc -> mc.mc_modules)

  let trylookup_p p mc = 
    try Some (lookup_p p mc) with _ -> None


  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_module1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)

  let exists x env = (trylookup x env <> None)
end

(* -------------------------------------------------------------------- *)
module ModTy = struct
  type t = tymod

  let bind x tymod env =
    bind MC.bind_modtype x tymod env

  let bindall xtys env =
    List.fold_left
      (fun env (x, tymod) -> bind x tymod env)
      env xtys

  let lookup_p = 
    lookup_p (fun mc -> mc.mc_modtypes)

  let trylookup_p p mc = 
    try Some (lookup_p p mc) with _ -> None

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_modtype1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)

  let exists x env = (trylookup x env <> None)
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  type t = theory

  let bind x th env =
    bind MC.bind_theory x th env

  let bindall xtys env =
    List.fold_left
      (fun env (x, tymod) -> bind x tymod env)
      env xtys

  let lookup_p = 
    lookup_p (fun mc -> mc.mc_theories)

  let trylookup_p p mc = 
    try Some (lookup_p p mc) with _ -> None

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_theory1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)

  let use path env = MC.mc_use env path

  let use_qs qs env = 
    let (path, _ as pth) = lookup qs env in
    path, MC.mc_use_th env pth

  (* FIXME *)
  let import (qs : qsymbol) (env : env) =
    let path, _ = lookup qs env in
    let mc1 = env.env_root in
    let mc2 = Lazy.force (MC.lookup_mc_p 
                            (EcPath.Pident (EcPath.basename path)) env) in
    let mc = 
      { mc_variables  = IM.merge mc1.mc_variables mc2.mc_variables;
        mc_functions  = IM.merge mc1.mc_functions mc2.mc_functions;
        mc_modules    = IM.merge mc1.mc_modules mc2.mc_modules;
        mc_modtypes   = IM.merge mc1.mc_modtypes mc2.mc_modtypes;
        mc_typedecls  = IM.merge mc1.mc_typedecls mc2.mc_typedecls;
        mc_operators  = IM.merge mc1.mc_operators mc2.mc_operators;
        mc_axioms     = IM.merge mc1.mc_axioms mc2.mc_axioms;
        mc_theories   = IM.merge mc1.mc_theories mc2.mc_theories;
        mc_components = IM.merge mc1.mc_components mc2.mc_components;
        mc_history    = (path, MC_import path) :: mc1.mc_history } in
    { env with env_root = mc }

  let exists x env = (trylookup x env <> None)

end

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of EcTypes.ty
  | `Function  of funsig
  | `Operator  of operator
  | `Module    of tymod
  | `ModType   of tymod
  | `TypeDecl  of tydecl
  | `Theory    of theory
]

let bind1 ((x, eb) : EcIdent.t * ebinding) (env : env) =
  match eb with
  | `Variable ty -> Var   .bind x ty env
  | `Function f  -> Fun   .bind x f  env
  | `Operator o  -> Op    .bind x o  env
  | `Module   m  -> Mod   .bind x m  env
  | `ModType  i  -> ModTy .bind x i  env
  | `TypeDecl t  -> Ty    .bind x t  env
  | `Theory   t  -> Theory.bind x t  env

let bindall (items : (EcIdent.t * ebinding) list) (env : env) =
  List.fold_left ((^~) bind1) env items

(* -------------------------------------------------------------------- *)
module Ident = struct
  type idlookup_t = [`Var | `Ctnt of operator]

  let trylookup (name : qsymbol) (env : env) =
    let for_var () =
      match Var.trylookup name env with
      | None -> None
      | Some (p, ty) -> Some (p, Some ty, (`Var :> idlookup_t))

    and for_op () =
      match Op.trylookup name env with
      | None -> None
      | Some (_, op) when not (op_ctnt op) -> None
      | Some (p, op) -> Some (p, op.op_codom, (`Ctnt op :> idlookup_t))
    in
      List.fpick [for_var; for_op]

  let lookup (name : qsymbol) (env : env) =
    match trylookup name env with
    | None   -> raise LookupFailure
    | Some x -> x
end
