(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcDecl
open EcTypesmod

(* -------------------------------------------------------------------- *)
type scope = EcPath.path option

type env = {
  env_scope : EcPath.path option;
  env_root  : mcomponents;
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
| MC_Theory    of EcTypesmod.theory * (mcomponents Lazy.t)

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
    env_root  = emcomponents; }

(* -------------------------------------------------------------------- *)
let root (env : env) = env.env_scope

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

  val bind      : EcIdent.t -> t -> env -> env
  val bindall   : (EcIdent.t * t) list -> env -> env
  val lookup    : qsymbol -> env -> EcPath.path * t
  val trylookup : qsymbol -> env -> (EcPath.path * t) option
end

(* -------------------------------------------------------------------- *)
module MC = struct
  module IM = EcIdent.Map

  let mc_history mitem mc =
    { mc with mc_history = mitem :: mc.mc_history }

  let mc_bind_variable path ty mc =
    let x = EcPath.basename path in
      { mc with
          mc_variables = IM.add x (path, ty) mc.mc_variables; }

  and mc_bind_function path fsig mc =
    let x = EcPath.basename path in
      { mc with
          mc_functions = IM.add x (path, fsig) mc.mc_functions; }

  and mc_bind_module path tymod comps mc =
    let x = EcPath.basename path in
      { mc with
          mc_modules    = IM.add x (path, tymod) mc.mc_modules;
          mc_components = IM.add x (path, comps) mc.mc_components; }

  and mc_bind_modtype path tymod mc =
    let x = EcPath.basename path in
      { mc with
          mc_modtypes = IM.add x (path, tymod) mc.mc_modtypes; }

  and mc_bind_typedecl path tydecl mc =
    let x = EcPath.basename path in
      { mc with
          mc_typedecls = IM.add x (path, tydecl) mc.mc_typedecls; }

  and mc_bind_op path op mc =
    let x = EcPath.basename path in
      { mc with
          mc_operators = IM.add x (path, op) mc.mc_operators; }

  and mc_bind_ax path ax mc =
    let x = EcPath.basename path in
      { mc with
          mc_axioms  = IM.add x (path, ax) mc.mc_axioms; }

  and mc_bind_theory path th comps mc =
    let x = EcPath.basename path in
      { mc with
          mc_theories   = IM.add x (path, th) mc.mc_theories;
          mc_components = IM.add x (path, comps) mc.mc_components; }

  let rec mc_of_module (_env : env) (_ : tymod) =
    lazy (failwith "")

  and mc_of_theory =
    let mc_of_theory scope (env : env) (th : theory) =
      let mc_of_theory_item mc = function
        | Th_type      (x, tydecl) -> bind_typedecl (scope, x) tydecl env mc
        | Th_operator  (x, op)     -> bind_op       (scope, x) op env mc
        | Th_axiom     (x, a)      -> bind_ax       (scope, x) a env mc
        | Th_modtype   (x, tymod)  -> bind_modtype  (scope, x) tymod env mc
        | Th_module    m           -> bind_module   (scope, m.me_name) m.me_sig env mc
        | Th_theory    (x, th)     -> bind_theory   (scope, x) th env mc
      in
        List.fold_left mc_of_theory_item emcomponents th
    in
      fun scope env th -> lazy (mc_of_theory scope env th)

  and bind_variable (scope, x) ty _env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Variable ty)
        (mc_bind_variable path ty mc)

  and bind_function (scope, x) fsig _env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Function fsig)
        (mc_bind_function path fsig mc)

  and bind_module (scope, x) tymod env mc =
    let comps = mc_of_module env tymod in
    let path  = EcPath.extend scope x in
      mc_history (path, MC_Module (tymod, comps))
        (mc_bind_module path tymod comps mc)

  and bind_modtype (scope, x) tymod env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Modtype tymod)
        (mc_bind_modtype path tymod mc)

  and bind_typedecl (scope, x) tydecl env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Typedecl tydecl)
        (mc_bind_typedecl path tydecl mc)

  and bind_op (scope, x) op env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Operator op)
        (mc_bind_op path op mc)

  and bind_ax (scope, x) ax env mc =
    let path = EcPath.extend scope x in
      mc_history (path, MC_Axiom ax)
        (mc_bind_ax path ax mc)

  and bind_theory (scope, x) th env mc =
    let comps = mc_of_theory (Some (EcPath.extend scope x)) env th in
    let path  = EcPath.extend scope x in
      mc_history (path, MC_Theory (th, comps))
        (mc_bind_theory path th comps mc)

  let bind_mcitem (path, mitem) mc =
      match mitem with
      | MC_Variable  ty          -> mc_bind_variable path ty mc
      | MC_Function  fsig        -> mc_bind_function path fsig mc
      | MC_Module    (m, submc)  -> mc_bind_module path m submc mc
      | MC_Modtype   tymod       -> mc_bind_modtype path tymod mc
      | MC_Typedecl  tydecl      -> mc_bind_typedecl path tydecl mc
      | MC_Operator  op          -> mc_bind_op path op mc
      | MC_Axiom     ax          -> mc_bind_ax path ax mc
      | MC_Theory    (th, submc) -> mc_bind_theory path th submc mc

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

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_variable1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
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

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
      (MC.lookup_function1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
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
    match EcIdent.Map.byident name env.env_root.mc_typedecls with
    | None -> false
    | Some (_, tydecl) -> tydecl.tyd_type <> None

  let unfold (name : EcPath.path) (args : EcTypes.ty list) (env : env) =
    let name = EcPath.basename name in

    match EcIdent.Map.byident name env.env_root.mc_typedecls with
    | None
    | Some (_, { tyd_type = None }) -> assert false
    | Some (_, ({ tyd_type = Some body } as tyd)) ->
        EcTypes.inst_var (EcTypes.init_substvar tyd.tyd_params args) body
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
end

(* -------------------------------------------------------------------- *)
(*module Pred = struct
  type t = predicate

  let bind x pred env =
    bind MC.bind_pred x pred env

  let bindall preds env =
    List.fold_left
      (fun env (x, tydecl) -> bind x tydecl env)
      env preds

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_pred1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
end*)

(* -------------------------------------------------------------------- *)
module Ax = struct
  type t = axiom

  let bind x axiom env =
    bind MC.bind_ax x axiom env

  let bindall axs env =
    List.fold_left
      (fun env (x, ax) -> bind x ax env)
      env axs

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_ax1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
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

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_module1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
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

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_modtype1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
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

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_theory1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)

  let import ((scope, id) : qsymbol) (env : env) =
    match EcIdent.Map.byident
             (EcPath.basename (fst (lookup (scope, id) env)))
             env.env_root.mc_components
    with
    | None    -> raise LookupFailure
    | Some mc ->
        let mc = Lazy.force (snd mc) in
          { env with
              env_root =
                List.fold_left
                  ((^~) MC.bind_mcitem) env.env_root mc.mc_history }
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
