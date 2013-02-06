(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcTypes
open EcFol
open EcDecl
open EcTypesmod
open EcWhy3

module IM  = EcIdent.Map
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
type lookup_failure = [
  | `Path    of EcPath.path
  | `QSymbol of qsymbol
]

exception LookupFailure of lookup_failure

let try_lf (f : unit -> 'a) =
  try Some (f ()) with LookupFailure _ -> None

(* -------------------------------------------------------------------- *)
type ctheory_w3 = {
  cth3_rebind : EcWhy3.rebinding;
  cth3_theory : ctheory;
}

let ctheory_of_ctheory_w3 (cth : ctheory_w3) =
  cth.cth3_theory

(* -------------------------------------------------------------------- *)
type varbind = {
  vb_type  : EcTypes.ty;
  vb_kind  : EcTypes.pvar_kind option;
}

type preenv = {
  env_scope  : EcPath.path;
  env_root   : premc;
  env_comps  : (EcPath.path * premc) Mid.t;
  env_w3     : EcWhy3.env;
  env_rb     : EcWhy3.rebinding;        (* in reverse order *)
  env_item   : ctheory_item list        (* in reverse order *)
}

and premc = {
  mc_variables  : (EcPath.path * varbind)                IM.t;
  mc_functions  : (EcPath.path * EcTypesmod.funsig)      IM.t;
  mc_modules    : (EcPath.path * EcTypesmod.module_expr) IM.t;
  mc_modtypes   : (EcPath.path * EcTypesmod.module_sig)  IM.t;
  mc_typedecls  : (EcPath.path * EcDecl.tydecl)          IM.t;
  mc_operators  : (EcPath.path * EcDecl.operator)        IM.t;
  mc_axioms     : (EcPath.path * EcDecl.axiom)           IM.t;
  mc_theories   : (EcPath.path * ctheory)                IM.t;
  mc_components : unit IM.t;
}

(* -------------------------------------------------------------------- *)
type env = preenv
type mcomponents = premc

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
}

(* -------------------------------------------------------------------- *)
let empty =
  let path = EcPath.Pident EcCoreLib.id_top
  and name = EcCoreLib.id_top in
  let env  =
    { env_scope = path;
      env_root  = { emcomponents with mc_components = IM.add name () IM.empty };
      env_comps = Mid.add name (path, emcomponents) Mid.empty;
      env_w3    = EcWhy3.empty;
      env_rb    = [];
      env_item  = [];
    }
  in 
    env

(* -------------------------------------------------------------------- *)
let preenv (env : preenv) : env = env

(* -------------------------------------------------------------------- *)
let root (env : env) = env.env_scope

(* -------------------------------------------------------------------- *)
module type S = sig
  type t

  val bind              : EcIdent.t -> t -> env -> env
  val bindall           : (EcIdent.t * t) list -> env -> env
  val lookup_by_path    : EcPath.path -> env -> t        (* full path *)
  val trylookup_by_path : EcPath.path -> env -> t option (* full path *)
  val lookup            : qsymbol -> env -> EcPath.path * t
  val lookup_path       : qsymbol -> env -> EcPath.path 
  val trylookup         : qsymbol -> env -> (EcPath.path * t) option
  val exists            : qsymbol -> env -> bool
  val add               : path    -> env -> env
end

(* -------------------------------------------------------------------- *)
module MC = struct
  (* ------------------------------------------------------------------ *)
  let lookup_mc_by_path =
    let rec lookup1 (env : env) (mc : mcomponents) (x : EcIdent.t) =
      match IM.byident x mc.mc_components with
      | None   -> None
      | Some _ -> omap (Mid.find_opt x env.env_comps) snd
    in
  
    let rec lookup env mc = function
      | Pident x      -> lookup1 env mc x
      | Pqname (p, x) -> obind (lookup env mc p) ((lookup1 env)^~ x)
    in
      fun env mc path -> lookup env mc path
  
  let lookup_by_path proj (path : EcPath.path) (env : env) = 
    let mc =
      match path with
      | Pident _      -> Some env.env_root
      | Pqname (p, _) -> lookup_mc_by_path env env.env_root p
    in
  
    let bname = EcPath.basename path in
    let obj   = obind mc (fun mc -> IM.byident bname (proj mc)) in
  
      match obj with
      | None        -> raise (LookupFailure (`Path path))
      | Some (p, x) -> assert (p = path); x

  (* ------------------------------------------------------------------ *)
  let rec lookup_mc (env : env) (qn : symbols) (mc : mcomponents) =
    match qn with
    | [] -> Some mc
    | name :: qn -> begin
      match IM.byname name mc.mc_components with
      | None -> None
      | Some (x, _) ->
          obind
            (Mid.find_opt x env.env_comps)
            (fun (_, mc) -> lookup_mc env qn mc)
    end

  let lookup proj ((qn, x) : qsymbol) (env : env) =
    match
      obind
        (lookup_mc env qn env.env_root)
        (fun mc -> IM.byname x (proj mc))
    with
    | None   -> raise (LookupFailure (`QSymbol (qn, x)))
    | Some x -> snd x

  let lookupall proj ((qn, x) : qsymbol) (env : env) =
    odfl []
      (omap
         (lookup_mc env qn env.env_root)
         (fun mc -> List.map snd (IM.allbyname x (proj mc))))

  (* ------------------------------------------------------------------ *)
  let mc_bind_variable path ty mc =
    let x = EcPath.basename path in
      { mc with
          mc_variables = IM.add x (path, ty) mc.mc_variables; }

  let mc_bind_function path fsig mc =
    let x = EcPath.basename path in
      { mc with
          mc_functions = IM.add x (path, fsig) mc.mc_functions; }

  let mc_bind_module path me mc =
    let x = EcPath.basename path in
      { mc with
          mc_modules = IM.add x (path, me) mc.mc_modules; }

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
          mc_axioms = IM.add x (path, ax) mc.mc_axioms; }

  let mc_bind_theory path th mc =
    let x = EcPath.basename path in
      { mc with
          mc_theories = IM.add x (path, th) mc.mc_theories; }

  let mc_bind_comp path mc =
    let x = EcPath.basename path in
      { mc with mc_components = IM.add x () mc.mc_components }

  let mc_of_module (env : env) (me : module_expr) =
    let xpath =
      let scope = EcPath.Pqname (env.env_scope, me.me_name) in
        fun x -> EcPath.Pqname (scope, x)
    in

    let mc1_of_module (mc : premc) = function
      | MI_Module _me ->
          mc                            (* FIXME *)

      | MI_Variable v ->
          let vty = {
            vb_type = v.v_type;
            vb_kind = Some PVglob;
          }
          in
            mc_bind_variable (xpath v.v_name) vty mc

      | MI_Function _f ->
          mc                            (* FIXME *)
    in
      List.fold_left mc1_of_module emcomponents me.me_comps

  (* ------------------------------------------------------------------ *)
  let bind env binder name obj =
    let path   = EcPath.Pqname (env.env_scope, name) in
    let comps  =
      Mid.change
        (fun o -> omap o (snd_map (binder path obj)))
        (EcPath.basename env.env_scope)
        env.env_comps
    in
      { env with
          env_root  = binder path obj env.env_root;
          env_comps = comps; }

  (* -------------------------------------------------------------------- *)
  let import env binder path obj =
    { env with
        env_root = binder path obj env.env_root; }

  (* -------------------------------------------------------------------- *)
  let bind_mc env name comps =
    let path = EcPath.Pqname (env.env_scope, name) in
    let env  =
      { env with
        env_root  = mc_bind_comp path env.env_root;
        env_comps = 
          Mid.change
            (fun o -> omap o (snd_map (mc_bind_comp path)))
            (EcPath.basename env.env_scope)
            env.env_comps; }
    in
    { env with                        (* FIXME: dup *)
        env_comps = Mid.add name (path, comps) env.env_comps }

  (* ------------------------------------------------------------------ *)
  let rec bind_variable x ty env =
    bind env mc_bind_variable x ty

  and bind_function x fsig env =
    bind env mc_bind_function x fsig

  and bind_module x me env =
    let comps = mc_of_module env me in
    let env   = bind env mc_bind_module x me in
    let env   = bind_mc env x comps in
      env

  and bind_modtype x tymod env =
    bind env mc_bind_modtype x tymod

  and bind_typedecl x tydecl env =
    bind env mc_bind_typedecl x tydecl

  and bind_op x op env =
    bind env mc_bind_op x op

  and bind_ax x ax env =
    bind env mc_bind_ax x ax

  and bind_theory x cth env =
    let env, comps = mc_of_ctheory env env.env_scope x cth in
    let env = bind env mc_bind_theory x cth in
    let env = bind_mc env x comps in
      env

  and mc_of_ctheory =
    let rec mc_of_ctheory_struct path (env, mc) = function 
      | CTh_type     (id, td)  -> env, mc_bind_typedecl (EcPath.Pqname (path, id)) td mc
      | CTh_operator (id, op)  -> env, mc_bind_op (EcPath.Pqname (path, id)) op mc
      | CTh_axiom    (id, ax)  -> env, mc_bind_ax (EcPath.Pqname (path, id)) ax mc
      | CTh_modtype  (id, tm)  -> env, mc_bind_modtype (EcPath.Pqname (path, id)) tm mc
      | CTh_module   m         -> env, mc_bind_module (EcPath.Pqname (path, m.me_name)) m mc
      | CTh_export   _         -> env, mc
      | CTh_theory   (id, cth) ->
          let env, submc =
            List.fold_left
              (mc_of_ctheory_struct (EcPath.Pqname (path, id)))
              (env, emcomponents) cth.cth_struct
          and subpath = EcPath.Pqname (path, id) in
  
          let env =
            let comps = env.env_comps in
            let comps = Mid.add id (subpath, submc) comps in
              { env with env_comps = comps }
          in
            (env, mc_bind_comp subpath (mc_bind_theory subpath cth mc))
    in
      fun (env : env) (path : EcPath.path) (x : EcIdent.t) (cth : ctheory) ->
        List.fold_left
          (mc_of_ctheory_struct (EcPath.Pqname (path, x)))
          (env, emcomponents)
          cth.cth_struct
end

(* -------------------------------------------------------------------- *)
let enter_id (name : EcIdent.t) (env : env) =
  let path = EcPath.Pqname (env.env_scope, name) in
  let env  = MC.bind_mc env name emcomponents in
    { env with
        env_scope = path;
        env_w3    = env.env_w3;
        env_rb    = [];
        env_item  = []; }

(* -------------------------------------------------------------------- *)
let enter (name : symbol) (env : env) =
  let name = EcIdent.create name in
  let env  = enter_id name env in
    (name, env)

(* -------------------------------------------------------------------- *)
module type Projector = sig
  type t

  val project : mcomponents -> (EcPath.path * t) EcIdent.Map.t
  val bind    : EcIdent.t -> t -> env -> env
  val rebind  : EcPath.path -> t -> premc -> premc
end

(* -------------------------------------------------------------------- *)
module BaseS(P : Projector) : S with type t = P.t = struct
  type t = P.t

  let bind = P.bind

  let bindall xtys env =
    List.fold_left
      (fun env (x, ty) -> bind x ty env)
      env xtys

  let lookup_by_path = 
    MC.lookup_by_path P.project

  let lookup =
    MC.lookup P.project

  let lookup_path qs env = fst (lookup qs env)

  let trylookup_by_path path env = 
    try_lf (fun () -> lookup_by_path path env)

  let trylookup x env =
    try_lf (fun () -> lookup x env)

  let exists x env = (trylookup x env <> None)

  let add p env = 
    let t = lookup_by_path p env in 
    MC.import env P.rebind p t 
    
end

(* -------------------------------------------------------------------- *)
module Var = struct
  include BaseS(struct
    type t = varbind

    let project mc = mc.mc_variables
    let bind = MC.bind_variable
    let rebind = MC.mc_bind_variable 
  end)

  let bind (x : EcIdent.t) (ty : EcTypes.ty) kind (env : env) =
    let vb = { vb_type = ty; vb_kind = kind } in
      bind x vb env

  let bindall xtys kind (env : env) =
    List.fold_left
      (fun env (x, ty) -> bind x ty kind env)
      env xtys

  let trylookup_local s env = 
    match trylookup ([],s) env with
    | Some(p,k) when k.vb_kind = None -> (Some (EcPath.basename p, k.vb_type))
    | _ -> None 

  let trylookup_pv qs env = 
    match trylookup qs env with
    | Some(p,{vb_kind = Some k; vb_type = ty}) ->
        Some ({pv_name = p; pv_kind = k}, ty)
    | _ -> None 
  
  let all_pv qname env = 
    let test (p,k) = 
      match k.vb_kind with
      | None -> None
      | Some k' -> Some ({ pv_name = p; pv_kind = k'}, k.vb_type) in
    List.pmap test 
      (MC.lookupall (fun mc -> mc.mc_variables) qname env)

end

(* -------------------------------------------------------------------- *)
module Fun = struct
  include BaseS(struct
    type t = funsig

    let project mc = mc.mc_functions
    let bind = MC.bind_function
    let rebind = MC.mc_bind_function
  end)
end

(* -------------------------------------------------------------------- *)
module Ty = struct
  include BaseS(struct
    type t = tydecl

    let project mc = mc.mc_typedecls

    let bind id t env = 
      let env = MC.bind_typedecl id t env in
      let w3, r = 
        EcWhy3.add_ty env.env_w3
          (EcPath.extend (Some env.env_scope) id) t
      in
        { env with
            env_w3   = w3;
            env_rb   = r::env.env_rb;
            env_item = CTh_type(id, t) :: env.env_item }

    let rebind = MC.mc_bind_typedecl
  end)

  let rebind = MC.bind_typedecl

  let defined (name : EcPath.path) (env : env) =
    match trylookup_by_path name env with
    | Some { tyd_type = Some _ } -> true
    | _ -> false

  let unfold (name : EcPath.path) (args : EcTypes.ty list) (env : env) =
    match trylookup_by_path name env with
    | Some ({ tyd_type = Some body} as tyd) ->
        EcTypes.Tvar.subst (EcTypes.Tvar.init tyd.tyd_params args) body
    | _ -> raise (LookupFailure (`Path name))
end

(* -------------------------------------------------------------------- *)
module Op = struct
  include BaseS(struct
    type t = operator

    let project mc = mc.mc_operators

    let bind id op env = 
      let env = MC.bind_op id op env in
      let w3, r = 
        EcWhy3.add_op env.env_w3 (EcPath.extend (Some env.env_scope) id) op
      in
        { env with
            env_w3   = w3;
            env_rb   = r :: env.env_rb;
            env_item = CTh_operator(id, op) :: env.env_item }

    let rebind = MC.mc_bind_op
  end)

  let rebind = MC.bind_op

  (* Use only for the && || ... *)
  let bind_logical id op env = 
    let env = MC.bind_op id op env in
      { env with
          env_item = CTh_operator(id, op) :: env.env_item }
    
  let all filter (qname : qsymbol) (env : env) =
    List.filter (fun (_,op) -> filter op)
      (MC.lookupall (fun mc -> mc.mc_operators) qname env)
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  include BaseS(struct
    type t = axiom

    let project mc = mc.mc_axioms
    let bind id ax env = 
      let env = MC.bind_ax id ax env in
      let w3, r = 
        EcWhy3.add_ax env.env_w3 (EcPath.extend (Some env.env_scope) id) ax
      in
        { env with
            env_w3   = w3;
            env_rb   = r :: env.env_rb;
            env_item = CTh_axiom(id, ax) :: env.env_item }
    let rebind = MC.mc_bind_ax

  end)
  let rebind = MC.bind_ax

  let instanciate p tys env = 
    match trylookup_by_path p env with
    | Some ({ ax_spec = Some f} as ax) ->
        Fsubst.subst_tvar (EcTypes.Tvar.init ax.ax_params tys) f
    | _ -> raise (LookupFailure (`Path p))
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  type t = module_expr

  let project mc = mc.mc_modules

  let bind_s = MC.bind_module

  let bindall_s xtys env =
    List.fold_left
      (fun env (x, ty) -> bind_s x ty env)
      env xtys

  let bind id m env = 
    assert (EcIdent.id_equal id m.me_name);
    let env = MC.bind_module id m env in
      { env with
          env_item = CTh_module m :: env.env_item }
      
  let bindall xtys env =
    List.fold_left
      (fun env (x, ty) -> bind x ty env)
      env xtys

  let lookup_by_path = 
    MC.lookup_by_path project

  let lookup =
    MC.lookup project

  let lookup_path qs env = fst (lookup qs env)

  let trylookup_by_path path env = 
    try_lf (fun () -> lookup_by_path path env)

  let trylookup x env =
    try_lf (fun () -> lookup x env)

  let exists x env = (trylookup x env <> None)  

  let add p env = 
    let t = lookup_by_path p env in 
    MC.import env MC.mc_bind_module p t 

end

(* -------------------------------------------------------------------- *)
module ModTy = struct
  include BaseS(struct
    type t = module_sig

    let project mc = mc.mc_modtypes
    let bind id mt env = 
      let env = MC.bind_modtype id mt env in
        { env with
            env_item = CTh_modtype(id, mt) :: env.env_item }
    let rebind = MC.mc_bind_modtype
  end)
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  type t = ctheory_w3

  (* -------------------------------------------------------------------- *)
  let rec ctheory_of_theory =
      fun th ->
        let items = List.map ctheory_item_of_theory_item th in
          { cth_desc = CTh_struct items; cth_struct = items; }

  and ctheory_item_of_theory_item = function
    | Th_type      (x, ty) -> CTh_type     (x, ty)
    | Th_operator  (x, op) -> CTh_operator (x, op)
    | Th_axiom     (x, ax) -> CTh_axiom    (x, ax)
    | Th_modtype   (x, mt) -> CTh_modtype  (x, mt)
    | Th_module    m       -> CTh_module   m
    | Th_theory    (x, th) -> CTh_theory   (x, ctheory_of_theory th)
    | Th_export    name    -> CTh_export   name

  (* ------------------------------------------------------------------ *)
  let enter = enter

  (* ------------------------------------------------------------------ *)
  let bind id cth env =
    let env = MC.bind_theory id cth.cth3_theory env in
      { env with
          env_w3   = EcWhy3.rebind env.env_w3 cth.cth3_rebind;
          env_rb   = List.rev_append cth.cth3_rebind env.env_rb;
          env_item = (CTh_theory (id, cth.cth3_theory)) :: env.env_item; }

  (* ------------------------------------------------------------------ *)
  let rebind = MC.bind_theory
    
  (* ------------------------------------------------------------------ *)
  let bindall xtys env =
    List.fold_left
      (fun env (x, ty) -> bind x ty env)
      env xtys
      
  (* ------------------------------------------------------------------ *)
  let lookup_by_path =
    MC.lookup_by_path (fun mc -> mc.mc_theories)
      
  (* ------------------------------------------------------------------ *)
  let lookup =
    MC.lookup (fun mc -> mc.mc_theories)
 
  let lookup_path qs env = fst (lookup qs env)
      
  (* ------------------------------------------------------------------ *)
  let trylookup_by_path path env = 
    try_lf (fun () -> lookup_by_path path env)
      
  (* ------------------------------------------------------------------ *)
  let trylookup x env =
    try_lf (fun () -> lookup x env)

  (* ------------------------------------------------------------------ *)
  let exists x env = (trylookup x env <> None)

  (* ------------------------------------------------------------------ *)
  let import (path : EcPath.path) (env : env) =
    let rec import (env : env) path (cth : ctheory) =
      let xpath x = EcPath.Pqname (path, x) in
      let rec import_cth_item (env : env) = function
        | CTh_type (x, ty) ->
            MC.import env MC.mc_bind_typedecl (xpath x) ty

        | CTh_operator (x, op) ->
            MC.import env MC.mc_bind_op (xpath x) op

        | CTh_axiom (x, ax) ->
            MC.import env MC.mc_bind_ax (xpath x) ax

        | CTh_modtype (x, ty) ->
            MC.import env MC.mc_bind_modtype (xpath x) ty

        | CTh_module m -> 
            MC.import env MC.mc_bind_module (xpath m.me_name) m

        | CTh_export p ->
            import env p (lookup_by_path p env)

        | CTh_theory (x, th) ->
            let env = MC.import env MC.mc_bind_theory (xpath x) th in
              { env with env_root = MC.mc_bind_comp (xpath x) env.env_root }
      in
        List.fold_left import_cth_item env cth.cth_struct

    in
      import env path (lookup_by_path path env)

  (* ------------------------------------------------------------------ *)
  let export (path : EcPath.path) (env : env) =
    let env = import path env in
      { env with
          env_item = CTh_export path :: env.env_item }

  (* ------------------------------------------------------------------ *)
  let close env = 
    let theory =
      let items = List.rev env.env_item in
        { cth_desc   = CTh_struct items;
          cth_struct = items; }
    in
      { cth3_rebind = List.rev env.env_rb;
        cth3_theory = theory; }

  (* ------------------------------------------------------------------ *)
  let require x cth env =
    let rootnm = EcPath.rootname env.env_scope in
    let thpath = EcPath.Pqname (EcPath.Pident rootnm, x) in

    let env, thmc =
      MC.mc_of_ctheory env (EcPath.Pident rootnm) x cth.cth3_theory
    in

    let topmc = snd (Mid.find rootnm env.env_comps) in
    let topmc = {
      topmc with
        mc_theories   = IM.add x (thpath, cth.cth3_theory) topmc.mc_theories;
        mc_components = IM.add x () topmc.mc_components; }
    in

    let root = {
      env.env_root with
        mc_theories   = IM.add x (thpath, cth.cth3_theory) topmc.mc_theories;
        mc_components = IM.add x () env.env_root.mc_components; }
    in

    let comps = env.env_comps in
    let comps = Mid.add rootnm (EcPath.Pident rootnm, topmc) comps in
    let comps = Mid.add x (thpath, thmc) comps in

    { env with
        env_root  = root;
        env_comps = comps;
        env_w3    = EcWhy3.rebind env.env_w3 cth.cth3_rebind; }

  let add p env = 
    let th = lookup_by_path p env in
    MC.import env MC.mc_bind_theory p th
end

(* -------------------------------------------------------------------- *)
module Ident = struct

  type idlookup_t = 
    [ `Local of EcIdent.t
    | `Pvar of EcTypes.prog_var 
    | `Ctnt of EcPath.path * operator ]

  let trylookup filter_op (name : qsymbol) (env : env) =
    match Var.trylookup name env with
    | Some (p, x) ->
        let idl = 
          match x.vb_kind with
          | None   -> `Local (EcPath.basename p) 
          | Some k -> `Pvar { EcTypes.pv_name = p; EcTypes.pv_kind = k } in
        [ x.vb_type, (idl :> idlookup_t) ]
    | None ->
        let all = Op.all filter_op name env in
        List.map (fun p -> 
          let op = snd p in 
          let ty = EcTypes.toarrow op.op_dom op.op_codom in
          ty, (`Ctnt p :> idlookup_t) ) all

  let lookup filter_op (name : qsymbol) (env : env) =
    match trylookup filter_op name env with
    | [x] -> x
    | _ -> raise (LookupFailure (`QSymbol name))

end

(* -------------------------------------------------------------------- *)
let import_w3 env th rd = 
  let lth, rbi = EcWhy3.import_w3 env.env_w3 env.env_scope th rd in
  let cth = List.map Theory.ctheory_item_of_theory_item lth in

  let env = {
    env with
      env_w3   = EcWhy3.rebind env.env_w3 [rbi];
      env_rb   = rbi :: env.env_rb;
      env_item = List.rev_append cth env.env_item;
  }
  in

  let add env = function
    | Th_type     (id, ty) -> Ty.rebind id ty env
    | Th_operator (id, op) -> Op.rebind id op env
    | Th_axiom    (id, ax) -> Ax.rebind id ax env
    | Th_theory   (id, th) ->
        Theory.rebind id (Theory.ctheory_of_theory th) env
    | _ -> assert false
  in

  let env = List.fold_left add env lth in
    (env, cth)

(* -------------------------------------------------------------------- *)
let import_w3_dir env dir name rd =
  let th = EcWhy3.get_w3_th dir name in
    import_w3 env th rd 

(* -------------------------------------------------------------------- *)
let initial = 
  let env0 = empty in
  let env = enter_id EcCoreLib.id_pervasive env0 in
  let unit_rn = 
    let tunit = Why3.Ty.ts_tuple 0 in
    let nunit = tunit.Why3.Ty.ts_name.Why3.Ident.id_string in
    let tt = Why3.Term.fs_tuple 0 in
    let ntt = tt.Why3.Term.ls_name.Why3.Ident.id_string in
    [ [nunit],EcWhy3.RDts, EcPath.basename EcCoreLib.p_unit;
      [ntt], EcWhy3.RDls, EcPath.basename EcCoreLib.p_tt
    ]  in
  let env, _ = import_w3 env (Why3.Theory.tuple_theory 0) unit_rn in
  let builtin_rn = [
    ["int"]    , EcWhy3.RDts, EcPath.basename EcCoreLib.p_int;
    ["real"]   , EcWhy3.RDts, EcPath.basename EcCoreLib.p_real;
    ["infix ="], EcWhy3.RDls, EcPath.basename EcCoreLib.p_eq 
  ] in
  let env, _ = import_w3 env Why3.Theory.builtin_theory builtin_rn in
  let bool_rn = [
    ["bool"] , EcWhy3.RDts, EcPath.basename EcCoreLib.p_bool;
    ["True"] , EcWhy3.RDls, EcPath.basename EcCoreLib.p_true;
    ["False"], EcWhy3.RDls, EcPath.basename EcCoreLib.p_false ] in
  let env, _ = import_w3 env Why3.Theory.bool_theory bool_rn in
  let add_bool sign env path = 
    Op.bind_logical (EcPath.basename path) 
      (mk_op [] sign EcTypes.tbool None) env in
  let env = add_bool [EcTypes.tbool] env EcCoreLib.p_not in
  let env = List.fold_left (add_bool [EcTypes.tbool;EcTypes.tbool]) env
      [EcCoreLib.p_and; EcCoreLib.p_or; EcCoreLib.p_imp; EcCoreLib.p_iff] in
  let tdistr = { tyd_params = [ EcIdent.create "'a" ]; tyd_type = None } in
  let env = Ty.bind (EcPath.basename EcCoreLib.p_distr) tdistr env in 
  let cth = Theory.close env in
  let env1 = Theory.bind EcCoreLib.id_pervasive cth env0 in
  let env1 = Theory.import EcCoreLib.p_pervasive env1 in
  env1

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of EcTypes.pvar_kind option * EcTypes.ty
  | `Function  of funsig
  | `Module    of module_expr
  | `ModType   of module_sig
]

let bind1 ((x, eb) : EcIdent.t * ebinding) (env : env) =
  match eb with
  | `Variable v -> Var   .bind x (snd v) (fst v) env
  | `Function f -> Fun   .bind x f env
  | `Module   m -> Mod   .bind x m env
  | `ModType  i -> ModTy .bind x i env

let bindall (items : (EcIdent.t * ebinding) list) (env : env) =
  List.fold_left ((^~) bind1) env items  

(* -------------------------------------------------------------------- *)
let rec dump ?(name = "Environment") pp (env : env) =
    EcDebug.onseq pp name ~extra:(EcPath.tostring env.env_scope)
      (Stream.of_list [
        (fun pp -> dump_premc ~name:"Root" pp env.env_root);
        (fun pp ->
           Mid.dump ~name:"Components"
             (fun k (p, _) ->
                Printf.sprintf "%s (%s)"
                  (EcIdent.tostring k) (EcPath.tostring p))
             (fun pp (_, (_, mc)) ->
                dump_premc ~name:"Component" pp mc)
             pp env.env_comps)
      ])

and dump_premc ~name pp mc =
  EcDebug.onseq pp name
    (Stream.of_list [
       (fun pp -> IM.dump "Variables"  (fun _ _ -> ()) pp mc.mc_variables );
       (fun pp -> IM.dump "Functions"  (fun _ _ -> ()) pp mc.mc_functions );
       (fun pp -> IM.dump "Modules"    (fun _ _ -> ()) pp mc.mc_modules   );
       (fun pp -> IM.dump "Modtypes"   (fun _ _ -> ()) pp mc.mc_modtypes  );
       (fun pp -> IM.dump "Typedecls"  (fun _ _ -> ()) pp mc.mc_typedecls );
       (fun pp -> IM.dump "Operators"  (fun _ _ -> ()) pp mc.mc_operators );
       (fun pp -> IM.dump "Axioms"     (fun _ _ -> ()) pp mc.mc_axioms    );
       (fun pp -> IM.dump "Theories"   (fun _ _ -> ()) pp mc.mc_theories  );
       (fun pp -> IM.dump "Components" (fun _ _ -> ()) pp mc.mc_components);
    ])

(* -------------------------------------------------------------------- *)     
let rec equal_type env t1 t2 = 
  match t1, t2 with
  | Tunivar uid1, Tunivar uid2 -> EcUidgen.uid_equal uid1 uid2
      
  | Tvar i1, Tvar i2 -> i1 = i2
  | Ttuple lt1, Ttuple lt2 ->
      List.for_all2 (equal_type env) lt1 lt2
  | Tfun(t1,t2), Tfun(t1',t2') ->
      equal_type env t1 t1' && equal_type env t2 t2'
  | Tconstr(p1,lt1), Tconstr(p2,lt2) when EcPath.p_equal p1 p2 ->
      List.for_all2 (equal_type env) lt1 lt2 || 
      (Ty.defined p1 env &&
       equal_type env (Ty.unfold p1 lt1 env) (Ty.unfold p2 lt2 env))
  | Tconstr(p1,lt1), _ when Ty.defined p1 env ->
      equal_type env (Ty.unfold p1 lt1 env) t2
  | _, Tconstr(p2,lt2) when Ty.defined p2 env ->
      equal_type env t1 (Ty.unfold p2 lt2 env)
  | _, _ -> false

exception IncompatibleType of ty * ty

exception IncompatibleForm of form * form * form * form
  
let check_type env t1 t2 = 
  if not (equal_type env t1 t2) then raise (IncompatibleType(t1,t2))

let rec destr_tfun env tf = 
  match tf with
  | Tfun(ty1,ty2) -> ty1, ty2
  | Tconstr(p,tys) when Ty.defined p env ->
      destr_tfun env (Ty.unfold p tys env) 
  | _ -> assert false (* FIXME error message *)

let rec ty_fun_app env tf targs = 
  match targs with
  | [] -> tf
  | t1 :: targs ->
      let dom,codom = destr_tfun env tf in
      check_type env dom t1;
      ty_fun_app env codom targs

(* TODO : can be good to also add unfolding of globals and locals *)
let check_alpha_equal env f1 f2 = 
  let error f1' f2' = raise (IncompatibleForm(f1,f2,f1',f2')) in
  let find alpha id = try Mid.find id alpha with _ -> id in
  let check_lpattern f1 f2 alpha lp1 lp2 = 
    match lp1, lp2 with
    | LSymbol id1, LSymbol id2 -> Mid.add id1 id2 alpha
    | LTuple lid1, LTuple lid2 when List.length lid1 = List.length lid2 ->
        List.fold_left2 (fun alpha id1 id2 -> Mid.add id1 id2 alpha) 
          alpha lid1 lid2
    | _, _ -> error f1 f2 in
  let check_binding f1 f2 alpha bd1 bd2 =
    let check_one alpha (x1,ty1) (x2,ty2) = 
      if equal_type env ty1 ty2 then Mid.add x1 x2 alpha 
      else error f1 f2 in
    List.fold_left2 check_one alpha bd1 bd2 in 
  let rec aux alpha f1 f2 = 
    match f1.f_node, f2.f_node with
    | Fquant(q1,bd1,f1'), Fquant(q2,bd2,f2') when 
        q1 = q2 && List.length bd1 = List.length bd2 ->
          let alpha = check_binding f1 f2 alpha bd1 bd2  in
          aux alpha f1' f2'
    | Fif(a1,b1,c1), Fif(a2,b2,c2) ->
        aux alpha a1 a2; aux alpha b1 b2; aux alpha c1 c2
    | Flet(p1,f1',g1), Flet(p2,f2',g2) ->
        aux alpha f1' f2';
        let alpha = check_lpattern f1 f2 alpha p1 p2 in
        aux alpha g1 g2
    | Fint i1, Fint i2 when i1 = i2 -> ()
    | Flocal id1, Flocal id2 when EcIdent.id_equal (find alpha id1) id2 -> ()
    | Fpvar(p1,_,s1), Fpvar(p2,_,s2) when pv_equal p1 p2 && s1 = s2 -> ()
    | Fop(p1, _), Fop(p2, _) when EcPath.p_equal p1 p2 -> () 
    | Fapp(f1,args1), Fapp(f2,args2) ->
        aux alpha f1 f2;
        List.iter2 (aux alpha) args1 args2
    | Ftuple args1, Ftuple args2 when List.length args1 = List.length args2 ->
        List.iter2 (aux alpha) args1 args2 
    | _, _ -> error f1 f2 in
  aux Mid.empty f1 f2

let is_alpha_equal env f1 f2 = 
  try check_alpha_equal env f1 f2; true
  with _ -> false

let check_goal env pi ld = EcWhy3.check_goal env.env_w3 pi ld

(** {2 Type safe soft constructors} *)

type c_tyexpr = tyexpr

let ce_type (e : tyexpr) =
  (oget e.tye_meta).tym_type

let ce_meta ty e : c_tyexpr =
  { tye_meta = Some { tym_type = ty };
    tye_desc = e; }

let ce_local (env : env) (x : EcIdent.t) =
  (* Je pense que c'est pas une bonne idee d'avoir ce path on devrait
     avoir Pident x, je n'aime pas que le path depend du scope *)
  let xpath = EcPath.Pqname (env.env_scope, x) in
  let xty   = Var.lookup_by_path xpath env in
    if xty.vb_kind <> None then assert false;
    ce_meta xty.vb_type (Elocal x)

let ce_var (env : env) (p : prog_var) =
  let xty = Var.lookup_by_path p.pv_name env in
    if xty.vb_kind = None then assert false;
    ce_meta xty.vb_type (Evar p)

let ce_int (_env : env) (i : int) =
  ce_meta tint (Eint i)

let ce_tuple (_env : env) es =
  ce_meta
    (Ttuple (List.map ce_type es))
    (Etuple es)

let ce_let (_env : env) p e1 e2 =
  ce_meta (ce_type e2) (Elet (p, e1, e2))

let ce_if (env : env) c e1 e2 =
  check_type env (ce_type c) tbool;
  check_type env (ce_type e1) (ce_type e2);
  ce_meta (ce_type e1) (Eif (c, e1, e2))

let ce_app (_env : env) _p _e _ty =
  assert false                          (* FIXME *)
