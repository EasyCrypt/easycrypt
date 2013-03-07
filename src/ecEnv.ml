(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcTypes
open EcFol
open EcMemory
open EcDecl
open EcModules
open EcTheory
open EcWhy3

(* -------------------------------------------------------------------- *)
module Ssym = EcSymbols.Ssym
module Msym = EcSymbols.Msym
module Mp   = EcPath.Mp
module Mid  = EcIdent.Mid

(* -------------------------------------------------------------------- *)
type ctheory_w3 = {
  cth3_rebind : EcWhy3.rebinding;
  cth3_theory : ctheory;
}

let ctheory_of_ctheory_w3 (cth : ctheory_w3) =
  cth.cth3_theory

(* -------------------------------------------------------------------- *)
type 'a suspension = {
  sp_target : 'a;
  sp_params : (EcIdent.t * module_type) list list;
}

exception IsSuspended

let suspend (x : 'a) params =
  { sp_target = x;
    sp_params = params; }

let sp_target { sp_target = x } = x

let is_suspended (x : 'a suspension) =
  List.exists (fun ps -> ps <> []) x.sp_params

let check_not_suspended (x : 'a suspension) =
  if is_suspended x then raise IsSuspended;
  x.sp_target

let unsuspend f (x : 'a suspension) (args : mpath list list) =
  try
    let s =
      List.fold_left2
        (List.fold_left2
           (fun s (x, _) a -> EcSubst.add_module s x a))
        EcSubst.empty x.sp_params args
    in
    if EcSubst.is_empty s then x.sp_target 
    else f s x.sp_target
  with Invalid_argument "List.fold_left2" ->
    assert false

(* -------------------------------------------------------------------- *)
type lookup_failure = [
  | `Path    of path
  | `QSymbol of qsymbol
]

exception LookupFailure of lookup_failure
exception DuplicatedBinding of symbol

let try_lf (f : unit -> 'a) =
  try Some (f ()) with LookupFailure _ -> None

(* -------------------------------------------------------------------- *)
type okind = [
  | `Variable
  | `Function
  | `Theory
  | `Module
  | `ModType
  | `TypeDecls
  | `OpDecls
  | `Lemma
]

module Kinds = EcUtils.Flags(struct
  type flag = okind

  let toint = function
    | `Variable  -> 0
    | `Function  -> 1
    | `Theory    -> 2
    | `Module    -> 3
    | `ModType   -> 4
    | `TypeDecls -> 5
    | `OpDecls   -> 6
    | `Lemma     -> 7
end)

let ok_container = Kinds.fromlist [`Theory; `Module]
let ok_modvalue  = Kinds.fromlist [`Variable; `Function]

(* -------------------------------------------------------------------- *)
type varbind = {
  vb_type  : EcTypes.ty;
  vb_kind  : EcTypes.pvar_kind;
}

type preenv = {
  env_scope    : EcPath.mpath;
  env_current  : activemc;
  env_comps    : premc EcPath.Mp.t;
  env_locals   : (EcIdent.t * EcTypes.ty) MMsym.t;
  env_memories : (EcMemory.memory * EcMemory.memenv) MMsym.t;
  env_actmem   : EcMemory.memory option;
  env_w3       : EcWhy3.env;
  env_rb       : EcWhy3.rebinding;        (* in reverse order *)
  env_item     : ctheory_item list        (* in reverse order *)
}

and premc = {
  mc_parameters : (EcIdent.t * module_type)        list;
  mc_variables  : (mpath * varbind)                Msym.t;
  mc_functions  : (mpath * EcModules.function_)    Msym.t;
  mc_modules    : (mpath * EcModules.module_expr)  Msym.t;
  mc_modtypes   : (mpath * EcModules.module_sig)   Msym.t;
  mc_typedecls  : (mpath * EcDecl.tydecl)          Msym.t;
  mc_operators  : (mpath * EcDecl.operator)        Msym.t;
  mc_axioms     : (mpath * EcDecl.axiom)           Msym.t;
  mc_theories   : (mpath * ctheory)     Msym.t;
  mc_components : path                             Msym.t;
}

and activemc = {
  amc_variables  : (mpath * varbind)                MMsym.t;
  amc_functions  : (mpath * EcModules.function_)    MMsym.t;
  amc_modules    : (mpath * EcModules.module_expr)  MMsym.t;
  amc_modtypes   : (mpath * EcModules.module_sig)   MMsym.t;
  amc_typedecls  : (mpath * EcDecl.tydecl)          MMsym.t;
  amc_operators  : (mpath * EcDecl.operator)        MMsym.t;
  amc_axioms     : (mpath * EcDecl.axiom)           MMsym.t;
  amc_theories   : (mpath * ctheory)     MMsym.t;
  amc_components : path                             MMsym.t;
}

and mc =
| PreMc of premc
| ActMc of activemc

let premc = fun (mc : premc   ) -> PreMc mc
let actmc = fun (mc : activemc) -> ActMc mc

(* -------------------------------------------------------------------- *)
type env = preenv

(* -------------------------------------------------------------------- *)
let empty_premc = {
  mc_parameters = [];
  mc_variables  = Msym.empty;
  mc_functions  = Msym.empty;
  mc_modules    = Msym.empty;
  mc_modtypes   = Msym.empty;
  mc_typedecls  = Msym.empty;
  mc_operators  = Msym.empty;
  mc_axioms     = Msym.empty;
  mc_theories   = Msym.empty;
  mc_components = Msym.empty;
}

and empty_activemc = {
  amc_variables  = MMsym.empty;
  amc_functions  = MMsym.empty;
  amc_modules    = MMsym.empty;
  amc_modtypes   = MMsym.empty;
  amc_typedecls  = MMsym.empty;
  amc_operators  = MMsym.empty;
  amc_axioms     = MMsym.empty;
  amc_theories   = MMsym.empty;
  amc_components = MMsym.empty;
}

(* -------------------------------------------------------------------- *)
let empty =
  let path = EcPath.msymbol EcCoreLib.id_top
  and name = EcCoreLib.id_top in
  let env  =
    { env_scope    = path;
      env_current  = { empty_activemc with
                         amc_components = MMsym.add name
                           (EcPath.path_of_mpath path)
                           MMsym.empty; };
      env_comps    = Mp.singleton (EcPath.psymbol name) empty_premc;
      env_locals   = MMsym.empty;
      env_memories = MMsym.empty;
      env_actmem   = None;
      env_w3       = EcWhy3.empty;
      env_rb       = [];
      env_item     = [];
    }
  in
    env

(* -------------------------------------------------------------------- *)
let preenv (env : preenv) : env = env

(* -------------------------------------------------------------------- *)
let root (env : env) = EcPath.path_of_mpath env.env_scope

(* -------------------------------------------------------------------- *)
module Dump = struct
  let rec dump ?(name = "Environment") pp (env : env) =
      EcDebug.onseq pp name ~extra:(EcPath.m_tostring env.env_scope)
        (Stream.of_list [
          (fun pp -> dump_amc ~name:"Root" pp env.env_current);
          (fun pp ->
             Mp.dump ~name:"Components"
               (fun k _ -> EcPath.tostring k)
               (fun pp (_, mc) ->
                  dump_premc ~name:"Component" pp mc)
               pp env.env_comps)
        ])
  
  and dump_premc ~name pp mc =
    let ppkey_mpath _ (p, _) = EcPath.m_tostring p
    and ppkey_comps _ p      = EcPath.tostring    p

    and ppval _ _ = () in
  
    EcDebug.onseq pp name
      (Stream.of_list [
         (fun pp -> Msym.dump ~name:"Variables"  ppkey_mpath ppval pp mc.mc_variables );
         (fun pp -> Msym.dump ~name:"Functions"  ppkey_mpath ppval pp mc.mc_functions );
         (fun pp -> Msym.dump ~name:"Modules"    ppkey_mpath ppval pp mc.mc_modules   );
         (fun pp -> Msym.dump ~name:"Modtypes"   ppkey_mpath ppval pp mc.mc_modtypes  );
         (fun pp -> Msym.dump ~name:"Typedecls"  ppkey_mpath ppval pp mc.mc_typedecls );
         (fun pp -> Msym.dump ~name:"Operators"  ppkey_mpath ppval pp mc.mc_operators );
         (fun pp -> Msym.dump ~name:"Axioms"     ppkey_mpath ppval pp mc.mc_axioms    );
         (fun pp -> Msym.dump ~name:"Theories"   ppkey_mpath ppval pp mc.mc_theories  );
         (fun pp -> Msym.dump ~name:"Components" ppkey_comps ppval pp mc.mc_components);
      ])
  
  and dump_amc ~name pp mc =
    EcDebug.onseq pp name
      (Stream.of_list [
         (fun pp -> MMsym.dump "Variables"  (fun _ _ -> ()) pp mc.amc_variables );
         (fun pp -> MMsym.dump "Functions"  (fun _ _ -> ()) pp mc.amc_functions );
         (fun pp -> MMsym.dump "Modules"    (fun _ _ -> ()) pp mc.amc_modules   );
         (fun pp -> MMsym.dump "Modtypes"   (fun _ _ -> ()) pp mc.amc_modtypes  );
         (fun pp -> MMsym.dump "Typedecls"  (fun _ _ -> ()) pp mc.amc_typedecls );
         (fun pp -> MMsym.dump "Operators"  (fun _ _ -> ()) pp mc.amc_operators );
         (fun pp -> MMsym.dump "Axioms"     (fun _ _ -> ()) pp mc.amc_axioms    );
         (fun pp -> MMsym.dump "Theories"   (fun _ _ -> ()) pp mc.amc_theories  );
         (fun pp -> MMsym.dump "Components" (fun _ _ -> ()) pp mc.amc_components);
      ])
end

let dump = Dump.dump

(* -------------------------------------------------------------------- *)
module MC = struct
  let top_path = EcPath.psymbol EcCoreLib.id_top

  (* ------------------------------------------------------------------ *)

  (* Lookup container components using given path. Returns the container
   * components along all the components parameters in reverse order
   * (i.e. from bottom component to the top one) *)
  let rec lookup_mc_by_path (env : env) (p : EcPath.path) =
    let params = odfl [] (
      match EcPath.prefix p with
      | None        -> None
      | Some prefix -> omap (lookup_mc_by_path env prefix) snd)
    in
      match Mp.find_opt p env.env_comps with
      | None -> None

      | Some mc ->
          Some (mc, mc.mc_parameters :: params)

  (* Lookup object referenced by path [path]. If path is reduced
   * to an identifier, use <top> as the path prefix. [proj]
   * should project the final component to the desired objects
   * map. *)
  let lookup_by_path proj (path : EcPath.path) (env : env) =
    let symbol = EcPath.basename path
    and scname = odfl top_path (EcPath.prefix path) in
    let mc     = lookup_mc_by_path env scname in

      match mc with
      | None -> raise (LookupFailure (`Path path))
      | Some (mc, params) -> begin
          match Msym.find_opt symbol (proj mc) with
          | None        -> raise (LookupFailure (`Path path))
          | Some (_, x) -> suspend x params
      end

  (* ------------------------------------------------------------------ *)
  module Px = struct
    type 'a projector = {
      (* Selecting / updating in a [premc] *)
      px_premc   : premc -> (mpath * 'a) Msym.t;
      px_topremc : (mpath * 'a) Msym.t -> premc -> premc;

      (* Selecting / updating in a [activemc] *)
      px_actmc   : activemc -> (mpath * 'a) MMsym.t;
      px_toactmc : (mpath * 'a) MMsym.t -> activemc -> activemc;
    }

    (* ---------------------------------------------------------------- *)
    let for_variable : varbind projector = {
      px_premc   = (fun mc -> mc.mc_variables);
      px_topremc = (fun m mc -> { mc with mc_variables = m });
      px_actmc   = (fun mc -> mc.amc_variables);
      px_toactmc = (fun m mc -> { mc with amc_variables = m });
    }

    let for_function : EcModules.function_ projector = {
      px_premc   = (fun mc -> mc.mc_functions);
      px_topremc = (fun m mc -> { mc with mc_functions = m });
      px_actmc   = (fun mc -> mc.amc_functions);
      px_toactmc = (fun m mc -> { mc with amc_functions = m });
    }

    let for_module : EcModules.module_expr projector = {
      px_premc   = (fun mc -> mc.mc_modules);
      px_topremc = (fun m mc -> { mc with mc_modules = m });
      px_actmc   = (fun mc -> mc.amc_modules);
      px_toactmc = (fun m mc -> { mc with amc_modules = m });
    }

    let for_modtype : EcModules.module_sig projector = {
      px_premc   = (fun mc -> mc.mc_modtypes);
      px_topremc = (fun m mc -> { mc with mc_modtypes = m });
      px_actmc   = (fun mc -> mc.amc_modtypes);
      px_toactmc = (fun m mc -> { mc with amc_modtypes = m });
    }

    let for_typedecl : EcDecl.tydecl projector = {
      px_premc   = (fun mc -> mc.mc_typedecls);
      px_topremc = (fun m mc -> { mc with mc_typedecls = m });
      px_actmc   = (fun mc -> mc.amc_typedecls);
      px_toactmc = (fun m mc -> { mc with amc_typedecls = m });
    }

    let for_operator : EcDecl.operator projector = {
      px_premc   = (fun mc -> mc.mc_operators);
      px_topremc = (fun m mc -> { mc with mc_operators = m });
      px_actmc   = (fun mc -> mc.amc_operators);
      px_toactmc = (fun m mc -> { mc with amc_operators = m });
    }

    let for_axiom : EcDecl.axiom projector = {
      px_premc   = (fun mc -> mc.mc_axioms);
      px_topremc = (fun m mc -> { mc with mc_axioms = m });
      px_actmc   = (fun mc -> mc.amc_axioms);
      px_toactmc = (fun m mc -> { mc with amc_axioms = m });
    }

    let for_theory : ctheory projector = {
      px_premc   = (fun mc -> mc.mc_theories);
      px_topremc = (fun m mc -> { mc with mc_theories = m });
      px_actmc   = (fun mc -> mc.amc_theories);
      px_toactmc = (fun m mc -> { mc with amc_theories = m });
    }
  end

  (* Lookup a compoments using a [symbol list] (scope), i.e. starting
   * from the compoment [env_root]. *)

  let path_of_qn (top : EcPath.path) (qn : symbol list) =
    List.fold_left EcPath.pqname top qn
      
  let lookup_mc (qn : symbol list) (env : env) =
    match qn with
    | [] -> Some (ActMc env.env_current)

    | top :: qn -> begin
        match MMsym.last top env.env_current.amc_components with
        | None -> None
        | Some p ->
            let p = path_of_qn p qn in
              omap (Mp.find_opt p env.env_comps) premc
      end

  (* ------------------------------------------------------------------ *)

  (* Direct lookup in a [container] using a [projector]. Returns only
   * last inserted object bound to the given name. *)
  let mc_lookup1 px x mc =
    match mc with
    | PreMc mc ->
        Msym.find_opt x (px.Px.px_premc mc)

    | ActMc mc ->
        MMsym.last x (px.Px.px_actmc mc)

  (* Direct lookup in a [container] using a [projector]. Returns all
   * the object bound to the given name. *)
  let mc_lookupall px x mc =
    match mc with
    | PreMc mc ->
        otolist (Msym.find_opt x (px.Px.px_premc mc))

    | ActMc mc ->
        MMsym.all x (px.Px.px_actmc mc)


  (* Lookup an object using a [qsymbol], i.e. starting from
   * the compoment [env_current]. The object returned is suspended. *)

  let _params_of_path (env : env) (path : path) =
      let prefix = oget (EcPath.prefix path) in
        snd (oget (lookup_mc_by_path env prefix))

  let lookup px ((qn, x) : qsymbol) (env : env) =
    match lookup_mc qn env with
    | None ->
        raise (LookupFailure (`QSymbol (qn, x)))

    | Some mc -> begin
        match mc_lookup1 px x mc with
        | None ->
            raise (LookupFailure (`QSymbol (qn, x)))

        | Some (p, obj) ->
            (p, suspend obj (_params_of_path env (EcPath.path_of_mpath p)))
      end

  let lookupall px ((qn, x) : qsymbol) (env : env) =
    match lookup_mc qn env with
    | None -> raise (LookupFailure (`QSymbol (qn, x)))
    | Some mc ->
        List.map
          (fun (p, obj) -> (p, suspend obj (_params_of_path env (EcPath.path_of_mpath p))))
          (mc_lookupall px x mc)

  (* Binding of an object in a [premc]. Fails if a binding already
   * exists for the given name and name. *)

  let mc_bind_raw px name path obj mc =
    let map = px.Px.px_premc mc in
      match Msym.find_opt name map with
      | Some _ -> raise (DuplicatedBinding name)
      | None   -> px.Px.px_topremc (Msym.add name (path, obj) map) mc

  let mc_bind px path obj mc =
    mc_bind_raw px (EcPath.basename (EcPath.path_of_mpath path)) path obj mc

  let mc_bind_variable path obj mc = mc_bind Px.for_variable path obj mc
  let mc_bind_function path obj mc = mc_bind Px.for_function path obj mc
  let mc_bind_module   path obj mc = mc_bind Px.for_module   path obj mc
  let mc_bind_modtype  path obj mc = mc_bind Px.for_modtype  path obj mc
  let mc_bind_typedecl path obj mc = mc_bind Px.for_typedecl path obj mc
  let mc_bind_operator path obj mc = mc_bind Px.for_operator path obj mc
  let mc_bind_axiom    path obj mc = mc_bind Px.for_axiom    path obj mc
  let mc_bind_theory   path obj mc = mc_bind Px.for_theory   path obj mc

  let mc_bind_mc (path : EcPath.path) mc =
    let name = EcPath.basename path in
      if Msym.find_opt name mc.mc_components <> None then
        raise (DuplicatedBinding name);
      { mc with
          mc_components = Msym.add name path mc.mc_components; }

  (* Binding of an object a in [activemc]. It is allowed two bind a
   * name several times. *)
  let amc_bind px x path obj mc =
    let map = px.Px.px_actmc mc in
    let obj = (path, obj) in
      px.Px.px_toactmc (MMsym.add x obj map) mc

  let amc_bind_mc (path : EcPath.path) mc =
    let name = EcPath.basename path in
      { mc with
          amc_components = MMsym.add name path mc.amc_components; }

  (* ------------------------------------------------------------------ *)
  let mc_of_module (env : env) (me : module_expr) =
    let xpath =
      let params = me.me_sig.mt_params in
      let params = List.map (fun (x, _) -> EcPath.mident x) params in
      let scope  = 
        EcPath.mqname env.env_scope EcPath.PKmodule me.me_name params in
        fun x -> EcPath.mqname scope EcPath.PKother x []
    in

    let mc1_of_module (mc : premc) = function
      | MI_Module me ->
          mc_bind_module (xpath me.me_name) me mc

      | MI_Variable v ->
          let vty =
            { vb_type = v.v_type;
              vb_kind = PVglob; }
          in
            mc_bind_variable (xpath v.v_name) vty mc

      | MI_Function f ->
          mc_bind_function (xpath f.f_name) f mc

    in
      List.fold_left mc1_of_module empty_premc me.me_comps

  (* ------------------------------------------------------------------ *)
  let mc_of_module_param (mid : EcIdent.t) (me : module_expr) =
    let xpath (x : symbol) =
      EcPath.mqname (EcPath.mident mid) EcPath.PKother x []
    in

    let mc1_of_module (mc : premc) = function
      | MI_Module _ -> assert false

      | MI_Variable v ->
          let vty =
            { vb_type = v.v_type;
              vb_kind = PVglob; }
          in
            mc_bind_raw Px.for_variable v.v_name (xpath v.v_name) vty mc


      | MI_Function f ->
          mc_bind_raw Px.for_function f.f_name (xpath f.f_name) f mc
    in
      List.fold_left mc1_of_module empty_premc me.me_comps

  (* ------------------------------------------------------------------ *)
  let bind px env k name obj =
    let path = EcPath.mqname env.env_scope k name [] in

      { env with
          env_current =
            amc_bind px name path obj env.env_current;
          env_comps =
            Mp.change
              (fun mc -> Some (mc_bind px path obj (oget mc)))
              (EcPath.path_of_mpath env.env_scope)
              env.env_comps; }

  (* -------------------------------------------------------------------- *)
  let bind_mc env name comps =
    let env_scope = env.env_scope in
    let path =
      EcPath.pqname (EcPath.path_of_mpath env_scope) name
    in

      if Mp.find_opt path env.env_comps <> None then
        raise (DuplicatedBinding name);

      { env with
          env_current = amc_bind_mc path env.env_current;
          env_comps =
            Mp.change
              (fun mc -> Some (mc_bind_mc path (oget mc)))
              (EcPath.path_of_mpath env_scope)
              (Mp.add path comps env.env_comps); }

  (* -------------------------------------------------------------------- *)
  let import px env path obj =
    let bname = EcPath.basename (EcPath.path_of_mpath path) in
      { env with
          env_current = amc_bind px bname path obj env.env_current; }

  (* ------------------------------------------------------------------ *)
  let rec bind_variable x ty env =
    bind Px.for_variable env EcPath.PKother x ty

  and bind_function x fsig env =
    bind Px.for_function env EcPath.PKother x fsig

  and bind_module x me env =
    let comps = mc_of_module env me in
    let env   = bind Px.for_module env EcPath.PKmodule x me in
    let env   = bind_mc env x comps in
      env

  and bind_modtype x tymod env =
    bind Px.for_modtype env EcPath.PKother x tymod

  and bind_typedecl x tydecl env =
    bind Px.for_typedecl env EcPath.PKother x tydecl

  and bind_operator x op env =
    bind Px.for_operator env EcPath.PKother x op

  and bind_axiom x ax env =
    bind Px.for_axiom env EcPath.PKother x ax

  and bind_theory x cth env =
    let env, comps = mc_of_ctheory env env.env_scope x cth in
    let env = bind Px.for_theory env EcPath.PKother x cth in
    let env = bind_mc env x comps in
      env

  and mc_of_ctheory =
    let rec mc_of_ctheory_struct path (env, mc) = function 
      | CTh_type     (x, td)  -> env, mc_bind_typedecl (EcPath.mqname path EcPath.PKother x []) td mc
      | CTh_operator (x, op)  -> env, mc_bind_operator (EcPath.mqname path EcPath.PKother x []) op mc
      | CTh_axiom    (x, ax)  -> env, mc_bind_axiom    (EcPath.mqname path EcPath.PKother x []) ax mc
      | CTh_modtype  (x, tm)  -> env, mc_bind_modtype  (EcPath.mqname path EcPath.PKother x []) tm mc
      | CTh_module   m        -> env, mc_bind_module   (EcPath.mqname path EcPath.PKmodule m.me_name []) m mc
      | CTh_export   _        -> env, mc
      | CTh_theory   (x, cth) ->
          let subpath = EcPath.mqname path EcPath.PKother x [] in
          let env, submc =
            List.fold_left
              (mc_of_ctheory_struct subpath)
              (env, empty_premc) cth.cth_struct
          in
  
          let env =
            let comps = env.env_comps in
            let comps = Mp.add (EcPath.path_of_mpath subpath) submc comps in
              { env with env_comps = comps }
          in
            (env, mc_bind_mc
                    (EcPath.path_of_mpath subpath)
                    (mc_bind_theory subpath cth mc))
    in
      fun (env : env) (path : EcPath.mpath) (x : symbol) (cth : ctheory) ->
        List.fold_left
          (mc_of_ctheory_struct (EcPath.mqname path EcPath.PKother x []))
          (env, empty_premc)
          cth.cth_struct
end

(* -------------------------------------------------------------------- *)
let enter (name : symbol) (k : EcPath.path_kind) params (env : env) =
  assert (List.uniq params);

  let params = List.map EcPath.mident params in
  let path   = EcPath.mqname env.env_scope k name params in
  let env    = MC.bind_mc env name empty_premc in

    { env with
        env_scope = path;
        env_rb    = [];
        env_item  = []; }

(* -------------------------------------------------------------------- *)
type meerror =
| UnknownMemory of [`Symbol of symbol | `Memory of memory]

exception MEError of meerror

(* -------------------------------------------------------------------- *)
module Memory = struct
  let byid (me : memory) (env : env) =
    let memories = MMsym.all (EcIdent.name me) env.env_memories in
    let memories = List.filter (fun (me', _) -> EcIdent.id_equal me me') memories in

      match memories with
      | []       -> None
      | [(_, m)] -> Some m
      | _        -> assert false

  let lookup (me : symbol) (env : env) =
    MMsym.last me env.env_memories

  let set_active (me : memory) (env : env) =
    match byid me env with
    | None   -> raise (MEError (UnknownMemory (`Memory me)))
    | Some _ -> { env with env_actmem = Some me }

  let get_active (env : env) =
    env.env_actmem

  let current (env : env) =
    match env.env_actmem with
    | None    -> None
    | Some me -> Some (me, oget (byid me env))

  let push (name : symbol) (me : memenv) (env : env) =
    let id   = EcIdent.create name in
    let maps = MMsym.add name (id, me) env.env_memories in
      (id, { env with env_memories = maps })
end

(* -------------------------------------------------------------------- *)
module Var = struct
  module Px = MC.Px

  type t = varbind

  let by_path (p : EcPath.path) (env : env) =
    MC.lookup_by_path Px.for_variable.Px.px_premc p env

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let by_mpath (p : EcPath.mpath) (env : env) =
    let subst _s (x : varbind) = x in
    let x = by_path (EcPath.path_of_mpath p) env in
      unsuspend subst x (EcPath.args_of_mpath p)

  let by_mpath_opt (p : EcPath.mpath) (env : env) =
    try_lf (fun () -> by_mpath p env)

  let lookup_locals name env =
    MMsym.all name env.env_locals

  let lookup_local name env =
    match MMsym.last name env.env_locals with 
    | None   -> raise (LookupFailure (`QSymbol ([], name)))
    | Some x -> x

  let lookup_local_opt name env =
    MMsym.last name env.env_locals

  let lookup_progvar qname env =
    let (p, x) = MC.lookup Px.for_variable qname env in
      if is_suspended x then
        raise (LookupFailure (`QSymbol qname));
      let x = x.sp_target in
        ({ pv_name = p; pv_kind = x.vb_kind }, x.vb_type)

  let lookup_progvar_opt name env =
    try_lf (fun () -> lookup_progvar name env)

  let bind name pvkind ty env =
    let vb = { vb_type = ty; vb_kind = pvkind; } in
      MC.bind_variable name vb env

  let bindall bindings pvkind env =
    List.fold_left
      (fun env (name, ty) -> bind name pvkind ty env)
      env bindings

   let bind_local name ty env =
     let s = EcIdent.name name in
       { env with
           env_locals = MMsym.add s (name, ty) env.env_locals }
 
   let bind_locals bindings env =
     List.fold_left
       (fun env (name, ty) -> bind_local name ty env)
       env bindings

  let add (path : EcPath.mpath) (env : env) =
    let obj = by_mpath path env in 
      MC.import Px.for_variable env path obj
end

(* -------------------------------------------------------------------- *)
module Fun = struct
  module Px = MC.Px

  type t = EcModules.function_

  let by_path (p : EcPath.path) (env : env) =
    MC.lookup_by_path Px.for_function.Px.px_premc p env 

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let by_mpath (p : EcPath.mpath) (env : env) =
    let x = by_path (EcPath.path_of_mpath p) env in
    unsuspend EcSubst.subst_function x (EcPath.args_of_mpath p)

  let by_mpath_opt (p : EcPath.mpath) (env : env) =
    try_lf (fun () -> by_mpath p env)

  let lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_function name env in
      if is_suspended x then
        raise (LookupFailure (`QSymbol name));
      (p, x.sp_target)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name fun_ env =
    MC.bind_function name fun_ env

  let add (path : EcPath.mpath) (env : env) =
    let obj = by_mpath path env in 
    MC.import Px.for_function env path obj
end

(* -------------------------------------------------------------------- *)
module Ty = struct
  module Px = MC.Px

  type t = EcDecl.tydecl

  let by_path (p : EcPath.path) (env : env) =
    check_not_suspended
      (MC.lookup_by_path Px.for_typedecl.Px.px_premc p env)

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_typedecl name env in
    (EcPath.path_of_mpath p, check_not_suspended x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
    MC.import Px.for_typedecl env (EcPath.mpath_of_path path) obj

  let bind name ty env =
    let env = MC.bind_typedecl name ty env in
    let (w3, rb) =
        EcWhy3.add_ty env.env_w3
          (EcPath.pqname (EcPath.path_of_mpath env.env_scope) name) ty
    in
      { env with
          env_w3   = w3;
          env_rb   = rb @ env.env_rb;
          env_item = CTh_type (name, ty) :: env.env_item; }

  let rebind name ty env =
    MC.bind_typedecl name ty env

  let defined (name : EcPath.path) (env : env) =
    match by_path_opt name env with
    | Some { tyd_type = Some _ } -> true
    | _ -> false

  let unfold (name : EcPath.path) (args : EcTypes.ty list) (env : env) =
    match by_path_opt name env with
    | Some ({ tyd_type = Some body} as tyd) ->
        EcTypes.Tvar.subst (EcTypes.Tvar.init tyd.tyd_params args) body
    | _ -> raise (LookupFailure (`Path name))
end

(* -------------------------------------------------------------------- *)
module Op = struct
  module Px = MC.Px

  type t = EcDecl.operator

  let by_path (p : EcPath.path) (env : env) =
    check_not_suspended
      (MC.lookup_by_path Px.for_operator.Px.px_premc p env)

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_operator name env in
    (EcPath.path_of_mpath p, check_not_suspended x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
    MC.import Px.for_operator env (EcPath.mpath_of_path path) obj

  let bind name op env =
    let env = MC.bind_operator name op env in
    let (w3, rb) =
        EcWhy3.add_op env.env_w3
          (EcPath.extend (Some (EcPath.path_of_mpath env.env_scope)) name) op
    in
      { env with
          env_w3   = w3;
          env_rb   = rb @ env.env_rb;
          env_item = CTh_operator(name, op) :: env.env_item; }

  (* This version does not create a Why3 binding. *)
  let bind_logical name op env = 
    let env = MC.bind_operator name op env in
      { env with
          env_item = CTh_operator (name, op) :: env.env_item }

  let rebind name op env =
    MC.bind_operator name op env

  let all filter (qname : qsymbol) (env : env) =
    let ops = MC.lookupall MC.Px.for_operator qname env in
    let ops =
      List.map
        (fun (p, op) ->
          (EcPath.path_of_mpath p, check_not_suspended op)) ops
    in
      List.filter (fun (_, op) -> filter op) ops
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  module Px = MC.Px

  type t = axiom

  let by_path (p : EcPath.path) (env : env) =
    check_not_suspended
      (MC.lookup_by_path Px.for_axiom.Px.px_premc p env)

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_axiom name env in
    (EcPath.path_of_mpath p, check_not_suspended x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
    MC.import Px.for_axiom env (EcPath.mpath_of_path path) obj

  let bind name ax env = 
    let env = MC.bind_axiom name ax env in
    let (w3, rb) = 
      EcWhy3.add_ax env.env_w3
        (EcPath.extend (Some (EcPath.path_of_mpath env.env_scope)) name) ax
    in
      { env with
          env_w3   = w3;
          env_rb   = rb @ env.env_rb;
          env_item = CTh_axiom (name, ax) :: env.env_item }

  let rebind name ax env =
    MC.bind_axiom name ax env

  let by_path (p : EcPath.path) (env : env) =
    check_not_suspended
      (MC.lookup_by_path Px.for_axiom.Px.px_premc p env)

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let instanciate p tys env = 
    match by_path_opt p env with
    | Some ({ ax_spec = Some f } as ax) ->
        Fsubst.subst_tvar (EcTypes.Tvar.init ax.ax_params tys) f
    | _ -> raise (LookupFailure (`Path p))
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  type t = module_expr

  module Px = MC.Px

  let by_path (p : EcPath.path) (env : env) =
    MC.lookup_by_path Px.for_module.Px.px_premc p env
    
  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let by_mpath (p : EcPath.mpath) (env : env) =
    let x = by_path (EcPath.path_of_mpath p) env in
    unsuspend EcSubst.subst_module x (EcPath.args_of_mpath p)

  let by_mpath_opt (p : EcPath.mpath) (env : env) =
    try_lf (fun () -> by_mpath p env)

  let lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_module name env in
      if is_suspended x then
        raise (LookupFailure (`QSymbol name));
      (p, x.sp_target)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name me env =
    assert (me.me_name = name);
    let env = MC.bind_module name me env in
    let (w3, rb) =
      EcWhy3.add_mod_exp env.env_w3
          (EcPath.pqname (EcPath.path_of_mpath env.env_scope) name) me in
    { env with
      env_w3 = w3;
      env_rb = rb @ env.env_rb;
      env_item = CTh_module me :: env.env_item }

  let bind_local name modty env =
    let modsig =
      check_not_suspended (MC.lookup_by_path Px.for_modtype.Px.px_premc modty env)
    in

    let me    = module_expr_of_module_sig name modty modsig in
    let path  = EcPath.pident name in
    let comps = MC.mc_of_module_param name me  in

    let env =
      { env with
          env_current = (
            let current = env.env_current in
            let current = MC.amc_bind_mc path current in
            let current = MC.amc_bind Px.for_module
                            (EcIdent.name name) (EcPath.mident name)
                            me current
            in
              current);
          env_comps = Mp.add path comps env.env_comps; }
    in
      env

  let bind_locals bindings env =
    List.fold_left
      (fun env (name, me) -> bind_local name me env)
      env bindings

  let add (path : EcPath.mpath) (env : env) =
    let obj = by_mpath path env in
      MC.import Px.for_module env path obj

  let rec unfold_mod_path (env : env) (p : EcPath.mpath) =
    match by_mpath_opt p env with
    | None -> unfold_mod_path_prefix env p
          
    | Some me -> begin
        match me.me_body with
        | ME_Alias alias ->
            unfold_mod_path env alias
              
        | _ ->
            unfold_mod_path_prefix env p
    end

  and unfold_mod_path_prefix (env : env) (p : EcPath.mpath) =
    match EcPath.m_split p with
    | None ->
        p
          
    | Some (prefix, k, x, args) ->
        let prefix = unfold_mod_path env prefix in
        let args   = List.map (unfold_mod_path env) args in
        EcPath.mqname prefix k x args

  let enter name params env =
    let env = enter name EcPath.PKmodule (List.map fst params) env in
      bind_locals params env
end

(* -------------------------------------------------------------------- *)
module ModTy = struct
  module Px = MC.Px

  type t = module_sig

  let by_path (p : EcPath.path) (env : env) =
    check_not_suspended
      (MC.lookup_by_path Px.for_modtype.Px.px_premc p env)

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_modtype name env in
    (EcPath.path_of_mpath p, check_not_suspended x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name modty env =
    let env = MC.bind_modtype name modty env in
    { env with
      env_item = CTh_modtype (name, modty) :: env.env_item }

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
    MC.import Px.for_modtype env (EcPath.mpath_of_path path) obj

  let mod_type_equiv (_ : env) (mty1 : module_type) (mty2 : module_type) =
    EcPath.p_equal mty1 mty2

  let has_mod_type (env : env) (dst : module_type list) (src : module_type) =
    List.exists (mod_type_equiv env src) dst
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  module Px = MC.Px

  type t = ctheory

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
  let enter name env =
    enter name EcPath.PKother [] env

  (* ------------------------------------------------------------------ *)
  let by_path (p : EcPath.path) (env : env) =
    check_not_suspended
      (MC.lookup_by_path Px.for_theory.Px.px_premc p env)

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_theory name env in
    (EcPath.path_of_mpath p, check_not_suspended x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  (* ------------------------------------------------------------------ *)
  let bind id cth env =
    let env = MC.bind_theory id cth.cth3_theory env in
      { env with
          env_w3   = EcWhy3.rebind env.env_w3 cth.cth3_rebind;
          env_rb   = List.rev_append cth.cth3_rebind env.env_rb;
          env_item = (CTh_theory (id, cth.cth3_theory)) :: env.env_item; }

  (* ------------------------------------------------------------------ *)
  let rebind name cth env =
    MC.bind_theory name cth env

  (* ------------------------------------------------------------------ *)
  let import (path : EcPath.path) (env : env) =
    let rec import (env : env) path (cth : ctheory) =
      let xpath x = EcPath.mqname path EcPath.PKother x [] in
      let rec import_cth_item (env : env) = function
        | CTh_type (x, ty) ->
            MC.import Px.for_typedecl env (xpath x) ty
              
        | CTh_operator (x, op) ->
            MC.import Px.for_operator env (xpath x) op
              
        | CTh_axiom (x, ax) ->
            MC.import Px.for_axiom env (xpath x) ax
              
        | CTh_modtype (x, ty) ->
            MC.import Px.for_modtype env (xpath x) ty
              
        | CTh_module m -> 
            MC.import Px.for_module env (EcPath.mqname path EcPath.PKmodule m.me_name []) m
              
        | CTh_export p ->
            let mp = EcPath.mpath_of_path p in
            import env mp (by_path p env)
              
        | CTh_theory (x, th) ->
            let env = MC.import Px.for_theory env (xpath x) th in
            { env with env_current =
              MC.amc_bind_mc (EcPath.path_of_mpath (xpath x)) env.env_current }
      in
      List.fold_left import_cth_item env cth.cth_struct

    in
      import env (EcPath.mpath_of_path path) (by_path path env)

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
    let rootnm = EcCoreLib.p_top in
    let mrootnm = EcPath.mpath_of_path rootnm in
    let thpath = EcPath.pqname rootnm x in
    let mthpath = EcPath.mpath_of_path thpath in

    let env, thmc =
      MC.mc_of_ctheory env mrootnm x cth.cth3_theory
    in

    let topmc = Mp.find rootnm env.env_comps in
    let topmc = {
      topmc with
        mc_theories   = Msym.add x (mthpath, cth.cth3_theory) topmc.mc_theories;
        mc_components = Msym.add x thpath topmc.mc_components; }
    in

    let current = {
      env.env_current with
        amc_theories =
          MMsym.add x (mthpath, cth.cth3_theory)
            env.env_current.amc_theories;
        amc_components =
          MMsym.add x thpath
                     env.env_current.amc_components; }
    in

    let comps = env.env_comps in
    let comps = Mp.add rootnm topmc comps in
    let comps = Mp.add thpath thmc  comps in

    { env with
        env_current = current;
        env_comps   = comps;
        env_w3      = EcWhy3.rebind env.env_w3 cth.cth3_rebind; }

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
      MC.import Px.for_theory env (EcPath.mpath_of_path path) obj
end

(* -------------------------------------------------------------------- *)
let import_w3 env th rd = 
  let lth, rbi = EcWhy3.import_w3 env.env_w3 
      (EcPath.path_of_mpath env.env_scope) th rd in
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
  let env = enter EcCoreLib.id_pervasive EcPath.PKother [] env0 in
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
      [EcCoreLib.p_and;EcCoreLib.p_anda; 
       EcCoreLib.p_or;EcCoreLib.p_ora;
       EcCoreLib.p_imp; EcCoreLib.p_iff] in
 let distr_rn = [
    ["distr"], EcWhy3.RDts, EcPath.basename EcCoreLib.p_distr;
  ] in
  let env, _ = import_w3 env EcWhy3.distr_theory distr_rn in
  let cth = Theory.close env in
  let env1 = Theory.bind EcCoreLib.id_pervasive cth env0 in
  let env1 = Theory.import EcCoreLib.p_pervasive env1 in
  env1

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of EcTypes.pvar_kind * EcTypes.ty
  | `Function  of function_
  | `Module    of module_expr
  | `ModType   of module_sig
]

let bind1 ((x, eb) : symbol * ebinding) (env : env) =
  match eb with
  | `Variable v -> Var   .bind x (fst v) (snd v) env
  | `Function f -> Fun   .bind x f env
  | `Module   m -> Mod   .bind x m env
  | `ModType  i -> ModTy .bind x i env

let bindall (items : (symbol * ebinding) list) (env : env) =
  List.fold_left ((^~) bind1) env items  

(* -------------------------------------------------------------------- *)     
exception IncompatibleType of ty * ty
exception IncompatibleForm of form * form * form * form

let rec equal_type env t1 t2 = 
  match t1.ty_node, t2.ty_node with
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

  
let check_type env t1 t2 = 
  if not (equal_type env t1 t2) then raise (IncompatibleType(t1,t2))

let rec destr_tfun env tf = 
  match tf.ty_node with
  | Tfun(ty1,ty2) -> ty1, ty2
  | Tconstr(p,tys) when Ty.defined p env ->
      destr_tfun env (Ty.unfold p tys env) 
  | _ -> assert false 

let rec ty_fun_app env tf targs = 
  match targs with
  | [] -> tf
  | t1 :: targs ->
      let dom,codom = destr_tfun env tf in
      check_type env dom t1;
      ty_fun_app env codom targs

(* TODO : can be good to also add unfolding of globals and locals *)

let pv_equal_norm env p1 p2 = 
  pv_equal p1 p2 || 
  (p1.pv_kind = p2.pv_kind &&
   EcPath.m_equal 
     (Mod.unfold_mod_path env p1.pv_name) (Mod.unfold_mod_path env p2.pv_name))

let m_equal_norm env p1 p2 = 
  EcPath.m_equal p1 p2 || 
  EcPath.m_equal (Mod.unfold_mod_path env p1) (Mod.unfold_mod_path env p2)

let e_equal_norm env e1 e2 =
  let find alpha id = try Mid.find id alpha with _ -> id in
  let check_lpattern alpha lp1 lp2 = 
    match lp1, lp2 with
    | LSymbol id1, LSymbol id2 -> Mid.add id1 id2 alpha
    | LTuple lid1, LTuple lid2 when List.length lid1 = List.length lid2 ->
        List.fold_left2 (fun alpha id1 id2 -> Mid.add id1 id2 alpha) 
          alpha lid1 lid2
    | _, _ -> raise Not_found in
  let rec aux alpha e1 e2 = 
    match e1.tye_node, e2.tye_node with
    | Eint   i1, Eint   i2 -> i1 = i2
    | Elocal id1, Elocal id2 -> EcIdent.id_equal (find alpha id1) id2
    | Evar   p1, Evar   p2 -> pv_equal_norm env p1 p2
    | Eop(o1,ty1), Eop(o2,ty2) -> 
        p_equal o1 o2 && List.all2 (equal_type env) ty1 ty2

    | Eapp(f1,args1), Eapp(f2,args2) ->
        aux alpha f1 f2 &&
        List.all2 (aux alpha) args1 args2
    | Elet(p1,f1',g1), Elet(p2,f2',g2) ->
        aux alpha f1' f2' &&
        (try aux (check_lpattern alpha p1 p2) g1 g2 with Not_found -> false)
    | Etuple args1, Etuple args2 -> List.all2 (aux alpha) args1 args2
    | Eif (a1,b1,c1), Eif(a2,b2,c2) ->
        aux alpha a1 a2 && aux alpha b1 b2 && aux alpha c1 c2 
    | _, _ -> false in
  aux Mid.empty e1 e2

let lv_equal_norm env lv1 lv2 = 
  match lv1, lv2 with
  | LvVar(p1,_), LvVar(p2,_) -> pv_equal_norm env p1 p2
  | LvTuple p1, LvTuple p2 ->
      List.all2 (fun (p1,_) (p2,_) -> pv_equal_norm env p1 p2) p1 p2
  | LvMap((m1,ty1),p1,e1,_), LvMap((m2,ty2),p2,e2,_) -> 
      p_equal m1 m2 &&
      List.all2 (equal_type env) ty1 ty2 &&
      pv_equal_norm env p1 p2 && e_equal_norm env e1 e2 
  | _, _ -> false 

let rec s_equal_norm env s1 s2 = 
  s_equal s1 s2 || 
  List.all2 (i_equal_norm env) s1.s_node s2.s_node

and i_equal_norm env i1 i2 = 
  i_equal i1 i2 || 
  match i1.i_node, i2.i_node with
  | Sasgn(lv1,e1), Sasgn(lv2,e2) -> 
      lv_equal_norm env lv1 lv2 && e_equal_norm env e1 e2
  | Srnd(lv1,e1), Srnd(lv2,e2) -> 
      lv_equal_norm env lv1 lv2 && e_equal_norm env e1 e2
  | Scall(lv1, f1, e1), Scall(lv2,f2,e2) ->
      oall2 (lv_equal_norm env) lv1 lv2 &&
      m_equal_norm env f1 f2 &&
      List.all2 (e_equal_norm env) e1 e2
  | Sif (a1,b1,c1), Sif(a2,b2,c2) ->
      e_equal_norm env a1 a2 
        && s_equal_norm env b1 b2 
        && s_equal_norm env c1 c2 
  | Swhile(a1,b1), Swhile(a2,b2) ->
      e_equal_norm env a1 a2 && s_equal_norm env b1 b2 
  | Sassert a1, Sassert a2 ->
      e_equal_norm env a1 a2 
  | _, _ -> false
        
  
  
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
      let tyok =
        match ty1, ty2 with
        | GTty    ty1, GTty ty2   -> equal_type env ty1 ty2
        | GTmodty p1 , GTmodty p2 -> ModTy.mod_type_equiv env p1 p2
        | GTmem      , GTmem      -> true
        | _          , _          -> false
      in
        if   tyok
        then Mid.add x1 x2 alpha
        else error f1 f2
    in
      List.fold_left2 check_one alpha bd1 bd2 in

  let rec aux alpha f1 f2 = 
    if Mid.is_empty alpha && f_equal f1 f2 then () 
    else match f1.f_node, f2.f_node with

    | Fquant(q1,bd1,f1'), Fquant(q2,bd2,f2') when 
        q1 = q2 && List.length bd1 = List.length bd2 ->
          let alpha = check_binding f1 f2 alpha bd1 bd2 in
          aux alpha f1' f2'

    | Fif(a1,b1,c1), Fif(a2,b2,c2) ->
        aux alpha a1 a2; aux alpha b1 b2; aux alpha c1 c2

    | Flet(p1,f1',g1), Flet(p2,f2',g2) ->
        aux alpha f1' f2';
        let alpha = check_lpattern f1 f2 alpha p1 p2 in
        aux alpha g1 g2

    | Fint i1, Fint i2 when i1 = i2 -> ()

    | Flocal id1, Flocal id2 when EcIdent.id_equal (find alpha id1) id2 -> ()

    | Fpvar(p1,m1), Fpvar(p2,m2) when 
        EcIdent.id_equal m1 m2 && pv_equal_norm env p1 p2  -> ()

    | Fop(p1, ty1), Fop(p2, ty2) when EcPath.p_equal p1 p2 &&
        List.all2 (equal_type env) ty1 ty2 -> () 

    | Fapp(f1,args1), Fapp(f2,args2) 
      when List.length args1 = List.length args2 ->
        aux alpha f1 f2;
        List.iter2 (aux alpha) args1 args2

    | Ftuple args1, Ftuple args2 when List.length args1 = List.length args2 ->
        List.iter2 (aux alpha) args1 args2

    | FhoareF(pre1,p1,post1), FhoareF(pre2,p2,post2) 
      when m_equal_norm env p1 p2 ->
        aux alpha pre1  pre2;
        aux alpha post1 post2

    | FhoareS(_,pre1,s1,post1), FhoareS(_,pre2,s2,post2) 
      when s_equal_norm env s1 s2 -> 
        aux alpha pre1  pre2;
        aux alpha post1 post2

    | FequivF(pre1,(l1,r1),post1), FequivF(pre2,(l2,r2),post2) 
      when m_equal_norm env l1 l2 && m_equal_norm env r1 r2 ->
        aux alpha pre1  pre2;
        aux alpha post1 post2

    | FequivS(pre1,((_,l1),(_,r1)),post1), FequivS(pre2,((_,l2),(_,r2)),post2) 
      when s_equal_norm env l1 l2 && s_equal_norm env r1 r2 ->
        aux alpha pre1  pre2;
        aux alpha post1 post2

    | Fpr(m1,p1,args1,res1,f1'), Fpr(m2,p2,args2,res2, f2') 
      when EcIdent.id_equal (find alpha m1) m2 &&
           m_equal_norm env p1 p2 &&  
           List.length args1 = List.length args2 ->
        List.iter2 (aux alpha) args1 args2;
        let (id1,ty1) = res1 in
        let (id2,ty2) = res2 in
        let alpha = 
          check_binding f1 f2 alpha [id1,GTty ty1] [id2,GTty ty2] in
        aux alpha f1' f2'

    | _, _ -> error f1 f2

  in
    aux Mid.empty f1 f2

let is_alpha_equal env f1 f2 = 
  try check_alpha_equal env f1 f2; true
  with _ -> false

let norm_pvar env pv = 
  let p = Mod.unfold_mod_path env pv.pv_name in
  if m_equal p pv.pv_name then pv else { pv_name = p; pv_kind = pv.pv_kind }
  
let rec norm_form env f =
  match f.f_node with
  | Fquant(q,bd,f) ->
      f_quant q bd (norm_form env f) 

  | Fif(a,b,c) ->
      f_if (norm_form env a) (norm_form env b) (norm_form env c)

  | Flet(p,f,g) ->
      f_let p (norm_form env f) (norm_form env g)

  | Fint _ | Flocal _ | Fop _ -> f  

  | Fpvar(p,m) -> f_pvar (norm_pvar env p) f.f_ty m

  | Fapp(f,args) ->
      f_app (norm_form env f) (List.map (norm_form env) args) f.f_ty 

  | Ftuple args ->
      f_tuple (List.map (norm_form env) args) 

  | FhoareF(pre,p,post) ->
      f_hoareF (norm_form env pre) 
        (Mod.unfold_mod_path env p) (norm_form env post)

  | FhoareS _ -> assert false (* FIXME ? Not implemented *)

  | FequivF(pre,(l,r),post) ->
      f_equivF (norm_form env pre) 
        (Mod.unfold_mod_path env l) (Mod.unfold_mod_path env r)
        (norm_form env post)

  | FequivS _ -> assert false (* FIXME ? Not implemented *)

  | Fpr(m,p,args,res,f) ->
      f_pr m (Mod.unfold_mod_path env p) (List.map (norm_form env) args) 
        res (norm_form env f)

let check_goal env pi ld = EcWhy3.check_goal env.env_w3 pi ld
