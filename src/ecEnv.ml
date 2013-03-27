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
open EcBaseLogic
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
        EcSubst.empty ([] :: x.sp_params) args
    in
      if EcSubst.is_empty s then x.sp_target else f s x.sp_target

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
  env_memories : actmem MMsym.t;
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

and actmem =
| AMAbstract of EcIdent.t
| AMConcrete of mpath * memenv

let premc = fun (mc : premc   ) -> PreMc mc
let actmc = fun (mc : activemc) -> ActMc mc

(* -------------------------------------------------------------------- *)
type env = preenv

(* -------------------------------------------------------------------- *)
let empty_premc params = {
  mc_parameters = params;
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
      env_comps    = Mp.singleton (EcPath.psymbol name) (empty_premc []);
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
               (fun k mc ->
                 Printf.sprintf "%s (%d)"
                   (EcPath.tostring k)
                   (List.length mc.mc_parameters))
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
    match path.EcPath.p_node with
    | EcPath.Psymbol _ -> []
    | EcPath.Pident  _ -> []

    | EcPath.Pqname (prefix, _) ->
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
    let rec mc_of_module (scope : EcPath.mpath) (me : module_expr) =
      let params   = me.me_sig.mis_params in
      let params   = List.map (fun (x, _) -> EcPath.mident x) params in
      let subscope = EcPath.mqname scope EcPath.PKmodule me.me_name params in
      let xpath = fun k x -> EcPath.mqname subscope k x [] in

      let mc1_of_module (mc : premc) = function
      | MI_Module subme ->
          let xpath = xpath EcPath.PKmodule subme.me_name in
          let (submc, subcomps) = mc_of_module subscope subme in
            (mc_bind_module xpath subme
               (mc_bind_mc (EcPath.path_of_mpath xpath) mc),
             Some (submc, subcomps))

      | MI_Variable v ->
          let vty =
            { vb_type = v.v_type;
              vb_kind = PVglob; }
          in
            (mc_bind_variable (xpath EcPath.PKother v.v_name) vty mc, None)

      | MI_Function f ->
          (mc_bind_function (xpath EcPath.PKother f.f_name) f mc, None)

      in

      let mc, submcs =
        List.map_fold mc1_of_module
          (empty_premc me.me_sig.mis_params)
          me.me_comps
      in
        ((me.me_name, mc), List.prmap (fun x -> x) submcs)
    in
      mc_of_module env.env_scope me

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
      List.fold_left mc1_of_module (empty_premc []) me.me_comps

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
    let rec bind_submc env path ((name, mc), submcs) =
      let path = EcPath.pqname path name in

      if Mp.find_opt path env.env_comps <> None then
        raise (DuplicatedBinding (EcPath.basename path));

      bind_submcs
        { env with env_comps = Mp.add path mc env.env_comps }
        path submcs

    and bind_submcs env path submcs =
      List.fold_left (bind_submc^~ path) env submcs
    in

    let (_, mc), submcs = mc_of_module env me in
    let env = bind Px.for_module env EcPath.PKmodule x me in
    let env = bind_mc env me.me_name mc in

      bind_submcs env
        (EcPath.pqname (EcPath.path_of_mpath env.env_scope) me.me_name)
        submcs

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
              (env, empty_premc []) cth.cth_struct
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
          (env, empty_premc [])
          cth.cth_struct
end

(* -------------------------------------------------------------------- *)
let enter (name : symbol) (k : EcPath.path_kind) params (env : env) =
  assert (List.uniq params);

  let params = List.map EcPath.mident params in
  let path   = EcPath.mqname env.env_scope k name params in
  let env    = MC.bind_mc env name (empty_premc []) in

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
  let actmem_name = function
    | AMAbstract x -> x
    | AMConcrete (_, m) -> EcMemory.memory m

  let byid (me : memory) (env : env) =
    let memories = MMsym.all (EcIdent.name me) env.env_memories in
    let memories =
      List.filter
        (fun me' -> EcIdent.id_equal me (actmem_name me'))
        memories
    in
      match memories with
      | []     -> None
      | m :: _ -> Some m

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

  let push (me : actmem) (env : env) =
    (* FIXME: assert (byid (actmem_name me) env = None); *)

    let id = actmem_name me in
    let maps =
      MMsym.add (EcIdent.name id) me env.env_memories
    in
      { env with env_memories = maps }

  let push_all memenvs env =
    List.fold_left
      (fun env (p, m) -> push (AMConcrete (p, m)) env)
      env memenvs

  let concretize mpath memenv env =
    let id = EcMemory.memory memenv in

    match byid id env with
    | None ->  raise (MEError (UnknownMemory (`Memory id)))
    | Some (AMConcrete _) -> failwith "memory-is-already-concrete"

    | Some (AMAbstract _) ->
        { env with
            env_memories =
              MMsym.add (EcIdent.name id) (AMConcrete (mpath, memenv))
                env.env_memories }
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

  let lookup_progvar ?side qname env =
    let inmem side =
      match fst qname with
      | [] -> begin
         match oget (Memory.byid side env) with
         | AMAbstract _ -> None
         | AMConcrete (mp, memenv) -> begin
             match EcMemory.lookup (snd qname) memenv with
             | None    -> None
             | Some ty ->
                 let pv =
                   { pv_name = EcPath.mqname mp EcPath.PKother (snd qname) [];
                     pv_kind = PVloc; }
                 in
                   Some (pv, ty)
           end
        end

      | _ -> None
    in

      match obind side inmem with
      | None -> begin
          let (p, x) = MC.lookup Px.for_variable qname env in
            if is_suspended x then
              raise (LookupFailure (`QSymbol qname));
            let x = x.sp_target in
              ({ pv_name = p; pv_kind = x.vb_kind }, x.vb_type)
        end

      | Some (pv, ty) -> (pv, ty)

  let lookup_progvar_opt ?side name env =
    try_lf (fun () -> lookup_progvar ?side name env)

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

  let sp_lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_function name env in
      (EcPath.path_of_mpath p, x)

  let sp_lookup_opt name env =
    try_lf (fun () -> sp_lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name fun_ env =
    MC.bind_function name fun_ env

  let add (path : EcPath.mpath) (env : env) =
    let obj = by_mpath path env in 
    MC.import Px.for_function env path obj

  let memenv ~hasres me path env =
    let fun_ = (by_path path env).sp_target in
    let adds =
      List.fold_left
        (fun memenv vd -> EcMemory.bind vd.v_name vd.v_type memenv)
    in

    let mem = EcMemory.empty me in
    let mem = adds mem (fst fun_.f_sig.fs_sig) in
    let mem =
      match fun_.f_def with
      | None   -> mem
      | Some d -> adds mem d.f_locals in
    let mem =
      if   hasres
      then adds mem [{v_name = "$res"; v_type = snd fun_.f_sig.fs_sig}] 
      else mem
    in
      mem

  let memenv_opt ~hasres me path env =
    try_lf (fun () -> memenv ~hasres me path env)

  let enter ~hasres me path env =
    let memenv =
      memenv hasres me (EcPath.path_of_mpath path) env
    in

    let env =
      Memory.set_active me 
        (Memory.push (AMConcrete (path, memenv)) env)
    in
      (memenv, env)
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

  let reducible env p = 
    try 
      let op = by_path p env in
      match op.op_kind with
      | OB_oper(Some _) | OB_pred(Some _) -> true
      | _ -> false 
    with _ -> false

  let reduce env p tys =
    let op = try by_path p env with _ -> assert false in
    let s = EcFol.Fsubst.init_subst_tvar (EcTypes.Tvar.init op.op_params tys) in
    let ids, f = 
      match op.op_kind with
      | OB_oper(Some(ids,e)) -> (ids, EcFol.form_of_expr EcFol.mhr e)
      | OB_pred(Some idsf) -> idsf
      | _ -> raise NotReducible in
    let bd = List.map2 (fun id ty -> id, GTty ty) ids op.op_dom in 
    EcFol.f_subst s (f_lambda bd f)
    
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

  let sp_lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_module name env in
      (p, x)

  let sp_lookup_opt name env =
    try_lf (fun () -> sp_lookup name env)

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
      let modsig =
        check_not_suspended
          (MC.lookup_by_path
             Px.for_modtype.Px.px_premc modty.mt_name env)
      in
        match modty.mt_args with
        | None -> modsig
        | Some args -> begin
          assert (List.length modsig.mis_params = List.length args);
          let subst =
            List.fold_left2
              (fun s (mid, _) arg ->
                EcSubst.add_module s mid arg)
              EcSubst.empty modsig.mis_params args
          in
            { (EcSubst.subst_modsig subst modsig) with mis_params = []; }
        end
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

  let mtype_string (m : module_type) =
    Printf.sprintf "%s(%s)"
      (EcPath.tostring m.mt_name)
      (String.concat ", " (List.map EcPath.m_tostring (odfl [] m.mt_args)))

  let mod_type_equiv (env : env) (mty1 : module_type) (mty2 : module_type) =
       (EcPath.p_equal mty1.mt_name mty2.mt_name)
    && oall2
         (List.all2
            (fun m1 m2 ->
               let m1 = Mod.unfold_mod_path env m1 in
               let m2 = Mod.unfold_mod_path env m2 in
                 EcPath.m_equal m1 m2))
         mty1.mt_args mty2.mt_args

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
  let bindx name th env =
    let rec compile1 path w3env item =
      let xpath = fun x -> EcPath.pqname path x in
        match item with
        | CTh_type     (x, ty) -> EcWhy3.add_ty w3env (xpath x) ty
        | CTh_operator (x, op) -> EcWhy3.add_op w3env (xpath x) op
        | CTh_axiom    (x, ax) -> EcWhy3.add_ax w3env (xpath x) ax
        | CTh_modtype  (_, _)  -> (w3env, [])
        | CTh_module   me      -> EcWhy3.add_mod_exp w3env (xpath me.me_name) me
        | CTh_export   _       -> (w3env, [])
        | CTh_theory (x, th)   -> compile (xpath x) w3env th

    and compile path w3env cth =
      let (w3env, rb) =
        List.map_fold (compile1 path) w3env cth.cth_struct
      in
        (w3env, List.rev (List.flatten rb))
    in

    let cpath = EcPath.path_of_mpath env.env_scope in
    let (w3env, rb) = compile (EcPath.pqname cpath name) env.env_w3 th in

    let env = MC.bind_theory name th env in
      { env with
          env_w3   = w3env;
          env_rb   = rb @ env.env_rb;
          env_item = (CTh_theory (name, th)) :: env.env_item; }

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
          MMsym.add x thpath env.env_current.amc_components; }
    in

    let comps = env.env_comps in
    let comps = Mp.add rootnm topmc comps in
    let comps = Mp.add thpath thmc  comps in

    { env with
        env_current = current;
        env_comps   = comps;
        env_w3      = EcWhy3.rebind env.env_w3 cth.cth3_rebind; }

  (* ------------------------------------------------------------------ *)
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


let norm_pvar env pv = 
  let p = Mod.unfold_mod_path env pv.pv_name in
  if m_equal p pv.pv_name then pv else { pv_name = p; pv_kind = pv.pv_kind }

let norm_form env =
  let norm_mp = EcPath.Hm.memo 107 (Mod.unfold_mod_path env) in
  let norm_pv pv = 
    let p = norm_mp pv.pv_name in
    if m_equal p pv.pv_name then pv else { pv_name = p; pv_kind = pv.pv_kind } in
  let norm_form = 
    EcFol.Hf.memo_rec 107 (fun aux f ->
      match f.f_node with
      | Fquant(q,bd,f) ->               (* FIXME: norm module_type *)
          f_quant q bd (aux f)

      | Fpvar(p,m) -> 
          let p' = norm_pv p in
          if p == p' then f else 
          f_pvar p' f.f_ty m

      | FhoareF(pre,p,post) ->
          let pre' = aux pre and p' = norm_mp p and post' = aux post in
          if pre == pre' && p == p' && post == post' then f else
          f_hoareF pre' p' post'

      |  FhoareS _ -> assert false (* FIXME ? Not implemented *)

      | FequivF(pre,(l,r),post) ->
          let pre' = aux pre and l' = norm_mp l 
          and r' = norm_mp r and post' = aux post in
          if pre == pre' && l == l' && r == r' && post == post' then f else
          f_equivF pre' l' r' post' 

      | FequivS _ -> assert false (* FIXME ? Not implemented *)

      | Fpr(m,p,args,e) ->
          let p' = norm_mp p and args' = List.smart_map aux args 
          and e' = aux e in
          if p == p' && args == args' && e == e' then f else 
          f_pr m p' args' e' 
      | _ -> EcFol.f_map (fun ty -> ty) aux f) in
  norm_form

let norm_l_decl env (hyps,concl) = 
  let norm = norm_form env in
  let onh (x,lk) = 
    match lk with
    | LD_var (ty,o) -> x, LD_var (ty, omap o norm)
    | LD_mem -> x, lk
    | LD_modty _ -> x, lk
    | LD_hyp f -> x, LD_hyp (norm f) in
  ({ hyps with h_local = List.map onh hyps.h_local}, norm concl)

let check_goal env pi ld = 
  EcWhy3.check_goal env.env_w3 pi (norm_l_decl env ld)

(* -------------------------------------------------------------------------- *)
(*
type judgment_uc = EcBaseLogic.judgment_uc 

type goals = judgment_uc * int list

type goal = judgment_uc * int 

type tactic = goal -> goals 

let open_juc = EcBaseLogic.open_juc

let t_id = EcBaseLogic.t_id 

let t_on_goals = EcBaseLogic.t_on_goals 

let t_seq = EcBaseLogic.t_seq 
let t_lseq = EcBaseLogic.t_lseq 

let t_subgoal = EcBaseLogic.t_subgoal 

let t_on_nth = EcBaseLogic.t_on_nth 

let t_on_first = EcBaseLogic.t_on_first 

let t_on_last = EcBaseLogic.t_on_first 

let t_seq_subgoal = EcBaseLogic.t_seq_subgoal

let get_goal g = (get_open_goal g).pj_decl
let get_hyps g = fst (get_goal g) 
let get_concl g = snd (get_goal g)

let t_admit =
  let rule = { pr_name = RN_admit; pr_hyps = [] } in
  upd_rule_done rule 

let t_clear id (juc,_ as g) = 
  let hyps,concl = get_goal g in
  let hyps = LDecl.clear id hyps in
  assert (not (Mid.mem id concl.f_fv));
  let juc,n1 = new_goal juc (hyps,concl) in
  let rule = { pr_name = RN_clear id; pr_hyps = [RA_id id;RA_node n1] } in
  upd_rule rule g 

let bind s x x' gty = 
  match gty with 
  | GTty ty    -> bind_local s x (f_local x' ty), LD_var (ty, None)
  | GTmodty mt -> bind_mod s x (EcPath.mident x'), LD_modty mt
  | GTmem      -> bind_mem s x x', LD_mem

let get_intros env hyps ids concl =
  let rec aux hyps ids s concl = 
    match ids with
    | [] -> hyps, EcFol.f_subst s concl 
    | x'::ids' ->
      match concl.f_node with
      | Fquant(Lforall, _, _) ->
        let (x,gty,concl) = EcFol.destr_forall1 concl in
	let s,lk = bind s x x' gty in
        let hyps = LDecl.add_local x' lk hyps in
        aux hyps ids' s concl
      | Flet(LSymbol(x,ty),e1,e2) ->
        let e1 = f_subst s e1 in
        let s = bind_local s x (f_local x' ty) in
        let hyps = LDecl.add_local x' (LD_var(ty,Some e1)) hyps in
        aux hyps ids' s concl
      | _ when is_imp concl ->
        let f,concl = destr_imp concl in
        let hyps = LDecl.add_local x' (LD_hyp (f_subst s f)) hyps in
        aux hyps ids' s concl
      | _ -> 
        if is_reducible env hyps concl then
          let concl = red env hyps concl in
          aux hyps ids s concl 
        else assert false (* FIXME : error message *)
  in
  aux hyps ids f_subst_id concl

let t_intros env ids (juc,_ as g) =
  let hyps,concl = get_goal g in
  let hyps,concl = get_intros env ids concl in
  let juc,n1     = new_goal juc (hyps,concl) in 
  let rule = { pr_name = RN_intros;
               pr_hyps = List.map (fun x -> RA_id x) ids @ [RA_node n1] } in
  upd_rule rule g
    
(*
let process_app_f env hyps juc app_f =
  match app_f with
  | AFform f -> 
    check_type f.f_t_ty tbool;
    let juc, n = new_goal juc (hyps,f) in
    juc, f, RA_node n 
  | AFhyp  id -> 
    let f = LDecl.lookup_hyp_by_id id hyps in
    juc, f, RA_id id  
  | AFglob (p,tys) ->
    let 

    of EcPath.path * ty list 
*)

  
let t_apply env app_f app_args (juc,_ as g) =
  let hyps, concl = get_goal g in
  let juc, s, f = process_app_f juc app_f in
  foo
(* (A => B) => A => B *)
*)
