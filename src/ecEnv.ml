(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcTypes
open EcFol
open EcDecl
open EcTypesmod
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
  not (List.for_all (fun ps -> ps <> []) x.sp_params)

let check_not_suspended (x : 'a suspension) =
  if is_suspended x then
    raise IsSuspended;
  x.sp_target

(* -------------------------------------------------------------------- *)
type lookup_failure = [
  | `Path    of epath
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
  vb_kind  : EcTypes.pvar_kind option;
}

type preenv = {
  env_scope   : EcPath.path;
  env_current : activemc;
  env_comps   : premc EcPath.Mp.t;
  env_bcomps  : premc EcIdent.Mid.t;
  env_w3      : EcWhy3.env;
  env_rb      : EcWhy3.rebinding;        (* in reverse order *)
  env_item    : ctheory_item list        (* in reverse order *)
}

and premc = {
  mc_parameters : (EcIdent.t * module_type)        list;
  mc_variables  : (epath * varbind)                Msym.t;
  mc_functions  : (epath * EcTypesmod.function_)   Msym.t;
  mc_modules    : ( cref * EcTypesmod.module_expr) Msym.t;
  mc_modtypes   : ( path * EcTypesmod.module_sig)  Msym.t;
  mc_typedecls  : ( path * EcDecl.tydecl)          Msym.t;
  mc_operators  : ( path * EcDecl.operator)        Msym.t;
  mc_axioms     : ( path * EcDecl.axiom)           Msym.t;
  mc_theories   : ( path * EcTypesmod.ctheory)     Msym.t;
  mc_components : path                            Msym.t;
}

and activemc = {
  amc_variables  : (epath * varbind)                MMsym.t;
  amc_functions  : (epath * EcTypesmod.function_)   MMsym.t;
  amc_modules    : ( cref * EcTypesmod.module_expr) MMsym.t;
  amc_modtypes   : ( path * EcTypesmod.module_sig)  MMsym.t;
  amc_typedecls  : ( path * EcDecl.tydecl)          MMsym.t;
  amc_operators  : ( path * EcDecl.operator)        MMsym.t;
  amc_axioms     : ( path * EcDecl.axiom)           MMsym.t;
  amc_theories   : ( path * EcTypesmod.ctheory)     MMsym.t;
  amc_components : cref                             MMsym.t;
}

and mc =
| PreMc of premc
| ActMc of activemc

let premc = fun (mc : premc   ) -> PreMc mc
let actmc = fun (mc : activemc) -> ActMc mc

let epath_of_cref = function
  | EcPath.CRefPath p   -> EPath p
  | EcPath.CRefMid  mid -> EModule (mid, None)

let cref_of_epath = function
  | EcPath.EPath   p        -> CRefPath p
  | EcPath.EModule (mid, _) -> CRefMid  mid

let epath_of_path p = EPath p

let path_of_epath = function
  | EcPath.EPath p -> p
  | _ -> assert false

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
  let path = EcPath.pident EcCoreLib.id_top
  and name = EcCoreLib.id_top in
  let env  =
    { env_scope   = path;
      env_current = { empty_activemc with
                        amc_components =
                          MMsym.add name (CRefPath path) MMsym.empty; };
      env_comps   = Mp.singleton (EcPath.pident name) empty_premc;
      env_bcomps  = Mid.empty;
      env_w3      = EcWhy3.empty;
      env_rb      = [];
      env_item    = [];
    }
  in
    env

(* -------------------------------------------------------------------- *)
let preenv (env : preenv) : env = env

(* -------------------------------------------------------------------- *)
let root (env : env) = env.env_scope

(* -------------------------------------------------------------------- *)
module Dump = struct
  let rec dump ?(name = "Environment") pp (env : env) =
      EcDebug.onseq pp name ~extra:(EcPath.tostring env.env_scope)
        (Stream.of_list [
          (fun pp -> dump_amc ~name:"Root" pp env.env_current);
          (fun pp ->
             Mp.dump ~name:"Components"
               (fun k _ -> EcPath.tostring k)
               (fun pp (_, mc) ->
                  dump_premc ~name:"Component" pp mc)
               pp env.env_comps);
          (fun pp ->
             Mid.dump ~name:"B-Components"
               (fun k _ -> EcIdent.tostring k)
               (fun pp (_, mc) ->
                  dump_premc ~name:"B-Component" pp mc)
               pp env.env_bcomps)
        ])
  
  and dump_premc ~name pp mc =
    let ppkey_path  _ (p, _) = EcPath.tostring      p
    and ppkey_epath _ (p, _) = EcPath.ep_tostring   p
    and ppkey_cref  _ (p, _) = EcPath.cref_tostring p
    and ppkey_comps _ p      = EcPath.tostring      p

    and ppval _ _ = () in
  
    EcDebug.onseq pp name
      (Stream.of_list [
         (fun pp -> Msym.dump ~name:"Variables"  ppkey_epath ppval pp mc.mc_variables );
         (fun pp -> Msym.dump ~name:"Functions"  ppkey_epath ppval pp mc.mc_functions );
         (fun pp -> Msym.dump ~name:"Modules"    ppkey_cref  ppval pp mc.mc_modules   );
         (fun pp -> Msym.dump ~name:"Modtypes"   ppkey_path  ppval pp mc.mc_modtypes  );
         (fun pp -> Msym.dump ~name:"Typedecls"  ppkey_path  ppval pp mc.mc_typedecls );
         (fun pp -> Msym.dump ~name:"Operators"  ppkey_path  ppval pp mc.mc_operators );
         (fun pp -> Msym.dump ~name:"Axioms"     ppkey_path  ppval pp mc.mc_axioms    );
         (fun pp -> Msym.dump ~name:"Theories"   ppkey_path  ppval pp mc.mc_theories  );
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
  let top_path = EcPath.pident EcCoreLib.id_top

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

  (* Direct lookup of the components of a module parameters
   * via its unique identifier *)
  let lookup_mc_by_mid (env : env) (mid : EcIdent.t) =
    Mid.find_opt mid env.env_bcomps

  (* Lookup object referenced by path [path]. If path is reduced
   * to an identifier, use <top> as the path prefix. [proj]
   * should project the final component to the desired objects
   * map. *)
  let lookup_by_path proj (path : EcPath.path) (env : env) =
    let symbol = EcPath.basename path
    and scname = odfl top_path (EcPath.prefix path) in
    let mc     = lookup_mc_by_path env scname in

      match mc with
      | None -> raise (LookupFailure (`Path (EPath path)))
      | Some (mc, params) -> begin
          match Msym.find_opt symbol (proj mc) with
          | None        -> raise (LookupFailure (`Path (EPath path)))
          | Some (_, x) -> suspend x params
      end

  (* ------------------------------------------------------------------ *)
  module Px = struct
    type ('p, 'a) projector = {
      (* Selecting / updating in a [premc] *)
      px_premc   : premc -> ('p * 'a) Msym.t;
      px_topremc : ('p * 'a) Msym.t -> premc -> premc;

      (* Selecting / updating in a [activemc] *)
      px_actmc   : activemc -> ('p * 'a) MMsym.t;
      px_toactmc : ('p * 'a) MMsym.t -> activemc -> activemc;

      (* epath/path embedding *)
      px_aptx : 'p   -> epath;
      px_patx : path -> 'p;
    }

    (* ---------------------------------------------------------------- *)
    let for_variable : (epath, varbind) projector = {
      px_premc   = (fun mc -> mc.mc_variables);
      px_topremc = (fun m mc -> { mc with mc_variables = m });
      px_actmc   = (fun mc -> mc.amc_variables);
      px_toactmc = (fun m mc -> { mc with amc_variables = m });
      px_aptx    = (fun (p : epath) -> p);
      px_patx    = (fun (p :  path) -> EPath p);
    }

    let for_function : (epath, EcTypesmod.function_) projector = {
      px_premc   = (fun mc -> mc.mc_functions);
      px_topremc = (fun m mc -> { mc with mc_functions = m });
      px_actmc   = (fun mc -> mc.amc_functions);
      px_toactmc = (fun m mc -> { mc with amc_functions = m });
      px_aptx    = (fun (p : epath) -> p);
      px_patx    = (fun (p :  path) -> EPath p);
    }

    let for_module : (cref, EcTypesmod.module_expr) projector = {
      px_premc   = (fun mc -> mc.mc_modules);
      px_topremc = (fun m mc -> { mc with mc_modules = m });
      px_actmc   = (fun mc -> mc.amc_modules);
      px_toactmc = (fun m mc -> { mc with amc_modules = m });
      px_aptx    = epath_of_cref;
      px_patx    = (fun (p :  path) -> CRefPath p);
    }

    let for_modtype : (path, EcTypesmod.module_sig) projector = {
      px_premc   = (fun mc -> mc.mc_modtypes);
      px_topremc = (fun m mc -> { mc with mc_modtypes = m });
      px_actmc   = (fun mc -> mc.amc_modtypes);
      px_toactmc = (fun m mc -> { mc with amc_modtypes = m });
      px_aptx    = epath_of_path;
      px_patx    = (fun (p :  path) -> p);
    }

    let for_typedecl : (path, EcDecl.tydecl) projector = {
      px_premc   = (fun mc -> mc.mc_typedecls);
      px_topremc = (fun m mc -> { mc with mc_typedecls = m });
      px_actmc   = (fun mc -> mc.amc_typedecls);
      px_toactmc = (fun m mc -> { mc with amc_typedecls = m });
      px_aptx    = epath_of_path;
      px_patx    = (fun (p :  path) -> p);
    }

    let for_operator : (path, EcDecl.operator) projector = {
      px_premc   = (fun mc -> mc.mc_operators);
      px_topremc = (fun m mc -> { mc with mc_operators = m });
      px_actmc   = (fun mc -> mc.amc_operators);
      px_toactmc = (fun m mc -> { mc with amc_operators = m });
      px_aptx    = epath_of_path;
      px_patx    = (fun (p :  path) -> p);
    }

    let for_axiom : (path, EcDecl.axiom) projector = {
      px_premc   = (fun mc -> mc.mc_axioms);
      px_topremc = (fun m mc -> { mc with mc_axioms = m });
      px_actmc   = (fun mc -> mc.amc_axioms);
      px_toactmc = (fun m mc -> { mc with amc_axioms = m });
      px_aptx    = epath_of_path;
      px_patx    = (fun (p :  path) -> p);
    }

    let for_theory : (path, EcTypesmod.ctheory) projector = {
      px_premc   = (fun mc -> mc.mc_theories);
      px_topremc = (fun m mc -> { mc with mc_theories = m });
      px_actmc   = (fun mc -> mc.amc_theories);
      px_toactmc = (fun m mc -> { mc with amc_theories = m });
      px_aptx    = epath_of_path;
      px_patx    = (fun (p :  path) -> p);
    }
  end

  (* Lookup a compoments using a [symbol list] (scope), i.e. starting
   * from the compoment [env_root]. *)

  let path_of_qn (top : EcPath.path) (qn : symbol list) =
    List.fold_left
      (fun p x -> EcPath.pqname (p, x)) top qn
      
  let lookup_mc (qn : symbol list) (env : env) =
    match qn with
    | [] -> Some (ActMc env.env_current)

    | top :: qn ->
        match MMsym.last top env.env_current.amc_components with
        | None -> None
        | Some cref -> begin
            match cref with
            | CRefMid mid ->
                if qn = [] then
                  let mc = oget (lookup_mc_by_mid env mid) in
                    Some (PreMc mc)
                else None

            | CRefPath p ->
                let p = path_of_qn p qn in
                  omap (Mp.find_opt p env.env_comps) premc
          end

  (* ------------------------------------------------------------------ *)

  (* Direct lookup in a [container] using a [projector]. Returns only
   * last inserted object bound to the given name. *)
  let mc_lookup1 px x mc =
    match mc with
    | PreMc mc ->
        omap
          (Msym.find_opt x (px.Px.px_premc mc))
          (fun (p, obj) -> (px.Px.px_aptx p, obj))

    | ActMc mc ->
        omap
          (MMsym.last x (px.Px.px_actmc mc))
          (fun (p, obj) -> (px.Px.px_aptx p, obj))

  (* Direct lookup in a [container] using a [projector]. Returns all
   * the object bound to the given name. *)
  let mc_lookupall px x mc =
    match mc with
    | PreMc mc ->
        otolist (omap
          (Msym.find_opt x (px.Px.px_premc mc))
          (fun (p, obj) -> (px.Px.px_aptx p, obj)))

    | ActMc mc ->
        List.map
          (fun (p, obj) -> (px.Px.px_aptx p, obj))
          (MMsym.all x (px.Px.px_actmc mc))


  (* Lookup an object using a [qsymbol], i.e. starting from
   * the compoment [env_current]. The object returned is suspended. *)

  let _params_of_epath (env : env) (epath : epath) =
    match epath with
    | EPath p ->
        let prefix = oget (EcPath.prefix p) in
          snd (oget (lookup_mc_by_path env prefix))

    | EModule _ -> []

  let lookup px ((qn, x) : qsymbol) (env : env) =
    match lookup_mc qn env with
    | None ->
        raise (LookupFailure (`QSymbol (qn, x)))

    | Some mc -> begin
        match mc_lookup1 px x mc with
        | None ->
            raise (LookupFailure (`QSymbol (qn, x)))

        | Some (p, obj) ->
            (p, suspend obj (_params_of_epath env p))
      end

  let lookupall px ((qn, x) : qsymbol) (env : env) =
    match lookup_mc qn env with
    | None -> raise (LookupFailure (`QSymbol (qn, x)))
    | Some mc ->
        List.map
          (fun (p, obj) -> (p, suspend obj (_params_of_epath env p)))
          (mc_lookupall px x mc)

  (* Binding of an object in a [premc]. Fails if a binding already
   * exists for the given name and name. *)

  let mc_bind_raw px name path obj mc =
    let map = px.Px.px_premc mc in
      match Msym.find_opt name map with
      | Some _ -> raise (DuplicatedBinding name)
      | None   -> px.Px.px_topremc (Msym.add name (path, obj) map) mc

  let mc_bind px path obj mc =
    mc_bind_raw px (EcPath.basename path) (px.Px.px_patx path) obj mc

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

  let amc_bind_mc (path : EcPath.cref) mc =
    let name =
      match path with
      | CRefPath path -> EcPath.basename path
      | CRefMid  mid  -> EcIdent.name mid
    in
      { mc with
          amc_components = MMsym.add name path mc.amc_components; }

  (* ------------------------------------------------------------------ *)
  let mc_of_module (env : env) (me : module_expr) =
    let xpath =
      let scope = EcPath.pqname (env.env_scope, me.me_name) in
        fun x -> EcPath.pqname (scope, x)
    in

    let mc1_of_module (mc : premc) = function
      | MI_Module me ->
          mc_bind_module (xpath me.me_name) me mc

      | MI_Variable v ->
          let vty =
            { vb_type = v.v_type;
              vb_kind = Some PVglob; }
          in
            mc_bind_variable (xpath v.v_name) vty mc

      | MI_Function f ->
          mc_bind_function (xpath f.f_name) f mc

    in
      List.fold_left mc1_of_module empty_premc me.me_comps

  (* ------------------------------------------------------------------ *)
  let mc_of_module_param (mid : EcIdent.t) (me : module_expr) =
    let xpath (x : symbol) = EcPath.EModule (mid, Some x) in

    let mc1_of_module (mc : premc) = function
      | MI_Module _ -> assert false

      | MI_Variable v ->
          let vty =
            { vb_type = v.v_type;
              vb_kind = Some PVglob; }
          in
            mc_bind_raw Px.for_variable v.v_name (xpath v.v_name) vty mc


      | MI_Function f ->
          mc_bind_raw Px.for_function f.f_name (xpath f.f_name) f mc
    in
      List.fold_left mc1_of_module empty_premc me.me_comps

  (* ------------------------------------------------------------------ *)
  let bind px env name obj =
    let path = EcPath.pqname (env.env_scope, name) in
      { env with
          env_current =
            amc_bind px name (px.Px.px_patx path) obj env.env_current;
          env_comps =
            Mp.change
              (fun mc -> Some (mc_bind px path obj (oget mc)))
              env.env_scope env.env_comps; }

  (* -------------------------------------------------------------------- *)
  let bind_mc env name comps =
    let path = EcPath.pqname (env.env_scope, name) in

      if Mp.find_opt path env.env_comps <> None then
        raise (DuplicatedBinding name);

      { env with
          env_current = amc_bind_mc (CRefPath path) env.env_current;
          env_comps =
            Mp.change
              (fun mc -> Some (mc_bind_mc path (oget mc)))
              env.env_scope
              (Mp.add path comps env.env_comps); }

  (* -------------------------------------------------------------------- *)
  let import px env path obj =
    { env with
        env_current =
          amc_bind px
            (EcPath.basename path) (px.Px.px_patx path)
            obj env.env_current; }

  (* ------------------------------------------------------------------ *)
  let rec bind_variable x ty env =
    bind Px.for_variable env x ty

  and bind_function x fsig env =
    bind Px.for_function env x fsig

  and bind_module x me env =
    let comps = mc_of_module env me in
    let env   = bind Px.for_module env x me in
    let env   = bind_mc env x comps in
      env

  and bind_modtype x tymod env =
    bind Px.for_modtype env x tymod

  and bind_typedecl x tydecl env =
    bind Px.for_typedecl env x tydecl

  and bind_operator x op env =
    bind Px.for_operator env x op

  and bind_axiom x ax env =
    bind Px.for_axiom env x ax

  and bind_theory x cth env =
    let env, comps = mc_of_ctheory env env.env_scope x cth in
    let env = bind Px.for_theory env x cth in
    let env = bind_mc env x comps in
      env

  and mc_of_ctheory =
    let rec mc_of_ctheory_struct path (env, mc) = function 
      | CTh_type     (x, td)  -> env, mc_bind_typedecl (EcPath.pqname (path, x)) td mc
      | CTh_operator (x, op)  -> env, mc_bind_operator (EcPath.pqname (path, x)) op mc
      | CTh_axiom    (x, ax)  -> env, mc_bind_axiom    (EcPath.pqname (path, x)) ax mc
      | CTh_modtype  (x, tm)  -> env, mc_bind_modtype  (EcPath.pqname (path, x)) tm mc
      | CTh_module   m        -> env, mc_bind_module   (EcPath.pqname (path, m.me_name)) m mc
      | CTh_export   _        -> env, mc
      | CTh_theory   (x, cth) ->
          let env, submc =
            List.fold_left
              (mc_of_ctheory_struct (EcPath.pqname (path, x)))
              (env, empty_premc) cth.cth_struct
          and subpath = EcPath.pqname (path, x) in
  
          let env =
            let comps = env.env_comps in
            let comps = Mp.add subpath submc comps in
              { env with env_comps = comps }
          in
            (env, mc_bind_mc subpath (mc_bind_theory subpath cth mc))
    in
      fun (env : env) (path : EcPath.path) (x : symbol) (cth : ctheory) ->
        List.fold_left
          (mc_of_ctheory_struct (EcPath.pqname (path, x)))
          (env, empty_premc)
          cth.cth_struct
end

(* -------------------------------------------------------------------- *)
let enter (name : symbol) (env : env) =
  let path = EcPath.pqname (env.env_scope, name) in
  let env  = MC.bind_mc env name empty_premc in
    { env with
        env_scope = path;
        env_w3    = env.env_w3;
        env_rb    = [];
        env_item  = []; }

(* -------------------------------------------------------------------- *)
module Var = struct
  module Px = MC.Px

  type t = varbind

  let by_path (p : EcPath.path) (env : env) =
    let x = MC.lookup_by_path Px.for_variable.Px.px_premc p env in
      (* Variables do NOT depend on module parameters *)
      x.sp_target

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_variable name env in
      (* Variables do NOT depend on module parameters *)
      (cref_of_epath p, x.sp_target)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let lookup_locals name env =
    let bindings =
      List.map
        (fun (p, x) -> (cref_of_epath p, x.vb_type))
        (MC.mc_lookupall Px.for_variable name (ActMc env.env_current))
    in
      List.pmap
        (fun (p, x) ->
           match p with
           | EcPath.CRefMid mid -> Some (mid, x)
           | _ -> None)
        bindings

  let lookup_local name env =
    match lookup_locals name env with
    | []     -> raise (LookupFailure (`QSymbol ([], name)))
    | x :: _ -> x

  let lookup_local_opt name env =
    try_lf (fun () -> lookup_local name env)

  let lookup_progvars qname env =
    let bindings =
      List.map
        (fun (p, x) -> (p, x.sp_target))
        (MC.lookupall Px.for_variable qname env)
    in

      List.pmap
        (fun (p, x) ->
           match x.vb_kind with
           | None    -> None
           | Some kd -> Some ({ pv_name = p; pv_kind = kd }, x.vb_type))
        bindings

  let lookup_progvar qname env =
    match lookup_progvars qname env with
    | []     -> raise (LookupFailure (`QSymbol qname))
    | x :: _ -> x

  let lookup_progvar_opt name env =
    try_lf (fun () -> lookup_progvar name env)

  let bind name pvkind ty env =
    let vb = { vb_type = ty; vb_kind = Some pvkind; } in
      MC.bind_variable name vb env

  let bindall bindings pvkind env =
    List.fold_left
      (fun env (name, ty) -> bind name pvkind ty env)
      env bindings

  let bind_local name ty env =
    let var  = { vb_type = ty; vb_kind = None; }
    and path = EModule (name, None) in

      { env with
          env_current =
            MC.amc_bind Px.for_variable (EcIdent.name name) path
              var env.env_current; }

  let bind_locals bindings env =
    List.fold_left
      (fun env (name, ty) -> bind_local name ty env)
      env bindings

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
      MC.import Px.for_variable env path obj
end

(* -------------------------------------------------------------------- *)
module Fun = struct
  module Px = MC.Px

  type t = EcTypesmod.function_

  let by_path (p : EcPath.path) (env : env) =
    let obj = MC.lookup_by_path Px.for_function.Px.px_premc p env in
      if is_suspended obj then
        raise (LookupFailure (`Path (EPath p)));
      obj.sp_target

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

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

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
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
      (path_of_epath p, check_not_suspended x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
      MC.import Px.for_typedecl env path obj

  let bind name ty env =
    let env = MC.bind_typedecl name ty env in
    let (w3, rb) =
        EcWhy3.add_ty env.env_w3
          (EcPath.extend (Some env.env_scope) name) ty
    in
      { env with
          env_w3   = w3;
          env_rb   = rb :: env.env_rb;
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
    | _ -> raise (LookupFailure (`Path (EPath name)))
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
      (path_of_epath p, check_not_suspended x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
      MC.import Px.for_operator env path obj

  let bind name op env =
    let env = MC.bind_operator name op env in
    let (w3, rb) =
        EcWhy3.add_op env.env_w3
          (EcPath.extend (Some env.env_scope) name) op
    in
      { env with
          env_w3   = w3;
          env_rb   = rb :: env.env_rb;
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
          (path_of_epath p, check_not_suspended op)) ops
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
      (path_of_epath p, check_not_suspended x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
      MC.import Px.for_axiom env path obj

  let bind name ax env = 
    let env = MC.bind_axiom name ax env in
    let (w3, rb) = 
      EcWhy3.add_ax env.env_w3
        (EcPath.extend (Some env.env_scope) name) ax
    in
      { env with
          env_w3   = w3;
          env_rb   = rb :: env.env_rb;
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
    | _ -> raise (LookupFailure (`Path (EPath p)))
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  type t = module_expr

  module Px = MC.Px

  let by_path (p : EcPath.path) (env : env) =
    let obj = MC.lookup_by_path Px.for_module.Px.px_premc p env in
      if is_suspended obj then
        raise (LookupFailure (`Path (EPath p)));
      obj.sp_target

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_module name env in
      if is_suspended x then
        raise (LookupFailure (`QSymbol name));
      (cref_of_epath p, x.sp_target)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name me env =
    assert (me.me_name = name);
    MC.bind_module name me env

  let bind_local name me env =
    let path  = CRefMid name in
    let comps = MC.mc_of_module_param name me  in
    let env   =
      { env with
          env_current = (
            let current = env.env_current in
            let current = MC.amc_bind_mc path current in
            let current = MC.amc_bind Px.for_module
                            (EcIdent.name name) path me current
            in
              current);
          env_bcomps =
            Mid.add name comps env.env_bcomps; }
    in
      Dump.dump EcDebug.initial env; env

  let bind_locals bindings env =
    List.fold_left
      (fun env (name, me) -> bind_local name me env)
      env bindings

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
      MC.import Px.for_module env path obj
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
      (path_of_epath p, check_not_suspended x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name modty env =
    MC.bind_modtype name modty env

  let add (path : EcPath.path) (env : env) =
    let obj = by_path path env in 
      MC.import Px.for_modtype env path obj
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
  let enter = enter

  (* ------------------------------------------------------------------ *)
  let by_path (p : EcPath.path) (env : env) =
    check_not_suspended
      (MC.lookup_by_path Px.for_theory.Px.px_premc p env)

  let by_path_opt (p : EcPath.path) (env : env) =
    try_lf (fun () -> by_path p env)

  let lookup name (env : env) =
    let (p, x) = MC.lookup Px.for_theory name env in
      (path_of_epath p, check_not_suspended x)

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
      let xpath x = EcPath.pqname (path, x) in
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
            MC.import Px.for_module env (xpath m.me_name) m

        | CTh_export p ->
            import env p (by_path p env)

        | CTh_theory (x, th) ->
            let env = MC.import Px.for_theory env (xpath x) th in
              { env with env_current =
                  MC.amc_bind_mc (CRefPath (xpath x)) env.env_current }
      in
        List.fold_left import_cth_item env cth.cth_struct

    in
      import env path (by_path path env)

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
    let thpath = EcPath.pqname (rootnm, x) in

    let env, thmc =
      MC.mc_of_ctheory env rootnm x cth.cth3_theory
    in

    let topmc = Mp.find rootnm env.env_comps in
    let topmc = {
      topmc with
        mc_theories   = Msym.add x (thpath, cth.cth3_theory) topmc.mc_theories;
        mc_components = Msym.add x thpath topmc.mc_components; }
    in

    let current = {
      env.env_current with
        amc_theories =
          MMsym.add x (thpath, cth.cth3_theory)
            env.env_current.amc_theories;
        amc_components =
          MMsym.add x (EcPath.CRefPath thpath)
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
      MC.import Px.for_theory env path obj
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
  let env = enter EcCoreLib.id_pervasive env0 in
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
  let tdistr = { tyd_params = [ EcIdent.create "'a" ]; tyd_type = None } in
  let env = Ty.bind (EcPath.basename EcCoreLib.p_distr) tdistr env in 
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
    | Fpvar(p1,s1), Fpvar(p2,s2) when pv_equal p1 p2 && s1 = s2 -> ()
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
