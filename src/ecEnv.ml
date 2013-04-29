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
type 'a suspension = {
  sp_target : 'a;
  sp_params : int * (EcIdent.t * module_type) list;
}

(* -------------------------------------------------------------------- *)
type ctheory_w3 = {
  cth3_rebind : EcWhy3.rebinding;
  cth3_theory : ctheory;
}

let ctheory_of_ctheory_w3 (cth : ctheory_w3) =
  cth.cth3_theory

(* -------------------------------------------------------------------- *)
let check_not_suspended (params, obj) =
  if not (List.for_all (fun x -> x = None) params) then
    assert false;
  obj

(* -------------------------------------------------------------------- *)

(* Paths as stored in the environment:
 * - Either a full path (sequence of symbols)
 * - Either a ident (module variable) followed by a optional path (inner path)
 *
 * No functor applications are present in these paths.
 *)

type ipath =
| IPPath  of EcPath.path
| IPIdent of EcIdent.t * EcPath.path option

let ibasename p =
  match p with
  | IPPath p -> EcPath.basename p
  | IPIdent (m, None) -> EcIdent.name m
  | IPIdent (_, Some p) -> EcPath.basename p

let itostring = function
  | IPPath p -> EcPath.tostring p
  | IPIdent (m, None) -> EcIdent.tostring m
  | IPIdent (m, Some p) ->
      Printf.sprintf "%s.%s"
        (EcIdent.tostring m) (EcPath.tostring p)

module IPathC = struct
  type t = ipath

  let compare p1 p2 =
    match p1, p2 with
    | IPIdent _, IPPath  _ -> -1
    | IPPath  _, IPIdent _ ->  1

    | IPIdent (i1, p1), IPIdent (i2, p2) -> begin
        match EcIdent.id_compare i1 i2 with
        | 0 -> ocompare EcPath.p_compare p1 p2
        | i -> i
    end

    | IPPath p1, IPPath p2 ->
        EcPath.p_compare p1 p2
end

module Mip = EcMaps.Map.Make(IPathC)
module Sip = Mip.Set

(* -------------------------------------------------------------------- *)
type varbind = {
  vb_type  : EcTypes.ty;
  vb_kind  : EcTypes.pvar_kind;
}

type obj = [
  | `Variable of varbind
  | `Function of function_
  | `Module   of module_expr
  | `ModSig   of module_sig
  | `TypeDecl of EcDecl.tydecl
  | `Operator of EcDecl.operator
  | `Axiom    of EcDecl.axiom
  | `Theory   of ctheory
]

type mc = {
  mc_parameters : ((EcIdent.t * module_type) list) option;
  mc_variables  : (ipath * varbind) MMsym.t;
  mc_functions  : (ipath * function_) MMsym.t;
  mc_modules    : (ipath * module_expr) MMsym.t;
  mc_modsigs    : (ipath * module_sig) MMsym.t;
  mc_tydecls    : (ipath * EcDecl.tydecl) MMsym.t;
  mc_operators  : (ipath * EcDecl.operator) MMsym.t;
  mc_axioms     : (ipath * EcDecl.axiom) MMsym.t;
  mc_theories   : (ipath * ctheory) MMsym.t;
  mc_components : ipath MMsym.t;
}

(* -------------------------------------------------------------------- *)
type preenv = {
  env_scope    : EcPath.path;
  env_current  : mc;
  env_comps    : mc Mip.t;
  env_locals   : (EcIdent.t * EcTypes.ty) MMsym.t;
  env_memories : EcMemory.memenv MMsym.t;
  env_actmem   : EcMemory.memory option;
  env_w3       : EcWhy3.env;
  env_rb       : EcWhy3.rebinding;        (* in reverse order *)
  env_item     : ctheory_item list        (* in reverse order *)
}

(* -------------------------------------------------------------------- *)
type env = preenv

(* -------------------------------------------------------------------- *)
module Dump = struct
  let rec dump ?(name = "Environment") pp (env : env) =
      EcDebug.onseq pp name ~extra:(EcPath.tostring env.env_scope)
        (Stream.of_list [
          (fun pp -> dump_mc ~name:"Root" pp env.env_current);
          (fun pp ->
             Mip.dump ~name:"Components"
               (fun k mc ->
                 Printf.sprintf "%s (%s)"
                   (itostring k)
                   (match mc.mc_parameters with
                    | None   -> "none"
                    | Some p -> string_of_int (List.length p)))
               (fun pp (_, mc) ->
                  dump_mc ~name:"Component" pp mc)
               pp env.env_comps)
        ])

  and dump_mc ~name pp mc =
    EcDebug.onseq pp name
      (Stream.of_list [
         (fun pp -> MMsym.dump "Variables"  (fun _ _ -> ()) pp mc.mc_variables );
         (fun pp -> MMsym.dump "Functions"  (fun _ _ -> ()) pp mc.mc_functions );
         (fun pp -> MMsym.dump "Modules"    (fun _ _ -> ()) pp mc.mc_modules   );
         (fun pp -> MMsym.dump "Modtypes"   (fun _ _ -> ()) pp mc.mc_modsigs   );
         (fun pp -> MMsym.dump "Typedecls"  (fun _ _ -> ()) pp mc.mc_tydecls   );
         (fun pp -> MMsym.dump "Operators"  (fun _ _ -> ()) pp mc.mc_operators );
         (fun pp -> MMsym.dump "Axioms"     (fun _ _ -> ()) pp mc.mc_axioms    );
         (fun pp -> MMsym.dump "Theories"   (fun _ _ -> ()) pp mc.mc_theories  );
         (fun pp -> MMsym.dump "Components" (fun _ _ -> ()) pp mc.mc_components);
      ])
end

let dump = Dump.dump


(* -------------------------------------------------------------------- *)
let root (env : env) =
  env.env_scope

let mroot (env : env) =
  EcPath.mpath_crt env.env_scope [] None (* FIXME *)

(* -------------------------------------------------------------------- *)
let empty_mc params = {
  mc_parameters = params;
  mc_modules    = MMsym.empty;
  mc_modsigs    = MMsym.empty;
  mc_tydecls    = MMsym.empty;
  mc_operators  = MMsym.empty;
  mc_axioms     = MMsym.empty;
  mc_theories   = MMsym.empty;
  mc_variables  = MMsym.empty;
  mc_functions  = MMsym.empty;
  mc_components = MMsym.empty;
}

(* -------------------------------------------------------------------- *)
let empty =
  let name = EcCoreLib.id_top in
  let path = EcPath.psymbol name in

  let env  =
    { env_scope    = path;
      env_current  = { (empty_mc None) with
                         mc_components =
                           MMsym.add name (IPPath path) MMsym.empty; };
      env_comps    = Mip.singleton (IPPath path) (empty_mc None);
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
type lookup_error = [
  | `XPath   of xpath
  | `MPath   of mpath
  | `Path    of path
  | `QSymbol of qsymbol
]

exception LookupFailure of lookup_error

let lookup_error cause =
  raise (LookupFailure cause)

(* -------------------------------------------------------------------- *)
exception DuplicatedBinding of symbol

(* -------------------------------------------------------------------- *)
let unsuspend _ (_, o) _ = o

(* -------------------------------------------------------------------- *)
module MC = struct
  (* ------------------------------------------------------------------ *)
  let top_path = EcPath.psymbol EcCoreLib.id_top

  (* ------------------------------------------------------------------ *)
  let _cutpath i p =
    Printf.printf "CUT/%d: %s\n%!" i (EcPath.tostring p);

    let rec doit i p =
      match p.EcPath.p_node with
      | EcPath.Psymbol _ ->
          (p, `Ct (i-1))

      | EcPath.Pqname (p, x) -> begin
          match doit i p with
          | (p, `Ct 0) -> (p, `Dn (EcPath.psymbol x))
          | (p, `Ct i) -> (EcPath.pqname p x, `Ct (i-1))
          | (p, `Dn q) -> (p, `Dn (EcPath.pqname q x))
      end
    in
      match doit i p with
      | (p, `Ct 0) -> (p, None)
      | (_, `Ct _) -> assert false
      | (p, `Dn q) -> (p, Some q)

  (* ------------------------------------------------------------------ *)
  let _downpath_for_var (local : bool) _env p args =
    List.iter
      (fun arg -> Printf.printf "%b\n" (arg = None))
      args;

    try
      let (l, a, r) = List.find_split (fun x -> x <> None) args in
        if not (List.for_all (fun x -> x = None) r) then
          assert false;

        let i = List.length l in        (* position of args in path *)
        let a = oget a in               (* arguments of top enclosing module *)
        let n = List.map fst a in       (* argument names *)

        let ap =
          match p with
          | IPPath p -> begin
             (* p,q = frontier with the first module *)
              let (p, q) = _cutpath (i+1) p in
                match q with
                | None -> assert false
                | Some q -> begin
                    if local then
                      let vname = EcPath.basename q in
                      let fpath = oget (EcPath.prefix q) in
                      let fname = EcPath.basename fpath in
                        EcPath.xpath
                          (EcPath.mpath_crt
                             p (List.map EcPath.mident n)
                             (EcPath.prefix fpath))
                          (EcPath.pqname (EcPath.psymbol fname) vname)
                    else
                      EcPath.xpath
                        (EcPath.mpath_crt
                           p (List.map EcPath.mident n)
                           (EcPath.prefix q))
                        (EcPath.psymbol (EcPath.basename q))
                end
          end

          | IPIdent (m, x) -> begin
              if i <> 1 then assert false;

              match omap x (fun x -> x.EcPath.p_node) with
              | Some (EcPath.Psymbol x) ->
                  EcPath.xpath
                    (EcPath.mpath_abs m (List.map EcPath.mident n))
                    (EcPath.psymbol x)

              | _ -> assert false
          end
        in
          ((i+1, a), ap)

    with Not_found ->
      assert false

  let _downpath_for_fun = _downpath_for_var false

  (* ------------------------------------------------------------------ *)
  let _downpath_for_mod _env p args =
    let (l, a, r) =
      try
        List.find_split (fun x -> x <> None) args
      with Not_found ->
        (args, Some [], [])
    in
      if not (List.for_all (fun x -> x = None) r) then
        assert false;

      let i = List.length l in        (* position of args in path *)
      let a = oget a in               (* arguments of top enclosing module *)
      let n = List.map fst a in       (* argument names *)

      let ap =
        match p with
        | IPPath p ->
           (* p,q = frontier with the first module *)
            let (p, q) = _cutpath (i+1) p in
              EcPath.mpath_crt p (List.map EcPath.mident n) q

        | IPIdent (m, None) ->
            if i <> 1 then assert false;
            EcPath.mpath_abs m (List.map EcPath.mident n)

        | _ -> assert false
      in
        ((List.length l, a), ap)

  (* ------------------------------------------------------------------ *)
  let _downpath_for_th _env p args =
    if not (List.for_all (fun x -> x = None) args) then
      assert false;

    match p with
    | IPIdent _ -> assert false
    | IPPath  p -> p

  let _downpath_for_tydecl   = _downpath_for_th
  let _downpath_for_modsig   = _downpath_for_th
  let _downpath_for_operator = _downpath_for_th
  let _downpath_for_axiom    = _downpath_for_th

  (* ------------------------------------------------------------------ *)
  let _params_of_path p env =
    let rec _params_of_path acc p =
      match EcPath.prefix p with
      | None   -> acc
      | Some p ->
          let mc = oget (Mip.find_opt (IPPath p) env.env_comps) in
            _params_of_path (mc.mc_parameters :: acc) p
    in
      _params_of_path [] p

  (* ------------------------------------------------------------------ *)
  let _params_of_ipath p env =
    match p with
    | IPPath  p           -> _params_of_path p env
    | IPIdent (_, None)   -> []
    | IPIdent (_, Some _) -> [(oget (Mip.find_opt p env.env_comps)).mc_parameters]

  (* ------------------------------------------------------------------ *)
  let by_path proj p env =
    let mcx =
      match p with
      | IPPath p -> begin
        match p.EcPath.p_node with
        | EcPath.Psymbol x ->
            Some (oget (Mip.find_opt (IPPath top_path) env.env_comps), x)

        | EcPath.Pqname (p, x) ->
            omap
              (Mip.find_opt (IPPath p) env.env_comps)
              (fun mc -> (mc, x))
      end

      | IPIdent (_, None) -> None

      | IPIdent (m, Some p) ->
          let prefix = EcPath.prefix p in
          let name = EcPath.basename p in
            omap
              (Mip.find_opt (IPIdent (m, prefix)) env.env_comps)
              (fun mc -> (mc, name))
    in
      match obind mcx (fun (mc, x) -> MMsym.last x (proj mc)) with
      | None     -> None
      | Some obj -> Some (_params_of_ipath p env, snd obj)

  (* ------------------------------------------------------------------ *)
  let path_of_qn (top : EcPath.path) (qn : symbol list) =
    List.fold_left EcPath.pqname top qn

  let pcat (p1 : EcPath.path) (p2 : EcPath.path) =
    path_of_qn p1 (EcPath.tolist p2)

  let lookup_mc qn env =
      match qn with
      | [] -> Some env.env_current

      | x :: qn ->
          let p =
            obind (MMsym.last x env.env_current.mc_components)
              (fun p ->
                match p, qn with
                | IPIdent _, [] -> Some p
                | IPIdent _, _  -> None
                | IPPath  p, _  -> Some (IPPath (path_of_qn p qn)))
          in
            obind p (fun p -> Mip.find_opt p env.env_comps)

  (* ------------------------------------------------------------------ *)
  let lookup proj (qn, x) env =
    let mc = lookup_mc qn env in
      omap
        (obind mc (fun mc -> MMsym.last x (proj mc)))
        (fun (p, obj) -> (p, (_params_of_ipath p env, obj)))

  (* ------------------------------------------------------------------ *)
  let lookup_all proj (qn, x) env =
    let mc = lookup_mc qn env in
      List.map
        (fun (p, obj) -> (p, (_params_of_ipath p env, obj)))
        (odfl [] (omap mc (fun mc -> MMsym.all x (proj mc))))

  (* ------------------------------------------------------------------ *)
  let bind up x obj env =
    let obj = (IPPath (EcPath.pqname env.env_scope x), obj) in

    let env =
      { env with env_current =
          up true env.env_current x obj }
    in
      { env with env_comps =
          Mip.change
            (fun mc -> Some (up false (oget mc) x obj))
            (IPPath env.env_scope)
            env.env_comps; }

  let import up p obj env =
    let name = ibasename p in
      { env with env_current =
          up env.env_current name (p, obj) }

  (* -------------------------------------------------------------------- *)
  let lookup_var qnx env =
    match lookup (fun mc -> mc.mc_variables) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) ->
      let local = (obj.vb_kind = EcTypes.PVloc) in
        (_downpath_for_var local env p args, obj)

  let _up_var _ mc x obj =
    { mc with mc_variables = MMsym.add x obj mc.mc_variables }

  let import_var p var env =
    import (_up_var true) p var env

  (* -------------------------------------------------------------------- *)
  let lookup_fun qnx env =
    match lookup (fun mc -> mc.mc_functions) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_fun env p args, obj)

  let _up_fun _ mc x obj =
    { mc with mc_functions = MMsym.add x obj mc.mc_functions }

  let import_fun p fun_ env =
    import (_up_fun true) p fun_ env

  (* -------------------------------------------------------------------- *)
  let lookup_mod qnx env =
    match lookup (fun mc -> mc.mc_modules) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_mod env p args, obj)

  let _up_mod _ mc x obj =
    { mc with mc_modules = MMsym.add x obj mc.mc_modules }

  let import_mod p mod_ env =
    import (_up_mod true) p mod_ env

  (* -------------------------------------------------------------------- *)
  let lookup_tydecl qnx env =
    match lookup (fun mc -> mc.mc_tydecls) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_tydecl env p args, obj)

  let _up_tydecl _ mc x obj =
    { mc with mc_tydecls = MMsym.add x obj mc.mc_tydecls }

  let import_tydecl p tyd env =
    import (_up_tydecl true) (IPPath p) tyd env

  (* -------------------------------------------------------------------- *)
  let lookup_modty qnx env =
    match lookup (fun mc -> mc.mc_modsigs) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_modsig env p args, obj)

  let _up_modty _ mc x obj =
    { mc with mc_modsigs = MMsym.add x obj mc.mc_modsigs }

  let import_modty p msig env =
    import (_up_modty true) (IPPath p) msig env

  (* -------------------------------------------------------------------- *)
  let lookup_operator qnx env =
    match lookup (fun mc -> mc.mc_operators) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_operator env p args, obj)

  let lookup_operators qnx env =
    List.map
      (fun (p, (args, obj)) -> (_downpath_for_operator env p args, obj))
      (lookup_all (fun mc -> mc.mc_operators) qnx env)

  let _up_operator _ mc x obj =
      { mc with mc_operators = MMsym.add x obj mc.mc_operators }

  let import_operator p op env =
    import (_up_operator true) (IPPath p) op env

  (* -------------------------------------------------------------------- *)
  let lookup_axiom qnx env =
    match lookup (fun mc -> mc.mc_axioms) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_axiom env p args, obj)

  let _up_axiom _ mc x obj =
    { mc with mc_axioms = MMsym.add x obj mc.mc_axioms }

  let import_axiom p ax env =
    import (_up_axiom true) (IPPath p) ax env

  (* -------------------------------------------------------------------- *)
  let _up_theory _ mc x obj =
    { mc with mc_theories = MMsym.add x obj mc.mc_theories }

  let lookup_theory qnx env =
    match lookup (fun mc -> mc.mc_theories) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_th env p args, obj)

  let import_theory p th env =
    import (_up_theory true) (IPPath p) th env

  (* -------------------------------------------------------------------- *)
  let _up_mc _ mc p =
    let name = EcPath.basename p in

    { mc with mc_components =
        MMsym.add name (IPPath p) mc.mc_components }

  let import_mc p env =
    let mc = _up_mc true env.env_current p in
      { env with env_current = mc }

  (* ------------------------------------------------------------------ *)
  let mc_of_module_r scope (me : module_expr) =
    let rec mc_of_module_r (p1, args, p2) me =
      let subp2 x =
        let p = EcPath.pqoname p2 x in
          (p, pcat p1 p)
      in

      let mc1_of_module (mc : mc) = function
        | MI_Module subme ->
            assert (subme.me_sig.mis_params = []);
  
            let (subp2, mep) = subp2 subme.me_name in
            let submcs = mc_of_module_r (p1, args, Some subp2) subme in
            let mc = _up_mc false mc mep in
            let mc = _up_mod false mc subme.me_name (IPPath mep, subme) in
              (mc, Some submcs)
  
        | MI_Variable v ->
            let (_subp2, mep) = subp2 v.v_name in
            let vty  =
              { vb_type = v.v_type;
                vb_kind = PVglob; }
            in
              (_up_var false mc v.v_name (IPPath mep, vty), None)
  
        | MI_Function f ->
            let (_subp2, mep) = subp2 f.f_name in
              (_up_fun false mc f.f_name (IPPath mep, f), None)
      in

      let (mc, submcs) =
        List.map_fold mc1_of_module
          (empty_mc
             (if p2 = None then Some me.me_sig.mis_params else None))
          me.me_comps
      in
        ((me.me_name, mc), List.prmap (fun x -> x) submcs)
    in
      mc_of_module_r
        (EcPath.pqname scope me.me_name, me.me_sig.mis_params, None)
        me

  let mc_of_module (env : env) (me : module_expr) =
    mc_of_module_r env.env_scope me

  (* ------------------------------------------------------------------ *)
  let rec mc_of_ctheory_r (scope : EcPath.path) (x, th) =
    let subscope = EcPath.pqname scope x in
    let expath = fun x -> EcPath.pqname subscope x in
    let add2mc up name obj mc =
      up false mc name (IPPath (expath name), obj)
    in

    let mc1_of_ctheory (mc : mc) = function
      | CTh_type (xtydecl, tydecl) ->
          (add2mc _up_tydecl xtydecl tydecl mc, None)

      | CTh_operator (xop, op) ->
          (add2mc _up_operator xop op mc, None)

      | CTh_axiom (xax, ax) ->
          (add2mc _up_axiom xax ax mc, None)

      | CTh_modtype (xmodty, modty) ->
          (add2mc _up_modty xmodty modty mc, None)

      | CTh_module subme ->
          (add2mc _up_mod subme.me_name subme mc, None) (* FIXME *)

      | CTh_theory (xsubth, subth) ->
          let submcs = mc_of_ctheory_r subscope (xsubth, subth) in
          let mc = _up_mc false mc (expath xsubth) in
            (add2mc _up_theory xsubth subth mc, Some submcs)

      | CTh_export _ -> (mc, None)
    in 

    let (mc, submcs) =
      List.map_fold mc1_of_ctheory (empty_mc None) th.cth_struct
    in
      ((x, mc), List.prmap (fun x -> x) submcs)

  let mc_of_ctheory (env : env) (x : symbol) (th : ctheory) =
    mc_of_ctheory_r env.env_scope (x, th)

  (* ------------------------------------------------------------------ *)
  let rec bind_submc env path ((name, mc), submcs) =
    let path = EcPath.pqname path name in

    if Mip.find_opt (IPPath path) env.env_comps <> None then
      raise (DuplicatedBinding (EcPath.basename path));

    bind_submcs
      { env with env_comps = Mip.add (IPPath path) mc env.env_comps }
      path submcs

  and bind_submcs env path submcs =
    List.fold_left (bind_submc^~ path) env submcs

  and bind_mc x mc env =
    let path = EcPath.pqname env.env_scope x in

    { env with
        env_current = _up_mc true env.env_current path;
        env_comps =
          Mip.change
            (fun mc -> Some (_up_mc false (oget mc) path))
            (IPPath env.env_scope)
            (Mip.add (IPPath path) mc env.env_comps); }

  and bind_theory x th env =
    let (_, mc), submcs = mc_of_ctheory env x th in
    let env = bind _up_theory x th env in
    let env = bind_mc x mc env in
    let env =
      bind_submcs env
        (EcPath.pqname env.env_scope x)
        submcs
    in
      env

  and bind_mod x mod_ env =
    let (_, mc), submcs = mc_of_module env mod_ in
    let env = bind _up_mod x mod_ env in
    let env = bind_mc x mc env in
    let env =
      bind_submcs env
        (EcPath.pqname env.env_scope x)
        submcs
    in
      env

  and bind_fun x vb env =
    bind _up_fun x vb env

  and bind_var x vb env =
    bind _up_var x vb env

  and bind_axiom x ax env =
    bind _up_axiom x ax env

  and bind_operator x op env =
    bind _up_operator x op env

  and bind_modty x msig env =
    bind _up_modty x msig env

  and bind_tydecl x tyd env =
    bind _up_tydecl x tyd env
end

(* -------------------------------------------------------------------- *)
let enter ?params (name : symbol) (env : env) =
  let path = EcPath.pqname env.env_scope name in

  if Mip.find_opt (IPPath path) env.env_comps <> None then
    raise (DuplicatedBinding name);

  let env = MC.bind_mc name (empty_mc params) env in

    { env with
        env_scope = (EcPath.pqname env.env_scope name);
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
    let memories =
      List.filter
        (fun me' -> EcIdent.id_equal me (EcMemory.memory me'))
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
    | Some me -> Some (oget (byid me env))

  let push (me : EcMemory.memenv) (env : env) =
    (* FIXME: assert (byid (EcMemory.memory me) env = None); *)

    let id = EcMemory.memory me in
    let maps =
      MMsym.add (EcIdent.name id) me env.env_memories
    in
      { env with env_memories = maps }

  let push_all memenvs env =
    List.fold_left
      (fun env m -> push m env)
      env memenvs

  let push_active memenv env =
    set_active (EcMemory.memory memenv)
      (push memenv env)
end

(* -------------------------------------------------------------------- *)
let ipath_of_mpath_opt (p : mpath_top) =
  match p with
  | `Abstract i ->
      IPIdent (i, None)

  | `Concrete (p1, p2) ->
      let pr = odfl p1 (omap p2 (MC.pcat p1)) in
        IPPath pr

let ipath_of_mpath (p : mpath) =
  match p.EcPath.m_top with
  | `Abstract i ->
      (IPIdent (i, None), (1, p.EcPath.m_args))

  | `Concrete (p1, p2) ->
      let pr = odfl p1 (omap p2 (MC.pcat p1)) in
        (IPPath pr, (EcPath.p_size p1, p.EcPath.m_args))

let ipath_of_xpath (p : xpath) =
  match p.EcPath.x_sub.EcPath.p_node with
  | EcPath.Psymbol x ->
      let xt p =
        match p with
        | IPPath p -> Some (IPPath (EcPath.pqname p x))
        | IPIdent (m, None) -> Some (IPIdent (m, Some (EcPath.psymbol x)))
        | _ -> None
      in

      let (p, a) = ipath_of_mpath p.EcPath.x_top in
        omap (xt p) (fun p -> (p, a))

  | _ -> None

(* -------------------------------------------------------------------- *)
let try_lf f =
  try  Some (f ())
  with LookupFailure _ -> None

(* -------------------------------------------------------------------- *)
module Var = struct
  type t = varbind

  let by_xpath (p : xpath) (env : env) =
    match ipath_of_xpath p with
    | None -> lookup_error (`XPath p)

    | Some (ip, (i, args)) -> begin
        match MC.by_path (fun mc -> mc.mc_variables) ip env with
        | None -> lookup_error (`XPath p)
        | Some (params, o) ->
           let local = o.vb_kind = EcTypes.PVloc in
           let ((spi, params), _) = MC._downpath_for_var local env ip params in
             if i <> spi || List.length args <> List.length params then
               assert false;
             o
      end

  let by_xpath_opt (p : xpath) (env : env) =
    try_lf (fun () -> by_xpath p env)

  let add (path : EcPath.xpath) (env : env) =
    let obj = by_xpath path env in
    let ip = fst (oget (ipath_of_xpath path)) in
      MC.import_var ip obj env

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
      | [] ->
          let memenv = oget (Memory.byid side env) in

          if EcMemory.memtype memenv = None then
            None
          else
            let mp = EcMemory.xpath memenv in
            begin match EcMemory.lookup (snd qname) memenv with
            | None    -> None
            | Some ty ->
                let pv =
                  { pv_name = EcPath.xqname mp (snd qname);
                    pv_kind = PVloc; }
                in
                  Printf.printf "XP1: %s\n%!" (EcPath.x_tostring pv.pv_name);
                Some (pv, ty)
            end

      | _ -> None
    in

      match obind side inmem with
      | None -> begin
          let (((_, a), p), x) = MC.lookup_var qname env in
            if a <> [] then
              raise (LookupFailure (`QSymbol qname));
            Printf.printf "XP2: %s\n%!" (EcPath.x_tostring p);
            ({ pv_name = p; pv_kind = x.vb_kind }, x.vb_type)
        end

      | Some (pv, ty) -> (pv, ty)

  let lookup_progvar_opt ?side name env =
    try_lf (fun () -> lookup_progvar ?side name env)

  let bind name pvkind ty env =
    let vb = { vb_type = ty; vb_kind = pvkind; } in
      MC.bind_var name vb env

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
end

(* -------------------------------------------------------------------- *)
module Fun = struct
  type t = EcModules.function_

  let enter (x : symbol) (env : env) =
    enter x env

  let by_ipath (p : ipath) (env : env) =
    MC.by_path (fun mc -> mc.mc_functions) p env

  let by_xpath (p : EcPath.xpath) (env : env) =
    Printf.printf "Fun.by_xpath: %s\n%!" (EcPath.x_tostring p);

    match ipath_of_xpath p with
    | None -> lookup_error (`XPath p)

    | Some (ip, (i, args)) -> begin
        match MC.by_path (fun mc -> mc.mc_functions) ip env with
        | None -> lookup_error (`XPath p)
        | Some (params, o) ->
           let ((spi, params), _op) = MC._downpath_for_fun env ip params in
             Printf.printf "Fun.by_xpath: %d %d\n%!" i spi;
             if i <> spi || List.length args <> List.length params then
               assert false;
             let s =
               List.fold_left2
                 (fun s (x, _) a -> EcSubst.add_module s x a)
                 EcSubst.empty params args
             in
               EcSubst.subst_function s o
      end

  let by_xpath_opt (p : EcPath.xpath) (env : env) =
    try_lf (fun () -> by_xpath p env)

  let lookup qname (env : env) =
    let (((_, a), p), x) = MC.lookup_fun qname env in
      if a <> [] then
        raise (LookupFailure (`QSymbol qname));
      (p, x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let sp_lookup qname (env : env) =
    let (((i, a), p), x) = MC.lookup_fun qname env in
    let obj = { sp_target = x; sp_params = (i, a); } in
      (p, obj)

  let sp_lookup_opt name env =
    try_lf (fun () -> sp_lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name fun_ env =
    MC.bind_fun name fun_ env

  let add (path : EcPath.xpath) (env : env) =
    let obj = by_xpath path env in
    let ip = fst (oget (ipath_of_xpath path)) in
      MC.import_fun ip obj env

  let add_in_memenv memenv vd =
    EcMemory.bind vd.v_name vd.v_type memenv

  let adds_in_memenv = List.fold_left add_in_memenv

  let actmem_pre me path fun_ =
    let mem = EcMemory.empty_local me path in
    adds_in_memenv mem (fst fun_.f_sig.fs_sig)

  let actmem_post me path fun_ =
    let mem = EcMemory.empty_local me path in
    add_in_memenv mem {v_name = "res"; v_type = snd fun_.f_sig.fs_sig}

  let actmem_body me path fun_ =
    let mem = actmem_pre me path fun_ in
    match fun_.f_def with
    | None -> assert false (* FIXME error message *)
    | Some fd -> fd, adds_in_memenv mem fd.f_locals

  let actmem_body_anonym me path locals =
    let mem = EcMemory.empty_local me path in
    adds_in_memenv mem locals

  let prF path env =
    let fun_ = by_xpath path env in
    let post = actmem_post EcFol.mhr path fun_ in
    Memory.push_active post env

  let hoareF_memenv path env = 
    let (ip, _) = oget (ipath_of_xpath path) in
    let fun_ = snd (oget (by_ipath ip env)) in
    let pre  = actmem_pre EcFol.mhr path fun_ in 
    let post = actmem_post EcFol.mhr path fun_ in 
    pre, post
    
  let hoareF path env = 
    let pre, post = hoareF_memenv path env in
    Memory.push_active pre env, Memory.push_active post env  

  let hoareS path env =
    let fun_ = by_xpath path env in
    let fd, memenv = actmem_body EcFol.mhr path fun_ in
    memenv, fd, Memory.push_active memenv env

  let hoareS_anonym _locals _env =      (* FIXME *)
    assert false

(*
    let path = env.env_scope in
    let memenv = actmem_body_anonym EcFol.mhr path locals in
    memenv, Memory.push_active memenv env
*)

  let equivF_memenv path1 path2 env = 
    let (ip1, _) = oget (ipath_of_xpath path1) in
    let (ip2, _) = oget (ipath_of_xpath path2) in

    let fun1 = snd (oget (by_ipath ip1 env)) in
    let fun2 = snd (oget (by_ipath ip2 env)) in
    let pre1 = actmem_pre EcFol.mleft path1 fun1 in
    let pre2 = actmem_pre EcFol.mright path2 fun2 in
    let post1 = actmem_post EcFol.mleft path1 fun1 in 
    let post2 = actmem_post EcFol.mright path2 fun2 in
    (pre1,pre2), (post1,post2)

  let equivF path1 path2 env = 
    let (pre1,pre2),(post1,post2) = equivF_memenv path1 path2 env in
    Memory.push_all [pre1; pre2] env,
    Memory.push_all [post1; post2] env

  let equivS path1 path2 env =
    let fun1 = by_xpath path1 env in
    let fun2 = by_xpath path2 env in
    let fd1, mem1 = actmem_body EcFol.mleft path1 fun1 in
    let fd2, mem2 = actmem_body EcFol.mright path2 fun2 in
    mem1, fd1, mem2, fd2, Memory.push_all [mem1; mem2] env

  let equivS_anonym _locals1 _locals2 _env = (* FIXME *)
    assert false

(*
    let path1, path2 = env.env_scope, env.env_scope in
    let mem1 = actmem_body_anonym EcFol.mleft path1 locals1 in
    let mem2 = actmem_body_anonym EcFol.mright path2 locals2 in
    mem1, mem2, Memory.push_all [mem1; mem2] env
*)

(*
  let enter name env =
    enter name EcPath.PKother [] env
*)
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  type t = module_expr

  let unsuspend_r f (i, args) (spi, params) o =
    if i <> spi || List.length args <> List.length params then
      assert false;
    let s =
      List.fold_left2
        (fun s (x, _) a -> EcSubst.add_module s x a)
        EcSubst.empty params args
    in
      f s o

  let unsuspend = unsuspend_r EcSubst.subst_module

  let by_ipath (p : ipath) (env : env) =
    let obj = MC.by_path (fun mc -> mc.mc_modules) p env in
    omap obj
      (fun (args, obj) ->
         (fst (MC._downpath_for_mod env p args), obj))

  let by_path (p : mpath_top) (env : env) =
    by_ipath (ipath_of_mpath_opt p) env

  let by_path_opt (p : mpath_top) (env : env) =
    try_lf (fun () -> by_path p env)

  let by_mpath (p : mpath) (env : env) =
    let (ip, (i, args)) = ipath_of_mpath p in

      match MC.by_path (fun mc -> mc.mc_modules) ip env with
      | None -> lookup_error (`MPath p)
      | Some (params, o) ->
          let ((spi, params), _op) =
            MC._downpath_for_mod env ip params
          in
            unsuspend (i, args) (spi, params) o

  let by_mpath_opt (p : EcPath.mpath) (env : env) =
    try_lf (fun () -> by_mpath p env)

  let add (p : EcPath.mpath) (env : env) =
    let obj = by_mpath p env in
      MC.import_mod (fst (ipath_of_mpath p)) obj env

  let lookup qname (env : env) =
    let (((_, a), p), x) = MC.lookup_mod qname env in
      if a <> [] then
        raise (LookupFailure (`QSymbol qname));
      (p, x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let sp_lookup qname (env : env) =
    let (((i, a), p), x) = MC.lookup_mod qname env in
    let obj = { sp_target = x; sp_params = (i, a); } in
      (p.EcPath.m_top, obj)

  let sp_lookup_opt name env =
    try_lf (fun () -> sp_lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name me env =
    assert (me.me_name = name);
    let env = MC.bind_mod name me env in
    let (w3, rb) =
      EcWhy3.add_mod_exp env.env_w3
          (EcPath.pqname env.env_scope name) me
    in
      { env with
        env_w3   = w3;
        env_rb   = rb @ env.env_rb;
        env_item = CTh_module me :: env.env_item }

  let bind_local _name _modty _env =
    assert false

(*
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
*)

  let bind_locals bindings env =
    List.fold_left
      (fun env (name, me) -> bind_local name me env)
      env bindings

  let enter name params env =
    let env = enter ~params name env in
      bind_locals params env
end

(* -------------------------------------------------------------------- *)
module Ty = struct
  type t = EcDecl.tydecl

  let by_path_opt (p : EcPath.path) (env : env) =
    omap 
      (MC.by_path (fun mc -> mc.mc_tydecls) (IPPath p) env)
      check_not_suspended

  let by_path (p : EcPath.path) (env : env) =
    match by_path_opt p env with
    | None -> lookup_error (`Path p)
    | Some obj -> obj

  let add (p : EcPath.path) (env : env) =
    let obj = by_path p env in
      MC.import_tydecl p obj env

  let lookup qname (env : env) =
    MC.lookup_tydecl qname env

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name ty env =
    let env = MC.bind_tydecl name ty env in
    let (w3, rb) =
        EcWhy3.add_ty env.env_w3
          (EcPath.pqname env.env_scope name) ty
    in
      { env with
          env_w3   = w3;
          env_rb   = rb @ env.env_rb;
          env_item = CTh_type (name, ty) :: env.env_item; }

  let rebind name ty env =
    MC.bind_tydecl name ty env

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
module NormMp = struct
  let rec norm_mpath env p =
    let (ip, (i, args)) = ipath_of_mpath p in
      match Mod.by_ipath ip env with
      | Some ((spi, params), ({ me_body = ME_Alias alias } as m)) ->
          assert (m.me_sig.mis_params = []);
          let p =
            Mod.unsuspend_r EcSubst.subst_mpath (i, args) (spi, params) alias
          in
            norm_mpath env p

      | _ -> begin
        match p.EcPath.m_top with
        | `Abstract _
        | `Concrete (_, None) -> p

        | `Concrete (p1, Some p2) -> begin
          let name = EcPath.basename p2 in
          let pr   = EcPath.mpath_crt p1 p.EcPath.m_args (EcPath.prefix p2) in
          let pr   = norm_mpath env pr in

            match pr.EcPath.m_top with
            | `Abstract _ -> p
            | `Concrete (p1, p2) ->
                 EcPath.mpath_crt p1 pr.EcPath.m_args
                   (Some (EcPath.pqoname p2 name))
        end
      end

  let norm_xpath env p =
    EcPath.xpath (norm_mpath env p.EcPath.x_top) p.EcPath.x_sub

  let norm_pvar env pv = 
    let p = norm_xpath env pv.pv_name in
      if   x_equal p pv.pv_name
      then pv
      else { pv_name = p; pv_kind = pv.pv_kind }

  let norm_form env =
    let norm_xp = EcPath.Hx.memo 107 (norm_xpath env) in
    let norm_pv pv =
      let p = norm_xp pv.pv_name in
        if   x_equal p pv.pv_name
        then pv
        else { pv_name = p; pv_kind = pv.pv_kind }
    in

    let norm_form =
      EcFol.Hf.memo_rec 107 (fun aux f ->
        match f.f_node with
        | Fquant(q,bd,f) ->               (* FIXME: norm module_type *)
          f_quant q bd (aux f)

        | Fpvar(p,m) ->
          let p' = norm_pv p in
          if p == p' then f else
            f_pvar p' f.f_ty m

        | FhoareF hf ->
          let pre' = aux hf.hf_pr and p' = norm_xp hf.hf_f
          and post' = aux hf.hf_po in
          if hf.hf_pr == pre' && hf.hf_f == p' && hf.hf_po == post' then f else
          f_hoareF pre' p' post'

(*        | FhoareS _ -> assert false (* FIXME ? Not implemented *) *)

        | FequivF ef ->
          let pre' = aux ef.ef_pr and l' = norm_xp ef.ef_fl
          and r' = norm_xp ef.ef_fr and post' = aux ef.ef_po in
          if ef.ef_pr == pre' && ef.ef_fl == l' &&
            ef.ef_fr == r' && ef.ef_po == post' then f else
          f_equivF pre' l' r' post'

(*        | FequivS _ -> assert false (* FIXME ? Not implemented *) *)

        | Fpr(m,p,args,e) ->
          let p' = norm_xp p in
          let args' = List.smart_map aux args in
          let e' = aux e in
          if p == p' && args == args' && e == e' then f else
          f_pr m p' args' e'

        | _ -> EcFol.f_map (fun ty -> ty) aux f) in
    norm_form

  let norm_op env op =
    match op.op_kind with
    | OB_pred (Some f) ->
        { op with op_kind = OB_pred (Some (norm_form env f)) }
    | _ -> op

  let norm_ax env ax =
    { ax with ax_spec = omap ax.ax_spec (norm_form env) }
end

(* -------------------------------------------------------------------- *)
module ModTy = struct
  type t = module_sig

  let by_path_opt (p : EcPath.path) (env : env) =
    omap 
      (MC.by_path (fun mc -> mc.mc_modsigs) (IPPath p) env)
      check_not_suspended

  let by_path (p : EcPath.path) (env : env) =
    match by_path_opt p env with
    | None -> lookup_error (`Path p)
    | Some obj -> obj

  let add (p : EcPath.path) (env : env) =
    let obj = by_path p env in
      MC.import_modty p obj env

  let lookup qname (env : env) =
    MC.lookup_modty qname env

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name modty env =
    let env = MC.bind_modty name modty env in
      { env with
          env_item = CTh_modtype (name, modty) :: env.env_item }

  let mod_type_equiv (env : env) (mty1 : module_type) (mty2 : module_type) =
       (EcPath.p_equal mty1.mt_name mty2.mt_name)
    && oall2
         (List.all2
            (fun m1 m2 ->
               let m1 = NormMp.norm_mpath env m1 in
               let m2 = NormMp.norm_mpath env m2 in
                 EcPath.m_equal m1 m2))
         mty1.mt_args mty2.mt_args

  let has_mod_type (env : env) (dst : module_type list) (src : module_type) =
    List.exists (mod_type_equiv env src) dst
end

(* -------------------------------------------------------------------- *)
module Op = struct
  type t = EcDecl.operator

  let by_path_opt (p : EcPath.path) (env : env) =
    omap 
      (MC.by_path (fun mc -> mc.mc_operators) (IPPath p) env)
      check_not_suspended

  let by_path (p : EcPath.path) (env : env) =
    match by_path_opt p env with
    | None -> lookup_error (`Path p)
    | Some obj -> obj

  let add (p : EcPath.path) (env : env) =
    let obj = by_path p env in
      MC.import_operator p obj env

  let lookup qname (env : env) =
    MC.lookup_operator qname env

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name op env =
    let env = MC.bind_operator name op env in
    let op = NormMp.norm_op env op in
    let (w3, rb) =
        EcWhy3.add_op env.env_w3
          (EcPath.pqname env.env_scope name) op
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
    let ops = MC.lookup_operators qname env in
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
    let s = 
      EcFol.Fsubst.init_subst_tvar (EcTypes.Tvar.init op.op_tparams tys) in
    let f = 
      match op.op_kind with
      | OB_oper(Some e) -> EcFol.form_of_expr EcFol.mhr e
      | OB_pred(Some idsf) -> idsf
      | _ -> raise NotReducible
    in
      EcFol.f_subst s f
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  type t = axiom

  let by_path_opt (p : EcPath.path) (env : env) =
    omap 
      (MC.by_path (fun mc -> mc.mc_axioms) (IPPath p) env)
      check_not_suspended

  let by_path (p : EcPath.path) (env : env) =
    match by_path_opt p env with
    | None -> lookup_error (`Path p)
    | Some obj -> obj

  let add (p : EcPath.path) (env : env) =
    let obj = by_path p env in
      MC.import_axiom p obj env

  let lookup qname (env : env) =
    MC.lookup_axiom qname env

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name ax env =
    let env = MC.bind_axiom name ax env in
    let (w3, rb) =
      EcWhy3.add_ax env.env_w3
        (EcPath.pqname env.env_scope name)
        (NormMp.norm_ax env ax) in
    { env with
      env_w3   = w3;
      env_rb   = rb @ env.env_rb;
      env_item = CTh_axiom (name, ax) :: env.env_item }

  let rebind name ax env =
    MC.bind_axiom name ax env

  let instanciate p tys env =
    match by_path_opt p env with
    | Some ({ ax_spec = Some f } as ax) ->
        Fsubst.subst_tvar (EcTypes.Tvar.init ax.ax_tparams tys) f
    | _ -> raise (LookupFailure (`Path p))
end


(* -------------------------------------------------------------------- *)
module Theory = struct
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
    enter name env

  (* ------------------------------------------------------------------ *)
  let by_path_opt (p : EcPath.path) (env : env) =
    omap 
      (MC.by_path (fun mc -> mc.mc_theories) (IPPath p) env)
      check_not_suspended

  let by_path (p : EcPath.path) (env : env) =
    match by_path_opt p env with
    | None -> lookup_error (`Path p)
    | Some obj -> obj

  let add (p : EcPath.path) (env : env) =
    let obj = by_path p env in
      MC.import_theory p obj env

  let lookup qname (env : env) =
    MC.lookup_theory qname env

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

    let cpath = env.env_scope in
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
      let xpath x = EcPath.pqname path x in
      let rec import_cth_item (env : env) = function
        | CTh_type (x, ty) ->
            MC.import_tydecl (xpath x) ty env

        | CTh_operator (x, op) ->
            MC.import_operator (xpath x) op env

        | CTh_axiom (x, ax) ->
            MC.import_axiom (xpath x) ax env

        | CTh_modtype (x, ty) ->
            MC.import_modty (xpath x) ty env

        | CTh_module m ->
            MC.import_mod (IPPath (xpath m.me_name)) m env

        | CTh_export p ->
            import env p (by_path p env)

        | CTh_theory (x, th) ->
            let env = MC.import_theory (xpath x) th env in
            let env = MC.import_mc (xpath x) env in
              env
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
    let rootnm  = EcCoreLib.p_top in
    let thpath  = EcPath.pqname rootnm x in

    let env =
      let (_, thmc), submcs =
        MC.mc_of_ctheory_r rootnm (x, cth.cth3_theory)
      in
        MC.bind_submc env rootnm ((x, thmc), submcs)
    in

    let topmc = Mip.find (IPPath rootnm) env.env_comps in
    let topmc = MC._up_theory false topmc x (IPPath thpath, cth.cth3_theory) in
    let topmc = MC._up_mc false topmc thpath in

    let current = env.env_current in
    let current = MC._up_theory true current x (IPPath thpath, cth.cth3_theory) in
    let current = MC._up_mc true current thpath in

    let comps = env.env_comps in
    let comps = Mip.add (IPPath rootnm) topmc comps in

    { env with
        env_current = current;
        env_comps   = comps;
        env_w3      = EcWhy3.rebind env.env_w3 cth.cth3_rebind; }
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
  let th = EcProvers.get_w3_th dir name in
    import_w3 env th rd

(* -------------------------------------------------------------------- *)
let initial =
  let env0 = empty in
  let env = enter EcCoreLib.id_Pervasive env0 in
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
    let ty = EcTypes.toarrow sign EcTypes.tbool in
    Op.bind_logical (EcPath.basename path) 
      (mk_op [] ty None) env in
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
  let env1 = Theory.bind EcCoreLib.id_Pervasive cth env0 in
  let env1 = Theory.import EcCoreLib.p_Pervasive env1 in
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
let norm_l_decl env (hyps,concl) =
  let norm = NormMp.norm_form env in
  let onh (x,lk) =
    match lk with
    | LD_var (ty,o) -> x, LD_var (ty, omap o norm)
    | LD_mem _ -> x, lk
    | LD_modty _ -> x, lk
    | LD_hyp f -> x, LD_hyp (norm f) in
  let concl = norm concl in
  let lhyps = List.map onh hyps.h_local in
  ({ hyps with h_local = lhyps}, concl)

let check_goal env pi ld =
  let ld = (norm_l_decl env ld) in
  let res = EcWhy3.check_goal env.env_w3 pi ld in
  res
