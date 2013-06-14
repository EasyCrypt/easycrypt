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
module Sip = EcMaps.Set.MakeOfMap(Mip)

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
  env_scope    : escope;
  env_current  : mc;
  env_comps    : mc Mip.t;
  env_locals   : (EcIdent.t * EcTypes.ty) MMsym.t;
  env_memories : EcMemory.memenv MMsym.t;
  env_actmem   : EcMemory.memory option;
  env_w3       : EcWhy3.env;
  env_rb       : EcWhy3.rebinding;        (* in reverse order *)
  env_item     : ctheory_item list        (* in reverse order *)
}

and escope = {
  ec_path  : EcPath.path;
  ec_scope : [ `Theory
             | `Module of EcPath.mpath
             | `Fun    of EcPath.xpath ];
}

(* -------------------------------------------------------------------- *)
type env = preenv

(* -------------------------------------------------------------------- *)
let root (env : env) =
  env.env_scope.ec_path

let mroot (env : env) =
  match env.env_scope.ec_scope with
  | `Theory   -> EcPath.mpath_crt (root env) [] None
  | `Module m -> m
  | `Fun    x -> x.EcPath.x_top

let xroot (env : env) =
  match env.env_scope.ec_scope with
  | `Fun x -> Some x
  | _ -> None

(* -------------------------------------------------------------------- *)
module Dump = struct
  let rec dump ?(name = "Environment") pp (env : env) =
      EcDebug.onseq pp name ~extra:(EcPath.tostring (root env))
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
    { env_scope    = { ec_path = path; ec_scope = `Theory; };
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

let pp_lookup_failure fmt e =
  let p =
    match e with
    | `XPath   p -> EcPath.x_tostring p
    | `MPath   p -> EcPath.m_tostring p
    | `Path    p -> EcPath.tostring p
    | `QSymbol p -> string_of_qsymbol p
  in
    Format.fprintf fmt "unknown symbol: %s" p

let () =
  let pp fmt exn =
    match exn with
    | LookupFailure p -> pp_lookup_failure fmt p
    | _ -> raise exn
  in
    EcPException.register pp

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
  let _downpath_for_modcp isvar ~local ~spsc env p args =
    let prefix =
      let prefix_of_mtop = function
        | `Concrete (p1, _) -> Some p1
        | `Abstract _ -> None
      in
        match env.env_scope.ec_scope with
        | `Theory   -> None
        | `Module m -> prefix_of_mtop m.EcPath.m_top
        | `Fun    m -> prefix_of_mtop m.EcPath.x_top.EcPath.m_top
    in          

    try
      let (l, a, r) = List.find_split (fun x -> x <> None) args in
        if not (List.for_all (fun x -> x = None) r) then
          assert false;

        let i = List.length l in        (* position of args in path *)
        let a = oget a in               (* arguments of top enclosing module *)
        let n = List.map fst a in       (* argument names *)

        let (ap, inscope) =
          match p with
          | IPPath p -> begin
             (* p,q = frontier with the first module *)
              let (p, q) = _cutpath (i+1) p in
                match q with
                | None -> assert false
                | Some q -> begin
                    let ap =
                      if local then
                        let vname = EcPath.basename q in
                        let fpath = oget (EcPath.prefix q) in
                        let fname = EcPath.basename fpath in
                          EcPath.xpath
                            (EcPath.mpath_crt
                               p (if isvar && not local then [] else List.map EcPath.mident n)
                               (EcPath.prefix fpath))
                            (EcPath.pqname (EcPath.psymbol fname) vname)
                      else
                        EcPath.xpath
                          (EcPath.mpath_crt
                             p (if isvar && not local then [] else List.map EcPath.mident n)
                             (EcPath.prefix q))
                          (EcPath.psymbol (EcPath.basename q))
                    in
                      (ap, odfl false (omap prefix (EcPath.p_equal p)))
                end
          end

          | IPIdent (m, x) -> begin
              if i <> 0 then assert false;

              match omap x (fun x -> x.EcPath.p_node) with
              | Some (EcPath.Psymbol x) ->
                  let ap =
                    EcPath.xpath
                      (EcPath.mpath_abs m
                         (if isvar then [] else List.map EcPath.mident n))
                      (EcPath.psymbol x)
                  in
                    (ap, false)

              | _ -> assert false
          end
        in
          ((i+1, if (inscope && not spsc) || isvar then [] else a), ap)

    with Not_found ->
      assert false

  let _downpath_for_var = _downpath_for_modcp true
  let _downpath_for_fun = _downpath_for_modcp false ~local:false

  (* ------------------------------------------------------------------ *)
  let _downpath_for_mod spsc env p args =
    let prefix =
      let prefix_of_mtop = function
        | `Concrete (p1, _) -> Some p1
        | `Abstract _ -> None
      in
        match env.env_scope.ec_scope with
        | `Theory   -> None
        | `Module m -> prefix_of_mtop m.EcPath.m_top
        | `Fun    m -> prefix_of_mtop m.EcPath.x_top.EcPath.m_top
    in          

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

      let (ap, inscope) =
        match p with
        | IPPath p ->
           (* p,q = frontier with the first module *)
            let (p, q) = _cutpath (i+1) p in
              (EcPath.mpath_crt p (List.map EcPath.mident n) q,
               odfl false (omap prefix (EcPath.p_equal p)))

        | IPIdent (m, None) ->
            if i <> 0 then assert false;
            (EcPath.mpath_abs m (List.map EcPath.mident n), false)

        | _ -> assert false
      in
        ((List.length l, if inscope && not spsc then [] else a), ap)

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
    | IPIdent (m, Some p) ->
        if EcPath.prefix p <> None then
          assert false;
        let mc = Mip.find_opt (IPIdent (m, None)) env.env_comps in
          [(oget mc).mc_parameters]

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

      | IPIdent (id, None) ->
          Some (env.env_current, EcIdent.name id)

      | IPIdent (m, Some p) ->
          let prefix = EcPath.prefix p in
          let name   = EcPath.basename p in
            omap
              (Mip.find_opt (IPIdent (m, prefix)) env.env_comps)
              (fun mc -> (mc, name))
    in

    let lookup (mc, x) =
      List.filter
        (fun (ip, _) -> IPathC.compare ip p = 0)
        (MMsym.all x (proj mc))
    in
      match omap mcx lookup with
      | None | Some [] -> None
      | Some (obj :: _) -> Some (_params_of_ipath p env, snd obj)

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
    let obj = (IPPath (EcPath.pqname (root env) x), obj) in

    let env =
      { env with env_current =
          up true env.env_current x obj }
    in
      { env with env_comps =
          Mip.change
            (fun mc -> Some (up false (oget mc) x obj))
            (IPPath (root env))
            env.env_comps; }

  let import up p obj env =
    let name = ibasename p in
      { env with env_current = up env.env_current name (p, obj) }

  (* -------------------------------------------------------------------- *)
  let lookup_var qnx env =
    match lookup (fun mc -> mc.mc_variables) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) ->
      let local = (obj.vb_kind = EcTypes.PVloc) in
        (_downpath_for_var local false env p args, obj)

  let _up_var candup mc x obj =
    if not candup && MMsym.last x mc.mc_variables <> None then
      raise (DuplicatedBinding x);
    { mc with mc_variables = MMsym.add x obj mc.mc_variables }

  let import_var p var env =
    import (_up_var true) p var env

  (* -------------------------------------------------------------------- *)
  let lookup_fun qnx env =
    match lookup (fun mc -> mc.mc_functions) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_fun false env p args, obj)

  let _up_fun candup mc x obj =
    if not candup && MMsym.last x mc.mc_functions <> None then
      raise (DuplicatedBinding x);
    { mc with mc_functions = MMsym.add x obj mc.mc_functions }

  let import_fun p fun_ env =
    import (_up_fun true) p fun_ env

  (* -------------------------------------------------------------------- *)
  let lookup_mod qnx env =
    match lookup (fun mc -> mc.mc_modules) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> 
      (_downpath_for_mod false env p args, obj)

  let _up_mod candup mc x obj =
    if not candup && MMsym.last x mc.mc_modules <> None then
      raise (DuplicatedBinding x);
    { mc with mc_modules = MMsym.add x obj mc.mc_modules }

  let import_mod p mod_ env =
    import (_up_mod true) p mod_ env

  (* -------------------------------------------------------------------- *)
  let lookup_tydecl qnx env =
    match lookup (fun mc -> mc.mc_tydecls) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_tydecl env p args, obj)

  let _up_tydecl candup mc x obj =
    if not candup && MMsym.last x mc.mc_tydecls <> None then
      raise (DuplicatedBinding x);
    { mc with mc_tydecls = MMsym.add x obj mc.mc_tydecls }

  let import_tydecl p tyd env =
    import (_up_tydecl true) (IPPath p) tyd env

  (* -------------------------------------------------------------------- *)
  let lookup_modty qnx env =
    match lookup (fun mc -> mc.mc_modsigs) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_modsig env p args, obj)

  let _up_modty candup mc x obj =
    if not candup && MMsym.last x mc.mc_modsigs <> None then
      raise (DuplicatedBinding x);
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

  let _up_operator candup mc x obj =
    if not candup && MMsym.last x mc.mc_operators <> None then
      raise (DuplicatedBinding x);
    { mc with mc_operators = MMsym.add x obj mc.mc_operators }

  let import_operator p op env =
    import (_up_operator true) (IPPath p) op env

  (* -------------------------------------------------------------------- *)
  let lookup_axiom qnx env =
    match lookup (fun mc -> mc.mc_axioms) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_axiom env p args, obj)

  let _up_axiom candup mc x obj =
    if not candup && MMsym.last x mc.mc_axioms <> None then
      raise (DuplicatedBinding x);
    { mc with mc_axioms = MMsym.add x obj mc.mc_axioms }

  let import_axiom p ax env =
    import (_up_axiom true) (IPPath p) ax env

  (* -------------------------------------------------------------------- *)
  let _up_theory candup mc x obj =
    if not candup && MMsym.last x mc.mc_theories <> None then
      raise (DuplicatedBinding x);
    { mc with mc_theories = MMsym.add x obj mc.mc_theories }

  let lookup_theory qnx env =
    match lookup (fun mc -> mc.mc_theories) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_th env p args, obj)

  let import_theory p th env =
    import (_up_theory true) (IPPath p) th env

  (* -------------------------------------------------------------------- *)
  let _up_mc candup mc p =
    let name = ibasename p in
    if not candup && MMsym.last name mc.mc_components <> None then
      raise (DuplicatedBinding name);
    { mc with mc_components =
        MMsym.add name p mc.mc_components }

  let import_mc p env =
    let mc = _up_mc true env.env_current p in
      { env with env_current = mc }

  (* ------------------------------------------------------------------ *)
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
          let mc = _up_mc false mc (IPPath mep) in
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

  let mc_of_module (env : env) (me : module_expr) =
    match env.env_scope.ec_scope with
    | `Theory ->
        let p1   = EcPath.pqname (root env) me.me_name
        and args = me.me_sig.mis_params in
          mc_of_module_r (p1, args, None) me

    | `Module mpath -> begin
       match mpath.EcPath.m_top with
       | `Concrete (p1, p2) ->
           let p2 = EcPath.pqoname p2 me.me_name in
             mc_of_module_r (p1, mpath.EcPath.m_args, Some p2) me

       | `Abstract _ -> assert false
    end

    | `Fun _ -> assert false

  (* ------------------------------------------------------------------ *)
  let mc_of_module_param (mid : EcIdent.t) (me : module_expr) =
    let xpath (x : symbol) =
      IPIdent (mid, Some (EcPath.psymbol x))
    in

    let mc1_of_module (mc : mc) = function
      | MI_Module _ -> assert false

      | MI_Variable v ->
          let vty =
            { vb_type = v.v_type;
              vb_kind = PVglob; }
          in
            _up_var false mc v.v_name (xpath v.v_name, vty)


      | MI_Function f ->
          _up_fun false mc f.f_name (xpath f.f_name, f)
    in
      List.fold_left
        mc1_of_module
        (empty_mc (Some me.me_sig.mis_params))
        me.me_comps

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
          let args = subme.me_sig.mis_params in
          let submcs = mc_of_module_r (expath subme.me_name, args, None) subme in
            (add2mc _up_mod subme.me_name subme mc, Some submcs)

      | CTh_theory (xsubth, subth) ->
          let submcs = mc_of_ctheory_r subscope (xsubth, subth) in
          let mc = _up_mc false mc (IPPath (expath xsubth)) in
            (add2mc _up_theory xsubth subth mc, Some submcs)

      | CTh_export _ -> (mc, None)
    in 

    let (mc, submcs) =
      List.map_fold mc1_of_ctheory (empty_mc None) th.cth_struct
    in
      ((x, mc), List.prmap (fun x -> x) submcs)

  let mc_of_ctheory (env : env) (x : symbol) (th : ctheory) =
    mc_of_ctheory_r (root env) (x, th)

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
    let path = EcPath.pqname (root env) x in

    { env with
        env_current = _up_mc true env.env_current (IPPath path);
        env_comps =
          Mip.change
            (fun mc -> Some (_up_mc false (oget mc) (IPPath path)))
            (IPPath (root env))
            (Mip.add (IPPath path) mc env.env_comps); }

  and bind_theory x th env =
    let (_, mc), submcs = mc_of_ctheory env x th in
    let env = bind _up_theory x th env in
    let env = bind_mc x mc env in
    let env =
      bind_submcs env
        (EcPath.pqname (root env) x)
        submcs
    in
      env

  and bind_mod x mod_ env =
    let (_, mc), submcs = mc_of_module env mod_ in
    let env = bind _up_mod x mod_ env in
    let env = bind_mc x mc env in
    let env =
      bind_submcs env
        (EcPath.pqname (root env) x)
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
exception InvalidStateForEnter

let enter mode (name : symbol) (env : env) =
  let path = EcPath.pqname (root env) name in

  if Mip.find_opt (IPPath path) env.env_comps <> None then
    raise (DuplicatedBinding name);

  match mode, env.env_scope.ec_scope with
  | `Theory, `Theory ->
      let env = MC.bind_mc name (empty_mc None) env in
        { env with
            env_scope = { ec_path = path; ec_scope = `Theory; };
            env_rb    = [];
            env_item  = []; }

  | `Module [], `Module mpath ->
      let mpath = EcPath.mqname mpath name in
      let env   = MC.bind_mc name (empty_mc None) env in
        { env with
            env_scope = { ec_path = path; ec_scope = `Module mpath; };
            env_rb    = [];
            env_item  = []; }

  | `Module params, `Theory ->
      let idents = List.map (fun (x, _) -> EcPath.mident x) params in
      let mpath  = EcPath.mpath_crt path idents None in
      let env    = MC.bind_mc name (empty_mc (Some params)) env in
        { env with
            env_scope = { ec_path = path; ec_scope = `Module mpath; };
            env_rb    = [];
            env_item  = []; }

  | `Fun, `Module mpath ->
      let xpath = EcPath.xpath_fun mpath name in
      let env   = MC.bind_mc name (empty_mc None) env in (* FIXME: remove *)
        { env with
            env_scope = { ec_path = path; ec_scope = `Fun xpath; };
            env_rb    = [];
            env_item  = []; }

  | _, _ ->
      raise InvalidStateForEnter

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

  let lookup (g : int) (me : symbol) (env : env) =
    let mems = MMsym.all me env.env_memories in
      try  Some (List.nth mems g)
      with Failure _ -> None

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
      (IPIdent (i, None), (0, p.EcPath.m_args))

  | `Concrete (p1, p2) ->
      let pr = odfl p1 (omap p2 (MC.pcat p1)) in
        (IPPath pr, ((EcPath.p_size p1)-1, p.EcPath.m_args))

let ipath_of_xpath (p : xpath) =
  match p.EcPath.x_sub.EcPath.p_node with
  | EcPath.Psymbol x ->
      let xt p =
        match p with
        | IPPath p -> Some (IPPath (EcPath.pqname p x))
        | IPIdent (m, None) -> Some (IPIdent (m, Some (EcPath.psymbol x)))
        | _ -> None
      in

      let (p, (i, a)) = ipath_of_mpath p.EcPath.x_top in
        omap (xt p) (fun p -> (p, (i+1, a)))

  | _ -> None

(* -------------------------------------------------------------------- *)
let try_lf f =
  try  Some (f ())
  with LookupFailure _ -> None

(* -------------------------------------------------------------------- *)
module Fun = struct
  type t = EcModules.function_

  let enter (x : symbol) (env : env) =
    enter `Fun x env

  let by_ipath (p : ipath) (env : env) =
    MC.by_path (fun mc -> mc.mc_functions) p env

  let by_xpath_r ~susp ~spsc (p : EcPath.xpath) (env : env) =
    match ipath_of_xpath p with
    | None -> lookup_error (`XPath p)

    | Some (ip, (i, args)) -> begin
        match MC.by_path (fun mc -> mc.mc_functions) ip env with
        | None -> lookup_error (`XPath p)
        | Some (params, o) ->
           let ((spi, params), _op) = MC._downpath_for_fun spsc env ip params in
           if i <> spi || susp && args <> [] then
             assert false;
           if not susp && List.length args <> List.length params then
             (Format.printf "args = %i; params = %i@." (List.length args)
                (List.length params);
             assert false);

           if susp then
             o
           else
             let s =
               List.fold_left2
                 (fun s (x, _) a -> EcSubst.add_module s x a)
                 EcSubst.empty params args
             in
             EcSubst.subst_function s o
      end

  let by_xpath (p : EcPath.xpath) (env : env) =
    by_xpath_r ~susp:false ~spsc:true p env

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
    adds_in_memenv mem fun_.f_sig.fs_params

  let actmem_post me path fun_ =
    let mem = EcMemory.empty_local me path in
    add_in_memenv mem {v_name = "res"; v_type = fun_.f_sig.fs_ret}

  let actmem_body me path fun_ =
    let mem = actmem_pre me path fun_ in
    match fun_.f_def with
    | FBabs _ -> assert false (* FIXME error message *)
    | FBdef fd -> fd, adds_in_memenv mem fd.f_locals

  let actmem_body_anonym me path locals =
    let mem = EcMemory.empty_local me path in
    adds_in_memenv mem locals
      
  let inv_memenv env = 
    let path  = mroot env in
    let xpath = EcPath.xpath_fun path "" in (* dummy value *)
    let meml  = EcMemory.empty_local EcFol.mleft xpath in
    let memr  = EcMemory.empty_local EcFol.mright xpath in
    Memory.push_all [meml;memr] env
    

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
end

(* -------------------------------------------------------------------- *)
module Var = struct
  type t = varbind

  let by_xpath_r (spsc : bool) (p : xpath) (env : env) =
    match ipath_of_xpath p with
    | None -> begin
      match p.EcPath.x_sub.EcPath.p_node with
      | EcPath.Pqname ({ p_node = EcPath.Psymbol f }, x) -> begin
        let mp = EcPath.mpath p.EcPath.x_top.EcPath.m_top [] in
        let fp = EcPath.xpath_fun mp f in
        let f  = Fun.by_xpath_r ~susp:true ~spsc fp env in
          try
            let v = List.find (fun v -> v.v_name = x) f.f_sig.fs_params in
              { vb_type = v.v_type; vb_kind = PVloc; }
          with Not_found -> begin
            match f.f_def with
            | FBdef def -> begin
              try
                let v = List.find (fun v -> v.v_name = x) def.f_locals in
                  { vb_type = v.v_type; vb_kind = PVloc; }
              with Not_found -> lookup_error (`XPath p)
            end
            | FBabs _ -> lookup_error (`XPath p)
          end
      end
      | _ -> lookup_error (`XPath p)
    end

    | Some (ip, (i, _args)) -> begin
        match MC.by_path (fun mc -> mc.mc_variables) ip env with
        | None -> lookup_error (`XPath p)
        | Some (params, o) ->
           let local = o.vb_kind = EcTypes.PVloc in
           let ((spi, _params), _) = MC._downpath_for_var local spsc env ip params in
             if i <> spi then
               assert false;
             o
      end

  let by_xpath (p : xpath) (env : env) =
    by_xpath_r true p env

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
                let pv = pv_loc mp (snd qname) in
                Some (pv, ty)
            end

      | _ -> None
    in
    match obind side inmem with
    | None -> 
        (* TODO FIXME, suspended for local program variable *)
        let (((_, _), p), x) = MC.lookup_var qname env in
        (pv p x.vb_kind, x.vb_type)

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
module Mod = struct
  type t = module_expr

  let unsuspend_r f (i, args) (spi, params) o =
    (* FIXME: it seems that the substitution is performed even if params = [] *)
    if i <> spi || List.length args <> List.length params then
      assert false;
    let s =
      List.fold_left2
        (fun s (x, _) a -> EcSubst.add_module s x a)
        EcSubst.empty params args
    in
      f s o

  let clear_sig sig_ =
    { mis_params = [];
      mis_body   =
        List.map
          (function Tys_function(s, _) -> Tys_function(s, {oi_calls = []}))
          sig_.mis_body }

  let unsuspend (i, args) (spi, params) me =
    let me =
      match args with
      | [] -> me
      | _  -> { me with me_sig = clear_sig me.me_sig }
    in
      unsuspend_r EcSubst.subst_module (i, args) (spi, params) me

  let by_ipath_r (spsc : bool) (p : ipath) (env : env) =
    let obj = MC.by_path (fun mc -> mc.mc_modules) p env in
      omap obj
        (fun (args, obj) ->
          (fst (MC._downpath_for_mod spsc env p args), obj))

  let by_ipath (p : ipath) (env : env) =
    by_ipath_r true p env

  let by_path (p : mpath_top) (env : env) =
    by_ipath (ipath_of_mpath_opt p) env

  let by_path_opt (p : mpath_top) (env : env) =
    try_lf (fun () -> by_path p env)

  let by_mpath (p : mpath) (env : env) =
    let (ip, (i, args)) = ipath_of_mpath p in

      match MC.by_path (fun mc -> mc.mc_modules) ip env with
      | None ->
          lookup_error (`MPath p)

      | Some (params, o) ->
          let ((spi, params), op) = MC._downpath_for_mod false env ip params in
          let (params, _istop) =
            match op.EcPath.m_top with
            | `Concrete (_, Some _) ->
                assert (o.me_sig.mis_params <> []);
                (params, false)
        
            | `Concrete (p, None) ->
                assert ((params = []) || ((spi+1) = EcPath.p_size p));
                ((if args = [] then [] else o.me_sig.mis_params), true)
        
            | `Abstract _m ->
                assert ((params = []) || spi = 0);
                ((if args = [] then [] else o.me_sig.mis_params), true)
          in
          unsuspend (i, args) (spi, params) o

  let by_mpath_opt (p : EcPath.mpath) (env : env) =
    try_lf (fun () -> by_mpath p env)

  let add (p : EcPath.mpath) (env : env) =
    let obj = by_mpath p env in
      MC.import_mod (fst (ipath_of_mpath p)) obj env

  let lookup qname (env : env) =
    let (((_, _a), p), x) = MC.lookup_mod qname env in
    (* FIXME : Ca c'est bizare quand on fait des foncteurs *)
(*      if a <> [] then
        raise (LookupFailure (`QSymbol qname)); *)
      (p, x)

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let sp_lookup qname (env : env) =
    let (((i, a), p), x) = MC.lookup_mod qname env in
    let obj = { sp_target = x; sp_params = (i, a); } in
      (p, obj)

  let sp_lookup_opt name env =
    try_lf (fun () -> sp_lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let bind name me env =
    assert (me.me_name = name);
    let env = MC.bind_mod name me env in
    let (w3, rb) =
      EcWhy3.add_mod_exp env.env_w3
          (EcPath.pqname (root env) name) me
    in
      { env with
        env_w3   = w3;
        env_rb   = rb @ env.env_rb;
        env_item = CTh_module me :: env.env_item }

  let me_of_mt env name modty restr = 
    let modsig =
      let modsig =
        match
          omap
            (MC.by_path
               (fun mc -> mc.mc_modsigs)
               (IPPath modty.mt_name) env)
            check_not_suspended
        with
        | None -> lookup_error (`Path modty.mt_name)
        | Some x -> x
      in
      EcSubst.subst_modsig
        ~params:(List.map fst modty.mt_params) EcSubst.empty modsig
    in
    module_expr_of_module_sig name modty modsig restr
    
  let bind_local name modty restr env =
(*    let modsig =
      let modsig =
        match
          omap
            (MC.by_path
               (fun mc -> mc.mc_modsigs)
               (IPPath modty.mt_name) env)
            check_not_suspended
        with
        | None -> lookup_error (`Path modty.mt_name)
        | Some x -> x
      in
        EcSubst.subst_modsig
          ~params:(List.map fst modty.mt_params) EcSubst.empty modsig
    in
    let me    = module_expr_of_module_sig name modty modsig restr in *)
    let me = me_of_mt env name modty restr in
    let path  = IPIdent (name, None) in
    let comps = MC.mc_of_module_param name me in

    let env =
      { env with
          env_current = (
            let current = env.env_current in
            let current = MC._up_mc  true current path in
            let current = MC._up_mod true current me.me_name (path, me) in
              current);
          env_comps = Mip.add path comps env.env_comps; }
    in
      env

  let bind_locals bindings env =
    List.fold_left
      (fun env (name, me) -> bind_local name me EcPath.Sm.empty env)
      env bindings

  let enter name params env =
    let env = enter (`Module params) name env in
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
          (EcPath.pqname (root env) name) ty
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
    match Mod.by_ipath_r true ip env with
    | Some ((spi, params), ({ me_body = ME_Alias alias } as m)) ->
      assert (m.me_sig.mis_params = []);
      let p = 
        Mod.unsuspend_r EcSubst.subst_mpath (i, args) (spi, params) alias in
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
          EcPath.mpath_crt p1 pr.EcPath.m_args (Some (EcPath.pqoname p2 name))
      end
    end

  let rec add_uses env rm us mp =
    let mp  = norm_mpath env mp in
    let top = EcPath.m_functor mp in
    let us  =
      if EcPath.Sm.mem top rm then us 
      else
        let us = 
          match (Mod.by_mpath top env).me_body with
          | ME_Structure ms -> EcPath.Sm.union ms.ms_uses us
          | ME_Decl _       -> us
          | _ -> assert false in
        EcPath.Sm.add top us in
    List.fold_left (add_uses env rm) us mp.EcPath.m_args 

  let top_uses env mp = add_uses env EcPath.Sm.empty EcPath.Sm.empty mp

  let norm_restr env restr = 
    EcPath.Sm.fold (fun mp r -> add_uses env EcPath.Sm.empty r mp)
      EcPath.Sm.empty restr

  let norm_xpath env p =
    EcPath.xpath (norm_mpath env p.EcPath.x_top) p.EcPath.x_sub

  let norm_pvar env pv = 
    let p = norm_xpath env pv.pv_name in
    if   x_equal p pv.pv_name
    then pv
    else EcTypes.pv p pv.pv_kind 

  let globals env m mp = 
    match (Mod.by_mpath mp env).me_body with
    | ME_Structure ms ->
        (* FIXME: What to do with the module parameter *)
      let sx = 
        EcPath.Mx.fold (fun x ty l -> 
          f_pvar (pv_glob x) ty m :: l) 
          ms.ms_vars [] in
      f_tuple sx, ms.ms_uses
    | _ -> assert false

  let rec norm_glob env m mp = 
    let mp = norm_mpath env mp in
    let gtop = 
      match mp.EcPath.m_top with
      | `Abstract _ -> f_glob (EcPath.mpath mp.EcPath.m_top []) m
      | `Concrete(p,_) -> 
        let top = EcPath.mpath (`Concrete(p,None)) mp.EcPath.m_args in
        let sx,us = globals env m top in
        let us = 
          List.map (fun mp -> fst (globals env m mp)) (EcPath.Sm.elements us) in
        f_tuple (sx::us) in
    let gargs = List.map (norm_glob env m) mp.EcPath.m_args in
    f_tuple (gtop :: gargs)

  let norm_tglob env mp =
    let g = (norm_glob env mhr mp) in
    g.f_ty

  let tglob_reducible env mp = 
    match (norm_tglob env mp).ty_node with
    | Tglob mp' -> not (EcPath.m_equal mp mp')
    | _ -> true

  let norm_ty env = 
    EcTypes.Hty.memo_rec 107 (
      fun aux ty ->
        match ty.ty_node with
        | Tglob mp -> norm_tglob env mp
        | _ -> ty_map aux ty) 
    
  let norm_form env =
    let norm_xp = EcPath.Hx.memo 107 (norm_xpath env) in
    let norm_pv pv =
      let p = norm_xp pv.pv_name in
      if   x_equal p pv.pv_name
      then pv
      else EcTypes.pv p pv.pv_kind 
    in
    let norm_ty : ty -> ty = norm_ty env in

    let norm_gty (id,gty) = 
      let gty = 
        match gty with
        | GTty ty -> GTty (norm_ty ty)
        | GTmodty (mt,restr) ->
          GTmodty(mt, Sm.fold (fun mp r -> Sm.add (norm_mpath env mp) r) restr Sm.empty)
        | GTmem None -> GTmem None
        | GTmem (Some mt) -> 
          let me = EcMemory.empty_local id (norm_xp (EcMemory.lmt_xpath mt)) in
          let me = Msym.fold (fun id ty me ->
            EcMemory.bind id (norm_ty ty) me) (EcMemory.lmt_bindings mt) me  in
          GTmem (snd me) in
      id,gty in
                
    let norm_form =
      EcFol.Hf.memo_rec 107 (fun aux f ->
        match f.f_node with
        | Fquant(q,bd,f) ->     
          let bd = List.map norm_gty bd in
          f_quant q bd (aux f)

        | Fpvar(p,m) ->
          let p' = norm_pv p in
          if p == p' then f else
            f_pvar p' f.f_ty m

        | Fglob(p,m) -> norm_glob env m p

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

        | _ -> EcFol.f_map norm_ty aux f) in
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

  exception ModTypeNotEquiv

  let rec mod_type_equiv (env : env) (mty1 : module_type) (mty2 : module_type) =
    if not (EcPath.p_equal mty1.mt_name mty2.mt_name) then
      raise ModTypeNotEquiv;

    if List.length mty1.mt_params <> List.length mty2.mt_params then
      raise ModTypeNotEquiv;
    if List.length mty1.mt_args <> List.length mty2.mt_args then
      raise ModTypeNotEquiv;

    let subst =
      List.fold_left2
        (fun subst (x1, p1) (x2, p2) ->
          let p1 = EcSubst.subst_modtype subst p1 in
          let p2 = EcSubst.subst_modtype subst p2 in
            mod_type_equiv env p1 p2;
            EcSubst.add_module subst x1 (EcPath.mident x2))
        EcSubst.empty mty1.mt_params mty2.mt_params
    in

    if not (
         List.all2
           (fun m1 m2 ->
             let m1 = NormMp.norm_mpath env (EcSubst.subst_mpath subst m1) in
             let m2 = NormMp.norm_mpath env (EcSubst.subst_mpath subst m2) in
               EcPath.m_equal m1 m2)
            mty1.mt_args mty2.mt_args) then
      raise ModTypeNotEquiv

  let mod_type_equiv env mty1 mty2 =
    try  mod_type_equiv env mty1 mty2; true
    with ModTypeNotEquiv -> false

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
          (EcPath.pqname (root env) name) op
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
    let f = 
      match op.op_kind with
      | OB_oper(Some e) -> EcFol.form_of_expr EcFol.mhr e
      | OB_pred(Some idsf) -> idsf
      | _ -> raise NotReducible
    in
    EcFol.Fsubst.subst_tvar (EcTypes.Tvar.init op.op_tparams tys) f
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
        (EcPath.pqname (root env) name)
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
    enter `Theory name env

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

    let (w3env, rb) =
      compile (EcPath.pqname (root env) name) env.env_w3 th
    in

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
            let env = MC.import_mod (IPPath (xpath m.me_name)) m env in
            let env = MC.import_mc (IPPath (xpath m.me_name)) env in
              env

        | CTh_export p ->
            import env p (by_path p env)

        | CTh_theory (x, th) ->
            let env = MC.import_theory (xpath x) th env in
            let env = MC.import_mc (IPPath (xpath x)) env in
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
    let topmc = MC._up_mc false topmc (IPPath thpath) in

    let current = env.env_current in
    let current = MC._up_theory true current x (IPPath thpath, cth.cth3_theory) in
    let current = MC._up_mc true current (IPPath thpath) in

    let comps = env.env_comps in
    let comps = Mip.add (IPPath rootnm) topmc comps in

    { env with
        env_current = current;
        env_comps   = comps;
        env_w3      = EcWhy3.rebind env.env_w3 cth.cth3_rebind; }
end

(* -------------------------------------------------------------------- *)
let import_w3 env th rd =
  let lth, rbi = EcWhy3.import_w3 env.env_w3 (root env) th rd in
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
  let env = enter `Theory EcCoreLib.id_Pervasive env0 in
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
  let res = EcWhy3.check_goal (Mod.me_of_mt env) env.env_w3 pi ld in
  res


module LDecl = struct
  open EcIdent
  type error = 
    | UnknownSymbol   of EcSymbols.symbol 
    | UnknownIdent    of EcIdent.t
    | NotAVariable    of EcIdent.t
    | NotAHypothesis  of EcIdent.t
    | CanNotClear     of EcIdent.t * EcIdent.t
    | DuplicateIdent  of EcIdent.t
    | DuplicateSymbol of EcSymbols.symbol

  exception Ldecl_error of error

  let pp_error fmt = function
    | UnknownSymbol  s  -> 
        Format.fprintf fmt "Unknown symbol %s" s
    | UnknownIdent   id -> 
        Format.fprintf fmt "Unknown ident  %s, please report" 
          (EcIdent.tostring id)
    | NotAVariable   id ->
        Format.fprintf fmt "The symbol %s is not a variable" (EcIdent.name id)
    | NotAHypothesis id ->
        Format.fprintf fmt "The symbol %s is not a hypothesis" (EcIdent.name id)
    | CanNotClear (id1,id2) ->
        Format.fprintf fmt "Cannot clear %s it is used in %s"
          (EcIdent.name id1) (EcIdent.name id2)
    | DuplicateIdent id ->
        Format.fprintf fmt "Duplicate ident %s, please report" 
          (EcIdent.tostring id)
    | DuplicateSymbol s ->
        Format.fprintf fmt 
          "An hypothesis or a variable named %s already exists" s

  let _ = EcPException.register (fun fmt exn ->
    match exn with
    | Ldecl_error e -> pp_error fmt e 
    | _ -> raise exn)

  let error e = raise (Ldecl_error e)

  let lookup s hyps = 
    try 
      List.find (fun (id,_) -> s = EcIdent.name id) hyps.h_local 
    with _ -> error (UnknownSymbol s)

  let lookup_by_id id hyps = 
    try 
      List.assoc_eq EcIdent.id_equal id hyps.h_local 
    with _ -> error (UnknownIdent id)

  let get_hyp = function
    | (id, LD_hyp f) -> (id,f)
    | (id,_) -> error (NotAHypothesis id) 

  let get_var = function
    | (id, LD_var (ty,_)) -> (id, ty)
    | (id,_) -> error (NotAVariable id) 

  let lookup_hyp s hyps = get_hyp (lookup s hyps)

  let has_hyp s hyps = 
    try ignore(lookup_hyp s hyps); true
    with _ -> false

  let lookup_hyp_by_id id hyps = snd (get_hyp (id, lookup_by_id id hyps))

  let lookup_var s hyps = get_var (lookup s hyps) 

  let lookup_var_by_id id hyps = snd (get_var (id, lookup_by_id id hyps))

  let reducible_var id hyps = 
    try 
      match lookup_by_id id hyps with
      | LD_var(_, Some _) -> true
      | _ -> false
    with _ -> false

  let reduce_var id hyps =
    try 
      match lookup_by_id id hyps with
      | LD_var(_, Some f) -> f
      | _ -> raise NotReducible
    with _ -> raise NotReducible

  let has_symbol s hyps = 
    try ignore(lookup s hyps); true with _ -> false 

  let has_ident id hyps = 
    try ignore(lookup_by_id id hyps); true with _ -> false 

  let check_id id hyps = 
    if has_ident id hyps then error (DuplicateIdent id)
    else 
      let s = EcIdent.name id in
      if s <> "_" && has_symbol s hyps then error (DuplicateSymbol s) 

  let add_local id ld hyps = 
    check_id id hyps;
    { hyps with h_local = (id,ld)::hyps.h_local }

  let fresh_id hyps s = 
    let s = 
      if s = "_" || not (has_symbol s hyps) then s
      else 
        let rec aux n = 
          let s = s ^ string_of_int n in
          if has_symbol s hyps then aux (n+1) else s in
        aux 0 in
    EcIdent.create s
      
  let fresh_ids hyps s =
    let hyps = ref hyps in
    List.map (fun s -> 
      let id = fresh_id !hyps s in
      hyps := add_local id (LD_var(tbool,None)) !hyps;
      id) s

  let clear ids hyps = 
    let fv_lk = function
      | LD_var (_,Some f) | LD_hyp f -> f.f_fv
      | _ -> Mid.empty in
    let check (id,lk) = 
      if EcIdent.Sid.mem id ids then false
      else
        let fv = fv_lk lk in
        if Mid.set_disjoint ids fv then true
        else 
          let inter = Mid.set_inter ids fv in
          error (CanNotClear(Sid.choose inter, id)) in
    { hyps with h_local = List.filter check hyps.h_local }

  let ld_subst s ld = 
    match ld with
    | LD_var (ty, body) ->
      LD_var (s.fs_ty ty, omap body (f_subst s))
    | LD_mem mt ->
      LD_mem (EcMemory.mt_substm s.fs_sty.ts_p s.fs_mp s.fs_ty mt)
    | LD_modty(p,r) ->
      let sub = s.fs_sty.ts_mp in
      let p' = EcModules.mty_subst s.fs_sty.ts_p sub p in
      let r' = 
        EcPath.Sm.fold (fun m r' -> EcPath.Sm.add (sub m) r') r 
          EcPath.Sm.empty in
      LD_modty(p',r')
    | LD_hyp f -> LD_hyp (f_subst s f)

end
