(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcTypes
open EcCoreFol
open EcMemory
open EcDecl
open EcModules
open EcTheory
open EcBaseLogic

(* -------------------------------------------------------------------- *)
module Ssym = EcSymbols.Ssym
module Msym = EcSymbols.Msym
module Mp   = EcPath.Mp
module Sid  = EcIdent.Sid
module Mid  = EcIdent.Mid
module TC   = EcTypeClass
module Mint = EcMaps.Mint

(* -------------------------------------------------------------------- *)
type 'a suspension = {
  sp_target : 'a;
  sp_params : int * (EcIdent.t * module_type) list;
}

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

let ippath_as_path (ip : ipath) =
  match ip with IPPath p -> p | _ -> assert false

(* -------------------------------------------------------------------- *)
type varbind = {
  vb_type  : EcTypes.ty;
  vb_kind  : [`Var of EcTypes.pvar_kind | `Proj of int];
}

type obj = [
  | `Variable of varbind
  | `Function of function_
  | `Module   of module_expr
  | `ModSig   of module_sig
  | `TypeDecl of EcDecl.tydecl
  | `Operator of EcDecl.operator
  | `Axiom    of EcDecl.axiom
  | `Theory   of (ctheory * thmode)
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
  mc_theories   : (ipath * (ctheory * thmode)) MMsym.t;
  mc_typeclasses: (ipath * typeclass) MMsym.t;
  mc_rwbase     : (ipath * path) MMsym.t;
  mc_components : ipath MMsym.t;
}

type use = {
  us_pv : ty Mx.t;
  us_gl : Sid.t;
}

type env_norm = {
  norm_mp   : EcPath.mpath Mm.t;
  norm_xpv  : EcPath.xpath Mx.t;   (* for global program variable *)
  norm_xfun : EcPath.xpath Mx.t;   (* for fun and local program variable *)
  mod_use   : use Mm.t;
  get_restr : use Mm.t;
}

(* -------------------------------------------------------------------- *)
type red_topsym = [ `Path of path | `Tuple ]

module Mrd = EcMaps.Map.Make(struct
  type t = red_topsym

  let compare (p1 : t) (p2 : t) =
    match p1, p2 with
    | `Path p1, `Path p2 ->  EcPath.p_compare p1 p2
    | `Tuple  , `Tuple   ->  0
    | `Tuple  , `Path _  -> -1
    | `Path _ , `Tuple   ->  1
end)

(* -------------------------------------------------------------------- *)
type preenv = {
  env_top      : EcPath.path option;
  env_gstate   : EcGState.gstate;
  env_scope    : escope;
  env_current  : mc;
  env_comps    : mc Mip.t;
  env_locals   : (EcIdent.t * EcTypes.ty) MMsym.t;
  env_memories : EcMemory.memenv MMsym.t;
  env_actmem   : EcMemory.memory option;
  env_abs_st   : EcModules.abs_uses Mid.t;
  env_tci      : ((ty_params * ty) * tcinstance) list;
  env_tc       : TC.graph;
  env_rwbase   : Sp.t Mip.t;
  env_atbase   : (path list Mint.t) Msym.t;
  env_redbase  : mredinfo;
  env_ntbase   : (path * env_notation) list;
  env_modlcs   : Sid.t;                 (* declared modules *)
  env_item     : ctheory_item list;     (* in reverse order *)
  env_norm     : env_norm ref;
}

and escope = {
  ec_path  : EcPath.path;
  ec_scope : [ `Theory
             | `Module of EcPath.mpath
             | `Fun    of EcPath.xpath ];
}

and tcinstance = [
  | `Ring    of EcDecl.ring
  | `Field   of EcDecl.field
  | `General of EcPath.path
]

and redinfo =
  { ri_priomap : (EcTheory.rule list) Mint.t;
    ri_list    : (EcTheory.rule list) Lazy.t; }

and mredinfo = redinfo Mrd.t

and env_notation = ty_params * EcDecl.notation

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
let astop (env : env) =
  { env with env_top = Some (root env); }

(* -------------------------------------------------------------------- *)
let gstate (env : env) =
  env.env_gstate

(* -------------------------------------------------------------------- *)
let notify ?(immediate = true) (env : preenv) (lvl : EcGState.loglevel) msg =
  let buf  = Buffer.create 0 in
  let fbuf = Format.formatter_of_buffer buf in
  ignore immediate; Format.kfprintf
    (fun _ ->
      Format.pp_print_flush fbuf ();
      EcGState.notify lvl (lazy (Buffer.contents buf)) (gstate env))
    fbuf msg

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
  mc_typeclasses= MMsym.empty;
  mc_rwbase     = MMsym.empty;
  mc_components = MMsym.empty;
}

(* -------------------------------------------------------------------- *)
let empty_norm_cache =
  { norm_mp   = Mm.empty;
    norm_xpv  = Mx.empty;
    norm_xfun = Mx.empty;
    mod_use   = Mm.empty;
    get_restr = Mm.empty; }

(* -------------------------------------------------------------------- *)
let empty gstate =
  let name = EcCoreLib.i_top in
  let path = EcPath.psymbol name in

  let env_current =
    let icomps = MMsym.add name (IPPath path) MMsym.empty in
    { (empty_mc None) with mc_components = icomps } in

  { env_top      = None;
    env_gstate   = gstate;
    env_scope    = { ec_path = path; ec_scope = `Theory; };
    env_current  = env_current;
    env_comps    = Mip.singleton (IPPath path) (empty_mc None);
    env_locals   = MMsym.empty;
    env_memories = MMsym.empty;
    env_actmem   = None;
    env_abs_st   = Mid.empty;
    env_tci      = [];
    env_tc       = TC.Graph.empty;
    env_rwbase   = Mip.empty;
    env_atbase   = Msym.empty;
    env_redbase  = Mrd.empty;
    env_ntbase   = [];
    env_modlcs   = Sid.empty;
    env_item     = [];
    env_norm     = ref empty_norm_cache; }

(* -------------------------------------------------------------------- *)
let copy (env : env) =
  { env with env_gstate = EcGState.copy env.env_gstate }

(* -------------------------------------------------------------------- *)
type lookup_error = [
  | `XPath   of xpath
  | `MPath   of mpath
  | `Path    of path
  | `QSymbol of qsymbol
  | `AbsStmt of EcIdent.t
]

exception LookupFailure of lookup_error

let pp_lookup_failure fmt e =
  let p =
    match e with
    | `XPath   p -> EcPath.x_tostring p
    | `MPath   p -> EcPath.m_tostring p
    | `Path    p -> EcPath.tostring p
    | `QSymbol p -> string_of_qsymbol p
    | `AbsStmt p -> EcIdent.tostring p
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
exception NotReducible

(* -------------------------------------------------------------------- *)
exception DuplicatedBinding of symbol

let _ = EcPException.register (fun fmt exn ->
  match exn with
  | DuplicatedBinding s ->
    Format.fprintf fmt "the symbol %s already exists" s
  | _ -> raise exn)

(* -------------------------------------------------------------------- *)
module MC = struct
  (* ------------------------------------------------------------------ *)
  let top_path = EcPath.psymbol EcCoreLib.i_top

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
        | `Local _ -> None
      in
        match env.env_scope.ec_scope with
        | `Theory   -> None
        | `Module m -> prefix_of_mtop m.EcPath.m_top
        | `Fun    m -> prefix_of_mtop m.EcPath.x_top.EcPath.m_top
    in

    try
      let (l, a, r) = List.find_pivot (fun x -> x <> None) args in
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
                      (ap, odfl false (prefix |> omap (EcPath.p_equal p)))
                end
          end

          | IPIdent (m, x) -> begin
              if i <> 0 then assert false;

              match x |> omap (fun x -> x.EcPath.p_node) with
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
        | `Local _ -> None
      in
        match env.env_scope.ec_scope with
        | `Theory   -> None
        | `Module m -> prefix_of_mtop m.EcPath.m_top
        | `Fun    m -> prefix_of_mtop m.EcPath.x_top.EcPath.m_top
    in

    let (l, a, r) =
      try
        List.find_pivot (fun x -> x <> None) args
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
               odfl false (prefix |> omap (EcPath.p_equal p)))

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

  let _downpath_for_tydecl    = _downpath_for_th
  let _downpath_for_modsig    = _downpath_for_th
  let _downpath_for_operator  = _downpath_for_th
  let _downpath_for_axiom     = _downpath_for_th
  let _downpath_for_typeclass = _downpath_for_th
  let _downpath_for_rwbase    = _downpath_for_th

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
        assert (is_none (EcPath.prefix p));
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
              (fun mc -> (mc, x))
              (Mip.find_opt (IPPath p) env.env_comps)
      end

      | IPIdent (id, None) ->
          Some (env.env_current, EcIdent.name id)

      | IPIdent (m, Some p) ->
          let prefix = EcPath.prefix p in
          let name   = EcPath.basename p in
            omap
              (fun mc -> (mc, name))
              (Mip.find_opt (IPIdent (m, prefix)) env.env_comps)
    in

    let lookup (mc, x) =
      List.filter
        (fun (ip, _) -> IPathC.compare ip p = 0)
        (MMsym.all x (proj mc))
    in
      match mcx |> omap lookup with
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

    | x :: qn when x = EcCoreLib.i_self && is_some env.env_top ->
        let p = IPPath (path_of_qn (oget env.env_top) qn) in
        Mip.find_opt p env.env_comps

    | x :: qn ->
        let x = if x = EcCoreLib.i_self then EcCoreLib.i_top else x in
        let p =
          (MMsym.last x env.env_current.mc_components) |>
            obind
              (fun p ->
                match p, qn with
                | IPIdent _, [] -> Some p
                | IPIdent _, _  -> None
                | IPPath  p, _  -> Some (IPPath (path_of_qn p qn)))
        in
          p |> obind (fun p -> Mip.find_opt p env.env_comps)

  (* ------------------------------------------------------------------ *)
  let lookup proj (qn, x) env =
    let mc = lookup_mc qn env in
      omap
        (fun (p, obj) -> (p, (_params_of_ipath p env, obj)))
        (mc |> obind (fun mc -> MMsym.last x (proj mc)))

  (* ------------------------------------------------------------------ *)
  let lookup_all proj (qn, x) env =
    let mc   = lookup_mc qn env in
    let objs = odfl [] (mc |> omap (fun mc -> MMsym.all x (proj mc))) in
    let _, objs =
      List.map_fold
        (fun ps ((p, _) as obj)->
          if   Sip.mem p ps
          then (ps, None)
          else (Sip.add p ps, Some obj))
        Sip.empty objs
    in
      List.pmap
        (omap (fun (p, obj) -> (p, (_params_of_ipath p env, obj))))
        objs

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
      let local =
        match obj.vb_kind with
        | `Var EcTypes.PVglob -> false
        | `Var EcTypes.PVloc | `Proj _ -> true in
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
  let lookup_axiom qnx env =
    match lookup (fun mc -> mc.mc_axioms) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_axiom env p args, obj)

  let lookup_axioms qnx env =
    List.map
      (fun (p, (args, obj)) -> (_downpath_for_axiom env p args, obj))
      (lookup_all (fun mc -> mc.mc_axioms) qnx env)

  let _up_axiom candup mc x obj =
    if not candup && MMsym.last x mc.mc_axioms <> None then
      raise (DuplicatedBinding x);
    { mc with mc_axioms = MMsym.add x obj mc.mc_axioms }

  let import_axiom p ax env =
    import (_up_axiom true) (IPPath p) ax env


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
    let module ELI = EcInductive in

    if not candup && MMsym.last x mc.mc_operators <> None then
      raise (DuplicatedBinding x);

    let mypath = lazy (ippath_as_path (fst obj)) in

    let mc = { mc with mc_operators = MMsym.add x obj mc.mc_operators } in
    let ax =
      match (snd obj).op_kind with
      | OB_pred (Some (PR_Ind pri)) ->
         let pri =
           { ELI.ip_path    = ippath_as_path (fst obj);
             ELI.ip_tparams = (snd obj).op_tparams;
             ELI.ip_prind   = pri; } in
         ELI.prind_schemes pri

      | _ -> [] in

    let ax = List.map (fun (name, (tv, cl)) ->
      let axp  = EcPath.prefix (Lazy.force mypath) in
      let axp  = IPPath (EcPath.pqoname axp name) in
      let ax   =
        { ax_kind    = `Axiom (Ssym.empty, false);
          ax_tparams = tv;
          ax_spec    = cl;
          ax_nosmt   = false; } in
      (name, (axp, ax))) ax in

    List.fold_left (fun mc -> curry (_up_axiom candup mc)) mc ax

  let import_operator p op env =
    import (_up_operator true) (IPPath p) op env

  (* -------------------------------------------------------------------- *)
  let lookup_tydecl qnx env =
    match lookup (fun mc -> mc.mc_tydecls) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_tydecl env p args, obj)

  let _up_tydecl candup mc x obj =
    if not candup && MMsym.last x mc.mc_tydecls <> None then
      raise (DuplicatedBinding x);
    let mc = { mc with mc_tydecls = MMsym.add x obj mc.mc_tydecls } in
    let mc =
      let mypath, tyd =
        match obj with IPPath p, x -> (p, x) | _, _ -> assert false in
      let ipath name = IPPath (EcPath.pqoname (EcPath.prefix mypath) name) in

      match tyd.tyd_type with
      | `Concrete _  -> mc
      | `Abstract _ -> mc

      | `Datatype dtype ->
          let cs      = dtype.tydt_ctors   in
          let schelim = dtype.tydt_schelim in
          let schcase = dtype.tydt_schcase in
          let params  = List.map (fun (x, _) -> tvar x) tyd.tyd_params in

          let for1 i (c, aty) =
            let aty = EcTypes.toarrow aty (tconstr mypath params) in
            let aty = EcSubst.freshen_type (tyd.tyd_params, aty) in
            let cop = mk_op (fst aty) (snd aty) (Some (OP_Constr (mypath, i))) in
            let cop = (ipath c, cop) in
              (c, cop)
          in

          let (schelim, schcase) =
            let do1 scheme name =
              let scname = Printf.sprintf "%s_%s" x name in
                (scname, { ax_tparams = tyd.tyd_params;
                           ax_spec    = scheme;
                           ax_kind    = `Axiom (Ssym.empty, false);
                           ax_nosmt   = true; })
            in
              (do1 schelim "ind", do1 schcase "case")
          in

          let cs = List.mapi for1 cs in
          let mc =
            List.fold_left
              (fun mc (c, cop) -> _up_operator candup mc c cop)
              mc cs
          in

          let mc = _up_axiom candup mc (fst schcase) (fst_map ipath schcase) in
          let mc = _up_axiom candup mc (fst schelim) (fst_map ipath schelim) in
            mc

      | `Record (scheme, fields) ->
          let params  = List.map (fun (x, _) -> tvar x) tyd.tyd_params in
          let nfields = List.length fields in
          let cfields =
            let for1 i (f, aty) =
              let aty = EcTypes.tfun (tconstr mypath params) aty in
              let aty = EcSubst.freshen_type (tyd.tyd_params, aty) in
              let fop = mk_op (fst aty) (snd aty) (Some (OP_Proj (mypath, i, nfields))) in
              let fop = (ipath f, fop) in
                (f, fop)
            in
              List.mapi for1 fields
          in

          let scheme =
            let scname = Printf.sprintf "%s_ind" x in
              (scname, { ax_tparams = tyd.tyd_params;
                         ax_spec    = scheme;
                         ax_kind    = `Axiom (Ssym.empty, false);
                         ax_nosmt   = true; })
          in

          let stname = Printf.sprintf "mk_%s" x in
          let stop   =
            let stty = toarrow (List.map snd fields) (tconstr mypath params) in
            let stty = EcSubst.freshen_type (tyd.tyd_params, stty) in
              mk_op (fst stty) (snd stty) (Some (OP_Record mypath))
          in

          let mc =
            List.fold_left
              (fun mc (f, fop) -> _up_operator candup mc f fop)
              mc ((stname, (ipath stname, stop)) :: cfields)
          in
            _up_axiom candup mc (fst scheme) (fst_map ipath scheme)

    in
      mc

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
  let lookup_typeclass qnx env =
    match lookup (fun mc -> mc.mc_typeclasses) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_typeclass env p args, obj)

  let _up_typeclass candup mc x obj =
    if not candup && MMsym.last x mc.mc_typeclasses <> None then
      raise (DuplicatedBinding x);
    let mc = { mc with mc_typeclasses = MMsym.add x obj mc.mc_typeclasses } in
    let mc =
      let mypath, tc =
        match obj with IPPath p, x -> (p, x) | _, _ -> assert false in
      let xpath name = EcPath.pqoname (EcPath.prefix mypath) name in

      let self = EcIdent.create "'self" in

      let tsubst =
        { ty_subst_id with
            ts_def = Mp.add mypath ([], tvar self) Mp.empty }
      in

      let operators =
        let on1 (opid, optype) =
          let opname = EcIdent.name opid in
          let optype = ty_subst tsubst optype in
          let opdecl = mk_op [(self, Sp.singleton mypath)] optype (Some OP_TC) in
            (opid, xpath opname, optype, opdecl)
        in
          List.map on1 tc.tc_ops
      in

      let fsubst =
        List.fold_left
          (fun s (x, xp, xty, _) ->
            let fop = EcCoreFol.f_op xp [tvar self] xty in
              Fsubst.f_bind_local s x fop)
          (Fsubst.f_subst_init ~sty:tsubst ())
          operators
      in

      let axioms =
        List.map
          (fun (x, ax) ->
            let ax = Fsubst.f_subst fsubst ax in
              (x, { ax_tparams = [(self, Sp.singleton mypath)];
                    ax_spec    = ax;
                    ax_kind    = `Axiom (Ssym.empty, false);
                    ax_nosmt   = true; }))
          tc.tc_axs
      in

      let mc =
        List.fold_left
          (fun mc (_, fpath, _, fop) ->
            _up_operator candup mc (EcPath.basename fpath) (IPPath fpath, fop))
          mc operators
      in
        List.fold_left
          (fun mc (x, ax) ->
            _up_axiom candup mc x (IPPath (xpath x), ax))
          mc axioms
    in
      mc

  let import_typeclass p ax env =
    import (_up_typeclass true) (IPPath p) ax env

  (* -------------------------------------------------------------------- *)
  let lookup_rwbase qnx env =
    match lookup (fun mc -> mc.mc_rwbase) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_rwbase env p args, obj)

  let _up_rwbase candup mc x obj=
    if not candup && MMsym.last x mc.mc_rwbase <> None then
      raise (DuplicatedBinding x);
    { mc with mc_rwbase = MMsym.add x obj mc.mc_rwbase }

  let import_rwbase p env =
    import (_up_rwbase true) (IPPath p) p env

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
              vb_kind = `Var PVglob; }
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
      ((me.me_name, mc), List.rev_pmap (fun x -> x) submcs)

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

       | `Local _ -> assert false
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
              vb_kind = `Var PVglob; }
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

      | CTh_theory (xsubth, ((items, `Concrete) as subth)) ->
          let submcs = mc_of_ctheory_r subscope (xsubth, items) in
          let mc = _up_mc false mc (IPPath (expath xsubth)) in
            (add2mc _up_theory xsubth subth mc, Some submcs)

      | CTh_theory (xsubth, ((_, `Abstract) as subth)) ->
          (add2mc _up_theory xsubth subth mc, None)

      | CTh_typeclass (x, tc) ->
          (add2mc _up_typeclass x tc mc, None)

      | CTh_baserw x ->
          (add2mc _up_rwbase x (expath x) mc, None)

      | CTh_export _ | CTh_addrw _ | CTh_instance _
      | CTh_auto   _ | CTh_reduction _ ->
          (mc, None)
    in

    let (mc, submcs) =
      List.map_fold mc1_of_ctheory (empty_mc None) th.cth_struct
    in
      ((x, mc), List.rev_pmap identity submcs)

  let mc_of_ctheory (env : env) (x : symbol) ((th, thmode) : ctheory * thmode) =
    match thmode with
    | `Concrete -> Some (mc_of_ctheory_r (root env) (x, th))
    | `Abstract -> None

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
    match mc_of_ctheory env x th with
    | None -> bind _up_theory x th env
    | Some ((_, mc), submcs) ->
        let env = bind _up_theory x th env in
        let env = bind_mc x mc env in
        bind_submcs env (EcPath.pqname (root env) x) submcs

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

  and bind_typeclass x tc env =
    bind _up_typeclass x tc env

  and bind_rwbase x p env =
    bind _up_rwbase x p env
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
            env_item  = []; }

  | `Module [], `Module mpath ->
      let mpath = EcPath.mqname mpath name in
      let env   = MC.bind_mc name (empty_mc None) env in
        { env with
            env_scope = { ec_path = path; ec_scope = `Module mpath; };
            env_item  = []; }

  | `Module params, `Theory ->
      let idents = List.map (fun (x, _) -> EcPath.mident x) params in
      let mpath  = EcPath.mpath_crt path idents None in
      let env    = MC.bind_mc name (empty_mc (Some params)) env in
        { env with
            env_scope = { ec_path = path; ec_scope = `Module mpath; };
            env_item  = []; }

  | `Fun, `Module mpath ->
      let xpath = EcPath.xpath_fun mpath name in
      let env   = MC.bind_mc name (empty_mc None) env in (* FIXME: remove *)
        { env with
            env_scope = { ec_path = path; ec_scope = `Fun xpath; };
            env_item  = []; }

  | _, _ ->
      raise InvalidStateForEnter

(* -------------------------------------------------------------------- *)
type meerror =
| UnknownMemory of [`Symbol of symbol | `Memory of memory]

exception MEError of meerror

(* -------------------------------------------------------------------- *)
module Memory = struct
  let all env =
    MMsym.fold (fun _ l all -> List.rev_append l all) env.env_memories []

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
let ipath_of_mpath (p : mpath) =
  match p.EcPath.m_top with
  | `Local i ->
      (IPIdent (i, None), (0, p.EcPath.m_args))

  | `Concrete (p1, p2) ->
      let pr = odfl p1 (p2 |> omap (MC.pcat p1)) in
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
        (xt p) |> omap (fun p -> (p, (i+1, a)))

  | _ -> None

(* -------------------------------------------------------------------- *)
let try_lf f =
  try  Some (f ())
  with LookupFailure _ -> None

(* ------------------------------------------------------------------ *)
module TypeClass = struct
  type t = typeclass

  let by_path_opt (p : EcPath.path) (env : env) =
    omap
      check_not_suspended
      (MC.by_path (fun mc -> mc.mc_typeclasses) (IPPath p) env)

  let by_path (p : EcPath.path) (env : env) =
    match by_path_opt p env with
    | None -> lookup_error (`Path p)
    | Some obj -> obj

  let add (p : EcPath.path) (env : env) =
    let obj = by_path p env in
      MC.import_typeclass p obj env

  let rebind name tc env =
    let env = MC.bind_typeclass name tc env in
      match tc.tc_prt with
      | None -> env
      | Some prt ->
          let myself = EcPath.pqname (root env) name in
            { env with env_tc = TC.Graph.add ~src:myself ~dst:prt env.env_tc }

  let bind name tc env =
    { (rebind name tc env) with
        env_item = CTh_typeclass (name, tc) :: env.env_item }

  let lookup qname (env : env) =
    MC.lookup_typeclass qname env

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let graph (env : env) =
    env.env_tc

  let bind_instance ty cr tci =
    (ty, cr) :: tci

  let add_instance ty cr env =
    { env with
        env_tci  = bind_instance ty cr env.env_tci;
        env_item = CTh_instance (ty, cr) :: env.env_item; }

  let get_instances env = env.env_tci
end

(* -------------------------------------------------------------------- *)
module BaseRw = struct
  let by_path_opt (p : EcPath.path) (env : env) =
    let ip = IPPath p in
    Mip.find_opt ip env.env_rwbase

  let by_path (p : EcPath.path) env =
    match by_path_opt p env with
    | None -> lookup_error (`Path p)
    | Some obj -> obj

  let lookup qname env =
    let _ip, p = MC.lookup_rwbase qname env in
    p, by_path p env

  let lookup_opt name env =
    try_lf (fun () -> lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let is_base name env =
    match lookup_opt name env with
    | None -> false
    | Some _ -> true

  let add name env =
    let p   = EcPath.pqname (root env) name in
    let env = MC.bind_rwbase name p env in
    let ip  = IPPath p in
    { env with
        env_rwbase = Mip.add ip Sp.empty env.env_rwbase;
        env_item   = CTh_baserw name :: env.env_item; }

  let addto p l env =
    { env with
        env_rwbase =
          Mip.change
            (omap (fun s -> List.fold_left (fun s r -> Sp.add r s) s l))
            (IPPath p) env.env_rwbase;
        env_item = CTh_addrw (p, l) :: env.env_item; }

end

(* -------------------------------------------------------------------- *)
module Reduction = struct
  type rule   = EcTheory.rule
  type topsym = red_topsym

  let add_rule ((_, rule) : path * rule option) (db : mredinfo) =
    match rule with None -> db | Some rule ->

    let p =
      match rule.rl_ptn with
      | Rule (`Op p , _) -> `Path (fst p)
      | Rule (`Tuple, _) -> `Tuple
      | Var _ | Int _ -> assert false in

    Mrd.change (fun rls ->
      let { ri_priomap } =
        match rls with
        | None   -> { ri_priomap = Mint.empty; ri_list = Lazy.from_val [] }
        | Some x -> x in

      let ri_priomap =
        let change prules = Some (odfl [] prules @ [rule]) in
        Mint.change change (abs rule.rl_prio) ri_priomap in

      let ri_list =
        Lazy.from_fun (fun () -> List.flatten (Mint.values ri_priomap)) in

      Some { ri_priomap; ri_list }) p db

  let add_rules (rules : (path * rule option) list) (db : mredinfo) =
    List.fold_left ((^~) add_rule) db rules

  let add (rules : (path * rule_option * rule option) list) (env : env) =
    let rstrip = List.map (fun (x, _, y) -> (x, y)) rules in
    { env with
        env_redbase = add_rules rstrip env.env_redbase;
        env_item    = CTh_reduction rules :: env.env_item; }

  let add1 (prule : path * rule_option * rule option) (env : env) =
    add [prule] env

  let get (p : topsym) (env : env) =
    Mrd.find_opt p env.env_redbase
    |> omap (fun x -> Lazy.force x.ri_list)
    |> odfl []
end

(* -------------------------------------------------------------------- *)
module Auto = struct
  let dname : symbol = ""

  let updatedb ~level ?base (ps : path list) (db : (path list Mint.t) Msym.t) =
    let nbase = (odfl dname base) in
    let ps' = Msym.find_def Mint.empty nbase db in
    let ps' =
      let doit x = Some (ofold (fun x ps -> ps @ x) ps x) in
      Mint.change doit level ps' in
    Msym.add nbase ps' db

  let add ~local ~level ?base (ps : path list) (env : env) =
    { env with
        env_atbase = updatedb ?base ~level ps env.env_atbase;
        env_item   = CTh_auto (local, level, base, ps) :: env.env_item; }

  let add1 ~local ~level ?base (p : path) (env : env) =
    add ~local ?base ~level [p] env

  let get_core ?base (env : env) =
    Msym.find_def Mint.empty (odfl dname base) env.env_atbase

  let flatten_db (db : path list Mint.t) =
    Mint.fold_left (fun ps _ ps' -> ps @ ps') [] db

  let get ?base (env : env) =
    flatten_db (get_core ?base env)

  let getall (bases : symbol list) (env : env) =
    let dbs = List.map (fun base -> get_core ~base env) bases in
    let dbs =
      List.fold_left (fun db mi ->
        Mint.union (fun _ sp1 sp2 -> Some (sp1 @ sp2)) db mi)
        Mint.empty dbs
    in flatten_db dbs

  let getx (base : symbol) (env : env) =
    let db = Msym.find_def Mint.empty base env.env_atbase in
    Mint.bindings db
end

(* -------------------------------------------------------------------- *)
module Ty = struct
  type t = EcDecl.tydecl

  let by_path_opt (p : EcPath.path) (env : env) =
    omap
      check_not_suspended
      (MC.by_path (fun mc -> mc.mc_tydecls) (IPPath p) env)

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

  let defined (name : EcPath.path) (env : env) =
    match by_path_opt name env with
    | Some { tyd_type = `Concrete _ } -> true
    | _ -> false

  let unfold (name : EcPath.path) (args : EcTypes.ty list) (env : env) =
    match by_path_opt name env with
    | Some ({ tyd_type = `Concrete body } as tyd) ->
        EcTypes.Tvar.subst
          (EcTypes.Tvar.init (List.map fst tyd.tyd_params) args)
          body
    | _ -> raise (LookupFailure (`Path name))

  let rec hnorm (ty : ty) (env : env) =
    match ty.ty_node with
    | Tconstr (p, tys) when defined p env -> hnorm (unfold p tys env) env
    | _ -> ty

  let rec decompose_fun (ty : ty) (env : env) : dom * ty =
    match (hnorm ty env).ty_node with
    | Tfun (ty1, ty2) ->
        fst_map (fun tys -> ty1 :: tys) (decompose_fun ty2 env)
    | _ -> ([], ty)

  let signature env =
    let rec doit acc ty =
      match (hnorm ty env).ty_node with
      | Tfun (dom, codom) -> doit (dom::acc) codom
      | _ -> (List.rev acc, ty)
    in fun ty -> doit [] ty

  let scheme_of_ty mode (ty : ty) (env : env) =
    let ty = hnorm ty env in
      match ty.ty_node with
      | Tconstr (p, tys) -> begin
          match by_path_opt p env with
          | Some ({ tyd_type = (`Datatype _ | `Record _) as body }) ->
              let prefix   = EcPath.prefix   p in
              let basename = EcPath.basename p in
              let basename =
                match body, mode with
                | `Record   _, (`Ind | `Case) -> basename ^ "_ind"
                | `Datatype _, `Ind           -> basename ^ "_ind"
                | `Datatype _, `Case          -> basename ^ "_case"
              in
                Some (EcPath.pqoname prefix basename, tys)
          | _ -> None
      end
      | _ -> None

  let rebind name ty env =
    let env = MC.bind_tydecl name ty env in

    match ty.tyd_type with
    | `Abstract tc ->
        let myty =
          let myp = EcPath.pqname (root env) name in
          let typ = List.map (fst_map EcIdent.fresh) ty.tyd_params in
            (typ, EcTypes.tconstr myp (List.map (tvar |- fst) typ)) in
        let instr =
          Sp.fold
            (fun p inst -> TypeClass.bind_instance myty (`General p) inst)
            tc env.env_tci
        in
          { env with env_tci = instr }

    | _ -> env

  let bind name ty env =
    { (rebind name ty env) with
         env_item = CTh_type (name, ty) :: env.env_item; }
end

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
             assert false;

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

  let addproj_in_memenv mem l =
    let n = List.length l in
    List.fold_lefti
      (fun mem i vd -> EcMemory.bind_proj i n vd.v_name vd.v_type mem) mem l

  let actmem_pre me path fun_ =
    let mem = EcMemory.empty_local me path in
    let mem = add_in_memenv mem {v_name = "arg"; v_type = fun_.f_sig.fs_arg } in
    match fun_.f_sig.fs_anames with
    | None -> mem
    | Some l -> addproj_in_memenv mem l


  let actmem_post me path fun_ =
    let mem = EcMemory.empty_local me path in
    add_in_memenv mem {v_name = "res"; v_type = fun_.f_sig.fs_ret}

  let actmem_body me path fun_ =
    match fun_.f_def with
    | FBabs _ -> assert false (* FIXME error message *)
    | FBalias _ -> assert false (* FIXME error message *)
    | FBdef fd ->
      let mem = EcMemory.empty_local me path in
      let mem = add_in_memenv mem {v_name="arg"; v_type=fun_.f_sig.fs_arg} in
      let mem =
        match fun_.f_sig.fs_anames with
        | None -> mem
        | Some l -> adds_in_memenv mem l in
      (fun_.f_sig,fd), adds_in_memenv mem fd.f_locals

  let inv_memory side env =
    let path  = mroot env in
    let xpath = EcPath.xpath_fun path "" in (* dummy value *)
    let id    = if side = `Left then EcCoreFol.mleft else EcCoreFol.mright in
    EcMemory.empty_local id xpath

  let inv_memenv env =
    let path  = mroot env in
    let xpath = EcPath.xpath_fun path "" in (* dummy value *)
    let meml  = EcMemory.empty_local EcCoreFol.mleft xpath in
    let memr  = EcMemory.empty_local EcCoreFol.mright xpath in
    Memory.push_all [meml;memr] env

  let inv_memenv1 env =
    let path  = mroot env in
    let xpath = EcPath.xpath_fun path "" in (* dummy value *)
    let mem  = EcMemory.empty_local EcCoreFol.mhr xpath in
    Memory.push_active mem env

  let prF_memenv m path env =
    let fun_ = by_xpath path env in
    actmem_post m path fun_

  let prF path env =
    let post = prF_memenv EcCoreFol.mhr path env in
    Memory.push_active post env

  let hoareF_memenv path env =
    let (ip, _) = oget (ipath_of_xpath path) in
    let fun_ = snd (oget (by_ipath ip env)) in
    let pre  = actmem_pre EcCoreFol.mhr path fun_ in
    let post = actmem_post EcCoreFol.mhr path fun_ in
    pre, post

  let hoareF path env =
    let pre, post = hoareF_memenv path env in
    Memory.push_active pre env, Memory.push_active post env

  let hoareS path env =
    let fun_ = by_xpath path env in
    let fd, memenv = actmem_body EcCoreFol.mhr path fun_ in
    memenv, fd, Memory.push_active memenv env

  let equivF_memenv path1 path2 env =
    let (ip1, _) = oget (ipath_of_xpath path1) in
    let (ip2, _) = oget (ipath_of_xpath path2) in

    let fun1 = snd (oget (by_ipath ip1 env)) in
    let fun2 = snd (oget (by_ipath ip2 env)) in
    let pre1 = actmem_pre EcCoreFol.mleft path1 fun1 in
    let pre2 = actmem_pre EcCoreFol.mright path2 fun2 in
    let post1 = actmem_post EcCoreFol.mleft path1 fun1 in
    let post2 = actmem_post EcCoreFol.mright path2 fun2 in
    (pre1,pre2), (post1,post2)

  let equivF path1 path2 env =
    let (pre1,pre2),(post1,post2) = equivF_memenv path1 path2 env in
    Memory.push_all [pre1; pre2] env,
    Memory.push_all [post1; post2] env

  let equivS path1 path2 env =
    let fun1 = by_xpath path1 env in
    let fun2 = by_xpath path2 env in
    let fd1, mem1 = actmem_body EcCoreFol.mleft path1 fun1 in
    let fd2, mem2 = actmem_body EcCoreFol.mright path2 fun2 in
    mem1, fd1, mem2, fd2, Memory.push_all [mem1; mem2] env
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
        if x = "arg" then {vb_type = f.f_sig.fs_arg; vb_kind = `Var PVloc }
        else
          try
            begin match f.f_sig.fs_anames with
            | None -> raise Not_found
            | Some l ->
              let v = List.find (fun v -> v.v_name = x) l in
              { vb_type = v.v_type; vb_kind = `Var PVloc; }
            end
          with Not_found -> begin
            match f.f_def with
            | FBdef def -> begin
              try
                let v = List.find (fun v -> v.v_name = x) def.f_locals in
                { vb_type = v.v_type; vb_kind = `Var PVloc; }
              with Not_found -> lookup_error (`XPath p)
            end
            | FBabs _ | FBalias _ -> lookup_error (`XPath p)
          end
      end
      | _ -> lookup_error (`XPath p)
    end

    | Some (ip, (i, _args)) -> begin
        match MC.by_path (fun mc -> mc.mc_variables) ip env with
        | None -> lookup_error (`XPath p)
        | Some (params, o) ->
           let local =
             match o.vb_kind with
             | `Var EcTypes.PVglob -> false
             | `Var EcTypes.PVloc | `Proj _ -> true in
           let ((spi, _params), _) =
             MC._downpath_for_var local spsc env ip params in
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
          if EcMemory.memtype memenv = None then None
          else
            let mp = EcMemory.xpath memenv in
            begin match EcMemory.lookup (snd qname) memenv with
            | None    -> None
            | Some (None,ty) ->
              let pv = pv_loc mp (snd qname) in
              Some (`Var pv, ty)
            | Some (Some i, ty) ->
              let pv = pv_arg mp in
              let fdef = Fun.by_xpath mp env in
              Some (`Proj (pv,fdef.f_sig.fs_arg, i), ty)
            end

      | _ -> None
    in
    match obind inmem side with
    | None ->
        (* TODO FIXME, suspended for local program variable *)
      let (((_, _), p), x) = MC.lookup_var qname env in
      let k =
        match x.vb_kind with
        | `Var k -> k
        | _ -> assert false (* PY : FIXME *) in
      (`Var (pv p k), x.vb_type)

    | Some pvt -> pvt

  let lookup_progvar_opt ?side name env =
    try_lf (fun () -> lookup_progvar ?side name env)

  let bind name pvkind ty env =
    let vb = { vb_type = ty; vb_kind = `Var pvkind; } in
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
module AbsStmt = struct
  type t = EcModules.abs_uses

  let byid id env =
    try Mid.find id env.env_abs_st
    with Not_found -> raise (LookupFailure (`AbsStmt id))

  let bind id us env =
    { env with env_abs_st = Mid.add id us env.env_abs_st }
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  type t = module_expr

  let unsuspend_r f istop (i, args) (spi, params) o =
    if i <> spi || List.length args > List.length params then
      assert false;
    if (not istop && List.length args <> List.length params) then
      assert false;

    let params = List.take (List.length args) params in

    let s =
      List.fold_left2
        (fun s (x, _) a -> EcSubst.add_module s x a)
        EcSubst.empty params args
    in
      f s o

  let clearparams n sig_ =
    let used, remaining = List.takedrop n sig_.mis_params in

    let keepcall =
      let used = EcIdent.Sid.of_list (List.map fst used) in
        fun xp ->
          match xp.EcPath.x_top.EcPath.m_top with
          | `Local id -> not (EcIdent.Sid.mem id used)
          | _ -> true
    in

    { mis_params = remaining;
      mis_body   =
        List.map
          (function Tys_function (s, oi) ->
            Tys_function (s, { oi_calls = List.filter keepcall oi.oi_calls;
                               oi_in    = oi.oi_in; }))
          sig_.mis_body }

  let unsuspend istop (i, args) (spi, params) me =
    let me =
      match args with
      | [] -> me
      | _  -> { me with me_sig = clearparams (List.length args) me.me_sig }
    in
      unsuspend_r EcSubst.subst_module istop (i, args) (spi, params) me

  let by_ipath_r (spsc : bool) (p : ipath) (env : env) =
    let obj = MC.by_path (fun mc -> mc.mc_modules) p env in
      obj |> omap
               (fun (args, obj) ->
                 (fst (MC._downpath_for_mod spsc env p args), obj))

  let by_mpath (p : mpath) (env : env) =
    let (ip, (i, args)) = ipath_of_mpath p in

      match MC.by_path (fun mc -> mc.mc_modules) ip env with
      | None ->
          lookup_error (`MPath p)

      | Some (params, o) ->
          let ((spi, params), op) = MC._downpath_for_mod false env ip params in
          let (params, istop) =
            match op.EcPath.m_top with
            | `Concrete (p, Some _) ->
                assert ((params = []) || ((spi+1) = EcPath.p_size p));
                (params, false)

            | `Concrete (p, None) ->
                assert ((params = []) || ((spi+1) = EcPath.p_size p));
                ((if args = [] then [] else o.me_sig.mis_params), true)

            | `Local _m ->
                assert ((params = []) || spi = 0);
                ((if args = [] then [] else o.me_sig.mis_params), true)
          in
            unsuspend istop (i, args) (spi, params) o

  let by_mpath_opt (p : EcPath.mpath) (env : env) =
    try_lf (fun () -> by_mpath p env)

  let add (p : EcPath.mpath) (env : env) =
    let obj = by_mpath p env in
      MC.import_mod (fst (ipath_of_mpath p)) obj env

  let lookup qname (env : env) =
    let (((_, _a), p), x) = MC.lookup_mod qname env in
    (* FIXME : this test is dubious for functors lookup *)
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
    { (MC.bind_mod name me env) with
          env_item = CTh_module me :: env.env_item;
          env_norm = ref !(env.env_norm); }

  let me_of_mt env name modty restr =
    let modsig =
      let modsig =
        match
          omap
            check_not_suspended
            (MC.by_path
               (fun mc -> mc.mc_modsigs)
               (IPPath modty.mt_name) env)
        with
        | None -> lookup_error (`Path modty.mt_name)
        | Some x -> x
      in
      EcSubst.subst_modsig
        ~params:(List.map fst modty.mt_params) EcSubst.empty modsig
    in
    module_expr_of_module_sig name modty modsig restr

  let bind_local name modty restr env =
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
          env_comps = Mip.add path comps env.env_comps;
          env_norm  = ref !(env.env_norm);
      }
    in
      env

  let declare_local id modty restr env =
    { (bind_local id modty restr env) with
        env_modlcs = Sid.add id env.env_modlcs; }

  let add_restr_to_locals restr env =

    let union_restr (rx1,r1) (rx2,r2) =
      Sx.union rx1 rx2, Sm.union r1 r2 in

    let update_id id mods =
      let update me =
        match me.me_body with
        | ME_Decl (mt, r) ->
          { me with me_body = ME_Decl (mt, union_restr restr r) }
        | _ -> me
      in
      MMsym.map_at
        (List.map
           (fun (ip, me) ->
             if   ip = IPIdent (id, None)
             then (ip, update me)
             else (ip, me)))
        (EcIdent.name id) mods
    in
    let envc =  { env.env_current
              with mc_modules =
        Sid.fold update_id env.env_modlcs
          env.env_current.mc_modules; } in
    let en = !(env.env_norm) in
    let norm = { en with get_restr = Mm.empty } in
    { env with env_current = envc;
      env_norm = ref norm;
    }

  let bind_locals bindings env =
    List.fold_left
      (fun env (name, me) -> bind_local name me (Sx.empty,Sm.empty) env)
      env bindings

  let enter name params env =
    let env = enter (`Module params) name env in
      bind_locals params env

  let add_mod_binding bd env =
    let do1 env (x,gty) =
      match gty with
      | GTmodty (p, r) -> bind_local x p r env
      | _ -> env
    in
      List.fold_left do1 env bd
end

(* -------------------------------------------------------------------- *)
module NormMp = struct
  let rec norm_mpath_for_typing env p =
    let (ip, (i, args)) = ipath_of_mpath p in
    match Mod.by_ipath_r true ip env with
    | Some ((spi, params), ({ me_body = ME_Alias (arity,alias) } as m)) ->
      assert (m.me_sig.mis_params = [] && arity = 0);
      let p =
        Mod.unsuspend_r EcSubst.subst_mpath
          true (i, args) (spi, params) alias
      in
        norm_mpath_for_typing env p

    | _ -> begin
      match p.EcPath.m_top with
      | `Local _
      | `Concrete (_, None) -> p

      | `Concrete (p1, Some p2) -> begin
        let name = EcPath.basename p2 in
        let pr   = EcPath.mpath_crt p1 p.EcPath.m_args (EcPath.prefix p2) in
        let pr   = norm_mpath_for_typing env pr in
        match pr.EcPath.m_top with
        | `Local _ -> p
        | `Concrete (p1, p2) ->
          EcPath.mpath_crt p1 pr.EcPath.m_args (Some (EcPath.pqoname p2 name))
      end
    end

  let rec norm_mpath_def env p =
    let top = EcPath.m_functor p in
    let args = p.EcPath.m_args in
    let sub =
      match p.EcPath.m_top with | `Local _ -> None | `Concrete(_,o) -> o in
    (* p is (top args).sub *)
    match Mod.by_mpath_opt top env with
    | None -> norm_mpath_for_typing env p
    | Some me ->
      begin match me.me_body with
      | ME_Alias (arity,mp) ->
        let nargs = List.length args in
        if arity <= nargs then
          let args, extra = List.takedrop arity args in
          let params = List.take arity me.me_sig.mis_params in
          let s =
            List.fold_left2
              (fun s (x, _) a -> EcSubst.add_module s x a)
              EcSubst.empty params args in
          let mp = EcSubst.subst_mpath s mp in
          let args' = mp.EcPath.m_args in
          let args2 = if extra = [] then args' else args' @ extra in
          let mp =
            match mp.EcPath.m_top with
            | `Local _ as x -> assert (sub = None); EcPath.mpath x args2
            | `Concrete(top',None) -> (* ((top' args') args).sub *)
              EcPath.mpath_crt top' args2 sub
            | `Concrete(top',(Some p' as sub')) -> (* ((top' args').sub').sub *)
              assert (args = []); (* A submodule cannot be a functor *)
              match sub with
              | None   -> EcPath.mpath_crt top' args2 sub'
              | Some p -> EcPath.mpath_crt top' args2 (Some (pappend p' p)) in
          norm_mpath env mp
        else
          EcPath.mpath p.EcPath.m_top (List.map (norm_mpath env) args)

      | ME_Structure _ when sub <> None ->
        begin
          let (ip, (i, args)) = ipath_of_mpath p in
          match Mod.by_ipath_r true ip env with
          | Some ((spi, params), ({ me_body = ME_Alias (_,alias) } as m)) ->
            assert (m.me_sig.mis_params = []);
            let p =
              Mod.unsuspend_r EcSubst.subst_mpath
                false (i, args) (spi, params) alias
            in
            norm_mpath env p
          | _ ->
            EcPath.mpath p.EcPath.m_top (List.map (norm_mpath env) args)
        end

      | _ ->
      (* The top is in normal form simply normalize the arguments *)
        EcPath.mpath p.EcPath.m_top (List.map (norm_mpath env) args)
      end

  and norm_mpath env p =
    try Mm.find p !(env.env_norm).norm_mp with Not_found ->
      let res = norm_mpath_def env p in
      let en = !(env.env_norm) in
      env.env_norm := { en with norm_mp = Mm.add p res en.norm_mp };
      res

  let rec norm_xfun env p =
    try Mx.find p !(env.env_norm).norm_xfun with Not_found ->
      let res =
        match p.x_sub.p_node with
        | Pqname(pf,x) ->
          let pf = norm_xfun env (EcPath.xpath p.x_top pf) in
          EcPath.xpath pf.x_top (EcPath.pqname pf.x_sub x)
        | _ ->
          let mp = norm_mpath env p.x_top in
          let pf = EcPath.xpath mp p.x_sub in
          match Fun.by_xpath_opt pf env with (* TODO B:use by_xpath_r *)
          | Some {f_def = FBalias xp} -> norm_xfun env xp
          | _ -> pf in
      let en = !(env.env_norm) in
      env.env_norm := { en with norm_xfun = Mx.add p res en.norm_xfun };
      res

  let norm_xpv env p =
    try Mx.find p !(env.env_norm).norm_xpv with Not_found ->
      let mp = p.x_top in
      assert (mp.m_args = []);
      let top = m_functor p.x_top in
      match Mod.by_mpath_opt top env with
      | None -> (* We are in typing mod .... *)
        let mp = norm_mpath env mp in
        let xp = EcPath.xpath mp p.x_sub in
        let res = xp_glob xp in
        res
      | Some me ->
        let params = me.me_sig.mis_params in
        let env', mp =
          if params = [] then env, mp
          else
            Mod.bind_locals params env,
            EcPath.m_apply mp (List.map (fun (id,_)->EcPath.mident id) params)in
        let mp = norm_mpath env' mp in
        let xp = EcPath.xpath mp p.x_sub in
        let res = (pv_glob xp).pv_name in
        let en = !(env.env_norm) in
        env.env_norm := { en with norm_xpv = Mx.add p res en.norm_xpv };
        res

  let use_empty = { us_pv = Mx.empty; us_gl = Sid.empty }
  let use_equal us1 us2 =
    Mx.equal (fun _ _ -> true) us1.us_pv us2.us_pv &&
      Sid.equal us1.us_gl us2.us_gl

  let use_union us1 us2 =
    { us_pv = Mx.union  (fun _ ty _ -> Some ty) us1.us_pv us2.us_pv;
      us_gl = Sid.union us1.us_gl us2.us_gl }
  let use_mem_xp xp us = Mx.mem xp us.us_pv
  let use_mem_gl mp us =
    assert (mp.m_args = []);
    match mp.m_top with
    | `Local id -> Sid.mem id us.us_gl
    | _ -> assert false

  let add_var env xp us =
    let xp = xp_glob xp in
    let xp = norm_xpv env xp in
    let vb = Var.by_xpath xp env in
    let pv = EcTypes.pv_glob xp in
    { us with us_pv = Mx.add pv.pv_name vb.vb_type us.us_pv }

  let add_glob id us =
    { us with us_gl = Sid.add id us.us_gl }

  let add_glob_except rm id us =
    if Sid.mem id rm then us else add_glob id us

  let gen_fun_use env fdone rm =
    let rec fun_use us f =
      let f = norm_xfun env f in
      if Mx.mem f !fdone then us
      else
        let f1 = Fun.by_xpath f env in
        fdone := Sx.add f !fdone;
        match f1.f_def with
        | FBdef fdef ->
          let f_uses = fdef.f_uses in
          let vars = Sx.union f_uses.us_reads f_uses.us_writes in
          let us = Sx.fold (add_var env) vars us in
          List.fold_left fun_use us f_uses.us_calls
        | FBabs oi ->
          let id =
            match f.x_top.m_top with
            | `Local id -> id
            | _ -> assert false in
          let us = add_glob_except rm id us in
          List.fold_left fun_use us oi.oi_calls
        | FBalias _ -> assert false in
    fun_use

  let fun_use env xp =
    gen_fun_use env (ref Sx.empty) Sid.empty use_empty xp

  let mod_use env mp =
    let mp = norm_mpath env mp in
    let me = Mod.by_mpath mp env in
    let params = me.me_sig.mis_params in
    let rm =
      List.fold_left (fun rm (id,_) -> Sid.add id rm) Sid.empty params in
    let env' = Mod.bind_locals params env in

    let mp' =
      EcPath.m_apply mp (List.map (fun (id,_) -> EcPath.mident id) params) in

    let fdone = ref Sx.empty in

    let rec mod_use us mp =
      let mp = norm_mpath env' mp in
      let me = Mod.by_mpath mp env' in
      assert (me.me_sig.mis_params = []);
      body_use mp us me.me_comps me.me_body

    and body_use mp us comps body =
      match body with
      | ME_Alias _ -> assert false
      | ME_Decl _ ->
        let id = match mp.m_top with `Local id -> id | _ -> assert false in
        let us = add_glob_except rm id us in
        List.fold_left (item_use mp) us comps
      | ME_Structure ms ->
        List.fold_left (item_use mp) us ms.ms_body

    and item_use mp us item =
      match item with
      | MI_Module me -> mod_use us (EcPath.mqname mp me.me_name)
      | MI_Variable v -> add_var env' (xpath_fun mp v.v_name) us
      | MI_Function f -> fun_use us (xpath_fun mp f.f_name)

    and fun_use us f = gen_fun_use env' fdone rm us f in

    mod_use use_empty mp'

  let mod_use env mp =
    try Mm.find mp !(env.env_norm).mod_use with Not_found ->
      let res = mod_use env mp in
      let en = !(env.env_norm) in
      env.env_norm := { en with mod_use = Mm.add mp res en.mod_use };
      res

  let norm_restr env (rx,r) =
    let restr = Sx.fold (fun xp r -> add_var env xp r) rx use_empty in
    Sm.fold (fun mp r -> use_union r (mod_use env mp)) r restr

  let get_restr env mp =
    try Mm.find mp !(env.env_norm).get_restr with Not_found ->
      let res =
        match (Mod.by_mpath mp env).me_body with
        | EcModules.ME_Decl(_,restr) -> norm_restr env restr
        | _ -> assert false in
      let en = !(env.env_norm) in
      env.env_norm := { en with get_restr = Mm.add mp res en.get_restr };
      res

  let equal_restr env r1 r2 = use_equal (norm_restr env r1) (norm_restr env r2)

  let norm_pvar env pv =
    let p =
      if pv.pv_kind = PVglob then norm_xpv env pv.pv_name
      else norm_xfun env pv.pv_name in
    if   x_equal p pv.pv_name then pv
    else EcTypes.pv p pv.pv_kind

  let globals env m mp =
    let us = mod_use env mp in
    let l =
      Sid.fold (fun id l -> f_glob (EcPath.mident id) m :: l) us.us_gl [] in
    let l =
      Mx.fold
        (fun xp ty l -> f_pvar (EcTypes.pv_glob xp) ty m :: l) us.us_pv l in
    f_tuple l

  let norm_glob env m mp = globals env m mp

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

  let rec norm_form env =
    let norm_ty1 : ty -> ty = norm_ty env in

    let norm_gty env (id,gty) =
      let gty =
        match gty with
        | GTty ty -> GTty (norm_ty env ty)
        | GTmodty _ -> gty
        | GTmem None -> gty
        | GTmem (Some mt) ->
          let me =
            EcMemory.empty_local id (norm_xfun env (EcMemory.lmt_xpath mt)) in
          let me = Msym.fold (fun id (p,ty) me ->
            EcMemory.bindp id p (norm_ty env ty) me)
              (EcMemory.lmt_bindings mt) me  in
          GTmem (snd me) in
      id,gty in

    let has_mod b =
      List.exists (fun (_,gty) ->
        match gty with GTmodty _ -> true | _ -> false) b in

    let norm_form =                     (* FIXME: use FSmart *)
      EcCoreFol.Hf.memo_rec 107 (fun aux f ->
        match f.f_node with
        | Fquant(q,bd,f) ->
          if has_mod bd then
            let env = Mod.add_mod_binding bd env in
            let bd = List.map (norm_gty env) bd in
            f_quant q bd (norm_form env f)
          else
          let bd = List.map (norm_gty env) bd in
          f_quant q bd (aux f)

        | Fpvar(p,m) ->
          let p' = norm_pvar env p in
          if p == p' then f else
            f_pvar p' f.f_ty m

        | Fglob(p,m) -> norm_glob env m p

        | FhoareF hf ->
          let pre' = aux hf.hf_pr and p' = norm_xfun env hf.hf_f
          and post' = aux hf.hf_po in
          if hf.hf_pr == pre' && hf.hf_f == p' && hf.hf_po == post' then f else
          f_hoareF pre' p' post'

        | FequivF ef ->
          let pre' = aux ef.ef_pr and l' = norm_xfun env ef.ef_fl
          and r' = norm_xfun env ef.ef_fr and post' = aux ef.ef_po in
          if ef.ef_pr == pre' && ef.ef_fl == l' &&
            ef.ef_fr == r' && ef.ef_po == post' then f else
          f_equivF pre' l' r' post'

        | Fpr pr ->
          let pr' = {
            pr_mem   = pr.pr_mem;
            pr_fun   = norm_xfun env pr.pr_fun;
            pr_args  = aux pr.pr_args;
            pr_event = aux pr.pr_event;
          } in FSmart.f_pr (f, pr) pr'

        | _ -> EcCoreFol.f_map norm_ty1 aux f) in
    norm_form

  let norm_op env op =
    let kind =
      match op.op_kind with
      | OB_pred (Some (PR_Plain f)) ->
         OB_pred (Some (PR_Plain (norm_form env f)))

      | OB_pred (Some (PR_Ind pri)) ->
         let pri = { pri with pri_ctors =
           List.map (fun x ->
             { x with prc_spec = List.map (norm_form env) x.prc_spec })
             pri.pri_ctors }
         in OB_pred (Some (PR_Ind pri))

      | _ -> op.op_kind
    in
    { op with
        op_kind = kind;
        op_ty   = norm_ty env op.op_ty; }

  let norm_ax env ax =
    { ax with ax_spec = norm_form env ax.ax_spec }

  let is_abstract_fun f env =
    let f = norm_xfun env f in
    match (Fun.by_xpath f env).f_def with
    | FBabs _ -> true
    | _ -> false

  let x_equal env f1 f2 =
    EcPath.x_equal (norm_xfun env f1) (norm_xfun env f2)

  let pv_equal env pv1 pv2 =
    EcTypes.pv_equal (norm_pvar env pv1) (norm_pvar env pv2)
end

let rec ty_hnorm (ty : ty) (env : env) =
    match ty.ty_node with
    | Tconstr (p, tys) when Ty.defined p env -> ty_hnorm (Ty.unfold p tys env) env
    | Tglob p -> NormMp.norm_tglob env p
    | _ -> ty

(* -------------------------------------------------------------------- *)
module ModTy = struct
  type t = module_sig

  let by_path_opt (p : EcPath.path) (env : env) =
    omap
      check_not_suspended
      (MC.by_path (fun mc -> mc.mc_modsigs) (IPPath p) env)

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

  let sig_of_mt env (mt:module_type) =
    let sig_ = by_path mt.mt_name env in
    let subst =
      List.fold_left2 (fun s (x1,_) a ->
        EcSubst.add_module s x1 a) EcSubst.empty sig_.mis_params mt.mt_args in
    let items =
      EcSubst.subst_modsig_body subst sig_.mis_body in
    let params = mt.mt_params in
    let keep =
      List.fold_left (fun k (x,_) ->
        EcPath.Sm.add (EcPath.mident x) k) EcPath.Sm.empty params in
    let keep_info f =
      EcPath.Sm.mem (f.EcPath.x_top) keep in
    let do1 = function
      | Tys_function(s,oi) ->
        Tys_function(s,{oi_calls = List.filter keep_info oi.oi_calls;
                        oi_in = oi.oi_in}) in
    { mis_params = params;
      mis_body   = List.map do1 items }
end


(* -------------------------------------------------------------------- *)
module Op = struct
  type t = EcDecl.operator

  let by_path_opt (p : EcPath.path) (env : env) =
    omap
      check_not_suspended
      (MC.by_path (fun mc -> mc.mc_operators) (IPPath p) env)

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
    let op  = NormMp.norm_op env op in
    let nt  =
      match op.op_kind with
      | OB_nott nt ->
         Some (EcPath.pqname (root env) name, (op.op_tparams, nt))
      | _ -> None
    in

    { env with
        env_ntbase = ofold List.cons env.env_ntbase nt;
        env_item   = CTh_operator(name, op) :: env.env_item; }

  let rebind name op env =
    MC.bind_operator name op env

  let all ?check (qname : qsymbol) (env : env) =
    let ops = MC.lookup_operators qname env in
    match check with
    | None -> ops
    | Some check -> List.filter (check |- snd) ops

  let reducible env p =
    try
      let op = by_path p env in
        match op.op_kind with
        | OB_oper (Some (OP_Plain _))
        | OB_pred (Some _) -> true
        | OB_oper None
        | OB_oper (Some (OP_Constr _))
        | OB_oper (Some (OP_Record _))
        | OB_oper (Some (OP_Proj _))
        | OB_oper (Some (OP_Fix _))
        | OB_oper (Some (OP_TC))
        | OB_pred None
        | OB_nott _ -> false

    with LookupFailure _ -> false

  let reduce env p tys =
    let op = oget (by_path_opt p env) in
    let f  =
      match op.op_kind with
      | OB_oper (Some (OP_Plain (e, _))) ->
          form_of_expr EcCoreFol.mhr e
      | OB_pred (Some (PR_Plain f)) ->
          f
      | _ -> raise NotReducible
    in
      EcCoreFol.Fsubst.subst_tvar
        (EcTypes.Tvar.init (List.map fst op.op_tparams) tys) f

  let is_projection env p =
    try  EcDecl.is_proj (by_path p env)
    with LookupFailure _ -> false

  let is_record_ctor env p =
    try  EcDecl.is_rcrd (by_path p env)
    with LookupFailure _ -> false

  let is_dtype_ctor env p =
    try  EcDecl.is_ctor (by_path p env)
    with LookupFailure _ -> false

  let is_fix_def env p =
    try  EcDecl.is_fix (by_path p env)
    with LookupFailure _ -> false

  let is_abbrev env p =
    try  EcDecl.is_abbrev (by_path p env)
    with LookupFailure _ -> false

  let is_prind env p =
    try  EcDecl.is_prind (by_path p env)
    with LookupFailure _ -> false

  let scheme_of_prind env (_mode : [`Case | `Ind]) p =
    match by_path_opt p env with
    | Some { op_kind = OB_pred (Some (PR_Ind pri)) } ->
       Some (EcInductive.prind_indsc_path p, List.length pri.pri_ctors)
    | _ -> None

  type notation = env_notation

  let get_notations env =
    env.env_ntbase
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  type t = axiom

  let by_path_opt (p : EcPath.path) (env : env) =
    omap
      check_not_suspended
      (MC.by_path (fun mc -> mc.mc_axioms) (IPPath p) env)

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
    let ax = NormMp.norm_ax env ax in
    let env = MC.bind_axiom name ax env in
    { env with env_item = CTh_axiom (name, ax) :: env.env_item }

  let rebind name ax env =
    MC.bind_axiom name ax env

  let instanciate p tys env =
    match by_path_opt p env with
    | Some ({ ax_spec = f } as ax) ->
        Fsubst.subst_tvar
          (EcTypes.Tvar.init (List.map fst ax.ax_tparams) tys) f
    | _ -> raise (LookupFailure (`Path p))

  let iter ?name f (env : env) =
    match name with
    | Some name ->
      let axs = MC.lookup_axioms name env in
      List.iter (fun (p,ax) -> f p ax) axs

    | None ->
        Mip.iter
          (fun _ mc -> MMsym.iter
            (fun _ (ip, ax) ->
              match ip with IPPath p -> f p ax | _ -> ())
            mc.mc_axioms)
          env.env_comps

  let all ?(check = fun _ _ -> true) ?name (env : env) =
    match name with
    | Some name ->
        let axs = MC.lookup_axioms name env in
        List.filter (fun (p, ax) -> check p ax) axs

    | None ->
        Mip.fold (fun _ mc aout ->
          MMsym.fold (fun _ axioms aout ->
            List.fold_right (fun (ip, ax) aout ->
              match ip with
              | IPPath p -> if check p ax then (p, ax) :: aout else aout
              | _ -> aout)
              axioms aout)
            mc.mc_axioms aout)
          env.env_comps []
end

(* -------------------------------------------------------------------- *)
module Algebra = struct
  let bind_ring ty cr env =
    assert (Mid.is_empty ty.ty_fv);
    { env with env_tci =
        TypeClass.bind_instance ([], ty) (`Ring cr) env.env_tci }

  let bind_field ty cr env =
    assert (Mid.is_empty ty.ty_fv);
    { env with env_tci =
        TypeClass.bind_instance ([], ty) (`Field cr) env.env_tci }

  let add_ring  ty cr env = TypeClass.add_instance ([], ty) (`Ring  cr) env
  let add_field ty cr env = TypeClass.add_instance ([], ty) (`Field cr) env
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  type t    = ctheory
  type mode = [`All | thmode]

  (* -------------------------------------------------------------------- *)
  let rec ctheory_of_theory =
      fun th ->
        let items = List.map ctheory_item_of_theory_item th in
          { cth_desc = CTh_struct items; cth_struct = items; }

  and ctheory_item_of_theory_item = function
    | Th_type      (x, ty)  -> CTh_type      (x, ty)
    | Th_operator  (x, op)  -> CTh_operator  (x, op)
    | Th_axiom     (x, ax)  -> CTh_axiom     (x, ax)
    | Th_modtype   (x, mt)  -> CTh_modtype   (x, mt)
    | Th_module    m        -> CTh_module    m
    | Th_export    name     -> CTh_export    name
    | Th_typeclass name     -> CTh_typeclass name
    | Th_instance  (ty, cr) -> CTh_instance  (ty, cr)
    | Th_baserw    x        -> CTh_baserw x
    | Th_addrw     (b, l)   -> CTh_addrw     (b, l)
    | Th_reduction rule     -> CTh_reduction rule
    | Th_auto      ps       -> CTh_auto      ps

    | Th_theory (x, (th, md)) ->
        CTh_theory (x, (ctheory_of_theory th, md))

  (* ------------------------------------------------------------------ *)
  let enter name env =
    enter `Theory name env

  (* ------------------------------------------------------------------ *)
  let by_path_opt ?(mode = `All)(p : EcPath.path) (env : env) =
    let obj =
      match MC.by_path (fun mc -> mc.mc_theories) (IPPath p) env, mode with
      | (Some (_, (_, `Concrete))) as obj, (`All | `Concrete) -> obj
      | (Some (_, (_, `Abstract))) as obj, (`All | `Abstract) -> obj
      | _, _ -> None

    in omap check_not_suspended obj

  let by_path ?mode (p : EcPath.path) (env : env) =
    match by_path_opt ?mode p env with
    | None -> lookup_error (`Path p)
    | Some obj -> obj

  let add (p : EcPath.path) (env : env) =
    let obj = by_path p env in
      MC.import_theory p obj env

  let lookup ?(mode = `Concrete) qname (env : env) =
    match MC.lookup_theory qname env, mode with
    | (_, (_, `Concrete)) as obj, (`All | `Concrete) -> obj
    | (_, (_, `Abstract)) as obj, (`All | `Abstract) -> obj
    | _ -> lookup_error (`QSymbol qname)

  let lookup_opt ?mode name env =
    try_lf (fun () -> lookup ?mode name env)

  let lookup_path ?mode name env =
    fst (lookup ?mode name env)

  (* ------------------------------------------------------------------ *)
  let rec bind_instance_cth path inst cth =
    List.fold_left (bind_instance_cth_item path) inst cth.cth_struct

  and bind_instance_cth_item path inst item =
    let xpath x = EcPath.pqname path x in

    match item with
    | CTh_instance (ty, k) ->
        TypeClass.bind_instance ty k inst

    | CTh_theory (x, (cth, `Concrete)) ->
        bind_instance_cth (xpath x) inst cth

    | CTh_type (x, tyd) -> begin
        match tyd.tyd_type with
        | `Abstract tc ->
            let myty =
              let typ = List.map (fst_map EcIdent.fresh) tyd.tyd_params in
                (typ, EcTypes.tconstr (xpath x) (List.map (tvar |- fst) typ))
            in
              Sp.fold
                (fun p inst -> TypeClass.bind_instance myty (`General p) inst)
                tc inst

        | _ -> inst
    end

    | _ -> inst

  (* ------------------------------------------------------------------ *)
  let rec bind_base_cth tx path base cth =
    List.fold_left (bind_base_cth_item tx path) base cth.cth_struct

  and bind_base_cth_item tx path base item =
    let xpath x = EcPath.pqname path x in

    match item with
    | CTh_theory (x, (cth, `Concrete)) ->
        bind_base_cth tx (xpath x) base cth
    | CTh_theory _ ->
        base
    | _ -> odfl base (tx path base item)

  (* ------------------------------------------------------------------ *)
  let bind_tc_cth =
    let for1 path base = function
      | CTh_typeclass (x, tc) ->
          tc.tc_prt |> omap (fun prt ->
            let src = EcPath.pqname path x in
            TC.Graph.add ~src ~dst:prt base)
      | _ -> None

    in bind_base_cth for1

  (* ------------------------------------------------------------------ *)
  let bind_br_cth =
    let for1 path base = function
      | CTh_baserw x ->
         let ip = IPPath (EcPath.pqname path x) in
         assert (not (Mip.mem ip base));
         Some (Mip.add ip Sp.empty base)

      | CTh_addrw (b, r) ->
         let change = function
           | None   -> assert false
           | Some s -> Some (List.fold_left (fun s r -> Sp.add r s) s r)

         in Some (Mip.change change (IPPath b) base)

      | _ -> None

    in bind_base_cth for1

  (* ------------------------------------------------------------------ *)
  let bind_at_cth =
    let for1 _path db = function
      | CTh_auto (false, level, base, ps) ->
         Some (Auto.updatedb ?base ~level ps db)
      | _ -> None

    in bind_base_cth for1

  (* ------------------------------------------------------------------ *)
  let bind_nt_cth =
    let for1 path base = function
      | CTh_operator (x, ({ op_kind = OB_nott nt } as op)) ->
         Some ((EcPath.pqname path x, (op.op_tparams, nt)) :: base)
      | _ -> None

    in bind_base_cth for1

  (* ------------------------------------------------------------------ *)
  let bind_rd_cth =
    let for1 _path db = function
      | CTh_reduction rules ->
         let rules = List.map (fun (x, _, y) -> (x, y)) rules in
         Some (Reduction.add_rules rules db)
      | _ -> None

    in bind_base_cth for1

  (* ------------------------------------------------------------------ *)
  let bind ?(mode = `Concrete) name cth env =
    let th = (cth, mode) in

    let env = MC.bind_theory name th env in
    let env = { env with env_item = (CTh_theory (name, th)) :: env.env_item } in

    match mode with
    | `Concrete ->
        let thname      = EcPath.pqname (root env) name in
        let env_tci     = bind_instance_cth thname env.env_tci cth in
        let env_tc      = bind_tc_cth thname env.env_tc cth in
        let env_rwbase  = bind_br_cth thname env.env_rwbase cth in
        let env_atbase  = bind_at_cth thname env.env_atbase cth in
        let env_ntbase  = bind_nt_cth thname env.env_ntbase cth in
        let env_redbase = bind_rd_cth thname env.env_redbase cth in
        { env with env_tci; env_tc; env_rwbase; env_atbase; env_ntbase; env_redbase; }

    | `Abstract ->
        env

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
            import env p (fst (by_path ~mode:`Concrete p env))

        | CTh_theory (x, ((_, `Concrete) as th)) ->
            let env = MC.import_theory (xpath x) th env in
            let env = MC.import_mc (IPPath (xpath x)) env in
              env

        | CTh_theory (x, ((_, `Abstract) as th)) ->
            MC.import_theory (xpath x) th env

        | CTh_typeclass (x, tc) ->
            MC.import_typeclass (xpath x) tc env

        | CTh_baserw x ->
            MC.import_rwbase (xpath x) env

        | CTh_addrw _ | CTh_instance _ | CTh_auto _ | CTh_reduction _ ->
            env

      in
        List.fold_left import_cth_item env cth.cth_struct

    in
      import env path (fst (by_path ~mode:`Concrete path env))

  (* ------------------------------------------------------------------ *)
  let export (path : EcPath.path) (env : env) =
    let env = import path env in
    { env with env_item = CTh_export path :: env.env_item }

  (* ------------------------------------------------------------------ *)
  let rec filter clears root cleared items =
    snd_map (List.pmap identity)
      (List.map_fold (filter1 clears root) cleared items)

  and filter_th clears root cleared items =
    let mempty = List.exists (EcPath.p_equal root) clears in
    let cleared, items = filter clears root cleared items in

    if   mempty && List.is_empty items
    then (Sp.add root cleared, None)
    else (cleared, Some items)

  and filter1 clears root =
    let inclear p = List.exists (EcPath.p_equal p) clears in
    let thclear = inclear root in

    fun cleared item ->
      match item with
      | CTh_theory (x, (cth, mode)) ->
         let cleared, items =
           let xpath = EcPath.pqname root x in
           filter_th clears xpath cleared cth.cth_struct in
         let item = items |> omap (fun items ->
           let cth = { cth with cth_struct = items } in
           CTh_theory (x, (cth, mode))) in
         (cleared, item)

      | _ -> let item = match item with

      | CTh_axiom (_, { ax_kind = `Lemma }) when thclear ->
          None

      | CTh_axiom (x, ({ ax_kind = `Axiom (tags, false) } as ax)) when thclear ->
          Some (CTh_axiom (x, { ax with ax_kind = `Axiom (tags, true) }))

      | CTh_addrw (p, ps) ->
          let ps = List.filter ((not) |- inclear |- oget |- EcPath.prefix) ps in
          if List.is_empty ps then None else Some (CTh_addrw (p, ps))

      | CTh_auto (lc, lvl, base, ps) ->
          let ps = List.filter ((not) |- inclear |- oget |- EcPath.prefix) ps in
          if List.is_empty ps then None else Some (CTh_auto (lc, lvl, base, ps))

      | (CTh_export p) as item ->
          if Sp.mem p cleared then None else Some item

      | _ as item -> Some item

      in (cleared, item)

  (* ------------------------------------------------------------------ *)
  let close ?(clears = []) ?(pempty = `No) env =
    let items = List.rev env.env_item in
    let items =
      if   List.is_empty clears
      then (if List.is_empty items then None else Some items)
      else snd (filter_th clears (root env) Sp.empty items) in

    let items =
      match items, pempty with
      | None, (`No | `ClearOnly) -> Some []
      | _, _ -> items
    in

    items |> omap (fun items ->
      { cth_desc = CTh_struct items; cth_struct = items; })

  (* ------------------------------------------------------------------ *)
  let require ?(mode = `Concrete) x cth env =
    let rootnm  = EcCoreLib.p_top in
    let thpath  = EcPath.pqname rootnm x in

    let env =
      match mode with
      | `Concrete ->
          let (_, thmc), submcs =
            MC.mc_of_ctheory_r rootnm (x, cth)
          in MC.bind_submc env rootnm ((x, thmc), submcs)

      | `Abstract -> env
    in

    let th = (cth, mode) in

    let topmc = Mip.find (IPPath rootnm) env.env_comps in
    let topmc = MC._up_theory false topmc x (IPPath thpath, th) in
    let topmc = MC._up_mc false topmc (IPPath thpath) in

    let current = env.env_current in
    let current = MC._up_theory true current x (IPPath thpath, th) in
    let current = MC._up_mc true current (IPPath thpath) in

    let comps = env.env_comps in
    let comps = Mip.add (IPPath rootnm) topmc comps in

    let env = { env with env_current = current; env_comps = comps; } in

    match mode with
    | `Abstract -> env

    | `Concrete ->
      { env with
          env_tci     = bind_instance_cth thpath env.env_tci cth;
          env_tc      = bind_tc_cth thpath env.env_tc cth;
          env_rwbase  = bind_br_cth thpath env.env_rwbase cth;
          env_atbase  = bind_at_cth thpath env.env_atbase cth;
          env_ntbase  = bind_nt_cth thpath env.env_ntbase cth;
          env_redbase = bind_rd_cth thpath env.env_redbase cth; }
end

(* -------------------------------------------------------------------- *)
let initial gstate = empty gstate

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
module LDecl = struct
  type error =
  | InvalidKind of EcIdent.t * [`Variable | `Hypothesis]
  | CannotClear of EcIdent.t * EcIdent.t
  | NameClash   of [`Ident of EcIdent.t | `Symbol of symbol]
  | LookupError of [`Ident of EcIdent.t | `Symbol of symbol]

  exception LdeclError of error

  let pp_error fmt (exn : error) =
    match exn with
    | LookupError (`Symbol s) ->
        Format.fprintf fmt "unknown symbol %s" s

    | NameClash (`Symbol s) ->
        Format.fprintf fmt
          "an hypothesis or variable named `%s` already exists" s

    | InvalidKind (x, `Variable) ->
        Format.fprintf fmt "`%s` is not a variable" (EcIdent.name x)

    | InvalidKind (x, `Hypothesis) ->
        Format.fprintf fmt "`%s` is not an hypothesis" (EcIdent.name x)

    | CannotClear (id1,id2) ->
        Format.fprintf fmt "cannot clear %s as it is used in %s"
        (EcIdent.name id1) (EcIdent.name id2)

    | LookupError (`Ident id) ->
        Format.fprintf fmt "unknown identifier `%s`, please report"
        (EcIdent.tostring id)

    | NameClash (`Ident id) ->
        Format.fprintf fmt "name clash for `%s`, please report"
        (EcIdent.tostring id)

  let _ = EcPException.register (fun fmt exn ->
    match exn with
    | LdeclError e -> pp_error fmt e
    | _ -> raise exn)

  let error e = raise (LdeclError e)

  (* ------------------------------------------------------------------ *)
  let ld_subst s ld =
    match ld with
    | LD_var (ty, body) ->
        LD_var (s.fs_ty ty, body |> omap (Fsubst.f_subst s))

    | LD_mem mt ->
        let mt = EcMemory.mt_substm s.fs_sty.ts_p s.fs_mp s.fs_ty mt
        in LD_mem mt

    | LD_modty (p, r) ->
        let (p, r) = gty_as_mod (Fsubst.gty_subst s (GTmodty (p, r)))
        in LD_modty (p, r)

    | LD_hyp f ->
        LD_hyp (Fsubst.f_subst s f)

    | LD_abs_st _ ->                    (* FIXME *)
        assert false

  (* ------------------------------------------------------------------ *)
  let ld_fv = function
  | LD_var (ty, None) ->
      ty.ty_fv
  | LD_var (ty,Some f) ->
      EcIdent.fv_union ty.ty_fv f.f_fv
  | LD_mem mt ->
      EcMemory.mt_fv mt
  | LD_hyp f ->
      f.f_fv
  | LD_modty (p, r) ->
      gty_fv (GTmodty(p,r))
  | LD_abs_st us ->
      let add fv (x,_) =  EcPath.x_fv fv x.pv_name in
      let fv = Mid.empty in
      let fv = List.fold_left add fv us.aus_reads in
      let fv = List.fold_left add fv us.aus_writes in
      List.fold_left EcPath.x_fv fv us.aus_calls

  (* ------------------------------------------------------------------ *)
  let by_name s hyps =
    match List.ofind ((=) s |- EcIdent.name |- fst) hyps.h_local with
    | None   -> error (LookupError (`Symbol s))
    | Some h -> h

  let by_id id hyps =
    match List.ofind (EcIdent.id_equal id |- fst) hyps.h_local with
    | None   -> error (LookupError (`Ident id))
    | Some x -> snd x

  (* ------------------------------------------------------------------ *)
  let as_hyp = function
    | (id, LD_hyp f) -> (id, f)
    | (id, _) -> error (InvalidKind (id, `Hypothesis))

  let as_var = function
    | (id, LD_var (ty, _)) -> (id, ty)
    | (id, _) -> error (InvalidKind (id, `Variable))

  (* ------------------------------------------------------------------ *)
  let hyp_by_name s hyps = as_hyp (by_name s hyps)
  let var_by_name s hyps = as_var (by_name s hyps)

  (* ------------------------------------------------------------------ *)
  let hyp_by_id x hyps = as_hyp (x, by_id x hyps)
  let var_by_id x hyps = as_var (x, by_id x hyps)

  (* ------------------------------------------------------------------ *)
  let has_gen dcast s hyps =
    try  ignore (dcast (by_name s hyps)); true
    with LdeclError (InvalidKind _ | LookupError _) -> false

  let hyp_exists s hyps = has_gen as_hyp s hyps
  let var_exists s hyps = has_gen as_var s hyps

  (* ------------------------------------------------------------------ *)
  let has_id x hyps =
    try  ignore (by_id x hyps); true
    with LdeclError (LookupError _) -> false

  let has_inld s = function
    | LD_mem (Some lmt) -> Msym.mem s (lmt_bindings lmt)
    | _ -> false

  let has_name ?(dep = false) s hyps =
    let test (id, k) =
      EcIdent.name id = s || (dep && has_inld s k)
    in List.exists test hyps.h_local

  (* ------------------------------------------------------------------ *)
  let can_unfold id hyps =
    try  match by_id id hyps with LD_var (_, Some _) -> true | _ -> false
    with LdeclError _ -> false

  let unfold id hyps =
    try
      match by_id id hyps with
      | LD_var (_, Some f) -> f
      | _ -> raise NotReducible
    with LdeclError _ -> raise NotReducible

  (* ------------------------------------------------------------------ *)
  let check_name_clash id hyps =
    if   has_id id hyps
    then error (NameClash (`Ident id))
    else
      let s = EcIdent.name id in
      if s <> "_" && has_name ~dep:false s hyps then
        error (NameClash (`Symbol s))

  let add_local id ld hyps =
    check_name_clash id hyps;
    { hyps with h_local = (id, ld) :: hyps.h_local }

  (* ------------------------------------------------------------------ *)
  let fresh_id hyps s =
    let s =
      if   s = "_" || not (has_name ~dep:true s hyps)
      then s
      else
        let rec aux n =
          let s = Printf.sprintf "%s%d" s n in
          if has_name ~dep:true s hyps then aux (n+1) else s
        in aux 0

    in EcIdent.create s

  let fresh_ids hyps names =
    let do1 hyps s =
      let id = fresh_id hyps s in
      (add_local id (LD_var (tbool, None)) hyps, id)
    in List.map_fold do1  hyps names

  (* ------------------------------------------------------------------ *)
  type hyps = {
    le_init : env;
    le_env  : env;
    le_hyps : EcBaseLogic.hyps;
  }

  let tohyps  lenv = lenv.le_hyps
  let toenv   lenv = lenv.le_env
  let baseenv lenv = lenv.le_init

  let add_local_env x k env =
    match k with
    | LD_var (ty, _)  -> Var.bind_local x ty env
    | LD_mem mt       -> Memory.push (x, mt) env
    | LD_modty (i, r) -> Mod.bind_local x i r env
    | LD_hyp   _      -> env
    | LD_abs_st us    -> AbsStmt.bind x us env

  (* ------------------------------------------------------------------ *)
  let add_local x k h =
    let le_hyps = add_local x k (tohyps h) in
    let le_env  = add_local_env x k h.le_env in
    { h with le_hyps; le_env; }

  (* ------------------------------------------------------------------ *)
  let init env ?(locals = []) tparams =
    let buildenv env =
      List.fold_right
        (fun (x, k) env -> add_local_env x k env)
        locals env
    in

    { le_init = env;
      le_env  = buildenv env;
      le_hyps = { h_tvar = tparams; h_local = locals; }; }

  (* ------------------------------------------------------------------ *)
  let clear ?(leniant = false) ids hyps =
    let rec filter ids hyps =
      match hyps with [] -> [] | ((id, lk) as bd) :: hyps ->

      let ids, bd =
        if EcIdent.Sid.mem id ids then (ids, None) else

        let fv = ld_fv lk in

        if Mid.set_disjoint ids fv then
          (ids, Some bd)
        else
          if leniant then
            (Mid.set_diff ids fv, Some bd)
          else
            let inter = Mid.set_inter ids fv in
            error (CannotClear (Sid.choose inter, id))
      in List.ocons bd (filter ids hyps)
    in

    let locals = filter ids hyps.le_hyps.h_local in

    init hyps.le_init ~locals hyps.le_hyps.h_tvar

  (* ------------------------------------------------------------------ *)
  let hyp_convert x check hyps =
    let module E = struct exception NoOp end in

    let init locals = init hyps.le_init ~locals hyps.le_hyps.h_tvar in

    let rec doit locals =
      match locals with
      | (y, LD_hyp fp) :: locals when EcIdent.id_equal x y -> begin
          let fp' = check (lazy (init locals)) fp in
          if fp == fp' then raise E.NoOp else (x, LD_hyp fp') :: locals
      end

      | [] -> error (LookupError (`Ident x))
      | ld :: locals -> ld :: (doit locals)

    in (try Some (doit hyps.le_hyps.h_local) with E.NoOp -> None) |> omap init

  (* ------------------------------------------------------------------ *)
  let local_hyps x hyps =
    let rec doit locals =
      match locals with
      | (y, _) :: locals ->
          if EcIdent.id_equal x y then locals else doit locals
      | [] ->
          error (LookupError (`Ident x)) in

    let locals = doit hyps.le_hyps.h_local in
    init hyps.le_init ~locals hyps.le_hyps.h_tvar

  (* ------------------------------------------------------------------ *)
  let by_name s hyps = by_name s (tohyps hyps)
  let by_id   x hyps = by_id   x (tohyps hyps)

  let has_name s hyps = has_name ~dep:false s (tohyps hyps)
  let has_id   x hyps = has_id x (tohyps hyps)

  let hyp_by_name s hyps = hyp_by_name s (tohyps hyps)
  let hyp_exists  s hyps = hyp_exists  s (tohyps hyps)
  let hyp_by_id   x hyps = snd (hyp_by_id x (tohyps hyps))

  let var_by_name s hyps = var_by_name s (tohyps hyps)
  let var_exists  s hyps = var_exists  s (tohyps hyps)
  let var_by_id   x hyps = snd (var_by_id x (tohyps hyps))

  let can_unfold x hyps = can_unfold x (tohyps hyps)
  let unfold     x hyps = unfold x (tohyps hyps)

  let fresh_id  hyps s = fresh_id  (tohyps hyps) s
  let fresh_ids hyps s = snd (fresh_ids (tohyps hyps) s)

  (* ------------------------------------------------------------------ *)
  let push_active m lenv =
    { lenv with le_env = Memory.push_active m lenv.le_env }

  let push_all l lenv =
    { lenv with le_env = Memory.push_all l lenv.le_env }

  let hoareF xp lenv =
     let env1, env2 = Fun.hoareF xp lenv.le_env in
    { lenv with le_env = env1}, {lenv with le_env = env2 }

  let equivF xp1 xp2 lenv =
    let env1, env2 = Fun.equivF xp1 xp2 lenv.le_env in
    { lenv with le_env = env1}, {lenv with le_env = env2 }

  let inv_memenv lenv =
    { lenv with le_env = Fun.inv_memenv lenv.le_env }

  let inv_memenv1 lenv =
    { lenv with le_env = Fun.inv_memenv1 lenv.le_env }
end
