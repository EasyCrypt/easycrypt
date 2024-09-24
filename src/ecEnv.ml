(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcAst
open EcTypes
open EcCoreFol
open EcCoreSubst
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

type glob_var_bind = EcTypes.ty

type mc = {
  mc_parameters : ((EcIdent.t * module_type) list) option;
  mc_variables  : (ipath * glob_var_bind) MMsym.t;
  mc_functions  : (ipath * function_) MMsym.t;
  mc_modules    : (ipath * (module_expr * locality option)) MMsym.t;
  mc_modsigs    : (ipath * top_module_sig) MMsym.t;
  mc_tydecls    : (ipath * EcDecl.tydecl) MMsym.t;
  mc_operators  : (ipath * EcDecl.operator) MMsym.t;
  mc_axioms     : (ipath * EcDecl.axiom) MMsym.t;
  mc_theories   : (ipath * ctheory) MMsym.t;
  mc_typeclasses: (ipath * typeclass) MMsym.t;
  mc_rwbase     : (ipath * path) MMsym.t;
  mc_components : ipath MMsym.t;
}

type use = {
  us_pv : ty Mx.t;
  us_gl : Sid.t;
}

let use_union us1 us2 =
  { us_pv = Mx.union  (fun _ ty _ -> Some ty) us1.us_pv us2.us_pv;
    us_gl = Sid.union us1.us_gl us2.us_gl; }

let use_empty = { us_pv = Mx.empty; us_gl = Sid.empty; }

type env_norm = {
  norm_mp       : EcPath.mpath Mm.t;
  norm_xpv      : EcPath.xpath Mx.t;   (* for global program variable *)
  norm_xfun     : EcPath.xpath Mx.t;   (* for fun and local program variable *)
  mod_use       : use Mm.t;
  get_restr_use : (use EcModules.use_restr) Mm.t;
}

(* -------------------------------------------------------------------- *)
type red_topsym = [
  | `Path of path
  | `Tuple
  | `Proj of int
]

module Mrd = EcMaps.Map.Make(struct
  type t = red_topsym

  let to_comparable (p : t) =
    match p with
    | `Path p -> `Path p.p_tag
    | `Tuple  -> `Tuple
    | `Proj i -> `Proj i

  let compare (p1 : t) (p2 : t) =
    Stdlib.compare (to_comparable p1) (to_comparable p2)
end)

(* -------------------------------------------------------------------- *)
module Mmem : sig
  type 'a t
  val empty : 'a t
  val all   : 'a t -> (EcIdent.t * 'a) list
  val byid  : EcIdent.t -> 'a t -> 'a
  val bysym : EcSymbols.symbol -> 'a t -> EcIdent.t * 'a
  val add   : EcIdent.t -> 'a -> 'a t -> 'a t
end = struct

  type 'a t = {
      m_s : memory Msym.t;
      m_id : 'a Mid.t;
    }

  let empty = {
      m_s = Msym.empty;
      m_id = Mid.empty;
    }

  let all m = Mid.bindings m.m_id

  let byid id m = Mid.find id m.m_id

  let bysym s m =
    let id = Msym.find s m.m_s in
    id, byid id m

  let add id a m = {
      m_s = Msym.add (EcIdent.name id) id m.m_s;
      m_id = Mid.add id a m.m_id
    }
end

(* -------------------------------------------------------------------- *)
type preenv = {
  env_top      : EcPath.path option;
  env_gstate   : EcGState.gstate;
  env_scope    : escope;
  env_current  : mc;
  env_comps    : mc Mip.t;
  env_locals   : (EcIdent.t * EcTypes.ty) MMsym.t;
  env_memories : EcMemory.memtype Mmem.t;
  env_actmem   : EcMemory.memory option;
  env_abs_st   : EcModules.abs_uses Mid.t;
  env_tci      : ((ty_params * ty) * tcinstance) list;
  env_tc       : TC.graph;
  env_rwbase   : Sp.t Mip.t;
  env_atbase   : (path list Mint.t) Msym.t;
  env_redbase  : mredinfo;
  env_ntbase   : ntbase Mop.t;
  env_modlcs   : Sid.t;                 (* declared modules *)
  env_item     : theory_item list;      (* in reverse order *)
  env_norm     : env_norm ref;
  (* Map theory paths to their env before just before theory was closed. *)
  (* The environment should be incuded for all theories, including       *)
  (* abstract ones. The purpose of this map is to simplify the code      *)
  (* related to pretty-printing.                                         *)
  env_thenvs   : preenv Mp.t;
}

and escope = {
  ec_path  : EcPath.path;
  ec_scope : scope;
}

and scope = [
  | `Theory
  | `Module of EcPath.mpath
  | `Fun    of EcPath.xpath
]

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

and ntbase = (path * env_notation) list

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

let scope (env : env) =
  env.env_scope.ec_scope

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
    get_restr_use = Mm.empty; }

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
    env_memories = Mmem.empty;
    env_actmem   = None;
    env_abs_st   = Mid.empty;
    env_tci      = [];
    env_tc       = TC.Graph.empty;
    env_rwbase   = Mip.empty;
    env_atbase   = Msym.empty;
    env_redbase  = Mrd.empty;
    env_ntbase   = Mop.empty;
    env_modlcs   = Sid.empty;
    env_item     = [];
    env_norm     = ref empty_norm_cache;
    env_thenvs   = Mp.empty; }

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
  let _downpath_for_modcp isvar ~spsc env p args =
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
                        EcPath.xpath
                          (EcPath.mpath_crt p (if isvar then [] else List.map EcPath.mident n)
                             (EcPath.prefix q))
                          (EcPath.basename q)
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
                      x
                  in
                    (ap, false)

              | _ -> assert false
          end
        in
          ((i+1, if (inscope && not spsc) || isvar then [] else a), ap)

    with Not_found ->
      assert false

  let _downpath_for_var = _downpath_for_modcp true
  let _downpath_for_fun = _downpath_for_modcp false

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
    | Some (p, (args, ty)) ->
      (_downpath_for_var ~spsc:false env p args, ty)

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
    | Some (p, (args, obj)) -> (_downpath_for_fun ~spsc:false env p args, obj)

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
        { ax_kind       = `Lemma;
          ax_tparams    = tv;
          ax_spec       = cl;
          ax_loca       = (snd obj).op_loca;
          ax_visibility = `Visible; } in
      (name, (axp, ax))) ax in

    List.fold_left (fun mc -> curry (_up_axiom candup mc)) mc ax

  let import_operator p op env =
    import (_up_operator true) (IPPath p) op env

  (* -------------------------------------------------------------------- *)
  let lookup_tydecl qnx env =
    match lookup (fun mc -> mc.mc_tydecls) qnx env with
    | None -> lookup_error (`QSymbol qnx)
    | Some (p, (args, obj)) -> (_downpath_for_tydecl env p args, obj)

  let lookup_tydecls qnx env =
    List.map
      (fun (p, (args, obj)) -> (_downpath_for_tydecl env p args, obj))
      (lookup_all (fun mc -> mc.mc_tydecls) qnx env)

  let _up_tydecl candup mc x obj =
    if not candup && MMsym.last x mc.mc_tydecls <> None then
      raise (DuplicatedBinding x);
    let mc = { mc with mc_tydecls = MMsym.add x obj mc.mc_tydecls } in
    let mc =
      let mypath, tyd =
        match obj with IPPath p, x -> (p, x) | _, _ -> assert false in
      let ipath name = IPPath (EcPath.pqoname (EcPath.prefix mypath) name) in

      let loca    = tyd.tyd_loca in

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
            let cop = mk_op
                        ~opaque:optransparent (fst aty) (snd aty)
                        (Some (OP_Constr (mypath, i))) loca in
            let cop = (ipath c, cop) in
              (c, cop)
          in

          let (schelim, schcase) =
            let do1 scheme name =
              let scname = Printf.sprintf "%s_%s" x name in
                (scname, { ax_tparams    = tyd.tyd_params;
                           ax_spec       = scheme;
                           ax_kind       = `Lemma;
                           ax_loca       = loca;
                           ax_visibility = `NoSmt;
                })
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

          let projs = (mypath, tyd.tyd_params, dtype) in
          let projs = EcInductive.datatype_projectors projs in

          List.fold_left (fun mc (c, op) ->
              let name = EcInductive.datatype_proj_name c in
              _up_operator candup mc name (ipath name, op)
            ) mc projs

      | `Record (scheme, fields) ->
          let params  = List.map (fun (x, _) -> tvar x) tyd.tyd_params in
          let nfields = List.length fields in
          let cfields =
            let for1 i (f, aty) =
              let aty = EcTypes.tfun (tconstr mypath params) aty in
              let aty = EcSubst.freshen_type (tyd.tyd_params, aty) in
              let fop = mk_op ~opaque:optransparent (fst aty) (snd aty)
                          (Some (OP_Proj (mypath, i, nfields))) loca in
              let fop = (ipath f, fop) in
                (f, fop)
            in
              List.mapi for1 fields
          in

          let scheme =
            let scname = Printf.sprintf "%s_ind" x in
              (scname, { ax_tparams    = tyd.tyd_params;
                         ax_spec       = scheme;
                         ax_kind       = `Lemma;
                         ax_loca       = loca;
                         ax_visibility = `NoSmt;
              })
          in

          let stname = Printf.sprintf "mk_%s" x in
          let stop   =
            let stty = toarrow (List.map snd fields) (tconstr mypath params) in
            let stty = EcSubst.freshen_type (tyd.tyd_params, stty) in
              mk_op ~opaque:optransparent (fst stty) (snd stty) (Some (OP_Record mypath)) loca
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
      let loca = match tc.tc_loca with `Local -> `Local | `Global -> `Global in

      let self = EcIdent.create "'self" in

      let tsubst =EcSubst.add_tydef EcSubst.empty mypath ([], tvar self) in

      let operators =
        let on1 (opid, optype) =
          let opname = EcIdent.name opid in
          let optype = EcSubst.subst_ty tsubst optype in
          let opdecl =
            mk_op ~opaque:optransparent [(self, Sp.singleton mypath)]
              optype (Some OP_TC) loca
          in (opid, xpath opname, optype, opdecl)
        in
          List.map on1 tc.tc_ops
      in

      let fsubst =
        List.fold_left
          (fun s (x, xp, xty, _) ->
            let fop = EcCoreFol.f_op xp [tvar self] xty in
              EcSubst.add_flocal s x fop)
          tsubst
          operators
      in

      let axioms =
        List.map
          (fun (x, ax) ->
            let ax = EcSubst.subst_form fsubst ax in
              (x, { ax_tparams    = [(self, Sp.singleton mypath)];
                    ax_spec       = ax;
                    ax_kind       = `Lemma;
                    ax_loca       = loca;
                    ax_visibility = `NoSmt; }))
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
  let rec mc_of_module_r (p1, args, p2, lc) me =
    let subp2 x =
      let p = EcPath.pqoname p2 x in
        (p, pcat p1 p)
    in

    let mc1_of_module (mc : mc) = function
      | MI_Module subme ->
          assert (subme.me_params = []);

          let (subp2, mep) = subp2 subme.me_name in
          let submcs = mc_of_module_r (p1, args, Some subp2, None) subme in
          let mc = _up_mc false mc (IPPath mep) in
          let mc = _up_mod false mc subme.me_name (IPPath mep, (subme, lc)) in
          (mc, Some submcs)

      | MI_Variable v ->
          let (_subp2, mep) = subp2 v.v_name in
          let vty  = v.v_type in
            (_up_var false mc v.v_name (IPPath mep, vty), None)

      | MI_Function f ->
          let (_subp2, mep) = subp2 f.f_name in
            (_up_fun false mc f.f_name (IPPath mep, f), None)
    in

    let (mc, submcs) =
      List.map_fold mc1_of_module
        (empty_mc
           (if p2 = None then Some me.me_params else None))
        me.me_comps
    in
      ((me.me_name, mc), List.rev_pmap (fun x -> x) submcs)

  let mc_of_module (env : env) { tme_expr = me; tme_loca = lc; } =
    match env.env_scope.ec_scope with
    | `Theory ->
        let p1   = EcPath.pqname (root env) me.me_name
        and args = me.me_params in
        mc_of_module_r (p1, args, None, Some lc) me

    | `Module mpath -> begin
       assert (lc = `Global);
       match mpath.EcPath.m_top with
       | `Concrete (p1, p2) ->
           let p2 = EcPath.pqoname p2 me.me_name in
           mc_of_module_r (p1, mpath.EcPath.m_args, Some p2, None) me

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
          _up_var false mc v.v_name (xpath v.v_name, v.v_type)


      | MI_Function f ->
          _up_fun false mc f.f_name (xpath f.f_name, f)
    in
      List.fold_left
        mc1_of_module
        (empty_mc (Some me.me_params))
        me.me_comps

  (* ------------------------------------------------------------------ *)
  let rec mc_of_theory_r (scope : EcPath.path) (x, cth) =
    let subscope = EcPath.pqname scope x in
    let expath = fun x -> EcPath.pqname subscope x in
    let add2mc up name obj mc =
      up false mc name (IPPath (expath name), obj)
    in

    let mc1_of_theory (mc : mc) (item : theory_item) =
      match item.ti_item with
      | Th_type (xtydecl, tydecl) ->
          (add2mc _up_tydecl xtydecl tydecl mc, None)

      | Th_operator (xop, op) ->
          (add2mc _up_operator xop op mc, None)

      | Th_axiom (xax, ax) ->
          (add2mc _up_axiom xax ax mc, None)

      | Th_modtype (xmodty, modty) ->
          (add2mc _up_modty xmodty modty mc, None)

      | Th_module { tme_expr = subme; tme_loca = lc; } ->
          let args = subme.me_params in
          let submcs =
            mc_of_module_r (expath subme.me_name, args, None, Some lc) subme
          in
            (add2mc _up_mod subme.me_name (subme, Some lc) mc, Some submcs)

      | Th_theory (xsubth, cth) ->
        if cth.cth_mode = `Concrete then
          let submcs = mc_of_theory_r subscope (xsubth, cth) in
          let mc = _up_mc false mc (IPPath (expath xsubth)) in
            (add2mc _up_theory xsubth cth mc, Some submcs)
        else
          (add2mc _up_theory xsubth cth mc, None)

      | Th_typeclass (x, tc) ->
          (add2mc _up_typeclass x tc mc, None)

      | Th_baserw (x, _) ->
          (add2mc _up_rwbase x (expath x) mc, None)

      | Th_export _ | Th_addrw _ | Th_instance _
      | Th_auto   _ | Th_reduction _ ->
          (mc, None)
    in

    let (mc, submcs) =
      List.map_fold mc1_of_theory (empty_mc None) cth.cth_items
    in
      ((x, mc), List.rev_pmap identity submcs)

  let mc_of_theory (env : env) (x : symbol) (cth : ctheory) =
    match cth.cth_mode with
    | `Concrete -> Some (mc_of_theory_r (root env) (x, cth))
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

  and bind_theory x (th:ctheory) env =
    match mc_of_theory env x th with
    | None -> bind _up_theory x th env
    | Some ((_, mc), submcs) ->
        let env = bind _up_theory x th env in
        let env = bind_mc x mc env in
        bind_submcs env (EcPath.pqname (root env) x) submcs

  and bind_mod x mod_ env =
    let (_, mc), submcs = mc_of_module env mod_ in
    let env = bind _up_mod x (mod_.tme_expr, Some mod_.tme_loca) env in
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
      let xpath = EcPath.xpath mpath name in
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
  let all env = Mmem.all env.env_memories

  let byid (me : memory) (env : env) =
    try Some (me, Mmem.byid me env.env_memories)
    with Not_found -> None

  let lookup (me : symbol) (env : env) =
    try Some (Mmem.bysym me env.env_memories)
    with Not_found -> None

  let set_active (me : memory) (env : env) =
    match byid me env with
    | None   -> raise (MEError (UnknownMemory (`Memory me)))
    | Some _ -> { env with env_actmem = Some me }

  let get_active (env : env) =
    env.env_actmem

  let current (env : env) =
    match env.env_actmem with
    | None    -> None
    | Some me -> byid me env

  let update (me: EcMemory.memenv) (env : env) =
    { env with env_memories = Mmem.add (fst me) (snd me) env.env_memories; }

  let push (me : EcMemory.memenv) (env : env) =
    (* TODO : A: *)
    (* FIXME: assert (byid (EcMemory.memory me) env = None); *)
    update me env

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
  let x = p.EcPath.x_sub in

  let xt p =
    match p with
    | IPPath p -> Some (IPPath (EcPath.pqname p x))
    | IPIdent (m, None) -> Some (IPIdent (m, Some (EcPath.psymbol x)))
    | _ -> None
  in

  let (p, (i, a)) = ipath_of_mpath p.EcPath.x_top in
  (xt p) |> omap (fun p -> (p, (i+1, a)))

(* -------------------------------------------------------------------- *)
let try_lf f =
  try  Some (f ())
  with LookupFailure _ -> None

(* -------------------------------------------------------------------- *)
let gen_iter fmc flk ?name f env =
  match name with
  | Some name ->
    List.iter (fun (p, ax) -> f p ax) (flk name env)

  | None ->
    Mip.iter
      (fun _ mc -> MMsym.iter
        (fun _ (ip, obj) ->
          match ip with IPPath p -> f p obj | _ -> ())
        (fmc mc))
      env.env_comps

(* -------------------------------------------------------------------- *)
let gen_all fmc flk ?(check = fun _ _ -> true) ?name (env : env) =
  match name with
  | Some name ->
      List.filter (fun (p, ax) -> check p ax) (flk name env)

  | None ->
      Mip.fold (fun _ mc aout ->
        MMsym.fold (fun _ objs aout ->
          List.fold_right (fun (ip, obj) aout ->
            match ip with
            | IPPath p -> if check p obj then (p, obj) :: aout else aout
            | _ -> aout)
            objs aout)
          (fmc mc) aout)
        env.env_comps []

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

  let bind ?(import = import0) name tc env =
    let env = if import.im_immediate then rebind name tc env else env in
    { env with
        env_item = mkitem import (Th_typeclass (name, tc)) :: env.env_item }

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

  let add_instance ?(import = import0) ty cr lc env =
    let env =
      if import.im_immediate then
        { env with env_tci = bind_instance ty cr env.env_tci }
      else env in
    { env with
        env_tci  = bind_instance ty cr env.env_tci;
        env_item = mkitem import (Th_instance (ty, cr, lc)) :: env.env_item; }

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

  let add ?(import = import0) name lc env =
    let p   = EcPath.pqname (root env) name in
    let env = if import.im_immediate then MC.bind_rwbase name p env else env in
    let ip  = IPPath p in
    { env with
        env_rwbase = Mip.add ip Sp.empty env.env_rwbase;
        env_item   = mkitem import (Th_baserw (name, lc)) :: env.env_item; }

  let addto ?(import = import0) p l lc env =
    let env =
      if import.im_immediate then
        { env with
            env_rwbase =
              Mip.change
                (omap (fun s -> List.fold_left (fun s r -> Sp.add r s) s l))
                (IPPath p) env.env_rwbase }
      else env in

    { env with
        env_rwbase =
          Mip.change
            (omap (fun s -> List.fold_left (fun s r -> Sp.add r s) s l))
            (IPPath p) env.env_rwbase;
        env_item = mkitem import (Th_addrw (p, l, lc)) :: env.env_item; }
end

(* -------------------------------------------------------------------- *)
module Reduction = struct
  type rule   = EcTheory.rule
  type topsym = red_topsym

  let add_rule ((_, rule) : path * rule option) (db : mredinfo) =
    match rule with None -> db | Some rule ->

    let p : topsym =
      match rule.rl_ptn with
      | Rule (`Op p, _)   -> `Path (fst p)
      | Rule (`Tuple, _)  -> `Tuple
      | Rule (`Proj i, _) -> `Proj i
      | Var _ | Int _     -> assert false in

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

  let add ?(import = import0) (rules : (path * rule_option * rule option) list) (env : env) =
    let rstrip = List.map (fun (x, _, y) -> (x, y)) rules in
    let env =
      if import.im_immediate then
        { env with env_redbase = add_rules rstrip env.env_redbase; }
      else env in

    { env with
        env_item = mkitem import (Th_reduction rules) :: env.env_item; }

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

  let add ?(import = import0) ~level ?base (ps : path list) lc (env : env) =
    let env =
      if import.im_immediate then
        { env with
            env_atbase = updatedb ?base ~level ps env.env_atbase; }
      else env
    in
      { env with env_item = mkitem import
         (Th_auto (level, base, ps, lc)) :: env.env_item; }

  let add1 ?import ~level ?base (p : path) lc (env : env) =
    add ?import ?base ~level [p] lc env

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
           let ((spi, params), _op) = MC._downpath_for_fun ~spsc env ip params in
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

  let adds_in_memenv memenv vd = EcMemory.bindall vd memenv
  let add_in_memenv memenv vd = adds_in_memenv memenv [vd]

  let add_params mem fun_ =
    adds_in_memenv mem fun_.f_sig.fs_anames

  let actmem_pre me fun_ =
    let mem = EcMemory.empty_local ~witharg:true me in
    add_params mem fun_

  let actmem_post me fun_ =
    let mem = EcMemory.empty_local ~witharg:false me in
    add_in_memenv mem { ov_name = Some res_symbol; ov_type = fun_.f_sig.fs_ret}

  let actmem_body me fun_ =
    match fun_.f_def with
    | FBabs _   -> assert false (* FIXME error message *)
    | FBalias _ -> assert false (* FIXME error message *)
    | FBdef fd   ->
      let mem = EcMemory.empty_local ~witharg:false me in
      let mem = add_params mem fun_ in
      let locals = List.map ovar_of_var fd.f_locals in
      (fun_.f_sig,fd), adds_in_memenv mem locals

  let inv_memory side =
    let id    = if side = `Left then EcCoreFol.mleft else EcCoreFol.mright in
    EcMemory.abstract id

  let inv_memenv env =
    Memory.push_all [inv_memory `Left; inv_memory `Rigth] env

  let inv_memenv1 env =
    let mem  = EcMemory.abstract EcCoreFol.mhr in
    Memory.push_active mem env

  let prF_memenv m path env =
    let fun_ = by_xpath path env in
    actmem_post m fun_

  let prF path env =
    let post = prF_memenv EcCoreFol.mhr path env in
    Memory.push_active post env

  let hoareF_memenv path env =
    let (ip, _) = oget (ipath_of_xpath path) in
    let fun_ = snd (oget (by_ipath ip env)) in
    let pre  = actmem_pre EcCoreFol.mhr fun_ in
    let post = actmem_post EcCoreFol.mhr fun_ in
    pre, post

  let hoareF path env =
    let pre, post = hoareF_memenv path env in
    Memory.push_active pre env, Memory.push_active post env

  let hoareS path env =
    let fun_ = by_xpath path env in
    let fd, memenv = actmem_body EcCoreFol.mhr fun_ in
    memenv, fd, Memory.push_active memenv env

  let equivF_memenv path1 path2 env =
    let (ip1, _) = oget (ipath_of_xpath path1) in
    let (ip2, _) = oget (ipath_of_xpath path2) in

    let fun1 = snd (oget (by_ipath ip1 env)) in
    let fun2 = snd (oget (by_ipath ip2 env)) in
    let pre1 = actmem_pre EcCoreFol.mleft fun1 in
    let pre2 = actmem_pre EcCoreFol.mright fun2 in
    let post1 = actmem_post EcCoreFol.mleft fun1 in
    let post2 = actmem_post EcCoreFol.mright fun2 in
    (pre1,pre2), (post1,post2)

  let equivF path1 path2 env =
    let (pre1,pre2),(post1,post2) = equivF_memenv path1 path2 env in
    Memory.push_all [pre1; pre2] env,
    Memory.push_all [post1; post2] env

  let equivS path1 path2 env =
    let fun1 = by_xpath path1 env in
    let fun2 = by_xpath path2 env in
    let fd1, mem1 = actmem_body EcCoreFol.mleft fun1 in
    let fd2, mem2 = actmem_body EcCoreFol.mright fun2 in
    mem1, fd1, mem2, fd2, Memory.push_all [mem1; mem2] env
end

(* -------------------------------------------------------------------- *)
module Var = struct
  type t = glob_var_bind

    let by_xpath_r (spsc : bool) (p : xpath) (env : env) =
    match ipath_of_xpath p with
    | None -> lookup_error (`XPath p)
    | Some (ip, (i, _args)) ->
      match MC.by_path (fun mc -> mc.mc_variables) ip env with
      | None -> lookup_error (`XPath p)
      | Some (params, ty) ->
        let ((spi, _params), _) =
          MC._downpath_for_var ~spsc env ip params in
        if i <> spi then
          assert false;
        ty

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
          begin match EcMemory.lookup_me (snd qname) memenv with
          | Some (v, Some pa, _) -> Some (`Proj(pv_arg, pa), v.v_type)
          | Some (v, None, _)    -> Some (`Var (pv_loc v.v_name), v.v_type)
          | None                 -> None
          end
      | _ -> None
    in
    match obind inmem side with
    | None ->
      let (((_, _), p), ty) = MC.lookup_var qname env in
      (`Var (pv_glob p), ty)

    | Some pvt -> pvt

  let lookup_progvar_opt ?side name env =
    try_lf (fun () -> lookup_progvar ?side name env)

  let bind_pvglob name ty env =
    MC.bind_var name ty env

  let bindall_pvglob bindings env =
    List.fold_left
      (fun env (name, ty) -> bind_pvglob name ty env)
      env bindings

  exception DuplicatedLocalBinding of EcIdent.t

   let bind_local ?uniq:(uniq=false) name ty env =
     let s = EcIdent.name name in
     if uniq && MMsym.all s env.env_locals <> [] then
       raise (DuplicatedLocalBinding name);
     { env with
       env_locals = MMsym.add s (name, ty) env.env_locals }

   let bind_locals ?uniq:(uniq=false) bindings env =
     List.fold_left
       (fun env (name, ty) -> bind_local ~uniq:uniq name ty env)
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
  type t   = top_module_expr
  type lkt = module_expr * locality option
  type spt = mpath * module_expr suspension * locality option

  let unsuspend_r f istop (i, args) (spi, params) o =
    if List.length args > List.length params then
      assert false;
    if i <> spi then
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

  let clearparams n params =
    let _, remaining = List.takedrop n params in
    remaining


  let unsuspend istop (i, args) (spi, params) me =
    let me =
      match args with
      | [] -> me
      | _  ->
        let me_params = clearparams (List.length args) me.me_params in

        let me_oinfos =
          let keep = List.map (EcPath.mident |- fst) me_params in
          let keep = Sm.of_list keep in
          Msym.map (OI.filter (fun f -> Sm.mem (f.x_top) keep)) me.me_oinfos in

        { me with me_params; me_oinfos; }
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

      | Some (params, (o, lc)) ->
          let ((spi, params), op) = MC._downpath_for_mod true env ip params in
          let (params, istop) =
            match op.EcPath.m_top with
            | `Concrete (p, Some _) ->
                assert ((params = []) || ((spi+1) = EcPath.p_size p));
                (params, false)

            | `Concrete (p, None) ->
                assert ((params = []) || ((spi+1) = EcPath.p_size p));
                ((if args = [] then [] else o.me_params), true)

            | `Local _m ->
                assert ((params = []) || spi = 0);
                ((if args = [] then [] else o.me_params), true)
          in
            (unsuspend istop (i, args) (spi, params) o, lc)

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
    let (((i, a), p), (x, lc)) = MC.lookup_mod qname env in
    let obj = { sp_target = x; sp_params = (i, a); } in
    (p, obj, lc)

  let sp_lookup_opt name env =
    try_lf (fun () -> sp_lookup name env)

  let lookup_path name env =
    fst (lookup name env)

  let add_xs_to_declared xs env =
    let update_id id mods =
      let update me =
        match me.me_body with
        | ME_Decl (mty, mr) ->
          let mr =
            mr_add_restr mr (ur_empty (xs, Sm.empty)) in
          { me with me_body = ME_Decl (mty, mr) }
        | _ -> me
      in
      MMsym.map_at
        (List.map
           (fun (ip, (me, lc)) ->
             if   ip = IPIdent (id, None)
             then (ip, (update me, lc))
             else (ip, (me, lc))))
        (EcIdent.name id) mods
    in
    let envc =  { env.env_current
              with mc_modules =
        Sid.fold update_id env.env_modlcs
          env.env_current.mc_modules; } in
    let en = !(env.env_norm) in
    let norm = { en with get_restr_use = Mm.empty } in
    { env with env_current = envc;
      env_norm = ref norm; }

  let rec vars_me mp xs me =
    vars_mb (EcPath.mqname mp me.me_name) xs me.me_body

  and vars_mb mp xs = function
    | ME_Alias _ | ME_Decl _ -> xs
    | ME_Structure ms ->
      List.fold_left (vars_item mp) xs ms.ms_body

  and vars_item mp xs = function
    | MI_Module me  -> vars_me mp xs me
    | MI_Variable v -> Sx.add (EcPath.xpath mp v.v_name) xs
    | MI_Function _ -> xs

  let add_restr_to_declared p me env =
    if me.tme_loca = `Local then
      let p = pqname p me.tme_expr.me_name in
      let mp = EcPath.mpath_crt p [] None in
      let xs = vars_mb mp Sx.empty me.tme_expr.me_body  in
      add_xs_to_declared xs env
    else env

  let bind ?(import = import0) name me env =
    assert (name = me.tme_expr.me_name);
    let env = if import.im_immediate then MC.bind_mod name me env else env in
    let env =
      { env with
          env_item = mkitem import (Th_module me) :: env.env_item;
          env_norm = ref !(env.env_norm); } in
    add_restr_to_declared (root env) me env

  let me_of_mt env name (mty, mr) =
    let modsig =
      let modsig =
        match
          omap
            check_not_suspended
            (MC.by_path
               (fun mc -> mc.mc_modsigs)
               (IPPath mty.mt_name) env)
        with
        | None -> lookup_error (`Path mty.mt_name)
        | Some x -> x
      in
      EcSubst.subst_modsig
        ~params:(List.map fst mty.mt_params) EcSubst.empty modsig.tms_sig
    in
    module_expr_of_module_sig name (mty, mr) modsig

  let bind_local name modty env =
    let me = me_of_mt env name modty in
    let path  = IPIdent (name, None) in
    let comps = MC.mc_of_module_param name me in

    let env =
      { env with
          env_current = (
            let current = env.env_current in
            let current = MC._up_mc  true current path in
            let current = MC._up_mod true current me.me_name (path, (me, None)) in
              current);
          env_comps = Mip.add path comps env.env_comps;
          env_norm  = ref !(env.env_norm);
      }
    in
      env

  let declare_local id modty env =
    { (bind_local id modty env) with
        env_modlcs = Sid.add id env.env_modlcs; }

  let is_declared id env = Sid.mem id env.env_modlcs

  let bind_locals bindings env =
    List.fold_left
      (fun env (name, me) -> bind_local name me env)
      env bindings

  let bind_param x mty env =
    bind_local x (mty, mr_full) env

  let bind_params params env =
    List.fold_left
      (fun env (x, mty) -> bind_param x mty env)
      env params

  let enter name params env =
    let env = enter (`Module params) name env in
    bind_params params env

  let add_mod_binding bd env =
    let do1 env (x,gty) =
      match gty with
      | GTmodty mty -> bind_local x mty env
      | _ -> env
    in
      List.fold_left do1 env bd

  let import_vars env p =
    let do1 env = function
      | MI_Variable v ->
        let vp  = EcPath.xpath p v.v_name in
        let ip  = fst (oget (ipath_of_xpath vp)) in
        let obj = v.v_type in
        MC.import_var ip obj env

      | _ -> env
    in

    List.fold_left do1 env (fst (by_mpath p env)).me_comps

  let iter ?name f (env : env) =
    gen_iter (fun mc -> mc.mc_modules) (assert false) ?name f env

  let all ?check ?name (env : env) =
    gen_all (fun mc -> mc.mc_modules) (assert false) ?check ?name env
end

(* -------------------------------------------------------------------- *)
module ModTy = struct
  type t = top_module_sig

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

  let modtype p env =
    let { tms_sig = sig_ } = by_path p env in
    (* eta-normal form *)
    { mt_params = sig_.mis_params;
      mt_name   = p;
      mt_args   = List.map (EcPath.mident -| fst) sig_.mis_params; }

  let bind ?(import = import0) name modty env =
    let env = if import.im_immediate then MC.bind_modty name modty env else env in
      { env with
          env_item = mkitem import (Th_modtype (name, modty)) :: env.env_item }

  let sig_of_mt (env : env) (mt : module_type) : module_sig =
    let { tms_sig = sig_ } = by_path mt.mt_name env in

    let subst =
      List.fold_left2 (fun s (x1,_) a ->
        EcSubst.add_module s x1 a) EcSubst.empty sig_.mis_params mt.mt_args in

    let items = EcSubst.subst_modsig_body subst sig_.mis_body in
    let ois = EcSubst.subst_oracle_infos subst sig_.mis_oinfos in
    let params = mt.mt_params in

    let keep = List.map (EcPath.mident |- fst) params in
    let keep = Sm.of_list keep in
    let ois = Msym.map (OI.filter (fun f -> Sm.mem (f.x_top) keep)) ois in

    { mis_params = params;
      mis_body   = items;
      mis_oinfos = ois; }
end

(* -------------------------------------------------------------------- *)
module NormMp = struct
  let rec norm_mpath_for_typing env p =
    let (ip, (i, args)) = ipath_of_mpath p in
    match Mod.by_ipath_r true ip env with
    | Some ((spi, params), ({ me_body = ME_Alias (arity,alias) } as m, _)) ->
      assert (m.me_params = [] && arity = 0);
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
    | Some (me, _) ->
      begin match me.me_body with
      | ME_Alias (arity,mp) ->
        let nargs = List.length args in
        if arity <= nargs then
          let args, extra = List.takedrop arity args in
          let params = List.take arity me.me_params in
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
          | Some ((spi, params), ({ me_body = ME_Alias (_,alias) } as m, _)) ->
            assert (m.me_params = []);
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
      | Some (me, _) ->
        let params = me.me_params in
        let env', mp =
          if params = [] then env, mp
          else
            Mod.bind_params params env,
            EcPath.m_apply mp (List.map (fun (id,_)->EcPath.mident id) params)in
        let mp = norm_mpath env' mp in
        let xp = EcPath.xpath mp p.x_sub in
        let res = xp_glob xp in
        let en = !(env.env_norm) in
        env.env_norm := { en with norm_xpv = Mx.add p res en.norm_xpv };
        res

  let use_equal us1 us2 =
    Mx.equal (fun _ _ -> true) us1.us_pv us2.us_pv &&
      Sid.equal us1.us_gl us2.us_gl

  let mem_xp x us = Mx.mem x us.us_pv

  (* Return [true] if [x] is forbidden in [restr]. *)
  let use_mem_xp x (restr : use use_restr) =
    let bneg = mem_xp x restr.ur_neg
    and bpos = match restr.ur_pos with
      | None -> false
      | Some sp -> not (mem_xp x sp) in
    bneg || bpos

  let mem_gl mp us =
    assert (mp.m_args = []);
    match mp.m_top with
    | `Local id -> Sid.mem id us.us_gl
    | _ -> assert false

  let use_mem_gl m restr =
    let bneg = mem_gl m restr.ur_neg
    and bpos = match restr.ur_pos with
      | None -> false
      | Some sp -> not (mem_gl m sp) in
    bneg || bpos

  let add_var env xp us =
    let xp = xp_glob xp in
    let xp = norm_xpv env xp in
    let ty = Var.by_xpath xp env in
    { us with us_pv = Mx.add xp ty us.us_pv }

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
            List.fold_left fun_use us (OI.allowed oi)

        | FBalias _ -> assert false in
    fun_use

  let fun_use env xp =
    gen_fun_use env (ref Sx.empty) Sid.empty use_empty xp

  (* The four functions below are used in mod_use_top and item_use. *)
  let rec mod_use env rm fdone us mp =
    let mp = norm_mpath env mp in
    let me, _ = Mod.by_mpath mp env in
    assert (me.me_params = []);
    body_use env rm fdone mp us me.me_comps me.me_body

  and item_use env rm fdone mp us item =
    match item with
    | MI_Module me -> mod_use env rm fdone us (EcPath.mqname mp me.me_name)
    | MI_Variable v -> add_var env (xpath mp v.v_name) us
    | MI_Function f -> fun_use_aux env rm fdone us (xpath mp f.f_name)

  and body_use env rm fdone mp us comps body =
    match body with
    | ME_Alias _ -> assert false
    | ME_Decl _ ->
      let id = match mp.m_top with `Local id -> id | _ -> assert false in
      let us = add_glob_except rm id us in
      List.fold_left (item_use env rm fdone mp) us comps
    | ME_Structure ms ->
      List.fold_left (item_use env rm fdone mp) us ms.ms_body

  and fun_use_aux env rm fdone us f =
    gen_fun_use env fdone rm us f

  let mod_use_top env mp =
    let mp = norm_mpath env mp in
    let me, _ = Mod.by_mpath mp env in
    let params = me.me_params in
    let rm =
      List.fold_left (fun rm (id,_) -> Sid.add id rm) Sid.empty params in
    let env' = Mod.bind_params params env in

    let mp' =
      EcPath.m_apply mp (List.map (fun (id,_) -> EcPath.mident id) params) in

    let fdone = ref Sx.empty in

    mod_use env' rm fdone use_empty mp'

  let mod_use env mp =
    try Mm.find mp !(env.env_norm).mod_use with Not_found ->
      let res = mod_use_top env mp in
      let en = !(env.env_norm) in
      env.env_norm := { en with mod_use = Mm.add mp res en.mod_use };
      res

  let item_use env mp item =
    item_use env Sid.empty (ref Sx.empty) mp use_empty item

  let restr_use env (mr : mod_restr) =
    let get_use (sx, sm) =
      Sx.fold (fun xp r -> add_var env xp r) sx use_empty
      |> Sm.fold (fun mp r -> use_union r (mod_use env mp)) sm in

    { ur_pos = omap get_use mr.ur_pos;
      ur_neg = get_use mr.ur_neg; }

  let get_restr_use env mp =
    try
      Mm.find mp !(env.env_norm).get_restr_use
    with Not_found ->
      let res =
        match (fst (Mod.by_mpath mp env)).me_body with
        | EcModules.ME_Decl (_, mr) -> restr_use env mr
        | _ -> assert false in
      let en = !(env.env_norm) in
      env.env_norm := { en with
        get_restr_use = Mm.add mp res en.get_restr_use };
      res

  let equal_restr env (r1 : mod_restr) (r2 : mod_restr) =
    let us1,us2 = restr_use env r1, restr_use env r2 in
    ur_equal use_equal us1 us2

  let sig_of_mp (env : env) (mp : mpath) : module_sig =
    let mp = norm_mpath env mp in
    let me, _ = Mod.by_mpath mp env in

    { mis_params = me.me_params;
      mis_body = me.me_sig_body;
      mis_oinfos = me.me_oinfos; }

  let norm_pvar env pv =
    match pv with
    | PVloc _ -> pv
    | PVglob xp ->
      let p = norm_xpv env xp in
      if   x_equal p xp then pv
      else EcTypes.pv_glob p

  let flatten_use (us : use) =
    let globs = Sid.elements us.us_gl in
    let globs = List.sort EcIdent.id_ntr_compare globs in

    let pv = Mx.bindings us.us_pv in
    let pv = List.sort (fun (xp1, _) (xp2, _) -> x_ntr_compare xp1 xp2) pv in

    (globs, pv)

  let globals env m mp =
    let us = mod_use env mp in

    let globs, pv = flatten_use us in
    let globs = List.map (fun id -> f_glob id m) globs in
    let pv = List.map (fun (xp, ty) -> f_pvar (pv_glob xp) ty m) pv in

    f_tuple (globs @ pv)

  let norm_glob env m mp = globals env m mp

  let norm_tglob env mp =
    let g = (norm_glob env mhr mp) in
    g.f_ty

  let rec norm_form env =
    let has_mod b =
      List.exists (fun (_,gty) ->
        match gty with GTmodty _ -> true | _ -> false) b in

    let norm_form =                     (* FIXME: use FSmart *)
      EcCoreFol.Hf.memo_rec 107 (fun aux f ->
        match f.f_node with
        | Fquant(q,bd,f) ->
          if has_mod bd then
            let env = Mod.add_mod_binding bd env in
            f_quant q bd (norm_form env f)
          else
          f_quant q bd (aux f)

        | Fpvar(p,m) ->
          let p' = norm_pvar env p in
          if p == p' then f else
            f_pvar p' f.f_ty m

        | FhoareF hf ->
          let pre' = aux hf.hf_pr and p' = norm_xfun env hf.hf_f
          and post' = aux hf.hf_po in
          if hf.hf_pr == pre' && hf.hf_f == p' && hf.hf_po == post' then f else
          f_hoareF pre' p' post'

        (* TODO: missing cases: FbdHoareF and every F*HoareS *)

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
          } in f_pr_r pr'

        | _ -> f)
          in
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
        op_ty   = op.op_ty; }

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
          let m1 = norm_mpath env (EcSubst.subst_mpath subst m1) in
          let m2 = norm_mpath env (EcSubst.subst_mpath subst m2) in
          EcPath.m_equal m1 m2)
        mty1.mt_args mty2.mt_args)
    then
      raise ModTypeNotEquiv

  let mod_type_equiv env ((mty1, mr1) : mty_mr) ((mty2, mr2) : mty_mr) =
    try
      mod_type_equiv env mty1 mty2;
      equal_restr env mr1 mr2
    with ModTypeNotEquiv -> false
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
        Tvar.subst
          (Tvar.init (List.map fst tyd.tyd_params) args)
          body
    | _ -> raise (LookupFailure (`Path name))

  let rec hnorm (ty : ty) (env : env) =
    match ty.ty_node with
    | Tconstr (p, tys) when defined p env -> hnorm (unfold p tys env) env
    | _ -> ty


  let rec ty_hnorm (ty : ty) (env : env) =
    match ty.ty_node with
    | Tconstr (p, tys) when defined p env -> ty_hnorm (unfold p tys env) env
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

  let get_top_decl (ty : ty) (env : env) =
    match (ty_hnorm ty env).ty_node with
    | Tconstr (p, tys) -> Some (p, oget (by_path_opt p env), tys)
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

  let bind ?(import = import0) name ty env =
    let env = if import.im_immediate then rebind name ty env else env in
    { env with env_item =
        mkitem import (Th_type (name, ty)) :: env.env_item }


  let iter ?name f (env : env) =
    gen_iter (fun mc -> mc.mc_tydecls) MC.lookup_tydecls ?name f env

  let all ?check ?name (env : env) =
    gen_all (fun mc -> mc.mc_tydecls) MC.lookup_tydecls ?check ?name env
end

let ty_hnorm = Ty.ty_hnorm

(* -------------------------------------------------------------------- *)
module Op = struct
  type t = EcDecl.operator

  type redmode = [`Force | `IfTransparent | `IfApplied]

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

  let update_ntbase path (name, op) base =
    let nt  =
      match op.op_kind with
      | OB_nott nt -> begin
        let head =
          match nt.ont_body.e_node with
          | Eapp ({ e_node = Eop (p, _)}, _) | Eop (p, _) -> Some p
          | _ -> None
        in
        Some (head, (EcPath.pqname path name, (op.op_tparams, nt)))
      end
      | _ -> None
    in

    ofold
      (fun (hd, nt) nts ->
        Mop.change (fun nts -> Some (nt :: odfl [] nts)) hd nts)
      base nt

  let bind ?(import = import0) name op env =
    let env = if import.im_immediate then MC.bind_operator name op env else env in
    let op  = NormMp.norm_op env op in
    let env_ntbase = update_ntbase (root env) (name, op) env.env_ntbase in

    { env with
        env_ntbase;
        env_item = mkitem import (Th_operator (name, op)) :: env.env_item; }

  let rebind name op env =
    MC.bind_operator name op env

  let core_reduce ?(mode = `IfTransparent) ?(nargs = 0) env p =
    let op = oget (by_path_opt p env) in

    match op.op_kind with
    | OB_oper (Some (OP_Plain f))
    | OB_pred (Some (PR_Plain f)) -> begin
        let f =
          match mode with
          | `Force ->
             f
          | `IfTransparent when not op.op_opaque.reduction ->
             f
          | `IfApplied when nargs >= odfl max_int op.op_unfold ->
             f
          | _ ->
             raise NotReducible
      in (op, f)
    end

    | _ -> raise NotReducible

  let reducible ?mode ?nargs env p =
    if Option.is_some (by_path_opt p env) then
      try
        ignore (core_reduce ?mode ?nargs env p : _ * form);
        true
      with NotReducible -> false
    else false

  let reduce ?mode ?nargs env p tys =
    let op, f = core_reduce ?mode ?nargs env p in
    Tvar.f_subst ~freshen:true (List.map fst op.op_tparams) tys f

  let is_projection env p =
    try  EcDecl.is_proj (by_path p env)
    with LookupFailure _ -> false

  let is_record_ctor env p =
    try  EcDecl.is_rcrd (by_path p env)
    with LookupFailure _ -> false

  let is_dtype_ctor ?nargs env p =
    try
      match (by_path p env).op_kind with
      | OB_oper (Some (OP_Constr (pt,i))) ->
        begin
          match nargs with
          | None -> true
          | Some nargs ->
            let tyv = Ty.by_path pt env in
            let tyv = oget (EcDecl.tydecl_as_datatype tyv) in
            let ctor_ty = snd (List.nth tyv.tydt_ctors i) in
            List.length ctor_ty = nargs
        end
      | _ -> false
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

  let get_notations ~(head : path option) (env : env) =
    Mop.find_def [] head env.env_ntbase

  let iter ?name f (env : env) =
    gen_iter (fun mc -> mc.mc_operators) MC.lookup_operators ?name f env

  let all ?check ?name (env : env) =
    gen_all (fun mc -> mc.mc_operators) MC.lookup_operators ?check ?name env
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

  let bind ?(import = import0) name ax env =
    let ax  = NormMp.norm_ax env ax in
    let env = if import.im_immediate then MC.bind_axiom name ax env else env in
    { env with env_item = mkitem import (Th_axiom (name, ax)) :: env.env_item }

  let rebind name ax env =
    MC.bind_axiom name ax env

  let instanciate p tys env =
    match by_path_opt p env with
    | Some ({ ax_spec = f } as ax) ->
        Tvar.f_subst ~freshen:true (List.map fst ax.ax_tparams) tys f
    | _ -> raise (LookupFailure (`Path p))

  let iter ?name f (env : env) =
    gen_iter (fun mc -> mc.mc_axioms) MC.lookup_axioms ?name f env

  let all ?check ?name (env : env) =
    gen_all (fun mc -> mc.mc_axioms) MC.lookup_axioms ?check ?name env
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

  let add_ring  ty cr lc env = TypeClass.add_instance ([], ty) (`Ring  cr) lc env
  let add_field ty cr lc env = TypeClass.add_instance ([], ty) (`Field cr) lc env
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  type t    = ctheory
  type mode = [`All | thmode]

  type compiled = env Mp.t

  type compiled_theory = {
    name     : symbol;
    ctheory  : t;
    compiled : compiled;
  }

  (* ------------------------------------------------------------------ *)
  let enter name env =
    enter `Theory name env

  (* ------------------------------------------------------------------ *)
  let by_path_opt ?(mode = `All)(p : EcPath.path) (env : env) =
    let obj =
      match MC.by_path (fun mc -> mc.mc_theories) (IPPath p) env, mode with
      | (Some (_, {cth_mode = `Concrete })) as obj, (`All | `Concrete) -> obj
      | (Some (_, {cth_mode = `Abstract })) as obj, (`All | `Abstract) -> obj
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
    | (_, { cth_mode = `Concrete }) as obj, (`All | `Concrete) -> obj
    | (_, { cth_mode = `Abstract }) as obj, (`All | `Abstract) -> obj
    | _ -> lookup_error (`QSymbol qname)

  let lookup_opt ?mode name env =
    try_lf (fun () -> lookup ?mode name env)

  let lookup_path ?mode name env =
    fst (lookup ?mode name env)

  (* ------------------------------------------------------------------ *)
  let env_of_theory (p : EcPath.path) (env : env) =
    if EcPath.isprefix ~prefix:p ~path:env.env_scope.ec_path then
      env
    else
      Option.get (Mp.find_opt p env.env_thenvs)

  (* ------------------------------------------------------------------ *)
  let rec bind_instance_th path inst cth =
    List.fold_left (bind_instance_th_item path) inst cth

  and bind_instance_th_item path inst item =
    if not item.ti_import.im_atimport then inst else

    let xpath x = EcPath.pqname path x in

    match item.ti_item with
    | Th_instance (ty, k, _) ->
        TypeClass.bind_instance ty k inst

    | Th_theory (x, cth) when cth.cth_mode = `Concrete ->
        bind_instance_th (xpath x) inst cth.cth_items

    | Th_type (x, tyd) -> begin
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
  let rec bind_base_th tx path base cth =
    List.fold_left (bind_base_th_item tx path) base cth

  and bind_base_th_item tx path base item =
    if not item.ti_import.im_atimport then base else

    let xpath x = EcPath.pqname path x in

    match item.ti_item with
    | Th_theory (x, cth) -> begin
        match cth.cth_mode with
        | `Concrete ->
            bind_base_th tx (xpath x) base cth.cth_items
        | `Abstract -> base
      end
    | _ -> odfl base (tx path base item.ti_item)

  (* ------------------------------------------------------------------ *)
  let bind_tc_th =
    let for1 path base = function
      | Th_typeclass (x, tc) ->
          tc.tc_prt |> omap (fun prt ->
            let src = EcPath.pqname path x in
            TC.Graph.add ~src ~dst:prt base)
      | _ -> None

    in bind_base_th for1

  (* ------------------------------------------------------------------ *)
  let bind_br_th =
    let for1 path base = function
      | Th_baserw (x,_) ->
         let ip = IPPath (EcPath.pqname path x) in
         assert (not (Mip.mem ip base));
         Some (Mip.add ip Sp.empty base)

      | Th_addrw (b, r, _) ->
         let change = function
           | None   -> assert false
           | Some s -> Some (List.fold_left (fun s r -> Sp.add r s) s r)

         in Some (Mip.change change (IPPath b) base)

      | _ -> None

    in bind_base_th for1

  (* ------------------------------------------------------------------ *)
  let bind_at_th =
    let for1 _path db = function
      | Th_auto (level, base, ps, _) ->
         Some (Auto.updatedb ?base ~level ps db)
      | _ -> None

    in bind_base_th for1

  (* ------------------------------------------------------------------ *)
  let bind_nt_th =
    let for1 path base = function
      | Th_operator (x, ({ op_kind = OB_nott _ } as op)) ->
        Some (Op.update_ntbase path (x, op) base)
      | _ -> None

    in bind_base_th for1

  (* ------------------------------------------------------------------ *)
  let bind_rd_th =
    let for1 _path db = function
      | Th_reduction rules ->
         let rules = List.map (fun (x, _, y) -> (x, y)) rules in
         Some (Reduction.add_rules rules db)
      | _ -> None

    in bind_base_th for1

  (* ------------------------------------------------------------------ *)
  let add_restr_th =
    let for1 path env = function
      | Th_module me -> Some (Mod.add_restr_to_declared path me env)
      | _ -> None
    in bind_base_th for1

  (* ------------------------------------------------------------------ *)
  let bind
    ?(import = import0)
     (cth  : compiled_theory)
     (env : env)
  =
    let { cth_items = items; cth_mode = mode; } = cth.ctheory in
    let env = MC.bind_theory cth.name cth.ctheory env in
    let env = {
      env with
        env_item = mkitem import (Th_theory (cth.name, cth.ctheory)) :: env.env_item }
    in

    let env =
      match import, mode with
      | _, `Concrete ->
          let thname      = EcPath.pqname (root env) cth.name in
          let env_tci     = bind_instance_th thname env.env_tci items in
          let env_tc      = bind_tc_th thname env.env_tc items in
          let env_rwbase  = bind_br_th thname env.env_rwbase items in
          let env_atbase  = bind_at_th thname env.env_atbase items in
          let env_ntbase  = bind_nt_th thname env.env_ntbase items in
          let env_redbase = bind_rd_th thname env.env_redbase items in
          let env =
            { env with
                env_tci   ; env_tc     ; env_rwbase;
                env_atbase; env_ntbase; env_redbase; }
          in
          add_restr_th thname env items

      | _, _ ->
          env
    in

    { env with
        env_thenvs = Mp.set_union env.env_thenvs cth.compiled }

  (* ------------------------------------------------------------------ *)
  let rebind name th env =
    MC.bind_theory name th env

  (* ------------------------------------------------------------------ *)
  let import (path : EcPath.path) (env : env) =
    let rec import (env : env) path (th : theory) =
      let xpath x = EcPath.pqname path x in
      let import_th_item (env : env) (item : theory_item) =
        if not item.ti_import.im_atimport then env else

        match item.ti_item with
        | Th_type (x, ty) ->
            if   ty.tyd_resolve
            then MC.import_tydecl (xpath x) ty env
            else env

        | Th_operator (x, op) ->
            MC.import_operator (xpath x) op env

        | Th_axiom (x, ax) ->
            if   ax.ax_visibility <> `Hidden
            then MC.import_axiom (xpath x) ax env
            else env

        | Th_modtype (x, mty) ->
            MC.import_modty (xpath x) mty env

        | Th_module ({ tme_expr = me; tme_loca = lc; }) ->
            let env = MC.import_mod (IPPath (xpath me.me_name)) (me, Some lc) env in
            let env = MC.import_mc (IPPath (xpath me.me_name)) env in
              env

        | Th_export (p, _) ->
            import env p (by_path ~mode:`Concrete p env).cth_items

        | Th_theory (x, ({cth_mode = `Concrete} as th)) ->
            let env = MC.import_theory (xpath x) th env in
            let env = MC.import_mc (IPPath (xpath x)) env in
              env

        | Th_theory (x, ({cth_mode = `Abstract} as th)) ->
            MC.import_theory (xpath x) th env

        | Th_typeclass (x, tc) ->
            MC.import_typeclass (xpath x) tc env

        | Th_baserw (x, _) ->
            MC.import_rwbase (xpath x) env

        | Th_addrw _ | Th_instance _ | Th_auto _ | Th_reduction _ ->
            env

      in
        List.fold_left import_th_item env th

    in
      import env path (by_path ~mode:`Concrete path env).cth_items

  (* ------------------------------------------------------------------ *)
  let export (path : EcPath.path) lc (env : env) =
    let env = import path env in
    { env with env_item = mkitem import0 (Th_export (path, lc)) :: env.env_item }

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
      let cleared, item_r =
        match item.ti_item with
        | Th_theory (x, cth) ->
           let cleared, items =
             let xpath = EcPath.pqname root x in
             filter_th clears xpath cleared cth.cth_items in
           let item = items |> omap (fun items ->
             let cth = { cth with cth_items = items } in
             Th_theory (x, cth)) in
           (cleared, item)

        | _ -> let item_r = match item.ti_item with

        | Th_axiom (_, { ax_kind = `Lemma }) when thclear ->
            None

        | Th_axiom (x, ({ ax_kind = `Axiom (tags, false) } as ax)) when thclear ->
            Some (Th_axiom (x, { ax with ax_kind = `Axiom (tags, true) }))

        | Th_addrw (p, ps, lc) ->
            let ps = List.filter ((not) |- inclear |- oget |- EcPath.prefix) ps in
            if List.is_empty ps then None else Some (Th_addrw (p, ps,lc))

        | Th_auto (lvl, base, ps, lc) ->
            let ps = List.filter ((not) |- inclear |- oget |- EcPath.prefix) ps in
            if List.is_empty ps then None else Some (Th_auto (lvl, base, ps, lc))

        | (Th_export (p, _)) as item ->
            if Sp.mem p cleared then None else Some item

        | _ as item -> Some item

        in (cleared, item_r)

      in (cleared, omap (fun item_r -> { item with ti_item = item_r; }) item_r)

  (* ------------------------------------------------------------------ *)
  type clear_mode = [`Full | `ClearOnly | `No]

  let close
    ?(clears : path list = [])
    ?(pempty : clear_mode = `No)
     (loca   : is_local)
     (mode   : thmode)
     (env    : env)
  =
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
      let ctheory =
        { cth_items  = items
        ; cth_source = None
        ; cth_loca   = loca
        ; cth_mode   = mode
        } in

      let root = env.env_scope.ec_path in
      let name = EcPath.basename root in

      let compiled =
        Mp.filter
          (fun path _ -> EcPath.isprefix ~prefix:root ~path)
          env.env_thenvs in
      let compiled = Mp.add env.env_scope.ec_path env compiled in

      { name; ctheory; compiled; }
    )

  (* ------------------------------------------------------------------ *)
  let require (compiled : compiled_theory) (env : env) =
    let cth    = compiled.ctheory in
    let rootnm = EcCoreLib.p_top in
    let thpath = EcPath.pqname rootnm compiled.name in

    let env =
      match cth.cth_mode with
      | `Concrete ->
          let (_, thmc), submcs =
            MC.mc_of_theory_r rootnm (compiled.name, cth)
          in MC.bind_submc env rootnm ((compiled.name, thmc), submcs)

      | `Abstract -> env
    in

    let topmc = Mip.find (IPPath rootnm) env.env_comps in
    let topmc = MC._up_theory false topmc compiled.name (IPPath thpath, cth) in
    let topmc = MC._up_mc false topmc (IPPath thpath) in

    let current = env.env_current in
    let current = MC._up_theory true current compiled.name (IPPath thpath, cth) in
    let current = MC._up_mc true current (IPPath thpath) in

    let comps = env.env_comps in
    let comps = Mip.add (IPPath rootnm) topmc comps in

    let env = { env with env_current = current; env_comps = comps; } in

    match cth.cth_mode with
    | `Abstract ->
      { env with
        env_thenvs  = Mp.set_union env.env_thenvs compiled.compiled; }

    | `Concrete ->
      { env with
          env_tci     = bind_instance_th thpath env.env_tci cth.cth_items;
          env_tc      = bind_tc_th thpath env.env_tc cth.cth_items;
          env_rwbase  = bind_br_th thpath env.env_rwbase cth.cth_items;
          env_atbase  = bind_at_th thpath env.env_atbase cth.cth_items;
          env_ntbase  = bind_nt_th thpath env.env_ntbase cth.cth_items;
          env_redbase = bind_rd_th thpath env.env_redbase cth.cth_items;
          env_thenvs  = Mp.set_union env.env_thenvs compiled.compiled; }
end

(* -------------------------------------------------------------------- *)
let initial gstate = empty gstate

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of EcTypes.ty
  | `Function  of function_
  | `Module    of module_expr
  | `ModType   of module_sig
]

(*  FIXME section :  Global ? *)
let bind1 ((x, eb) : symbol * ebinding) (env : env) =
  match eb with
  | `Variable ty -> Var   .bind_pvglob x ty env
  | `Function f  -> Fun   .bind x f env
  | `Module   m  -> Mod   .bind x {tme_expr = m; tme_loca = `Global} env
  | `ModType  i  -> ModTy .bind x {tms_sig  = i; tms_loca = `Global} env

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
        LD_var (ty_subst s ty, body |> omap (Fsubst.f_subst s))

    | LD_mem mt ->
        LD_mem (EcMemory.mt_subst (ty_subst s) mt)

    | LD_modty mty ->
        LD_modty (Fsubst.mty_mr_subst s mty)

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
  | LD_modty p ->
      gty_fv (GTmodty p)
  | LD_abs_st us ->
    let add fv (x,_) = match x with
      | PVglob x -> EcPath.x_fv fv x
      | PVloc _ -> fv in

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
    | LD_mem mt -> is_bound s mt
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
    | LD_modty i -> Mod.bind_local x i env
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


let pp_debug_form = ref (fun _env _fmt _f -> assert false)
