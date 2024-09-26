(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcAst
open EcTypes
open EcPath

module Sid = EcIdent.Sid
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
type lvalue = EcAst.lvalue

let lv_equal = EcAst.lv_equal

(* -------------------------------------------------------------------- *)
let lv_fv = EcAst.lv_fv

let symbol_of_lv = function
  | LvVar (pv, _) ->
      EcTypes.symbol_of_pv pv

  | LvTuple pvs ->
      String.concat "" (List.map (EcTypes.symbol_of_pv |- fst) pvs)

let ty_of_lv = function
  | LvVar   (_, ty)       -> ty
  | LvTuple tys           -> EcTypes.ttuple (List.map snd tys)

let lv_of_list = function
  | [] -> None
  | [(pv, ty)] -> Some (LvVar (pv, ty))
  | pvs -> Some (LvTuple pvs)

let lv_to_list = function
  | LvVar (pv, _) -> [pv]
  | LvTuple pvs -> List.fst pvs

let name_of_lv lv =
  match lv with
  | LvVar (pv, _) ->
     EcTypes.name_of_pvar pv
  | LvTuple pvs ->
     String.concat "_" (List.map (EcTypes.name_of_pvar |- fst) pvs)

let lv_of_expr e =
  match e.e_node with
  | Evar pv ->
     LvVar (pv, e_ty e)
  | Etuple pvs ->
     LvTuple (List.map (fun e -> EcTypes.destr_var e, e_ty e) pvs)
  | _ -> failwith "failed to construct lv from expr"

(* -------------------------------------------------------------------- *)
type instr = EcAst.instr

type instr_node = EcAst.instr_node

type stmt = EcAst.stmt

(* -------------------------------------------------------------------- *)
let i_equal   = EcAst.i_equal
let i_hash    = EcAst.i_hash
let i_compare = fun i1 i2 -> i_hash i1 - i_hash i2
let i_fv      = EcAst.i_fv
let i_node i  = i.i_node

let s_equal   = EcAst.s_equal
let s_hash    = EcAst.s_hash
let s_compare = fun s1 s2 -> s_hash s1 - s_hash s2
let s_fv      = EcAst.s_fv

(* -------------------------------------------------------------------- *)
module MSHi = EcMaps.MakeMSH(struct type t = instr let tag i = i.i_tag end)
module Si   = MSHi.S
module Mi   = MSHi.M
module Hi   = MSHi.H

(* -------------------------------------------------------------------- *)

let stmt = EcAst.stmt

let rstmt s = stmt (List.rev s)

(* --------------------------------------------------------------------- *)
let i_asgn     (lv, e)      = mk_instr (Sasgn (lv, e))
let i_rnd      (lv, e)      = mk_instr (Srnd (lv, e))
let i_call     (lv, m, tys) = mk_instr (Scall (lv, m, tys))
let i_if       (c, s1, s2)  = mk_instr (Sif (c, s1, s2))
let i_while    (c, s)       = mk_instr (Swhile (c, s))
let i_match    (e, b)       = mk_instr (Smatch (e, b))
let i_assert   e            = mk_instr (Sassert e)
let i_abstract id           = mk_instr (Sabstract id)

let s_seq      s1 s2        = stmt (s1.s_node @ s2.s_node)
let s_empty                 = stmt []

let s_asgn     arg = stmt [i_asgn arg]
let s_rnd      arg = stmt [i_rnd arg]
let s_call     arg = stmt [i_call arg]
let s_if       arg = stmt [i_if arg]
let s_while    arg = stmt [i_while arg]
let s_match    arg = stmt [i_match arg]
let s_assert   arg = stmt [i_assert arg]
let s_abstract arg = stmt [i_abstract arg]

(* -------------------------------------------------------------------- *)
let get_asgn = function
  | { i_node = Sasgn (lv, e) } -> Some (lv, e)
  | _ -> None

let get_rnd = function
  | { i_node = Srnd (lv, e) } -> Some (lv, e)
  | _ -> None

let get_call = function
  | { i_node = Scall (lv, f, fs) } -> Some (lv, f, fs)
  | _ -> None

let get_if = function
  | { i_node = Sif (e, s1, s2) } -> Some (e, s1, s2)
  | _ -> None

let get_while = function
  | { i_node = Swhile (e, s) } -> Some (e, s)
  | _ -> None

let get_match = function
  | { i_node = Smatch (e, b) } -> Some (e, b)
  | _ -> None

let get_assert = function
  | { i_node = Sassert e } -> Some e
  | _ -> raise Not_found

(* -------------------------------------------------------------------- *)
let _destr_of_get (get : instr -> 'a option) (i : instr) =
  match get i with Some x -> x | None -> raise Not_found

let destr_asgn   = _destr_of_get get_asgn
let destr_rnd    = _destr_of_get get_rnd
let destr_call   = _destr_of_get get_call
let destr_if     = _destr_of_get get_if
let destr_while  = _destr_of_get get_while
let destr_match  = _destr_of_get get_match
let destr_assert = _destr_of_get get_assert

(* -------------------------------------------------------------------- *)
let _is_of_get (get : instr -> 'a option) (i : instr) =
  EcUtils.is_some (get i)

let is_asgn   = _is_of_get get_asgn
let is_rnd    = _is_of_get get_rnd
let is_call   = _is_of_get get_call
let is_if     = _is_of_get get_if
let is_while  = _is_of_get get_while
let is_match  = _is_of_get get_match
let is_assert = _is_of_get get_assert

(* -------------------------------------------------------------------- *)
module Uninit = struct    (* FIXME: generalize this for use in ecPV *)
  let e_pv e =
    let rec e_pv sid e =
      match e.e_node with
      | Evar (PVglob _) -> sid
      | Evar (PVloc id) -> Ssym.add id sid
      | _               -> e_fold e_pv sid e in

    e_pv Ssym.empty e
end

let rec lv_get_uninit_read (w : Ssym.t) (lv : lvalue) =
  let sx_of_pv pv = match pv with
    | PVloc v -> Ssym.singleton v
    | PVglob _ -> Ssym.empty
  in

  match lv with
  | LvVar (x, _) ->
      Ssym.union (sx_of_pv x) w

  | LvTuple xs ->
      let w' = List.map (sx_of_pv |- fst) xs in
      Ssym.big_union (w :: w')

and s_get_uninit_read (w : Ssym.t) (s : stmt) =
  let do1 (w, r) i =
    let w, r' = i_get_uninit_read w i in
    (w, Ssym.union r r')

  in List.fold_left do1 (w, Ssym.empty) s.s_node

and i_get_uninit_read (w : Ssym.t) (i : instr) =
  match i.i_node with
  | Sasgn (lv, e) | Srnd (lv, e) ->
      let r1 = Ssym.diff (Uninit.e_pv e) w in
      let w2 = lv_get_uninit_read w lv in
      (Ssym.union w w2, r1)

  | Scall (olv, _, args) ->
      let r1 = Ssym.diff (Ssym.big_union (List.map (Uninit.e_pv) args)) w in
      let w = olv |> omap (lv_get_uninit_read w) |> odfl w in
      (w, r1)

  | Sif (e, s1, s2) ->
      let r = Ssym.diff (Uninit.e_pv e) w in
      let w1, r1 = s_get_uninit_read w s1 in
      let w2, r2 = s_get_uninit_read w s2 in
      (Ssym.union w (Ssym.inter w1 w2), Ssym.big_union [r; r1; r2])

  | Swhile (e, s) ->
      let r  = Ssym.diff (Uninit.e_pv e) w in
      let rs = snd (s_get_uninit_read w s) in
      (w, Ssym.union r rs)

  | Smatch (e, bs) ->
      let r   = Ssym.diff (Uninit.e_pv e) w in
      let wrs = List.map (fun (_, b) -> s_get_uninit_read w b) bs in
      let ws, rs = List.split wrs in
      (Ssym.union w (Ssym.big_inter ws), Ssym.big_union (r :: rs))

  | Sassert e ->
      (w, Ssym.diff (Uninit.e_pv e) w)

  | Sabstract (_ : EcIdent.t) ->
      (w, Ssym.empty)

let get_uninit_read (s : stmt) =
  snd (s_get_uninit_read Ssym.empty s)

(* -------------------------------------------------------------------- *)
type 'a use_restr = 'a EcAst.use_restr

let ur_app f a =
  { ur_pos = (omap f) a.ur_pos;
    ur_neg = f a.ur_neg; }

(* Nothing is restricted. *)
let ur_empty emp = { ur_pos = None; ur_neg = emp; }

(* Everything is restricted. *)
let ur_full emp = { ur_pos = Some emp; ur_neg = emp; }

let ur_pos_subset subset ur1 ur2 = match ur1,ur2 with
  | _, None -> true             (* Indeed, [None] means everybody. *)
  | None, Some _ -> false
  | Some s1, Some s2 -> subset s1 s2

let ur_equal = EcAst.ur_equal

(* Union for negative restrictions, intersection for positive ones.
   [None] stands for everybody. *)
let ur_union union inter ur1 ur2 =
  let ur_pos = match ur1.ur_pos, ur2.ur_pos with
    | None, None -> None
    | None, Some s | Some s, None -> Some s
    | Some s1, Some s2 -> some @@ inter s1 s2 in

  { ur_pos = ur_pos;
    ur_neg = union ur1.ur_neg ur2.ur_neg; }

(* Converse of ur_union. *)
let ur_inter union inter ur1 ur2 =
  let ur_pos = match ur1.ur_pos, ur2.ur_pos with
    | None, _ | _, None -> None
    | Some s1, Some s2 -> some @@ union s1 s2 in

  { ur_pos = ur_pos;
    ur_neg = inter ur1.ur_neg ur2.ur_neg; }

(* -------------------------------------------------------------------- *)
(* Oracle information of a procedure [M.f]. *)
module PreOI : sig
  type t = EcAst.oracle_info

  val equal : t -> t -> bool

  val hash : t -> int

  val allowed : t -> xpath list

  val allowed_s : t -> Sx.t

  val mk : xpath list -> t

  val filter : (xpath -> bool) -> t -> t
end = struct
  type t = EcAst.oracle_info

  let equal =
    EcAst.oi_equal

  let hash =
    EcAst.oi_hash

  let allowed oi =
    oi.oi_calls

  let allowed_s oi =
    allowed oi |> Sx.of_list

  let mk oi_calls =
    { oi_calls }

  let filter f oi =
    mk (List.filter f oi.oi_calls)
end

(* -------------------------------------------------------------------- *)
type mr_xpaths = EcAst.mr_xpaths

type mr_mpaths = EcAst.mr_mpaths

type mod_restr = EcAst.mod_restr

let mr_equal = EcAst.mr_equal
let mr_hash  = EcAst.mr_hash

let ois_is_empty (ois : oracle_infos) =
  Msym.for_all (fun _ oi -> [] = PreOI.allowed oi) ois

let mr_xpaths_fv (m : mr_xpaths) : int Mid.t =
  EcPath.Sx.fold
    (fun xp fv -> EcPath.x_fv fv xp)
    (Sx.union
       m.ur_neg
       (EcUtils.odfl Sx.empty m.ur_pos))
    EcIdent.Mid.empty

let mr_mpaths_fv (m : mr_mpaths) : int Mid.t =
  EcPath.Sm.fold
    (fun mp fv -> EcPath.m_fv fv mp)
    (Sm.union
       m.ur_neg
       (EcUtils.odfl Sm.empty m.ur_pos))
    EcIdent.Mid.empty

(* -------------------------------------------------------------------- *)
type funsig = {
  fs_name   : symbol;
  fs_arg    : EcTypes.ty;
  fs_anames : ovariable list;
  fs_ret    : EcTypes.ty;
}

let fs_equal f1 f2 =
    List.all2 EcTypes.ov_equal f1.fs_anames f2.fs_anames
    && (EcTypes.ty_equal f1.fs_ret f2.fs_ret)
    && (EcTypes.ty_equal f1.fs_arg f2.fs_arg)
    && (EcSymbols.sym_equal f1.fs_name f2.fs_name)

(* -------------------------------------------------------------------- *)
type module_type = EcAst.module_type

type module_sig_body_item = Tys_function of funsig

type module_sig_body = module_sig_body_item list

type module_sig = {
  mis_params : (EcIdent.t * module_type) list;
  mis_body   : module_sig_body;
  mis_oinfos : oracle_infos;
}

type top_module_sig = {
  tms_sig  : module_sig;
  tms_loca : is_local;
}

(* -------------------------------------------------------------------- *)
(* Simple module signature, without restrictions. *)
type module_smpl_sig = {
  miss_params : (EcIdent.t * module_type) list;
  miss_body   : module_sig_body;
}

let sig_smpl_sig_coincide msig smpl_sig =
  let eqparams =
    List.for_all2 EcIdent.id_equal
      (List.map fst msig.mis_params)
      (List.map fst smpl_sig.miss_params) in

  let ls =
    List.map (fun (Tys_function fs) -> fs.fs_name, fs ) msig.mis_body
    |> EcSymbols.Msym.of_list
  and ls_smpl =
    List.map (fun (Tys_function fs) -> fs.fs_name, fs ) smpl_sig.miss_body
    |> EcSymbols.Msym.of_list in
  let eqsig =
    Msym.fold2_union (fun _ aopt bopt eqsig -> match aopt, bopt with
        | Some fs1, Some fs2 -> (fs_equal fs1 fs2) && eqsig
        | _ -> false)  ls_smpl ls true; in

  eqparams && eqsig

(* -------------------------------------------------------------------- *)
type uses = {
  us_calls  : xpath list;
  us_reads  : Sx.t;
  us_writes : Sx.t;
}

let mk_uses c r w =
  let map s = Sx.fold (fun x s ->
      Sx.change
        (fun b -> assert (not b); true)
        (EcTypes.xp_glob x) s) s Sx.empty in
  {us_calls = c; us_reads = map r; us_writes = map w }

(* -------------------------------------------------------------------- *)
type function_def = {
  f_locals : variable list;
  f_body   : stmt;
  f_ret    : EcTypes.expr option;
  f_uses   : uses;
}

let fd_equal f1 f2 =
     (s_equal f1.f_body f2.f_body)
  && (EcUtils.opt_equal EcTypes.e_equal f1.f_ret f2.f_ret)
  && (List.all2 EcTypes.v_equal f1.f_locals f2.f_locals)

let fd_hash f =
  Why3.Hashcons.combine2
    (s_hash f.f_body)
    (Why3.Hashcons.combine_option EcTypes.e_hash f.f_ret)
    (Why3.Hashcons.combine_list EcTypes.v_hash 0 f.f_locals)

(* -------------------------------------------------------------------- *)
type function_body =
| FBdef   of function_def
| FBalias of xpath
| FBabs   of PreOI.t

type function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : function_body;
}

(* -------------------------------------------------------------------- *)
type abs_uses = {
  aus_calls  : EcPath.xpath list;
  aus_reads  : (EcTypes.prog_var * EcTypes.ty) list;
  aus_writes : (EcTypes.prog_var * EcTypes.ty) list;
}

type module_expr = {
  me_name     : symbol;
  me_params   : (EcIdent.t * module_type) list;
  me_body     : module_body;
  me_comps    : module_comps;
  me_sig_body : module_sig_body;
  me_oinfos   : oracle_infos;
}

and module_body =
  | ME_Alias       of int * EcPath.mpath
  | ME_Structure   of module_structure       (* Concrete modules. *)
  | ME_Decl        of mty_mr                 (* Abstract modules. *)

and module_structure = {
  ms_body      : module_item list;
}

and module_item =
  | MI_Module   of module_expr
  | MI_Variable of variable
  | MI_Function of function_

and module_comps = module_comps_item list

and module_comps_item = module_item

type top_module_expr = {
  tme_expr : module_expr;
  tme_loca : locality;
}

(* -------------------------------------------------------------------- *)
let ur_hash = EcAst.ur_hash

let mty_hash = EcAst.mty_hash
let mty_equal = EcAst.mty_equal

(* -------------------------------------------------------------------- *)
let get_uninit_read_of_fun (f : function_) =
  match f.f_def with
  | FBalias _ | FBabs _ -> Ssym.empty

  | FBdef fd ->
      let w =
        let toloc ov =
          (* We don't allow anonymous parameters on concrete procedures *)
          assert (is_some ov.ov_name);
          oget ov.ov_name
        in
        let w = List.map toloc f.f_sig.fs_anames in
        Ssym.of_list w
      in

      let w, r  = s_get_uninit_read w fd.f_body in
      let raout = fd.f_ret |> omap (Uninit.e_pv) in
      let raout = Ssym.diff (raout |> odfl Ssym.empty) w in
      Ssym.union r raout

(* -------------------------------------------------------------------- *)
let get_uninit_read_of_module (p : path) (me : module_expr) =
  let rec doit_me acc (mp, me) =
    match me.me_body with
    | ME_Alias     _  -> acc
    | ME_Decl      _  -> acc
    | ME_Structure mb -> doit_mb acc (mp, mb)

  and doit_mb acc (mp, mb) =
    List.fold_left
      (fun acc item -> doit_mb1 acc (mp, item))
      acc mb.ms_body

  and doit_mb1 acc (mp, item) =
    match item with
    | MI_Module subme ->
        doit_me acc (EcPath.mqname mp subme.me_name, subme)

    | MI_Variable _ ->
        acc

    | MI_Function f ->
        let xp = xpath mp f.f_name in
        let r  = get_uninit_read_of_fun f in
        if Ssym.is_empty r then acc else (xp, r) :: acc

  in

  let mp =
    let margs =
      List.map
        (fun (x, _) -> EcPath.mpath_abs x [])
        me.me_params
    in EcPath.mpath_crt (EcPath.pqname p me.me_name) margs None

  in List.rev (doit_me [] (mp, me))
