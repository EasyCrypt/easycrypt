(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcUid

module BI = EcBigInt

type memory = EcIdent.t

type 'a equality = 'a -> 'a -> bool
type 'a hash = 'a -> int
type 'a fv   = 'a -> int EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
type pvar_kind =
  | PVKglob
  | PVKloc

type prog_var =
  | PVglob of EcPath.xpath
  | PVloc of EcSymbols.symbol

type equantif  = [ `ELambda | `EForall | `EExists ]

type quantif =
  | Lforall
  | Lexists
  | Llambda

(* -------------------------------------------------------------------- *)
type hoarecmp = FHle | FHeq | FHge

(* -------------------------------------------------------------------- *)

type 'a use_restr = {
  ur_pos : 'a option;   (* If not None, can use only element in this set. *)
  ur_neg : 'a;          (* Cannot use element in this set. *)
}

type mr_xpaths = EcPath.Sx.t use_restr
type mr_mpaths = EcPath.Sm.t use_restr

(* -------------------------------------------------------------------- *)
type ty = {
  ty_node : ty_node;
  ty_fv   : int Mid.t; (* only ident appearing in path *)
  ty_tag  : int;
}

and ty_node =
  | Tglob   of EcIdent.t (* The tuple of global variable of the module *)
  | Tunivar of EcUid.uid
  | Tvar    of EcIdent.t
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

(* -------------------------------------------------------------------- *)
and ovariable = {
  ov_name : EcSymbols.symbol option;
  ov_type : ty;
}

and variable = {
  v_name : EcSymbols.symbol;   (* can be "_" *)
  v_type : ty;
}

and lpattern =
  | LSymbol of (EcIdent.t * ty)
  | LTuple  of (EcIdent.t * ty) list
  | LRecord of EcPath.path * (EcIdent.t option * ty) list

and expr = {
  e_node : expr_node;
  e_ty   : ty;
  e_fv   : int Mid.t;
  e_tag  : int;
}

and expr_node =
  | Eint   of BI.zint                      (* int. literal          *)
  | Elocal of EcIdent.t                    (* let-variables         *)
  | Evar   of prog_var                     (* module variable       *)
  | Eop    of EcPath.path * ty list        (* op apply to type args *)
  | Eapp   of expr * expr list             (* op. application       *)
  | Equant of equantif * ebindings * expr  (* fun/forall/exists     *)
  | Elet   of lpattern * expr * expr       (* let binding           *)
  | Etuple of expr list                    (* tuple constructor     *)
  | Eif    of expr * expr * expr           (* _ ? _ : _             *)
  | Ematch of expr * expr list * ty        (* match _ with _        *)
  | Eproj  of expr * int                   (* projection of a tuple *)

and ebinding  = EcIdent.t * ty
and ebindings = ebinding list

(* -------------------------------------------------------------------- *)

and lvalue =
  | LvVar   of (prog_var * ty)
  | LvTuple of (prog_var * ty) list

(* -------------------------------------------------------------------- *)
and instr = {
  i_node : instr_node;
  i_fv : int Mid.t;
  i_tag  : int;
}

and instr_node =
  | Sasgn     of lvalue * expr
  | Srnd      of lvalue * expr
  | Scall     of lvalue option * EcPath.xpath * expr list
  | Sif       of expr * stmt * stmt
  | Swhile    of expr * stmt
  | Smatch    of expr * ((EcIdent.t * ty) list * stmt) list
  | Sassert   of expr
  | Sabstract of EcIdent.t

and stmt = {
  s_node : instr list;
  s_fv   : int Mid.t;
  s_tag  : int;
}

(* -------------------------------------------------------------------- *)
and oracle_info = {
  oi_calls : xpath list;
}

and oracle_infos = oracle_info Msym.t

and mod_restr = (EcPath.Sx.t * EcPath.Sm.t) use_restr

and module_type = {
  mt_params : (EcIdent.t * module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
}

(* -------------------------------------------------------------------- *)
and proj_arg =
  { arg_ty  : ty; (* type of the procedure argument "arg" *)
    arg_pos : int;       (* projection *)
  }

and local_memtype = {
  lmt_name : symbol option;     (* provides access to the full local memory *)
  lmt_decl : ovariable list;
  lmt_proj : (int * ty) Msym.t;  (* where to find the symbol in mt_decl and its type *)
  lmt_ty   : ty;                 (* ttuple (List.map v_type mt_decl) *)
  lmt_n    : int;                (* List.length mt_decl *)
}

and memtype =
  | Lmt_concrete of local_memtype option

and memenv = memory * memtype

(* -------------------------------------------------------------------- *)
and gty =
  | GTty    of ty
  | GTmodty of mty_mr
  | GTmem   of memtype

and mty_mr = module_type * mod_restr

and binding  = (EcIdent.t * gty)
and bindings = binding list

and form = {
  f_node : f_node;
  f_ty   : ty;
  f_fv   : int Mid.t; (* local, memory, module ident *)
  f_tag  : int;
}

and f_node =
  | Fquant  of quantif * bindings * form
  | Fif     of form * form * form
  | Fmatch  of form * form list * ty
  | Flet    of lpattern * form * form
  | Fint    of BI.zint
  | Flocal  of EcIdent.t
  | Fpvar   of prog_var * memory
  | Fglob   of EcIdent.t * memory
  | Fop     of EcPath.path * ty list
  | Fapp    of form * form list
  | Ftuple  of form list
  | Fproj   of form * int

  | FhoareF of sHoareF (* $hr / $hr *)
  | FhoareS of sHoareS

  | FbdHoareF of bdHoareF (* $hr / $hr *)
  | FbdHoareS of bdHoareS

  | FeHoareF of eHoareF (* $hr / $hr *)
  | FeHoareS of eHoareS

  | FequivF of equivF (* $left,$right / $left,$right *)
  | FequivS of equivS

  | FeagerF of eagerF

  | Fpr of pr (* hr *)

and eagerF = {
  eg_pr : form;
  eg_sl : stmt;  (* No local program variables *)
  eg_fl : EcPath.xpath;
  eg_fr : EcPath.xpath;
  eg_sr : stmt;  (* No local program variables *)
  eg_po : form
}

and equivF = {
  ef_pr : form;
  ef_fl : EcPath.xpath;
  ef_fr : EcPath.xpath;
  ef_po : form;
}

and equivS = {
  es_ml  : memenv;
  es_mr  : memenv;
  es_pr  : form;
  es_sl  : stmt;
  es_sr  : stmt;
  es_po  : form; }

and sHoareF = {
  hf_pr : form;
  hf_f  : EcPath.xpath;
  hf_po : form;
}

and sHoareS = {
  hs_m  : memenv;
  hs_pr : form;
  hs_s  : stmt;
  hs_po : form; }


and eHoareF = {
  ehf_pr  : form;
  ehf_f   : EcPath.xpath;
  ehf_po  : form;
}

and eHoareS = {
  ehs_m   : memenv;
  ehs_pr  : form;
  ehs_s   : stmt;
  ehs_po  : form;
}

and bdHoareF = {
  bhf_pr  : form;
  bhf_f   : EcPath.xpath;
  bhf_po  : form;
  bhf_cmp : hoarecmp;
  bhf_bd  : form;
}

and bdHoareS = {
  bhs_m   : memenv;
  bhs_pr  : form;
  bhs_s   : stmt;
  bhs_po  : form;
  bhs_cmp : hoarecmp;
  bhs_bd  : form;
}

and pr = {
  pr_mem   : memory;
  pr_fun   : EcPath.xpath;
  pr_args  : form;
  pr_event : form;
}

(* ----------------------------------------------------------------- *)
(* Equality, hash, and fv                                            *)
(* ----------------------------------------------------------------- *)
let ty_equal : ty -> ty -> bool = (==)
let ty_hash ty = ty.ty_tag
let ty_fv ty = ty.ty_fv

(* -------------------------------------------------------------------- *)
let v_equal vd1 vd2 =
  vd1.v_name = vd2.v_name &&
  ty_equal vd1.v_type vd2.v_type

let v_hash v =
  Why3.Hashcons.combine
    (Hashtbl.hash v.v_name)
    (ty_hash v.v_type)

(* -------------------------------------------------------------------- *)
let pv_equal v1 v2 = match v1, v2 with
  | PVglob x1, PVglob x2 ->
    EcPath.x_equal x1 x2
  | PVloc i1, PVloc i2 -> EcSymbols.sym_equal i1 i2
  | PVloc _, PVglob _ | PVglob _, PVloc _ -> false

let pv_kind = function
  | PVglob _ -> PVKglob
  | PVloc _ -> PVKloc

let pv_hash v =
  let h = match v with
    | PVglob x -> EcPath.x_hash x
    | PVloc i -> Hashtbl.hash i in
  Why3.Hashcons.combine
    h (if pv_kind v = PVKglob then 1 else 0)

let pv_fv = function
  | PVglob x -> EcPath.x_fv Mid.empty x
  | PVloc _ -> Mid.empty

(* -------------------------------------------------------------------- *)
let idty_equal (x1,t1) (x2,t2) =
  EcIdent.id_equal x1 x2 && ty_equal t1 t2

let lp_equal p1 p2 =
  match p1, p2 with
  | LSymbol xt1, LSymbol xt2 -> idty_equal xt1 xt2
  | LTuple lx1, LTuple lx2 -> List.all2 idty_equal lx1 lx2
  | _ -> false

let idty_hash (x,t) = Why3.Hashcons.combine (EcIdent.id_hash x) (ty_hash t)

let lp_hash = function
  | LSymbol  x -> idty_hash x
  | LTuple  lx -> Why3.Hashcons.combine_list idty_hash 0 lx

  | LRecord (p, lx) ->
      let for1 (x, ty) =
        Why3.Hashcons.combine (ty_hash ty)
          (Why3.Hashcons.combine_option EcIdent.id_hash x)
      in
        Why3.Hashcons.combine_list for1 (p_hash p) lx

let lp_fv = function
  | LSymbol (id, _) ->
      Sid.singleton id

  | LTuple ids ->
      List.fold_left (fun s (id, _) -> Sid.add id s) Sid.empty ids

  | LRecord (_, ids) ->
      List.fold_left
        (fun s (id, _) -> ofold Sid.add s id)
        Sid.empty ids

(* -------------------------------------------------------------------- *)
let e_equal   = ((==) : expr -> expr -> bool)
let e_hash    = fun e -> e.e_tag
let e_fv e    = e.e_fv

(* -------------------------------------------------------------------- *)
let eqt_equal : equantif -> equantif -> bool = (==)
let eqt_hash  : equantif -> int = Hashtbl.hash

(* -------------------------------------------------------------------- *)

let lv_equal lv1 lv2 =
  match lv1, lv2 with
  | LvVar (pv1, ty1), LvVar (pv2, ty2) ->
         (pv_equal pv1 pv2)
      && (ty_equal ty1 ty2)

  | LvTuple tu1, LvTuple tu2 ->
      List.all2
        (fun (pv1, ty1) (pv2, ty2) ->
             (pv_equal pv1 pv2)
          && (ty_equal ty1 ty2))
        tu1 tu2

  | _, _ -> false

let lv_fv = function
  | LvVar (pv, _) ->
      pv_fv pv

  | LvTuple pvs ->
      let add s (pv, _) = EcIdent.fv_union s (pv_fv pv) in
      List.fold_left add Mid.empty pvs


let lv_hash = function
  | LvVar (pv, ty) ->
      Why3.Hashcons.combine (pv_hash pv) (ty_hash ty)

  | LvTuple pvs ->
      Why3.Hashcons.combine_list
        (fun (pv, ty) ->
          Why3.Hashcons.combine (pv_hash pv) (ty_hash ty)) 0 pvs


(* -------------------------------------------------------------------- *)
let i_equal   = ((==) : instr -> instr -> bool)
let i_hash    = fun i -> i.i_tag
let i_fv i    = i.i_fv

let s_equal   = ((==) : stmt -> stmt -> bool)
let s_hash    = fun s -> s.s_tag
let s_fv      = fun s -> s.s_fv


(*-------------------------------------------------------------------- *)
let qt_equal : quantif -> quantif -> bool = (==)
let qt_hash  : quantif -> int = Hashtbl.hash

(*-------------------------------------------------------------------- *)
let f_equal : form -> form -> bool = (==)
let f_hash f = f.f_tag
let f_fv f = f.f_fv

(* -------------------------------------------------------------------- *)
let oi_equal oi1 oi2 =
  List.all2 EcPath.x_equal oi1.oi_calls oi2.oi_calls

let oi_hash oi =
  Why3.Hashcons.combine_list EcPath.x_hash 0
    (List.sort EcPath.x_compare oi.oi_calls)

(* -------------------------------------------------------------------- *)
let hcmp_hash : hoarecmp -> int = Hashtbl.hash

(* -------------------------------------------------------------------- *)
let ov_hash v =
  Why3.Hashcons.combine
    (Hashtbl.hash v.ov_name)
    (ty_hash v.ov_type)

let ov_equal vd1 vd2 =
  EcUtils.opt_equal (=) vd1.ov_name vd2.ov_name &&
  ty_equal vd1.ov_type vd2.ov_type

let v_hash v =
  Why3.Hashcons.combine
    (Hashtbl.hash v.v_name)
    (ty_hash v.v_type)

let v_equal vd1 vd2 =
  vd1.v_name = vd2.v_name &&
  ty_equal vd1.v_type vd2.v_type

(* -------------------------------------------------------------------- *)

let mr_xpaths (mr : mod_restr) : mr_xpaths =
  { ur_pos = omap fst mr.ur_pos;
    ur_neg = fst mr.ur_neg; }

let mr_mpaths (mr : mod_restr) : mr_mpaths =
  { ur_pos = omap snd  mr.ur_pos;
    ur_neg = snd mr.ur_neg; }

let ur_equal (equal : 'a -> 'a -> bool) ur1 ur2 =
  equal ur1.ur_neg ur2.ur_neg
  && (opt_equal equal) ur1.ur_pos ur2.ur_pos

let ur_hash elems el_hash ur =
  Why3.Hashcons.combine
    (Why3.Hashcons.combine_option
       (fun l -> Why3.Hashcons.combine_list el_hash 0 (elems l))
       ur.ur_pos)
    (Why3.Hashcons.combine_list el_hash 0
       (elems ur.ur_neg))

let mr_equal mr1 mr2 =
  let eq (x1,m1) (x2,m2) = Sx.equal x1 x2 && Sm.equal m1 m2 in
  ur_equal eq mr1 mr2

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

let mr_fv (mr : mod_restr) : int Mid.t =
  fv_union
    (mr_xpaths_fv (mr_xpaths mr))
    (mr_mpaths_fv (mr_mpaths mr))

let mr_hash (mr : mod_restr) =
  Why3.Hashcons.combine
    (ur_hash EcPath.Sx.ntr_elements EcPath.x_hash (mr_xpaths mr))
    (ur_hash EcPath.Sm.ntr_elements EcPath.m_hash (mr_mpaths mr))

let mty_hash (mty : module_type) =
  Why3.Hashcons.combine2
    (EcPath.p_hash mty.mt_name)
    (Why3.Hashcons.combine_list
       (fun (x, _) -> EcIdent.id_hash x)
       0 mty.mt_params)
    (Why3.Hashcons.combine_list EcPath.m_hash 0 mty.mt_args)

let rec mty_equal (mty1 : module_type) (mty2 : module_type) =
     (EcPath.p_equal mty1.mt_name mty2.mt_name)
  && (List.all2 EcPath.m_equal mty1.mt_args mty2.mt_args)
  && (List.all2 (pair_equal EcIdent.id_equal mty_equal)
        mty1.mt_params mty2.mt_params)

let mty_fv (mty : module_type) =
  let fv =
    List.fold_left
      (fun fv mp -> m_fv fv mp)
      Mid.empty mty.mt_args in

  List.fold_left (fun fv (x, _) -> Mid.remove x fv) fv mty.mt_params

(* -------------------------------------------------------------------- *)
let mty_mr_equal ((mty1, mr1) : mty_mr) ((mty2, mr2) : mty_mr) =
  mty_equal mty1 mty2 && mr_equal mr1 mr2

let mty_mr_hash ((mty, mr) : mty_mr) =
  Why3.Hashcons.combine (mty_hash mty) (mr_hash mr)

let mty_mr_fv ((mty, mr) : mty_mr) =
  fv_union (mty_fv mty) (mr_fv mr)

(* -------------------------------------------------------------------- *)
let lmt_hash lmem =
  let el_hash (s,(i,ty)) =
    Why3.Hashcons.combine2
      (Hashtbl.hash s)
      i (ty_hash ty) in
  let lmt_proj_hash =
    Why3.Hashcons.combine_list el_hash 0 (Msym.bindings lmem.lmt_proj) in
  let lmt_name_hash = Why3.Hashcons.combine_option Hashtbl.hash lmem.lmt_name in
  let lmt_decl_hash = Why3.Hashcons.combine_list ov_hash 0 lmem.lmt_decl in
  Why3.Hashcons.combine_list
    (fun i -> i)
    (ty_hash lmem.lmt_ty)
    [ lmem.lmt_n;
      lmt_name_hash;
      lmt_decl_hash;
      lmt_proj_hash; ]

let mt_fv = function
  | Lmt_concrete None       -> EcIdent.Mid.empty
  | Lmt_concrete (Some lmt) ->
    List.fold_left (fun fv v ->
        EcIdent.fv_union fv v.ov_type.ty_fv
      ) EcIdent.Mid.empty lmt.lmt_decl

let lmt_equal ty_equal (mt1:local_memtype) (mt2:local_memtype) =
  mt1.lmt_name = mt2.lmt_name
  &&
    if mt1.lmt_name = None
    then
      Msym.equal (fun (_,ty1) (_,ty2) ->
          ty_equal ty1 ty2
        ) mt1.lmt_proj mt2.lmt_proj
    else
      List.all2 ov_equal mt1.lmt_decl mt2.lmt_decl

let mt_equal_gen ty_equal (Lmt_concrete mt1) (Lmt_concrete mt2) =
  oeq (lmt_equal ty_equal) mt1 mt2

let mt_equal = mt_equal_gen ty_equal

let me_hash (mem, Lmt_concrete mt) =
  Why3.Hashcons.combine
    (EcIdent.id_hash mem)
    (Why3.Hashcons.combine_option lmt_hash mt)

let mem_equal = EcIdent.id_equal

let me_equal_gen ty_equal (m1,mt1) (m2,mt2) =
  mem_equal m1 m2 && mt_equal_gen ty_equal mt1 mt2

let me_equal = me_equal_gen ty_equal

(*-------------------------------------------------------------------- *)
let gty_equal ty1 ty2 =
  match ty1, ty2 with
  | GTty ty1, GTty ty2 ->
      ty_equal ty1 ty2

  | GTmodty mtymr1, GTmodty mtymr2  ->
    mty_mr_equal mtymr1 mtymr2

  | GTmem mt1, GTmem mt2 ->
      mt_equal mt1 mt2

  | _ , _ -> false

let gty_hash = function
  | GTty ty -> ty_hash ty
  | GTmodty mtymr  ->  mty_mr_hash mtymr
  | GTmem _ -> 1

(* -------------------------------------------------------------------- *)
let gty_fv = function
  | GTty ty -> ty.ty_fv
  | GTmodty mtymr -> mty_mr_fv mtymr
  | GTmem mt -> mt_fv mt

(*-------------------------------------------------------------------- *)

let b_equal (b1 : bindings) (b2 : bindings) =
  let b1_equal (x1, ty1) (x2, ty2) =
    EcIdent.id_equal x1 x2 && gty_equal ty1 ty2
  in
    List.all2 b1_equal b1 b2

let b_hash (bs : bindings) =
  let b1_hash (x, ty) =
    Why3.Hashcons.combine (EcIdent.tag x) (gty_hash ty)
  in
    Why3.Hashcons.combine_list b1_hash 0 bs

(* -------------------------------------------------------------------- *)
let i_equal   = ((==) : instr -> instr -> bool)
let i_hash    = fun i -> i.i_tag
let i_fv i    = i.i_fv

let s_equal   = ((==) : stmt -> stmt -> bool)
let s_hash    = fun s -> s.s_tag
let s_fv      = fun s -> s.s_fv

(*-------------------------------------------------------------------- *)
let hf_equal hf1 hf2 =
     f_equal hf1.hf_pr hf2.hf_pr
  && f_equal hf1.hf_po hf2.hf_po
  && EcPath.x_equal hf1.hf_f hf2.hf_f

let hs_equal hs1 hs2 =
     f_equal hs1.hs_pr hs2.hs_pr
  && f_equal hs1.hs_po hs2.hs_po
  && s_equal hs1.hs_s hs2.hs_s
  && me_equal hs1.hs_m hs2.hs_m

let ehf_equal hf1 hf2 =
     f_equal hf1.ehf_pr  hf2.ehf_pr
  && f_equal hf1.ehf_po  hf2.ehf_po
  && EcPath.x_equal hf1.ehf_f hf2.ehf_f

let ehs_equal hs1 hs2 =
     f_equal hs1.ehs_pr  hs2.ehs_pr
  && f_equal hs1.ehs_po  hs2.ehs_po
  && s_equal hs1.ehs_s hs2.ehs_s
  && me_equal hs1.ehs_m hs2.ehs_m

let bhf_equal bhf1 bhf2 =
     f_equal bhf1.bhf_pr bhf2.bhf_pr
  && f_equal bhf1.bhf_po bhf2.bhf_po
  && EcPath.x_equal bhf1.bhf_f bhf2.bhf_f
  && bhf1.bhf_cmp = bhf2.bhf_cmp
  && f_equal bhf1.bhf_bd bhf2.bhf_bd

let bhs_equal bhs1 bhs2 =
     f_equal bhs1.bhs_pr bhs2.bhs_pr
  && f_equal bhs1.bhs_po bhs2.bhs_po
  && s_equal bhs1.bhs_s bhs2.bhs_s
  && me_equal bhs1.bhs_m bhs2.bhs_m
  && bhs1.bhs_cmp = bhs2.bhs_cmp
  && f_equal bhs1.bhs_bd bhs2.bhs_bd

let eqf_equal ef1 ef2 =
     f_equal ef1.ef_pr ef2.ef_pr
  && f_equal ef1.ef_po ef2.ef_po
  && EcPath.x_equal ef1.ef_fl ef2.ef_fl
  && EcPath.x_equal ef1.ef_fr ef2.ef_fr

let eqs_equal es1 es2 =
     f_equal es1.es_pr es2.es_pr
  && f_equal es1.es_po es2.es_po
  && s_equal es1.es_sl es2.es_sl
  && s_equal es1.es_sr es2.es_sr
  && me_equal es1.es_ml es2.es_ml
  && me_equal es1.es_mr es2.es_mr

let egf_equal eg1 eg2 =
     f_equal eg1.eg_pr eg2.eg_pr
  && f_equal eg1.eg_po eg2.eg_po
  && s_equal eg1.eg_sl eg2.eg_sl
  && EcPath.x_equal eg1.eg_fl eg2.eg_fl
  && EcPath.x_equal eg1.eg_fr eg2.eg_fr
  && s_equal eg1.eg_sr eg2.eg_sr

let pr_equal pr1 pr2 =
     EcIdent.id_equal pr1.pr_mem pr2.pr_mem
  && EcPath.x_equal   pr1.pr_fun pr2.pr_fun
  && f_equal          pr1.pr_event pr2.pr_event
  && f_equal          pr1.pr_args pr2.pr_args

(* -------------------------------------------------------------------- *)
let hf_hash hf =
  Why3.Hashcons.combine2
    (f_hash hf.hf_pr) (f_hash hf.hf_po) (EcPath.x_hash hf.hf_f)

let hs_hash hs =
  Why3.Hashcons.combine3
    (f_hash hs.hs_pr) (f_hash hs.hs_po)
    (s_hash hs.hs_s)
    (me_hash hs.hs_m)

let ehf_hash hf =
  Why3.Hashcons.combine2
    (f_hash hf.ehf_pr) (f_hash hf.ehf_po)
    (EcPath.x_hash hf.ehf_f)

let ehs_hash hs =
  Why3.Hashcons.combine3
    (f_hash hs.ehs_pr) (f_hash hs.ehs_po)
    (s_hash hs.ehs_s)
    (me_hash hs.ehs_m)

let bhf_hash bhf =
  Why3.Hashcons.combine_list f_hash
    (Why3.Hashcons.combine (hcmp_hash bhf.bhf_cmp) (EcPath.x_hash bhf.bhf_f))
    [bhf.bhf_pr;bhf.bhf_po;bhf.bhf_bd]

let bhs_hash bhs =
  Why3.Hashcons.combine_list f_hash
    (Why3.Hashcons.combine2
       (hcmp_hash bhs.bhs_cmp)
       (s_hash bhs.bhs_s)
       (me_hash bhs.bhs_m))
    [bhs.bhs_pr;bhs.bhs_po;bhs.bhs_bd]

let ef_hash ef =
  Why3.Hashcons.combine3
    (f_hash ef.ef_pr) (f_hash ef.ef_po)
    (EcPath.x_hash ef.ef_fl) (EcPath.x_hash ef.ef_fr)

let es_hash es =
  Why3.Hashcons.combine3
    (f_hash es.es_pr) (f_hash es.es_po)
    (s_hash es.es_sl)
    (Why3.Hashcons.combine2
       (me_hash es.es_mr)
       (me_hash es.es_ml)
       (s_hash es.es_sr))

let eg_hash eg =
  Why3.Hashcons.combine3
    (f_hash eg.eg_pr) (f_hash eg.eg_po)
    (Why3.Hashcons.combine (s_hash eg.eg_sl) (EcPath.x_hash eg.eg_fl))
    (Why3.Hashcons.combine (s_hash eg.eg_sr) (EcPath.x_hash eg.eg_fr))

let pr_hash pr =
  Why3.Hashcons.combine3
    (EcIdent.id_hash pr.pr_mem)
    (EcPath.x_hash   pr.pr_fun)
    (f_hash          pr.pr_args)
    (f_hash          pr.pr_event)


(* ----------------------------------------------------------------- *)
(* Hashconsing                                                       *)
(* ----------------------------------------------------------------- *)

module Hsty = Why3.Hashcons.Make (struct
  type t = ty

  let equal ty1 ty2 =
    match ty1.ty_node, ty2.ty_node with
    | Tglob m1, Tglob m2 ->
        EcIdent.id_equal m1 m2

    | Tunivar u1, Tunivar u2 ->
        uid_equal u1 u2

    | Tvar v1, Tvar v2 ->
        id_equal v1 v2

    | Ttuple lt1, Ttuple lt2 ->
        List.all2 ty_equal lt1 lt2

    | Tconstr (p1, lt1), Tconstr (p2, lt2) ->
        EcPath.p_equal p1 p2 && List.all2 ty_equal lt1 lt2

    | Tfun (d1, c1), Tfun (d2, c2)->
        ty_equal d1 d2 && ty_equal c1 c2

    | _, _ -> false

  let hash ty =
    match ty.ty_node with
    | Tglob m          -> EcIdent.id_hash m
    | Tunivar u        -> u
    | Tvar    id       -> EcIdent.tag id
    | Ttuple  tl       -> Why3.Hashcons.combine_list ty_hash 0 tl
    | Tconstr (p, tl)  -> Why3.Hashcons.combine_list ty_hash p.p_tag tl
    | Tfun    (t1, t2) -> Why3.Hashcons.combine (ty_hash t1) (ty_hash t2)

  let fv ty =
    let union ex =
      List.fold_left (fun s a -> fv_union s (ex a)) Mid.empty in

    match ty with
    | Tglob m          -> EcIdent.fv_add m Mid.empty
    | Tunivar _        -> Mid.empty
    | Tvar    _        -> Mid.empty (* FIXME: section *)
    | Ttuple  tys      -> union (fun a -> a.ty_fv) tys
    | Tconstr (_, tys) -> union (fun a -> a.ty_fv) tys
    | Tfun    (t1, t2) -> union (fun a -> a.ty_fv) [t1; t2]

  let tag n ty = { ty with ty_tag = n; ty_fv = fv ty.ty_node; }
end)

let mk_ty node =
  Hsty.hashcons { ty_node = node; ty_tag = -1; ty_fv = Mid.empty }

(* ----------------------------------------------------------------- *)

module Hexpr = Why3.Hashcons.Make (struct
  type t = expr

  let b_equal b1 b2 =
    let b1_equal (x1, ty1) (x2, ty2) =
      EcIdent.id_equal x1 x2 && ty_equal ty1 ty2 in
    List.all2 b1_equal b1 b2

  let equal_node e1 e2 =
    match e1, e2 with
    | Eint   i1, Eint   i2 -> BI.equal i1 i2
    | Elocal x1, Elocal x2 -> EcIdent.id_equal x1 x2
    | Evar   x1, Evar   x2 -> pv_equal x1 x2

    | Eop (p1, tys1), Eop (p2, tys2) ->
           (EcPath.p_equal p1 p2)
        && (List.all2 ty_equal tys1 tys2)

    | Eapp (e1, es1), Eapp (e2, es2) ->
           (e_equal e1 e2)
        && (List.all2 e_equal es1 es2)

    | Elet (lp1, e1, f1), Elet (lp2, e2, f2) ->
        (lp_equal lp1 lp2) && (e_equal e1 e2) && (e_equal f1 f2)

    | Etuple es1, Etuple es2 ->
        List.all2 e_equal es1 es2

    | Eif (c1, e1, f1), Eif (c2, e2, f2) ->
        (e_equal c1 c2) && (e_equal e1 e2) && (e_equal f1 f2)

    | Ematch (e1, es1, ty1), Ematch (e2, es2, ty2) ->
           List.all2 e_equal (e1 :: es1) (e2 :: es2)
        && ty_equal ty1 ty2

    | Equant (q1, b1, e1), Equant (q2, b2, e2) ->
        eqt_equal q1 q2 && e_equal e1 e2 && b_equal b1 b2

    | Eproj(e1, i1), Eproj(e2, i2) ->
        i1 = i2 && e_equal e1 e2

    | _, _ -> false

  let equal e1 e2 =
    equal_node e1.e_node e2.e_node &&
    ty_equal e1.e_ty e2.e_ty

  let b_hash bs =
    let b1_hash (x, ty) =
      Why3.Hashcons.combine (EcIdent.tag x) (ty_hash ty)
    in
    Why3.Hashcons.combine_list b1_hash 0 bs

  let hash e =
    match e.e_node with
    | Eint   i -> BI.hash i
    | Elocal x -> Hashtbl.hash x
    | Evar   x -> pv_hash x

    | Eop (p, tys) ->
        Why3.Hashcons.combine_list ty_hash
          (EcPath.p_hash p) tys

    | Eapp (e, es) ->
        Why3.Hashcons.combine_list e_hash (e_hash e) es

    | Elet (p, e1, e2) ->
        Why3.Hashcons.combine2
          (lp_hash p) (e_hash e1) (e_hash e2)

    | Etuple es ->
        Why3.Hashcons.combine_list e_hash 0 es

    | Eif (c, e1, e2) ->
        Why3.Hashcons.combine2
          (e_hash c) (e_hash e1) (e_hash e2)

    | Ematch (e, es, ty) ->
        Why3.Hashcons.combine_list e_hash
          (Why3.Hashcons.combine (e_hash e) (ty_hash ty))
          es

    | Equant (q, b, e) ->
        Why3.Hashcons.combine2 (eqt_hash q) (e_hash e) (b_hash b)

    | Eproj (e, i) ->
        Why3.Hashcons.combine (e_hash e) i

  let fv_node e =
    let union ex =
      List.fold_left (fun s e -> fv_union s (ex e)) Mid.empty
    in

    match e with
    | Eint _            -> Mid.empty
    | Eop (_, tys)      -> union (fun a -> a.ty_fv) tys
    | Evar v            -> pv_fv v
    | Elocal id         -> fv_singleton id
    | Eapp (e, es)      -> union e_fv (e :: es)
    | Elet (lp, e1, e2) -> fv_union (e_fv e1) (fv_diff (e_fv e2) (lp_fv lp))
    | Etuple es         -> union e_fv es
    | Eif (e1, e2, e3)  -> union e_fv [e1; e2; e3]
    | Ematch (e, es, _) -> union e_fv (e :: es)
    | Equant (_, b, e)  -> List.fold_left (fun s (id, _) -> Mid.remove id s) (e_fv e) b
    | Eproj (e, _)      -> e_fv e

  let tag n e =
    let fv = fv_union (fv_node e.e_node) e.e_ty.ty_fv in
      { e with e_tag = n; e_fv = fv; }
end)

(* -------------------------------------------------------------------- *)
let mk_expr e ty =
  Hexpr.hashcons { e_node = e; e_tag = -1; e_fv = Mid.empty; e_ty = ty }

(* -------------------------------------------------------------------- *)
let mhr    = EcIdent.create "&hr"
let mleft  = EcIdent.create "&1"
let mright = EcIdent.create "&2"

module Hsform = Why3.Hashcons.Make (struct
  type t = form

  let equal_node f1 f2 =
    match f1, f2 with
    | Fquant(q1,b1,f1), Fquant(q2,b2,f2) ->
        qt_equal q1 q2 && b_equal b1 b2 && f_equal f1 f2

    | Fif(b1,t1,f1), Fif(b2,t2,f2) ->
        f_equal b1 b2 && f_equal t1 t2 && f_equal f1 f2

    | Fmatch(b1,es1,ty1), Fmatch(b2,es2,ty2) ->
           List.all2 f_equal (b1::es1) (b2::es2)
        && ty_equal ty1 ty2

    | Flet(lp1,e1,f1), Flet(lp2,e2,f2) ->
        lp_equal lp1 lp2 && f_equal e1 e2 && f_equal f1 f2

    | Fint i1, Fint i2 ->
        BI.equal i1 i2

    | Flocal id1, Flocal id2 ->
        EcIdent.id_equal id1 id2

    | Fpvar(pv1,s1), Fpvar(pv2,s2) ->
        EcIdent.id_equal s1 s2 && pv_equal pv1 pv2

    | Fglob(mp1,m1), Fglob(mp2,m2) ->
      EcIdent.id_equal mp1 mp2 && EcIdent.id_equal m1 m2

    | Fop(p1,lty1), Fop(p2,lty2) ->
        EcPath.p_equal p1 p2 && List.all2 ty_equal lty1 lty2

    | Fapp(f1,args1), Fapp(f2,args2) ->
        f_equal f1 f2 && List.all2 f_equal args1 args2

    | Ftuple args1, Ftuple args2 ->
        List.all2 f_equal args1 args2

    | Fproj(f1,i1), Fproj(f2,i2) ->
      i1 = i2 && f_equal f1 f2

    | FhoareF  hf1 , FhoareF  hf2  -> hf_equal hf1 hf2
    | FhoareS  hs1 , FhoareS  hs2  -> hs_equal hs1 hs2
    | FeHoareF  hf1 , FeHoareF  hf2  -> ehf_equal hf1 hf2
    | FeHoareS  hs1 , FeHoareS  hs2  -> ehs_equal hs1 hs2
    | FbdHoareF   bhf1, FbdHoareF   bhf2 -> bhf_equal bhf1 bhf2
    | FbdHoareS   bhs1, FbdHoareS   bhs2 -> bhs_equal bhs1 bhs2
    | FequivF     eqf1, FequivF     eqf2 -> eqf_equal eqf1 eqf2
    | FequivS     eqs1, FequivS     eqs2 -> eqs_equal eqs1 eqs2
    | FeagerF     eg1 , FeagerF     eg2  -> egf_equal eg1 eg2
    | Fpr         pr1 , Fpr         pr2  -> pr_equal pr1 pr2

    | _, _ -> false

  let equal f1 f2 =
       ty_equal f1.f_ty f2.f_ty
    && equal_node f1.f_node f2.f_node

  let hash f =
    match f.f_node with
    | Fquant(q, b, f) ->
        Why3.Hashcons.combine2 (f_hash f) (b_hash b) (qt_hash q)

    | Fif(b, t, f) ->
        Why3.Hashcons.combine2 (f_hash b) (f_hash t) (f_hash f)

    | Fmatch (f, fs, ty) ->
        Why3.Hashcons.combine_list f_hash
          (Why3.Hashcons.combine (f_hash f) (ty_hash ty))
          fs

    | Flet(lp, e, f) ->
        Why3.Hashcons.combine2 (lp_hash lp) (f_hash e) (f_hash f)

    | Fint i -> Hashtbl.hash i

    | Flocal id -> EcIdent.tag id

    | Fpvar(pv, m) ->
        Why3.Hashcons.combine (pv_hash pv) (EcIdent.id_hash m)

    | Fglob(mp, m) ->
        Why3.Hashcons.combine (EcIdent.id_hash mp) (EcIdent.id_hash m)

    | Fop(p, lty) ->
        Why3.Hashcons.combine_list ty_hash (EcPath.p_hash p) lty

    | Fapp(f, args) ->
        Why3.Hashcons.combine_list f_hash (f_hash f) args

    | Ftuple args ->
        Why3.Hashcons.combine_list f_hash 0 args
    | Fproj(f,i) ->
        Why3.Hashcons.combine (f_hash f) i

    | FhoareF  hf   -> hf_hash hf
    | FhoareS  hs   -> hs_hash hs
    | FeHoareF  hf  -> ehf_hash hf
    | FeHoareS  hs  -> ehs_hash hs
    | FbdHoareF   bhf  -> bhf_hash bhf
    | FbdHoareS   bhs  -> bhs_hash bhs
    | FequivF     ef   -> ef_hash ef
    | FequivS     es   -> es_hash es
    | FeagerF     eg   -> eg_hash eg
    | Fpr         pr   -> pr_hash pr

  let fv_mlr = Sid.add mleft (Sid.singleton mright)

  let fv_node f =
    let union ex nodes =
      List.fold_left (fun s a -> fv_union s (ex a)) Mid.empty nodes
    in

    match f with
    | Fint _              -> Mid.empty
    | Fop (_, tys)        -> union (fun a -> a.ty_fv) tys
    | Fpvar (PVglob pv,m) -> EcPath.x_fv (fv_add m Mid.empty) pv
    | Fpvar (PVloc _,m)   -> fv_add m Mid.empty
    | Fglob (mp,m)        -> fv_add mp (fv_add m Mid.empty)
    | Flocal id           -> fv_singleton id
    | Fapp (f, args)      -> union f_fv (f :: args)
    | Ftuple args         -> union f_fv args
    | Fproj(e, _)         -> f_fv e
    | Fif (f1, f2, f3)    -> union f_fv [f1; f2; f3]
    | Fmatch (b, fs, ty)  -> fv_union ty.ty_fv (union f_fv (b :: fs))

    | Fquant(_, b, f) ->
      let do1 (id, ty) fv = fv_union (gty_fv ty) (Mid.remove id fv) in
      List.fold_right do1 b (f_fv f)

    | Flet(lp, f1, f2) ->
      let fv2 = fv_diff (f_fv f2) (lp_fv lp) in
      fv_union (f_fv f1) fv2

    | FhoareF hf ->
      let fv = fv_union (f_fv hf.hf_pr) (f_fv hf.hf_po) in
      EcPath.x_fv (Mid.remove mhr fv) hf.hf_f

    | FhoareS hs ->
      let fv = fv_union (f_fv hs.hs_pr) (f_fv hs.hs_po) in
      fv_union (s_fv hs.hs_s) (Mid.remove (fst hs.hs_m) fv)

    | FeHoareF hf ->
      let fv = fv_union (f_fv hf.ehf_pr) (f_fv hf.ehf_po) in
      EcPath.x_fv (Mid.remove mhr fv) hf.ehf_f

    | FeHoareS hs ->
      let fv = fv_union (f_fv hs.ehs_pr) (f_fv hs.ehs_po) in
      fv_union (s_fv hs.ehs_s) (Mid.remove (fst hs.ehs_m) fv)

    | FbdHoareF bhf ->
      let fv =
        fv_union (f_fv bhf.bhf_pr)
          (fv_union (f_fv bhf.bhf_po) (f_fv bhf.bhf_bd)) in
      EcPath.x_fv (Mid.remove mhr fv) bhf.bhf_f

    | FbdHoareS bhs ->
      let fv =
        fv_union (f_fv bhs.bhs_pr)
          (fv_union (f_fv bhs.bhs_po) (f_fv bhs.bhs_bd)) in
      fv_union (s_fv bhs.bhs_s) (Mid.remove (fst bhs.bhs_m) fv)

    | FequivF ef ->
        let fv = fv_union (f_fv ef.ef_pr) (f_fv ef.ef_po) in
        let fv = fv_diff fv fv_mlr in
        EcPath.x_fv (EcPath.x_fv fv ef.ef_fl) ef.ef_fr

    | FequivS es ->
        let fv = fv_union (f_fv es.es_pr) (f_fv es.es_po) in
        let ml, mr = fst es.es_ml, fst es.es_mr in
        let fv = fv_diff fv (Sid.add ml (Sid.singleton mr)) in
        fv_union fv
          (fv_union (s_fv es.es_sl) (s_fv es.es_sr))

    | FeagerF eg ->
        let fv = fv_union (f_fv eg.eg_pr) (f_fv eg.eg_po) in
        let fv = fv_diff fv fv_mlr in
        let fv = EcPath.x_fv (EcPath.x_fv fv eg.eg_fl) eg.eg_fr in
        fv_union fv
          (fv_union (s_fv eg.eg_sl) (s_fv eg.eg_sr))

    | Fpr pr ->
        let fve = Mid.remove mhr (f_fv pr.pr_event) in
        let fv  = EcPath.x_fv fve pr.pr_fun in
        fv_union (f_fv pr.pr_args) (fv_add pr.pr_mem fv)

  let tag n f =
    let fv = fv_union (fv_node f.f_node) f.f_ty.ty_fv in
      { f with f_tag = n; f_fv = fv; }
end)

let mk_form node ty =
  let aout =
    Hsform.hashcons
      { f_node = node;
        f_ty   = ty;
        f_fv   = Mid.empty;
        f_tag  = -1; }
  in assert (ty_equal ty aout.f_ty); aout

(* -------------------------------------------------------------------- *)
module Hinstr = Why3.Hashcons.Make (struct
  type t = instr

  let equal_node i1 i2 =
    match i1, i2 with
    | Sasgn (lv1, e1), Sasgn (lv2, e2) ->
        (lv_equal lv1 lv2) && (e_equal e1 e2)

    | Srnd (lv1, e1), Srnd (lv2, e2) ->
        (lv_equal lv1 lv2) && (e_equal e1 e2)

    | Scall (lv1, f1, es1), Scall (lv2, f2, es2) ->
           (EcUtils.opt_equal lv_equal lv1 lv2)
        && (EcPath.x_equal f1 f2)
        && (List.all2 e_equal es1 es2)

    | Sif (c1, s1, r1), Sif (c2, s2, r2) ->
           (e_equal c1 c2)
        && (s_equal s1 s2)
        && (s_equal r1 r2)

    | Swhile (c1, s1), Swhile (c2, s2) ->
           (e_equal c1 c2)
        && (s_equal s1 s2)

    | Smatch (e1, b1), Smatch (e2, b2) when List.length b1 = List.length b2 ->
        let forb (bs1, s1) (bs2, s2) =
          let forbs (x1, ty1) (x2, ty2) =
               EcIdent.id_equal x1  x2
            && ty_equal ty1 ty2
          in List.all2 forbs bs1 bs2 && s_equal s1 s2
        in e_equal e1 e2 && List.all2 forb b1 b2

    | Sassert e1, Sassert e2 ->
        (e_equal e1 e2)

    | Sabstract id1, Sabstract id2 -> EcIdent.id_equal id1 id2

    | _, _ -> false

  let equal i1 i2 = equal_node i1.i_node i2.i_node

  let hash p =
    match p.i_node with
    | Sasgn (lv, e) ->
        Why3.Hashcons.combine
          (lv_hash lv) (e_hash e)

    | Srnd (lv, e) ->
        Why3.Hashcons.combine
          (lv_hash lv) (e_hash e)

    | Scall (lv, f, tys) ->
        Why3.Hashcons.combine_list e_hash
          (Why3.Hashcons.combine
             (omap_dfl lv_hash 0 lv) (EcPath.x_hash f))
          tys

    | Sif (c, s1, s2) ->
        Why3.Hashcons.combine2
          (e_hash c) (s_hash s1) (s_hash s2)

    | Swhile (c, s) ->
        Why3.Hashcons.combine (e_hash c) (s_hash s)

    | Smatch (e, b) ->
        let forb (bds, s) =
          let forbs (x, ty) =
            Why3.Hashcons.combine (EcIdent.id_hash x) (ty_hash ty)
          in Why3.Hashcons.combine_list forbs (s_hash s) bds
        in Why3.Hashcons.combine_list forb (e_hash e) b

    | Sassert e -> e_hash e

    | Sabstract id -> EcIdent.id_hash id

  let i_fv   = function
    | Sasgn (lv, e) ->
        EcIdent.fv_union (lv_fv lv) (e_fv e)

    | Srnd (lv, e) ->
        EcIdent.fv_union (lv_fv lv) (e_fv e)

    | Scall (olv, f, args) ->
        let ffv = EcPath.x_fv Mid.empty f in
        let ofv = olv |> omap lv_fv |> odfl Mid.empty in
        List.fold_left
          (fun s a -> EcIdent.fv_union s (e_fv a))
          (EcIdent.fv_union ffv ofv) args

    | Sif (e, s1, s2) ->
        List.fold_left EcIdent.fv_union Mid.empty
          [e_fv e; s_fv s1; s_fv s2]

    | Swhile (e, s)  ->
        EcIdent.fv_union (e_fv e) (s_fv s)

    | Smatch (e, b) ->
        let forb (bs, s) =
          let bs = Sid.of_list (List.map fst bs) in
          EcIdent.fv_diff (s_fv s) bs

        in List.fold_left
             (fun s b -> EcIdent.fv_union s (forb b))
             (e_fv e) b

    | Sassert e    ->
        e_fv e

    | Sabstract id ->
        EcIdent.fv_singleton id

  let tag n p = { p with i_tag = n; i_fv = i_fv p.i_node }
end)

let mk_instr i = Hinstr.hashcons
  { i_node = i; i_tag = -1; i_fv = Mid.empty }

(* -------------------------------------------------------------------- *)
module Hstmt = Why3.Hashcons.Make (struct
  type t = stmt

  let equal_node s1 s2 =
    List.all2 i_equal s1 s2

  let equal s1 s2 = equal_node s1.s_node s2.s_node

  let hash p =
    Why3.Hashcons.combine_list i_hash 0 p.s_node

  let tag n p =
    let fv =
      List.fold_left
        (fun s i -> EcIdent.fv_union s (i_fv i))
        Mid.empty p.s_node
    in { p with s_tag = n; s_fv = fv; }
end)

let stmt s = Hstmt.hashcons
  { s_node = s; s_tag = -1; s_fv = Mid.empty}
