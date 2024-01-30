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

type ty = {
  ty_node : ty_node;
  ty_fv   : int Mid.t; (* only ident appearing in path *)
  ty_tag  : int;
}

and ty_node =
  | Tmem    of memtype
  | Tunivar of EcUid.uid
  | Tvar    of EcIdent.t
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

(* -------------------------------------------------------------------- *)
(* lmt_symb :
   A map associating to a symbol is type
   furthermore for function argument we also associate the projection
   with respect to arg
   proc f (x1:t1, _: t2)
   lmt_symb[x1] -> (arg, t1*t2, Some 0), t1
   Particular case when the procedure has only one argument:
   proc f (x1:t1)
   lmt_symb[x1] -> (arg, t1, None), t1

   lmt_proj :
   It is the inverse map of lmt_symb, it is used for printing

   We can look in EcMemory for a better understanding
*)

and proj_tbl =
  | Ptbl_direct of EcSymbols.symbol
  | Ptbl_proj   of EcSymbols.symbol EcMaps.Mint.t

and local_memtype = {
  lmt_symb : ((EcSymbols.symbol * ty * int option) option * ty) Msym.t;
  lmt_proj : proj_tbl Msym.t;
  lmt_fv   : int EcIdent.Mid.t;
  lmt_tag  : int;
}

(* The type of memory restricted to a gvar_set *)
(* [lmt = None] is for an axiom schema, and is instantiated to a concrete
   memory type when the axiom schema is.  *)
and memtype = {
  mt_lmt : local_memtype option;
  mt_gvs : gvar_set;
  mt_fv  : int Mid.t;
  mt_tag : int;
}

and memenv = memory * memtype

(* -------------------------------------------------------------------- *)
and functor_fun = {
  ff_params : (EcIdent.t * module_type) list;
  ff_xp     : xpath;  (* The xpath is fully applied *)
  ff_fv     : int Mid.t;
  ff_tag    : int;
}

and gvar_set_node =
  | Empty                              (* The empty memory                           *)
  | All                                (* The memory of All global                   *)
  | Set       of Sx.t                  (* The memory restricted to the variable in s *)
  | GlobFun   of functor_fun           (* The global memory used by the function     *)
  | Union     of gvar_set * gvar_set   (* Union                                      *)
  | Diff      of gvar_set * gvar_set   (* Difference                                 *)
  | Inter     of gvar_set * gvar_set   (* Intersection                               *)

and gvar_set = {
  gvs_node : gvar_set_node;
  gvs_tag  : int;
  gvs_fv   : int EcIdent.Mid.t;
}

and var_set = {
  lvs : Ssym.t;
  gvs : gvar_set;
  vs_tag : int;
}

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
  oi_costs : (form * form Mx.t) option;
  oi_fv    : int Mid.t;
  oi_tag   : int;
}

and module_type = {
  mt_restr  : gvar_set;  (* The set of allowed global variables *)
  (* params are unbound in restr *)
  mt_params : (EcIdent.t * module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
  mt_oi     : oracle_info Msym.t;
  mty_fv    : int Mid.t;
  mty_tag   : int;
}


(* -------------------------------------------------------------------- *)
and gty =
  | GTty    of ty
  | GTmodty of module_type

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

  | Fpvar   of prog_var * form        (* x{m} *)
  | Fmrestr of form * memtype         (* (m|X) *)
  | Fupdvar of form * prog_var * form (* m[x<-v] *)
  | Fupdmem of form * var_set * form  (* m[X<- m'] *)

  | Fop     of EcPath.path * ty list
  | Fapp    of form * form list
  | Ftuple  of form list
  | Fproj   of form * int

  | FhoareF of sHoareF (* $hr / $hr *)
  | FhoareS of sHoareS

  | FcHoareF of cHoareF (* $hr / $hr *)
  | FcHoareS of cHoareS

  | FbdHoareF of bdHoareF (* $hr / $hr *)
  | FbdHoareS of bdHoareS

  | FeHoareF of eHoareF (* $hr / $hr *)
  | FeHoareS of eHoareS

  | FequivF of equivF (* $left,$right / $left,$right *)
  | FequivS of equivS

  | FeagerF of eagerF

  | Fcoe of coe

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

and cHoareF = {
  chf_pr : form;
  chf_f  : EcPath.xpath;
  chf_po : form;
  chf_co : cost;
}

and cHoareS = {
  chs_m  : memenv;
  chs_pr : form;
  chs_s  : stmt;
  chs_po : form;
  chs_co : cost; }

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
  pr_mem   : form;
  pr_fun   : EcPath.xpath;
  pr_args  : form;
  pr_event : form;
}

and coe = {
  coe_pre : form;
  coe_mem : memenv;
  coe_e   : expr;
}

(* Invariant: keys of c_calls are functions of local modules,
   with no arguments. *)
and cost = {
  c_self  : form;    (* of type xint *)
  c_calls : call_bound EcPath.Mx.t;
}

(* Call with cost at most [cb_cost], called at mist [cb_called].
   [cb_cost] is here to properly handle substsitution when instantiating an
   abstract module by a concrete one. *)
and call_bound = {
  cb_cost  : form;   (* of type xint *)
  cb_called : form;  (* of type int  *)
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
let oi_equal : oracle_info -> oracle_info -> bool = (==)
let oi_hash oi = oi.oi_tag
let oi_fv oi = oi.oi_fv

(* -------------------------------------------------------------------- *)
let mty_equal : module_type -> module_type -> bool = (==)
let mty_hash mty = mty.mty_tag
let mty_fv mty = mty.mty_fv

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

(* ----------------------------------------------------------------- *)
let ff_equal : functor_fun -> functor_fun -> bool = (==)
let ff_hash ff = ff.ff_tag
let ff_fv ff = ff.ff_fv

(*-------------------------------------------------------------------- *)
let gvs_equal : gvar_set -> gvar_set -> bool = (==)
let gvs_hash gvs = gvs.gvs_tag
let gvs_fv gvs = gvs.gvs_fv

(*-------------------------------------------------------------------- *)
let vs_equal : var_set -> var_set -> bool = (==)
let vs_hash vs = vs.vs_tag
let vs_fv vs = vs.gvs.gvs_fv

(* -------------------------------------------------------------------- *)
let lmt_equal : local_memtype -> local_memtype -> bool = (==)
let lmt_hash lmt = lmt.lmt_tag
let lmt_fv lmt   = lmt.lmt_fv


(* -------------------------------------------------------------------- *)
let mt_equal : memtype -> memtype -> bool = (==)
let mt_hash mt = mt.mt_tag
let mt_fv mt = mt.mt_fv

let is_schema mt = mt.mt_lmt = None
(* -------------------------------------------------------------------- *)
let mem_equal = EcIdent.id_equal

let me_equal  (m1,mt1) (m2,mt2) =
  mem_equal m1 m2 && mt_equal mt1 mt2

let me_hash (mem,mt) = Why3.Hashcons.combine (EcIdent.id_hash mem) (mt_hash mt)


(*-------------------------------------------------------------------- *)
let gty_equal ty1 ty2 =
  match ty1, ty2 with
  | GTty ty1, GTty ty2 ->
      ty_equal ty1 ty2

  | GTmodty p1, GTmodty p2  ->
    mty_equal p1 p2

  | _ , _ -> false

let gty_hash = function
  | GTty ty -> ty_hash ty
  | GTmodty p  ->  mty_hash p

let gty_fv = function
  | GTty ty -> ty.ty_fv
  | GTmodty mty -> mty_fv mty

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
let call_bound_equal cb1 cb2 =
     f_equal cb1.cb_cost cb2.cb_cost
  && f_equal cb1.cb_called cb2.cb_called

let cost_equal c1 c2 =
     f_equal c1.c_self c2.c_self
  && EcPath.Mx.equal call_bound_equal c1.c_calls c2.c_calls

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

let chf_equal chf1 chf2 =
     f_equal chf1.chf_pr chf2.chf_pr
  && f_equal chf1.chf_po chf2.chf_po
  && cost_equal chf1.chf_co chf2.chf_co
  && EcPath.x_equal chf1.chf_f chf2.chf_f

let chs_equal chs1 chs2 =
     f_equal chs1.chs_pr chs2.chs_pr
  && f_equal chs1.chs_po chs2.chs_po
  && cost_equal chs1.chs_co chs2.chs_co
  && s_equal chs1.chs_s chs2.chs_s
  && me_equal chs1.chs_m chs2.chs_m

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

let coe_equal coe1 coe2 =
     e_equal   coe1.coe_e coe2.coe_e
  && f_equal           coe1.coe_pre coe2.coe_pre
  && me_equal coe1.coe_mem coe2.coe_mem

let pr_equal pr1 pr2 =
     f_equal pr1.pr_mem pr2.pr_mem
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

let coe_hash coe =
  Why3.Hashcons.combine2
    (f_hash coe.coe_pre)
    (e_hash coe.coe_e)
    (me_hash coe.coe_mem)

let call_bound_hash cb =
  Why3.Hashcons.combine
    (f_hash cb.cb_cost)
    (f_hash cb.cb_called)

let cost_hash cost =
  Why3.Hashcons.combine
    (f_hash cost.c_self)
    (Why3.Hashcons.combine_list
       (fun (f,c) ->
          Why3.Hashcons.combine
            (EcPath.x_hash f)
            (call_bound_hash c))
       0 (EcPath.Mx.bindings cost.c_calls))

let chf_hash chf =
  Why3.Hashcons.combine3
    (f_hash chf.chf_pr)
    (f_hash chf.chf_po)
    (cost_hash chf.chf_co)
    (EcPath.x_hash chf.chf_f)

let chs_hash chs =
  Why3.Hashcons.combine3
    (f_hash chs.chs_pr)
    (f_hash chs.chs_po)
    (cost_hash chs.chs_co)
    (Why3.Hashcons.combine
       (s_hash chs.chs_s)
       (me_hash chs.chs_m))


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
    (f_hash pr.pr_mem)
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
    | Tmem mt1, Tmem mt2 ->
        mt_equal mt1 mt2

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
    | Tmem mt          -> mt_hash mt
    | Tunivar u        -> u
    | Tvar    id       -> EcIdent.tag id
    | Ttuple  tl       -> Why3.Hashcons.combine_list ty_hash 0 tl
    | Tconstr (p, tl)  -> Why3.Hashcons.combine_list ty_hash p.p_tag tl
    | Tfun    (t1, t2) -> Why3.Hashcons.combine (ty_hash t1) (ty_hash t2)

  let fv ty =
    let union ex =
      List.fold_left (fun s a -> fv_union s (ex a)) Mid.empty in

    match ty with
    | Tmem mt          -> mt.mt_fv
    | Tunivar _        -> Mid.empty
    | Tvar    _        -> Mid.empty (* FIXME: section *)
    | Ttuple  tys      -> union (fun a -> a.ty_fv) tys
    | Tconstr (_, tys) -> union (fun a -> a.ty_fv) tys
    | Tfun    (t1, t2) -> union (fun a -> a.ty_fv) [t1; t2]

  let tag n ty = { ty with ty_tag = n; ty_fv = fv ty.ty_node; }
end)

let mk_ty node =
  Hsty.hashcons { ty_node = node; ty_tag = -1; ty_fv = Mid.empty }

module Hslmt = Why3.Hashcons.Make (struct

  type t = local_memtype

  let equal (lmt1:local_memtype) (lmt2:local_memtype) =
    Msym.equal
       (fun (o1, ty1) (o2, ty2) ->
         ty_equal ty1 ty2 &&
         opt_equal (fun (s1,ty1,i1) (s2,ty2, i2) ->
             i1 = i2 && ty_equal ty1 ty2 && sym_equal s1 s2) o1 o2)
       lmt1.lmt_symb lmt2.lmt_symb

  let hash lmt =
    Msym.fold
      (fun s (_,ty) hash -> Why3.Hashcons.combine2 (Hashtbl.hash s) (ty_hash ty) hash)
      lmt.lmt_symb 0

  let fv lmt =
    (* Remark no need to take the type in the first componant since the variable is declared *)
    Msym.fold (fun _ (_, ty) fv -> fv_union fv (ty.ty_fv))
      lmt.lmt_symb Mid.empty

  let tag n lmt =
    { lmt with
      lmt_tag = n; lmt_fv = fv lmt }
end)

let mk_lmt lmt_symb lmt_proj =
  Hslmt.hashcons { lmt_symb; lmt_proj; lmt_fv = Mid.empty; lmt_tag = -1 }

(* ----------------------------------------------------------------- *)
module Hsoi = Why3.Hashcons.Make(struct
  type t = oracle_info

  let equal oi1 oi2 =
    List.equal x_equal oi1.oi_calls oi2.oi_calls &&
    opt_equal (fun (c1,m1) (c2,m2) ->
        f_equal c1 c2 && Mx.equal f_equal m1 m2) oi1.oi_costs oi2.oi_costs

  let hash oi =
    let doit (c,m) =
      Mx.fold (fun x f h -> Why3.Hashcons.combine2 (x_hash x) (f_hash f) h)
        m (f_hash c) in
    Why3.Hashcons.combine_list x_hash (ohash doit oi.oi_costs) oi.oi_calls

  let fv oi =
    let doit (c,m) =
      Mx.fold (fun x f fv -> fv_union (x_fv fv x) (f_fv f)) m (f_fv c) in
    List.fold_left x_fv (omap_dfl doit Mid.empty oi.oi_costs) oi.oi_calls

  let tag n oi =
    { oi with oi_tag = n; oi_fv = fv oi }
end)

let mk_oi oi_calls oi_costs =
  Hsoi.hashcons { oi_calls; oi_costs; oi_fv = Mid.empty; oi_tag = -1 }

(* ----------------------------------------------------------------- *)
(*
module Hsmr = Why3.Hashcons.Make (struct

  type t = mod_restr

  let equal mr1 mr2 =
    gvs_equal mr1.mr_mem mr2.mr_mem &&
    Msym.equal oi_equal mr1.mr_oinfos mr2.mr_oinfos

  let hash mr =
    Msym.fold (fun _ oi h -> Why3.Hashcons.combine (oi_hash oi) h)
      mr.mr_oinfos (gvs_hash mr.mr_mem)

  let fv mr =
    Msym.fold (fun _ oi fv -> fv_union (oi_fv oi) fv)
      mr.mr_oinfos (gvs_fv mr.mr_mem)

  let tag n mr = { mr with mr_tag = n; mr_fv = fv mr }
end)

let mk_mr mr_mem mr_oinfos =
  Hsmr.hashcons { mr_mem; mr_oinfos; mr_fv = Mid.empty; mr_tag = -1 }
*)
(* ----------------------------------------------------------------- *)
module Hsmty = Why3.Hashcons.Make (struct

  type t = module_type

  let equal mty1 mty2 =
    gvs_equal mty1.mt_restr mty2.mt_restr &&
    p_equal mty1.mt_name mty2.mt_name &&
    List.equal
      (fun (id1,mt1) (id2,mt2) -> id_equal id1 id2 && mty_equal mt1 mt2)
      mty1.mt_params mty2.mt_params &&
    List.equal m_equal mty1.mt_args mty2.mt_args &&
    Msym.equal oi_equal mty1.mt_oi mty2.mt_oi

  let hash mty =
    let h =
      Why3.Hashcons.combine_list
        (fun (id,mt) -> Why3.Hashcons.combine (id_hash id) (mty_hash mt))
        (p_hash mty.mt_name) mty.mt_params in
    let h =
      Why3.Hashcons.combine_list m_hash h mty.mt_args in
    let h =
      Msym.fold
        (fun _ oi h -> Why3.Hashcons.combine (oi_hash oi) h)
        mty.mt_oi h
    in
    Why3.Hashcons.combine (gvs_hash mty.mt_restr) h

  let fv mty =
    let fv =
      Msym.fold (fun _ oi fv -> fv_union (oi_fv oi) fv)
        mty.mt_oi Mid.empty in
    let fv =
      List.fold_left m_fv fv mty.mt_args in
    let fv =
      List.fold_right (fun (id, mty) fv ->
       fv_union (mty_fv mty) (Mid.remove id fv)) mty.mt_params fv in
    fv_union (gvs_fv mty.mt_restr) fv

  let tag n mty =
    { mty with mty_tag = n; mty_fv = fv mty }
end)

let mk_mty mt_restr mt_params mt_name mt_args mt_oi =
  Hsmty.hashcons
    { mt_restr; mt_params; mt_name; mt_args; mt_oi;
      mty_fv = Mid.empty; mty_tag = -1 }

(* ----------------------------------------------------------------- *)
module Hsmt = Why3.Hashcons.Make (struct

  type t = memtype

  let equal mt1 mt2 =
    opt_equal lmt_equal mt1.mt_lmt mt2.mt_lmt && gvs_equal mt1.mt_gvs mt2.mt_gvs

  let hash mt =
    Why3.Hashcons.combine (ohash lmt_hash mt.mt_lmt) (gvs_hash mt.mt_gvs)

  let tag n mt =
    { mt with
      mt_tag = n; mt_fv = fv_union (omap_dfl lmt_fv Mid.empty mt.mt_lmt) (gvs_fv mt.mt_gvs) }
end)

let mk_mt mt_lmt mt_gvs =
  Hsmt.hashcons { mt_lmt; mt_gvs; mt_fv = Mid.empty; mt_tag = -1 }

(* ----------------------------------------------------------------- *)
module Hsff = Why3.Hashcons.Make (struct
  type t = functor_fun

  let equal ff1 ff2 =
    List.equal (fun (id1,mty1) (id2,mty2) -> id_equal id1 id2 && mty_equal mty1 mty2)
       ff1.ff_params ff2.ff_params &&
    x_equal ff1.ff_xp ff2.ff_xp

  let hash ff =
    Why3.Hashcons.combine_list
      (fun (id, mty) -> Why3.Hashcons.combine (id_hash id) (mty_hash mty))
      (x_hash ff.ff_xp) ff.ff_params

  let fv ff =
    List.fold_right (fun (id, mty) fv ->
       fv_union (mty_fv mty) ( Mid.remove id fv)) ff.ff_params
           (x_fv Mid.empty ff.ff_xp)

  let tag n ff =
    { ff with ff_tag = n; ff_fv = fv ff }

end)

let mk_ff ff_params ff_xp =
  Hsff.hashcons {ff_params; ff_xp; ff_fv = Mid.empty; ff_tag = -1 }

(* ----------------------------------------------------------------- *)
module Hsgvs = Why3.Hashcons.Make (struct

  type t = gvar_set

  let equal gvs1 gvs2 =
    match gvs1.gvs_node, gvs2.gvs_node with
    | Empty, Empty -> true
    | All  , All   -> true
    | Set x, Set y -> Sx.equal x y
    | GlobFun f1, GlobFun f2 -> ff_equal f1 f2
    | Union(s11,s12), Union(s21,s22)
    | Diff (s11,s12), Diff (s21,s22)
    | Inter(s11,s12), Inter(s21,s22) -> gvs_equal s11 s21 && gvs_equal s12 s22
    | _, _ -> false

  let hash gvs =
    match gvs.gvs_node with
    | Empty        -> 0
    | All          -> 1
    | Set s        -> Sx.fold (fun x h -> Why3.Hashcons.combine (x_hash x) h) s 2
    | GlobFun f    -> ff_hash f
    | Union(s1,s2) -> Why3.Hashcons.combine_list gvs_hash 3 [s1; s2]
    | Diff (s1,s2) -> Why3.Hashcons.combine_list gvs_hash 4 [s1; s2]
    | Inter(s1,s2) -> Why3.Hashcons.combine_list gvs_hash 5 [s1; s2]

  let fv gvs =
    match gvs with
    | Empty | All  -> Mid.empty
    | Set _        -> Mid.empty (* global variable path has not ident *)
    | GlobFun f    -> ff_fv f
    | Union(s1,s2) | Diff (s1,s2) | Inter(s1,s2) ->
        fv_union (gvs_fv s1) (gvs_fv s2)

  let tag n gvs = { gvs with gvs_tag = n; gvs_fv = fv gvs.gvs_node; }

end)

let mk_gvs gvs_node =
  Hsgvs.hashcons { gvs_node; gvs_fv = Mid.empty; gvs_tag = -1 }

(* ----------------------------------------------------------------- *)
module Hsvs = Why3.Hashcons.Make (struct

 type t = var_set

  let equal vs1 vs2 =
    Ssym.equal vs1.lvs vs2.lvs &&
    gvs_equal vs1.gvs vs2.gvs

  let hash vs =
    Why3.Hashcons.combine (gvs_hash vs.gvs) (Hashtbl.hash vs.lvs)

  let tag n vs = { vs with vs_tag = n; }

end)

let mk_vs lvs gvs =
  Hsvs.hashcons { lvs; gvs; vs_tag = -1 }

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

let mk_expr e ty =
  Hexpr.hashcons { e_node = e; e_tag = -1; e_fv = Mid.empty; e_ty = ty }

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
        f_equal s1 s2 && pv_equal pv1 pv2

    | Fmrestr(m1, mt1), Fmrestr(m2, mt2) ->
        f_equal m1 m2 && mt_equal mt1 mt2

    | Fupdvar(m1, x1, f1), Fupdvar(m2, x2, f2)  ->
        f_equal m1 m2 && f_equal f1 f2 && pv_equal x1 x2

    | Fupdmem(m1, s1, m1'), Fupdmem(m2, s2, m2')  ->
        f_equal m1 m2 && f_equal m1' m2' && vs_equal s1 s2

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
    | FcHoareF hf1 , FcHoareF hf2  -> chf_equal hf1 hf2
    | FcHoareS hs1 , FcHoareS hs2  -> chs_equal hs1 hs2
    | FeHoareF  hf1 , FeHoareF  hf2  -> ehf_equal hf1 hf2
    | FeHoareS  hs1 , FeHoareS  hs2  -> ehs_equal hs1 hs2
    | FbdHoareF   bhf1, FbdHoareF   bhf2 -> bhf_equal bhf1 bhf2
    | FbdHoareS   bhs1, FbdHoareS   bhs2 -> bhs_equal bhs1 bhs2
    | FequivF     eqf1, FequivF     eqf2 -> eqf_equal eqf1 eqf2
    | FequivS     eqs1, FequivS     eqs2 -> eqs_equal eqs1 eqs2
    | FeagerF     eg1 , FeagerF     eg2  -> egf_equal eg1 eg2
    | Fpr         pr1 , Fpr         pr2  -> pr_equal pr1 pr2
    | Fcoe        coe1, Fcoe        coe2 -> coe_equal coe1 coe2

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
        Why3.Hashcons.combine (pv_hash pv) (f_hash m)

    | Fmrestr(m,mt) ->
        Why3.Hashcons.combine (f_hash m) (mt_hash mt)

    | Fupdvar(m,x,v) ->
        Why3.Hashcons.combine2 (f_hash m) (pv_hash x) (f_hash v)

    | Fupdmem(m,s,m') ->
        Why3.Hashcons.combine2 (f_hash m) (vs_hash s) (f_hash m')

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
    | FcHoareF chf  -> chf_hash chf
    | FcHoareS chs  -> chs_hash chs
    | FeHoareF  hf  -> ehf_hash hf
    | FeHoareS  hs  -> ehs_hash hs
    | FbdHoareF   bhf  -> bhf_hash bhf
    | FbdHoareS   bhs  -> bhs_hash bhs
    | FequivF     ef   -> ef_hash ef
    | FequivS     es   -> es_hash es
    | FeagerF     eg   -> eg_hash eg
    | Fcoe        coe  -> coe_hash coe
    | Fpr         pr   -> pr_hash pr

  let fv_mlr = Sid.add mleft (Sid.singleton mright)

  let cost_fv cost =
    let self_fv = f_fv cost.c_self in
    EcPath.Mx.fold (fun f c fv ->
        let c_fv =
          fv_union
            (fv_union (f_fv c.cb_cost) fv)
            (f_fv c.cb_called) in
        EcPath.x_fv c_fv f
      ) cost.c_calls self_fv

  let fv_node f =
    let union ex nodes =
      List.fold_left (fun s a -> fv_union s (ex a)) Mid.empty nodes
    in

    match f with
    | Fint _              -> Mid.empty
    | Fop (_, tys)        -> union (fun a -> a.ty_fv) tys

    | Fpvar (x,m)         -> fv_union (f_fv m) (pv_fv x)
    | Fmrestr(m,mt)        -> fv_union (f_fv m) (mt_fv mt)
    | Fupdvar(m,x,v)      -> fv_union (f_fv m) (fv_union (pv_fv x) (f_fv v))
    | Fupdmem(m,s,m')     -> fv_union (f_fv m) (fv_union (vs_fv s) (f_fv m'))

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

    | FcHoareF chf ->
      let fv = fv_union (f_fv chf.chf_pr)
          (fv_union (f_fv chf.chf_po) (cost_fv chf.chf_co)) in
      EcPath.x_fv (Mid.remove mhr fv) chf.chf_f

    | FcHoareS chs ->
      let fv = fv_union (f_fv chs.chs_pr)
          (fv_union (f_fv chs.chs_po) (cost_fv chs.chs_co)) in
      fv_union (s_fv chs.chs_s) (Mid.remove (fst chs.chs_m) fv)

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

    | Fcoe coe ->
      fv_union
        (Mid.remove (fst coe.coe_mem) (f_fv coe.coe_pre))
        (e_fv coe.coe_e)

    | Fpr pr ->
        let fve = Mid.remove mhr (f_fv pr.pr_event) in
        let fv  = EcPath.x_fv fve pr.pr_fun in
        fv_union (f_fv pr.pr_args) (fv_union (f_fv pr.pr_mem) fv)

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
