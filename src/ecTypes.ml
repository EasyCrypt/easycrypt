(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcPath
open EcAst

module BI = EcBigInt

(* -------------------------------------------------------------------- *)
type locality  = [`Local | `Declare | `Global]
type is_local  = [`Local | `Global]

let local_of_locality = function
  | `Local   -> `Local
  | `Global  -> `Global
  | `Declare -> `Local

(* -------------------------------------------------------------------- *)
type ty = EcAst.ty
type ty_node = EcAst.ty_node

type dom = ty list

let ty_equal = EcAst.ty_equal
let ty_hash = EcAst.ty_hash

let mk_ty = EcAst.mk_ty

module MSHty = EcMaps.MakeMSH(struct
  type t = ty
  let tag t = t.ty_tag
end)

module Mty = MSHty.M
module Sty = MSHty.S
module Hty = MSHty.H

(* -------------------------------------------------------------------- *)
let rec dump_ty ty =
  match ty.ty_node with
  | Tglob p ->
      EcIdent.tostring p

  | Tunivar i ->
      Printf.sprintf "#%d" i

  | Tvar id ->
      EcIdent.tostring id

  | Ttuple tys ->
      Printf.sprintf "(%s)" (String.concat ", " (List.map dump_ty tys))

  | Tconstr (p, tys) ->
      Printf.sprintf "%s[%s]" (EcPath.tostring p)
        (String.concat ", " (List.map dump_ty tys))

  | Tfun (t1, t2) ->
      Printf.sprintf "(%s) -> (%s)" (dump_ty t1) (dump_ty t2)

(* -------------------------------------------------------------------- *)
let tuni uid     = mk_ty (Tunivar uid)
let tvar id      = mk_ty (Tvar id)
let tconstr p lt = mk_ty (Tconstr (p, lt))
let tfun t1 t2   = mk_ty (Tfun (t1, t2))
let tglob m      = mk_ty (Tglob m)

(* -------------------------------------------------------------------- *)
let tunit      = tconstr EcCoreLib.CI_Unit .p_unit    []
let tbool      = tconstr EcCoreLib.CI_Bool .p_bool    []
let tint       = tconstr EcCoreLib.CI_Int  .p_int     []
let txint      = tconstr EcCoreLib.CI_xint .p_xint    []

let tdistr ty  = tconstr EcCoreLib.CI_Distr.p_distr   [ty]
let toption ty = tconstr EcCoreLib.CI_Option.p_option [ty]
let treal      = tconstr EcCoreLib.CI_Real .p_real    []
let tcpred ty  = tfun ty tbool

let trealp    = tconstr EcCoreLib.CI_Xreal.p_realp []
let txreal    = tconstr EcCoreLib.CI_Xreal.p_xreal []

let ttuple lt    =
  match lt with
  | []  -> tunit
  | [t] -> t
  | _ -> mk_ty (Ttuple lt)

let toarrow dom ty =
  List.fold_right tfun dom ty

let tpred t = tfun t tbool

(* -------------------------------------------------------------------- *)
let tytuple_flat (ty : ty) =
  match ty.ty_node with Ttuple tys -> tys | _ -> [ty]

let rec tyfun_flat (ty : ty) =
  match ty.ty_node with
  | Tfun (t1, t2) ->
      let dom, codom = tyfun_flat t2 in (t1 :: dom, codom)
  | _ ->
      ([], ty)

(* -------------------------------------------------------------------- *)
let as_tdistr (ty : ty) =
  match ty.ty_node with
  | Tconstr (p, [sty])
      when EcPath.p_equal p EcCoreLib.CI_Distr.p_distr
    -> Some sty

  | _ -> None

let is_tdistr (ty : ty) = as_tdistr ty <> None

(* -------------------------------------------------------------------- *)
let ty_map f t =
  match t.ty_node with
  | Tglob _ | Tunivar _ | Tvar _ -> t

  | Ttuple lty ->
     ttuple (List.Smart.map f lty)

  | Tconstr (p, lty) ->
     let lty = List.Smart.map f lty in
     tconstr p lty

  | Tfun (t1, t2) ->
      tfun (f t1) (f t2)

let ty_fold f s ty =
  match ty.ty_node with
  | Tglob _ | Tunivar _ | Tvar _ -> s
  | Ttuple lty -> List.fold_left f s lty
  | Tconstr(_, lty) -> List.fold_left f s lty
  | Tfun(t1,t2) -> f (f s t1) t2

let ty_sub_exists f t =
  match t.ty_node with
  | Tglob _ | Tunivar _ | Tvar _ -> false
  | Ttuple lty -> List.exists f lty
  | Tconstr (_, lty) -> List.exists f lty
  | Tfun (t1, t2) -> f t1 || f t2

let ty_iter f t =
  match t.ty_node with
  | Tglob _ | Tunivar _ | Tvar _ -> ()
  | Ttuple lty -> List.iter f lty
  | Tconstr (_, lty) -> List.iter f lty
  | Tfun (t1,t2) -> f t1; f t2

exception FoundUnivar

let rec ty_check_uni t =
  match t.ty_node with
  | Tunivar _ -> raise FoundUnivar
  | _ -> ty_iter ty_check_uni t

(* -------------------------------------------------------------------- *)
let symbol_of_ty (ty : ty) =
  match ty.ty_node with
  | Tglob   _      -> "g"
  | Tunivar _      -> "u"
  | Tvar    _      -> "x"
  | Ttuple  _      -> "x"
  | Tfun    _      -> "f"
  | Tconstr (p, _) ->
      let x = EcPath.basename p in
      let rec doit i =
        if   i >= String.length x
        then "x"
        else match Char.lowercase_ascii x.[i] with
             | 'a' .. 'z' -> String.make 1 x.[i]
             | _ -> doit (i+1)
      in
        doit 0

let fresh_id_of_ty (ty : ty) =
  EcIdent.create (symbol_of_ty ty)

(* -------------------------------------------------------------------- *)
type ovariable = EcAst.ovariable

let ov_name { ov_name = x } = x
let ov_type { ov_type = x } = x

let ov_hash = EcAst.ov_hash
let ov_equal = EcAst.ov_equal

type variable = EcAst.variable

let v_name { v_name = x } = x
let v_type { v_type = x } = x

let v_hash = EcAst.v_hash
let v_equal = EcAst.v_equal

let ovar_of_var { v_name = n; v_type = t } =
  { ov_name = Some n; ov_type = t }

module Tvar = struct

  let rec fv_rec fv t =
    match t.ty_node with
    | Tvar id -> Sid.add id fv
    | _ -> ty_fold fv_rec fv t

  let fv = fv_rec Sid.empty
end

let ty_fv_and_tvar (ty : ty) =
  EcIdent.fv_union ty.ty_fv (Mid.map (fun () -> 1) (Tvar.fv ty))

(* -------------------------------------------------------------------- *)
type pvar_kind = EcAst.pvar_kind

type prog_var = EcAst.prog_var

let pv_equal = EcAst.pv_equal

let pv_kind = EcAst.pv_kind

let pv_hash = EcAst.pv_hash

let pv_compare v1 v2 =
  match v1, v2 with
  | PVloc i1,  PVloc i2  -> EcSymbols.sym_compare i1 i2
  | PVglob x1, PVglob x2 -> EcPath.x_compare x1 x2
  | _, _ -> Stdlib.compare (pv_kind v1) (pv_kind v2)

let pv_compare_p v1 v2 =
  match v1, v2 with
  | PVloc i1,  PVloc i2  -> EcSymbols.sym_compare i1 i2
  | PVglob x1, PVglob x2 -> EcPath.x_compare_na x1 x2
  | _, _ -> Stdlib.compare (pv_kind v1) (pv_kind v2)

let pv_ntr_compare v1 v2 =
  match v1, v2 with
  | PVloc i1,  PVloc i2  -> EcSymbols.sym_compare i1 i2
  | PVglob x1, PVglob x2 -> EcPath.x_ntr_compare x1 x2
  | _, _ -> Stdlib.compare (pv_kind v1) (pv_kind v2)

let is_loc  = function PVloc _ -> true  | PVglob _ -> false
let is_glob = function PVloc _ -> false | PVglob _ -> true

let get_loc = function PVloc id -> id | PVglob _ -> assert false
let get_glob = function PVloc _ -> assert false | PVglob xp -> xp

let symbol_of_pv = function
  | PVglob x -> x.EcPath.x_sub
  | PVloc id -> id

let string_of_pvar_kind = function
  | PVKglob -> "PVKglob"
  | PVKloc  -> "PVKloc"

let string_of_pvar (p : prog_var) =
  let sp = match p with
    | PVglob x -> EcPath.x_tostring x
    | PVloc id -> id in

  Printf.sprintf "%s[%s]"
    sp (string_of_pvar_kind (pv_kind p))

let name_of_pvar pv =
  match pv with
  | PVloc x -> x
  | PVglob xp -> EcPath.xbasename xp

let pv_loc id = PVloc id

let arg_symbol = "arg"
let res_symbol = "res"
let pv_arg = PVloc arg_symbol
let pv_res =  PVloc res_symbol

let xp_glob x =
  let top = x.EcPath.x_top in
  if top.EcPath.m_args = [] then x else
    (* remove the functor argument *)
    let ntop = EcPath.mpath top.m_top [] in
    EcPath.xpath ntop x.EcPath.x_sub

let pv_glob x = PVglob (xp_glob x)

let pv_subst m_subst px = match px with
  | PVglob x ->
    let mp' = m_subst x in
    if x == mp' then px else pv_glob mp'
  | PVloc _ -> px

(* -------------------------------------------------------------------- *)
type lpattern = EcAst.lpattern

let idty_equal = EcAst.idty_equal

let lp_equal = EcAst.lp_equal

let idty_hash = EcAst.idty_hash

let lp_hash = EcAst.lp_hash

let lp_ids = function
  | LSymbol (id,_)  -> [id]
  | LTuple  ids     -> List.map fst ids
  | LRecord (_,ids) -> List.pmap fst ids

let lp_bind = function
  | LSymbol b     -> [b]
  | LTuple  b     -> b
  | LRecord (_,b) ->
      List.pmap (fun (x, ty) -> omap (fun x -> (x, ty)) x) b

(* -------------------------------------------------------------------- *)
type expr = EcAst.expr

type expr_node = EcAst.expr_node

type equantif  = EcAst.equantif
type ebinding  = EcAst.ebinding
type ebindings = EcAst.ebindings

type closure = (EcIdent.t * ty) list * expr

(* -------------------------------------------------------------------- *)
let e_equal   = EcAst.e_equal
let e_hash    = EcAst.e_hash
let e_compare = fun e1 e2 -> e_hash e1 - e_hash e2
let e_fv      = EcAst.e_fv
let e_ty  e   = e.e_ty

(* -------------------------------------------------------------------- *)
let lp_fv = EcAst.lp_fv

let pv_fv = EcAst.pv_fv

(* -------------------------------------------------------------------- *)
let eqt_equal = EcAst.eqt_equal

(* -------------------------------------------------------------------- *)

let e_tt    = mk_expr (Eop (EcCoreLib.CI_Unit.p_tt, [])) tunit
let e_int   = fun i -> mk_expr (Eint i) tint
let e_local = fun x ty -> mk_expr (Elocal x) ty
let e_var   = fun x ty -> mk_expr (Evar x) ty
let e_op    = fun x targs ty -> mk_expr (Eop (x, targs)) ty
let e_let   = fun pt e1 e2 -> mk_expr (Elet (pt, e1, e2)) e2.e_ty
let e_tuple = fun es ->
  match es with
  | []  -> e_tt
  | [x] -> x
  | _   -> mk_expr (Etuple es) (ttuple (List.map e_ty es))

let e_if    = fun c e1 e2 -> mk_expr (Eif (c, e1, e2)) e2.e_ty
let e_match = fun e es ty -> mk_expr (Ematch (e, es, ty)) ty
let e_proj  = fun e i ty -> mk_expr (Eproj(e,i)) ty

let e_proj_simpl e i ty =
  match e.e_node with
  | Etuple es -> List.nth es i
  | _ -> e_proj e i ty

let e_quantif q b e =
  if List.is_empty b then e else

  let b, e =
    match e.e_node with
    | Equant (q', b', e) when eqt_equal q q' -> (b@b', e)
    | _ -> b, e in

  let ty =
    match q with
    | `ELambda -> toarrow (List.map snd b) e.e_ty
    | `EForall | `EExists -> tbool

  in mk_expr (Equant (q, b, e)) ty

let e_forall b e = e_quantif `EForall b e
let e_exists b e = e_quantif `EExists b e
let e_lam    b e = e_quantif `ELambda b e

let e_app x args ty =
  if args = [] then x
  else
    match x.e_node with
    | Eapp(x', args') -> mk_expr (Eapp (x', (args'@args))) ty
    | _ -> mk_expr (Eapp (x, args)) ty

let e_app_op ?(tyargs=[]) op args ty =
  e_app (e_op op tyargs (toarrow (List.map e_ty args) ty)) args ty

(* -------------------------------------------------------------------- *)
module Reals : sig
  val of_lit : EcBigInt.zint -> expr
  val of_int : expr -> expr
  val add    : expr -> expr -> expr
  val opp    : expr -> expr
  val sub    : expr -> expr -> expr
  val mul    : expr -> expr -> expr
  val inv    : expr -> expr
  val div    : expr -> expr -> expr
end = struct
  module CIR = EcCoreLib.CI_Real

  let of_int f = e_app_op CIR.p_real_of_int [f] treal
  let of_lit n = of_int (e_int n)

  let add f1 f2 = e_app_op CIR.p_real_add [f1; f2] treal
  let opp f     = e_app_op CIR.p_real_opp [f] treal
  let sub f1 f2 = add f1 (opp f2)
  let mul f1 f2 = e_app_op CIR.p_real_mul [f1; f2] treal
  let inv f     = e_app_op CIR.p_real_inv [f] treal
  let div f1 f2 = mul f1 (inv f2)
end

(* -------------------------------------------------------------------- *)
let e_decimal (n, (l, f)) =
  if EcBigInt.equal f EcBigInt.zero then Reals.of_lit n else

  let d   = EcBigInt.pow (EcBigInt.of_int 10) l in
  let gcd = EcBigInt.gcd f d in
  let f   = EcBigInt.div f gcd in
  let d   = EcBigInt.div d gcd in
  let fct = Reals.div (Reals.of_lit f) (Reals.of_lit d) in

  if   EcBigInt.equal n EcBigInt.zero
  then fct
  else Reals.add (Reals.of_lit n) fct

(* -------------------------------------------------------------------- *)
let e_none (ty : ty) : expr =
  e_op EcCoreLib.CI_Option.p_none [ty] (toption ty)

let e_some ({ e_ty = ty } as e : expr) : expr =
  let op = e_op EcCoreLib.CI_Option.p_some [ty] (tfun ty (toption ty)) in
  e_app op [e] (toption ty)

let e_oget (e : expr) (ty : ty) : expr =
  let op = e_op EcCoreLib.CI_Option.p_oget [ty] (tfun (toption ty) ty) in
  e_app op [e] ty

(* -------------------------------------------------------------------- *)
let e_map fty fe e =
  match e.e_node with
  | Eint _ | Elocal _ | Evar _ -> e

  | Eop (p, tys) ->
      let tys' = List.Smart.map fty tys in
      let ty'  = fty e.e_ty in
        e_op p tys' ty'

  | Eapp (e1, args) ->
      let e1'   = fe e1 in
      let args' = List.Smart.map fe args in
      let ty'   = fty e.e_ty in
        e_app e1' args' ty'

  | Elet (lp, e1, e2) ->
      let e1' = fe e1 in
      let e2' = fe e2 in
        e_let lp e1' e2'

  | Etuple le ->
      let le' = List.Smart.map fe le in
        e_tuple le'

  | Eproj (e1, i) ->
      let e' = fe e1 in
      let ty = fty e.e_ty in
      e_proj e' i ty

  | Eif (e1, e2, e3) ->
      let e1' = fe e1 in
      let e2' = fe e2 in
      let e3' = fe e3 in
      e_if e1' e2' e3'

  | Ematch (b, es, ty) ->
      let ty' = fty ty in
      let b'  = fe b in
      let es' = List.Smart.map fe es in
      e_match b' es' ty'

  | Equant (q, b, bd) ->
      let dop (x, ty as xty) =
        let ty' = fty ty in
          if ty == ty' then xty else (x, ty') in
      let b'  = List.Smart.map dop b in
      let bd' = fe bd in
      e_quantif q b' bd'

let e_fold (fe : 'a -> expr -> 'a) (state : 'a) (e : expr) =
  match e.e_node with
  | Eint _                -> state
  | Elocal _              -> state
  | Evar _                -> state
  | Eop _                 -> state
  | Eapp (e, args)        -> List.fold_left fe (fe state e) args
  | Elet (_, e1, e2)      -> List.fold_left fe state [e1; e2]
  | Etuple es             -> List.fold_left fe state es
  | Eproj(e,_)            -> fe state e
  | Eif (e1, e2, e3)      -> List.fold_left fe state [e1; e2; e3]
  | Ematch (e, es, _)     -> List.fold_left fe state (e :: es)
  | Equant (_, _, e1)     -> fe state e1

let e_iter (fe : expr -> unit) (e : expr) =
  e_fold (fun () e -> fe e) () e

module MSHe = EcMaps.MakeMSH(struct type t = expr let tag e = e.e_tag end)
module Me = MSHe.M
module Se = MSHe.S
module He = MSHe.H

(* -------------------------------------------------------------------- *)
let is_local e =
  match e.e_node with
  | Elocal _ -> true
  | _ -> false

(* -------------------------------------------------------------------- *)
let destr_local e =
   match e.e_node with
  | Elocal id -> id
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let is_var e =
  match e.e_node with
  | Evar _ -> true
  | _ -> false

(* -------------------------------------------------------------------- *)
let destr_var e =
   match e.e_node with
  | Evar pv -> pv
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let is_tuple_var e =
  match e.e_node with
  | Etuple es -> List.for_all is_var es
  | _ -> false

(* -------------------------------------------------------------------- *)
let destr_tuple_var e =
   match e.e_node with
  | Etuple es -> List.map destr_var es
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let destr_app = function
    { e_node = Eapp (e, es) } -> (e, es) | e -> (e, [])

(* -------------------------------------------------------------------- *)
let split_args e =
  match e.e_node with
  | Eapp (e, args) -> (e, args)
  | _ -> (e, [])
