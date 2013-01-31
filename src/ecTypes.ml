(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcUidgen

(* -------------------------------------------------------------------- *)
type ty =
  | Tunivar of EcUidgen.uid
  | Tvar    of EcIdent.t
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty
 
type dom = ty list
type tysig = dom * ty 

(* -------------------------------------------------------------------- *)
let tunit      = Tconstr(EcCoreLib.p_unit, [])
let tbool      = Tconstr(EcCoreLib.p_bool, [])
let tint       = Tconstr(EcCoreLib.p_int , [])
let tdistr  ty = Tconstr(EcCoreLib.p_distr, [ty])
 
let toarrow dom ty = 
  List.fold_right (fun t1 t2 -> Tfun(t1,t2)) dom ty

(* -------------------------------------------------------------------- *)
let map f t = 
  match t with 
  | Tunivar _ | Tvar _ -> t
  | Ttuple lty -> Ttuple (List.map f lty)
  | Tconstr(p, lty) -> Tconstr (p, List.map f lty)
  | Tfun(t1,t2)     -> Tfun(f t1, f t2)

let fold f s = function
  | Tunivar _ | Tvar _ -> s
  | Ttuple lty -> List.fold_left f s lty
  | Tconstr(_, lty) -> List.fold_left f s lty
  | Tfun(t1,t2) -> f (f s t1) t2

let sub_exists f t =
  match t with
  | Tunivar _ | Tvar _ -> false
  | Ttuple lty -> List.exists f lty
  | Tconstr (_, lty) -> List.exists f lty
  | Tfun (t1,t2) -> f t1 || f t2
  
(* -------------------------------------------------------------------- *)
module Tuni = struct
  let subst1 ((id, t) : uid * ty) =
    let rec aux = function
      | Tunivar id' when uid_equal id id' -> t
      | u -> map aux u in
    aux

  let subst (uidmap : ty Muid.t) =
    let rec aux = function
      | (Tunivar id) as t -> odfl t (Muid.find_opt id uidmap)
      | t -> map aux t in
    aux 

  let subst_dom uidmap = List.map (subst uidmap)

  let occur u = 
    let rec aux t = 
      match t with
      | Tunivar u' -> uid_equal u u'
      | _ -> sub_exists aux t in
    aux

  let rec fv_rec fv t = 
    match t with
    | Tunivar id -> Suid.add id fv 
    | _ -> fold fv_rec fv t 

  let fv = fv_rec Suid.empty

  let fv_sig (dom, codom) = 
    List.fold_left fv_rec (fv codom) dom
end

module Tvar = struct 
  let subst1 (id,t) = 
    let rec aux = function
      | Tvar id' when id_equal id id' -> t
      | u -> map aux u in
    aux

  let subst (s : ty Mid.t) =
    let rec aux = function
      | (Tvar id) as t -> odfl t (Mid.find_opt id s)
      | t -> map aux t in
    aux 

  let init lv lt = 
    assert (List.length lv = List.length lt);
    List.fold_left2 (fun s v t -> Mid.add v t s) Mid.empty lv lt

  let rec fv_rec fv t = 
    match t with
    | Tvar id -> Sid.add id fv 
    | _ -> fold fv_rec fv t 

  let fv = fv_rec Sid.empty

  let fv_sig (dom, codom) = 
    List.fold_left fv_rec (fv codom) dom

end

(* -------------------------------------------------------------------- *)
type pvar_kind = 
  | PVglob
  | PVloc 

type prog_var = 
    { pv_name : EcPath.path;
      pv_kind : pvar_kind }

type lpattern =
  | LSymbol of EcIdent.t
  | LTuple  of EcIdent.t list

type tyexpr = {
  tye_desc : tyexpr_r;
  tye_meta : tyexpr_meta option;
}

and tyexpr_r =
  | Eint      of int                              (* int. literal       *)
  | Elocal    of EcIdent.t                        (* let-variables      *)
  | Evar      of prog_var                         (* module variable    *)
  | Eop       of EcPath.path * ty list            (* op apply to type args *)
  | Eapp      of tyexpr * tyexpr list             (* op. application    *)
  | Elet      of lpattern * tyexpr * tyexpr       (* let binding        *)
  | Etuple    of tyexpr list                      (* tuple constructor  *)
  | Eif       of tyexpr * tyexpr * tyexpr         (* _ ? _ : _          *)

and tyexpr_meta = {
  tym_type : ty;
}

let e_ty e = (oget e.tye_meta).tym_type
(* -------------------------------------------------------------------- *)
let e_tyexpr (e : tyexpr_r) =
  { tye_desc = e; tye_meta = None; }

let e_int      = fun i        -> e_tyexpr (Eint i)
let e_local    = fun x        -> e_tyexpr (Elocal x)
let e_var      = fun x        -> e_tyexpr (Evar x)
let e_op       = fun x targs  -> e_tyexpr (Eop (x, targs))
let e_app x args = 
  match x.tye_desc with
  | Eapp(x', args') -> e_tyexpr (Eapp (x', (args'@args)))
  | _ -> e_tyexpr (Eapp (x, args))

let e_let      = fun pt e1 e2 -> e_tyexpr (Elet (pt, e1, e2))
let e_tuple    = fun es       -> e_tyexpr (Etuple es)
let e_if       = fun c e1 e2  -> e_tyexpr (Eif (c, e1, e2))

(* -------------------------------------------------------------------- *)
let pv_equal v1 v2 = 
  EcPath.p_equal v1.pv_name v2.pv_name && v1.pv_kind = v2.pv_kind 

(* -------------------------------------------------------------------- *)
let ids_of_lpattern = function
  | LSymbol id -> [id] 
  | LTuple ids -> ids

let rec e_map fty fmeta fe e =
  { tye_desc = e_map_r fty fe e.tye_desc;
    tye_meta = fmeta e.tye_meta; }

and e_map_r fty fe e =
  match e with 
  | Eint _                -> e
  | Elocal id             -> Elocal id
  | Evar id               -> Evar id
  | Eop (p, tys)          -> Eop(p, List.map fty tys)
  | Eapp (e, args)        -> Eapp(fe e, List.map fe args)
  | Elet (lp, e1, e2)     -> Elet (lp, fe e1, fe e2)
  | Etuple le             -> Etuple (List.map fe le)
  | Eif (e1, e2, e3)      -> Eif (fe e1, fe e2, fe e3)


let rec e_fold fe state e =
  e_fold_r fe state e.tye_desc

and e_fold_r fe state e =
  match e with
  | Eint _                -> state
  | Elocal _              -> state
  | Evar _                -> state
  | Eop _                 -> state
  | Eapp (e, args)        -> List.fold_left fe (fe state e) args
  | Elet (_, e1, e2)      -> List.fold_left fe state [e1; e2]
  | Etuple es             -> List.fold_left fe state es
  | Eif (e1, e2, e3)      -> List.fold_left fe state [e1; e2; e3]


(* -------------------------------------------------------------------- *)
module Esubst = struct 
  let mapty onty = 
    let onmeta _ = None in
    let rec aux e = e_map onty onmeta aux e in
    aux 

  let uni (uidmap : ty Muid.t) = mapty (Tuni.subst uidmap)
end

(* -------------------------------------------------------------------- *)
module Dump = struct
  let ty_dump pp =
    let rec ty_dump pp = function
      | Tunivar i ->
          EcDebug.single pp ~extra:(string_of_int i) "Tunivar"
  
      | Tvar a ->
          EcDebug.single pp ~extra:(EcIdent.tostring a) "Tvar"
  
      | Ttuple tys ->
          EcDebug.onhlist pp "Ttuple" ty_dump tys
  
      | Tconstr (p, tys) ->
          let strp = EcPath.tostring p in
            EcDebug.onhlist pp ~extra:strp "Tconstr" ty_dump tys
      | Tfun (t1, t2) ->
          EcDebug.onhlist pp "Tfun" ty_dump [t1;t2]
    in
      fun ty -> ty_dump pp ty

  let ex_dump pp =
    let rec ex_dump pp e =
      match e.tye_desc with
      | Eint i ->
          EcDebug.single pp ~extra:(string_of_int i) "Eint"

      | Elocal x ->
          EcDebug.onhlist pp
            "Elocal" ~extra:(EcIdent.tostring x)
            ty_dump []
        
      | Evar x ->
          EcDebug.onhlist pp
            "Evar" ~extra:(EcPath.tostring x.pv_name)
            ty_dump []
      | Eop (x, tys) ->
          EcDebug.onhlist pp "Eop" ~extra:(EcPath.tostring x)
            ty_dump tys
          
      | Eapp (e, args) -> 
          EcDebug.onhlist pp "Eapp" ex_dump (e::args)

      | Elet (_p, e1, e2) ->            (* FIXME *)
          let printers = [ex_dump^~ e1; ex_dump^~ e2] in
            EcDebug.onseq pp "Elet" (Stream.of_list printers)
        
      | Etuple es ->
          EcDebug.onhlist pp ~enum:true "Etuple" ex_dump es
        
      | Eif (c, e1, e2) ->
          EcDebug.onhlist pp "Eif" ex_dump [c; e1; e2]
    in
      fun e -> ex_dump pp e
end
