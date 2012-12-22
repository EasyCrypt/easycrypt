open EcUtils
open EcIdent
open EcTypes

type quantif = 
  | Lforall
  | Lexists

type binding = (EcIdent.t * ty) list

module Side : sig
  type t = int
  (* For non relational formula *)
  val mono : t 
  (* For relational formula *)
  val left : t
  val right : t 
end = struct
  type t = int 
  let mono = 0
  let left = 1
  let right = 2
end

type form = { 
    f_node : f_node;
    f_ty   : ty;
    f_fv  : Sid.t }

and f_node = 
  | Fquant of quantif * binding * form
  | Fif    of form * form * form
  | Flet   of lpattern * form * form
  | Fint    of int                               (* int. literal        *)
  | Flocal  of EcIdent.t                         (* Local variable      *)
  | Fpvar   of EcTypes.prog_var * ty * Side.t    (* sided symbol        *)
  | Fapp    of EcPath.path * form list           (* op/pred application *)
  | Ftuple  of form list                         (* tuple constructor     *)

let fv f = f.f_fv 
let ty f = f.f_ty

let fv_node = function
  | Fint _ | Fpvar _ -> Sid.empty
  | Flocal id -> Sid.singleton id
  | Fquant(_,b,f) -> 
      List.fold_left (fun s (id,_) -> Sid.remove id s) (fv f) b 
  | Fif(f1,f2,f3) -> 
      Sid.union (fv f1) (Sid.union (fv f2) (fv f3))
  | Flet(lp, f1, f2) ->
      let fv2 = 
        List.fold_left (fun s id -> Sid.remove id s) (fv f2) (ids_of_lpattern lp) in
      Sid.union (fv f1) fv2
  | Fapp(_,args) | Ftuple args ->
      List.fold_left (fun s f -> Sid.union s (fv f)) Sid.empty args
  
let mk_form node ty = 
  { f_node = node;
    f_ty   = ty;
    f_fv  = fv_node node }

let ty_bool = tbool
let ty_int = tint 
let ty_unit = tunit

let f_app x args ty = 
  mk_form (Fapp(x,args)) ty

let f_true = f_app EcCoreLib.p_true [] ty_bool
let f_false = f_app EcCoreLib.p_false [] ty_bool
let f_bool b = if b then f_true else f_false
let f_int n = mk_form (Fint n) ty_int

let f_not f = f_app EcCoreLib.p_not [f] ty_bool
let f_and f1 f2 = f_app EcCoreLib.p_and [f1;f2] ty_bool
let f_or  f1 f2 = f_app EcCoreLib.p_or [f1;f2] ty_bool
let f_imp f1 f2 = f_app EcCoreLib.p_imp [f1;f2] ty_bool
let f_iff f1 f2 = f_app EcCoreLib.p_iff [f1;f2] ty_bool

let f_local x ty = mk_form (Flocal x) ty
let f_pvar x ty s = mk_form (Fpvar(x,ty,s)) ty

let f_tuple args = 
  mk_form (Ftuple args) (Ttuple (List.map ty args))

let f_if f1 f2 f3 = mk_form (Fif(f1,f2,f3)) f2.f_ty 

let f_let q f1 f2 = mk_form (Flet(q,f1,f2)) f2.f_ty (* FIXME rename binding *)

let f_quant q b f = mk_form (Fquant(q,b,f)) ty_bool (* FIXME rename binding *)
let f_exists b f = f_quant Lexists b f 
let f_forall b f = f_quant Lforall b f

let map gt g f = 
  match f.f_node with
  | Fquant(q,b,f) -> 
      f_quant q (List.map (fun (x,ty) -> x, gt ty) b) (g f)
  | Fif(f1,f2,f3) -> f_if (g f1) (g f2) (g f3)
  | Flet(lp,f1,f2) -> f_let lp (g f1) (g f2)
  | Fint i -> f_int i 
  | Flocal id -> f_local id (gt f.f_ty)
  | Fpvar(id,ty,s) -> f_pvar id (gt ty) s
  | Fapp(p,es) -> f_app p (List.map g es) (gt f.f_ty)
  | Ftuple es -> f_tuple (List.map g es) 

(* -------------------------------------------------------------------- *)
module Fsubst = struct
  let mapty onty = 
    let rec aux f = map onty aux f in
    aux 

  let uni uidmap = mapty (Tuni.subst uidmap)

end
