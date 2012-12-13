open EcUtils
open EcIdent
open EcTypes

type lbinop = 
  | Land 
  | Lor
  | Limp
  | Liff

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
  | Ftrue
  | Ffalse
  | Fnot   of form
  | Fbinop of form * lbinop * form
  | Fquant of quantif * binding * form
  | Fif    of form * form * form
  | Flet   of lpattern * form * form
  | Funit                                        (* unit literal        *)
  | Fint    of int                               (* int. literal        *)
  | Flocal  of EcIdent.t                         (* Local variable      *)
  | Fpvar   of EcPath.path * ty * Side.t         (* sided symbol        *)
  | Fapp    of EcPath.path * form list           (* op/pred application *)
  | Ftuple  of form list                         (* tuple constructor     *)

let fv f = f.f_fv 
let ty f = f.f_ty

let fv_node = function
  | Ftrue | Ffalse | Funit | Fint _ | Fpvar _ -> Sid.empty
  | Flocal id -> Sid.singleton id
  | Fnot f -> f.f_fv
  | Fbinop(f1,_,f2) -> Sid.union (fv f1) (fv f2)
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

let ty_bool = tbool ()
let ty_int = tint ()
let ty_unit = tunit ()

let f_true = mk_form Ftrue ty_bool
let f_false = mk_form Ffalse ty_bool
let f_bool b = if b then f_true else f_false
let f_int n = mk_form (Fint n) ty_int
let f_unit = mk_form Funit ty_unit

let f_not f = mk_form (Fnot f) ty_bool
let f_binop f1 op f2 = mk_form (Fbinop(f1,op,f2)) ty_bool
let f_local x ty = mk_form (Flocal x) ty
let f_pvar x ty s = mk_form (Fpvar(x,ty,s)) ty

let f_app x args oty = 
  let ty = odfl ty_bool oty in
  mk_form (Fapp(x,args)) ty

let f_tuple args = 
  mk_form (Ftuple args) (Ttuple (List.map ty args))

let f_if f1 f2 f3 = mk_form (Fif(f1,f2,f3)) f2.f_ty 

let f_let q f1 f2 = mk_form (Flet(q,f1,f2)) f2.f_ty (* FIXME rename binding *)

let f_quant q b f = mk_form (Fquant(q,b,f)) ty_bool (* FIXME rename binding *)
let f_exists b f = f_quant Lexists b f 
let f_forall b f = f_quant Lforall b f

let map gt g f = 
  match f.f_node with
  | Ftrue -> f_true
  | Ffalse -> f_false
  | Fnot f -> f_not (g f)
  | Fbinop(f1,op,f2) -> f_binop (g f1) op (g f2)
  | Fquant(q,b,f) -> 
      f_quant q (List.map (fun (x,ty) -> x, gt ty) b) (g f)
  | Fif(f1,f2,f3) -> f_if (g f1) (g f2) (g f3)
  | Flet(lp,f1,f2) -> f_let lp (g f1) (g f2)
  | Funit -> f_unit 
  | Fint i -> f_int i 
  | Flocal id -> f_local id (gt f.f_ty)
  | Fpvar(id,ty,s) -> f_pvar id (gt ty) s
  | Fapp(p,es) -> f_app p (List.map g es) (Some (gt f.f_ty))
  | Ftuple es -> f_tuple (List.map g es) 

(* -------------------------------------------------------------------- *)
module Subst = struct
  let uni uidmap = 
    let rec aux formula =
      map (EcTypes.Subst.uni uidmap) aux formula in
    aux
end
