(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcTypes

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

let mem_equal = EcIdent.id_equal

(* -------------------------------------------------------------------- *)
type local_memtype = {
  mt_path : EcPath.xpath;
  mt_vars : ((int*int) option * ty) Msym.t
}

type memtype = local_memtype option

let mt_fv = function
  | None -> EcIdent.Mid.empty
  | Some lmt ->
    let fv = EcPath.x_fv EcIdent.Mid.empty lmt.mt_path in
    Msym.fold (fun _ (_,ty) fv -> EcIdent.fv_union fv ty.ty_fv) lmt.mt_vars fv 

let lmt_equal mt1 mt2 =   
  EcPath.x_equal mt1.mt_path mt2.mt_path &&
    Msym.equal (fun (p1,ty1) (p2,ty2) -> p1 = p2 && ty_equal ty1 ty2) 
      mt1.mt_vars mt2.mt_vars

let lmt_xpath mt = mt.mt_path
let lmt_bindings mt = mt.mt_vars

let mt_equal mt1 mt2 = 
  match mt1, mt2 with
  | Some mt1, Some mt2 -> lmt_equal mt1 mt2
  | None, None         -> true
  | _   , _            -> false

let mt_xpath = function
  | None -> assert false
  | Some mt -> lmt_xpath mt
 
let mt_bindings = function
  | None -> assert false
  | Some mt -> lmt_bindings mt

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype 

let me_equal (m1,mt1) (m2,mt2) = 
  mem_equal m1 m2 && mt_equal mt1 mt2 

(* -------------------------------------------------------------------- *)
let memory   (m,_) = m
let memtype  (_,mt) = mt
let xpath    (_,mt) = mt_xpath mt
let bindings (_,mt) = mt_bindings mt

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

(* -------------------------------------------------------------------- *)
let empty_local (me : memory) mp =
  (me, Some {mt_path   = mp; mt_vars   = Msym.empty; } )

let abstract (me:memory) = (me,None)

(* -------------------------------------------------------------------- *)
let bindp (x : symbol) pr (ty : EcTypes.ty) ((m,mt) : memenv) =
  let mt = match mt with
    | None -> assert false
    | Some mt -> mt in
  let merger = function
    | Some _ -> raise (DuplicatedMemoryBinding x)
    | None   -> Some (pr,ty)
  in
    (m, Some { mt with mt_vars = Msym.change merger x mt.mt_vars })

let bind_proj i n x ty me = bindp x (Some (i,n)) ty me
let bind x ty me = bindp x None ty me

(* -------------------------------------------------------------------- *)
let lookup (x : symbol) ((_,mt) : memenv) =
  match mt with 
  | None -> None
  | Some mt ->  Msym.find_opt x (lmt_bindings mt)

let is_bound x me = lookup x me <> None
  
(* -------------------------------------------------------------------- *)
let mt_subst sx st o =
  match o with
  | None -> o
  | Some mt ->
    let p' = sx mt.mt_path in
    let vars' = 
      if st == identity then mt.mt_vars else
        Msym.map (fun (p,ty) -> p, st ty) mt.mt_vars in 
           (* FIXME could be greate to use smart_map *)
    if p' == mt.mt_path && vars' == mt.mt_vars then o else
      Some { mt_path   = p'; mt_vars   = vars' }

let mt_substm sp smp st o =
  mt_subst (EcPath.x_substm sp smp) st o

let me_subst sx sm st (m,mt as me) =
  let m' = EcIdent.Mid.find_def m m sm in
  let mt' = mt_subst sx st mt in
  if m' == m && mt' == mt then me else 
    (m', mt')

let me_substm sp smp sm st me =
  me_subst (EcPath.x_substm sp smp) sm st me



