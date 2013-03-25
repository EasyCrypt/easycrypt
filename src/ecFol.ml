(* -------------------------------------------------------------------- *)
open EcDebug
open EcUtils
open EcMaps
open EcIdent
open EcTypes
open EcModules

type memory = EcMemory.memory

(* -------------------------------------------------------------------- *)
type gty =
  | GTty    of EcTypes.ty
  | GTmodty of module_type
  | GTmem

type quantif = 
  | Lforall
  | Lexists
  | Llambda

type binding = (EcIdent.t * gty) list

let mstd   = EcIdent.create "$std"
let mpre   = EcIdent.create "$pre"
let mpost  = EcIdent.create "$post"
let mhr    = EcIdent.create "$hr"
let mleft  = EcIdent.create "$1"
let mright = EcIdent.create "$2"

type form = { 
  f_node : f_node;
  f_ty   : ty; 
  f_fv   : int EcIdent.Mid.t; (* local, memory, module ident *)
  f_tag  : int;
}

and f_node =
  | Fquant  of quantif * binding * form
  | Fif     of form * form * form
  | Flet    of lpattern * form * form
  | Fint    of int                               (* int. literal              *)
  | Flocal  of EcIdent.t                         (* Local variable            *)
  | Fpvar   of EcTypes.prog_var * memory         (* sided symbol              *)
  | Fop     of EcPath.path * ty list             (* Op/pred application to ty *)
  | Fapp    of form * form list                  (* application *)
  | Ftuple  of form list                         (* tuple constructor   *)

  | FhoareF of form * EcPath.mpath * form  (* $pre / $post *)
  | FhoareS of EcMemory.memenv * form * stmt * form (* $hr / $hr *)

    (* $left,$right / $left,$right *)
  | FequivF of form * (EcPath.mpath * EcPath.mpath) * form
  | FequivS of form * (EcMemory.memenv * stmt) EcUtils.double * form

  | Fpr of memory * EcPath.mpath * form list * form (* $post *)

(*-------------------------------------------------------------------- *)
let f_equal : form -> form -> bool = (==)
let f_compare f1 f2 = f2.f_tag - f1.f_tag 
let f_hash f = f.f_tag 
let f_fv f = f.f_fv 
let f_ty f = f.f_ty

module MSHf = EcMaps.MakeMSH(struct
  type t = form
  let tag f = f.f_tag
end)

module Mf = MSHf.M
module Sf = MSHf.S
module Hf = MSHf.H

let qt_equal : quantif -> quantif -> bool = (==)
let qt_hash = function
  | Lforall -> 0
  | Lexists -> 1
  | Llambda -> 2

let gty_equal ty1 ty2 =
  match ty1, ty2 with
  | GTty    ty1, GTty   ty2 -> EcTypes.ty_equal ty1 ty2
  | GTmodty p1, GTmodty p2  -> EcPath.p_equal p1 p2
  | GTmem     , GTmem       -> true
  | _         , _           -> false

let gty_hash = function
  | GTty    ty -> Why3.Hashcons.combine (EcTypes.ty_hash ty) 0
  | GTmodty p  -> Why3.Hashcons.combine (EcPath.p_hash   p ) 1
  | GTmem      -> Hashtbl.hash GTmem

let b_equal (b1 : binding) (b2 : binding) =
  let b1_equal (x1, ty1) (x2, ty2) = 
    EcIdent.id_equal x1 x2 && gty_equal ty1 ty2
  in
    List.all2 b1_equal b1 b2
    
let b_hash (bs : binding) =
  let b1_hash (x, ty) = 
    Why3.Hashcons.combine (EcIdent.tag x) (gty_hash ty)
  in
    Why3.Hashcons.combine_list b1_hash 0 bs

(* -------------------------------------------------------------------- *)
module Hsform = Why3.Hashcons.Make (struct
  type t = form

  let equal_node f1 f2 =
    match f1, f2 with
    | Fquant(q1,b1,f1), Fquant(q2,b2,f2) ->
        qt_equal q1 q2 && b_equal b1 b2 && f_equal f1 f2 

    | Fif(b1,t1,f1), Fif(b2,t2,f2) ->
        f_equal b1 b2 && f_equal t1 t2 && f_equal f1 f2

    | Flet(lp1,e1,f1), Flet(lp2,e2,f2) ->
        lp_equal lp1 lp2 && f_equal e1 e2 && f_equal f1 f2

    | Fint i1, Fint i2 ->
        i1 = i2

    | Flocal id1, Flocal id2 ->
        EcIdent.id_equal id1 id2

    | Fpvar(pv1,s1), Fpvar(pv2,s2) -> 
        EcIdent.id_equal s1 s2 && EcTypes.pv_equal pv1 pv2

    | Fop(p1,lty1), Fop(p2,lty2) ->
        EcPath.p_equal p1 p2 && List.all2 ty_equal lty1 lty2

    | Fapp(f1,args1), Fapp(f2,args2) ->
        f_equal f1 f2 && List.all2 f_equal args1 args2

    | Ftuple args1, Ftuple args2 ->
        List.all2 f_equal args1 args2

    | FhoareF (pre1, mp1, post1), FhoareF (pre2, mp2, post2) ->
           EcPath.m_equal mp1 mp2
        && f_equal pre1  pre2
        && f_equal post1 post2

    | FhoareS(me1,pre1,s1,post1), FhoareS(me2,pre2,s2,post2) ->
           f_equal pre1 pre2 
        && f_equal post1 post2 
        && s_equal s1 s2 
        && EcMemory.me_equal me1 me2
        
    | FequivF(pre1,(mpl1,mpr1),post1), FequivF(pre2,(mpl2,mpr2),post2) ->
           f_equal pre1 pre2 
        && f_equal post1 post2 
        && EcPath.m_equal mpl1 mpl2 
        && EcPath.m_equal mpr1 mpr2 

    | FequivS(pre1,((mel1,sl1),(mer1,sr1)),post1), 
      FequivS(pre2,((mel2,sl2),(mer2,sr2)),post2) ->
           f_equal pre1 pre2 
        && f_equal post1 post2 
        && s_equal sl1 sl2 
        && s_equal sr1 sr2 
        && EcMemory.me_equal mel1 mel2
        && EcMemory.me_equal mer1 mer2

    | Fpr (m1, mp1, args1, ev1), Fpr (m2, mp2, args2, ev2) ->
           EcIdent.id_equal m1  m2
        && EcPath.m_equal   mp1 mp2
        && f_equal          ev1 ev2
        && (List.all2 f_equal args1 args2)

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

    | Flet(lp, e, f) ->
        Why3.Hashcons.combine2 (lp_hash lp) (f_hash e) (f_hash f)

    | Fint i -> Hashtbl.hash i

    | Flocal id -> EcIdent.tag id

    | Fpvar(pv, s) ->
        Why3.Hashcons.combine (EcTypes.pv_hash pv) (EcIdent.id_hash s)

    | Fop(p, lty) -> 
        Why3.Hashcons.combine_list ty_hash (EcPath.p_hash p) lty

    | Fapp(f, args) ->
        Why3.Hashcons.combine_list f_hash (f_hash f) args

    | Ftuple args ->
        Why3.Hashcons.combine_list f_hash 0 args

    | FhoareF (pre, mp, post) ->
        Why3.Hashcons.combine2
          (f_hash pre) (f_hash post) (EcPath.m_hash mp)

    | FhoareS (_m, p, s, q) ->
        Why3.Hashcons.combine2
          (f_hash p) (f_hash q) (EcModules.s_hash s)

    | FequivF (pre, (mp1, mp2), post) ->
        Why3.Hashcons.combine3
          (f_hash pre) (f_hash post)
          (EcPath.m_hash mp1) (EcPath.m_hash mp2)
    | FequivS (pre, ((_,s1),(_,s2)), post) ->
        Why3.Hashcons.combine3
          (f_hash pre) (f_hash post)
          (EcModules.s_hash s1) (EcModules.s_hash s2)

    | Fpr (_m, mp, args, ev) ->
        let id =
          Why3.Hashcons.combine
            (EcPath.m_hash   mp)
            (f_hash          ev)
        in
          Why3.Hashcons.combine_list f_hash id args


  let fv_mlr = Sid.add mleft (Sid.singleton mright)

  let fv_node = function
    | Fint _ | Fpvar _ | Fop _ -> Mid.empty
    | Flocal id -> fv_singleton id 
    | Fquant(_,b,f) -> 
        List.fold_left (fun s (id,_) -> Mid.remove id s) (f_fv f) b 
    | Fif(f1,f2,f3) -> 
        fv_union (f_fv f1) (fv_union (f_fv f2) (f_fv f3))
    | Flet(lp, f1, f2) ->
        let fv2 = fv_diff (f_fv f2) (lp_fv lp) in
        fv_union (f_fv f1) fv2
    | Fapp(f,args) ->
        List.fold_left (fun s a -> fv_union s (f_fv a)) (f_fv f) args
    | Ftuple args ->
        List.fold_left (fun s a -> fv_union s (f_fv a)) Mid.empty args
    | FhoareF (pre,mp,post) ->
        let fv = 
          fv_union (Mid.remove mpre (f_fv pre)) 
            (Mid.remove mpost (f_fv post)) in
        EcPath.m_fv fv mp
    | FhoareS(_,pre,s,post) ->
        let fv = Mid.remove mhr (fv_union (f_fv pre) (f_fv post)) in
        fv_union (EcModules.s_fv s) fv
    | FequivF (pre,(fl,fr),post) ->
        let fv = fv_diff (fv_union (f_fv pre) (f_fv post)) fv_mlr in
        EcPath.m_fv (EcPath.m_fv fv fl) fr
    | FequivS (pre,((_,sl),(_,sr)),post) ->
        let fv = fv_diff (fv_union (f_fv pre) (f_fv post)) fv_mlr in
        fv_union fv (fv_union (EcModules.s_fv sl) (EcModules.s_fv sr))
    | Fpr (m,mp,args,event) ->
        let fve = Mid.remove mpost (f_fv event) in
        let fv  = EcPath.m_fv fve mp in
        List.fold_left (fun s f -> fv_union s (f_fv f))
          (fv_add m fv) args
  
  let tag n f = { f with f_tag = n;
                  f_fv = fv_node f.f_node }
end)

(* -------------------------------------------------------------------- *)
let rec lp_dump (lp : lpattern) =
  match lp with
  | LSymbol (x,_) ->
      dleaf "LSymbol (%s)" (EcIdent.tostring x)

  | LTuple xs ->
      let xs = List.map (fun (x,_) -> EcIdent.tostring x) xs in
        dleaf "LTuple (%s)" (String.concat ", " xs)

let string_of_quantif = function
  | Lforall -> "Lforall"
  | Lexists -> "Lexists"
  | Llambda -> "Llambda"

let gty_dump (gty : gty) =
  match gty with
  | GTty    t -> dnode "GTty" [ty_dump t]
  | GTmodty _ -> dleaf "GTmodty"
  | GTmem     -> dleaf "GTmem"

let bd_dump (x, gty) =
  dnode
    (Printf.sprintf "binding (%s)" (EcIdent.tostring x))
    [gty_dump gty]

let rec f_dump (f : form) : dnode =
  let node =
    match f.f_node with
    | Fquant (q, b, f) ->
        dnode
          (Printf.sprintf "Fquant (%s)" (string_of_quantif q))
          (List.flatten [List.map bd_dump b; [f_dump f]])
  
    | Flocal x ->
        dleaf "Flocal (%s)" (EcIdent.tostring x)
  
    | Fint i ->
        dleaf "Fint (%d)"  i
  
    | Fpvar (x, m) ->
        dleaf "Fpvar (%s, %s)" (string_of_pvar x) (EcIdent.tostring m)
  
    | Fif (c, f1, f2) ->
        dnode "Fif" (List.map f_dump [c; f1; f2])
  
    | Flet (p, f1, f2) ->
        dnode "Flet" [lp_dump p; f_dump f1; f_dump f2]
  
    | Fapp (f, fs) ->
        dnode "Fapp" [f_dump f; dnode "arguments" (List.map f_dump fs)]
  
    | Fop (p, tys) ->
        dnode
          (Printf.sprintf "Fop (%s)" (EcPath.tostring p))
          [dnode "type-arguments" (List.map ty_dump tys)]
  
    | Ftuple fs ->
        dnode "Ftuple" (List.map f_dump fs)
  
    | FhoareF _ -> dleaf "FhoareF"
    | FhoareS _ -> dleaf "FhoareS"
    | FequivF _ -> dleaf "FequivF"
    | FequivS _ -> dleaf "FequivS"
    | Fpr     _ -> dleaf "Fpr"
  in
    (* dnode "Form" [ty_dump f.f_ty; node] *)
    node

(* -------------------------------------------------------------------- *)
let mk_form node ty =  Hsform.hashcons 
    { f_node = node;
      f_ty   = ty;
      f_fv   = Mid.empty;
      f_tag = -1; }

let ty_bool = tbool
let ty_int  = tint 
let ty_unit = tunit
let ty_real = treal

let f_op x tys ty = 
  mk_form (Fop(x,tys)) ty

let f_app f args ty = 
  if args = [] then f 
  else match f.f_node with
  | Fapp(f',args') -> mk_form (Fapp(f', args'@args)) ty
  | _ -> mk_form (Fapp(f,args)) ty

let f_true = f_op EcCoreLib.p_true [] ty_bool
let f_false = f_op EcCoreLib.p_false [] ty_bool
let f_bool b = if b then f_true else f_false
let f_int n = mk_form (Fint n) ty_int

let ty_fbool1 = tfun ty_bool ty_bool
let ty_fbool2 = tfun ty_bool ty_fbool1 

let fop_not = f_op EcCoreLib.p_not [] ty_fbool1
let f_not f = f_app fop_not [f] ty_bool

let fop_and = f_op EcCoreLib.p_and [] ty_fbool2
let f_and f1 f2 = f_app fop_and [f1;f2] ty_bool

let fop_anda = f_op EcCoreLib.p_anda [] ty_fbool2
let f_anda f1 f2 = f_app fop_anda [f1;f2] ty_bool

let fop_or = f_op EcCoreLib.p_or [] ty_fbool2
let f_or  f1 f2 = f_app fop_or [f1;f2] ty_bool

let fop_ora = f_op EcCoreLib.p_ora [] ty_fbool2
let f_ora  f1 f2 = f_app fop_ora [f1;f2] ty_bool

let fop_imp = f_op EcCoreLib.p_imp [] ty_fbool2
let f_imp f1 f2 = f_app fop_imp [f1;f2] ty_bool

let fop_iff = f_op EcCoreLib.p_iff [] ty_fbool2
let f_iff f1 f2 = f_app fop_iff [f1;f2] ty_bool

let fop_eq ty = f_op EcCoreLib.p_eq [ty] (tfun ty (tfun ty ty_bool))
let f_eq f1 f2 = f_app (fop_eq f1.f_ty) [f1;f2] ty_bool

let f_local x ty = mk_form (Flocal x) ty
let f_pvar x ty s = mk_form (Fpvar(x, s)) ty

let f_tuple args = 
  mk_form (Ftuple args) (ttuple (List.map f_ty args))

let f_if f1 f2 f3 = mk_form (Fif(f1,f2,f3)) f2.f_ty 

let f_let q f1 f2 = mk_form (Flet(q,f1,f2)) f2.f_ty (* FIXME rename binding *)

let f_quant q b f = 
  if b = [] then f 
  else 
    let q, b, f = 
      match f.f_node with
      | Fquant(q',b',f') when q = q' -> q, b@b', f'
      | _ -> q, b , f in
    let ty = 
      if q = Llambda then 
        let dom = List.map (fun (_,gty) -> 
          match gty with GTty ty -> ty | _ -> assert false) b in
        toarrow dom f.f_ty 
      else ty_bool in
    mk_form (Fquant(q,b,f)) ty

let f_exists b f = f_quant Lexists b f 
let f_forall b f = f_quant Lforall b f
let f_lambda b f = f_quant Llambda b f


let f_hoareF pre f post = mk_form (FhoareF(pre,f,post)) ty_bool
let f_hoareS mem pre s post = mk_form (FhoareS(mem,pre,s,post)) ty_bool
let f_equivF pre fl fr post = mk_form (FequivF(pre,(fl,fr),post)) ty_bool
let f_equivS pre meml sl memr sr post = 
  mk_form (FequivS(pre,((meml,sl),(memr,sr)),post)) ty_bool
let f_pr m f args e = mk_form (Fpr(m,f,args,e)) ty_real



let fop_int_leq = f_op EcCoreLib.p_leq [] (tfun tint (tfun tint ty_bool))
let f_int_le f1 f2 = 
  if ty_equal f1.f_ty tint then 
    f_app fop_int_leq [f1;f2] ty_bool
  else 
    assert false (* FIXME *)

let fop_int_lt = f_op EcCoreLib.p_lt [] (tfun tint (tfun tint ty_bool))
let f_int_lt f1 f2 = 
  if ty_equal f1.f_ty tint then 
    f_app fop_int_lt [f1;f2] ty_bool
  else 
    assert false (* FIXME *)

(* -------------------------------------------------------------------- *)
type destr_error =
  | Destr_local
  | Destr_not 
  | Destr_and
  | Destr_or
  | Destr_imp
  | Destr_iff
  | Destr_eq
  | Destr_forall
  | Destr_exists
  | Destr_let1

exception DestrError of destr_error

let destr_error e = raise (DestrError e)

let destr_local f = 
  match f.f_node with
  | Flocal id -> id
  | _ -> destr_error Destr_local

let is_op_and p = 
  EcPath.p_equal p EcCoreLib.p_and || EcPath.p_equal p EcCoreLib.p_anda

let is_op_or p = 
  EcPath.p_equal p EcCoreLib.p_or || EcPath.p_equal p EcCoreLib.p_ora

let destr_and f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when is_op_and p -> f1,f2
  | _ -> destr_error Destr_and 

let destr_or f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when is_op_or p -> f1,f2
  | _ -> destr_error Destr_or 

let destr_imp f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when EcPath.p_equal p EcCoreLib.p_imp -> 
      f1,f2
  | _ -> destr_error Destr_imp 

let destr_iff f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when EcPath.p_equal p EcCoreLib.p_iff -> 
      f1,f2
  | _ -> destr_error Destr_iff 

let destr_eq f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when EcPath.p_equal p EcCoreLib.p_eq -> 
      f1,f2
  | _ -> destr_error Destr_eq 

let destr_not f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1]) when EcPath.p_equal p EcCoreLib.p_not -> 
      f1
  | _ -> destr_error Destr_not 

let destr_forall1 f = 
  match f.f_node with
  | Fquant(Lforall,(x,t)::bd,p) -> x,t,f_forall bd p 
  | _ -> destr_error Destr_forall

let destr_exists1 f = 
  match f.f_node with
  | Fquant(Lexists,(x,t)::bd,p) -> x,t,f_exists bd p 
  | _ -> destr_error Destr_exists

let destr_let1 f = 
  match f.f_node with
  | Flet(LSymbol(x,ty), e1,e2) -> x,ty,e1,e2 
  | _ -> destr_error Destr_let1

(* -------------------------------------------------------------------- *)

let is_local f = 
  match f.f_node with
  | Flocal _ -> true
  | _ -> false

let is_true f = f_equal f f_true

let is_false f = f_equal f f_false
  
let is_and f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},_) -> is_op_and p 
  | _ -> false 

let is_or f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},_) -> is_op_or p 
  | _ -> false 

let is_not f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},_) -> EcPath.p_equal p EcCoreLib.p_not 
  | _ -> false

let is_imp f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},_) when EcPath.p_equal p EcCoreLib.p_imp -> true
  | _ -> false

let is_iff f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},_) when EcPath.p_equal p EcCoreLib.p_iff -> true
  | _ -> false

let is_eq f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},_) when EcPath.p_equal p EcCoreLib.p_eq -> true
  | _ -> false

let is_forall f = 
  match f.f_node with
  | Fquant(Lforall,_,_) -> true
  | _ -> false

let is_exists f = 
  match f.f_node with
  | Fquant(Lexists,_,_) -> true
  | _ -> false

let is_let1 f = 
  match f.f_node with
  | Flet(LSymbol(_,_), _,_) -> true
  | _ -> false
(* -------------------------------------------------------------------- *)
let f_map gt g f = 
    match f.f_node with
    | Fquant(q,b,f1) ->
        let map_gty (x,ty as b1) = 
          let ty' =
            match ty with
            | GTty ty1 ->
                let ty1' = gt ty1 in
                if ty1 == ty1' then ty else GTty ty1'
            | _ -> ty in
          if ty == ty' then b1 else (x,ty') in
        let b' = List.smart_map map_gty b in
        let f1' = g f1 in
        if b == b' && f1 == f1' then f else 
        f_quant q b' f1'

    | Fif(f1,f2,f3) ->
        let f1' = g f1 in
        let f2' = g f2 in
        let f3' = g f3 in
        if f1 == f1' && f2 == f2' && f3 == f3' then f else
        f_if f1' f2' f3'

    | Flet(lp,f1,f2) ->
        let f1' = g f1 in
        let f2' = g f2 in
        if f1 == f1' && f2 == f2' then f else
        f_let lp f1' f2'

    | Fint _ -> f 

    | Flocal id ->
        let ty' = gt f.f_ty in
          if f.f_ty == ty' then f else f_local id ty'

    | Fpvar(id,s) -> 
        let ty' = gt f.f_ty in
        if f.f_ty == ty' then f else 
        f_pvar id ty' s

    | Fop(p,tys) -> 
        let tys' = List.smart_map gt tys in
        let ty' = gt f.f_ty in
        if f.f_ty == ty' && tys == tys' then f else 
        f_op p tys' ty'

    | Fapp(e, es) ->
        let e' = g e in
        let es' = List.smart_map g es in
        let ty' = gt f.f_ty in
        if f.f_ty == ty' && e == e' && es == es' then f else
        f_app e' es' ty'

    | Ftuple es -> 
        let es' = List.smart_map g es in
        if es == es' then f else 
        f_tuple es'

    | FhoareF(pre,mp,post) -> 
        let pre' = g pre in
        let post' = g post in
        if pre == pre' && post == post' then f else 
        f_hoareF pre' mp post'

    | FhoareS(m,pre,s,post) ->
        let pre' = g pre in
        let post' = g post in
        if pre == pre' && post == post' then f else 
        f_hoareS m pre' s post'

    | FequivF(pre,(mp1,mp2),post) -> 
        let pre' = g pre in
        let post' = g post in
        if pre == pre' && post == post' then f else 
        f_equivF pre' mp1 mp2 post'

    | FequivS(pre,((ml,sl),(mr,sr)),post) ->
        let pre' = g pre in
        let post' = g post in
        if pre == pre' && post == post' then f else 
        f_equivS pre' ml sl mr sr post'

    | Fpr(m,mp,args,ev) -> 
        let args' = List.smart_map g args in
        let ev' = g ev in
        if args == args' && ev == ev' then f else
        f_pr m mp args' ev'

type f_subst = { 
    fs_p   : EcPath.path -> EcPath.path;
    fs_ty  : ty -> ty;
    fs_mp  : EcPath.mpath Mid.t;
    fs_loc : form Mid.t;
    fs_mem : EcIdent.t Mid.t;
  }

let f_subst_id = {
  fs_p   = identity;
  fs_ty  = identity;
  fs_mp  = Mid.empty;
  fs_loc = Mid.empty;
  fs_mem = Mid.empty
}

let bind_local s x t = 
  let merger o = assert (o = None); Some t in
  { s with fs_loc = Mid.change merger x s.fs_loc }

let bind_mem s m1 m2 = 
  let merger o = assert (o = None); Some m2 in
  { s with fs_mem = Mid.change merger m1 s.fs_mem }

let bind_mod s x mp = 
  let merger o = assert (o = None); Some mp in
  { s with fs_mp = Mid.change merger x s.fs_mp }

let add_local s (x,t) = 
  let x' = EcIdent.fresh x in
  let t' = s.fs_ty t in
  bind_local s x (f_local x' t'), (x',t')

let add_locals = List.map_fold add_local

let subst_lpattern (s: f_subst) (lp:lpattern) = 
  match lp with
  | LSymbol x ->
      let s, x' = add_local s x in
      s , LSymbol x'
  | LTuple xs ->
      let s',xs'  = add_locals s xs in
      s', LTuple xs'

let add_binding s (x,gty) =
  match gty with
  | GTty ty -> 
      let s,(x',ty') = add_local s (x,ty) in
      s,(x',GTty ty')
  | GTmodty p ->
      let p' = s.fs_p p in
      let x' = EcIdent.fresh x in
      bind_mod s x (EcPath.mident x'), (x',GTmodty p')
  | GTmem ->
      let x' = EcIdent.fresh x in
      bind_mem s x x', (x',GTmem)

let add_bindings = List.map_fold add_binding
   
let rec f_subst (s:f_subst) f = 
  match f.f_node with
  | Fquant(q,b,f1) ->
      let s,b = add_bindings s b in
      let f1 = f_subst s f1 in
      f_quant q b f1
  | Flet(lp,f1,f2) -> 
      let f1 = f_subst s f1 in
      let s,lp = subst_lpattern s lp in
      let f2 = f_subst s f2 in
      f_let lp f1 f2
  | Flocal id ->
      (try Mid.find id s.fs_loc with _ -> 
        (* FIXME : this can be dangerous, maybe use a flag *)
        let ty' = s.fs_ty f.f_ty in
        if f.f_ty == ty' then f else f_local id ty')
  | Fop(p,tys) ->
      let ty'  = s.fs_ty f.f_ty in
      let tys' = List.smart_map s.fs_ty tys in
      let p'   = s.fs_p p in
        if   f.f_ty == ty' && tys == tys' && p == p'
        then f
        else f_op p' tys' ty'
  | Fpvar(pv,m) ->
      let pv' = pv_subst (EcPath.m_subst s.fs_p s.fs_mp) pv in
      let m'  = Mid.find_def m m s.fs_mem in
      let ty' = s.fs_ty f.f_ty in
      if pv == pv' && m == m' && ty' = f.f_ty then f else 
      f_pvar pv' ty' m'
  | FhoareF(pre,mp,post) ->
      assert (not (Mid.mem mpre s.fs_mem) && not (Mid.mem mpost s.fs_mem));
      let pre'  = f_subst s pre in
      let post' = f_subst s post in
      let mp'   = EcPath.m_subst s.fs_p s.fs_mp mp in
      if pre == pre' && post == post' && mp == mp' then f else 
      f_hoareF pre' mp' post'
  | FhoareS(me, pre, st, post) ->
      assert (not (Mid.mem mhr s.fs_mem));
      let pre'  = f_subst s pre in
      let post' = f_subst s post in
      let es = e_subst_init s.fs_p s.fs_ty s.fs_mp in
      let st'   = EcModules.s_subst es st in
      (* FIXME me : should we perform subst in path ? *)
      if pre == pre' && st == st' && post == post' then f else
      f_hoareS me pre' st' post'
  | FequivF(pre,(mp1,mp2),post) ->
      assert (not (Mid.mem mleft s.fs_mem) && not (Mid.mem mright s.fs_mem));
      let pre'  = f_subst s pre in
      let post' = f_subst s post in
      let mp1'   = EcPath.m_subst s.fs_p s.fs_mp mp1 in
      let mp2'   = EcPath.m_subst s.fs_p s.fs_mp mp2 in
      if pre == pre' && post == post' && mp1 == mp1' && mp2 == mp2' then f 
      else f_equivF pre' mp1' mp2' post'
  | FequivS(pre,((me1,st1),(me2,st2)),post) -> 
      assert (not (Mid.mem mleft s.fs_mem) && not (Mid.mem mright s.fs_mem));
      let pre'  = f_subst s pre in
      let post' = f_subst s post in
      let es = e_subst_init s.fs_p s.fs_ty s.fs_mp in
      let st1'   = EcModules.s_subst es st1 in
      let st2'   = EcModules.s_subst es st2 in
      (* FIXME me1/2 : should we perform subst in path ? *)
      if pre == pre' && st1 == st1' && st2 == st2' && post == post' then f 
      else f_equivS pre me1 st1' me2 st2' post'
  | Fpr(m,mp,args,e) ->
      assert (not (Mid.mem mpost s.fs_mem));
      let m'    = Mid.find_def m m s.fs_mem in
      let mp'   = EcPath.m_subst s.fs_p s.fs_mp mp in
      let args' = List.smart_map (f_subst s) args in
      let e'    = (f_subst s) e in
      if m == m' && mp == mp' && args == args' && e == e' then f else
      f_pr m' mp' args' e'

  | _ -> f_map s.fs_ty (f_subst s) f 


module Fsubst = struct
  
  let mapty onty = 
    f_subst { f_subst_id with fs_ty = onty }
 
  let uni uidmap = mapty (Tuni.subst uidmap)

  let subst_locals s = 
    Hf.memo_rec 107 (fun aux f ->
      match f.f_node with 
      | Flocal id ->
          (try Mid.find id s with _ -> f)
      | _ -> f_map (fun ty -> ty) aux f)

  let subst_local id f1 f2 =
    subst_locals (Mid.singleton id f1) f2

  let init_subst_tvar s = 
    let sty = { ty_subst_id with ts_v = s } in
    { f_subst_id with fs_ty = ty_subst sty }

  let subst_tvar s = 
    let sf  = init_subst_tvar s in
    f_subst sf

end



let f_if_simpl f1 f2 f3 =
  if f_equal f2 f3 then f2
  else if is_true f1 then f2 
  else if is_false f1 then f3
  else f_if f1 f2 f3

let can_subst f = 
  match f.f_node with
  | Fint _ | Flocal _ | Fpvar _ | Fop _ -> true
  | _ -> false

let f_let_simpl lp f1 f2 =
  match lp, f1.f_node with
  | LSymbol (id,_), _ ->
      let n = Mid.find_def 0 id (f_fv f2) in
      if n = 0 then f2 
      else if n = 1 || can_subst f1 then Fsubst.subst_local id f1 f2
      else f_let lp f1 f2 
  | LTuple ids, Ftuple fs ->
      let d, s = 
        List.fold_left2 (fun (d,s) (id,ty) f1 ->
          let n = Mid.find_def 0 id (f_fv f2) in
          if n = 0 then (d,s) 
          else if n = 1 || can_subst f1 then (d,Mid.add id f1 s)
          else (((id,ty),f1)::d,s)) ([],Mid.empty) ids fs in
      List.fold_left (fun f2 (id,f1) -> f_let (LSymbol id) f1 f2)
        (Fsubst.subst_locals s f2) d
  | LTuple _, _ -> f_let lp f1 f2 

let f_lets_simpl =
  (* FIXME : optimize this *)
  List.fold_right (fun (lp,f1) f2 -> f_let_simpl lp f1 f2) 

let f_forall_simpl b f = 
  let b = List.filter (fun (id,_) -> Mid.mem id (f_fv f)) b in
  f_forall b f 

let f_quant_simpl q b f =
  if q = Lforall then f_forall_simpl b f else f_exists b f

let f_not_simpl f = 
  if is_not f then destr_not f
  else if is_true f then f_false
  else if is_false f then f_true
  else f_not f

let f_and_simpl f1 f2 = 
  if is_true f1 then f2
  else if is_false f1 then f_false
  else if is_true f2 then f1
  else if is_false f2 then f_false 
  else f_and f1 f2

let f_anda_simpl f1 f2 = 
  if is_true f1 then f2
  else if is_false f1 then f_false
  else if is_true f2 then f1
  else if is_false f2 then f_false 
  else f_anda f1 f2

let f_or_simpl f1 f2 = 
  if is_true f1 then f_true
  else if is_false f1 then f2 
  else if is_true f2 then f_true
  else if is_false f2 then f1
  else f_or f1 f2

let f_ora_simpl f1 f2 = 
  if is_true f1 then f_true
  else if is_false f1 then f2 
  else if is_true f2 then f_true
  else if is_false f2 then f1
  else f_ora f1 f2

let f_imp_simpl f1 f2 = 
  if is_true f1 then f2
  else if is_false f1 || is_true f2 then f_true
  else if is_false f2 then f_not_simpl f1
  else f_imp f1 f2 
    (* FIXME : simplify x = f1 => f2 into x = f1 => f2{x<-f2} *)

let f_iff_simpl f1 f2 = 
  if f_equal f1 f2 then f_true
  else if is_true f1 then f2
  else if is_false f1 then f_not_simpl f2
  else if is_true f2 then f1
  else if is_false f2 then f_not_simpl f1
  else f_iff f1 f2

let f_eq_simpl f1 f2 = 
  if f_equal f1 f2 then f_true
  else f_eq f1 f2

let rec form_of_expr mem (e: expr) = 
  match e.e_node with
  | Eint n -> f_int n
  | Elocal id -> f_local id e.e_ty
  | Evar pv -> f_pvar pv e.e_ty mem
  | Eop (op,tys) -> f_op op tys e.e_ty
  | Eapp (e,es) -> 
      f_app (form_of_expr mem e) (List.map (form_of_expr mem) es) e.e_ty
  | Elet (lpt,e1,e2) -> f_let lpt (form_of_expr mem e1) (form_of_expr mem e2)
  | Etuple es -> f_tuple (List.map (form_of_expr mem) es)
  | Eif (e1,e2,e3) -> 
      f_if (form_of_expr mem e1) (form_of_expr mem e2) (form_of_expr mem e3)

type op_kind = 
  | OK_true
  | OK_false
  | OK_not
  | OK_and   of bool
  | OK_or    of bool
  | OK_imp
  | OK_iff
  | OK_eq
  | OK_other 

let op_kind = 
  let l = [EcCoreLib.p_true, OK_true; EcCoreLib.p_false, OK_false;
           EcCoreLib.p_not, OK_not; 
           EcCoreLib.p_anda, OK_and true; EcCoreLib.p_and, OK_and false; 
           EcCoreLib.p_ora,  OK_or true;  EcCoreLib.p_or,  OK_or  false; 
           EcCoreLib.p_imp, OK_imp; EcCoreLib.p_iff, OK_iff;
           EcCoreLib.p_eq, OK_eq] in
  let tbl = EcPath.Hp.create 11 in
  List.iter (fun (p,k) -> EcPath.Hp.add tbl p k) l;
  fun p -> try EcPath.Hp.find tbl p with _ -> OK_other

let is_logical_op op =
  match op_kind op with
  | OK_not | OK_and _ | OK_or _ | OK_imp | OK_iff | OK_eq -> true
  | _ -> false


 
