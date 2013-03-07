(* -------------------------------------------------------------------- *)
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

type binding = (EcIdent.t * gty) list

let mstd   = EcIdent.create "$std"
let mpre   = EcIdent.create "$pre"
let mpost  = EcIdent.create "$post"
let mhr    = EcIdent.create "$hr"
let mleft  = EcIdent.create "$left"
let mright = EcIdent.create "$right"

type form = { 
  f_node : f_node;
  f_ty   : ty; 
  f_fv   : EcIdent.Sid.t;
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

  | Fhoare  of EcMemory.memenv * form * EcModules.function_def * form

  | FhoareF of form * EcPath.mpath * form  (* $pre / $post *)
  | FhoareS of EcMemory.memenv * form * stmt * form (* $hr / $hr *)

    (* $left,$right / $left,$right *)
  | FequivF of form * (EcPath.mpath * EcPath.mpath) * form
  | FequivS of form * (EcMemory.memenv * stmt) EcUtils.double * form

  | Fpr     of memory * EcPath.mpath * form list * (EcIdent.t * ty) * form (* $post *)

(* -------------------------------------------------------------------- *)
let fv f = f.f_fv 
let ty f = f.f_ty

(*-------------------------------------------------------------------- *)
let f_equal : form -> form -> bool = (==)
let f_hash f = f.f_tag 

let qt_equal : quantif -> quantif -> bool = (==)
let qt_hash = function
  | Lforall -> 0
  | Lexists -> 1

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

  let equal f1 f2 =
    match f1.f_node, f2.f_node with
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

    | Fhoare (mem1, pre1, s1, post1), Fhoare (mem2,pre2, s2, post2) ->
      (* FIXME: mem1, mem2 *)
        f_equal pre1 pre2
        && f_equal post1 post2
        && EcModules.fd_equal s1 s2

    | _, _ -> false

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

    | Fhoare(m, p, s, q) ->
      (* FIXME: m *)
        Why3.Hashcons.combine2
          (f_hash p) (f_hash q) (EcModules.fd_hash s)

  let tag n f = { f with f_tag = n }
end)

(* -------------------------------------------------------------------- *)
let fv_node = function
  | Fint _ | Fpvar _ | Fop _ -> Sid.empty
  | Flocal id -> Sid.singleton id
  | Fquant(_,b,f) -> 
      List.fold_left (fun s (id,_) -> Sid.remove id s) (fv f) b 
  | Fif(f1,f2,f3) -> 
      Sid.union (fv f1) (Sid.union (fv f2) (fv f3))
  | Flet(lp, f1, f2) ->
      let fv2 = 
        List.fold_left (fun s id -> Sid.remove id s) (fv f2) (ids_of_lpattern lp) in
      Sid.union (fv f1) fv2
  | Fapp(f,args) ->
      List.fold_left (fun s f -> Sid.union s (fv f)) (fv f) args
  | Ftuple args ->
      List.fold_left (fun s f -> Sid.union s (fv f)) Sid.empty args 
  | Fhoare (_,pre,_,post) ->
      Sid.union (fv pre) (fv post)

(* -------------------------------------------------------------------- *)
let mk_form node ty =  Hsform.hashcons 
    { f_node = node;
      f_ty   = ty;
      f_fv   = fv_node node;
      f_tag = -1; }

let ty_bool = tbool
let ty_int  = tint 
let ty_unit = tunit
let ty_real = treal

let f_op x tys ty = 
  mk_form (Fop(x,tys)) ty

let f_app f args ty = 
  match f.f_node with
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
  mk_form (Ftuple args) (ttuple (List.map ty args))

let f_if f1 f2 f3 = mk_form (Fif(f1,f2,f3)) f2.f_ty 

let f_let q f1 f2 = mk_form (Flet(q,f1,f2)) f2.f_ty (* FIXME rename binding *)

let f_quant q b f = 
  if b = [] then f else
  mk_form (Fquant(q,b,f)) ty_bool (* FIXME rename binding *)

let f_exists b f = f_quant Lexists b f 
let f_forall b f = f_quant Lforall b f

let f_hoare mem pre s post = mk_form (Fhoare(mem,pre,s,post)) ty_bool

let f_hoareF pre f post = mk_form (FhoareF(pre,f,post)) ty_bool
let f_equivF pre f1 f2 post = mk_form (FequivF(pre,(f1,f2),post)) ty_bool
let f_pr m f args res e = mk_form (Fpr(m,f,args,res,e)) ty_real

(* -------------------------------------------------------------------- *)
type destr_error =
  | Destr_and
  | Destr_or
  | Destr_imp
  | Destr_forall
  | Destr_exists

exception DestrError of destr_error

let destr_error e = raise (DestrError e)

let destr_and f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when 
      EcPath.p_equal p EcCoreLib.p_and || 
      EcPath.p_equal p EcCoreLib.p_anda -> 
      f1,f2
  | _ -> destr_error Destr_and 

let destr_or f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when 
      EcPath.p_equal p EcCoreLib.p_or || 
      EcPath.p_equal p EcCoreLib.p_ora -> 
      f1,f2
  | _ -> destr_error Destr_or 

let destr_imp f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when EcPath.p_equal p EcCoreLib.p_imp -> 
      f1,f2
  | _ -> destr_error Destr_imp 

let destr_forall1 f = 
  match f.f_node with
  | Fquant(Lforall,(x,t)::bd,p) -> x,t,f_forall bd p 
  | _ -> destr_error Destr_forall

let destr_exists1 f = 
  match f.f_node with
  | Fquant(Lexists,(x,t)::bd,p) -> x,t,f_exists bd p 
  | _ -> destr_error Destr_exists

(* -------------------------------------------------------------------- *)

let is_and f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},_) when EcPath.p_equal p EcCoreLib.p_and -> true
  | _ -> false 

let is_or f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},_) when EcPath.p_equal p EcCoreLib.p_or -> true
  | _ -> false 

let is_imp f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},_) when EcPath.p_equal p EcCoreLib.p_imp -> true
  | _ -> false

let is_forall f = 
  match f.f_node with
  | Fquant(Lforall,_,_) -> true
  | _ -> false

let is_exists f = 
  match f.f_node with
  | Fquant(Lexists,_,_) -> true
  | _ -> false
  
(* -------------------------------------------------------------------- *)
let map gt g f = 
  let map_gty = function
    | GTty ty -> GTty (gt ty)
    | _ as x  -> x
  in
    match f.f_node with
    | Fquant(q,b,f) ->
        f_quant q (List.map (fun (x,ty) -> x, map_gty ty) b) (g f)
    | Fif(f1,f2,f3) -> f_if (g f1) (g f2) (g f3)
    | Flet(lp,f1,f2) -> f_let lp (g f1) (g f2)
    | Fint i -> f_int i 
    | Flocal id -> f_local id (gt f.f_ty)
    | Fpvar(id,s) -> f_pvar id (gt f.f_ty) s
    | Fop(p,tys) -> f_op p (List.map gt tys) (gt f.f_ty)
    | Fapp(e, es) -> f_app (g e) (List.map g es) (gt f.f_ty)
    | Ftuple es -> f_tuple (List.map g es)
    | Fhoare(m,p,s,q) -> f_hoare m (g p) s (g q)

(* -------------------------------------------------------------------- *)
module Fsubst = struct
  let mapty onty = 
    let rec aux f = map onty aux f in
    aux

  let uni uidmap = mapty (Tuni.subst uidmap)

  let idty ty = ty 

  let subst_local id fid =
    let rec aux f = 
      match f.f_node with
      | Flocal id1 when EcIdent.id_equal id id1 -> fid
      | _ -> map idty aux f in
    aux

  let subst_tvar mtv = mapty (EcTypes.Tvar.subst mtv)
end

(* -------------------------------------------------------------------- *)
(*    Basic construction for building the logic                         *)

type local_kind =
  | LD_var   of ty * form option
  | LD_mem
  | LD_modty of EcModules.module_type
  | LD_hyp   of form  (* of type bool *)

type l_local = EcIdent.t * local_kind

type hyps = {
    h_tvar  : EcIdent.t list;
    h_local : l_local list;
  }

type l_decl = hyps * form

type prover_info = unit (* FIXME *)

type rule_name = 
  | RN_admit
  | RN_clear of EcIdent.t 
  | RN_prover of prover_info 

  | RN_local  of EcIdent.t
    (* H:f in G    ===>  E,G |- f  *)

  | RN_global of EcPath.path * ty list
    (* p: ['as], f in E  ==> E,G |- f{'as <- tys} *)

  | RN_exc_midle 
    (* E;G |- A \/ !A *)

  | RN_eq of EcIdent.t * form
    (* E;G |- t ~ u   E;G |- P(t)  ===> E;G |- P(u)  *)
    (* where ~ := = | <=>                            *)

  | RN_and_I 
    (* E;G |- A   E;G |- B   ===> E;G |- A /\ B *) 

  | RN_or_I  of bool  (* true = left; false = right *)
    (* E;G |- A_i   ===> E;G |- A_1 \/ A_2 *) 

  | RN_imp_I 
    (* E;G,A |- B   ===> E;G |- A => B *) 

  | RN_forall_I 
    (* E,x:T; G |- P ===> E;G |- forall (x:T), P *)

  | RN_exists_I of form
    (* E;G |- P{x<-t}  ===> E;G |- exists (x:T), P *)

  | RN_and_E 
    (* E;G |- A /\ B   E;G |- A => B => C                ===> E;G |- C *)

  | RN_or_E  
    (* E;G |- A \/ B   E;G |- A => C  E;G |- B => C      ===> E;G |- C *)
                
  | RN_imp_E 
    (* E;G |- A => B   E;G |- A  E;G |- B => C           ===> E;G |- C *)
                     
  | RN_forall_E of form 
    (* E;G |- forall x:t, P  E;G |- P(t) => C            ===> E;G |- C *)

  | RN_exists_E 
    (* E;G |- exists x:t, P  E;G |- forall x:t, P => C   ===> E;G |- C *)

  (* H rules *)
  | RN_app of (int * form)
  | RN_wp of int
  | RN_skip

type rule = (rule_name, l_decl) EcBaseLogic.rule
type judgment = (rule_name, l_decl) EcBaseLogic.judgment

module LDecl = struct
  type error = 
    | UnknownSymbol   of EcSymbols.symbol 
    | UnknownIdent    of EcIdent.t
    | NotAVariable    of EcIdent.t
    | NotAHypothesis  of EcIdent.t
    | CanNotClear     of EcIdent.t * EcIdent.t
    | CannotClearMem
    | CannotClearModTy
    | DuplicateIdent  of EcIdent.t
    | DuplicateSymbol of EcSymbols.symbol

  exception Ldecl_error of error

  let pp_error fmt = function
    | UnknownSymbol  s  -> 
        Format.fprintf fmt "Unknown symbol %s" s
    | UnknownIdent   id -> 
        Format.fprintf fmt "Unknown ident  %s, please report" 
          (EcIdent.tostring id)
    | NotAVariable   id ->
        Format.fprintf fmt "The symbol %s is not a variable" (EcIdent.name id)
    | NotAHypothesis id ->
        Format.fprintf fmt "The symbol %s is not a hypothesis" (EcIdent.name id)
    | CanNotClear (id1,id2) ->
        Format.fprintf fmt "Cannot clear %s it is used in %s"
          (EcIdent.name id1) (EcIdent.name id2)
    | CannotClearMem ->
        Format.fprintf fmt "Cannot clear memories"
    | CannotClearModTy ->
        Format.fprintf fmt "Cannot clear modules"
    | DuplicateIdent id ->
        Format.fprintf fmt "Duplicate ident %s, please report" 
          (EcIdent.tostring id)
    | DuplicateSymbol s ->
        Format.fprintf fmt 
          "An hypothesis or a variable named %s already exists" s

  let _ = EcPexception.register (fun fmt exn ->
    match exn with
    | Ldecl_error e -> pp_error fmt e 
    | _ -> raise exn)

  let error e = raise (Ldecl_error e)

  let lookup s hyps = 
    try 
      List.find (fun (id,_) -> s = EcIdent.name id) hyps.h_local 
    with _ -> error (UnknownSymbol s)

  let lookup_by_id id hyps = 
    try 
      List.assoc_eq EcIdent.id_equal id hyps.h_local 
    with _ -> error (UnknownIdent id)

  let get_hyp = function
    | (id, LD_hyp f) -> (id,f)
    | (id,_) -> error (NotAHypothesis id) 

  let get_var = function
    | (id, LD_var (ty,_)) -> (id, ty)
    | (id,_) -> error (NotAVariable id) 

  let lookup_hyp s hyps = get_hyp (lookup s hyps)

  let has_hyp s hyps = 
    try ignore(lookup_hyp s hyps); true
    with _ -> false

  let lookup_hyp_by_id id hyps = snd (get_hyp (id, lookup_by_id id hyps))

  let lookup_var s hyps = get_var (lookup s hyps) 

  let lookup_var_by_id id hyps = snd (get_var (id, lookup_by_id id hyps))

  let has_symbol s hyps = 
    try ignore(lookup s hyps); true with _ -> false 

  let has_ident id hyps = 
    try ignore(lookup_by_id id hyps); true with _ -> false 

  let check_id id hyps = 
    if has_ident id hyps then error (DuplicateIdent id)
    else 
      let s = EcIdent.name id in
      if s <> "_" && has_symbol s hyps then error (DuplicateSymbol s) 

  let add_local id ld hyps = 
    check_id id hyps;
    { hyps with h_local = (id,ld)::hyps.h_local }

  let clear id hyps = 
    let r,(_,ld), l = 
      try List.find_split (fun (id',_) -> EcIdent.id_equal id id') hyps.h_local
      with _ ->  error (UnknownIdent id) in
    let check_hyp id = function 
      | (id', LD_var (_, Some f)) when Sid.mem id f.f_fv ->
          error (CanNotClear(id,id'))
      | (id', LD_hyp f) when Sid.mem id f.f_fv -> 
          error (CanNotClear(id,id'))
      | _ -> () in
    begin match ld with
    | LD_var   _ -> List.iter (check_hyp id) r
    | LD_mem     -> error CannotClearMem
    | LD_modty _ -> error CannotClearModTy
    | LD_hyp   _ -> ()
    end;
      { hyps with h_local = List.rev_append r l }
end









(* SUBST_FORM *)

module Lvar = struct
  type t = Flocal of EcIdent.t | Fpvar of EcTypes.prog_var * EcMemory.memory

  let mk_local id = Flocal id

  let mk_pvar pv mem = Fpvar (pv,mem)

  let compare lv1 lv2 = compare lv1 lv2

  let eq_lvar lv1 lv2 = match lv1, lv2 with
    | Flocal id1, Flocal id2 ->
      EcIdent.id_equal id1 id2
    | Fpvar (pv1,mem1), Fpvar (pv2,mem2) ->
      EcTypes.pv_equal pv1 pv2 && EcMemory.mem_equal mem1 mem2 
    | _ -> false

end

module LVmap = Map.Make(Lvar)



module LVset = struct
  include Set.Make(Lvar)
  let pvars s = 
    let rec proj = function 
      | [] -> []
      | Lvar.Fpvar(p,mem) :: lvs -> (p,mem) :: (proj lvs)
      | _ :: lvs -> proj (lvs)
    in
    proj (elements s)
end



module Subst = struct

  exception ClashSubst

  type t = form LVmap.t
 
  let empty_subst = LVmap.empty

  let find lv subst = LVmap.find lv subst

  let add_subst lv e subst =
    try 
      ignore (find lv subst);
      raise ClashSubst
    with Not_found ->
      LVmap.add lv e subst

  let single_subst lv e = add_subst lv e empty_subst

  let remove_subst lv subst = LVmap.remove lv subst

  let rec flvar_form f_pvar f_local fm = 
    let flvar_form = flvar_form f_pvar f_local in
    match fm.f_node with
    | Fint _ | Fop _ -> LVset.empty
    | Fpvar (pv,mem) -> f_pvar pv mem
    | Flocal id -> f_local id
    | Fquant(_,bds,f) -> 
      List.fold_left (fun s (id,_) -> LVset.remove (Lvar.mk_local id) s) (flvar_form f) bds
    | Fif(f1,f2,f3) -> 
      LVset.union (flvar_form f1) (LVset.union (flvar_form f2) (flvar_form f3))
    | Flet(lp, f1, f2) ->
      let fv2 = 
        List.fold_left (fun s id -> LVset.remove (Lvar.mk_local id)  s) (flvar_form f2)
          (EcTypes.ids_of_lpattern lp) in
      LVset.union (flvar_form f1) fv2
    | Fapp(f,args) ->
      List.fold_left (fun s f -> LVset.union s (flvar_form f)) (flvar_form f) args
    | Ftuple args ->
      List.fold_left (fun s f -> LVset.union s (flvar_form f)) LVset.empty args 
    (* FIXME: ignoring program variables *)
    (* this pattern should never occur with a stratified formula-type *)
    | Fhoare (mem,pre,_,post) -> LVset.union (flvar_form pre) (flvar_form post)


      
  let fpvar_form = 
    flvar_form (fun pv mem -> LVset.singleton (Lvar.mk_pvar pv mem)) (fun _ -> LVset.empty)
  let flocal_form = flvar_form (fun _ _ -> LVset.empty) (fun id -> LVset.singleton (Lvar.mk_local id))

  let flvar_form = flvar_form (fun pv mem -> LVset.singleton (Lvar.mk_pvar pv mem))
    (fun id -> LVset.singleton (Lvar.mk_local id))

  let rec subst_form subst fm = match fm.f_node with
    | Fquant (qt, bds, fm) ->
      let subst' =
        (* I'm assuming binders are only identified by name, not both name and type *)
        let ids = List.map fst bds in
        List.fold_left (fun s id -> remove_subst (Lvar.mk_local id) s) subst ids
      in
      let bds',fm' = alpha_renaming bds fm subst' in
      f_quant qt bds' fm'

    | Fif (f1,f2,f3) ->
      f_if (subst_form subst f1) (subst_form subst f2) (subst_form subst f3)

    | Flet _ ->
      assert false (* FIXME: TODO *)
        
    | Flocal id -> 
      begin
        try LVmap.find (Lvar.mk_local id) subst 
        with Not_found -> fm
      end
    | Fpvar (pv,mem) -> 
      begin
        try LVmap.find (Lvar.mk_pvar pv mem) subst 
        with Not_found -> fm
      end

    | Fapp (fm',fms) -> f_app (subst_form subst fm') (List.map (subst_form subst) fms) fm.f_ty
    | Ftuple fms -> f_tuple (List.map (subst_form subst) fms)

    | Fop _ | Fint _ -> fm

    | Fhoare _ -> assert false

  and alpha_renaming bds fm subst' =
    let fv_in_fm = flvar_form fm in
    let new_fv_in_subst = 
      let f lv set =
        try
          LVset.union set (flvar_form (LVmap.find lv subst'))
        with Not_found -> set
      in
      LVset.fold f fv_in_fm LVset.empty
    in
    let f (bds,fm) (id,ty) =
      (* modules and memories cannot be subtituted ... *)
      match ty with
        | GTty ty when LVset.mem (Lvar.mk_local id) new_fv_in_subst ->
          let id' = EcIdent.fresh id in
          let fm' = subst_form (single_subst (Lvar.mk_local id) (f_local id' ty)) fm in
          (id',GTty ty)::bds, fm'
        | GTty _ | GTmodty _ | GTmem -> 
          ((id,ty)::bds,fm)
    in
    List.fold_left f ([],fm) (List.rev bds)


end

(* ENDOF SUBST_FORM *)



let rec form_of_exp mem (e: EcTypes.tyexpr) = 
  let ty = EcTypes.type_of_exp e in 
  match e.EcTypes.tye_node with
    | EcTypes.Eint n -> f_int n
    | EcTypes.Elocal id -> f_local id ty
    | EcTypes.Evar pv -> f_pvar pv ty mem
    | EcTypes.Eop (op,tys) -> f_op op tys ty
    | EcTypes.Eapp (e,es) -> 
      f_app (form_of_exp mem e) (List.map (form_of_exp mem) es) ty
    | EcTypes.Elet (lpt,e1,e2) -> f_let lpt (form_of_exp mem e1) (form_of_exp mem e2)
    | EcTypes.Etuple es -> f_tuple (List.map (form_of_exp mem) es)
    | EcTypes.Eif (e1,e2,e3) -> 
      f_if (form_of_exp mem e1) (form_of_exp mem e2) (form_of_exp mem e3)












