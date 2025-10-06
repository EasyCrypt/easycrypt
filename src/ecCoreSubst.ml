(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcPath
open EcUid
open EcAst
open EcTypes
open EcCoreFol
open EcCoreModules

(* -------------------------------------------------------------------- *)
type mod_extra = {
  mex_tglob : ty;
  mex_glob  : memory -> form;
}

type sc_instanciate = {
  sc_memtype : memtype;
  sc_mempred : mem_pr Mid.t;
  sc_expr    : expr Mid.t;
}

(* -------------------------------------------------------------------- *)
type f_subst = {
  fs_freshen : bool; (* true means freshen locals *)
  fs_u       : ty Muid.t;
  fs_v       : ty Mid.t;
  fs_mod     : EcPath.mpath Mid.t;
  fs_modex   : mod_extra Mid.t;
  fs_loc     : form Mid.t;
  fs_eloc    : expr Mid.t;
  fs_mem     : EcIdent.t Mid.t;
  (* free variables in the codom of the substitution *)
  fs_fv      : int Mid.t;
}

(* -------------------------------------------------------------------- *)
type 'a substitute = f_subst -> 'a -> 'a
type tx = before:form -> after:form -> form
type 'a tx_substitute = ?tx:tx -> 'a substitute
type 'a subst_binder = f_subst -> 'a -> f_subst * 'a

(* -------------------------------------------------------------------- *)
let mex_fv (mp : mpath) (ex : mod_extra) : uid Mid.t =
  let m = EcIdent.create "m" in
  fv_union
    (m_fv (ty_fv ex.mex_tglob) mp)
    (Mid.remove m (f_fv (ex.mex_glob m)))

(* -------------------------------------------------------------------- *)
let fv_Mid (type a)
  (fv : a -> uid Mid.t) (m  : a Mid.t) (s  : uid Mid.t) : uid Mid.t
=
  Mid.fold (fun _ t s -> fv_union s (fv t)) m s

(* -------------------------------------------------------------------- *)
let f_subst_init
      ?(freshen=false)
      ?(tu=Muid.empty)
      ?(tv=Mid.empty)
      ?(esloc=Mid.empty)
      () =
  let fv = Mid.empty in
  let fv = Muid.fold (fun _ t s -> fv_union s (ty_fv t)) tu fv in
  let fv = fv_Mid ty_fv tv fv in
  let fv = fv_Mid e_fv esloc fv in

  {
    fs_freshen  = freshen;
    fs_u        = tu;
    fs_v        = tv;
    fs_mod      = Mid.empty;
    fs_modex    = Mid.empty;
    fs_loc      = Mid.empty;
    fs_eloc     = esloc;
    fs_mem      = Mid.empty;
    fs_fv       = fv;
  }

let f_subst_id = f_subst_init ()

(* -------------------------------------------------------------------- *)
let bind_elocal (s : f_subst) (x : ident) (e : expr) : f_subst =
  let fs_eloc = Mid.add x e s.fs_eloc in
  let fs_fv   = fv_union (e_fv e) s.fs_fv in
  { s with fs_eloc; fs_fv; }

(* -------------------------------------------------------------------- *)
let bind_elocals (s : f_subst) (esloc : expr Mid.t) : f_subst =
  let merger (_ : ident) (oe1 : expr option) (oe2 : expr option) =
    match oe2 with None -> oe1 | Some _ -> oe2 in
  let fs_eloc = Mid.merge merger s.fs_eloc esloc in
  let fs_fv = fv_Mid e_fv esloc s.fs_fv in
  { s with fs_eloc; fs_fv; }

(* -------------------------------------------------------------------- *)
let f_bind_local (s : f_subst) (x : ident) (t : form) : f_subst =
  let fs_loc = Mid.add x t s.fs_loc in
  let fs_fv = fv_union (f_fv t) s.fs_fv in
  { s with fs_loc; fs_fv; }

(* -------------------------------------------------------------------- *)
let f_bind_mem (s : f_subst) (m1 : memory) (m2 : memory) : f_subst =
  let fs_mem = Mid.add m1 m2 s.fs_mem in
  let fs_fv = fv_add m2 s.fs_fv in
  { s with fs_mem; fs_fv; }

(* -------------------------------------------------------------------- *)
let bind_mod (s : f_subst) (x : ident) (mp : mpath) (ex : mod_extra) : f_subst =
  { s with
      fs_mod   = Mid.add x mp s.fs_mod;
      fs_modex = Mid.add x ex s.fs_modex;
      fs_fv    = fv_union (mex_fv mp ex) s.fs_fv; }

(* -------------------------------------------------------------------- *)
let f_bind_absmod (s : f_subst) (m1 : ident) (m2 : ident) : f_subst =
  bind_mod
    s m1 (EcPath.mident m2)
    { mex_tglob = tglob m2; mex_glob = (fun m -> (f_glob m2 m).inv); }

(* -------------------------------------------------------------------- *)
let f_bind_mod (s : f_subst) (x : ident) (mp : mpath) (norm_mod : memory -> form) : f_subst =
  match EcPath.mget_ident_opt mp with
  | None ->
    let ex = {
      mex_tglob = (norm_mod (EcIdent.create "&dummy")).f_ty;
      mex_glob  = norm_mod;
    } in
     bind_mod s x mp ex
  | Some id ->
    f_bind_absmod s x id

(* -------------------------------------------------------------------- *)
let f_bind_rename s xfrom xto ty =
  let xf = f_local xto ty in
  (* FIXME: This work just by luck ... *)
  let xe = e_local xto ty in
  let s  = f_bind_local s xfrom xf in
  (* Free variable already added by f_bind_local *)
  { s with fs_eloc = Mid.add xfrom xe s.fs_eloc; }

(* ------------------------------------------------------------------ *)
let f_rem_local (s : f_subst) (x : ident) : f_subst =
  { s with fs_loc  = Mid.remove x s.fs_loc;
           fs_eloc = Mid.remove x s.fs_eloc; }

(* -------------------------------------------------------------------- *)
let f_rem_mem (s : f_subst) (m : memory) : f_subst =
  assert (not (Mid.mem m s.fs_fv));
  { s with fs_mem = Mid.remove m s.fs_mem }

(* -------------------------------------------------------------------- *)
let f_rem_mod (s : f_subst) (x : ident) : f_subst =
  { s with
    fs_mod   = Mid.remove x s.fs_mod;
    fs_modex = Mid.remove x s.fs_modex; }

(* -------------------------------------------------------------------- *)
let is_ty_subst_id (s : f_subst) : bool =
     Mid.is_empty s.fs_mod
  && Muid.is_empty s.fs_u
  && Mid.is_empty s.fs_v

(* -------------------------------------------------------------------- *)
let rec ty_subst (s : f_subst) (ty : ty) : ty =
  match ty.ty_node with
  | Tglob m ->
       Mid.find_opt m s.fs_modex
    |> Option.map (fun ex -> ex.mex_tglob)
    |> Option.value ~default:ty
  | Tunivar id ->
       Muid.find_opt id s.fs_u
    |> Option.map (ty_subst s)
    |> Option.value ~default:ty
  | Tvar id ->
    Mid.find_def ty id s.fs_v
  | _ ->
    ty_map (ty_subst s) ty

(* -------------------------------------------------------------------- *)
let ty_subst (s : f_subst) : ty -> ty =
  if is_ty_subst_id s then identity else ty_subst s

(* -------------------------------------------------------------------- *)
let is_e_subst_id (s : f_subst) =
     not s.fs_freshen
  && is_ty_subst_id s
  && Mid.is_empty s.fs_eloc

(* -------------------------------------------------------------------- *)
let refresh (s : f_subst) (x : ident) : ident =
  if s.fs_freshen || Mid.mem x s.fs_fv then
    EcIdent.fresh x
  else x

(* -------------------------------------------------------------------- *)
let add_elocal (s : f_subst) ((x, t) as xt : ebinding) : f_subst * ebinding =
  let x' = refresh s x in
  let t' = ty_subst s t in
  let s = f_rem_local s x in
  if   x == x' && t == t'
  then (s, xt)
  else (bind_elocal s x (e_local x' t'), (x', t'))

(* -------------------------------------------------------------------- *)
let add_elocals = List.Smart.map_fold add_elocal

(* -------------------------------------------------------------------- *)
let x_subst (s : f_subst) (x : xpath) : xpath =
  EcPath.x_subst_abs s.fs_mod x

(* -------------------------------------------------------------------- *)
let pv_subst (s : f_subst) (pv : prog_var) : prog_var =
  pv_subst (x_subst s) pv

(* -------------------------------------------------------------------- *)
let elp_subst (s : f_subst) (lp : lpattern) : f_subst * lpattern =
  match lp with
  | LSymbol x ->
    let (s, x') = add_elocal s x in
    (s, LSymbol x')

  | LTuple xs ->
    let (s, xs') = add_elocals s xs in
    (s, LTuple xs')

  | LRecord (p, xs) ->
    let (s, xs') =
      List.Smart.map_fold
        (fun s ((x, t) as xt) ->
          match x with
          | None ->
              let t' = ty_subst s t in
              if t == t' then (s, xt) else (s, (x, t'))
          | Some x ->
              let (s, (x', t')) = add_elocal s (x, t) in
              if   x == x' && t == t'
              then (s, xt)
              else (s, (Some x', t')))
        s xs
    in
      (s, LRecord (p, xs'))

(* -------------------------------------------------------------------- *)
let rec e_subst (s : f_subst) (e : expr) : expr =
  match e.e_node with
  | Elocal id -> begin
    match Mid.find_opt id s.fs_eloc with
    | Some e' -> e'
    | None    -> e_local id (ty_subst s e.e_ty)
    end

  | Evar pv ->
    let pv' = pv_subst s pv in
    let ty' = ty_subst s e.e_ty in
    e_var pv' ty'

  | Eop (p, tys) ->
    let tys' = List.Smart.map (ty_subst s) tys in
    let ty'  = ty_subst s e.e_ty in
    e_op p tys' ty'

  | Elet (lp, e1, e2) ->
    let e1' = e_subst s e1 in
    let s, lp' = elp_subst s lp in
    let e2' = e_subst s e2 in
    e_let lp' e1' e2'

  | Equant (q, b, e1) ->
    let s, b' = add_elocals s b in
    let e1' = e_subst s e1 in
    e_quantif q b' e1'

  | _ -> e_map (ty_subst s) (e_subst s) e

(* -------------------------------------------------------------------- *)
let e_subst (s : f_subst) : expr -> expr=
  if is_e_subst_id s then
    identity
  else
    if   s.fs_freshen
    then e_subst s
    else He.memo 107 (e_subst s)

(* -------------------------------------------------------------------- *)
let rec s_subst_top (s : f_subst) : stmt -> stmt =
  let e_subst = e_subst s in

  let rec pvt_subst ((pv, ty) as p) : prog_var * ty =
    let pv' = pv_subst s pv in
    let ty' = ty_subst s ty in

    if   pv == pv' && ty == ty'
    then p
    else (pv', ty')

  and lv_subst (lv : lvalue) : lvalue =
    match lv with
    | LvVar pvt ->
      LvVar (pvt_subst pvt)

    | LvTuple pvs ->
      LvTuple (List.Smart.map pvt_subst pvs)

  and i_subst (i : instr) : instr =
    match i.i_node with
    | Sasgn (lv, e) ->
      i_asgn (lv_subst lv, e_subst e)

    | Srnd (lv, e) ->
      i_rnd (lv_subst lv, e_subst e)

    | Scall (olv, mp, args) ->
      let olv'  = olv |> OSmart.omap lv_subst in
      let mp'   = EcPath.x_subst_abs s.fs_mod mp in
      let args' = List.Smart.map e_subst args in

      i_call (olv', mp', args')

    | Sif (e, s1, s2) ->
      i_if (e_subst e, s_subst s1, s_subst s2)

    | Swhile(e, b) ->
      i_while (e_subst e, s_subst b)

    | Smatch (e, b) ->
      let forb ((xs, subs) as b1) =
        let s, xs' = add_elocals s xs in
        let subs'  = s_subst_top s subs in
        if xs == xs' && subs == subs' then b1 else (xs', subs')
      in

      i_match (e_subst e, List.Smart.map forb b)

    | Sassert e ->
      i_assert (e_subst e)

    | Sabstract _ ->
      i

  and s_subst (s : stmt) : stmt =
    stmt (List.Smart.map i_subst s.s_node)

  in s_subst

(* -------------------------------------------------------------------- *)
let s_subst (s : f_subst) : stmt -> stmt =
  if is_e_subst_id s then identity else s_subst_top s

(* -------------------------------------------------------------------- *)
module Fsubst = struct
  let is_subst_id (s : f_subst) : bool =
       s.fs_freshen = false
    && is_ty_subst_id s
    && Mid.is_empty   s.fs_loc
    && Mid.is_empty   s.fs_mem
    && Mid.is_empty   s.fs_eloc

  (* ------------------------------------------------------------------ *)
  let has_mem (s : f_subst) (x : ident) : bool =
      Mid.mem x s.fs_mem

  (* ------------------------------------------------------------------ *)
  let add_local (s : f_subst) ((x, t) as xt : ebinding) : f_subst * ebinding =
    let x' = refresh s x in
    let t' = ty_subst s t in
    let s  = f_rem_local s x in
    if   x == x' && t == t'
    then (s, xt)
    else (f_bind_rename s x x' t', (x', t'))

  (* ------------------------------------------------------------------ *)
  let add_locals : f_subst -> ebindings -> f_subst * ebindings =
    List.Smart.map_fold add_local

  (* ------------------------------------------------------------------ *)
  let lp_subst (s : f_subst) (lp : lpattern) : f_subst * lpattern =
    match lp with
    | LSymbol x ->
      let (s, x') = add_local s x in
      if x == x' then (s, lp) else (s, LSymbol x')

    | LTuple xs ->
      let (s, xs') = add_locals s xs in
      if xs == xs' then (s, lp) else (s, LTuple xs')

    | LRecord (p, xs) ->
      let (s, xs') =
        List.Smart.map_fold
          (fun s ((x, t) as xt) ->
            match x with
            | None ->
                let t' = ty_subst s t in
                  if t == t' then (s, xt) else (s, (x, t'))
            | Some x ->
                let (s, (x', t')) = add_local s (x, t) in
                  if   x == x' && t == t'
                  then (s, xt)
                  else (s, (Some x', t')))
          s xs
      in
        if xs == xs' then (s, lp) else (s, LRecord (p, xs'))

  (* ------------------------------------------------------------------ *)
  let m_subst (s : f_subst) (m : memory) : memory =
    Mid.find_def m m s.fs_mem

  (* -------------------------------------------------------------------- *)
  let me_subst (s : f_subst) (me : memenv) : memenv =
    EcMemory.me_subst s.fs_mem (ty_subst s) me

  (* ------------------------------------------------------------------ *)
  let rec f_subst ~(tx : tx) (s : f_subst) (fp : form) : form =
    tx ~before:fp ~after:(match fp.f_node with
    | Fquant (q, b, f) ->
      let s, b' = add_bindings s b in
      let f' = f_subst ~tx s f in
      f_quant q b' f'

    | Flet (lp, f1, f2) ->
      let f1' = f_subst ~tx s f1 in
      let s, lp' = lp_subst s lp in
      let f2' = f_subst ~tx s f2 in
      f_let lp' f1' f2'

    | Flocal id -> begin
      match Mid.find_opt id s.fs_loc with
      | Some f ->
        f
      | None ->
        let ty' = ty_subst s fp.f_ty in
        f_local id ty'
    end

    | Fop (p, tys) ->
      let ty'  = ty_subst s fp.f_ty in
      let tys' = List.Smart.map (ty_subst s) tys in
      f_op p tys' ty'

    | Fpvar (pv, m) ->
      let pv' = pv_subst s pv in
      let m'  = m_subst s m in
      let ty' = ty_subst s fp.f_ty in
      (f_pvar pv' ty' m').inv

    | Fglob (mid, m) ->
      let m'  = m_subst s m in
      begin match Mid.find_opt mid s.fs_mod with
      | None -> (f_glob mid m').inv
      | Some _ -> (Mid.find mid s.fs_modex).mex_glob m'
      end

    | FhoareF hf ->
      let hf_f   = x_subst s hf.hf_f in
      let (s, m) = add_m_binding s hf.hf_m in
      let hf_pr  = f_subst ~tx s (hf_pr hf).inv in
      let hf_po  = f_subst ~tx s (hf_po hf).inv in
      f_hoareF {m;inv=hf_pr} hf_f {m;inv=hf_po}

    | FhoareS hs ->
      let hs_s    = s_subst s hs.hs_s in
      let s, (m, mt) = add_me_binding s hs.hs_m in
      let hs_pr   = f_subst ~tx s (hs_pr hs).inv in
      let hs_po   = f_subst ~tx s (hs_po hs).inv in
      f_hoareS mt {m;inv=hs_pr} hs_s {m;inv=hs_po}

    | FeHoareF hf ->
      let hf_f  = x_subst s hf.ehf_f in
      let (s, m) = add_m_binding s hf.ehf_m in
      let hf_pr = f_subst ~tx s (ehf_pr hf).inv in
      let hf_po = f_subst ~tx s (ehf_po hf).inv in
      f_eHoareF {m;inv=hf_pr} hf_f {m;inv=hf_po}

    | FeHoareS hs ->
      let hs_s    = s_subst s hs.ehs_s in
      let s, (m, mt) = add_me_binding s hs.ehs_m in
      let hs_pr   = f_subst ~tx s (ehs_pr hs).inv in
      let hs_po   = f_subst ~tx s (ehs_po hs).inv in
      f_eHoareS mt {m;inv=hs_pr} hs_s {m;inv=hs_po}

    | FbdHoareF hf ->
      let hf_f  = x_subst s hf.bhf_f in
      let (s, m) = add_m_binding s hf.bhf_m in
      let hf_pr = f_subst ~tx s (bhf_pr hf).inv in
      let hf_po = f_subst ~tx s (bhf_po hf).inv in
      let hf_bd = f_subst ~tx s (bhf_bd hf).inv in
      f_bdHoareF {m;inv=hf_pr} hf_f {m;inv=hf_po} hf.bhf_cmp {m;inv=hf_bd}

    | FbdHoareS hs ->
      let hs_s = s_subst s hs.bhs_s in
      let s, hs_m = add_me_binding s hs.bhs_m in
      let m = fst hs_m in
      let hs_pr = f_subst ~tx s (bhs_pr hs).inv in
      let hs_po = f_subst ~tx s (bhs_po hs).inv in
      let hs_bd = f_subst ~tx s (bhs_bd hs).inv in
      f_bdHoareS (snd hs_m) {m;inv=hs_pr} hs_s {m;inv=hs_po} hs.bhs_cmp {m;inv=hs_bd}

    | FequivF ef ->
      let ef_fl = x_subst s ef.ef_fl in
      let ef_fr = x_subst s ef.ef_fr in
      let (s, ml) = add_m_binding s ef.ef_ml in
      let (s, mr) = add_m_binding s ef.ef_mr in
      let ef_pr = f_subst ~tx s (ef_pr ef).inv in
      let ef_po = f_subst ~tx s (ef_po ef).inv in
      f_equivF {ml;mr;inv=ef_pr} ef_fl ef_fr {ml;mr;inv=ef_po}

    | FequivS es ->
      let es_sl = s_subst s es.es_sl in
      let es_sr = s_subst s es.es_sr in
      let s, (ml, mlt) = add_me_binding s es.es_ml in
      let s, (mr, mrt) = add_me_binding s es.es_mr in
      let es_pr = f_subst ~tx s (es_pr es).inv in
      let es_po = f_subst ~tx s (es_po es).inv in
      f_equivS mlt mrt {ml;mr;inv=es_pr} es_sl es_sr {ml;mr;inv=es_po}

    | FeagerF eg ->
      let eg_fl = x_subst s eg.eg_fl in
      let eg_fr = x_subst s eg.eg_fr in
      let eg_sl = s_subst s eg.eg_sl in
      let eg_sr = s_subst s eg.eg_sr in
      let (s, ml) = add_m_binding s eg.eg_ml in
      let (s, mr) = add_m_binding s eg.eg_mr in
      let eg_pr = f_subst ~tx s (eg_pr eg).inv in
      let eg_po = f_subst ~tx s (eg_po eg).inv in
      f_eagerF {ml;mr;inv=eg_pr} eg_sl eg_fl eg_fr eg_sr {ml;mr;inv=eg_po}

    | Fpr pr ->
      let pr_mem   = m_subst s pr.pr_mem in
      let pr_fun   = x_subst s pr.pr_fun in
      let pr_args  = f_subst ~tx s pr.pr_args in
      let ev = pr.pr_event in
      let (s, m) = add_m_binding s ev.m in
      let pr_event = f_subst ~tx s ev.inv in

      f_pr pr_mem pr_fun pr_args {m;inv=pr_event}

    | _ ->
      f_map (ty_subst s) (f_subst ~tx s) fp)

  (* ------------------------------------------------------------------ *)
  and oi_subst (s : f_subst) (oi : PreOI.t) : PreOI.t =
    PreOI.mk (List.map (x_subst s) (PreOI.allowed oi))

  (* ------------------------------------------------------------------ *)
  and mr_subst (s : f_subst) (mr : mod_restr) : mod_restr =
    let sx = x_subst s in
    let sm = EcPath.m_subst_abs s.fs_mod in
    let subst_ (xs, ms) = (Sx.map sx xs, Sm.map sm ms) in
    ur_app subst_ mr

  (* ------------------------------------------------------------------ *)
  and mp_subst (s : f_subst) (mp : mpath) : mpath =
    EcPath.m_subst_abs s.fs_mod mp

  (* ------------------------------------------------------------------ *)
  and mty_subst (s : f_subst) (mty : module_type) : module_type =
    let s, mt_params = add_mod_params s mty.mt_params in
    let mt_name = mty.mt_name in
    let mt_args = List.map (mp_subst s) mty.mt_args in
    { mt_params; mt_name; mt_args; }

  (* ------------------------------------------------------------------ *)
  and mty_mr_subst (s : f_subst) ((mty, mr) : mty_mr) : mty_mr =
    mty_subst s mty, mr_subst s mr

  (* ------------------------------------------------------------------ *)
  and gty_subst (s : f_subst) (gty : gty) : gty =
    if is_subst_id s then gty else

    match gty with
    | GTty ty ->
      let ty' = ty_subst s ty in
      if ty == ty' then gty else GTty ty'

    | GTmodty p ->
      let p' = mty_mr_subst s p in
      if p == p' then gty else GTmodty p'

    | GTmem mt ->
      let mt' = EcMemory.mt_subst (ty_subst s) mt in
      if mt == mt' then gty else GTmem mt'

  (* ------------------------------------------------------------------ *)
  and add_binding (s : f_subst) ((x, gty) as xt : binding) : f_subst * binding =
    let gty' = gty_subst s gty in
    let x'   = refresh s x in

    if x == x' && gty == gty' then
      let s = match gty with
        | GTty    _ -> f_rem_local s x
        | GTmodty _ -> f_rem_mod   s x
        | GTmem   _ -> f_rem_mem   s x
      in
        (s, xt)
    else
      let s = match gty' with
        | GTty   ty -> f_bind_rename s x x' ty
        | GTmodty _ -> f_bind_absmod s x x'
        | GTmem   _ -> f_bind_mem s x x'
      in
        (s, (x', gty'))

  (* ------------------------------------------------------------------ *)
  and add_bindings (s : f_subst) : bindings -> f_subst * bindings =
    List.map_fold add_binding s

  (* ------------------------------------------------------------------ *)
  and add_mod_params (s : f_subst) (params : _) =
    (* We rely on add_bindings, hence the injection of parameters as
     * bindings. We use the mr_full restriction set. Any other choice
     * would have been equivalent as this set is not used by
     * the function add_bindings. *)
    let s, params =
      add_bindings s
        (List.map (fun (x, mty) -> (x, GTmodty (mty, EcModules.mr_full))) params) in
    let params = List.map (fun (x, gty) -> x, fst (as_modty gty)) params in
    s, params

  (* ------------------------------------------------------------------ *)
  and add_m_binding (s : f_subst) (m : memory) : f_subst * memory =
    let m'  = refresh s m in
    if m == m' then
      let s = f_rem_mem s m in
      (s, m)
    else
      let s = f_bind_mem s m m' in
      (s, m')
  (* ------------------------------------------------------------------ *)

  and add_me_binding (s : f_subst) ((x, mt) as me : memenv) : f_subst * memenv =
    let mt' = EcMemory.mt_subst (ty_subst s) mt in
    let x'  = refresh s x in
    if x == x' && mt == mt' then
      let s = f_rem_mem s x in
      (s, me)
    else
      let s = f_bind_mem s x x' in
      (s, (x', mt'))

  (* ------------------------------------------------------------------ *)
  (* Wrapper functions                                                  *)
  (* ------------------------------------------------------------------ *)
  let x_subst = x_subst
  let pv_subst = pv_subst

  let f_subst_init  = f_subst_init
  let f_subst_id    = f_subst_id

  let f_bind_local  = f_bind_local
  let f_bind_mem    = f_bind_mem
  let f_bind_absmod = f_bind_absmod
  let f_bind_mod    = f_bind_mod
  let f_bind_rename = f_bind_rename

  let add_binding  = add_binding
  let add_bindings = add_bindings

  (* ------------------------------------------------------------------ *)
  let f_subst ?(tx = fun ~before:_ ~after:f -> f) s =
    if is_subst_id s then identity else f_subst ~tx s

  let e_subst = e_subst
  let s_subst = s_subst

  let gty_subst = gty_subst
  let mr_subst = mr_subst
  let mty_subst = mty_subst
  let oi_subst  = oi_subst
  let mty_mr_subst = mty_mr_subst

  (* ------------------------------------------------------------------ *)
  let f_subst_local (x : ident) (t : form) : form -> form =
    let s = f_bind_local f_subst_id x t in
    fun f -> if Mid.mem x f.f_fv then f_subst s f else f

  (* ------------------------------------------------------------------ *)
  let f_subst_mem (m1 : memory) (m2 : memory) : form -> form =
    let s = f_bind_mem f_subst_id m1 m2 in
    fun f -> if Mid.mem m1 f.f_fv then f_subst s f else f

  (* ------------------------------------------------------------------ *)
  let init_subst_tvar ~(freshen : bool) (s : ty Mid.t) : f_subst =
    f_subst_init ~freshen ~tv:s ()

  let f_subst_tvar ~(freshen : bool) (s : ty Mid.t) : form -> form =
    f_subst (init_subst_tvar ~freshen s)
end

(* -------------------------------------------------------------------- *)
module Tuni = struct
  let subst (uidmap : ty Muid.t) : f_subst =
    f_subst_init ~tu:uidmap ()

  let subst1 ((id, t) : uid * ty) : f_subst =
    subst (Muid.singleton id t)

  let subst_dom (uidmap : ty Muid.t) (dom : dom) : dom =
    List.map (ty_subst (subst uidmap)) dom

  let occurs (u : uid) : ty -> bool =
    let rec aux t =
      match t.ty_node with
      | Tunivar u' -> uid_equal u u'
      | _ -> ty_sub_exists aux t in
    aux

  let univars : ty -> Suid.t =
    let rec doit univars t =
      match t.ty_node with
      | Tunivar uid -> Suid.add uid univars
      | _ -> ty_fold doit univars t

    in fun t -> doit Suid.empty t

  let rec fv_rec (fv : Suid.t) (t : ty) : Suid.t =
    match t.ty_node with
    | Tunivar id -> Suid.add id fv
    | _ -> ty_fold fv_rec fv t

  let fv (ty : ty) : Suid.t =
    fv_rec Suid.empty ty
end

(* -------------------------------------------------------------------- *)
module Tvar = struct
  let subst (s : ty Mid.t) (ty : ty) : ty =
    ty_subst { f_subst_id with fs_v = s } ty

  let subst1 ((id, t) : ebinding) (ty : ty) : ty =
    subst (Mid.singleton id t) ty

  let init (lv : ident list) (lt : ty list) : ty Mid.t =
    assert (List.length lv = List.length lt);
    List.fold_left2 (fun s v t -> Mid.add v t s) Mid.empty lv lt

  let f_subst ~(freshen : bool) (lv : ident list) (lt : ty list) : form -> form =
    Fsubst.f_subst_tvar ~freshen (init lv lt)
end
