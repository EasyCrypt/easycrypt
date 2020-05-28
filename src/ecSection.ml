(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcTypes
open EcDecl
open EcModules

module Sid  = EcIdent.Sid
module Mid  = EcIdent.Mid
module MSym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
exception NoSectionOpened

type lvl = [`Local | `Global] * [`Axiom | `Lemma]

type locals = {
  lc_env       : EcEnv.env;
  lc_name      : symbol option;
  lc_lemmas    : (path * lvl) list * lvl Mp.t;
  lc_modules   : Sp.t;
  lc_abstracts : (EcIdent.t * module_type) list * Sid.t;
  lc_items     : EcTheory.ctheory_item list;
}

let env_of_locals (lc : locals) = lc.lc_env

let items_of_locals (lc : locals) = lc.lc_items

let is_local who p (lc : locals) =
  match who with
  | `Lemma  -> Mp.find_opt p (snd lc.lc_lemmas) |> omap fst = Some `Local
  | `Module -> Sp.mem p lc.lc_modules

exception UseLocal of EcPath.mpath

let rec use_mp_local (lc : locals) mp =
  begin match mp.m_top with
  | `Local _ -> ()
  | `Concrete (p, _) -> if is_local `Module p lc then raise (UseLocal mp)
  end;
  List.iter (use_mp_local lc) mp.m_args

let is_mp_local mp (lc : locals) =
  try use_mp_local lc mp; false
  with UseLocal _ -> true

let rec is_mp_abstract mp (lc : locals) =
  let toplocal =
    match mp.m_top with
    | `Concrete _ -> false
    | `Local i -> Sid.mem i (snd lc.lc_abstracts)
  in
    toplocal || (List.exists (is_mp_abstract^~ lc) mp.m_args)

let rec on_mpath_ty cb (ty : ty) =
  match ty.ty_node with
  | Tunivar _        -> ()
  | Tvar    _        -> ()
  | Tglob mp         -> cb mp
  | Ttuple tys       -> List.iter (on_mpath_ty cb) tys
  | Tconstr (_, tys) -> List.iter (on_mpath_ty cb) tys
  | Tfun (ty1, ty2)  -> List.iter (on_mpath_ty cb) [ty1; ty2]

let on_mpath_pv cb (pv : prog_var)=
  match pv with
  | PVglob xp -> cb xp.x_top
  | _         -> ()

let on_mpath_lp cb (lp : lpattern) =
  match lp with
  | LSymbol (_, ty) -> on_mpath_ty cb ty
  | LTuple  xs      -> List.iter (fun (_, ty) -> on_mpath_ty cb ty) xs
  | LRecord (_, xs) -> List.iter (on_mpath_ty cb |- snd) xs

let on_mpath_binding cb ((_, ty) : (EcIdent.t * ty)) =
  on_mpath_ty cb ty

let on_mpath_bindings cb bds =
  List.iter (on_mpath_binding cb) bds

let rec on_mpath_expr cb (e : expr) =
  let cbrec = on_mpath_expr cb in

  let rec fornode () =
    match e.e_node with
    | Eint   _            -> ()
    | Elocal _            -> ()
    | Equant (_, bds, e)  -> on_mpath_bindings cb bds; cbrec e
    | Evar   pv           -> on_mpath_pv cb pv
    | Elet   (lp, e1, e2) -> on_mpath_lp cb lp; List.iter cbrec [e1; e2]
    | Etuple es           -> List.iter cbrec es
    | Eop    (_, tys)     -> List.iter (on_mpath_ty cb) tys
    | Eapp   (e, es)      -> List.iter cbrec (e :: es)
    | Eif    (c, e1, e2)  -> List.iter cbrec [c; e1; e2]
    | Ematch (e, es, ty)  -> on_mpath_ty cb ty; List.iter cbrec (e :: es)
    | Eproj  (e, _)       -> cbrec e

  in on_mpath_ty cb e.e_ty; fornode ()

let on_mpath_lv cb (lv : lvalue) =
  let for1 (pv, ty) = on_mpath_pv cb pv; on_mpath_ty cb ty in

    match lv with
    | LvVar   pv  -> for1 pv
    | LvTuple pvs -> List.iter for1 pvs

let rec on_mpath_instr cb (i : instr)=
  match i.i_node with
  | Srnd (lv, e) | Sasgn (lv, e) ->
      on_mpath_lv cb lv;
      on_mpath_expr cb e

  | Sassert e ->
      on_mpath_expr cb e

  | Scall (lv, f, args) ->
      lv |> oiter (on_mpath_lv cb);
      cb f.x_top;
      List.iter (on_mpath_expr cb) args

  | Sif (e, s1, s2) ->
      on_mpath_expr cb e;
      List.iter (on_mpath_stmt cb) [s1; s2]

  | Swhile (e, s) ->
      on_mpath_expr cb e;
      on_mpath_stmt cb s

  | Sabstract _ -> ()

and on_mpath_stmt cb (s : stmt) =
  List.iter (on_mpath_instr cb) s.s_node

let on_mpath_memtype cb mt =
  EcMemory.mt_iter_ty (on_mpath_ty cb) mt

let on_mpath_memenv cb (m : EcMemory.memenv) =
  on_mpath_memtype cb (snd m)

let on_mpath_restr cb restr =
  Sx.iter (fun x -> cb x.x_top) restr.mr_xpaths.ur_neg;
  oiter (Sx.iter (fun x -> cb x.x_top)) restr.mr_xpaths.ur_pos;
  Sm.iter cb restr.mr_mpaths.ur_neg;
  oiter (Sm.iter cb) restr.mr_mpaths.ur_pos;
  Msym.iter (fun _ oi ->
      List.iter (fun x -> cb x.x_top) (OI.allowed oi)
    ) restr.mr_oinfos

let rec on_mpath_modty cb mty =
  List.iter (fun (_, mty) -> on_mpath_modty cb mty) mty.mt_params;
  List.iter cb mty.mt_args;
  on_mpath_restr cb mty.mt_restr

let on_mpath_gbinding cb b =
  match b with
  | EcFol.GTty ty ->
      on_mpath_ty cb ty
  | EcFol.GTmodty mty ->
      on_mpath_modty cb mty

  | EcFol.GTmem mt ->
    on_mpath_memtype cb mt

let on_mpath_gbindings cb b =
  List.iter (fun (_, b) -> on_mpath_gbinding cb b) b

let rec on_mpath_form cb (f : EcFol.form) =
  let cbrec = on_mpath_form cb in

  let rec fornode () =
    match f.EcFol.f_node with
    | EcFol.Fint      _            -> ()
    | EcFol.Flocal    _            -> ()
    | EcFol.Fquant    (_, b, f)    -> on_mpath_gbindings cb b; cbrec f
    | EcFol.Fif       (f1, f2, f3) -> List.iter cbrec [f1; f2; f3]
    | EcFol.Fmatch    (b, fs, ty)  -> on_mpath_ty cb ty; List.iter cbrec (b :: fs)
    | EcFol.Flet      (lp, f1, f2) -> on_mpath_lp cb lp; List.iter cbrec [f1; f2]
    | EcFol.Fop       (_, tys)     -> List.iter (on_mpath_ty cb) tys
    | EcFol.Fapp      (f, fs)      -> List.iter cbrec (f :: fs)
    | EcFol.Ftuple    fs           -> List.iter cbrec fs
    | EcFol.Fproj     (f, _)       -> cbrec f
    | EcFol.Fpvar     (pv, _)      -> on_mpath_pv  cb pv
    | EcFol.Fglob     (mp, _)      -> cb mp
    | EcFol.FhoareF   hf           -> on_mpath_hf  cb hf
    | EcFol.FhoareS   hs           -> on_mpath_hs  cb hs
    | EcFol.FcHoareF  chf          -> on_mpath_chf cb chf
    | EcFol.FcHoareS  chs          -> on_mpath_chs cb chs
    | EcFol.FequivF   ef           -> on_mpath_ef  cb ef
    | EcFol.FequivS   es           -> on_mpath_es  cb es
    | EcFol.FeagerF   eg           -> on_mpath_eg  cb eg
    | EcFol.FbdHoareS bhs          -> on_mpath_bhs cb bhs
    | EcFol.FbdHoareF bhf          -> on_mpath_bhf cb bhf
    | EcFol.Fcoe      coe          -> on_mpath_coe cb coe
    | EcFol.Fpr       pr           -> on_mpath_pr  cb pr

  and on_mpath_hf cb hf =
    on_mpath_form cb hf.EcFol.hf_pr;
    on_mpath_form cb hf.EcFol.hf_po;
    cb hf.EcFol.hf_f.x_top

  and on_mpath_hs cb hs =
    on_mpath_form cb hs.EcFol.hs_pr;
    on_mpath_form cb hs.EcFol.hs_po;
    on_mpath_stmt cb hs.EcFol.hs_s;
    on_mpath_memenv cb hs.EcFol.hs_m

  and on_mpath_ef cb ef =
    on_mpath_form cb ef.EcFol.ef_pr;
    on_mpath_form cb ef.EcFol.ef_po;
    cb ef.EcFol.ef_fl.x_top;
    cb ef.EcFol.ef_fr.x_top

  and on_mpath_es cb es =
    on_mpath_form cb es.EcFol.es_pr;
    on_mpath_form cb es.EcFol.es_po;
    on_mpath_stmt cb es.EcFol.es_sl;
    on_mpath_stmt cb es.EcFol.es_sr;
    on_mpath_memenv cb es.EcFol.es_ml;
    on_mpath_memenv cb es.EcFol.es_mr

  and on_mpath_eg cb eg =
    on_mpath_form cb eg.EcFol.eg_pr;
    on_mpath_form cb eg.EcFol.eg_po;
    cb eg.EcFol.eg_fl.x_top;
    cb eg.EcFol.eg_fr.x_top;
    on_mpath_stmt cb eg.EcFol.eg_sl;
    on_mpath_stmt cb eg.EcFol.eg_sr;

  and on_mpath_chf cb chf =
    on_mpath_form cb chf.EcFol.chf_pr;
    on_mpath_form cb chf.EcFol.chf_po;
    on_mpath_cost cb chf.EcFol.chf_co;
    cb chf.EcFol.chf_f.x_top

  and on_mpath_chs cb chs =
    on_mpath_form cb chs.EcFol.chs_pr;
    on_mpath_form cb chs.EcFol.chs_po;
    on_mpath_cost cb chs.EcFol.chs_co;
    on_mpath_stmt cb chs.EcFol.chs_s;
    on_mpath_memenv cb chs.EcFol.chs_m

  and on_mpath_bhf cb bhf =
    on_mpath_form cb bhf.EcFol.bhf_pr;
    on_mpath_form cb bhf.EcFol.bhf_po;
    on_mpath_form cb bhf.EcFol.bhf_bd;
    cb bhf.EcFol.bhf_f.x_top

  and on_mpath_bhs cb bhs =
    on_mpath_form cb bhs.EcFol.bhs_pr;
    on_mpath_form cb bhs.EcFol.bhs_po;
    on_mpath_form cb bhs.EcFol.bhs_bd;
    on_mpath_stmt cb bhs.EcFol.bhs_s;
    on_mpath_memenv cb bhs.EcFol.bhs_m

  and on_mpath_coe cb coe =
    on_mpath_form cb coe.EcFol.coe_pre;
    on_mpath_expr cb coe.EcFol.coe_e;
    on_mpath_memenv cb coe.EcFol.coe_mem;

  and on_mpath_pr cb pr =
    cb pr.EcFol.pr_fun.x_top;
    List.iter (on_mpath_form cb) [pr.EcFol.pr_event; pr.EcFol.pr_args]

  and on_mpath_cost cb cost =
    on_mpath_form cb cost.EcFol.c_self;
    Mx.iter (fun f c ->
        cb f.x_top;
        on_mpath_form cb c.EcFol.cb_called;
        on_mpath_form cb c.EcFol.cb_cost) cost.EcFol.c_calls

  in
    on_mpath_ty cb f.EcFol.f_ty; fornode ()

let rec on_mpath_module cb (me : module_expr) =
  match me.me_body with
  | ME_Alias (_, mp)  -> cb mp
  | ME_Structure st   ->
    on_mpath_mstruct cb st;

  | ME_Decl mty -> on_mpath_mdecl cb mty

and on_mpath_mdecl cb mty =
  on_mpath_modty cb mty;

and on_mpath_mstruct cb st =
  List.iter (on_mpath_mstruct1 cb) st.ms_body

and on_mpath_mstruct1 cb item =
  match item with
  | MI_Module   me -> on_mpath_module cb me
  | MI_Variable x  -> on_mpath_ty cb x.v_type
  | MI_Function f  -> on_mpath_fun cb f

and on_mpath_fun cb fun_ =
  on_mpath_fun_sig  cb fun_.f_sig;
  on_mpath_fun_body cb fun_.f_def

and on_mpath_fun_sig cb fsig =
  on_mpath_ty cb fsig.fs_arg;
  on_mpath_ty cb fsig.fs_ret

and on_mpath_fun_body cb fbody =
  match fbody with
  | FBalias xp -> cb xp.x_top
  | FBdef fdef -> on_mpath_fun_def cb fdef
  | FBabs oi   -> on_mpath_fun_oi  cb oi

and on_mpath_fun_def cb fdef =
  List.iter (fun v -> on_mpath_ty cb v.v_type) fdef.f_locals;
  on_mpath_stmt cb fdef.f_body;
  fdef.f_ret |> oiter (on_mpath_expr cb);
  on_mpath_uses cb fdef.f_uses

and on_mpath_uses cb uses =
  List.iter (fun x -> cb x.x_top) uses.us_calls;
  Sx.iter   (fun x -> cb x.x_top) uses.us_reads;
  Sx.iter   (fun x -> cb x.x_top) uses.us_writes

and on_mpath_fun_oi cb oi =
  List.iter (fun x -> cb x.x_top) (OI.allowed oi)

(* -------------------------------------------------------------------- *)

let check_use_local_or_abs lc mp =
  if is_mp_local mp lc || is_mp_abstract mp lc then
    raise (UseLocal mp)

let form_use_local f lc =
  try  on_mpath_form (use_mp_local lc) f; None
  with UseLocal mp -> Some mp

(* -------------------------------------------------------------------- *)
let form_use_local_or_abs f lc =
  try  on_mpath_form (check_use_local_or_abs lc) f; false
  with UseLocal _ -> true

(* -------------------------------------------------------------------- *)
let module_use_local_or_abs m lc =
  try  on_mpath_module (check_use_local_or_abs lc) m; false
  with UseLocal _ -> true

(* -------------------------------------------------------------------- *)
let opdecl_use_local_or_abs opdecl lc =
  let cb = check_use_local_or_abs lc in

  try
    on_mpath_ty cb opdecl.op_ty;
    (match opdecl.op_kind with
     | OB_pred None -> ()

     | OB_pred (Some (PR_Plain f)) ->
        on_mpath_form cb f

     | OB_pred (Some (PR_Ind pri)) ->
        on_mpath_bindings cb pri.pri_args;
        List.iter (fun ctor ->
          on_mpath_gbindings cb ctor.prc_bds;
          List.iter (on_mpath_form cb) ctor.prc_spec)
        pri.pri_ctors

     | OB_nott nott -> begin
        List.iter (on_mpath_ty cb |- snd) nott.ont_args;
        on_mpath_ty cb nott.ont_resty;
        on_mpath_expr cb nott.ont_body
       end


     | OB_oper None   -> ()
     | OB_oper Some b ->
         match b with
         | OP_Constr _ -> ()
         | OP_Record _ -> ()
         | OP_Proj   _ -> ()
         | OP_TC       -> ()
         | OP_Plain  (e, _) -> on_mpath_expr cb e
         | OP_Fix    f ->
           let rec on_mpath_branches br =
             match br with
             | OPB_Leaf (bds, e) ->
                 List.iter (on_mpath_bindings cb) bds;
                 on_mpath_expr cb e
             | OPB_Branch br ->
                 Parray.iter on_mpath_branch br

           and on_mpath_branch br =
             on_mpath_branches br.opb_sub

           in on_mpath_branches f.opf_branches);
    false

  with UseLocal _ -> true

(* -------------------------------------------------------------------- *)
let tydecl_use_local_or_abs tydecl lc =
  let cb = check_use_local_or_abs lc in

  try
    (match tydecl.tyd_type with
    | `Concrete ty -> on_mpath_ty cb ty
    | `Abstract _  -> ()

    | `Record (f, fds) ->
        on_mpath_form cb f;
        List.iter (on_mpath_ty cb |- snd) fds

    | `Datatype dt ->
        List.iter (List.iter (on_mpath_ty cb) |- snd) dt.tydt_ctors;
        List.iter (on_mpath_form cb) [dt.tydt_schelim; dt.tydt_schcase]);
    false

  with UseLocal _ -> true

(* -------------------------------------------------------------------- *)
let abstracts lc = lc.lc_abstracts

let generalize env lc (f : EcFol.form) =
  let axioms =
    List.pmap
      (fun (p, lvl) ->
         match lvl with `Global, `Axiom -> Some p | _ -> None)
      (fst lc.lc_lemmas)
  in

  match axioms with
  | [] ->
    let mods = Sid.of_list (List.map fst (fst lc.lc_abstracts)) in
      if   Mid.set_disjoint mods f.EcFol.f_fv
      then f
      else begin
        List.fold_right
          (fun (x, mty) f ->
             match Mid.mem x f.EcFol.f_fv with
             | false -> f
             | true  -> EcFol.f_forall [(x, EcFol.GTmodty mty)] f)
          (fst lc.lc_abstracts) f
      end

  | _ ->
    let f =
      let do1 p f =
        let ax = EcEnv.Ax.by_path p env in
        EcFol.f_imp ax.ax_spec f
      in
          List.fold_right do1 axioms f in
    let f =
      let do1 (x, mty) f =
        EcFol.f_forall [(x, EcFol.GTmodty mty)] f
      in
        List.fold_right do1 (fst lc.lc_abstracts) f
    in
      f

let elocals (env : EcEnv.env) (name : symbol option) : locals =
  { lc_env       = env;
    lc_name      = name;
    lc_lemmas    = ([], Mp.empty);
    lc_modules   = Sp.empty;
    lc_abstracts = ([], Sid.empty);
    lc_items     = []; }

type t = locals list

let initial : t = []

let in_section (cs : t) =
  match cs with [] -> false | _ -> true

let enter (env : EcEnv.env) (name : symbol option) (cs : t) : t =
  match List.ohead cs with
  | None    -> [elocals env name]
  | Some ec ->
    let ec =
      { ec with
          lc_items = [];
          lc_abstracts = ([], snd ec.lc_abstracts);
          lc_env = env;
          lc_name = name; }
    in
      ec :: cs

let exit (cs : t) =
  match cs with
  | [] -> raise NoSectionOpened
  | ec :: cs ->
      ({ ec with lc_items     = List.rev ec.lc_items;
                 lc_abstracts = fst_map List.rev ec.lc_abstracts;
                 lc_lemmas    = fst_map List.rev ec.lc_lemmas},
       cs)

let path (cs : t) : symbol option * path =
  match cs with
  | [] -> raise NoSectionOpened
  | ec :: _ -> (ec.lc_name, EcEnv.root ec.lc_env)

let opath (cs : t) =
  try Some (path cs) with NoSectionOpened -> None

let topenv (cs : t) : EcEnv.env =
  match List.rev cs with
  | [] -> raise NoSectionOpened
  | ec :: _ -> ec.lc_env

let locals (cs : t) : locals =
  match cs with
  | [] -> raise NoSectionOpened
  | ec :: _ -> ec

let olocals (cs : t) =
  try Some (locals cs) with NoSectionOpened -> None

let onactive (f : locals -> locals) (cs : t) =
  match cs with
  | []      -> raise NoSectionOpened
  | c :: cs -> (f c) :: cs

let add_local_mod (p : path) (cs : t) : t =
  onactive (fun ec -> { ec with lc_modules = Sp.add p ec.lc_modules }) cs

let add_lemma (p : path) (lvl : lvl) (cs : t) : t =
  onactive (fun ec ->
    let (axs, map) = ec.lc_lemmas in
      { ec with lc_lemmas = ((p, lvl) :: axs, Mp.add p lvl map) })
    cs

let add_item item (cs : t) : t =
  let doit ec = { ec with lc_items = item :: ec.lc_items } in
    onactive doit cs

let add_abstract id mt (cs : t) : t =
  let doit ec =
    match Sid.mem id (snd ec.lc_abstracts) with
    | true  -> assert false
    | false ->
        let (ids, set) = ec.lc_abstracts in
        let (ids, set) = ((id, mt) :: ids, Sid.add id set) in
          { ec with lc_abstracts = (ids, set) }
  in
    onactive doit cs
