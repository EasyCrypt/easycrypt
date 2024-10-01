(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcAst
open EcTypes
open EcDecl
open EcModules
open EcTheory
open EcFol

module Sid  = EcIdent.Sid
module Mid  = EcIdent.Mid
module MSym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type cbarg = [
  | `Type       of path
  | `Op         of path
  | `Ax         of path
  | `Module     of mpath
  | `ModuleType of path
  | `Typeclass  of path
  | `Instance   of tcinstance
]

type cb = cbarg -> unit

(* -------------------------------------------------------------------- *)
type dep_error =
  { e_env : EcEnv.env;
    e_who : locality * cbarg;
    e_dep : locality * cbarg;
  }

let pp_cbarg env fmt (who : cbarg) =
  let ppe = EcPrinting.PPEnv.ofenv env in
  match who with
  | `Type p -> Format.fprintf fmt "type %a" (EcPrinting.pp_tyname ppe) p
  | `Op   p -> Format.fprintf fmt "operator %a" (EcPrinting.pp_opname ppe) p
  | `Ax   p -> Format.fprintf fmt "lemma/axiom %a" (EcPrinting.pp_axname ppe) p
  | `Module mp ->
    let ppe =
      match mp.m_top with
      | `Local id -> EcPrinting.PPEnv.add_locals ppe [id]
      | _ -> ppe in
    Format.fprintf fmt "module %a" (EcPrinting.pp_topmod ppe) mp
  | `ModuleType p ->
    let mty = EcEnv.ModTy.modtype p env in
    Format.fprintf fmt "module type %a" (EcPrinting.pp_modtype1 ppe) mty
  | `Typeclass p ->
    Format.fprintf fmt "typeclass %a" (EcPrinting.pp_tcname ppe) p
  | `Instance tci ->
    match tci with
    | `Ring _ -> Format.fprintf fmt "ring instance"
    | `Field _ -> Format.fprintf fmt "field instance"
    | `General _ -> Format.fprintf fmt "instance"

let pp_locality fmt = function
  | `Local -> Format.fprintf fmt "local"
  | `Global -> ()
  | `Declare -> Format.fprintf fmt "declared"

let pp_lc_cbarg env fmt (lc, who) =
  Format.fprintf fmt "%a %a" pp_locality lc (pp_cbarg env) who

let pp_error fmt err =
  let pp = pp_lc_cbarg err.e_env in
  Format.fprintf fmt "%a cannot depend on %a" pp err.e_who pp err.e_dep

(* -------------------------------------------------------------------- *)
exception SectionError of string

let pp_section_error fmt exn =
  match exn with
  | SectionError s ->
      Format.fprintf fmt "%s" s

  | _ -> raise exn

let _ = EcPException.register pp_section_error

let hierror fmt =
  let buf  = Buffer.create 127 in
  let bfmt = Format.formatter_of_buffer buf in

  Format.kfprintf
    (fun _ ->
      Format.pp_print_flush bfmt ();
      raise (SectionError (Buffer.contents buf)))
    bfmt fmt

(* -------------------------------------------------------------------- *)
let rec on_mp (cb : cb) (mp : mpath) =
  let f = m_functor mp in
  cb (`Module f);
  List.iter (on_mp cb) mp.m_args

let on_xp (cb : cb) (xp : xpath) =
  on_mp cb xp.x_top

let rec on_ty (cb : cb) (ty : ty) =
  match ty.ty_node with
  | Tunivar _        -> ()
  | Tvar    _        -> ()
  | Tglob   _        -> ()
  | Ttuple tys       -> List.iter (on_ty cb) tys
  | Tconstr (p, tys) -> cb (`Type p); List.iter (on_ty cb) tys
  | Tfun (ty1, ty2)  -> List.iter (on_ty cb) [ty1; ty2]

let on_pv (cb : cb) (pv : prog_var)=
  match pv with
  | PVglob xp -> on_xp cb xp
  | _         -> ()

let on_lp (cb : cb) (lp : lpattern) =
  match lp with
  | LSymbol (_, ty) -> on_ty cb ty
  | LTuple  xs      -> List.iter (fun (_, ty) -> on_ty cb ty) xs
  | LRecord (_, xs) -> List.iter (on_ty cb |- snd) xs

let on_binding (cb : cb) ((_, ty) : (EcIdent.t * ty)) =
  on_ty cb ty

let on_bindings (cb : cb) (bds : (EcIdent.t * ty) list) =
  List.iter (on_binding cb) bds

let rec on_expr (cb : cb) (e : expr) =
  let cbrec = on_expr cb in

  let fornode () =
    match e.e_node with
    | Eint   _            -> ()
    | Elocal _            -> ()
    | Equant (_, bds, e)  -> on_bindings cb bds; cbrec e
    | Evar   pv           -> on_pv cb pv
    | Elet   (lp, e1, e2) -> on_lp cb lp; List.iter cbrec [e1; e2]
    | Etuple es           -> List.iter cbrec es
    | Eop    (p, tys)     -> cb (`Op p); List.iter (on_ty cb) tys
    | Eapp   (e, es)      -> List.iter cbrec (e :: es)
    | Eif    (c, e1, e2)  -> List.iter cbrec [c; e1; e2]
    | Ematch (e, es, ty)  -> on_ty cb ty; List.iter cbrec (e :: es)
    | Eproj  (e, _)       -> cbrec e

  in on_ty cb e.e_ty; fornode ()

let on_lv (cb : cb) (lv : lvalue) =
  let for1 (pv, ty) = on_pv cb pv; on_ty cb ty in

    match lv with
    | LvVar   pv  -> for1 pv
    | LvTuple pvs -> List.iter for1 pvs

let rec on_instr (cb : cb) (i : instr)=
  match i.i_node with
  | Srnd (lv, e) | Sasgn (lv, e) ->
      on_lv cb lv;
      on_expr cb e

  | Sassert e ->
      on_expr cb e

  | Scall (lv, f, args) ->
      lv |> oiter (on_lv cb);
      on_xp cb f;
      List.iter (on_expr cb) args

  | Sif (e, s1, s2) ->
      on_expr cb e;
      List.iter (on_stmt cb) [s1; s2]

  | Swhile (e, s) ->
      on_expr cb e;
      on_stmt cb s

  | Smatch (e, b) ->
      let forb (bs, s) =
        List.iter (on_ty cb |- snd) bs;
        on_stmt cb s
      in on_expr cb e; List.iter forb b

  | Sabstract _ -> ()

and on_stmt (cb : cb) (s : stmt) =
  List.iter (on_instr cb) s.s_node

let on_memtype cb mt =
  EcMemory.mt_iter_ty (on_ty cb) mt

let on_memenv cb (m : EcMemory.memenv) =
  on_memtype cb (snd m)

let rec on_form (cb : cb) (f : EcFol.form) =
  let cbrec = on_form cb in

  let rec fornode () =
    match f.EcAst.f_node with
    | EcAst.Fint      _            -> ()
    | EcAst.Flocal    _            -> ()
    | EcAst.Fquant    (_, b, f)    -> on_gbindings cb b; cbrec f
    | EcAst.Fif       (f1, f2, f3) -> List.iter cbrec [f1; f2; f3]
    | EcAst.Fmatch    (b, fs, ty)  -> on_ty cb ty; List.iter cbrec (b :: fs)
    | EcAst.Flet      (lp, f1, f2) -> on_lp cb lp; List.iter cbrec [f1; f2]
    | EcAst.Fop       (p, tys)     -> cb (`Op p); List.iter (on_ty cb) tys
    | EcAst.Fapp      (f, fs)      -> List.iter cbrec (f :: fs)
    | EcAst.Ftuple    fs           -> List.iter cbrec fs
    | EcAst.Fproj     (f, _)       -> cbrec f
    | EcAst.Fpvar     (pv, _)      -> on_pv  cb pv
    | EcAst.Fglob     _            -> ()
    | EcAst.FhoareF   hf           -> on_hf  cb hf
    | EcAst.FhoareS   hs           -> on_hs  cb hs
    | EcAst.FeHoareF  hf           -> on_ehf  cb hf
    | EcAst.FeHoareS  hs           -> on_ehs  cb hs
    | EcAst.FequivF   ef           -> on_ef  cb ef
    | EcAst.FequivS   es           -> on_es  cb es
    | EcAst.FeagerF   eg           -> on_eg  cb eg
    | EcAst.FbdHoareS bhs          -> on_bhs cb bhs
    | EcAst.FbdHoareF bhf          -> on_bhf cb bhf
    | EcAst.Fpr       pr           -> on_pr  cb pr

  and on_hf cb hf =
    on_form cb hf.EcAst.hf_pr;
    on_form cb hf.EcAst.hf_po;
    on_xp cb hf.EcAst.hf_f

  and on_hs cb hs =
    on_form cb hs.EcAst.hs_pr;
    on_form cb hs.EcAst.hs_po;
    on_stmt cb hs.EcAst.hs_s;
    on_memenv cb hs.EcAst.hs_m

  and on_ef cb ef =
    on_form cb ef.EcAst.ef_pr;
    on_form cb ef.EcAst.ef_po;
    on_xp cb ef.EcAst.ef_fl;
    on_xp cb ef.EcAst.ef_fr

  and on_es cb es =
    on_form cb es.EcAst.es_pr;
    on_form cb es.EcAst.es_po;
    on_stmt cb es.EcAst.es_sl;
    on_stmt cb es.EcAst.es_sr;
    on_memenv cb es.EcAst.es_ml;
    on_memenv cb es.EcAst.es_mr

  and on_eg cb eg =
    on_form cb eg.EcAst.eg_pr;
    on_form cb eg.EcAst.eg_po;
    on_xp cb eg.EcAst.eg_fl;
    on_xp cb eg.EcAst.eg_fr;
    on_stmt cb eg.EcAst.eg_sl;
    on_stmt cb eg.EcAst.eg_sr;

  and on_ehf cb hf =
    on_form cb hf.EcAst.ehf_pr;
    on_form cb hf.EcAst.ehf_po;
    on_xp cb hf.EcAst.ehf_f

  and on_ehs cb hs =
    on_form cb hs.EcAst.ehs_pr;
    on_form cb hs.EcAst.ehs_po;
    on_stmt cb hs.EcAst.ehs_s;
    on_memenv cb hs.EcAst.ehs_m

  and on_bhf cb bhf =
    on_form cb bhf.EcAst.bhf_pr;
    on_form cb bhf.EcAst.bhf_po;
    on_form cb bhf.EcAst.bhf_bd;
    on_xp cb bhf.EcAst.bhf_f

  and on_bhs cb bhs =
    on_form cb bhs.EcAst.bhs_pr;
    on_form cb bhs.EcAst.bhs_po;
    on_form cb bhs.EcAst.bhs_bd;
    on_stmt cb bhs.EcAst.bhs_s;
    on_memenv cb bhs.EcAst.bhs_m


  and on_pr cb pr =
    on_xp cb pr.EcAst.pr_fun;
    List.iter (on_form cb) [pr.EcAst.pr_event; pr.EcAst.pr_args]

  in
    on_ty cb f.EcAst.f_ty; fornode ()

and on_restr (cb : cb) (restr : mod_restr) =
  let doit (xs, ms) = Sx.iter (on_xp cb) xs; Sm.iter (on_mp cb) ms in
  oiter doit restr.ur_pos;
  doit restr.ur_neg

and on_modty cb (mty : module_type) =
  cb (`ModuleType mty.mt_name);
  List.iter (fun (_, mty) -> on_modty cb mty) mty.mt_params;
  List.iter (on_mp cb) mty.mt_args

and on_mty_mr (cb : cb) ((mty, mr) : mty_mr) =
  on_modty cb mty; on_restr cb mr

and on_gbinding (cb : cb) (b : gty) =
  match b with
  | EcAst.GTty ty ->
      on_ty cb ty
  | EcAst.GTmodty mty ->
      on_mty_mr cb mty
  | EcAst.GTmem m ->
      on_memtype cb m

and on_gbindings (cb : cb) (b : (EcIdent.t * gty) list) =
  List.iter (fun (_, b) -> on_gbinding cb b) b

and on_module (cb : cb) (me : module_expr) =
  match me.me_body with
  | ME_Alias (_, mp)  -> on_mp cb mp
  | ME_Structure st   -> on_mstruct cb st
  | ME_Decl mty       -> on_mty_mr cb mty

and on_mstruct (cb : cb) (st : module_structure) =
  List.iter (on_mpath_mstruct1 cb) st.ms_body

and on_mpath_mstruct1 (cb : cb) (item : module_item) =
  match item with
  | MI_Module   me -> on_module cb me
  | MI_Variable x  -> on_ty cb x.v_type
  | MI_Function f  -> on_fun cb f

and on_fun (cb : cb) (fun_ : function_) =
  on_fun_sig  cb fun_.f_sig;
  on_fun_body cb fun_.f_def

and on_fun_sig (cb : cb) (fsig : funsig) =
  on_ty cb fsig.fs_arg;
  on_ty cb fsig.fs_ret

and on_fun_body (cb : cb) (fbody : function_body) =
  match fbody with
  | FBalias xp -> on_xp cb xp
  | FBdef fdef -> on_fun_def cb fdef
  | FBabs oi   -> on_oi  cb oi

and on_fun_def (cb : cb) (fdef : function_def) =
  List.iter (fun v -> on_ty cb v.v_type) fdef.f_locals;
  on_stmt cb fdef.f_body;
  fdef.f_ret |> oiter (on_expr cb);
  on_uses cb fdef.f_uses

and on_uses (cb : cb) (uses : uses) =
  List.iter (on_xp cb) uses.us_calls;
  Sx.iter   (on_xp cb) uses.us_reads;
  Sx.iter   (on_xp cb) uses.us_writes

and on_oi (cb : cb) (oi : OI.t) =
  List.iter (on_xp cb) (OI.allowed oi)

(* -------------------------------------------------------------------- *)
let on_typeclasses cb s =
  Sp.iter (fun p -> cb (`Typeclass p)) s

let on_typarams cb typarams =
    List.iter (fun (_,s) -> on_typeclasses cb s) typarams

(* -------------------------------------------------------------------- *)
let on_tydecl (cb : cb) (tyd : tydecl) =
  on_typarams cb tyd.tyd_params;
  match tyd.tyd_type with
  | `Concrete ty -> on_ty cb ty
  | `Abstract s  -> on_typeclasses cb s
  | `Record (f, fds) ->
      on_form cb f;
      List.iter (on_ty cb |- snd) fds
  | `Datatype dt ->
     List.iter (List.iter (on_ty cb) |- snd) dt.tydt_ctors;
     List.iter (on_form cb) [dt.tydt_schelim; dt.tydt_schcase]

let on_typeclass cb tc =
  oiter (fun p -> cb (`Typeclass p)) tc.tc_prt;
  List.iter (fun (_,ty) -> on_ty cb ty) tc.tc_ops;
  List.iter (fun (_,f)  -> on_form cb f) tc.tc_axs

(* -------------------------------------------------------------------- *)
let on_opdecl (cb : cb) (opdecl : operator) =
  on_typarams cb opdecl.op_tparams;
  let for_kind () =
    match opdecl.op_kind with
   | OB_pred None -> ()

   | OB_pred (Some (PR_Plain f)) ->
      on_form cb f

   | OB_pred (Some (PR_Ind pri)) ->
     on_bindings cb pri.pri_args;
     List.iter (fun ctor ->
         on_gbindings cb ctor.prc_bds;
         List.iter (on_form cb) ctor.prc_spec)
       pri.pri_ctors

   | OB_nott nott ->
     List.iter (on_ty cb |- snd) nott.ont_args;
     on_ty cb nott.ont_resty;
     on_expr cb nott.ont_body

   | OB_oper None   -> ()
   | OB_oper Some b ->
     match b with
     | OP_Constr _ | OP_Record _ | OP_Proj   _ -> assert false
     | OP_TC -> assert false
     | OP_Plain  f -> on_form cb f
     | OP_Fix    f ->
       let rec on_mpath_branches br =
         match br with
         | OPB_Leaf (bds, e) ->
           List.iter (on_bindings cb) bds;
           on_expr cb e
         | OPB_Branch br ->
           Parray.iter on_mpath_branch br

       and on_mpath_branch br =
         on_mpath_branches br.opb_sub

       in on_mpath_branches f.opf_branches

  in on_ty cb opdecl.op_ty; for_kind ()

(* -------------------------------------------------------------------- *)
let on_axiom (cb : cb) (ax : axiom) =
  on_typarams cb ax.ax_tparams;
  on_form cb ax.ax_spec

(* -------------------------------------------------------------------- *)
let on_modsig (cb:cb) (ms:module_sig) =
  List.iter (fun (_,mt) -> on_modty cb mt) ms.mis_params;
  List.iter (fun (Tys_function fs) ->
      on_ty cb fs.fs_arg;
      List.iter (fun x -> on_ty cb x.ov_type) fs.fs_anames;
      on_ty cb fs.fs_ret;) ms.mis_body;
  Msym.iter (fun _ oi -> on_oi cb oi) ms.mis_oinfos

let on_ring cb r =
  on_ty cb r.r_type;
  let on_p p = cb (`Op p) in
  List.iter on_p [r.r_zero; r.r_one; r.r_add; r.r_mul];
  List.iter (oiter on_p) [r.r_opp; r.r_exp; r.r_sub];
  match r.r_embed with
  | `Direct | `Default -> ()
  | `Embed p -> on_p p

let on_field cb f =
  on_ring cb f.f_ring;
  let on_p p = cb (`Op p) in
  on_p f.f_inv; oiter on_p f.f_div

let on_instance cb ty tci =
  on_typarams cb (fst ty);
  on_ty cb (snd ty);
  match tci with
  | `Ring r    -> on_ring  cb r
  | `Field f   -> on_field cb f
  | `General p ->
    (* FIXME section: ring/field use type class that do not exists *)
    cb (`Typeclass p)

(* -------------------------------------------------------------------- *)
type sc_name =
  | Th of symbol * is_local * thmode
  | Sc of symbol option
  | Top

type scenv = {
  sc_env   : EcEnv.env;
  sc_top   : scenv option;
  sc_loca  : is_local;
  sc_name  : sc_name;
  sc_insec : bool;
  sc_abstr : bool;
  sc_items : sc_items;
}

and sc_item =
  | SC_th_item  of EcTheory.theory_item
  | SC_th       of EcEnv.Theory.compiled_theory
  | SC_decl_mod of EcIdent.t * mty_mr

and sc_items =
  sc_item list

let initial env =
  { sc_env     = env;
    sc_top     = None;
    sc_loca    = `Global;
    sc_name    = Top;
    sc_insec   = false;
    sc_abstr   = false;
    sc_items   = [];
  }

let env scenv = scenv.sc_env

(* -------------------------------------------------------------------- *)
let pp_axname scenv =
  EcPrinting.pp_axname (EcPrinting.PPEnv.ofenv scenv.sc_env)

let pp_thname scenv =
  EcPrinting.pp_thname (EcPrinting.PPEnv.ofenv scenv.sc_env)

(* -------------------------------------------------------------------- *)
let locality (env : EcEnv.env) (who : cbarg) =
  match who with
  | `Type p -> (EcEnv.    Ty.by_path p env).tyd_loca
  | `Op   p -> (EcEnv.    Op.by_path p env).op_loca
  | `Ax   p -> (EcEnv.    Ax.by_path p env).ax_loca
  | `Typeclass  p -> ((EcEnv.TypeClass.by_path p env).tc_loca :> locality)
  | `Module mp    ->
    begin match EcEnv.Mod.by_mpath_opt mp env with
    | Some (_, Some lc) -> lc
     (* in this case it should be a quantified module *)
    | _         -> `Global
    end
  | `ModuleType p -> ((EcEnv.ModTy.by_path p env).tms_loca :> locality)
  | `Instance _ -> assert false

(* -------------------------------------------------------------------- *)
type to_clear =
  { lc_theory    : Sp.t;
    lc_axioms    : Sp.t;
    lc_baserw    : Sp.t; }

type to_gen =
  { tg_env     : scenv;
    tg_params  : (EcIdent.t * Sp.t) list;
    tg_binds   : bind list;
    tg_subst   : EcSubst.subst;
    tg_clear   : to_clear; }

and bind =
  | Binding of binding
  | Imply    of form

let empty_locals =
  { lc_theory    = Sp.empty;
    lc_axioms    = Sp.empty;
    lc_baserw    = Sp.empty; }

let add_clear to_gen who =
  let tg_clear = to_gen.tg_clear in
  let tg_clear =
    match who with
    | `Th         p -> {tg_clear with lc_theory  = Sp.add p tg_clear.lc_theory  }
    | `Ax         p -> {tg_clear with lc_axioms  = Sp.add p tg_clear.lc_axioms  }
    | `Baserw     p -> {tg_clear with lc_baserw  = Sp.add p tg_clear.lc_baserw  }
  in
  { to_gen with tg_clear }

let add_bind binds bd = binds @ [Binding bd]
let add_imp binds f   = binds @ [Imply f]


let to_clear to_gen who =
  match who with
  | `Th p -> Sp.mem p to_gen.tg_clear.lc_theory
  | `Ax p -> Sp.mem p to_gen.tg_clear.lc_axioms
  | `Baserw p -> Sp.mem p to_gen.tg_clear.lc_baserw

let to_keep to_gen who = not (to_clear to_gen who)

let generalize_type to_gen ty =
  EcSubst.subst_ty to_gen.tg_subst ty

let add_declared_mod to_gen id modty =
  { to_gen with
    tg_binds  = add_bind to_gen.tg_binds (id, gtmodty modty);
    tg_subst  = EcSubst.add_module to_gen.tg_subst id (mpath_abs id [])
  }

let add_declared_ty to_gen path tydecl =
  assert (tydecl.tyd_params = []);
  let s =
    match tydecl.tyd_type with
    | `Abstract s -> s
    | _ -> assert false in

  let name = "'" ^ basename path in
  let id = EcIdent.create name in
  { to_gen with
    tg_params = to_gen.tg_params @ [id, s];
    tg_subst  = EcSubst.add_tydef to_gen.tg_subst path ([], tvar id);
  }

let add_declared_op to_gen path opdecl =
  assert (
      opdecl.op_tparams = [] &&
      match opdecl.op_kind with
      | OB_oper None | OB_pred None -> true
      | _ -> false);
  let name = basename path in
  let id = EcIdent.create name in
  let ty = generalize_type to_gen opdecl.op_ty in
  {
    to_gen with
    tg_binds = add_bind to_gen.tg_binds (id, gtty ty);
    tg_subst =
      match opdecl.op_kind with
      | OB_oper _ -> EcSubst.add_opdef to_gen.tg_subst path ([], e_local id ty)
      | OB_pred _ ->  EcSubst.add_pddef to_gen.tg_subst path ([], f_local id ty)
      | _ -> assert false }

  let tvar_fv ty = Mid.map (fun () -> 1) (EcTypes.Tvar.fv ty)
  let fv_and_tvar_e e =
    let rec aux fv e =
      let fv = EcIdent.fv_union fv (tvar_fv e.e_ty) in
      match e.e_node with
      | Eop(_, tys) -> List.fold_left (fun fv ty -> EcIdent.fv_union fv (tvar_fv ty)) fv tys
      | Equant(_,d,e) ->
        let fv = List.fold_left (fun fv (_,ty) -> EcIdent.fv_union fv (tvar_fv ty)) fv d in
        aux fv e
      | _ -> e_fold aux fv e
    in aux e.e_fv e

let rec gty_fv_and_tvar : gty -> int Mid.t = function
  | GTty ty ->
    EcTypes.ty_fv_and_tvar ty

  | GTmodty mty ->
    EcAst.mty_mr_fv mty

  | GTmem mt ->
    EcMemory.mt_fv mt

and fv_and_tvar_f f =
  let fv = ref f.f_fv in
  let rec aux f =
    fv := EcIdent.fv_union !fv (tvar_fv f.f_ty);
    match f.f_node with
    | Fop(_, tys) -> fv := List.fold_left (fun fv ty -> EcIdent.fv_union fv (tvar_fv ty)) !fv tys
    | Fquant(_, d, f) ->
      fv := List.fold_left (fun fv (_,gty) -> EcIdent.fv_union fv (gty_fv_and_tvar gty)) !fv d;
      aux f
    | Fmatch (b, bs, ty) ->
      fv := EcIdent.fv_union (tvar_fv ty) !fv;
      List.iter aux (b :: bs)
    | _ -> EcFol.f_iter aux f
  in
  aux f; !fv

let tydecl_fv tyd =
  let fv =
    match tyd.tyd_type with
    | `Concrete ty -> ty_fv_and_tvar ty
    | `Abstract _ -> Mid.empty
    | `Datatype tydt ->
      List.fold_left (fun fv (_, l) ->
        List.fold_left (fun fv ty ->
            EcIdent.fv_union fv (ty_fv_and_tvar ty)) fv l)
        Mid.empty tydt.tydt_ctors
    | `Record (_f, l) ->
      List.fold_left (fun fv (_, ty) ->
          EcIdent.fv_union fv (ty_fv_and_tvar ty)) Mid.empty l in
  List.fold_left (fun fv (id, _) -> Mid.remove id fv) fv tyd.tyd_params

let op_body_fv body ty =
  let fv = ty_fv_and_tvar ty in
  match body with
  | OP_Plain f -> EcIdent.fv_union fv (fv_and_tvar_f f)
  | OP_Constr _ | OP_Record _ | OP_Proj _ | OP_TC -> fv
  | OP_Fix opfix ->
    let fv =
      List.fold_left (fun fv (_, ty) -> EcIdent.fv_union fv (ty_fv_and_tvar ty))
        fv opfix.opf_args in
    let fv = EcIdent.fv_union fv (ty_fv_and_tvar opfix.opf_resty) in
    let rec fv_branches fv = function
      | OPB_Leaf (l, e) ->
        let fv = EcIdent.fv_union fv (fv_and_tvar_e e) in
        List.fold_left (fun fv l ->
            List.fold_left (fun fv (_, ty) ->
                EcIdent.fv_union fv (ty_fv_and_tvar ty)) fv l) fv l
      | OPB_Branch p ->
        Parray.fold_left (fun fv ob -> fv_branches fv ob.opb_sub) fv p in
    fv_branches fv opfix.opf_branches

let pr_body_fv body ty =
  let fv = ty_fv_and_tvar ty in
  match body with
  | PR_Plain f -> EcIdent.fv_union fv (fv_and_tvar_f f)
  | PR_Ind pri ->
    let fv =
      List.fold_left (fun fv (_, ty) -> EcIdent.fv_union fv (ty_fv_and_tvar ty))
        fv pri.pri_args in
    let fv_prctor fv ctor =
      let fv1 =
        List.fold_left (fun fv f -> EcIdent.fv_union fv (fv_and_tvar_f f))
          Mid.empty ctor.prc_spec in
      let fv1 = List.fold_left (fun fv (id, gty) ->
          EcIdent.fv_union (Mid.remove id fv) (gty_fv_and_tvar gty)) fv1 ctor.prc_bds in
      EcIdent.fv_union fv fv1 in
    List.fold_left fv_prctor fv pri.pri_ctors

let notation_fv nota =
  let fv = EcIdent.fv_union (fv_and_tvar_e nota.ont_body) (ty_fv_and_tvar nota.ont_resty) in
  List.fold_left (fun fv (id,ty) ->
      EcIdent.fv_union (Mid.remove id fv) (ty_fv_and_tvar ty)) fv nota.ont_args

let generalize_extra_ty to_gen fv =
  List.filter (fun (id,_) -> Mid.mem id fv) to_gen.tg_params

let rec generalize_extra_args binds fv =
  match binds with
  | [] -> []
  | Binding (id, gt) :: binds ->
    let args = generalize_extra_args binds fv in
    if Mid.mem id fv then
      match gt with
      | GTty ty -> (id, ty) :: args
      | GTmodty  _ -> assert false
      | GTmem _    -> assert false
    else args
  | Imply _ :: binds -> generalize_extra_args binds fv

let rec generalize_extra_forall ~imply binds f =
  match binds with
  | [] -> f
  | Binding (id,gt) :: binds ->
    let f = generalize_extra_forall ~imply binds f in
    if Mid.mem id f.f_fv then
      f_forall [id,gt] f
    else f
  | Imply f1 :: binds ->
    let f = generalize_extra_forall ~imply binds f in
    if imply then f_imp f1 f else f

let generalize_tydecl to_gen prefix (name, tydecl) =
  let path = pqname prefix name in
  match tydecl.tyd_loca with
  | `Local -> to_gen, None
  | `Global ->
    let tydecl = EcSubst.subst_tydecl to_gen.tg_subst tydecl in
    let fv = tydecl_fv tydecl in
    let extra = generalize_extra_ty to_gen fv in
    let tyd_params = extra @ tydecl.tyd_params in
    let args = List.map (fun (id, _) -> tvar id) tyd_params in
    let fst_params = List.map fst tydecl.tyd_params in
    let tosubst = fst_params, tconstr path args in
    let tg_subst, tyd_type =
      match tydecl.tyd_type with
      | `Concrete _ | `Abstract _ ->
        EcSubst.add_tydef to_gen.tg_subst path tosubst, tydecl.tyd_type
      | `Record (f, prs) ->
        let subst    = EcSubst.empty in
        let tg_subst = to_gen.tg_subst in
        let subst    = EcSubst.add_tydef subst path tosubst in
        let tg_subst = EcSubst.add_tydef tg_subst path tosubst in
        let rsubst   = ref subst in
        let rtg_subst = ref tg_subst in
        let tin = tconstr path args in
        let add_op (s, ty) =
          let p = pqname prefix s in
          let tosubst = fst_params, e_op p args (tfun tin ty) in
          rsubst := EcSubst.add_opdef !rsubst p tosubst;
          rtg_subst := EcSubst.add_opdef !rtg_subst p tosubst;
          s, ty
        in
        let prs = List.map add_op prs in
        let f = EcSubst.subst_form !rsubst f in
        !rtg_subst, `Record (f, prs)
      | `Datatype dt ->
        let subst    = EcSubst.empty in
        let tg_subst = to_gen.tg_subst in
        let subst    = EcSubst.add_tydef subst path tosubst in
        let tg_subst = EcSubst.add_tydef tg_subst path tosubst in
        let subst_ty = EcSubst.subst_ty subst in
        let rsubst   = ref subst in
        let rtg_subst = ref tg_subst in
        let tout = tconstr path args in
        let add_op (s,tys) =
          let tys = List.map subst_ty tys in
          let p = pqname prefix s in
          let pty = toarrow tys tout in
          let tosubst = fst_params, e_op p args pty in
          rsubst := EcSubst.add_opdef !rsubst p tosubst;
          rtg_subst := EcSubst.add_opdef !rtg_subst p tosubst ;
          s, tys in
        let tydt_ctors   = List.map add_op dt.tydt_ctors in
        let tydt_schelim = EcSubst.subst_form !rsubst dt.tydt_schelim in
        let tydt_schcase = EcSubst.subst_form !rsubst dt.tydt_schcase in
        !rtg_subst, `Datatype {tydt_ctors; tydt_schelim; tydt_schcase }

    in

    let to_gen = { to_gen with tg_subst} in
    let tydecl = {
        tyd_params; tyd_type;
        tyd_loca = `Global;
        tyd_resolve = tydecl.tyd_resolve } in
    to_gen, Some (Th_type (name, tydecl))

  | `Declare ->
    let to_gen = add_declared_ty to_gen path tydecl in
    to_gen, None

let generalize_opdecl to_gen prefix (name, operator) =
  let path = pqname prefix name in
  match operator.op_loca with
  | `Local -> to_gen, None
  | `Global ->
    let operator = EcSubst.subst_op to_gen.tg_subst operator in
    let tg_subst, operator =
      match operator.op_kind with
      | OB_oper None ->
        let fv = ty_fv_and_tvar operator.op_ty in
        let extra = generalize_extra_ty to_gen fv in
        let tparams = extra @ operator.op_tparams in
        let opty = operator.op_ty in
        let args = List.map (fun (id, _) -> tvar id) tparams in
        let tosubst = (List.map fst operator.op_tparams,
                       e_op path args opty) in
        let tg_subst =
          EcSubst.add_opdef to_gen.tg_subst path tosubst in
        tg_subst, mk_op ~opaque:operator.op_opaque tparams opty None `Global

      | OB_pred None ->
        let fv = ty_fv_and_tvar operator.op_ty in
        let extra = generalize_extra_ty to_gen fv in
        let tparams = extra @ operator.op_tparams in
        let opty = operator.op_ty in
        let args = List.map (fun (id, _) -> tvar id) tparams in
        let tosubst = (List.map fst operator.op_tparams,
                       f_op path args opty) in
        let tg_subst =
          EcSubst.add_pddef to_gen.tg_subst path tosubst in
        tg_subst, mk_op ~opaque:operator.op_opaque tparams opty None `Global

      | OB_oper (Some body) ->
        let fv = op_body_fv body operator.op_ty in
        let extra_t = generalize_extra_ty to_gen fv in
        let tparams = extra_t @ operator.op_tparams in
        let extra_a = generalize_extra_args to_gen.tg_binds fv in
        let opty = toarrow (List.map snd extra_a) operator.op_ty in
        let t_args = List.map (fun (id, _) -> tvar id) tparams in
        let eop = e_op path t_args opty in
        let e   =
          e_app eop (List.map (fun (id,ty) -> e_local id ty) extra_a)
            operator.op_ty in
        let tosubst =
          (List.map fst operator.op_tparams, e) in
        let tg_subst =
          EcSubst.add_opdef to_gen.tg_subst path tosubst in
        let body =
          match body with
          | OP_Constr _ | OP_Record _ | OP_Proj _ -> assert false
          | OP_TC -> assert false (* ??? *)
          | OP_Plain f ->
            OP_Plain (f_lambda (List.map (fun (x, ty) -> (x, GTty ty)) extra_a) f)
          | OP_Fix opfix ->
            let subst = EcSubst.add_opdef EcSubst.empty path tosubst in
            let nb_extra = List.length extra_a in
            let opf_struct =
              let (l,i) = opfix.opf_struct in
              (List.map (fun i -> i + nb_extra) l, i + nb_extra) in
            OP_Fix {
                opf_args     = extra_a @ opfix.opf_args;
                opf_resty    = opfix.opf_resty;
                opf_struct;
                opf_branches = EcSubst.subst_branches subst opfix.opf_branches;
              }
        in
        let operator =
          mk_op ~opaque:operator.op_opaque tparams opty (Some body) `Global in
        tg_subst, operator

      | OB_pred (Some body) ->
        let fv = pr_body_fv body operator.op_ty in
        let extra_t = generalize_extra_ty to_gen fv in
        let op_tparams = extra_t @ operator.op_tparams in
        let extra_a = generalize_extra_args to_gen.tg_binds fv in
        let op_ty   = toarrow (List.map snd extra_a) operator.op_ty in
        let t_args  = List.map (fun (id, _) -> tvar id) op_tparams in
        let fop = f_op path t_args op_ty in
        let f   =
          f_app fop (List.map (fun (id,ty) -> f_local id ty) extra_a)
            operator.op_ty in
        let tosubst =
          (List.map fst operator.op_tparams, f) in
        let tg_subst =
          EcSubst.add_pddef to_gen.tg_subst path tosubst in
        let body =
          match body with
          | PR_Plain f ->
            PR_Plain (f_lambda (List.map (fun (x,ty) -> (x,GTty ty)) extra_a) f)
          | PR_Ind pri ->
            let pri_args = extra_a @ pri.pri_args in
            PR_Ind { pri with pri_args }
        in
        let operator =
          { op_tparams; op_ty;
            op_kind     = OB_pred (Some body);
            op_loca     = `Global;
            op_opaque   = operator.op_opaque;
            op_clinline = operator.op_clinline;
            op_unfold   = operator.op_unfold; } in
        tg_subst, operator

      | OB_nott nott ->
        let fv = notation_fv nott in
        let extra_t = generalize_extra_ty to_gen fv in
        let op_tparams = extra_t @ operator.op_tparams in
        let extra_a = generalize_extra_args to_gen.tg_binds fv in
        let op_ty   = toarrow (List.map snd extra_a) operator.op_ty in
        let nott = { nott with ont_args = extra_a @ nott.ont_args; } in
        to_gen.tg_subst,
          { op_tparams; op_ty;
            op_kind     = OB_nott nott;
            op_loca     = `Global;
            op_opaque   = operator.op_opaque;
            op_clinline = operator.op_clinline;
            op_unfold   = operator.op_unfold; }
    in
    let to_gen = {to_gen with tg_subst} in
    to_gen, Some (Th_operator (name, operator))

  | `Declare ->
    let to_gen = add_declared_op to_gen path operator in
    to_gen, None

let generalize_axiom to_gen prefix (name, ax) =
  let ax = EcSubst.subst_ax to_gen.tg_subst ax in
  let path = pqname prefix name in
  match ax.ax_loca with
  | `Local ->
    assert (not (is_axiom ax.ax_kind));
    add_clear to_gen (`Ax path), None
  | `Global ->
    let ax_spec =
      match ax.ax_kind with
      | `Axiom _ ->
        generalize_extra_forall ~imply:false to_gen.tg_binds ax.ax_spec
      | `Lemma   ->
        generalize_extra_forall ~imply:true to_gen.tg_binds ax.ax_spec
    in
    let extra_t = generalize_extra_ty to_gen (fv_and_tvar_f ax_spec) in
    let ax_tparams = extra_t @ ax.ax_tparams in
    to_gen, Some (Th_axiom (name, {ax with ax_tparams; ax_spec}))
  | `Declare ->
    assert (is_axiom ax.ax_kind);
    assert (ax.ax_tparams = []);
    let to_gen = add_clear to_gen (`Ax path) in
    let to_gen =
      { to_gen with tg_binds = add_imp to_gen.tg_binds ax.ax_spec } in
    to_gen, None

let generalize_modtype to_gen (name, ms) =
  match ms.tms_loca with
  | `Local -> to_gen, None
  | `Global ->
    let ms = EcSubst.subst_top_modsig to_gen.tg_subst ms in
    to_gen, Some (Th_modtype (name, ms))

let generalize_module to_gen prefix me =
  match me.tme_loca with
  | `Local -> to_gen, None

  | `Global -> begin
    let me = EcSubst.subst_top_module to_gen.tg_subst me in

    match me.tme_expr.me_body with
    | ME_Alias (_, mp) -> begin
      let bds = to_gen.tg_binds in
      let bds = List.filter_map (function Binding (m, GTmodty _) -> Some m | _ -> None) bds in
      let bds = Sid.of_list bds in

      let exception Inline in

      let check_gen (x : cbarg) =
        match x with
        | `Module { m_top = `Local x } ->
          if Sid.mem x bds then raise Inline
        | _ -> () in

      try
        on_mp check_gen mp;
        to_gen, Some (Th_module me)

      with Inline ->
        let to_gen = { to_gen with tg_subst =
          EcSubst.add_moddef
            ~src:(EcPath.pqname prefix me.tme_expr.me_name)
            ~dst:mp to_gen.tg_subst } in
        to_gen, None
    end

    | _ ->
      (* FIXME section: we can generalize declare module *)
      to_gen, Some (Th_module me)
  end

  | `Declare -> assert false (* should be a LC_decl_mod *)

let generalize_export to_gen (p,lc) =
  if lc = `Local || to_clear to_gen (`Th p) then to_gen, None
  else to_gen, Some (Th_export (p,lc))

let generalize_instance to_gen (ty,tci, lc) =
  if lc = `Local then to_gen, None
  (* FIXME: be sure that we have no dep to declare or local,
     or fix this code *)
  else to_gen, Some (Th_instance (ty,tci,lc))

let generalize_baserw to_gen prefix (s,lc) =
  if lc = `Local then
    add_clear to_gen (`Baserw (pqname prefix s)), None
  else to_gen, Some (Th_baserw (s,lc))

let generalize_addrw to_gen (p, ps, lc) =
  if lc = `Local || to_clear to_gen (`Baserw p) then
    to_gen, None
  else
    let ps = List.filter (fun p -> to_keep to_gen (`Ax p)) ps in
    if ps = [] then to_gen, None
    else to_gen, Some (Th_addrw (p, ps, lc))

let generalize_reduction to_gen _rl = to_gen, None

let generalize_auto to_gen (n,s,ps,lc) =
  if lc = `Local then to_gen, None
  else
    let ps = List.filter (fun p -> to_keep to_gen (`Ax p)) ps in
    if ps = [] then to_gen, None
    else to_gen, Some (Th_auto (n,s,ps,lc))

(* --------------------------------------------------------------- *)
let get_locality scenv = scenv.sc_loca

let set_local l =
  match l with
  | `Global -> `Local
  | _ -> l

let rec set_local_item item =
  let lcitem =
    match item.ti_item with
    | Th_type         (s,ty) -> Th_type      (s, { ty with tyd_loca = set_local ty.tyd_loca })
    | Th_operator     (s,op) -> Th_operator  (s, { op with op_loca  = set_local op.op_loca   })
    | Th_axiom        (s,ax) -> Th_axiom     (s, { ax with ax_loca  = set_local ax.ax_loca   })
    | Th_modtype      (s,ms) -> Th_modtype   (s, { ms with tms_loca = set_local ms.tms_loca  })
    | Th_module          me  -> Th_module        { me with tme_loca = set_local me.tme_loca  }
    | Th_typeclass    (s,tc) -> Th_typeclass (s, { tc with tc_loca  = set_local tc.tc_loca   })
    | Th_theory      (s, th) -> Th_theory    (s, set_local_th th)
    | Th_export       (p,lc) -> Th_export    (p, set_local lc)
    | Th_instance (ty,ti,lc) -> Th_instance  (ty,ti, set_local lc)
    | Th_baserw       (s,lc) -> Th_baserw    (s, set_local lc)
    | Th_addrw     (p,ps,lc) -> Th_addrw     (p, ps, set_local lc)
    | Th_reduction       r   -> Th_reduction r
    | Th_auto     (i,s,p,lc) -> Th_auto      (i, s, p, set_local lc)

  in { item with ti_item = lcitem }

and set_local_th th =
  { th with cth_items = List.map set_local_item th.cth_items;
            cth_loca  = set_local th.cth_loca; }

let sc_th_item t item =
  let item =
    match get_locality t with
    | `Global -> item
    | `Local  -> set_local_item item in
  SC_th_item item

let sc_decl_mod (id,mt) = SC_decl_mod (id,mt)


(* ---------------------------------------------------------------- *)

let is_abstract_ty = function
  | `Abstract _ -> true
  | _           -> false

(*
let rec check_glob_mp_ty s scenv mp =
  let mtop = `Module (mastrip mp) in
  if is_declared scenv mtop then
    hierror "global %s can't depend on declared module" s;
  if is_local scenv mtop then
    hierror "global %s can't depend on local module" s;
  List.iter (check_glob_mp_ty s scenv) mp.m_args

let rec check_glob_mp scenv mp =
  let mtop = `Module (mastrip mp) in
  if is_local scenv mtop then
    hierror "global definition can't depend on local module";
  List.iter (check_glob_mp scenv) mp.m_args
 *)

let check s scenv who b =
  if not b then
    hierror "%a %s" (pp_lc_cbarg scenv.sc_env) who s

let check_section scenv who =
  check "is only allowed in section" scenv who (scenv.sc_insec)

let check_polymorph scenv who typarams =
  check "cannot be polymorphic" scenv who (typarams = [])

let check_abstract = check "should be abstract"

type can_depend = {
    d_ty    : locality list;
    d_op    : locality list;
    d_ax    : locality list;
    d_sc    : locality list;
    d_mod   : locality list;
    d_modty : locality list;
    d_tc    : locality list;
  }

let cd_glob =
  { d_ty    = [`Global];
    d_op    = [`Global];
    d_ax    = [`Global];
    d_sc    = [`Global];
    d_mod   = [`Global];
    d_modty = [`Global];
    d_tc    = [`Global];
  }

let can_depend (cd : can_depend) = function
  | `Type       _ -> cd.d_ty
  | `Op         _ -> cd.d_op
  | `Ax         _ -> cd.d_ax
  | `Sc         _ -> cd.d_sc
  | `Module     _ -> cd.d_mod
  | `ModuleType _ -> cd.d_modty
  | `Typeclass  _ -> cd.d_tc
  | `Instance   _ -> assert false


let cb scenv from cd who =
  let env = scenv.sc_env in
  let lc = locality env who in
  let lcs = can_depend cd who in
  if not (List.mem lc lcs) then
    hierror "%a" pp_error { e_env = env;
                            e_who = from;
                            e_dep = (lc, who); }

(* FIXME section: check all callback.
   Did we need a different callback for type and expr/form *)
let check_tyd scenv prefix name tyd =
  let path = EcPath.pqname prefix name in
  let from = tyd.tyd_loca, `Type path in
  match tyd.tyd_loca with
  | `Local -> check_section scenv from
  | `Declare ->
    check_section scenv from;
    check_polymorph scenv from tyd.tyd_params;
    check_abstract scenv from (is_abstract_ty tyd.tyd_type)
  | `Global ->
    let cd = {
        d_ty    = [`Declare; `Global];
        d_op    = [`Global];
        d_ax    = [];
        d_sc    = [];
        d_mod   = [`Global];
        d_modty = [];
        d_tc    = [`Global];
      } in
    on_tydecl (cb scenv from cd) tyd

(*
let cb_glob scenv (who:cbarg) =
  match who with
  | `Type p ->
    if is_local scenv who then
      hierror "global definition can't depend of local type %s"
        (EcPath.tostring p)
  | `Module mp ->
    check_glob_mp scenv mp
  | `Op p ->
    if is_local scenv who then
      hierror "global definition can't depend of local op %s"
        (EcPath.tostring p)
  | `ModuleType p ->
    if is_local scenv who then
      hierror "global definition can't depend of local module type %s"
        (EcPath.tostring p)
  | `Ax _ | `Typeclass _ -> assert false
*)

let is_abstract_op op =
  match op.op_kind with
  | OB_oper None | OB_pred None -> true
  | _ -> false

let check_op scenv prefix name op =
  let path = EcPath.pqname prefix name in
  let from = op.op_loca, `Op path in
  match op.op_loca with
  | `Local -> check_section scenv from
  | `Declare ->
    check_section scenv from;
    check_polymorph scenv from op.op_tparams;
    check_abstract scenv from (is_abstract_op op);
    (* The call back is used only for the type *)
    let cd = {
        d_ty    = [`Declare; `Global];
        d_op    = [`Declare; `Global];
        d_ax    = [];
        d_sc    = [];
        d_mod   = [`Declare; `Global];
        d_modty = [];
        d_tc    = [`Global];
      } in
    on_opdecl (cb scenv from cd) op

  | `Global ->
    let cd = {
        d_ty    = [`Declare; `Global];
        d_op    = [`Declare; `Global];
        d_ax    = [];
        d_sc    = [];
        d_mod   = [`Global];
        d_modty = [];
        d_tc    = [`Global];
      } in
    on_opdecl (cb scenv from cd) op

let is_inth scenv =
  match scenv.sc_name with
  | Th _ -> true
  | _    -> false

let check_ax (scenv : scenv) (prefix : path) (name : symbol) (ax : axiom) =
  let path = EcPath.pqname prefix name in
  let from = ax.ax_loca, `Ax path in
  let cd = {
      d_ty    = [`Declare; `Global];
      d_op    = [`Declare; `Global];
      d_ax    = [];
      d_sc    = [];
      d_mod   = [`Declare; `Global];
      d_modty = [`Global];
      d_tc    = [`Global];
    } in
  let doit = on_axiom (cb scenv from cd) in
  let error b s1 s =
    if b then hierror "%s %a %s" s1 (pp_axname scenv) path s in

  match ax.ax_loca with
  | `Local ->
    check_section scenv from;
    error (is_axiom ax.ax_kind && not scenv.sc_abstr) "axiom" "cannot be local"

  | `Declare ->
    check_section scenv from;
    check_polymorph scenv from ax.ax_tparams;
    error (is_lemma ax.ax_kind) "declare lemma" "is not allowed";
    doit ax

  | `Global ->
    if scenv.sc_insec then
      begin
        (* FIXME section: is it the correct way to do a warning *)
        if is_axiom ax.ax_kind then
           EcEnv.notify ~immediate:true scenv.sc_env `Warning
             "global axiom %a in section" (pp_axname scenv) path;
        doit ax
      end

let check_modtype scenv prefix name ms =
  let path = pqname prefix name in
  let from = ((ms.tms_loca :> locality), `ModuleType path) in
  match ms.tms_loca with
  | `Local -> check_section scenv from
  | `Global ->
    if scenv.sc_insec then
      on_modsig (cb scenv from cd_glob) ms.tms_sig


let check_module scenv prefix tme =
  let me = tme.tme_expr in
  let path = pqname prefix me.me_name in
  let from = ((tme.tme_loca :> locality), `Module (mpath_crt path [] None)) in
  match tme.tme_loca with
  | `Local -> check_section scenv from
  | `Global ->
    if scenv.sc_insec then
      let cd =
        { d_ty    = [`Global];
          d_op    = [`Global];
          d_ax    = [];
          d_sc    = [];
          d_mod   = [`Global]; (* FIXME section: add local *)
          d_modty = [`Global];
          d_tc    = [`Global];
        } in
      on_module (cb scenv from cd) me
  | `Declare -> (* Should be SC_decl_mod ... *)
    assert false

let check_typeclass scenv prefix name tc =
  let path = pqname prefix name in
  let from = ((tc.tc_loca :> locality), `Typeclass path) in
  if tc.tc_loca = `Local then check_section scenv from
  else
    on_typeclass (cb scenv from cd_glob) tc

let check_instance scenv ty tci lc =
  let from = (lc :> locality), `Instance tci in
  if lc = `Local then check_section scenv from
  else
    if scenv.sc_insec then
      match tci with
      | `Ring _ | `Field _ -> on_instance (cb scenv from cd_glob) ty tci
      | `General _ ->
        let cd = { cd_glob with d_ty = [`Declare; `Global]; } in
        on_instance (cb scenv from cd) ty tci

(* -----------------------------------------------------------*)
let enter_theory (name:symbol) (lc:is_local) (mode:thmode) scenv : scenv =
  if not scenv.sc_insec && lc = `Local then
     hierror "can not start a local theory outside of a section";
  { sc_env   = EcEnv.Theory.enter name scenv.sc_env;
    sc_top   = Some scenv;
    sc_loca  = if lc = `Local then lc else scenv.sc_loca;
    sc_abstr = scenv.sc_abstr || mode = `Abstract;
    sc_insec = scenv.sc_insec;
    sc_name  = Th (name, lc, mode);
    sc_items = []; }

let exit_theory ?clears ?pempty scenv =
  match scenv.sc_name with
  | Sc _    -> hierror "cannot close a theory containing pending sections"
  | Top     -> hierror "no theory to close"
  | Th (name, lc, mode) ->
    let cth = EcEnv.Theory.close ?clears ?pempty lc mode scenv.sc_env in
    let scenv = oget scenv.sc_top in
    name, cth, scenv

(* -----------------------------------------------------------*)
let add_item_ (item : theory_item) (scenv:scenv) =
  let item = if scenv.sc_loca = `Local then set_local_item item else item in
  let env = scenv.sc_env in
  let env =
    match item.ti_item with
    | Th_type    (s,tyd) -> EcEnv.Ty.bind s tyd env
    | Th_operator (s,op) -> EcEnv.Op.bind s op env
    | Th_axiom   (s, ax) -> EcEnv.Ax.bind s ax env
    | Th_modtype (s, ms) -> EcEnv.ModTy.bind s ms env
    | Th_module       me -> EcEnv.Mod.bind me.tme_expr.me_name me env
    | Th_typeclass(s,tc) -> EcEnv.TypeClass.bind s tc env
    | Th_export  (p, lc) -> EcEnv.Theory.export p lc env
    | Th_instance (tys,i,lc) -> EcEnv.TypeClass.add_instance tys i lc env
    | Th_baserw   (s,lc) -> EcEnv.BaseRw.add s lc env
    | Th_addrw (p,ps,lc) -> EcEnv.BaseRw.addto p ps lc env
    | Th_auto (level, base, ps, lc) -> EcEnv.Auto.add ~level ?base ps lc env
    | Th_reduction r     -> EcEnv.Reduction.add r env
    | _                  -> assert false
  in
  { scenv with
    sc_env = env;
    sc_items = SC_th_item item :: scenv.sc_items}

let add_th ~import (cth : EcEnv.Theory.compiled_theory) scenv =
  let env = EcEnv.Theory.bind ~import cth scenv.sc_env in
  { scenv with sc_env = env; sc_items = SC_th cth :: scenv.sc_items; }

(* -----------------------------------------------------------*)
let rec generalize_th_item (to_gen : to_gen) (prefix : path) (th_item : theory_item) =
  let to_gen, item =
    match th_item.ti_item with
    | Th_type tydecl     -> generalize_tydecl to_gen prefix tydecl
    | Th_operator opdecl -> generalize_opdecl to_gen prefix opdecl
    | Th_axiom  ax       -> generalize_axiom  to_gen prefix ax
    | Th_modtype ms      -> generalize_modtype to_gen ms
    | Th_module me       -> generalize_module  to_gen prefix me
    | Th_theory th       -> (generalize_ctheory to_gen prefix th, None)
    | Th_export (p,lc)   -> generalize_export to_gen (p,lc)
    | Th_instance (ty,i,lc) -> generalize_instance to_gen (ty,i,lc)
    | Th_typeclass _     -> assert false
    | Th_baserw (s,lc)   -> generalize_baserw to_gen prefix (s,lc)
    | Th_addrw (p,ps,lc) -> generalize_addrw to_gen (p, ps, lc)
    | Th_reduction rl    -> generalize_reduction to_gen rl
    | Th_auto hints      -> generalize_auto to_gen hints

  in

  let scenv =
    item |> Option.fold ~none:to_gen.tg_env ~some:(fun item ->
      let item = { ti_import = th_item.ti_import; ti_item = item; } in
      add_item_ item to_gen.tg_env
    )
  in

  { to_gen with tg_env = scenv }

and generalize_ctheory
  (genenv      : to_gen)
  (prefix      : path)
  ((name, cth) : symbol * ctheory)
: to_gen
=
  let path = pqname prefix name in

  if cth.cth_mode = `Abstract && cth.cth_loca = `Local then
    add_clear genenv (`Th path)
  else
    let compiled =
      let genenv =
        let scenv =
          enter_theory
            name `Global cth.cth_mode
            genenv.tg_env
        in
        { genenv with tg_env = scenv }
      in

      let genenv =
        List.fold_left (fun genenv item ->
          generalize_th_item genenv path item
        ) genenv cth.cth_items in

      let _, compiled, _ = exit_theory genenv.tg_env in

      compiled
    in        

    match compiled with
    | None ->
      genenv
    | Some compiled when List.is_empty compiled.ctheory.cth_items ->
      genenv
    | Some compiled ->
      let scenv = add_th ~import:import0 compiled genenv.tg_env in
      { genenv with tg_env = scenv; }

and generalize_lc_item (genenv : to_gen) (prefix : path) (item : sc_item) =
  match item with
  | SC_decl_mod (id, modty) ->
    add_declared_mod genenv id modty
  | SC_th_item th_item ->
    generalize_th_item genenv prefix th_item
  | SC_th cth ->
    generalize_ctheory genenv prefix (cth.name, cth.ctheory)

and generalize_lc_items (genenv : to_gen) (prefix : path) (items : sc_item list) =
  List.fold_left
    (fun genenv item ->
      generalize_lc_item genenv prefix item)
    genenv items

let genenv_of_scenv (scenv : scenv) : to_gen =
  { tg_env    = Option.get (scenv.sc_top)
  ; tg_params = []
  ; tg_binds  = []
  ; tg_subst  = EcSubst.empty
  ; tg_clear  = empty_locals } 

let generalize_lc_items scenv  =
  let togen =
    generalize_lc_items
      (genenv_of_scenv scenv)
      (EcEnv.root scenv.sc_env)
      (List.rev scenv.sc_items)
  in togen.tg_env
  
(* -----------------------------------------------------------*)
let import p scenv =
  { scenv with sc_env = EcEnv.Theory.import p scenv.sc_env }

let import_vars m scenv =
  { scenv with
    sc_env = EcEnv.Mod.import_vars scenv.sc_env m }

let require (cth : EcEnv.Theory.compiled_theory) (scenv : scenv) =
  (* FIXME section *)
  if scenv.sc_insec then hierror "cannot use `require' in sections";
  { scenv with sc_env = EcEnv.Theory.require cth scenv.sc_env }

let astop scenv =
  if scenv.sc_insec then hierror "can not require inside a section";
  { scenv with sc_env = EcEnv.astop scenv.sc_env }

(* -----------------------------------------------------------*)
let check_item scenv item =
  let prefix = EcEnv.root scenv.sc_env in
  match item.ti_item with
  | Th_type     (s,tyd) -> check_tyd scenv prefix s tyd
  | Th_operator  (s,op) -> check_op  scenv prefix s op
  | Th_axiom    (s, ax) -> check_ax  scenv prefix s ax
  | Th_modtype  (s, ms) -> check_modtype scenv prefix s ms
  | Th_module        me -> check_module  scenv prefix me
  | Th_typeclass (s,tc) -> check_typeclass scenv prefix s tc
  | Th_export   (_, lc) -> assert (lc = `Global || scenv.sc_insec);
  | Th_instance  (ty,tci,lc) -> check_instance scenv ty tci lc
  | Th_baserw (_,lc) ->
    if (lc = `Local && not scenv.sc_insec) then
      hierror "local base rewrite can only be declared inside section";
  | Th_addrw (_,_,lc) ->
    if (lc = `Local && not scenv.sc_insec) then
      hierror "local hint rewrite can only be declared inside section";
  | Th_auto (_, _, _, lc) ->
    if (lc = `Local && not scenv.sc_insec) then
      hierror "local hint can only be declared inside section";
  | Th_reduction _ -> ()
  | Th_theory  _   -> assert false

let rec add_item (item : theory_item) (scenv : scenv) =
  let item = if scenv.sc_loca = `Local then set_local_item item else item in
  let scenv1 = add_item_ item scenv in
  begin match item.ti_item with
  | Th_theory (s,cth) ->
    if cth.cth_loca = `Local && not scenv.sc_insec then
      hierror "local theory %a can only be used inside section"
        (pp_thname scenv1) (pqname (EcEnv.root scenv.sc_env) s);
    let scenv = enter_theory s cth.cth_loca cth.cth_mode scenv in
    ignore (add_items cth.cth_items scenv)
  | _ -> check_item scenv1 item
  end;
  scenv1

and add_items (items : theory) (scenv : scenv) =
  let add scenv item = add_item item scenv in
  List.fold_left add scenv items

let add_decl_mod id mt scenv =
  match scenv.sc_name with
  | Th _ | Top ->
    hierror "declare module are only allowed inside section"
  | Sc _ ->
    let cd = {
      d_ty    = [`Global];
      d_op    = [`Global];
      d_ax    = [];
      d_sc    = [];
      d_mod   = [`Declare; `Global];
      d_modty = [`Global];
      d_tc    = [`Global];
    } in
    let from = `Declare, `Module (mpath_abs id []) in
    on_mty_mr (cb scenv from cd) mt;
    { scenv with
      sc_env = EcEnv.Mod.declare_local id mt scenv.sc_env;
      sc_items = SC_decl_mod (id, mt) :: scenv.sc_items }

(* -----------------------------------------------------------*)
let enter_section (name : symbol option) (scenv : scenv) =
  { sc_env = scenv.sc_env;
    sc_top = Some scenv;
    sc_loca = `Global;
    sc_name = Sc name;
    sc_insec = true;
    sc_abstr = false;
    sc_items = []; }

let exit_section (name : symbol option) (scenv : scenv) =
  match scenv.sc_name with
  | Top  ->
    hierror "no section to close"
  | Th _ ->
    hierror "cannot close a section containing pending theories"
  | Sc sname ->
    let get = odfl "<empty>" in
    if sname <> name then
      hierror "expecting [%s], not [%s]" (get sname) (get name);
    generalize_lc_items scenv
