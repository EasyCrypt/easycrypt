(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcAst
open EcTypes
open EcEnv
open EcFol
open EcReduction
open EcBaseLogic
open EcMemory
module BI = EcBigInt

(* -------------------------------------------------------------------- *)
type state = {
  st_ri   : reduction_info;
  st_hyps : LDecl.hyps;
  st_env  : EcEnv.env;
}

(* -------------------------------------------------------------------- *)
module Subst : sig
  type subst

  val subst_id : subst

  val subst          : subst -> form -> form
  val subst_ty       : subst -> ty -> ty
  val subst_xpath    : subst -> EcPath.xpath -> EcPath.xpath
  val subst_m        : subst -> ident -> ident
  val subst_me       : subst -> EcMemory.memenv -> EcMemory.memenv
  val subst_lpattern : subst -> lpattern -> subst * lpattern
  val subst_stmt     : subst -> EcModules.stmt -> EcModules.stmt
  val subst_e        : subst -> expr -> expr

  val bind_local   : subst -> ident -> form -> subst
  val bind_locals  : subst -> (ident * form) list -> subst
  val add_binding  : subst -> binding -> subst * binding
  val add_bindings : subst -> bindings -> subst * bindings

  val has_mem : subst -> ident -> bool
end = struct
  type subst = f_subst

  let subst_id       = Fsubst.f_subst_id
  let subst          = Fsubst.f_subst ?tx:None
  let subst_ty       = ty_subst
  let subst_xpath    = Fsubst.x_subst
  let subst_m        = Fsubst.m_subst
  let subst_me       = Fsubst.me_subst
  let subst_lpattern = Fsubst.lp_subst
  let subst_stmt     = Fsubst.s_subst
  let subst_e        = Fsubst.e_subst
  let bind_local     = Fsubst.f_bind_local
  let add_binding    = Fsubst.add_binding
  let add_bindings   = Fsubst.add_bindings

  let bind_locals (s : subst) xs =
    List.fold_left (fun s (x, e) -> bind_local s x e) s xs

  let has_mem = Fsubst.has_mem

end

type subst = Subst.subst

(* -------------------------------------------------------------------- *)
let rec f_eq_simpl st f1 f2 =
  if f_equal f1 f2 then f_true else

  match fst_map f_node (destr_app f1), fst_map f_node (destr_app f2) with
  | (Fop (p1, _), args1), (Fop (p2, _), args2)
      when EcEnv.Op.is_dtype_ctor st.st_env p1
           && EcEnv.Op.is_dtype_ctor st.st_env p2 ->

    let idx p =
      let idx = EcEnv.Op.by_path p st.st_env in
      snd (EcDecl.operator_as_ctor idx)
    in
    if   idx p1 <> idx p2
    then f_false
    else f_ands0_simpl (List.map2 (f_eq_simpl st) args1 args2)

  | _, _ ->
    if (EqTest.for_type st.st_env f1.f_ty EcTypes.tunit &&
        EqTest.for_type st.st_env f2.f_ty EcTypes.tunit) ||
       is_alpha_eq st.st_hyps f1 f2
    then f_true
    else EcFol.f_eq_simpl f1 f2

(* -------------------------------------------------------------------- *)
let rec f_map_get_simpl st m x bty =
  match m.f_node with
  | Fapp({ f_node = Fop(p, _)}, [e])
      when EcPath.p_equal p EcCoreLib.CI_Map.p_cst ->
    e

  | Fapp({f_node = Fop(p, _)}, [m'; x'; e])
      when EcPath.p_equal p EcCoreLib.CI_Map.p_set
    -> begin

    match sform_of_form (f_eq_simpl st x' x) with
    | SFtrue  -> e
    | SFfalse -> f_map_get_simpl st m' x bty
    | _       ->
      let m' = f_map_set_simplify st m' x in
      let m' = f_map_set m' x' e in
      f_map_get m' x bty
  end

  | _ -> f_map_get m x bty

and f_map_set_simplify st m x =
  match m.f_node with
  | Fapp({ f_node = Fop(p, _)}, [m'; x'; e])
      when EcPath.p_equal p EcCoreLib.CI_Map.p_set
    -> begin

    match sform_of_form (f_eq_simpl st x' x) with
    | SFtrue  -> f_map_cst x.f_ty e
    | SFfalse -> f_map_set_simplify st m' x
    | _       ->
      let m' = f_map_set_simplify st m' x in
      f_map_set m' x' e
  end

  | _ -> m

(* -------------------------------------------------------------------- *)
module Args : sig
  type args = private { resty : ty; stack : form list; }

  val empty   : ty -> args
  val create  : ty -> form list -> args
  val isempty : args -> bool
  val push1   : form -> args -> args
  val pushn   : form list -> args -> args
  val pop     : args -> (form * args) option
end = struct
  type args = { resty : ty; stack : form list; }

  let empty (ty : ty) : args =
    { resty = ty; stack = []; }

  let create (resty : ty) (stack : form list) : args =
    { resty; stack; }

  let isempty (args : args) : bool =
    List.is_empty args.stack

  let push1 (f : form) (args : args) =
    { args with stack = f :: args.stack; }

  let pushn (fs : form list) (args : args) =
    { args with stack = fs @ args.stack; }

  let pop (args : args) : (form * args) option =
    match args.stack with
    | [] -> None
    | f :: stack -> Some (f, { args with stack; })
end

type args = Args.args

(* -------------------------------------------------------------------- *)
let norm_xfun st s f =
  let f  = Subst.subst_xpath s f in
  if st.st_ri.modpath then EcEnv.NormMp.norm_xfun st.st_env f else f

let norm_stmt s c  = Subst.subst_stmt s c
let norm_me   s me = Subst.subst_me s me
let norm_e    s e  = Subst.subst_e s e

(* -------------------------------------------------------------------- *)
let rec norm st s f =
(* FIXME : I think substitution in type is wrong *)
 let f = cbv st s f (Args.empty (Subst.subst_ty s f.f_ty)) in
 norm_lambda st f

and norm_lambda (st : state) (f : form) =
  match f.f_node with
  | Fquant (Llambda, b, f) ->
    let s, b = Subst.add_bindings Subst.subst_id b in
    let st = { st with st_env = Mod.add_mod_binding b st.st_env } in
    f_lambda b (norm st s f)

  | Fapp (f1, args) ->
    f_app (norm_lambda st f1) (List.map (norm_lambda st) args) f.f_ty

  | Ftuple args -> f_tuple (List.map (norm_lambda st) args)

  | Fproj (f1, i) -> f_proj (norm_lambda st f1) i f.f_ty

  | Fquant  _ | Fif     _ | Fmatch    _ | Flet _ | Fint _ | Flocal _
  | Fglob   _ | Fpvar   _ | Fop       _

  | FhoareF _   | FhoareS _
  | FbdHoareF _ | FbdHoareS _
  | FeHoareF _ | FeHoareS _
  | FequivF _   | FequivS _
  | FeagerF   _ | Fpr _

    -> f

(* -------------------------------------------------------------------- *)
and betared st s bd f args =
  match bd, Args.pop args with
  | [], _ ->
     cbv st s f args

  | _, None ->
     Subst.subst s (f_quant Llambda bd f)

  | (x, gty) :: bd, Some (v, args) ->
     let _ : ty = EcFol.as_gtty gty in
     let s = Subst.bind_local s x v in
     betared st s bd f args

(* -------------------------------------------------------------------- *)
and try_reduce_record_projection
  (st : state) ((p, _tys) : EcPath.path * ty list) (args : args)
=
  let exception Bailout in

  try
    if not (
      st.st_ri.iota 
      && EcEnv.Op.is_projection st.st_env p
      && not (Args.isempty args)
    ) then raise Bailout;

    let mk, args1 = oget (Args.pop args) in

    match mk.f_node with
    | Fapp ({ f_node = Fop (mkp, _) }, mkargs)
        when (EcEnv.Op.is_record_ctor st.st_env mkp) ->
      let v = oget (EcEnv.Op.by_path_opt p st.st_env) in
      let v = proj3_2 (EcDecl.operator_as_proj v) in
      Some (app_red st (List.nth mkargs v) args1)

    | _ ->
      None

  with Bailout ->
    None

(* -------------------------------------------------------------------- *)
and try_reduce_fixdef
  (st : state) ((p, tys) : EcPath.path * ty list) (args : args)
=
  let exception Bailout in

  try
    if not (st.st_ri.iota && EcEnv.Op.is_fix_def st.st_env p) then
      raise Bailout;

    let Args.{ resty = ty; stack = args; } = args in
    let op  = oget (EcEnv.Op.by_path_opt p st.st_env) in
    let fix = EcDecl.operator_as_fix op in

    if List.length args < snd (fix.EcDecl.opf_struct) then
      raise Bailout;

    let args, eargs = List.split_at (snd (fix.EcDecl.opf_struct)) args in

    let vargs = Array.of_list args in
    let pargs = List.fold_left (fun (opb, acc) v ->
        let v = vargs.(v) in

          match fst_map (fun x -> x.f_node) (EcFol.destr_app v) with
          | (Fop (p, _), cargs) when EcEnv.Op.is_dtype_ctor st.st_env p -> begin
              let idx = EcEnv.Op.by_path p st.st_env in
              let idx = snd (EcDecl.operator_as_ctor idx) in
                match opb with
                | EcDecl.OPB_Leaf   _  -> assert false
                | EcDecl.OPB_Branch bs ->
                  ((Parray.get bs idx).EcDecl.opb_sub, cargs :: acc)
            end
          | _ -> raise Bailout)
      (fix.EcDecl.opf_branches, []) (fst fix.EcDecl.opf_struct)
    in

    let pargs, (bds, body) =
      match pargs with
      | EcDecl.OPB_Leaf (bds, body), cargs -> (List.rev cargs, (bds, body))
      | _ -> assert false
    in

    let subst =
      List.fold_left2
        (fun subst (x, _) fa -> Subst.bind_local subst x fa)
        Subst.subst_id fix.EcDecl.opf_args args in

    let subst =
      List.fold_left2
        (fun subst bds cargs ->
          List.fold_left2
            (fun subst (x, _) fa -> Subst.bind_local subst x fa)
            subst bds cargs)
        subst bds pargs in

    let body = EcFol.form_of_expr body in
    let body =
      Tvar.f_subst ~freshen:true op.EcDecl.op_tparams tys body in

    Some (cbv st subst body (Args.create ty eargs))

  with Bailout ->
    None

(* -------------------------------------------------------------------- *)
and app_red st f1 args =
  match f1.f_node with
  (* β-reduction *)
  | Fquant (Llambda, bd, f2) when not (Args.isempty args) && st.st_ri.beta ->
      betared st Subst.subst_id bd f2 args

  (* op reduction (ι-reduction / delta / user-defined rules) *)
  | Fop (p, tys) ->
    List.find_map_opt
      (fun f -> f st (p, tys) args)
      [ try_reduce_record_projection
      ; try_reduce_fixdef]
    |> ofdfl (fun () -> reduce_user_delta st f1 p tys args)

  | _ ->
    f_app f1 args.stack args.resty

and reduce_user_delta st f1 p tys args =
  let f2 = f_app f1 args.stack args.resty in

  match reduce_user_with_exn st f2 with
  | f -> f
  | exception NotReducible ->
    let mode = st.st_ri.delta_p p in
    let nargs = List.length args.stack in
    match mode with
    | #Op.redmode as mode when Op.reducible ~mode ~nargs st.st_env p ->
      let f = Op.reduce ~mode ~nargs st.st_env p tys in
      cbv st Subst.subst_id f args
    | _ -> f2

(* -------------------------------------------------------------------- *)
and reduce_logic st f =
  EcReduction.reduce_logic st.st_ri st.st_env st.st_hyps f

and reduce_user_with_exn st f =
  match reduce_logic st f with
  | f -> cbv_init st Subst.subst_id f
  | exception NotReducible ->
    (* Try user reduction *)
    let simplify = cbv_init st Subst.subst_id in
    let f = reduce_user_gen simplify st.st_ri st.st_env st.st_hyps f in
    cbv_init st Subst.subst_id f

and reduce_user st f =
  try  reduce_user_with_exn st f
  with NotReducible -> f

(* -------------------------------------------------------------------- *)
and cbv_init st s f =
  cbv st s f (Args.empty (Subst.subst_ty s f.f_ty))

(* -------------------------------------------------------------------- *)
and cbv (st : state) (s : subst) (f : form) (args : args) : form =
  match f.f_node with
  | Fquant ((Lforall | Lexists) as q, b, f) -> begin
    assert (Args.isempty args);

    let b, f =
      let s, b = Subst.add_bindings s b in
      let st = { st with st_env = Mod.add_mod_binding b st.st_env } in
      b, norm st s f in

    match q, st.st_ri.logic with
    | Lforall, Some `Full -> f_forall_simpl b f
    | Lforall, _          -> f_forall b f
    | Lexists, Some `Full -> f_exists_simpl b f
    | Lexists, _          -> f_exists b f
    | Llambda, _          -> assert false
  end

  | Fquant (Llambda, [x, GTty _], { f_node = Fapp (fn, fnargs) })
      when st.st_ri.eta && Args.isempty args && EcReduction.can_eta x (fn, fnargs)
    ->
    let rfn = f_app fn (List.take (List.length fnargs - 1) fnargs) f.f_ty in
    cbv st s rfn args

  | Fquant (Llambda, b, f1) when not (Args.isempty args) ->
    cbv_init st Subst.subst_id (betared st s b f1 args)

  | Fquant (Llambda, _, _) ->
    assert (Args.isempty args);
    Subst.subst s f

  | Fif (f, f1, f2) ->
    if st.st_ri.iota then
      let f = cbv_init st s f in
      match sform_of_form f with
      | SFtrue  -> cbv st s f1 args
      | SFfalse -> cbv st s f2 args
      | _ ->
        (* FIXME: should we normalize f, f1 and f2 ? *)
        app_red st
          (f_if_simpl (norm_lambda st f) (norm st s f1) (norm st s f2)) args
    else
      app_red st
        (f_if (norm st s f) (norm st s f1) (norm st s f2)) args

  | Fmatch (cf, bs, ty) ->
      if st.st_ri.iota then
        let cf = cbv_init st s cf in
        match fst_map f_node (destr_app cf) with
        | Fop (p, _), cargs when EcEnv.Op.is_dtype_ctor st.st_env p ->
            let idx = EcEnv.Op.by_path p st.st_env in
            let idx = snd (EcDecl.operator_as_ctor idx) in
            let br  = oget (List.nth_opt bs idx) in
            cbv st s br (Args.pushn cargs args)

        | _ ->
          let bs = List.map (norm st s) bs in
          app_red st (f_match (norm_lambda st cf) bs ty) args

      else
        let bs = List.map (norm st s) bs in
        app_red st (f_match (norm st s cf) bs ty) args

  | Flet (p, f1, f2) ->
    let f1 = cbv_init st s f1 in
    begin match p, f1.f_node with
    (* ζ-reduction *)
    | LSymbol(x,_), _ when st.st_ri.zeta ->
      let s = Subst.bind_local s x f1 in
      cbv st s f2 args

    (* ζ-reduction *)
    | LTuple ids, Ftuple es when st.st_ri.zeta ->
      let s = Subst.bind_locals s (List.combine (List.fst ids) es) in
      cbv st s f2 args

    (* FIXME: LRecord *)
    | _, _ ->
      let f1 = norm_lambda st f1 in
      let s, p = Subst.subst_lpattern s p in
      let f2 = norm st s f2 in
      app_red st (f_let p f1 f2) args
    end

  | Fint _ -> assert (Args.isempty args); f

  | Flocal _ -> app_red st (Subst.subst s f) args

  | Fglob _ -> app_red st (Subst.subst s f) args

  (* μ-reduction *)
  | Fpvar _ ->
    let pv, m = destr_pvar (Subst.subst s f) in
    let pv =
      if   st.st_ri.modpath
      then EcEnv.NormMp.norm_pvar st.st_env pv
      else pv in
    app_red st (f_pvar pv f.f_ty m).inv args

  | Fop _ -> app_red st (Subst.subst s f) args

  | Fapp (f1, args1) ->
    let args1 = List.map (cbv_init st s) args1 in
    cbv st s f1 (Args.pushn args1 args)

  | Ftuple args1 ->
    assert (Args.isempty args);
    reduce_user st (f_tuple (List.map (cbv_init st s) args1))

  | Fproj (f1, i) ->
    let f1 = cbv_init st s f1 in
    let f1 =
      match f1.f_node with
      | Ftuple args when st.st_ri.iota -> List.nth args i
      | _ -> reduce_user st (f_proj (norm_lambda st f1) i f.f_ty) in
    app_red st f1 args

  | FhoareF hf ->
    assert (Args.isempty args);
    assert (not (Subst.has_mem s hf.hf_m));
    let hf_pr = norm st s (hf_pr hf).inv in
    let hf_po = norm st s (hf_po hf).inv in
    let hf_f  = norm_xfun st s hf.hf_f in
    let (m,_) = norm_me s (abstract hf.hf_m) in
    f_hoareF {m;inv=hf_pr} hf_f {m;inv=hf_po}

  | FhoareS hs ->
    assert (Args.isempty args);
    assert (not (Subst.has_mem s (fst hs.hs_m)));
    let hs_pr = norm st s (hs_pr hs).inv in
    let hs_po = norm st s (hs_po hs).inv in
    let hs_s  = norm_stmt s hs.hs_s in
    let hs_m  = norm_me s hs.hs_m in
    let m = fst hs_m in
    f_hoareS (snd hs_m) {m;inv=hs_pr} hs_s {m;inv=hs_po}

  | FeHoareF hf ->
    assert (Args.isempty args);
    assert (not (Subst.has_mem s hf.ehf_m));
    let ehf_pr  = norm st s (ehf_pr hf).inv in
    let ehf_po  = norm st s (ehf_po hf).inv in
    let ehf_f   = norm_xfun st s hf.ehf_f in
    let (m,_) = norm_me s (abstract hf.ehf_m) in
    f_eHoareF {m;inv=ehf_pr} ehf_f {m;inv=ehf_po}

  | FeHoareS hs ->
    assert (Args.isempty args);
    assert (not (Subst.has_mem s (fst hs.ehs_m)));
    let ehs_pr  = norm st s (ehs_pr hs).inv in
    let ehs_po  = norm st s (ehs_po hs).inv in
    let ehs_s   = norm_stmt s hs.ehs_s in
    let (m,mt)   = norm_me s hs.ehs_m in
    f_eHoareS mt {m;inv=ehs_pr} ehs_s {m;inv=ehs_po}

  | FbdHoareF hf ->
    assert (Args.isempty args);
    assert (not (Subst.has_mem s hf.bhf_m));
    let bhf_pr = norm st s (bhf_pr hf).inv in
    let bhf_po = norm st s (bhf_po hf).inv in
    let bhf_f  = norm_xfun st s hf.bhf_f in
    let bhf_bd = norm st s (bhf_bd hf).inv in
    let (m,_) = norm_me s (abstract hf.bhf_m) in
    f_bdHoareF {m;inv=bhf_pr} bhf_f {m;inv=bhf_po} hf.bhf_cmp {m;inv=bhf_bd}

  | FbdHoareS bhs ->
    assert (Args.isempty args);
    assert (not (Subst.has_mem s (fst bhs.bhs_m)));
    let bhs_pr = norm st s (bhs_pr bhs).inv in
    let bhs_po = norm st s (bhs_po bhs).inv in
    let bhs_s  = norm_stmt s bhs.bhs_s in
    let bhs_bd = norm st s (bhs_bd bhs).inv in
    let (m,mt)  = norm_me s bhs.bhs_m in
    f_bdHoareS mt {m;inv=bhs_pr} bhs_s {m;inv=bhs_po} bhs.bhs_cmp {m;inv=bhs_bd}

  | FequivF ef ->
    assert (Args.isempty args);
    assert (not (Subst.has_mem s ef.ef_ml));
    assert (not (Subst.has_mem s ef.ef_mr));
    let ef_pr = norm st s (ef_pr ef).inv in
    let ef_po = norm st s (ef_po ef).inv in
    let ef_fl = norm_xfun st s ef.ef_fl in
    let ef_fr = norm_xfun st s ef.ef_fr in
    let (ml,_) = norm_me s (abstract ef.ef_ml) in
    let (mr,_) = norm_me s (abstract ef.ef_mr) in
    f_equivF {ml;mr;inv=ef_pr} ef_fl ef_fr {ml;mr;inv=ef_po}

  | FequivS es ->
    assert (Args.isempty args);
    assert (not (Subst.has_mem s (fst es.es_ml)));
    assert (not (Subst.has_mem s (fst es.es_mr)));
    let es_pr = norm st s (es_pr es).inv in
    let es_po = norm st s (es_po es).inv in
    let es_sl = norm_stmt s es.es_sl in
    let es_sr = norm_stmt s es.es_sr in
    let (ml,mlt)  = norm_me s es.es_ml in
    let (mr,mrt)  = norm_me s es.es_mr in
    f_equivS mlt mrt {ml;mr;inv=es_pr} es_sl es_sr {ml;mr;inv=es_po}

  | FeagerF eg ->
    assert (Args.isempty args);
    assert (not (Subst.has_mem s eg.eg_ml));
    assert (not (Subst.has_mem s eg.eg_mr));
    let eg_pr = norm st s (eg_pr eg).inv in
    let eg_po = norm st s (eg_po eg).inv in
    let eg_fl = norm_xfun st s eg.eg_fl in
    let eg_fr = norm_xfun st s eg.eg_fr in
    let eg_sl = norm_stmt s eg.eg_sl in
    let eg_sr = norm_stmt s eg.eg_sr in
    let (ml,_) = norm_me s (abstract eg.eg_ml) in
    let (mr,_) = norm_me s (abstract eg.eg_mr) in
    f_eagerF {ml;mr;inv=eg_pr} eg_sl eg_fl eg_fr eg_sr {ml;mr;inv=eg_po}

  | Fpr pr ->
    assert (Args.isempty args);
    assert (not (Subst.has_mem s pr.pr_event.m));
    let pr_mem   = Subst.subst_m s pr.pr_mem in
    let pr_fun   = norm_xfun st s pr.pr_fun in
    let pr_args  = norm st s pr.pr_args in
    let pr_event = norm st s pr.pr_event.inv in
    let (m,_) = norm_me s (abstract pr.pr_event.m) in
    f_pr pr_mem pr_fun pr_args {m;inv=pr_event}

(* -------------------------------------------------------------------- *)
(* FIXME : initialize the subst with let in hyps *)
let norm_cbv (ri : reduction_info) hyps f =
  let st = {
    st_hyps = hyps;
    st_env  = LDecl.toenv hyps;
    st_ri   = ri
  } in

  let add_hyp s (x,k) =
    match k with
    | LD_var (_, Some e) when ri.delta_h x ->
      let v = cbv_init st s e in Subst.bind_local s x v
    | _ -> s in

  let s =
    List.fold_left
      add_hyp
      Subst.subst_id
      (List.rev (LDecl.tohyps hyps).h_local)

  in norm st s f
