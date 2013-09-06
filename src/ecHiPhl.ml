(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcParsetree
open EcLocation
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcReduction
open EcBaseLogic
open EcLogic
open EcHiLogic
open EcCorePhl
open EcCoreHiPhl
open EcCoreHiLogic
open EcPhl

module TT = EcTyping
module UE = EcUnify.UniEnv


(* César says: too much code repetition w.r.t. ecPhl *)
let process_bdHoare_deno info (_,n as g) = 
  let process_cut g (pre,post) = 
    let hyps,concl = get_goal g in
    let cmp, f, bd =
      match concl.f_node with
      | Fapp({f_node = Fop(op,_)}, [f;bd]) when is_pr f &&
          (EcPath.p_equal op EcCoreLib.p_eq || 
             EcPath.p_equal op EcCoreLib.p_real_le ) ->
        let cmp = if EcPath.p_equal op EcCoreLib.p_eq then FHeq else FHle in
        cmp, f, bd
      | Fapp({f_node = Fop(op,_)}, [bd;f]) when is_pr f 
          &&
          (EcPath.p_equal op EcCoreLib.p_eq || 
             EcPath.p_equal op EcCoreLib.p_real_le ) ->
        let cmp = if EcPath.p_equal op EcCoreLib.p_eq then FHeq else FHge in
        cmp, f , bd
      | _ -> cannot_apply "bdHoare_deno" 
        "the conclusion is not a suitable Pr expression" in (* FIXME error message *) 
    let _,f,_,event = destr_pr f in
    let penv, qenv = LDecl.hoareF f hyps in
    let pre  = pre  |> omap_dfl (fun p -> process_form penv p tbool) f_true in
    let post = post |> omap_dfl (fun p -> process_form qenv p tbool) event in
    f_bdHoareF pre f post cmp bd 
  in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let bhf = t_as_bdHoareF f in
    bhf.bhf_pr, bhf.bhf_po in
  t_on_first (t_use an gs) (t_bdHoare_deno pre post (juc,n))

let process_equiv_deno info (_,n as g) = 
  let process_cut g (pre,post) = 
    let hyps,concl = get_goal g in
    let _op, f1, f2 =
      match concl.f_node with
      | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 -> 
        op, f1, f2
      | _ -> cannot_apply "equiv_deno" "" in (* FIXME error message *) 
    let _,fl,_,_ = destr_pr f1 in
    let _,fr,_,_ = destr_pr f2 in
    let penv, qenv = LDecl.equivF fl fr hyps in
    let pre  = pre |> omap_dfl (fun p -> process_form penv p tbool) f_true in
    (* FIXME: Benjamin : below: put a better default event instead of f_true *)
    let post = post |> omap_dfl (fun p -> process_form qenv p tbool) f_true in
    f_equivF pre fl fr post in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let ef = t_as_equivF f in
    ef.ef_pr, ef.ef_po in
  t_on_first (t_use an gs) (t_equiv_deno pre post (juc,n))
  
let process_ppr (phi1,phi2) g =
  let hyps,concl = get_goal g in
  let ef = t_as_equivF concl in
  let _penv,qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in
  let phi1 = process_form_opt qenv phi1 None in
  let phi2 = process_form_opt qenv phi2 None in
  (* TODO: check for type unification *)
  let ty = f_ty phi1 in
  t_ppr ty phi1 phi2 g


let process_hoare_bd_hoare g = t_hoare_bd_hoare g
let process_prbounded = t_prbounded
let process_prfalse = t_prfalse
let process_bdeq = t_bdeq


(* -------------------------------------------------------------------- *)
let process_phl loc ptac g =
  let t =
    match ptac with
    | Pfun_def                  -> EcPhlFun.t_fun_def
    | Pfun_abs f                -> EcPhlFun.process_fun_abs f
    | Pfun_upto info            -> EcPhlFun.process_fun_upto info 
    | Pfun_to_code              -> EcPhlFun.t_fun_to_code 
    | Pskip                     -> EcPhlSkip.t_skip
    | Papp (dir, k, phi, f)     -> EcPhlApp.process_app dir k phi f
    | Pwp k                     -> EcPhlWp.t_wp k
    | Psp k                     -> EcPhlSp.t_sp k
    | Prcond (side, b, i)       -> EcPhlRCond.t_rcond side b i
    | Pcond side                -> EcPhlCond.process_cond side
    | Pwhile (side, (phi, vopt))-> EcPhlWhile.process_while side phi vopt
    | Pfission info             -> EcPhlLoopTx.process_fission info
    | Pfusion info              -> EcPhlLoopTx.process_fusion info
    | Punroll info              -> EcPhlLoopTx.process_unroll info
    | Psplitwhile info          -> EcPhlLoopTx.process_splitwhile info
    | Pcall (side, info)        -> EcPhlCall.process_call side info
    | Pswap info                -> EcPhlSwap.process_swap info
    | Pinline info              -> EcPhlInline.process_inline info
    | Pcfold info               -> EcPhlCodeTx.process_cfold info
    | Pkill info                -> EcPhlCodeTx.process_kill info
    | Palias info               -> EcPhlCodeTx.process_alias info
    | Prnd (side, info)         -> EcPhlRnd.process_rnd side info
    | Pconseq (nm,info)         -> EcPhlConseq.process_conseq nm info
    | Phr_exists_elim           -> EcPhlExists.t_hr_exists_elim
    | Phr_exists_intro fs       -> EcPhlExists.process_exists_intro fs
    | Pexfalso                  -> EcPhlExfalso.t_exfalso
    | Pbdhoaredeno info         -> process_bdHoare_deno info
    | PPr (phi1,phi2)           -> process_ppr (phi1,phi2)
    | Pfel (at_pos,info)        -> EcPhlFel.process_fel at_pos info
    | Pequivdeno info           -> process_equiv_deno info
    | Phoare | Pbdhoare         -> process_hoare_bd_hoare
    | Pprbounded                -> process_prbounded
    | Pprfalse                  -> process_prfalse
    | Ppr_rewrite s             -> EcPhlPrRw.t_pr_rewrite s 
    | Pbdeq                     -> process_bdeq
    | Peqobs_in info            -> EcPhlEqobs.process_eqobs_in info
    | Ptrans_stmt info          -> EcPhlTrans.process_equiv_trans info
    | Peager_seq (info,pos,eqR) -> EcEager.process_seq info pos eqR
    | Peager_if                 -> EcEager.t_eager_if
  in
    set_loc loc t g
