(* -------------------------------------------------------------------- *)
open EcParsetree
open EcLocation
open EcBaseLogic
open EcLogic

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
    | Pbdhoaredeno info         -> EcPhlDeno.process_bdHoare_deno info
    | PPr (phi1, phi2)          -> EcPhlPr.process_ppr (phi1, phi2)
    | Pfel (at_pos, info)       -> EcPhlFel.process_fel at_pos info
    | Pequivdeno info           -> EcPhlDeno.process_equiv_deno info
    | Phoare | Pbdhoare         -> EcPhlBdHoare.t_hoare_bd_hoare
    | Pprbounded                -> EcPhlPr.t_prbounded true
    | Pprfalse                  -> EcPhlPr.t_prfalse
    | Ppr_rewrite s             -> EcPhlPrRw.t_pr_rewrite s 
    | Pbdeq                     -> EcPhlBdHoare.t_bdeq
    | Peqobs_in info            -> EcPhlEqobs.process_eqobs_in info
    | Ptrans_stmt info          -> EcPhlTrans.process_equiv_trans info
    | Psymmetry                 -> EcPhlSym.process_equiv_sym
    | Peager_seq (info,pos,eqR) -> EcEager.process_seq info pos eqR
    | Peager_if                 -> EcEager.t_eager_if
    | Peager_while info         -> EcEager.process_while info
  in
    set_loc loc t g
