(* -------------------------------------------------------------------- *)
open EcParsetree
open EcLogic

(* -------------------------------------------------------------------- *)
let process_phl loc ptac g =
  let t =
    match ptac with
    | Pfun `Def                 -> OldEcPhlFun.t_fun_def
    | Pfun (`Abs f)             -> OldEcPhlFun.process_fun_abs f
    | Pfun (`Upto info)         -> OldEcPhlFun.process_fun_upto info
    | Pfun `Code                -> OldEcPhlFun.t_fun_to_code
    | Pskip                     -> EcPhlSkip.t_skip
    | Papp (dir, k, phi, f)     -> EcPhlApp.process_app dir k phi f
    | Pwp k                     -> EcPhlWp.t_wp k
    | Psp k                     -> EcPhlSp.t_sp k
    | Prcond (side, b, i)       -> EcPhlRCond.t_rcond side b i
    | Pcond side                -> EcPhlCond.process_cond side
    | Pwhile(side,(phi,vopt,info))->EcPhlWhile.process_while side phi vopt info
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
    | Pset info                 -> EcPhlCodeTx.process_set info
    | Prnd (side, info)         -> EcPhlRnd.process_rnd side info
    | Pconseq (nm,info)         -> OldEcPhlConseq.process_conseq nm info
    | Phr_exists_elim           -> EcPhlExists.t_hr_exists_elim
    | Phr_exists_intro fs       -> EcPhlExists.process_exists_intro fs
    | Pexfalso                  -> EcPhlExfalso.t_exfalso
    | Pbydeno (mode, info)      -> EcPhlDeno.process_deno mode info
    | PPr info                  -> EcPhlPr.process_ppr info
    | Pfel (at_pos, info)       -> EcPhlFel.process_fel at_pos info
    | Phoare                    -> EcPhlBdHoare.t_hoare_bd_hoare
    | Pbdhoare_split i          -> EcPhlBdHoare.process_bdhoare_split i
    | Pprbounded                -> EcPhlPr.t_prbounded true
    | Psim info                 -> EcPhlEqobs.process_eqobs_in info
    | Ptrans_stmt info          -> EcPhlTrans.process_equiv_trans info
    | Psymmetry                 -> EcPhlSym.process_equiv_sym
    | Peager_seq (info,pos,eqR) -> EcEager.process_seq info pos eqR
    | Peager_if                 -> EcEager.process_if
    | Peager_while info         -> EcEager.process_while info
    | Peager_fun_def            -> EcEager.process_fun_def 
    | Peager_fun_abs(info,eqI)  -> EcEager.process_fun_abs info eqI
    | Peager_call info          -> EcEager.process_call info
    | Peager(info, eqI)         -> EcEager.process_eager info eqI
    | Pbd_equiv info            -> 
      let side, pr, po = info in
      let info = Some {fp_kind = FPCut((Some pr,Some po),None); fp_args = []} in
      let info2, info3 = if side then info, None else None, info in
      OldEcPhlConseq.process_conseq true (None, info2, info3)
    | Pauto                     -> EcAuto.t_auto 

  in
    set_loc loc t g
