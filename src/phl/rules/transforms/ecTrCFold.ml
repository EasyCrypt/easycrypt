(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcTypes
open EcModules
open EcFol
open EcPV
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the [cfold] transformation, resolved: the position is a
   normalized (possibly nested) code position. *)
type tr_cfold = {
  trcf_at    : EcMatching.Position.nm_codepos;
  trcf_len   : int option;
  trcf_eager : bool;
}

type EcPlTransform.transform += TrCFold of tr_cfold

(* -------------------------------------------------------------------- *)
let invalid fmt = Format.kasprintf (fun msg -> raise (InvalidTransform msg)) fmt

(* -------------------------------------------------------------------- *)
(* Constant folding (see the [.mli]). The scan works on a block starting
   at an assignment to local variables.

  It initializes:
  - propagate: a substitution mapping the assigned variables to their values
  - preserve : for each propagated variable, the variables that must keep their
    current value for that propagated expression to remain valid

  It then scans subsequent instructions from left to right.

  For assignments:
  - if the assigned variable is preserved, stop in non-eager mode; in eager
    mode, substitute in the right-hand side and promote that variable to the
    propagated substitution
  - if the assigned variable is already propagated, update its propagated value
    and recompute its preservation set
  - otherwise, substitute propagated values in the right-hand side and keep the
    assignment

  For calls, loops, conditionals, matches, and random samplings:
  - continue only if none of the currently propagated or preserved variables is
    written by the instruction; in that case, substitute propagated values in
    the instruction
  - otherwise, stop

  For abstract instructions without calls:
  - continue only if they neither read nor write propagated or preserved
    variables
  - otherwise, stop

  When the scan stops, the remaining propagated substitution is materialized as
  assignments appended after the transformed prefix.

  The values are simplified without delta (the local definitions of the
  goal are not unfolded): the entry simplifies under its environment only.
*)
let cfold (p : tr_cfold) (ctxt : tr_ctxt) (s : stmt) =
  let env   = ctxt.trc_env in
  let me    = ctxt.trc_me in
  let eager = p.trcf_eager in
  let hyps  = EcEnv.LDecl.init env [] in

  let zpr =
    try  Zpr.zipper_of_nm_cpos p.trcf_at s
    with EcMatching.Position.InvalidCPos -> invalid "invalid code position" in

  let e_simplify (e : expr) =
    let e = form_of_expr ~m:(fst me) e in
    let e = EcReduction.simplify EcReduction.nodelta hyps e in
    expr_of_ss_inv { m = fst me; inv = e } in

  let i_simplify (i : instr) =
    i_map_expr e_simplify i in

  (*
     Process one instruction under the current propagated substitution and
     preservation map.

     - `Continue ((subst, preserve), is)` means that propagation may proceed,
       with updated state and replacement instructions `is`
     - `Interrupt` means that propagation stops before this instruction

     In eager mode, assigning to a preserved variable does not stop the scan:
     the assigned expression is first substituted, then that variable is
     promoted into the propagated substitution.
   *)
  let for_instruction (subst, preserve: (expr, unit) Mpv.t * (PV.t Mnpv.t)) (i : instr) =
    let esubst subst e =
      EcPV.Mpv.esubst env subst e |> e_simplify
    in
    let isubst subst i =
      EcPV.Mpv.isubst env subst i |> i_simplify
    in
    let is_preserved preserve pv =
      Mnpv.exists (fun _ preserve -> EcPV.PV.mem_pv env pv preserve) preserve
    in
    let is_propagated subst pv =
      Mnpv.contains (Mpv.pvs subst) pv
    in
    let propagated_pvs subst =
      (Mpv.pvs subst) |> Mnpv.bindings |> List.fst
    in
    (* Update preserve vars on assignment to given PV  *)
    (* Do not include any propagated vars, since these *)
    (* are automatically preserved by construction     *)
    let update_preserved preserve subst pv e =
      let rd = EcPV.e_read env e in
      let rd = List.fold_left (fun rd pv ->
        EcPV.PV.remove env pv rd
      ) rd (propagated_pvs subst)
      in
      Mnpv.add pv rd preserve
    in
    let promote_preserved_to_propagated subst preserve pv (e:expr) =
      let preserve = Mnpv.map (fun preserve ->
        PV.remove env pv preserve
      ) preserve
      in
      let subst = Mpv.add env pv e subst in
      (subst, preserve)
    in

    match i.i_node with
    | Sasgn (lv, e) ->
      let asgns = explode_assgn lv e in
      let exception Abort in
      begin try
        let (subst, preserve), asgns = List.fold_left_map (fun (subst, preserve) ((pv, t), e) ->
          (* 1. When hitting an assignment to a preserved var *)
          if is_preserved preserve pv then
            if eager (* 1.1 Promote to propagated on eager *)
            then
              let e = esubst subst e in
              promote_preserved_to_propagated subst preserve pv e, None
            else raise Abort (* 1.2 Fail on non-eager *)
          else
          (* 2. When not preserved and not propagated, do nothing *)
          if not (is_propagated subst pv) then
            (subst, preserve), Some ((pv, t), esubst subst e)
          (* 3. When propagated, propagate *)
          else
            let e = esubst subst e in
            let preserve = update_preserved preserve subst pv e in
            let subst = Mpv.add env pv e subst in
            (subst, preserve), None
        ) (subst, preserve) asgns
        in
        let asgns = List.filter_map identity asgns in
        `Continue ((subst, preserve), Option.to_list (i_asgn_of_pve asgns))
        with Abort -> `Interrupt
      end

    | Srnd _
    | Scall _
    | Swhile _
    | Sif _
    | Smatch _ ->
      let wr = EcPV.i_write env i in
      let spvs = Mnpv.keys (Mpv.pvs subst) in
      let ppvs = Mnpv.keys preserve in
      if
        let check = List.for_all (fun pv ->
        not @@ EcPV.PV.mem_pv env pv wr) in
        check spvs && check ppvs
      then
        `Continue ((subst, preserve), [isubst subst i])
      else
        `Interrupt

    | Sraise _ -> `Interrupt

    | Sabstract id ->
      let aus = EcEnv.AbsStmt.byid id env in
      begin match aus with
      | { aus_calls = []; aus_reads; aus_writes } ->
        if List.for_all (fun (pv, _) ->
          not ((is_propagated subst pv) || (is_preserved preserve pv))
        ) (aus_reads @ aus_writes) then
          `Continue ((subst, preserve), [i])
        else
          `Interrupt
      | _ -> `Interrupt
      end
  in

  let body, epilog =
    match p.trcf_len with
    | None ->
      (zpr.Zpr.z_tail, [])
    | Some olen ->
      if List.length zpr.Zpr.z_tail < olen+1 then
        invalid "expecting at least %d instructions" olen;
      List.takedrop (olen+1) zpr.Zpr.z_tail in

  let _lv, (subst, _preserve), body, rem =
    match body with
    | { i_node = Sasgn (lv, e) } :: is ->
      let asgns = explode_assgn lv e in
      let lv = List.fst asgns in

      if not (List.for_all (is_loc -| fst) lv) then
        invalid "left-values must be made of local variables only";

      (* Variables in the domain of substs
         are variables to be propagated    *)
      let subst =
        List.fold_left
          (fun subst ((pv, _), e) -> Mpv.add env pv e subst)
          Mpv.empty asgns in

      let preserve =
        List.fold_left
          (fun preserve ((pv, _), e) ->
            Mnpv.add
              pv
              EcPV.(PV.remove env pv (e_read env e))
              preserve)
          Mnpv.empty
          asgns
      in

      let (subst, preserve), is, rem =
        List.fold_left_map_while for_instruction (subst, preserve) is in

      lv, (subst, preserve), List.flatten is, rem

    | _ ->
      invalid "cannot find a left-value assignment at given position"
  in

  let asgns = Mnpv.bindings (Mpv.pvs subst) in

  let lv, es = List.map (fun (pv, e) ->
    (pv, e_ty e), e) asgns |> List.split
  in

  let asgn =
    lv_of_list lv
    |> Option.map (fun lv -> i_asgn (lv, e_tuple es))
    |> Option.to_list in

  let zpr =
    { zpr with Zpr.z_tail = body @ asgn @ rem @ epilog } in

  { trr_me  = me;
    trr_s   = Zpr.zip zpr;
    trr_obl = []; }

let () =
  register (function
    | TrCFold p -> Some (cfold p)
    | _ -> None)
