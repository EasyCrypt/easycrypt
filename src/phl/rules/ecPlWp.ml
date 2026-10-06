(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcAst
open EcModules
open EcFol

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Weakest preconditions of statement suffixes, shared by the wp rules of
   every logic. A statement is traversed backwards, instruction by
   instruction, as long as its wp can be computed; the instructions that
   could not be traversed are returned, so that callers know the prefix
   that remains.

   Please, note that WP only operates over assignments and conditional
   statements (and, one-sided, [raise]). Any weakening of this restriction
   may break the soundness of the bounded hoare logic. *)

exception No_wp

(* -------------------------------------------------------------------- *)
let find_poe hyps memenv epost (e : EcTypes.expr) =
  let m = EcMemory.memory memenv in
  let f = form_of_expr ~m e in
  let f = EcReduction.h_red_until EcReduction.full_red hyps f in
  let (ex, tyargs), args = destr_op_app f in

  assert (List.is_empty tyargs);

  let default_exn () =
    match Mop.find_opt None epost with
    | Some body -> body
    | None ->
      tacuerror
        "missing postcondition for exception %a"
        EcPrinting.pp_path ex in

  let body =
    Mop.find_opt (Some ex) epost
    |> ofdfl (fun () -> default_exn ()) in

  f_app_simpl body args EcTypes.tbool

let wp_asgn_aux memenv lv e (lets, f) =
  let m = EcMemory.memory memenv in
  let let1 = lv_subst m lv (ss_inv_of_expr m e).inv in
    (let1::lets, f)

(* -------------------------------------------------------------------- *)
let rec wp_stmt
  ?(mc       : (memory * memory) option)
   (onesided : bool)
   (hyps     : EcEnv.LDecl.hyps)
   (memenv   : memenv)
   (stmt     : instr list)
   (letsf    : _)
   (epost    : form Mop.t)
=
  match stmt with
  | [] -> (stmt, letsf)
  | i :: stmt' ->
      try
        let letsf = wp_instr ?mc onesided hyps memenv i letsf epost in
        wp_stmt ?mc onesided hyps memenv stmt' letsf epost
      with No_wp -> (stmt, letsf)

and wp_instr
  ?(mc       : (memory * memory) option)
   (onesided : bool)
   (hyps     : EcEnv.LDecl.hyps)
   (memenv   : memenv)
   (i        : instr)
   (letsf    : _)
   (epost    : form Mop.t)
=
  match i.i_node with
  | Sasgn (lv,e) ->
    wp_asgn_aux memenv lv e letsf

  | Sif (e,s1,s2) ->
      let (r1,letsf1) =
        wp_stmt ?mc onesided hyps memenv (List.rev s1.s_node) letsf epost in
      let (r2,letsf2) =
        wp_stmt ?mc onesided hyps memenv (List.rev s2.s_node) letsf epost in
      if List.is_empty r1 && List.is_empty r2 then begin
        let env = EcEnv.LDecl.toenv hyps in
        let post1 = mk_let_of_lv_substs ?mc:mc env letsf1 in
        let post2 = mk_let_of_lv_substs ?mc:mc env letsf2 in
        let m = EcMemory.memory memenv in
        let post  = f_if (ss_inv_of_expr m e).inv post1 post2 in
        ([], post)
      end else raise No_wp

  | Smatch (e, bs) -> begin
      let wps =
        let do1 (_, s) =
          wp_stmt ?mc onesided hyps memenv (List.rev s.s_node) letsf epost in
        List.map do1 bs
      in

      if not (List.for_all (fun (r, _) -> List.is_empty r) wps) then
        raise No_wp;
      let pbs =
        List.map2
          (fun (bds, _) (_, letsf) ->
            let post = mk_let_of_lv_substs (EcEnv.LDecl.toenv hyps) letsf in
            f_lambda (List.map (snd_map gtty) bds) post)
          bs wps
      in
      let m = EcMemory.memory memenv in
      let post = f_match (ss_inv_of_expr m e).inv pbs EcTypes.tbool in
      ([],post)
    end

  | Sraise e when onesided ->
    ([], find_poe hyps memenv epost e)

  | _ -> raise No_wp

(* -------------------------------------------------------------------- *)
let rec ewp_stmt env (memenv:EcMemory.memenv) (stmt: EcModules.instr list) letspf =
  match stmt with
  | [] -> stmt, letspf
  | i :: stmt' ->
      try
        let letspf = ewp_instr env memenv i letspf in
        ewp_stmt env memenv stmt' letspf
      with No_wp -> (stmt, letspf)

and ewp_instr env (memenv:EcMemory.memenv) i letspf =
  match i.i_node with
  | Sasgn (lv, e) ->
    wp_asgn_aux memenv lv e letspf

  | Srnd(lv, distr) ->
    let (lets,f) = letspf in
    let ty_distr = proj_distr_ty env (EcTypes.e_ty distr) in
    let x_id = EcIdent.create (symbol_of_lv lv) in
    let x = f_local x_id ty_distr in
    let m = EcMemory.memory memenv in
    let distr = (EcFol.ss_inv_of_expr m distr).inv in
    let let1 = lv_subst m lv x in
    let lets = let1 :: lets in
    let f = mk_let_of_lv_substs env (lets,f) in
    let f = f_Ep ty_distr distr (f_lambda [(x_id,GTty ty_distr)] f) in
    ([], f)

  | Sif(e, s1, s2) ->
    let r1,(lets1,f1) = ewp_stmt env memenv (List.rev s1.s_node) letspf in
    let r2,(lets2,f2) = ewp_stmt env memenv (List.rev s2.s_node) letspf in
    if List.is_empty r1 && List.is_empty r2 then begin
      let f1 = mk_let_of_lv_substs env (lets1,f1) in
      let f2 = mk_let_of_lv_substs env (lets2,f2) in
      let m = EcMemory.memory memenv in
      let e = (ss_inv_of_expr m e).inv in
      let f = f_if e f1 f2 in
      ([], f)
    end else raise No_wp

  | _ -> raise No_wp

(* -------------------------------------------------------------------- *)
let wp
  ?(mc       : (memory * memory) option)
  ?(uselet   : bool = true)
  ?(onesided : bool = false)
   (hyps     : EcEnv.LDecl.hyps)
   (m        : memenv)
   (s        : stmt)
   (poe      : exnpost)
=
  let post, epost = POE.destruct poe in
  let (r, letsf) =
    wp_stmt ?mc onesided hyps m (List.rev s.s_node) ([], post) epost
  in
  let pre = mk_let_of_lv_substs ?mc ~uselet (EcEnv.LDecl.toenv hyps) letsf in
  (List.rev r, pre)

let ewp ?(uselet=true) env m s post =
  let r,(lets,f) = ewp_stmt env m (List.rev s.s_node) ([],post) in
  let pre = mk_let_of_lv_substs ~uselet env (lets,f) in
  (List.rev r, pre)

(* -------------------------------------------------------------------- *)
let check_wp_progress tc (i : 'a option) (rm : instr list) =
  if is_some i && not (List.is_empty rm) then
    tc_error !!tc "remaining %i instruction(s)" (List.length rm)
