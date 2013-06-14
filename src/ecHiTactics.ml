(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcLocation
open EcSymbols
open EcParsetree
open EcTypes
open EcModules
open EcFol

open EcBaseLogic
open EcLogic
open EcHiLogic
open EcHiPhl

(* -------------------------------------------------------------------- *)
let process_case loc env pf g =
  let concl = get_concl g in
  match concl.f_node with
  | FhoareS _ ->
    let f = process_phl_formula env g pf in
    EcPhl.t_hoare_case f g
  | FequivS _ ->
    let f = process_prhl_formula env g pf in
    EcPhl.t_equiv_case f g
  | _ ->
    let f = process_formula env g pf in
    t_seq (set_loc loc (t_case env f))
      (t_simplify env EcReduction.betaiota_red) g

(* -------------------------------------------------------------------- *)
let process_debug env =
  let l = fun x -> EcLocation.mk_loc EcLocation._dummy x in
  let (p, _) = EcTyping.trans_msymbol env (l [(l "M", Some [l [(l "K", None)]])]) in
    ignore (EcEnv.Mod.by_mpath p env)

(* -------------------------------------------------------------------- *)
let process_progress (prtc, mkpv) env t =
  let t = 
    match t with 
    | None   -> t_id None 
    | Some t -> prtc mkpv env t
  in
    t_progress env t

(* -------------------------------------------------------------------- *)
let rec process_tactics mkpv env (tacs : ptactic list) (gs : goals) : goals =
  match tacs with
  | [] -> gs

  | tac1 :: tacs2 ->
      let gs = process_tactic mkpv env tac1 gs in
        process_tactics mkpv env tacs2 gs

(* -------------------------------------------------------------------- *)
and process_tactic_chain mkpv env (t : ptactic_chain) (gs : goals) : goals =
  match t with
  | Psubtacs tacs -> t_subgoal  (List.map (process_tactic1 mkpv env) tacs) gs
  | Pfirst   t    -> t_on_first (process_tactic1 mkpv env t) gs
  | Plast    t    -> t_on_last  (process_tactic1 mkpv env t) gs
  | Protate  d    -> t_rotate   d gs

(* -------------------------------------------------------------------- *)
and process_tactic mkpv env (tac : ptactic) (gs : goals) : goals =
  let dointros pis =
    let mk_id (IPCore s) = lmap (fun s -> EcIdent.create (odfl "_" s)) s in
      t_intros env (List.map mk_id pis)
  in

  let gs = process_tactic_core mkpv env tac.pt_core gs in
  let gs = t_on_goals (dointros tac.pt_intros) gs in
    gs

(* -------------------------------------------------------------------- *)
and process_tactic1 mkpv env (tac : ptactic) ((juc, n) : goal) : goals =
  process_tactic mkpv env tac (juc, [n])

(* -------------------------------------------------------------------- *)
and process_tactic_core mkpv env (tac : ptactic_core) (gs : goals) : goals =
  let loc = tac.pl_loc in

  let tac =
    match unloc tac with
    | Pidtac msg     -> `One (t_id msg)
    | Pdo (b, n, t)  -> `One (t_do b n (process_tactic_core1 mkpv env t))
    | Ptry t         -> `One (t_try (process_tactic_core1 mkpv env t))
    | Pby t          -> `One (t_close (fun (juc, n) -> process_tactics mkpv env t (juc, [n])))
    | Pseq tacs      -> `One (fun (juc, n) -> process_tactics mkpv env tacs (juc, [n]))
    | Pcase  i       -> `One (process_case loc env i)
    | Pprogress t    -> `One (process_progress (process_tactic_core1, mkpv) env t)
    | Padmit         -> `One (t_admit)
    | Pdebug         -> `One (process_debug env; t_id None)
    | Plogic t       -> `One (process_logic mkpv loc env t)
    | PPhl tac       -> `One (EcHiPhl.process_phl loc env tac)
    | Psubgoal tc    -> `All (process_tactic_chain mkpv env tc)
  in

  let tac = match tac with `One t -> t_on_goals t | `All t -> t in

    set_loc loc tac gs

(* -------------------------------------------------------------------- *)
and process_tactic_core1 mkpv env (tac : ptactic_core) ((juc, n) : goal) : goals =
  process_tactic_core mkpv env tac (juc, [n])
