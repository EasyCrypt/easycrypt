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
let rec process_logic_tacs mkpv env tacs gs : goals =
  match tacs with
  | [] -> gs

  | {pl_desc = Psubgoal tacs1; pl_loc = loc } :: tacs2 ->
      let gs = set_loc loc (process_subgoal mkpv env tacs1) gs in
        process_logic_tacs mkpv env tacs2 gs

  | tac1 :: tacs2 ->
      let gs = t_on_goals (process_logic_tac mkpv env tac1) gs in
        process_logic_tacs mkpv env tacs2 gs

(* -------------------------------------------------------------------- *)
and process_subgoal mkpv env t gs =
  match t with
  | Psubtacs tacs ->
      t_subgoal (List.map (process_logic_tac mkpv env) tacs) gs

  | Pfirst t -> t_on_first (process_logic_tac mkpv env t) gs
  | Plast  t -> t_on_last  (process_logic_tac mkpv env t) gs

(* -------------------------------------------------------------------- *)
and process_logic_tac mkpv env (tac:ptactic) (g:goal) : goals =
  let myself = process_logic_tac in
  let loc    = tac.pl_loc in

  let tac =
    match unloc tac with
    | Pidtac msg     -> t_id msg
    | Pdo (b, n, t)  -> t_do b n (process_logic_tac mkpv env t)
    | Ptry t         -> t_try (process_logic_tac mkpv env t)
    | Pby t          -> t_close (fun (juc, n) -> process_logic_tacs mkpv env t (juc, [n]))
    | Pseq tacs      -> fun (juc, n) -> process_logic_tacs mkpv env tacs (juc, [n])
    | Psubgoal _     -> assert false
    | Pcase  i       -> process_case loc env i
    | Pprogress t    -> process_progress (myself, mkpv) env t
    | Padmit         -> t_admit
    | Pdebug         -> process_debug env; t_id None
    | Plogic t       -> process_logic mkpv loc env t
    | PPhl tac       -> EcHiPhl.process_phl loc env tac
  in
    set_loc loc tac g
