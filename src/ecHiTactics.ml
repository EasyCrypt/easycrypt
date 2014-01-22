(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree
open EcFol

open EcLogic
open EcHiLogic
open EcCoreHiPhl

(* -------------------------------------------------------------------- *)
let process_case loc gp g =
  let form_of_gp () =
    match gp with
    | [`Form (occ, pf)] ->
        if occ <> None then
          tacuerror ~loc "cannot specify an occurence selector"
        else pf
    | _ -> tacuerror ~loc "must give exactly one boolean formula"
  in
    match (get_concl g).f_node with
    | FbdHoareS _ | FhoareS _ -> 
        EcPhlCase.t_hl_case
          (process_phl_formula g (form_of_gp ())) g

    | FequivS _ -> 
        EcPhlCase.t_equiv_case
          (process_prhl_formula g (form_of_gp ())) g

    | _ -> process_case loc gp g

(* -------------------------------------------------------------------- *)
let process_debug (juc, n) = (juc, [n])

(* -------------------------------------------------------------------- *)
let process_admit g =
  (* FIXME: use notifier *)
  EcFortune.pick () |> oiter (fun msg -> Printf.printf "[W] %s\n%!" msg);
  t_admit g

(* -------------------------------------------------------------------- *)
let process_progress s (prtc, mkpv) t =
  let t = 
    match t with 
    | None   -> t_id None 
    | Some t -> 
      if s then tacuerror "progress * do not accept tactic";
      prtc mkpv t
  in
  if s then t_progress_one
  else t_progress t 

(* -------------------------------------------------------------------- *)
let rec process_tactics mkpv (tacs : ptactic list) (gs : goals) : goals =
  match tacs with
  | [] -> gs

  | tac1 :: tacs2 ->
      let gs = process_tactic mkpv tac1 gs in
        process_tactics mkpv tacs2 gs

(* -------------------------------------------------------------------- *)
and process_tactic_chain mkpv (t : ptactic_chain) (gs : goals) : goals =
  match t with
  | Psubtacs tacs   -> t_subgoal   (List.map (process_tactic1 mkpv) tacs) gs
  | Pfirst   (t, i) -> t_on_firsts (process_tactic1 mkpv t) i gs
  | Plast    (t, i) -> t_on_lasts  (process_tactic1 mkpv t) i gs
  | Protate  (d, i) -> t_rotate    d i gs

(* -------------------------------------------------------------------- *)
and process_tactic mkpv (tac : ptactic) (gs : goals) : goals =
  let cf =
    match unloc tac.pt_core with
    | Plogic (Pintro _ | Prewrite _ | Pgeneralize _ )
    | Pidtac _ -> true
    | _ -> false
  in

  let gs = process_tactic_core mkpv tac.pt_core gs in
  let gs = EcHiLogic.process_mintros ~cf tac.pt_intros gs in
    gs

(* -------------------------------------------------------------------- *)
and process_tactic1 mkpv (tac : ptactic) ((juc, n) : goal) : goals =
  process_tactic mkpv tac (juc, [n])

(* -------------------------------------------------------------------- *)
and process_tactic_core mkpv (tac : ptactic_core) (gs : goals) : goals =
  let loc = tac.pl_loc in
  let eng = process_tactic_core1 mkpv in

  let tac =
    match unloc tac with
    | Pidtac msg      -> `One (t_id msg)
    | Pdo ((b, n), t) -> `One (t_do b n (process_tactic_core1 mkpv t))
    | Ptry t          -> `One (t_try (process_tactic_core1 mkpv t))
    | Pby t           -> `One (process_by mkpv t)
    | Por (t1, t2)    -> `One (process_or  mkpv t1 t2)
    | Pseq tacs       -> `One (fun (juc, n) -> process_tactics mkpv tacs (juc, [n]))
    | Pcase i         -> `One (process_case loc i)
    | Pprogress (s,t) -> `One (process_progress s (process_tactic_core1,mkpv) t)
    | Padmit          -> `One (process_admit)
    | Pdebug          -> `One (process_debug)
    | Plogic t        -> `One (process_logic (eng, mkpv) loc t)
    | PPhl tac        -> `One (EcHiPhl.process_phl loc tac)
    | Psubgoal tc     -> `All (process_tactic_chain mkpv tc)
  in

  let tac = match tac with `One t -> t_on_goals t | `All t -> t in

    set_loc loc tac gs

(* -------------------------------------------------------------------- *)
and process_tactic_core1 mkpv (tac : ptactic_core) ((juc, n) : goal) : goals =
  process_tactic_core mkpv tac (juc, [n])

(* -------------------------------------------------------------------- *)
and process_by mkpv t (juc, n) =
  let goal =
    match t with
    | None   -> (juc, [n])
    | Some t -> process_tactics mkpv t (juc, [n])
  in
    t_on_goals EcHiLogic.process_done goal

(* -------------------------------------------------------------------- *)
and process_or mkpv t1 t2 g =
  t_or
    (process_tactic1 mkpv t1)
    (process_tactic1 mkpv t2)
    g
