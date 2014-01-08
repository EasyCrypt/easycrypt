(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcLocation
open EcTypes
open EcModules
open EcFol
open EcBaseLogic
open EcLogic
open EcPV
open EcCorePhl

(* -------------------------------------------------------------------- *)
class rn_hl_swap side pos1 pos2 pos3 =
object
  inherit xrule "[hl] swap"

  method side : bool option = side
  method pos1 : int = pos1
  method pos2 : int = pos2
  method pos3 : int = pos3
end

let rn_hl_swap side pos1 pos2 pos3 =
  RN_xtd (new rn_hl_swap side pos1 pos2 pos3 :> xrule)

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  let check_swap env s1 s2 = 
    let m1,m2 = s_write env s1, s_write env s2 in
    let r1,r2 = s_read  env s1, s_read env s2 in
    (* FIXME it is not suffisant *)
    let m2r1 = PV.interdep env m2 r1 in
    let m1m2 = PV.interdep env m1 m2 in
    let m1r2 = PV.interdep env m1 r2 in
    let error mode d = 
      EcLogic.tacuerror 
        "cannot swap: the two statements are not independent, %t"
        (fun fmt ->
           let (s1, s2) =
             match mode with
             | `RW -> "read" , "written"
             | `WR -> "write", "read"
           in
             Format.fprintf fmt
               "the first statement can %s %a which can be %s by the second"
               s1 (PV.pp env) d s2)
    in
      if not (PV.is_empty m2r1) then error `RW m2r1;
      if not (PV.is_empty m1m2) then error `WR m1m2;
      if not (PV.is_empty m1r2) then error `WR m1r2

  let swap_stmt env p1 p2 p3 s = 
    let s = s.s_node in
    let len = List.length s in
    if not (1<= p1 && p1 < p2 && p2 <= p3 && p3 <= len) then
      cannot_apply "swap" 
        (Format.sprintf
           "invalid position, 1 <= %i < %i <= %i <= %i"
           p1 p2 p3 len);
    let hd,tl = List.take_n (p1-1) s in
    let s12,tl = List.take_n (p2-p1) tl in
    let s23,tl = List.take_n (p3-p2+1) tl in
      check_swap env (stmt s12) (stmt s23);
      stmt (List.flatten [hd;s23;s12;tl]) 
end

(* -------------------------------------------------------------------- *)
let t_hoare_swap p1 p2 p3 g =
  let env,_,concl = get_goal_e g in
  let hs    = t_as_hoareS concl in
  let s = LowInternal.swap_stmt env p1 p2 p3 hs.hs_s in
  let concl = f_hoareS_r {hs with hs_s = s } in
    prove_goal_by [concl] (rn_hl_swap None p1 p2 p3) g

let t_bdHoare_swap p1 p2 p3 g =
  let env,_,concl = get_goal_e g in
  let bhs    = t_as_bdHoareS concl in
  let s = LowInternal.swap_stmt env p1 p2 p3 bhs.bhs_s in
  let concl = f_bdHoareS_r {bhs with bhs_s = s } in
    prove_goal_by [concl] (rn_hl_swap None p1 p2 p3) g

let t_equiv_swap side p1 p2 p3 g =
  let env,_,concl = get_goal_e g in
  let es    = t_as_equivS concl in
  let sl,sr = 
    match side with
    | true  -> LowInternal.swap_stmt env p1 p2 p3 es.es_sl, es.es_sr
    | false -> es.es_sl, LowInternal.swap_stmt env p1 p2 p3 es.es_sr
  in
  let concl = f_equivS_r {es with es_sl = sl; es_sr = sr } in
    prove_goal_by [concl] (rn_hl_swap (Some side) p1 p2 p3) g

(* -------------------------------------------------------------------- *)
module HiInternal = struct
  let stmt_length side concl = 
    match concl.f_node, side with
    | FhoareS hs, None -> List.length hs.hs_s.s_node
    | FbdHoareS bhs, None -> List.length bhs.bhs_s.s_node
    | FequivS es, Some side -> 
      List.length (if side then es.es_sl.s_node else es.es_sr.s_node)
    | FequivS _, None -> assert false 
    | _ -> cannot_apply "stmt_length" "a phl/pbhl/prhl judgement was expected"
end

(* -------------------------------------------------------------------- *)
let rec process_swap1 info g =
  let side,pos = info.pl_desc in
  let concl = get_concl g in
  if is_equivS concl && side = None then
    t_seq (process_swap1 {info with pl_desc = (Some true, pos)})
      (process_swap1 {info with pl_desc = (Some false, pos)}) g 
  else
    let p1, p2, p3 = match pos with
      | SKbase(p1,p2,p3) -> p1, p2, p3
      | SKmove p ->
        if 0 < p then 1, 2, p+1
        else if p < 0 then
          let len = HiInternal.stmt_length side concl in
          len+p, len, len
        else (* p = 0 *) 0,0,0
      | SKmovei(i,p) ->
        if 0 < p then i, i+1, i+p
        else if p < 0 then i+p, i, i
        else (* p = 0 *) 0,0,0
      | SKmoveinter(i1,i2,p) ->
        if 0 < p then i1, i2+1, i2+p
        else if p < 0 then i1+p, i1, i2
        else (* p = 0 *) 0,0,0
    in
    let tac =
      if p1 = 0 then t_id None else
        match side with
        | None when is_hoareS concl ->
          t_hoare_swap p1 p2 p3
        | None when is_bdHoareS concl ->
          t_bdHoare_swap p1 p2 p3
        | None ->
          t_seq (process_swap1 {info with pl_desc = (Some true, pos)})
            (process_swap1 {info with pl_desc = (Some false, pos)})
        | Some side ->
          t_equiv_swap side p1 p2 p3
    in
    set_loc info.pl_loc tac g


let process_swap info =
  t_lseq (List.map process_swap1 info)
