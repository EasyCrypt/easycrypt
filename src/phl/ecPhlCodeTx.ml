(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcPV
open EcCorePhl

module Mid = EcIdent.Mid
module Zpr = EcMetaProg.Zipper

(* -------------------------------------------------------------------- *)
class rn_hl_kill side cpos len =
object
  inherit xrule "[hl] kill"

  method side     : bool option = side
  method position : codepos     = cpos
  method length   : int option  = len
end

let rn_hl_kill side cpos len =
  RN_xtd (new rn_hl_kill side cpos len :> xrule)

let t_kill side cpos olen g =
  let env = LDecl.toenv (get_hyps g) in
  let kill_stmt _env (_, po) me zpr =
    let error fmt =
      (* TO BE MOVED *)
      let buf  = Buffer.create 127 in
      let fbuf = Format.formatter_of_buffer buf in
        Format.kfprintf
          (fun _ ->
            Format.pp_print_flush fbuf ();
            tacuerror "cannot kill code, %s" (Buffer.contents buf))
          fbuf fmt
    in

    let (ks, tl) =
      match olen with
      | None -> (zpr.Zpr.z_tail, [])
      | Some len ->
          if List.length zpr.Zpr.z_tail < len then
            tacuerror "cannot find %d consecutive instructions at given position" len;
          List.take_n len zpr.Zpr.z_tail
    in

    let ks_wr = is_write env PV.empty ks in
    (* FIXME [BG]: check the usage of po_rd *)
    let po_rd = PV.fv env (fst me) po in

    let pp_of_name =
      let ppe = EcPrinting.PPEnv.ofenv env in
        fun fmt x ->
          match x with
          | `Global p -> EcPrinting.pp_topmod ppe fmt p
          | `PV     p -> EcPrinting.pp_pv     ppe fmt p
    in

    List.iteri
      (fun i is ->
         let is_rd = is_read env PV.empty is in
         let indp  = PV.interdep env ks_wr is_rd in
           match PV.pick indp with
           | None   -> ()
           | Some x ->
               match i with
               | 0 ->
                   error
                     "code writes variables (%a) used by the current block"
                     pp_of_name x
               | _ ->
                 error
                   "code writes variables (%a) used by the %dth parent block"
                   pp_of_name x i)
      (Zpr.after ~strict:false { zpr with Zpr.z_tail = tl; });

    begin
      match PV.pick (PV.interdep env ks_wr po_rd) with
      | None   -> ()
      | Some x ->
          error
            "code writes variables (%a) used by the post-condition"
            pp_of_name x
    end;

    let kslconcl = EcFol.f_bdHoareS me f_true (stmt ks) f_true FHeq f_r1 in
      (me, { zpr with Zpr.z_tail = tl; }, [kslconcl])
  in

  let tr = fun side -> rn_hl_kill side cpos olen in
    t_code_transform side ~bdhoare:true cpos tr (t_zip kill_stmt) g

(* -------------------------------------------------------------------- *)
class rn_hl_alias side pos =
object
  inherit xrule "[hl] alias"

  method side     : bool option = side
  method position : codepos     = pos
end

let rn_hl_alias side pos =
  RN_xtd (new rn_hl_alias side pos :> xrule)

let alias_stmt id _ me i =
  match i.i_node with
  | Srnd (lv, e) ->
      let id       = odfl "x" (omap EcLocation.unloc id) in
      let ty       = e.e_ty in
      let id       = { v_name = id; v_type = ty; } in
      let (me, id) = fresh_pv me id in
      let pv       = pv_loc (EcMemory.xpath me) id in

        (me, [i_rnd (LvVar (pv, ty), e); i_asgn (lv, e_var pv ty)])

  | _ ->
      tacuerror "cannot create an alias for that kind of instruction"

let t_alias side cpos id g =
  let tr = fun side -> rn_hl_alias side cpos in
  t_code_transform side ~bdhoare:true cpos tr (t_fold (alias_stmt id)) g

(* -------------------------------------------------------------------- *)
class rn_hl_set side pos =
object
  inherit xrule "[hl] set"

  method side     : bool option = side
  method position : codepos     = pos
end

let rn_hl_set side pos =
  RN_xtd (new rn_hl_set side pos :> xrule)

let set_stmt fresh id e = 
  let get_i me = 
    let id       = EcLocation.unloc id in
    let  v       = { v_name = id; v_type = e.e_ty } in
    let (me, id) = fresh_pv me v in
    let pv       = pv_loc (EcMemory.xpath me) id in
    me,i_asgn (LvVar(pv,e.e_ty), e) in
  let get_i = 
    if fresh then get_i 
    else
      let res = ref None in
      fun me ->
        if !res = None then res := Some (get_i me);
        oget !res in
  fun _ _ me z ->
    let me,i = get_i me in
    (me, {z with Zpr.z_tail = i::z.Zpr.z_tail},[])

let t_set fresh side cpos id e g =
  let tr = fun side -> rn_hl_set side cpos in
  t_code_transform side ~bdhoare:true cpos tr (t_zip (set_stmt fresh id e)) g

(* -------------------------------------------------------------------- *)
let cfold_stmt env me olen zpr =
  let (asgn, i, tl) =
    match zpr.Zpr.z_tail with
    | ({ i_node = Sasgn (lv, e) } as i) :: tl -> begin
      let asgn =
        match lv with
        | LvMap _ -> tacuerror "left-value is a map assignment"
        | LvVar (x, ty) -> [(x, ty, e)]
        | LvTuple xs -> begin
          match e.e_node with
          | Etuple es -> List.map2 (fun (x, ty) e -> (x, ty, e)) xs es
          | _ -> assert false
        end
      in
        (asgn, i, tl)
    end

    | _ -> 
        tacuerror "cannot find a left-value assignment at given position"
  in

  let (tl1, tl2) =
    match olen with
    | None      -> (tl, [])
    | Some olen ->
        if List.length tl < olen then
          tacuerror "expecting at least %d instructions after assignment" olen;
        List.take_n olen tl
  in

  List.iter
    (fun (x, _, _) ->
      if x.pv_kind <> PVloc then
        tacuerror "left-values must be local variables")
    asgn;

  List.iter
    (fun (_, _, e) ->
        if e_fv e <> Mid.empty || e_read env PV.empty e <> PV.empty then
          tacuerror "right-values are not closed expression")
    asgn;

  let wrs = is_write env EcPV.PV.empty tl1 in
  let asg = List.fold_left
              (fun pv (x, ty, _) -> EcPV.PV.add env x ty pv)
              EcPV.PV.empty asgn
  in

  if not (EcPV.PV.indep env wrs asg) then
    tacuerror "cannot cfold non read-only local variables";

  let subst =
    List.fold_left
      (fun subst (x, _ty, e) ->  Mpv.add env x e subst)
      Mpv.empty asgn
  in

  let tl1 = Mpv.issubst env subst tl1 in

  let zpr =
    { zpr with Zpr.z_tail = tl1 @ (i :: tl2) }
  in
    (me, zpr, [])

class rn_hl_cfold side pos len =
object
  inherit xrule "[hl] cfold"

  method side     : bool option = side
  method position : codepos     = pos
  method length   : int option  = len
end

let rn_hl_cfold side pos len =
  RN_xtd (new rn_hl_cfold side pos len :> xrule)

let t_cfold side cpos olen g =
  let tr = fun side -> rn_hl_cfold side cpos olen in
  let cb = fun hyps _ me zpr -> cfold_stmt (LDecl.toenv hyps) me olen zpr in 
    t_code_transform ~bdhoare:true side cpos tr (t_zip cb) g

let process_cfold (side, cpos, olen) g =
  t_cfold side cpos olen g

let process_kill (side, cpos, len) g =
  t_kill side cpos len g

let process_alias (side, cpos, id) g =
  t_alias side cpos id g

let process_set (fresh,side,cpos, id, e) g = 
  let e = EcCoreHiPhl.process_phl_exp side e None g in
  t_set fresh side cpos id e g 
  
