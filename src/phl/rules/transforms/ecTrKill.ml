(* -------------------------------------------------------------------- *)
open EcUtils
open EcModules
open EcPV
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the [kill] transformation, resolved: the position is a
   normalized (possibly nested) code position. *)
type tr_kill = {
  trk_at  : EcMatching.Position.nm_codepos;
  trk_len : int option;
}

type EcPlTransform.transform += TrKill of tr_kill

(* -------------------------------------------------------------------- *)
let invalid fmt = Format.kasprintf (fun msg -> raise (InvalidTransform msg)) fmt

(* -------------------------------------------------------------------- *)
(* Remove the killed instructions [ks], provided that what they write is
   read neither by the code that may run after them nor by the
   postcondition; [ks] must be lossless. *)
let kill (p : tr_kill) (ctxt : tr_ctxt) (s : stmt) =
  let env = ctxt.trc_env in

  let zpr =
    try  Zpr.zipper_of_nm_cpos p.trk_at s
    with EcMatching.Position.InvalidCPos -> invalid "invalid code position" in

  let (ks, tl) =
    match p.trk_len with
    | None -> (zpr.Zpr.z_tail, [])
    | Some len ->
        if List.length zpr.Zpr.z_tail < len then
          invalid "cannot find %d consecutive instructions at given position" len;
        List.takedrop len zpr.Zpr.z_tail
  in

  let ks_wr = is_write env ks in

  let pp_of_name =
    let ppe = EcPrinting.PPEnv.ofenv env in
    fun fmt x ->
      match x with
      | `Global p -> EcPrinting.pp_topmod ppe fmt p
      | `PV     p -> EcPrinting.pp_pv     ppe fmt p
  in

  (* [ks] is replaced by [skip]. This is sound if [ks] is lossless
     (obligation) and if the variables it writes ([ks_wr]) are read
     neither by the postcondition nor by any code that may run after
     [ks]: then both programs end in states that agree outside of
     [ks_wr]. The code that may run after [ks] is, for each enclosing
     block, the code that follows the block's cursor, and, for each
     enclosing while loop, the loop guard and the whole loop body (with
     [ks] removed): the next iterations run them again, including the
     part of the body before [ks]. This is what
     [EcPV.zpr_pv `Read `After] computes. *)
  let af_rd =
    zpr_pv `Read `After env PV.empty ((zpr.Zpr.z_head, tl), zpr.Zpr.z_path) in

  begin
    match PV.pick (PV.interdep env ks_wr af_rd) with
    | None   -> ()
    | Some x ->
        invalid
          "code writes variables (%a) used by the code that may run after it"
          pp_of_name x
  end;

  begin
    match PV.pick (PV.interdep env ks_wr (Lazy.force ctxt.trc_post)) with
    | None   -> ()
    | Some x ->
        invalid
          "code writes variables (%a) used by the post-condition"
          pp_of_name x
  end;

  { trr_me  = ctxt.trc_me;
    trr_s   = Zpr.zip { zpr with Zpr.z_tail = tl; };
    trr_obl = [OLossless (stmt ks)]; }

let () =
  register (function
    | TrKill p -> Some (kill p)
    | _ -> None)
