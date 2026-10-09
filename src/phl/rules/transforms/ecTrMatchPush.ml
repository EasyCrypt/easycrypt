(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcModules
open EcFol
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* The [match-push] transformation has no parameters: it acts on the first
   instruction of the statement. *)
type EcPlTransform.transform += TrMatchPush

(* -------------------------------------------------------------------- *)
(* Push the continuation [c] of the leading [match] into each of its
   branches. The pattern variables of a branch are local identifiers bound
   in its body; [c] lies outside of their scope, so a branch whose pattern
   variables occur free in [c] is first renamed apart (fresh identifiers),
   so that [c] is not captured. *)
let match_push (ctxt : tr_ctxt) (s : stmt) =
  match s.s_node with
  | { i_node = Smatch (e, bs) } :: c ->
      let c = stmt c in
      let fv = s_fv c in

      let push ((xs, b) : (EcIdent.t * ty) list * stmt) =
        if List.exists (fun (x, _) -> EcIdent.Mid.mem x fv) xs then
          let xs' = List.map (fst_map EcIdent.fresh) xs in
          let sb  =
            List.fold_left2
              (fun sb (x, _) (x', ty) -> bind_elocal sb x (e_local x' ty))
              Fsubst.f_subst_id xs xs' in
          (xs', s_seq (s_subst sb b) c)
        else (xs, s_seq b c) in

      { trr_me  = ctxt.trc_me;
        trr_s   = stmt [i_match (e, List.map push bs)];
        trr_obl = []; }

  | _ ->
      raise (InvalidTransform "the first instruction is not a match")

let () =
  register (function
    | TrMatchPush -> Some match_push
    | _ -> None)
