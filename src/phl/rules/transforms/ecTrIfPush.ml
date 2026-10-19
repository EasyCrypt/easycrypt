(* -------------------------------------------------------------------- *)
open EcModules
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* The [if-push] transformation has no parameters: it acts on the first
   instruction of the statement. *)
type EcPlTransform.transform += TrIfPush

(* -------------------------------------------------------------------- *)
(* Push the continuation [c] of the leading conditional into both of its
   branches. *)
let if_push (ctxt : tr_ctxt) (s : stmt) =
  match s.s_node with
  | { i_node = Sif (e, c1, c2) } :: c ->
      let c = stmt c in
      { trr_me  = ctxt.trc_me;
        trr_s   = stmt [i_if (e, s_seq c1 c, s_seq c2 c)];
        trr_obl = []; }

  | _ ->
      raise (InvalidTransform "the first instruction is not a conditional")

let () =
  register (function
    | TrIfPush -> Some if_push
    | _ -> None)
