(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv

(* -------------------------------------------------------------------- *)
(* Program transformations: an open catalogue of pure statement-level
   transformations, each registered with the function computing it, and a
   closed set of abstract obligations that each logic's transformation
   rule states in its own terms. *)
type transform = ..

type obligation =
  | OPrefixPost of prefix_post

and prefix_post = {
  opp_prefix : stmt;
  opp_cond   : ss_inv;
}

type tr_ctxt = {
  trc_env  : env;
  trc_me   : memenv;
  trc_post : EcPV.PV.t Lazy.t;
}

type tr_result = {
  trr_me  : memenv;
  trr_s   : stmt;
  trr_obl : obligation list;
}

exception InvalidTransform of string

(* -------------------------------------------------------------------- *)
(* The registry: partial handlers over the open [transform] type, as for
   the rule checkers ([EcCoreGoal.register_rule_checker]). *)
let entries : (transform -> (tr_ctxt -> stmt -> tr_result) option) list ref =
  ref []

let register f =
  entries := f :: !entries

let apply (ctxt : tr_ctxt) (t : transform) (s : stmt) =
  match List.find_map (fun f -> f t) !entries with
  | None     -> raise (InvalidTransform "unknown program transformation")
  | Some run -> run ctxt s
