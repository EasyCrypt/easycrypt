(* -------------------------------------------------------------------- *)
open EcFol
open EcEnv
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* Shared scaffolding for proof-node checkers (see [EcCoreGoal.rule]).

   A checker rebuilds the subgoals a rule should have produced and compares
   them, up to conversion, against what the node recorded. Only the two
   per-rule pieces differ — how to read the judgement out of the goal, and how
   to recompute its subgoals from the recorded parameters — everything else
   (deriving the context, the arity check, the per-subgoal comparison and the
   error reporting) lives here. *)

(* -------------------------------------------------------------------- *)
(* Compare the [expected] subgoal conclusions against the recorded [subs], up
   to conversion under each subgoal's own hypotheses. *)
let recheck_forms (name : string) (expected : form list) (subs : pregoal list) =
  let nexp = List.length expected and ngot = List.length subs in
  if nexp <> ngot then
    raise (RecheckFailure
             (Printf.sprintf "%s: expected %d subgoal(s), got %d" name nexp ngot));
  List.iteri
    (fun k (e, (g : pregoal)) ->
      if not (EcReduction.is_conv g.g_hyps e g.g_concl) then
        raise (RecheckFailure (Printf.sprintf "%s: subgoal %d mismatch" name (k+1))))
    (List.combine expected subs)

(* -------------------------------------------------------------------- *)
(* Build a [rule_checker] from a judgement reader [destr] and a subgoal builder
   [build]. [build] is handed the goal's hypotheses (the authoritative context;
   its environment is [LDecl.toenv] of them) and recomputes the subgoals — the
   recorded parameters are captured in [build] at registration time. Any
   exception raised while reading or rebuilding is surfaced as a
   [RecheckFailure], so a checker never leaks a raw user-level exception. *)
let checker_of
    (name  : string)
    (destr : proofenv -> form -> 'a)
    (build : LDecl.hyps -> 'a -> form list)
  : rule_checker =
  fun pe goal subs ->
    try recheck_forms name (build goal.g_hyps (destr pe goal.g_concl)) subs with
    | RecheckFailure _ as e -> raise e
    | e -> raise (RecheckFailure (Printf.sprintf "%s: %s" name (Printexc.to_string e)))
