(* See proof_speculation.mli for the contract. *)

(* --- Tactic catalog ------------------------------------------------- *)

type tactic =
  | Apply_hyp
  | Move_intros
  | Rewrite
  | Apply_lemma
  | Rewrite_lemma
  | Suggest_closers

let tactic_label = function
  | Apply_hyp       -> "apply <hypothesis>"
  | Move_intros     -> "move => <intro pattern>"
  | Rewrite         -> "rewrite <args…>"
  | Apply_lemma     -> "apply <lemma by search>"
  | Rewrite_lemma   -> "rewrite <lemma by search>"
  | Suggest_closers -> "suggest closers (trivial / smt / by done / …)"

let tactic_catalog =
  [ Apply_hyp; Move_intros; Rewrite;
    Apply_lemma; Rewrite_lemma;
    Suggest_closers ]

(* --- Pure source builders ------------------------------------------ *)

let verb_keyword = function `Apply -> "apply" | `Rewrite -> "rewrite"

let apply_hyp_source (h : Goal_view.hypothesis) = "apply " ^ h.name ^ "."

let move_cumulative_source tokens =
  "move => " ^ String.concat " " tokens ^ "."

let rewrite_cumulative_source tokens =
  "rewrite " ^ String.concat " " tokens ^ "."

(* Prefer [qname] since it always resolves regardless of whether the
   hit's theory is currently imported. For unmarked hits the parser
   sets qname = short_name, so this is equivalent in that case. *)
let lemma_picker_source ~verb (h : Search_result.hit) =
  Printf.sprintf "%s %s." (verb_keyword verb) h.qname

(* --- Cumulative-handle session ------------------------------------- *)

type session = {
  underlying : Ec_llm_session.t;
  handle : Speculation.handle;
}

type trial_outcome =
  | Trial_ok of { goals : Goal_view.t option; body : string }
  | Trial_err of string

let begin_session underlying =
  { underlying; handle = Speculation.capture underlying }

let captured_uuid s = Speculation.captured_uuid s.handle

let fetch_goals session =
  match Ec_llm_session.goals ~structured:true session with
  | Error _ -> None
  | Ok s ->
    (match Goal_view.of_string s with
     | Error _ -> None
     | Ok gv -> Some gv)

let try_ s ~source =
  match Speculation.rollback s.underlying s.handle with
  | Error e -> Trial_err (Error.to_string e)
  | Ok () ->
    let corr = Correlation.of_client "proof-spec-try" in
    (match
       Ec_llm_session.exec s.underlying ~corr
         ~sentence_class:`Executable ~source
     with
     | Error e -> Trial_err (Error.to_string e)
     | Ok ok ->
       let goals = fetch_goals s.underlying in
       Trial_ok { goals; body = ok.output })

let commit _ = Ok ()

let discard s = Speculation.rollback s.underlying s.handle

(* --- One-shot helpers ---------------------------------------------- *)

let try_tactic underlying ~source =
  let s = begin_session underlying in
  let outcome = try_ s ~source in
  let _ = discard s in
  outcome

(* --- Read-only directive query ------------------------------------- *)

type query_result = {
  body : string;
  notices : string list;
}

let query session ~source =
  let corr = Correlation.of_client "proof-spec-query" in
  match
    Ec_llm_session.exec session ~corr ~sentence_class:`Directive ~source
  with
  | Error e -> Error e
  | Ok ok -> Ok { body = ok.output; notices = ok.notices }

(* --- Lemma preview ------------------------------------------------- *)

type lemma_preview =
  | Preview_ok of { goals_after : Goal_view.t option; body : string }
  | Preview_err of string

let preview_lemma underlying ~verb ?prev hit =
  let prev_rolled =
    match prev with
    | None -> Ok ()
    | Some s -> Speculation.rollback s.underlying s.handle
  in
  match prev_rolled with
  | Error e -> Error e
  | Ok () ->
    let session = begin_session underlying in
    let source = lemma_picker_source ~verb hit in
    let corr = Correlation.of_client "proof-spec-preview" in
    let outcome =
      match
        Ec_llm_session.exec underlying ~corr
          ~sentence_class:`Executable ~source
      with
      | Error e -> Preview_err (Error.to_string e)
      | Ok ok ->
        let goals_after = fetch_goals underlying in
        Preview_ok { goals_after; body = ok.output }
    in
    Ok (outcome, session)

(* --- Closer suggester ---------------------------------------------- *)

type suggest_outcome =
  | Suggest_closes
  | Suggest_open of int
  | Suggest_err of string

type suggest_row = {
  src : string;
  label : string;
  outcome : suggest_outcome;
}

let sort_suggest_rows rows =
  let bucket = function
    | { outcome = Suggest_closes; _ } -> 0
    | { outcome = Suggest_open _; _ } -> 1
    | { outcome = Suggest_err _;   _ } -> 2
  in
  List.stable_sort (fun a b -> compare (bucket a) (bucket b)) rows

(* Heuristic ascending runtime order; sweep stops at the first closer. *)
let default_closer_candidates = [
  "reflexivity", "reflexivity.";
  "trivial",     "trivial.";
  "assumption",  "assumption.";
  "by done",     "by done.";
  "by auto",     "by auto.";
  "smt()",       "smt().";
]

(* Read the current subgoal count, or [None] if goals can't be
   fetched / parsed. Used by [suggest_closers] to detect whether the
   focused subgoal closed (count went down) vs. only opened new
   branches (count went up) vs. had no effect (count unchanged). *)
let goal_count_now session =
  match Ec_llm_session.goals ~structured:true session with
  | Error _ -> None
  | Ok s ->
    match Goal_view.of_string s with
    | Error _ -> None
    | Ok gv -> Some gv.subgoal_count

let suggest_closers
    underlying
    ?(candidates = default_closer_candidates)
    ?before_candidate
    ?on_progress
    ()
  =
  let total = List.length candidates in
  let invoke_before label remaining =
    match before_candidate with
    | None -> ()
    | Some f -> f ~label ~remaining
  in
  let invoke_progress row remaining =
    match on_progress with
    | None -> ()
    | Some f -> f row ~remaining
  in
  (* Snapshot the count BEFORE the sweep so each candidate's outcome
     compares against the focused-pre-sweep state. The picker is
     called at one user position so the pre-sweep count is stable
     across candidates (we rollback after each). *)
  let count_before = goal_count_now underlying in
  let classify count_after =
    match count_before, count_after with
    | _, Some 0 ->
      (* Whole proof discharged. *)
      Suggest_closes
    | Some before, Some after when after < before ->
      (* Focused subgoal closed; other unrelated subgoals from
         earlier branches may remain. Still a closer for the
         focused goal. *)
      Suggest_closes
    | _, Some after ->
      (* Focused not closed; report total post-tactic count.
         (Caller's UI shows "→ N subgoal(s) remain" — accurate
         even when [after >= before].) *)
      Suggest_open after
    | _, None ->
      Suggest_err "(goals unavailable after try)"
  in
  (* Each candidate: before-callback, capture, exec, classify,
     rollback, on_progress, decide whether to early-stop or continue.
     Both callbacks fire at rollback-stable boundaries (session at
     base uuid). *)
  let rec loop acc remaining = function
    | [] -> Ok (List.rev acc)
    | (label, src) :: rest ->
      (* Pre-candidate hook: session is at base (rollback-stable). *)
      invoke_before label remaining;
      let handle = Speculation.capture underlying in
      let corr = Correlation.of_client "proof-spec-suggest" in
      let outcome =
        match
          Ec_llm_session.exec underlying ~corr
            ~sentence_class:`Executable ~source:src
        with
        | Error e -> Suggest_err (Error.to_string e)
        | Ok _ -> classify (goal_count_now underlying)
      in
      (match Speculation.rollback underlying handle with
       | Error e -> Error e
       | Ok () ->
         let row = { src; label; outcome } in
         let remaining' = remaining - 1 in
         (* Decision (1): on_progress AFTER rollback. *)
         invoke_progress row remaining';
         match outcome with
         | Suggest_closes ->
           (* Found a closer — stop the sweep, skip remaining
              candidates. *)
           Ok (List.rev (row :: acc))
         | Suggest_open _ | Suggest_err _ ->
           loop (row :: acc) remaining' rest)
  in
  loop [] total candidates
