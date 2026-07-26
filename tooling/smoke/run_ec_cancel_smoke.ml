(** UPSTREAM § 25 / doc/cancellation.md C2 — OCaml-level smoke for the
    SIGINT-driven graceful cancel path.

    Scenarios (each spawns its own [ec llm] subprocess):

      1. [smt-cancel-recover] — long SMT call gets SIGINT'd ~50ms in;
         we observe the "canceled" ERROR reply within
         [cancel_response_budget_s] AND the same session accepts
         further commands afterward (no SIGKILL, session intact).
         If the toy goal happens to close before the cancel window,
         we accept "completed-before-cancel" and log it — same
         posture as [run_smt_scenarios] in the no-prover case.
      2. [smt-recover-after-cancel] — after the cancel, run a fresh
         trivial SMT call; assert it succeeds. Validates Why3
         respawn (lazy: next SMT call, [is_connected ()] check at
         the head of [maybe_start_why3_server_]).
      3. [non-smt-cancel] — SIGINT outside any tactic; assert it is
         absorbed cleanly (flag cleared at next [process_ec_input]),
         a follow-up trivial command succeeds.

    All scenarios distinguish "canceled" from "Session_restarted" /
    "Cancelled (legacy SIGKILL)" — those would indicate a regression
    where the subprocess died instead of replying gracefully. *)

open Ecd_core
open Eio.Std

let binary_path () =
  match Sys.getenv_opt "EC_LLM_BIN" with
  | Some p -> Some p
  | None ->
    let candidate = Filename.concat (Sys.getcwd ())
                      "_build/default/src/ec.exe" in
    if Sys.file_exists candidate then Some candidate else None

(* Deliberately-unsolvable goal: provers run until [pr_timelimit] (3s
   default) then surface a failure. SIGINT during this window must
   interrupt within [cancel_response_budget_s] — if instead the
   cancel mechanism is broken, the smt call runs to its 3s timeout
   and the smoke fails the budget assertion.
   Using a false goal (rather than a hard-but-true one) is a load-
   bearing choice: it guarantees the SMT call doesn't close before
   the cancel window fires regardless of the local prover stack. *)
let unsolvable_smt_sentences =
  [ "lemma s_unsolvable : forall (n : int), n = n + 1."
  ; "proof."
  ; "move => n."
  ; "smt()."
  ; "qed."
  ]

(* A goal trivial enough to validate the post-cancel session is healthy
   AND that Why3 respawn worked (since this also fires SMT). *)
let trivial_smt_sentences =
  [ "lemma s_trivial (x y : int) : x + y = y + x."
  ; "proof."
  ; "smt()."
  ; "qed."
  ]

(* Pre-cancel preamble — same as run_smt_scenarios. *)
let preamble =
  [ "require import AllCore."
  ; "require import Int."
  ]

let now_s env = Eio.Time.now (Eio.Stdenv.clock env)

let cancel_response_budget_s = 2.0
(** Wall-clock budget for the cancel-induced ERROR reply. The
    EcCancel.check () polling target is < 100ms for pure-OCaml
    aborts and < 500ms for SMT-bound aborts. We give 2s headroom
    here for CI variance. *)

let cancel_window_s = 0.5
(** Time after kicking off the SMT call before we deliver SIGINT.
    Wider than [run_smt_scenarios.scenario_cancel]'s 50ms because we
    need to be reliably inside the prover-blocking call: the first
    SMT call also pays Why3-server startup (~100-200ms) before the
    blocking-read window opens. *)

(* -------------------------------------------------------------------- *)

let start_session ~bin env sw label =
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr ~executable:bin
    ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
  let s = Ec_llm_session.start ~sw ~label in
  let feed corr src =
    match
      Ec_llm_session.exec s
        ~corr:(Correlation.of_client corr)
        ~sentence_class:`Executable ~source:src
    with
    | Ok _  -> ()
    | Error e ->
      Printf.eprintf "%s: preamble failed at %s: %s\n%!"
        label corr (Error.to_string e);
      exit 1
  in
  List.iteri (fun i src -> feed (Printf.sprintf "pre-%d" i) src) preamble;
  s

(* Feed an ordered list of sentences; return the last result.
   Stops on the first Error. *)
let exec_sentences s ~corr_prefix sentences =
  let rec go i = function
    | [] -> Ok ()
    | src :: rest ->
      let corr =
        Correlation.of_client (Printf.sprintf "%s-%d" corr_prefix i)
      in
      match
        Ec_llm_session.exec s ~corr ~sentence_class:`Executable ~source:src
      with
      | Ok _ -> go (i + 1) rest
      | Error e -> Error e
  in
  go 1 sentences

(* Send SIGINT directly to the EC subprocess pid. We intentionally do
   NOT call [Ec_llm_session.cancel], which SIGKILLs and marks the
   session as cancelled — this smoke is precisely about the gentler
   SIGINT path that keeps the session alive. *)
let send_sigint s =
  let pid = Ec_llm_session.pid s in
  try Unix.kill pid Sys.sigint with Unix.Unix_error _ -> ()

(* -------------------------------------------------------------------- *)
(* Scenario 1 + 2 fused: SMT cancel, then a trivial SMT call to verify
   the session survived AND Why3 respawned. *)

type cancel_outcome =
  | Canceled            (** ERROR reply with "canceled" body *)
  | Completed_before    (** SMT closed the goal before SIGINT fired *)
  | Session_killed      (** Subprocess died — regression *)
  | Other_error of string

let classify_cancel_result = function
  | Ok _ -> Completed_before
  | Error (Error.Session_restarted { reason }) ->
    Session_killed (* shouldn't happen with C2 *)
    |> fun k -> ignore reason; k
  | Error (Error.Cancelled { reason }) ->
    Session_killed
    |> fun k -> ignore reason; k
  | Error (Error.Internal { detail }) when
      String.length detail >= 8
      && String.sub (String.lowercase_ascii detail) 0 8 = "canceled" ->
    Canceled
  | Error e ->
    let s = Error.to_string e in
    let s_low = String.lowercase_ascii s in
    let contains sub =
      let n = String.length sub in
      let m = String.length s_low in
      let rec loop i =
        if i + n > m then false
        else if String.sub s_low i n = sub then true
        else loop (i + 1)
      in loop 0
    in
    if contains "canceled" then Canceled
    else Other_error s

let scenario_smt_cancel_then_recover ~bin env =
  Switch.run @@ fun sw ->
  let s = start_session ~bin env sw "ec-cancel-smt" in
  let clock = Eio.Stdenv.clock env in
  let t0 = now_s env in
  let result = ref (Other_error "unset") in
  let exec_done = ref false in
  Fiber.both
    (fun () ->
       let r =
         exec_sentences s ~corr_prefix:"unsolvable-smt"
           unsolvable_smt_sentences
       in
       result := classify_cancel_result r;
       exec_done := true)
    (fun () ->
       Eio.Time.sleep clock cancel_window_s;
       send_sigint s);
  let cancel_dt = now_s env -. t0 in
  let cancel_kind, cancel_ok, cancel_detail =
    match !result with
    | Canceled ->
      ("canceled", true,
       Printf.sprintf "graceful SIGINT reply within %.3fs" cancel_dt)
    | Completed_before ->
      ("completed-before-cancel", true,
       "smt finished before cancel window — mechanism not exercised")
    | Session_killed ->
      ("session-killed", false,
       "REGRESSION: subprocess died instead of replying canceled")
    | Other_error msg ->
      ("error", false, msg)
  in
  let kind1_ok =
    cancel_ok && cancel_dt < cancel_response_budget_s
  in
  let kind1_detail =
    if cancel_dt >= cancel_response_budget_s then
      Printf.sprintf "%s (BUDGET EXCEEDED: %.3fs >= %.3fs)"
        cancel_detail cancel_dt cancel_response_budget_s
    else cancel_detail
  in
  (* Phase 2 — recover. The unsolvable lemma's proof is still open
     (smt() failed mid-proof); abort it first, then run a fresh
     trivial SMT call to confirm the session is alive AND Why3
     respawned cleanly. *)
  let phase2_kind, phase2_ok, phase2_detail =
    if not (Ec_llm_session.is_alive s) then
      ("recover", false, "session not alive after cancel")
    else begin
      let t2 = now_s env in
      let r_abort =
        exec_sentences s ~corr_prefix:"recover-abort" [ "abort." ]
      in
      let r =
        match r_abort with
        | Error e ->
          Error e
        | Ok () ->
          exec_sentences s ~corr_prefix:"recover-smt" trivial_smt_sentences
      in
      let dt2 = now_s env -. t2 in
      match r with
      | Ok _ ->
        ("recover", true,
         Printf.sprintf "abort + trivial smt closed in %.3fs (Why3 respawn worked)"
           dt2)
      | Error e ->
        ("recover", false,
         Printf.sprintf "post-cancel recovery failed: %s" (Error.to_string e))
    end
  in
  Ec_llm_session.close s;
  let total_dt = now_s env -. t0 in
  ( Printf.sprintf "smt-cancel-recover (%s/%s)" cancel_kind phase2_kind,
    kind1_ok && phase2_ok,
    total_dt,
    Printf.sprintf "cancel: %s | recover: %s" kind1_detail phase2_detail )

(* -------------------------------------------------------------------- *)
(* Scenario 3 — SIGINT outside any tactic. Should be absorbed cleanly. *)

let scenario_idle_cancel ~bin env =
  Switch.run @@ fun sw ->
  let s = start_session ~bin env sw "ec-cancel-idle" in
  let clock = Eio.Stdenv.clock env in
  let t0 = now_s env in
  send_sigint s;
  (* Brief settle period so the signal is delivered while the
     subprocess is in [input_line stdin]. *)
  Eio.Time.sleep clock 0.05;
  let r =
    exec_sentences s ~corr_prefix:"idle-recover"
      [ "lemma s_idle (x : int) : x = x." ; "proof." ; "trivial." ; "qed." ]
  in
  let dt = now_s env -. t0 in
  Ec_llm_session.close s;
  match r with
  | Ok _ ->
    ("idle-cancel", true, dt,
     "SIGINT-while-idle absorbed; follow-up command succeeded")
  | Error e ->
    ("idle-cancel", false, dt,
     Printf.sprintf "post-idle-cancel command failed: %s"
       (Error.to_string e))

(* -------------------------------------------------------------------- *)

let () =
  match binary_path () with
  | None ->
    Printf.printf "skip: no ec llm binary found (set EC_LLM_BIN)\n%!";
    exit 0
  | Some bin ->
    Eio_main.run @@ fun env ->
    Printf.printf "ec-cancel-smoke: bin=%s\n%!" bin;
    let safe label f =
      try f ()
      with e ->
        ( label, false, 0.0,
          Printf.sprintf "uncaught exception: %s" (Printexc.to_string e) )
    in
    let results =
      [ safe "smt-cancel-recover"
          (fun () -> scenario_smt_cancel_then_recover ~bin env)
      ; safe "idle-cancel"
          (fun () -> scenario_idle_cancel             ~bin env) ]
    in
    let all_ok = List.for_all (fun (_, ok, _, _) -> ok) results in
    Printf.printf "scenarios:\n%!";
    let json_list =
      List.map (fun (name, ok, dt, detail) ->
        Printf.printf "  %-40s %-6s  %.3fs%s\n%!"
          name (if ok then "ok" else "FAIL") dt
          (if detail = "" then "" else "  -- " ^ detail);
        `Assoc [
          "name",       `String name;
          "ok",         `Bool ok;
          "duration_s", `Float dt;
          "detail",     `String detail;
        ])
        results
    in
    print_endline
      (Yojson.Safe.to_string (`Assoc [ "ec_cancel_scenarios", `List json_list ]));
    if all_ok then Printf.printf "all scenarios passed\n%!"
    else exit 1
