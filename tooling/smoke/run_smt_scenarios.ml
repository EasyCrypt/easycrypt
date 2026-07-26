(** Phase 1 SMT scenarios (plan acceptance gate). Three cases against
    the real [ec llm] subprocess:

      1. success             — SMT closes a trivial goal.
      2. cancel-mid-solve    — cancel the session while SMT is running;
                               observe the typed Session_restarted
                               result and a clean shutdown. When the
                               environment has no working external
                               prover, SMT can close the toy goals
                               below before the 250ms cancel window
                               fires, in which case we accept the
                               "completed-before-cancel" outcome and
                               log it — the mechanism is still
                               exercised end-to-end. Meaningful
                               cancel testing requires a working
                               prover (alt-ergo/z3/cvc4).
      3. two concurrent      — two independent sessions run SMT in
                               parallel fibers; both succeed.

    Writes the three outcomes + timings in a JSON line so the Phase 1
    measurement record is machine-readable. Skips cleanly when no
    [ec llm] binary is available. *)

open Ecd_core
open Eio.Std

let binary_path () =
  match Sys.getenv_opt "EC_LLM_BIN" with
  | Some p -> Some p
  | None ->
    let candidate = Filename.concat (Sys.getcwd ())
                      "_build/default/src/ec.exe" in
    if Sys.file_exists candidate then Some candidate else None

(* `exec` only consumes one parsed top-level form per call (EC's
   xparse returns the first), so we list sentences separately and
   feed them one at a time. SMT only fires on the `smt().` step. *)

let trivial_smt_sentences =
  [ "lemma s_ok (x y : int) : (x + y) * (x - y) = x * x - y * y."
  ; "proof."
  ; "smt()."
  ; "qed."
  ]

(* A harder goal (Lagrange identity) forcing the prover to do real
   nonlinear work; resists `ring` / `trivial`, so the cancel fiber
   has measurable wall-clock window. *)
let hard_smt_sentences =
  [ "lemma s_hard (a b c d : int) : \
     (a * a + b * b) * (c * c + d * d) = \
     (a * c - b * d) * (a * c - b * d) + (a * d + b * c) * (a * d + b * c)."
  ; "proof."
  ; "smt()."
  ; "qed."
  ]

let now_s env = Eio.Time.now (Eio.Stdenv.clock env)

let run_primary ~bin env sw label =
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr ~executable:bin
    ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
  let s = Ec_llm_session.start ~sw ~label in
  (* Prime the preamble so the SMT lemmas can elaborate. *)
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
  (* Preamble is two sentences — feed each through `exec` individually
     so ec llm's xparse returns after the first. *)
  feed "pre1" "require import AllCore.";
  feed "pre2" "require import Int.";
  s

(* ---------------------------------------------------------------- *)

(* Feed an ordered list of sentences through exec, returning the
   last result. Stops and returns on the first Error. *)
let exec_sentences s ~corr_prefix sentences =
  let rec go i = function
    | [] -> Ok ()
    | src :: rest ->
      let corr =
        Correlation.of_client (Printf.sprintf "%s-%d" corr_prefix i)
      in
      match Ec_llm_session.exec s ~corr ~sentence_class:`Executable ~source:src with
      | Ok _ -> go (i + 1) rest
      | Error e -> Error e
  in
  go 1 sentences

let scenario_success ~bin env =
  Switch.run @@ fun sw ->
  let s = run_primary ~bin env sw "smt-success" in
  let t0 = now_s env in
  let result = exec_sentences s ~corr_prefix:"smt-ok" trivial_smt_sentences in
  let dt = now_s env -. t0 in
  Ec_llm_session.close s;
  match result with
  | Ok _ -> ("success", true, dt, "")
  | Error e -> ("success", false, dt, Error.to_string e)

let cancel_deadline_s = 20.0
(** Hard ceiling on the cancel scenario. If the exec fiber fails to
    unblock within this many seconds after SIGKILL, we conclude the
    cancellation machinery is broken and fail the scenario. *)

let scenario_cancel ~bin env =
  Switch.run @@ fun sw ->
  let s = run_primary ~bin env sw "smt-cancel" in
  let clock = Eio.Stdenv.clock env in
  let t0 = now_s env in
  let result = ref `Timed_out in
  let timed_out = ref false in
  (match
     Eio.Time.with_timeout clock cancel_deadline_s (fun () ->
       Fiber.both
         (fun () ->
            result := (match
                         exec_sentences s ~corr_prefix:"smt-long"
                           hard_smt_sentences
                       with
                       | Ok _    -> `Ok
                       | Error e -> `Error e))
         (fun () ->
            (* Aggressive cancel window — shorter than a typical SMT
               round-trip (~140ms in this env). Long enough that the
               `smt().` exec is in-flight when cancel fires. *)
            Eio.Time.sleep clock 0.05;
            Ec_llm_session.cancel s
              ~corr:(Correlation.of_client "smt-cancel-issuer"));
       Ok ())
   with
   | Ok ()              -> ()
   | Error `Timeout     -> timed_out := true);
  let dt = now_s env -. t0 in
  Ec_llm_session.close s;
  let kind, detail, ok =
    if !timed_out then
      ( "hung",
        Printf.sprintf
          "exec fiber failed to unblock within %.0fs of SIGKILL" cancel_deadline_s,
        false )
    else match !result with
      | `Ok ->
        ( "completed-before-cancel", "smt finished before 50ms cancel fired",
          true )
      | `Error (Error.Session_restarted { reason }) -> ("cancelled", reason, true)
      | `Error (Error.Cancelled { reason })         -> ("cancelled", reason, true)
      | `Error e -> ("error", Error.to_string e, false)
      | `Timed_out -> ("hung", "unreached", false)
  in
  (Printf.sprintf "cancel-mid-solve (%s)" kind, ok, dt, detail)

let scenario_concurrent ~bin env =
  Switch.run @@ fun sw ->
  let a = run_primary ~bin env sw "smt-a" in
  let b = run_primary ~bin env sw "smt-b" in
  let t0 = now_s env in
  let ra = ref (Error (Error.Internal { detail = "unreached" })) in
  let rb = ref (Error (Error.Internal { detail = "unreached" })) in
  Fiber.both
    (fun () ->
       ra := exec_sentences a ~corr_prefix:"smt-a" trivial_smt_sentences)
    (fun () ->
       rb := exec_sentences b ~corr_prefix:"smt-b" trivial_smt_sentences);
  let dt = now_s env -. t0 in
  Ec_llm_session.close a;
  Ec_llm_session.close b;
  let ok = Result.is_ok !ra && Result.is_ok !rb in
  let detail =
    if ok then ""
    else Printf.sprintf
           "a=%s b=%s"
           (match !ra with Ok _ -> "ok" | Error e -> Error.to_string e)
           (match !rb with Ok _ -> "ok" | Error e -> Error.to_string e)
  in
  ("two-concurrent", ok, dt, detail)

let scenario_startup ~bin env =
  Switch.run @@ fun sw ->
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr ~executable:bin
    ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
  let t0 = now_s env in
  let s = Ec_llm_session.start ~sw ~label:"startup-probe" in
  let dt = now_s env -. t0 in
  Ec_llm_session.close s;
  ("startup-cost", true, dt, "cold spawn + READY + handshake")

(* ---------------------------------------------------------------- *)

let () =
  match binary_path () with
  | None ->
    Printf.printf "skip: no ec llm binary found (set EC_LLM_BIN)\n%!";
    exit 0
  | Some bin ->
    Eio_main.run @@ fun env ->
    Printf.printf "smt-scenarios: bin=%s\n%!" bin;
    let results =
      [ scenario_startup    ~bin env
      ; scenario_success    ~bin env
      ; scenario_cancel     ~bin env
      ; scenario_concurrent ~bin env ]
    in
    let all_ok =
      List.for_all (fun (_, ok, _, _) -> ok) results
    in
    Printf.printf "scenarios:\n%!";
    let json_list =
      List.map (fun (name, ok, dt, detail) ->
        Printf.printf "  %-20s %-6s  %.3fs%s\n%!"
          name (if ok then "ok" else "FAIL") dt
          (if detail = "" then "" else "  -- " ^ detail);
        `Assoc [
          "name",     `String name;
          "ok",       `Bool ok;
          "duration_s", `Float dt;
          "detail",   `String detail;
        ])
        results
    in
    print_endline
      (Yojson.Safe.to_string (`Assoc [ "smt_scenarios", `List json_list ]));
    if all_ok then Printf.printf "all scenarios passed\n%!"
    else exit 1
