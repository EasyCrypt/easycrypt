(** Stage 2 substrate smoke. Exercises Log, Request_registry,
    Debouncer, Configuration. (Crash_handler tested separately — it
    requires fork+signal which doesn't fit a normal smoke.) *)

open Ecd_core

let pass = ref 0
let fail = ref 0
let check label cond detail =
  if cond then begin incr pass; Printf.printf "  ok  %s\n%!" label end
  else begin incr fail; Printf.printf "  FAIL %s — %s\n%!" label detail end

(* --- Log -------------------------------------------------------- *)

let test_log () =
  Printf.printf "\n== Log ==\n%!";
  let buf = Buffer.create 256 in
  let logger = Log.to_buffer ~level:`Debug buf in
  Log.configure logger;
  Log.info "hello %s" "world";
  Log.warn ?corr:None "oops";
  Log.err ~corr:(Correlation.of_client "req-42") "error context";
  Log.debug "verbose";
  let lines =
    String.split_on_char '\n' (Buffer.contents buf)
    |> List.filter (fun s -> s <> "")
  in
  check "Log emitted 4 lines" (List.length lines = 4)
    (Printf.sprintf "got %d" (List.length lines));
  let parse_or_fail s =
    try Some (Yojson.Safe.from_string s) with _ -> None
  in
  let all_parse =
    List.for_all (fun l -> parse_or_fail l <> None) lines
  in
  check "Log every line is valid JSON" all_parse
    "at least one line failed to parse";
  let has_field expected fld =
    List.exists (fun l ->
      match parse_or_fail l with
      | None -> false
      | Some j ->
        (try Yojson.Safe.Util.member fld j |> Yojson.Safe.Util.to_string = expected
         with _ -> false))
      lines
  in
  check "Log includes msg=hello world" (has_field "hello world" "msg") "";
  check "Log includes msg=oops" (has_field "oops" "msg") "";
  check "Log includes msg=error context" (has_field "error context" "msg") "";
  check "Log carries level=info" (has_field "info" "level") "";
  check "Log carries level=warn" (has_field "warn" "level") "";
  check "Log carries level=error" (has_field "error" "level") "";
  check "Log carries correlation"
    (List.exists (fun l ->
       match parse_or_fail l with
       | None -> false
       | Some j ->
         (try
           let s = Yojson.Safe.Util.member "corr" j |> Yojson.Safe.Util.to_string in
           (* Correlation.of_client wraps with "c:" prefix *)
           s = "c:req-42"
          with _ -> false))
       lines)
    "no line carried the correlation";
  (* Level filter check *)
  let buf2 = Buffer.create 256 in
  let logger2 = Log.to_buffer ~level:`Warn buf2 in
  Log.configure logger2;
  Log.debug "should not appear";
  Log.info "should not appear";
  Log.warn "appears";
  Log.err "appears";
  let lines2 =
    String.split_on_char '\n' (Buffer.contents buf2)
    |> List.filter (fun s -> s <> "")
  in
  check "Log level filter drops debug+info"
    (List.length lines2 = 2)
    (Printf.sprintf "got %d" (List.length lines2))

(* --- Configuration --------------------------------------------- *)

let test_configuration () =
  Printf.printf "\n== Configuration ==\n%!";
  let cfg = Configuration.create () in
  check "default fileMode = preservation"
    (Configuration.file_mode cfg = `Preservation) "";
  check "default cachePolicy = lax"
    (Configuration.cache_policy cfg = `Lax) "";
  check "default goalsCacheBudgetMB = 64"
    (Configuration.goals_cache_budget_mb cfg = 64) "";
  check "default recoveryStrategy = halt"
    (Configuration.recovery_strategy cfg = `Halt) "";
  check "default autoReconcile = true"
    (Configuration.auto_reconcile cfg = true) "";
  check "default debounceMs = 200"
    (Configuration.debounce_ms cfg = 200) "";
  check "default maxExecMsPerSentence = None"
    (Configuration.max_exec_ms_per_sentence cfg = None) "";
  check "default speculation = true"
    (Configuration.speculation_enabled cfg = true) "";
  check "default bulletSemantics = lenient"
    (Configuration.bullet_semantics cfg = `Lenient) "";
  Configuration.set cfg "proof.cachePolicy" (`String "strict");
  Configuration.set cfg "proof.debounceMs" (`Int 500);
  Configuration.set cfg "proof.maxExecMsPerSentence" (`Int 30000);
  check "set: cachePolicy = strict"
    (Configuration.cache_policy cfg = `Strict) "";
  check "set: debounceMs = 500"
    (Configuration.debounce_ms cfg = 500) "";
  check "set: maxExecMsPerSentence = Some 30000"
    (Configuration.max_exec_ms_per_sentence cfg = Some 30000) "";
  Configuration.set_many cfg
    [ "proof.fileMode", `String "realtime";
      "proof.realTimeReload", `String "prompt" ];
  check "set_many: fileMode = realtime"
    (Configuration.file_mode cfg = `Realtime) "";
  check "set_many: realTimeReload = prompt"
    (Configuration.real_time_reload cfg = `Prompt) ""

(* --- Request_registry ------------------------------------------ *)

let test_request_registry env =
  Printf.printf "\n== Request_registry ==\n%!";
  Eio.Switch.run @@ fun sw ->
  let reg = Request_registry.create () in
  check "empty registry size = 0" (Request_registry.size reg = 0) "";
  let corr1 = Correlation.of_client "req-1" in
  let corr2 = Correlation.of_client "req-2" in
  let cancelled1 = Atomic.make false in
  let cancelled2 = Atomic.make false in
  let done1 = Atomic.make false in
  let cancel_p1 = Request_registry.register reg corr1 in
  let cancel_p2 = Request_registry.register reg corr2 in
  Eio.Fiber.fork ~sw (fun () ->
    Fun.protect
      ~finally:(fun () -> Request_registry.unregister reg corr1)
      (fun () ->
        let outcome = Eio.Fiber.first
          (fun () ->
            Eio.Time.sleep (Eio.Stdenv.clock env) 5.0;
            `Done)
          (fun () ->
            Eio.Promise.await cancel_p1;
            `Cancelled)
        in
        match outcome with
        | `Done -> Atomic.set done1 true
        | `Cancelled -> Atomic.set cancelled1 true));
  Eio.Fiber.fork ~sw (fun () ->
    Fun.protect
      ~finally:(fun () -> Request_registry.unregister reg corr2)
      (fun () ->
        let outcome = Eio.Fiber.first
          (fun () ->
            Eio.Time.sleep (Eio.Stdenv.clock env) 5.0;
            `Done)
          (fun () ->
            Eio.Promise.await cancel_p2;
            `Cancelled)
        in
        match outcome with
        | `Done -> ()
        | `Cancelled -> Atomic.set cancelled2 true));
  (* Give fibers a chance to start. *)
  Eio.Time.sleep (Eio.Stdenv.clock env) 0.05;
  check "registry size = 2 after register" (Request_registry.size reg = 2)
    (Printf.sprintf "got %d" (Request_registry.size reg));
  Request_registry.cancel reg corr1;
  Eio.Time.sleep (Eio.Stdenv.clock env) 0.1;
  check "cancel(corr1) propagated" (Atomic.get cancelled1) "";
  check "corr2 still in flight" (not (Atomic.get cancelled2)) "";
  check "registry size = 1 after one cancel" (Request_registry.size reg = 1)
    (Printf.sprintf "got %d" (Request_registry.size reg));
  Request_registry.cancel_all reg;
  Eio.Time.sleep (Eio.Stdenv.clock env) 0.1;
  check "cancel_all propagated to corr2" (Atomic.get cancelled2) "";
  check "registry empty after cancel_all" (Request_registry.size reg = 0)
    (Printf.sprintf "got %d" (Request_registry.size reg));
  check "neither fiber completed naturally"
    (not (Atomic.get done1)) "fiber 1 ran to completion despite cancel";
  (* cancel on unknown id is silent *)
  let bogus = Correlation.of_client "bogus" in
  Request_registry.cancel reg bogus;
  check "cancel(unknown) is silent" true ""

(* --- Debouncer ------------------------------------------------- *)

let test_debouncer env =
  Printf.printf "\n== Debouncer ==\n%!";
  Eio.Switch.run @@ fun sw ->
  let processed = Atomic.make [] in
  let process v = Atomic.set processed (v :: Atomic.get processed) in
  let clock = Eio.Stdenv.clock env in
  let d = Debouncer.create ~sw ~clock ~delay:0.1 ~process in
  (* Trigger 5 times in quick succession; only the last value should
     be processed once after the debounce elapses. *)
  Debouncer.trigger d "v1";
  Debouncer.trigger d "v2";
  Debouncer.trigger d "v3";
  Debouncer.trigger d "v4";
  Debouncer.trigger d "v5";
  Eio.Time.sleep clock 0.05;
  check "debouncer hasn't fired yet" (Atomic.get processed = []) "";
  Eio.Time.sleep clock 0.2;
  let p = Atomic.get processed in
  check "debouncer fires exactly once after burst" (List.length p = 1)
    (Printf.sprintf "got %d invocations" (List.length p));
  check "debouncer processed latest value (v5)"
    (p = ["v5"])
    (Printf.sprintf "got [%s]" (String.concat "; " p));
  (* Trigger again, then flush before delay elapses; should NOT fire *)
  Atomic.set processed [];
  Debouncer.trigger d "v6";
  Eio.Time.sleep clock 0.02;
  Debouncer.flush d;
  Eio.Time.sleep clock 0.2;
  check "flush prevents pending fire" (Atomic.get processed = []) "";
  (* Trigger once after flush; should fire. *)
  Debouncer.trigger d "v7";
  Eio.Time.sleep clock 0.2;
  let p2 = Atomic.get processed in
  check "trigger after flush still works" (p2 = ["v7"])
    (Printf.sprintf "got [%s]" (String.concat "; " p2));

  (* Regression: process calls must not overlap. Pre-fix, two
     triggers spaced more than [delay] apart could fire two fibers
     past Eio.Fiber.first concurrently, both calling process at the
     same time — corrupts shared state in real consumers (analyze
     session's Buf_read). Use a slow process (longer than delay)
     and trigger repeatedly; assert the recorded intervals never
     overlap. *)
  let intervals : (float * float) list Atomic.t = Atomic.make [] in
  let now () = Eio.Time.now clock in
  let slow_process _v =
    let start = now () in
    Eio.Time.sleep clock 0.3;
    let stop = now () in
    Atomic.set intervals ((start, stop) :: Atomic.get intervals)
  in
  let d2 = Debouncer.create ~sw ~clock ~delay:0.05 ~process:slow_process in
  for i = 1 to 8 do
    Debouncer.trigger d2 (Printf.sprintf "burst-%d" i);
    Eio.Time.sleep clock 0.10
  done;
  (* Wait for any tail process to drain. *)
  Eio.Time.sleep clock 1.0;
  let ivs = List.sort compare (Atomic.get intervals) in
  let rec check_disjoint = function
    | [] | [_] -> true
    | (_, e1) :: ((s2, _) :: _ as rest) -> e1 <= s2 && check_disjoint rest
  in
  check "process calls never overlap" (check_disjoint ivs)
    (Printf.sprintf "intervals=%s"
       (String.concat ", "
          (List.map (fun (s, e) -> Printf.sprintf "[%.3f,%.3f]" s e) ivs)));
  check "coalescing reduces invocation count below trigger count"
    (List.length ivs < 8)
    (Printf.sprintf "got %d invocations for 8 triggers" (List.length ivs))

(* --- Main ------------------------------------------------------- *)

let () =
  test_log ();
  test_configuration ();
  Eio_main.run (fun env ->
    test_request_registry env;
    test_debouncer env);
  Printf.printf "\n== substrate smoke ==\n";
  Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
