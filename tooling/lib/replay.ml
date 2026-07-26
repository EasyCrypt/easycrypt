(** Transcript replay driver. Consumes a `JSON-per-line` transcript
    produced by {!Transcript.to_channel}, re-drives a fresh
    {!Ec_llm_session} backend against each recorded session, and
    asserts that the live replies match what was recorded.

    The driver serves two roles:
    - **Test substrate**. Any PoC phase can record a transcript and
      rerun it as a golden. Changes to the daemon that preserve
      semantics should produce matching replays.
    - **Reproduction harness**. A bug seen in production with
      `--transcript foo.jsonl` can be rerun offline with `ecd replay
      foo.jsonl` to reproduce.

    Scope for v0:
    - Single-session replay (transcripts with multiple session labels
      replay each session in isolation, sequentially).
    - Compares `uuid`, `restarted`, `status`, and optionally the body
      line list.
    - Ignores timing, correlation IDs, pid, and notice ordering —
      those are recording-environment-specific.
    - Events the replayer doesn't understand are skipped; the
      comparison rests on `session.exec` events being followed by a
      `session.reply`, `session.restart`, or
      `invariant.uuid_mismatch` event for the same session label. *)

open Eio.Std

(* ---------------------------------------------------------------- *)
(* Parsed event                                                       *)
(* ---------------------------------------------------------------- *)

type event = {
  kind    : string;
  sess    : string option;
  payload : Yojson.Safe.t;
}

let parse_line (line : string) : event option =
  match Yojson.Safe.from_string line with
  | exception _ -> None
  | json ->
    let open Yojson.Safe.Util in
    (try
       let kind = json |> member "kind" |> to_string in
       let payload = json |> member "payload" in
       let sess =
         try Some (payload |> member "label" |> to_string)
         with _ -> None
       in
       Some { kind; sess; payload }
     with _ -> None)

let read_events (path : string) : event list =
  let ic = open_in path in
  Fun.protect
    ~finally:(fun () -> try close_in ic with _ -> ())
    (fun () ->
       let rec loop acc =
         match input_line ic with
         | exception End_of_file -> List.rev acc
         | line ->
           match parse_line line with
           | None -> loop acc
           | Some e -> loop (e :: acc)
       in
       loop [])

(* ---------------------------------------------------------------- *)
(* Comparison + per-session replay                                    *)
(* ---------------------------------------------------------------- *)

type mismatch = {
  seq      : int;     (** Index of the offending exec within the session. *)
  expected : string;  (** Human-readable description of the recorded outcome. *)
  got      : string;  (** Human-readable description of the live outcome. *)
}

type session_result = {
  label      : string;
  execs      : int;   (** How many session.exec events we replayed. *)
  matches    : int;   (** Of those, how many matched the recording. *)
  mismatches : mismatch list;
}

type options = {
  strict_body : bool;
  (** When true, also require the reply body (line list) to match.
      Defaults to false — bodies are deterministic in principle but
      formatting whitespace / goal rendering can drift across EC
      builds, and the replay driver's primary value is invariant
      checking on uuid + restart semantics. *)
}

let default_options = { strict_body = false }

let string_of_class (payload : Yojson.Safe.t)
  : [ `Executable | `Doc_comment | `Directive | `Meta ] option =
  let open Yojson.Safe.Util in
  match payload |> member "class" with
  | exception _ -> None
  | `String "executable"  -> Some `Executable
  | `String "doc_comment" -> Some `Doc_comment
  | `String "directive"   -> Some `Directive
  | `String "meta"        -> Some `Meta
  | _ -> None

let expected_summary (outcome_event : event) : string =
  let open Yojson.Safe.Util in
  match outcome_event.kind with
  | "session.reply" ->
    let status =
      try outcome_event.payload |> member "status" |> to_string
      with _ -> "?"
    in
    let uuid =
      try outcome_event.payload |> member "uuid" |> to_int
      with _ -> -1
    in
    let restarted =
      try outcome_event.payload |> member "restarted" |> to_bool
      with _ -> false
    in
    Printf.sprintf "reply status=%s uuid=%d restarted=%b"
      status uuid restarted
  | "session.restart" ->
    let new_uuid =
      try outcome_event.payload |> member "new_uuid" |> to_int
      with _ -> -1
    in
    Printf.sprintf "restart new_uuid=%d" new_uuid
  | "invariant.uuid_mismatch" ->
    "invariant.uuid_mismatch"
  | other -> Printf.sprintf "<%s>" other

let live_summary_ok (ok : Session.exec_ok) =
  Printf.sprintf "reply status=ok uuid=%d restarted=%b"
    ok.replied_uuid ok.restarted

let live_summary_err (e : Error.t) =
  Printf.sprintf "error: %s" (Error.to_string e)

(* Partition events for one session label, preserving order. *)
let events_for_label (events : event list) (label : string) : event list =
  List.filter
    (fun e ->
       match e.sess with
       | Some l when l = label -> true
       | _ -> false)
    events

(* Split events into (exec, outcome) pairs. Outcome is the next
   session.reply / session.restart / invariant.uuid_mismatch that
   follows the exec within the same session. *)
type exec_pair = {
  exec    : event;
  outcome : event option;
}

let pair_execs (events : event list) : exec_pair list =
  let rec loop acc = function
    | [] -> List.rev acc
    | e :: rest when e.kind = "session.exec" ->
      let outcome =
        List.find_opt
          (fun e2 ->
             e2.kind = "session.reply"
             || e2.kind = "session.restart"
             || e2.kind = "invariant.uuid_mismatch")
          rest
      in
      loop ({ exec = e; outcome } :: acc) rest
    | _ :: rest -> loop acc rest
  in
  loop [] events

let labels_in (events : event list) : string list =
  let seen = Hashtbl.create 4 in
  List.iter
    (fun e ->
       match e.sess with
       | Some l when not (Hashtbl.mem seen l) ->
         Hashtbl.add seen l ()
       | _ -> ())
    events;
  Hashtbl.fold (fun l () acc -> l :: acc) seen []

(* Replay a single session's exec pairs against a freshly-spawned
   backend. Stops early on a fatal error (session crashed / cancelled
   in a way that prevents further execs); mismatches before that
   point are reported normally. *)
let replay_session ~env ~sw ~options ~label (pairs : exec_pair list)
  : session_result =
  let _ = env in
  let session = Ec_llm_session.start ~sw ~label:("replay-" ^ label) in
  let mismatches = ref [] in
  let matches = ref 0 in
  let record_mismatch seq expected got =
    mismatches := { seq; expected; got } :: !mismatches
  in
  let rec go seq = function
    | [] -> ()
    | pair :: rest ->
      let open Yojson.Safe.Util in
      let source =
        try pair.exec.payload |> member "source" |> to_string
        with _ -> ""
      in
      if source = "" then begin
        (* Pre-schema-extension transcript: no source recorded. Abort
           this session's replay with a clear message. *)
        record_mismatch seq
          "session.exec carrying `source` field"
          "session.exec payload missing `source` — transcript predates \
           replay-schema extension";
        ()
      end
      else begin
        let is_exec_json =
          let open Yojson.Safe.Util in
          try pair.exec.payload |> member "exec_json" |> to_bool
          with _ -> false
        in
        let corr =
          Correlation.of_client (Printf.sprintf "replay-%s-%d" label seq)
        in
        let live =
          if is_exec_json then
            (* Addition 13 events: the recorded [source] is the JSON
               command payload. Dispatch through [exec_json] so the
               server sees an [EXEC-JSON] request, not a <BEGIN> frame. *)
            Ec_llm_session.exec_json session ~corr ~command_json:source
          else
            let cls =
              match string_of_class pair.exec.payload with
              | Some (`Executable | `Doc_comment | `Directive as c) -> c
              | _ ->
                (* Best-effort fallback; EC will refuse [`Meta]. *)
                `Executable
            in
            Ec_llm_session.exec session ~corr ~sentence_class:cls ~source
        in
        let expected =
          match pair.outcome with
          | Some ev -> expected_summary ev
          | None -> "<no outcome recorded>"
        in
        let got =
          match live with
          | Ok ok -> live_summary_ok ok
          | Error e -> live_summary_err e
        in
        let matches_invariant =
          match pair.outcome, live with
          | Some ev, Ok ok ->
            (match ev.kind with
             | "session.reply" ->
               let status =
                 try ev.payload |> member "status" |> to_string
                 with _ -> ""
               in
               let uuid =
                 try ev.payload |> member "uuid" |> to_int
                 with _ -> -1
               in
               let restarted =
                 try ev.payload |> member "restarted" |> to_bool
                 with _ -> false
               in
               status = "ok"
               && uuid = ok.replied_uuid
               && restarted = ok.restarted
             | "session.restart" ->
               let new_uuid =
                 try ev.payload |> member "new_uuid" |> to_int
                 with _ -> -1
               in
               ok.restarted && new_uuid = ok.replied_uuid
             | _ -> false)
          | Some ev, Error _ ->
            ev.kind = "session.reply"
            && (try ev.payload |> member "status" |> to_string = "error"
                with _ -> false)
          | None, _ -> false
        in
        let body_ok =
          if not options.strict_body then true
          else match pair.outcome, live with
            | Some ev, Ok ok when ev.kind = "session.reply"
                               || ev.kind = "session.restart" ->
              let recorded_body =
                try ev.payload |> member "body" |> to_list
                    |> List.map to_string
                with _ -> []
              in
              String.concat "\n" recorded_body = ok.output
            | _ -> true
        in
        if matches_invariant && body_ok then incr matches
        else record_mismatch seq expected got;
        (* Continue unless the live side died fatally. *)
        match live with
        | Ok _ -> go (seq + 1) rest
        | Error (Error.Session_restarted _) ->
          (* If the recorded path also restarted, the next exec
             happens on a fresh subprocess — the live session is
             equivalent. If it was a crash, we can still try to
             continue; Ec_llm_session.exec will return errors. *)
          go (seq + 1) rest
        | Error _ -> go (seq + 1) rest
      end
  in
  go 0 pairs;
  Ec_llm_session.close session;
  {
    label;
    execs = List.length pairs;
    matches = !matches;
    mismatches = List.rev !mismatches;
  }

(* ---------------------------------------------------------------- *)
(* Public entry                                                       *)
(* ---------------------------------------------------------------- *)

let run ~env ~options (transcript_path : string) : session_result list =
  Switch.run @@ fun sw ->
  let events = read_events transcript_path in
  let labels = labels_in events in
  List.map
    (fun label ->
       let session_events = events_for_label events label in
       let pairs = pair_execs session_events in
       replay_session ~env ~sw ~options ~label pairs)
    labels
