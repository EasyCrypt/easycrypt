type kind =
  | Request_in
  | Request_out
  | Notification_out
  | Session_spawn
  | Session_exec
  | Session_reply
  | Session_kill
  | Session_restart
  | Session_crashed
  | Pool_acquire
  | Pool_release
  | Pool_evict
  | Overlay_set
  | Overlay_clear
  | Overlay_apply
  | Cas_issue
  | Cas_stale_reject
  | Invariant_uuid_mismatch
  | Log_info
  | Log_warn
  | Log_error

let kind_to_string = function
  | Request_in              -> "request.in"
  | Request_out             -> "request.out"
  | Notification_out        -> "notification.out"
  | Session_spawn           -> "session.spawn"
  | Session_exec            -> "session.exec"
  | Session_reply           -> "session.reply"
  | Session_kill            -> "session.kill"
  | Session_restart         -> "session.restart"
  | Session_crashed         -> "session.crashed"
  | Pool_acquire            -> "pool.acquire"
  | Pool_release            -> "pool.release"
  | Pool_evict              -> "pool.evict"
  | Overlay_set             -> "overlay.set"
  | Overlay_clear           -> "overlay.clear"
  | Overlay_apply           -> "overlay.apply"
  | Cas_issue               -> "cas.issue"
  | Cas_stale_reject        -> "cas.stale_reject"
  | Invariant_uuid_mismatch -> "invariant.uuid_mismatch"
  | Log_info                -> "log.info"
  | Log_warn                -> "log.warn"
  | Log_error               -> "log.error"

(* A sink is a function that accepts one pre-formatted line (no
   trailing newline). The backend appends the newline and flushes. *)
type sink = string -> unit

type t = {
  mu     : Mutex.t;
  t0_ns  : int;
  write  : sink;
}

let now_monotonic_ns () =
  (* [Unix.gettimeofday] is wall-clock, not monotonic; on the platforms
     we care about, [Mtime_clock] would be better, but avoid the extra
     dep for PoC. Wall-clock drift is acceptable for a development
     transcript. *)
  int_of_float (Unix.gettimeofday () *. 1.0e9)

let make (write : sink) =
  { mu = Mutex.create (); t0_ns = now_monotonic_ns (); write }

let to_channel oc =
  make (fun line ->
    try
      output_string oc line;
      output_char oc '\n';
      flush oc
    with _ -> ())

let to_buffer buf =
  make (fun line ->
    Buffer.add_string buf line;
    Buffer.add_char buf '\n')

let devnull () = make (fun _ -> ())

let record t ?corr kind payload =
  let dt = now_monotonic_ns () - t.t0_ns in
  let micros = dt / 1_000 in
  let cid =
    match corr with
    | None -> `Null
    | Some c -> `String (Correlation.to_string c)
  in
  let line =
    Yojson.Safe.to_string (`Assoc [
      "t",       `Int micros;
      "cid",     cid;
      "kind",    `String (kind_to_string kind);
      "payload", payload;
    ])
  in
  Mutex.lock t.mu;
  (try t.write line with _ -> ());
  Mutex.unlock t.mu

(* Global singleton *)
let g = ref (devnull ())
let configure t = g := t
let current () = !g
let record_g ?corr kind payload = record !g ?corr kind payload
