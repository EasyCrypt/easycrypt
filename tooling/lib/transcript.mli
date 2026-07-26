(** Structured per-event transcript log. See [doc/tooling-protocol.md]
    § 14. One JSON object per line:
      {"t": <monotonic micros since init>,
       "cid": "<correlation id | null>",
       "kind": "<event kind>",
       "payload": { ... }}

    Writes are serialised through a Mutex so concurrent Eio fibers
    can record events safely. The transcript is a best-effort log —
    write failures are swallowed rather than propagated to callers. *)

type t

(** Event kinds listed in the protocol spec § 14. The set is open-ended
    — add a variant here when a new event kind is introduced and keep
    [doc/tooling-protocol.md] § 14 in sync. *)
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
  (** Subprocess exited unexpectedly (not via [close]/[cancel]).
      Payload: [{label, exit_kind: "exit:N" | "signal:N"}]. Published
      by the per-session supervisor fiber. *)
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

val to_channel : out_channel -> t
val to_buffer  : Buffer.t -> t
val devnull    : unit -> t
(** Default no-op transcript. *)

val record :
  t ->
  ?corr:Correlation.t ->
  kind ->
  Yojson.Safe.t ->
  unit

(** Global convenience: one transcript per daemon. Callers may use
    [configure] at startup and [current] / [record_g] from anywhere.
    Defaults to [devnull] until configured. *)

val configure : t -> unit
val current   : unit -> t
val record_g  :
  ?corr:Correlation.t ->
  kind ->
  Yojson.Safe.t ->
  unit
