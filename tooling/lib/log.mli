(** Structured operational logger. Distinct from [Transcript] (event
    log for replay determinism) and [Telemetry] (opt-in metrics).
    Three orthogonal channels in the daemon; this is for human-
    readable warnings, info, debug — for developers and sysadmins.

    Output: JSONL lines `{t, level, corr, msg}` to a configurable
    sink. Default: stderr at [`Info] level. CLI flag `--log <path>`
    overrides destination; `--log-level <lvl>` overrides level.

    Writes are serialised through a Mutex so concurrent Eio fibers
    can log safely. Write failures are swallowed (logging must not
    break the caller). *)

type level = [ `Debug | `Info | `Warn | `Error ]

type t

val to_channel : ?level:level -> out_channel -> t
val to_buffer  : ?level:level -> Buffer.t -> t
val devnull    : unit -> t
(** Default no-op sink. *)

(** Global convenience: one logger per daemon. Defaults to [devnull]
    until [configure] is called. *)
val configure : t -> unit
val current   : unit -> t

(** Per-call logging. [corr] threads correlation IDs into log lines
    so request flow can be reconstructed by grep. *)
val debug :
  ?corr:Correlation.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a
val info :
  ?corr:Correlation.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a
val warn :
  ?corr:Correlation.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a
val err :
  ?corr:Correlation.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a
