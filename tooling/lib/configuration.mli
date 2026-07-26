(** Workspace / per-document configuration. Typed accessors over a
    flat string→Yojson.Safe.t store. Settings come from LSP
    [workspace/configuration] requests; defaults baked in here.

    Schema in [doc/lsp-schema.md] § 15. Settings list grows as
    features land; this module owns the default-value table. *)

type t

val create : unit -> t
(** Fresh configuration with all defaults. *)

(** Replace a setting. Caller is responsible for type compatibility
    with the accessors. *)
val set : t -> string -> Yojson.Safe.t -> unit

(** Replace many settings at once (e.g., from a single LSP
    [workspace/configuration] response). *)
val set_many : t -> (string * Yojson.Safe.t) list -> unit

(** {2 Typed accessors — return defaults when unset / wrong type} *)

val file_mode : t -> [ `Preservation | `Realtime ]
val real_time_reload : t -> [ `Instant | `Prompt ]
val cache_policy : t -> [ `Lax | `Strict ]
val goals_cache_budget_mb : t -> int
val recovery_strategy : t -> [ `Halt | `Best_effort_admit ]
val auto_reconcile : t -> bool
val debounce_ms : t -> int
val max_exec_ms_per_sentence : t -> int option
val speculation_enabled : t -> bool
val speculation_budget_ms : t -> int
val bullet_semantics : t -> [ `Strict | `Lenient | `Off ]

(** {2 Global singleton convenience} *)

val configure : t -> unit
val current : unit -> t
