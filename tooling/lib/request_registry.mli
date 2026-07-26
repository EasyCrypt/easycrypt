(** Generic in-flight-request registry. Surface-agnostic — used by
    LSP and MCP servers to track in-flight client requests so cancel
    notifications can interrupt the right work.

    Pattern:
    {[
      let reg = Request_registry.create () in
      (* on inbound request *)
      let cancel_p = Request_registry.register reg corr in
      Fun.protect
        ~finally:(fun () -> Request_registry.unregister reg corr)
        (fun () ->
          (* race work against cancel signal *)
          Eio.Fiber.first
            (fun () -> handle_request (); `Done)
            (fun () -> Eio.Promise.await cancel_p; `Cancelled))
      |> ignore
      (* on inbound cancel *)
      Request_registry.cancel reg corr;
    ]}

    Each registered request gets a unit promise. The request fiber
    races its work against awaiting the promise; cancel resolves the
    promise; the race aborts the work. Avoids switch poisoning of
    [Eio.Switch.fail].

    Thread-safe under Eio fiber concurrency (Hashtbl protected by
    Mutex). [cancel] is idempotent and silent on unknown ids — fits
    LSP semantics where cancel notifications may race with normal
    completion. *)

type t

val create : unit -> t

val register : t -> Correlation.t -> unit Eio.Promise.t
(** Register a new in-flight request for [corr]. Returns the
    cancel-signal promise the request fiber should race against.
    Replaces any prior registration for [corr]. *)

val unregister : t -> Correlation.t -> unit
(** Remove [corr]'s entry. Idempotent. Call from the request fiber's
    [Fun.protect ~finally] so cleanup runs even on cancellation. *)

val cancel : t -> Correlation.t -> unit
(** Cancel [corr]'s in-flight work by resolving its cancel promise.
    Idempotent; silent on unknown ids (cancel-races-with-completion
    is normal). *)

val cancel_all : t -> unit
(** Cancel every registered request. Used during shutdown. *)

val size : t -> int
(** Current number of in-flight registrations. For diagnostics. *)
