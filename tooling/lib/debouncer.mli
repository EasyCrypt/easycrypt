(** Per-document debouncer for didChange-driven work. Pattern:

    {[
      let d = Debouncer.create ~sw ~clock ~delay:0.2
        ~process:(fun new_state -> publish_diagnostics new_state)
      in
      (* on every didChange *)
      Debouncer.trigger d new_doc_state
    ]}

    Calling [trigger] cancels any pending sleep + reschedules. The
    processor only runs after [delay] elapses without further
    triggers. Latest-trigger value wins.

    Used in [Lsp_methods.register_diagnostics] to coalesce typing
    bursts: 5-10 didChange/sec compresses to one ANALYZE-JSON
    dispatch per ~200ms quiet period. *)

type 'a t

val create :
  sw:Eio.Switch.t ->
  clock:_ Eio.Time.clock ->
  delay:float ->
  process:('a -> unit) ->
  'a t

val trigger : 'a t -> 'a -> unit
(** Schedule [process value] to run after [delay] seconds. If a
    pending run exists, cancel it and reschedule with the new value. *)

val flush : 'a t -> unit
(** Cancel any pending run without processing. Call during shutdown. *)
