(** In-memory publish point with subscribe/publish semantics suitable
    for smoke tests. Delivers events synchronously to every subscriber. *)

type state = {
  mutable subscribers : (Publish.event -> unit) list;
  mutable last_snapshot : Publish.snapshot;
  mutable emitted : Publish.event list;
}

let make_state () : state =
  {
    subscribers = [];
    last_snapshot =
      { cas = "00000000000000000000000000000000";
        current_sentence = None;
        overlay_stack = [];
      };
    emitted = [];
  }

module As_point : Publish.POINT with type state = state = struct
  type nonrec state = state

  let publish s ev =
    s.emitted <- ev :: s.emitted;
    (match ev with
     | Publish.State_changed { cas; current_sentence; _ } ->
         s.last_snapshot <-
           { s.last_snapshot with cas; current_sentence = Some current_sentence }
     | Publish.Server_restarted { new_cas; _ } ->
         s.last_snapshot <-
           { cas = new_cas; current_sentence = None; overlay_stack = [] }
     | Publish.Session_crashed _ ->
         (* Crash doesn't update the snapshot — the pool replaces the
            slot and a subsequent state-mutating exec will refresh CAS. *)
         ());
    List.iter (fun f -> f ev) s.subscribers

  let snapshot s = s.last_snapshot
  let subscribe s f = s.subscribers <- f :: s.subscribers
end

let make () : Publish.t * state =
  let s = make_state () in
  (Publish.of_impl (module As_point) s, s)

let events_emitted s = List.rev s.emitted
