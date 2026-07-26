type 'a t = {
  sw : Eio.Switch.t;
  clock : float Eio.Time.clock_ty Eio.Resource.t;
  delay : float;
  process : 'a -> unit;
  pending : 'a option Atomic.t;
  cancel_resolver : (unit Eio.Promise.u) option Atomic.t;
  (* Serializes process calls. Triggers spaced more than [delay]
     apart can each fire their own fiber past [Eio.Fiber.first]; the
     cancel mechanism only protects against still-sleeping fibers,
     so without serialization two [process] invocations could overlap
     and (in our use case) corrupt the analyze session's [Buf_read]
     by interleaving stdin writes / stdout reads on the same buffer. *)
  process_mutex : Eio.Mutex.t;
}

let create ~sw ~clock ~delay ~process =
  { sw;
    clock = (clock :> float Eio.Time.clock_ty Eio.Resource.t);
    delay;
    process;
    pending = Atomic.make None;
    cancel_resolver = Atomic.make None;
    process_mutex = Eio.Mutex.create ();
  }

let cancel_in_flight t =
  match Atomic.exchange t.cancel_resolver None with
  | None -> ()
  | Some resolver ->
    (try Eio.Promise.resolve resolver () with _ -> ())

let run_process_safely t v =
  try t.process v
  with exn ->
    (* Don't propagate — the debouncer fiber is daemon-lived and
       an uncaught exception would tear it down. Surface the
       failure in logs so it's not silently lost. *)
    try
      Printf.eprintf
        "debouncer: process raised %s\n%s%!"
        (Printexc.to_string exn)
        (Printexc.get_backtrace ())
    with _ -> ()

let trigger t value =
  Atomic.set t.pending (Some value);
  cancel_in_flight t;
  let promise, resolver = Eio.Promise.create () in
  Atomic.set t.cancel_resolver (Some resolver);
  Eio.Fiber.fork ~sw:t.sw (fun () ->
    let outcome =
      Eio.Fiber.first
        (fun () -> Eio.Time.sleep t.clock t.delay; `Fired)
        (fun () -> Eio.Promise.await promise; `Cancelled)
    in
    match outcome with
    | `Cancelled -> ()
    | `Fired ->
      (* Clear our cancel_resolver if we're still the current one
         (a later trigger may have already replaced it). *)
      let _ = Atomic.compare_and_set t.cancel_resolver
                (Some resolver) None in
      (* Serialize against any in-flight [process] call. While we
         wait, more triggers may set [pending]; the drain loop below
         coalesces them so we run [process] on the latest value
         without falling behind. *)
      Eio.Mutex.use_rw ~protect:false t.process_mutex (fun () ->
        let rec drain () =
          match Atomic.exchange t.pending None with
          | None -> ()
          | Some v -> run_process_safely t v; drain ()
        in
        drain ()))

let flush t =
  Atomic.set t.pending None;
  cancel_in_flight t
