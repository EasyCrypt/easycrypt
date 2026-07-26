type entry = {
  promise : unit Eio.Promise.t;
  resolver : unit Eio.Promise.u;
}

type t = {
  mu : Mutex.t;
  tbl : (string, entry) Hashtbl.t;
}

let create () = {
  mu = Mutex.create ();
  tbl = Hashtbl.create 32;
}

let with_lock t f =
  Mutex.lock t.mu;
  let r = try f () with e -> Mutex.unlock t.mu; raise e in
  Mutex.unlock t.mu;
  r

let key corr = Correlation.to_string corr

let register t corr =
  let promise, resolver = Eio.Promise.create () in
  with_lock t (fun () ->
    Hashtbl.replace t.tbl (key corr) { promise; resolver });
  promise

let unregister t corr =
  with_lock t (fun () -> Hashtbl.remove t.tbl (key corr))

let cancel t corr =
  let entry_opt =
    with_lock t (fun () -> Hashtbl.find_opt t.tbl (key corr))
  in
  match entry_opt with
  | None -> ()
  | Some { resolver; promise } ->
    if not (Eio.Promise.is_resolved promise) then
      (try Eio.Promise.resolve resolver () with _ -> ())

let cancel_all t =
  let entries =
    with_lock t (fun () ->
      Hashtbl.fold (fun _ e acc -> e :: acc) t.tbl [])
  in
  List.iter (fun { resolver; promise } ->
    if not (Eio.Promise.is_resolved promise) then
      try Eio.Promise.resolve resolver () with _ -> ())
    entries

let size t =
  with_lock t (fun () -> Hashtbl.length t.tbl)
