module Make (B : Session.BACKEND) = struct
  type kind = [ `Lsp | `Mcp | `Spec ]

  type config = {
    pool_size : int;
    k_lsp : int;
    k_mcp : int;
    k_spec : int;
  }

  type entry = {
    session : B.t;
    mutable in_use : bool;
    mutable kind : kind option;
  }

  type t = {
    config : config;
    entries : entry array;
  }

  let make ~sw config =
    assert (config.k_lsp + config.k_mcp + config.k_spec <= config.pool_size);
    let entries =
      Array.init config.pool_size (fun i ->
          {
            session = B.start ~sw ~label:(Printf.sprintf "scratch-%d" i);
            in_use = false;
            kind = None;
          })
    in
    { config; entries }

  let in_use_count t kind =
    Array.fold_left
      (fun acc e -> if e.in_use && e.kind = Some kind then acc + 1 else acc)
      0 t.entries

  let quota t = function
    | `Lsp -> t.config.k_lsp
    | `Mcp -> t.config.k_mcp
    | `Spec -> t.config.k_spec

  let acquire_scratch t ~kind ~corr:_ =
    let cur = in_use_count t kind in
    let q = quota t kind in
    (* Simple policy: quota applies as a *reservation floor* — the kind
       always gets at least [q] slots; beyond that, falls back to the
       shared pool. *)
    let free = ref None in
    Array.iter
      (fun e -> if (not e.in_use) && !free = None then free := Some e)
      t.entries;
    match !free with
    | None -> Error (Error.Pool_exhausted { kind })
    | Some e ->
        let reserved_in_use = in_use_count t `Lsp
                              + in_use_count t `Mcp
                              + in_use_count t `Spec in
        let total_reserved = t.config.k_lsp + t.config.k_mcp + t.config.k_spec in
        if cur >= q && reserved_in_use >= total_reserved
           && Array.fold_left
                (fun a e -> if e.in_use then a + 1 else a) 0 t.entries
              >= t.config.pool_size
        then Error (Error.Pool_exhausted { kind })
        else (
          e.in_use <- true;
          e.kind <- Some kind;
          Ok e.session)

  let release t session =
    Array.iter
      (fun e ->
        if e.session == session then (
          e.in_use <- false;
          e.kind <- None))
      t.entries

  let close_all t = Array.iter (fun e -> B.close e.session) t.entries
end
