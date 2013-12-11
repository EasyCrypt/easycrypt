(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open Why3

(* ----------------------------------------------------------------------*)
module Config : sig
  type prover =
    string * Why3.Whyconf.config_prover * Why3.Driver.driver

  val load    : string option -> unit
  val w3_env  : unit -> Env.env
  val provers : unit -> prover list
  val known_provers : unit -> string list
end = struct
  type prover =
    string * Why3.Whyconf.config_prover * Why3.Driver.driver

  let theconfig  : (Whyconf.config option) ref = ref None
  let themain    : (Whyconf.main   option) ref = ref None
  let thew3_env  : (Env.env        option) ref = ref None
  let theprovers : (_              list  ) ref = ref []

  let load why3config =
    if !theconfig = None then begin
      let config  = Whyconf.read_config why3config in
      let main    = Whyconf.get_main config in
      Whyconf.load_plugins main;
      let w3_env  = Env.create_env (Whyconf.loadpath main) in
      let provers =
        Whyconf.Mprover.fold
          (fun p config l ->
            (p.Whyconf.prover_name, config,
             Driver.load_driver w3_env config.Whyconf.driver []) :: l)
          (Whyconf.get_provers config) []
      in
        theconfig  := Some config;
        themain    := Some main;
        thew3_env  := Some w3_env;
        theprovers := provers
    end

  let w3_env () =
    load None; EcUtils.oget !thew3_env

  let provers () =
    load None; !theprovers

  let known_provers () =
    List.map (fun (p,_,_) -> p) (provers())
end

let initialize    = Config.load
let known_provers = Config.known_provers

(* -------------------------------------------------------------------- *)
exception UnknownProver of string

let get_prover name =
  try  List.find (fun (s,_,_) -> s = name) (Config.provers ())
  with Not_found -> raise (UnknownProver name)

let is_prover_known name =
  try ignore (get_prover name); true with UnknownProver _ -> false

(* -------------------------------------------------------------------- *)
let get_w3_th dirname name =
  Env.find_theory (Config.w3_env ()) dirname name

(* -------------------------------------------------------------------- *)
type prover_infos = {
  pr_maxprocs  : int;
  pr_provers   : string list;
  pr_timelimit : int;
  pr_wrapper   : string option;
}

let dft_prover_infos = {
  pr_maxprocs  = 3;
  pr_provers   = [];
  pr_timelimit = 3;
  pr_wrapper   = None;
}

let dft_prover_names = ["Alt-Ergo"; "Z3"; "Vampire"; "Eprover"; "Yices"]

(* -------------------------------------------------------------------- *)
type hflag = [ `Include | `Exclude ]
type xflag = [ hflag | `Inherit ]

type hints = {
  ht_this : xflag;
  ht_axs  : hflag Msym.t;
  ht_sub  : hints Msym.t;
}

module Hints = struct
  open EcPath

  let create (xflag : xflag) = {
    ht_this = xflag;
    ht_axs  = Msym.empty;
    ht_sub  = Msym.empty;
  }

  let empty : hints = create `Exclude
  let full  : hints = create `Include

  let rec acton (cb : hints -> hints) (p : path option) (m : hints) =
    match p with
    | None   -> cb m
    | Some p ->
        let x = EcPath.basename p in
        let p = EcPath.prefix p in
          acton (fun m ->
            { m with ht_sub =
                Msym.change
                  (fun s -> Some (cb (odfl (create `Inherit) s)))
                  x m.ht_sub })
            p m

  let add1 (p : path) (h : hflag) (m : hints) =
    let x = EcPath.basename p in
    let p = EcPath.prefix p in
      acton (fun m -> { m with ht_axs = Msym.add x h m.ht_axs }) p m

  let addm (p : path) (h : hflag) (m : hints) =
    let x = EcPath.basename p in
    let p = EcPath.prefix p in
      acton
        (fun m ->
           { m with ht_sub = Msym.add x (create (h :> xflag)) m.ht_sub })
        p m

  let mem (p : path) m =
    let rec find p m =
      match p with
      | None   -> m
      | Some p ->
          let x = EcPath.basename p in
          let p = EcPath.prefix p in
          let m = find p m in
            match Msym.find_opt x m.ht_sub with
            | Some m' when m'.ht_this = `Inherit -> { m' with ht_this = m.ht_this }
            | Some m' -> m'
            | None    -> create m.ht_this
    in

    let m = find (EcPath.prefix p) m in
      match Msym.find_opt (EcPath.basename p) m.ht_axs with
      | None when m.ht_this = `Include -> true
      | None when m.ht_this = `Exclude -> false
      | None -> assert false
      | Some `Include -> true
      | Some `Exclude -> false
end

(* -------------------------------------------------------------------- *)
let restartable_syscall (call : unit -> 'a) : 'a =
  let output = ref None in
    while !output = None do
      try  output := Some (call ())
      with
      | Unix.Unix_error (errno, _, _) when errno = Unix.EINTR -> ()
    done;
    EcUtils.oget !output

let execute_task (pi : prover_infos) task =
  let module CP = Call_provers in

  let pcs = Array.create pi.pr_maxprocs None in

  (* Run process, ignoring prover failing to start *)
  let run i prover =
    try
      let (_, pr, dr)  = get_prover prover in
      let pc =
        let command = pr.Whyconf.command in
        let command =
          match pi.pr_wrapper with
          | None -> command
          | Some wrapper -> Printf.sprintf "%s %s" wrapper command
        in
          Driver.prove_task ~command ~timelimit:pi.pr_timelimit dr task ()
      in
        pcs.(i) <- Some (prover, pc)
    with e ->
      Format.printf "Error when starting %s: %a" prover
        EcPException.exn_printer e;
      ()
  in

  EcUtils.try_finally
    (fun () ->
      (* Start the provers, at most maxprocs run in the same time *)
      let pqueue = Queue.create () in
      List.iteri
        (fun i prover ->
           if i < pi.pr_maxprocs then run i prover else Queue.add prover pqueue)
        pi.pr_provers;
           
      (* Wait for the first prover giving a definitive answer *)
      let status = ref None in
      let alives = ref (-1) in
      while !alives <> 0 && !status = None do
        let pid, st =
          try  restartable_syscall Unix.wait
          with Unix.Unix_error _ -> (-1, Unix.WEXITED 127)
        in
        alives := 0;
        for i = 0 to (Array.length pcs) - 1 do
          match pcs.(i) with
          | None -> ()
          | Some (_prover, pc) ->
              if CP.prover_call_pid pc = pid then begin
                pcs.(i) <- None;            (* DO IT FIRST *)
                let result = CP.post_wait_call pc st () in
                let ans = result.CP.pr_answer in
                match ans with
                | CP.Valid   -> status := Some true
                | CP.Invalid -> status := Some false
                | CP.Failure _ | CP.HighFailure ->
                  Format.printf "[info] Warning: prover %s exited with %a\n%!" 
                    _prover CP.print_prover_answer ans;
                  if not (Queue.is_empty pqueue) then run i (Queue.take pqueue)
                | _ ->
                  if not (Queue.is_empty pqueue) then run i (Queue.take pqueue)
              end;
              if pcs.(i) <> None then incr alives
        done
      done;
      !status)

    (* Clean-up: hard kill + wait for remaining provers *)
    (fun () ->
      for i = 0 to (Array.length pcs) - 1 do
        match pcs.(i) with
        | None -> ()
        | Some (_prover,pc) ->
            let pid = CP.prover_call_pid pc in
            pcs.(i) <- None;
            begin try Unix.kill pid 15 with Unix.Unix_error _ -> () end;
            let _, st =
              restartable_syscall (fun () -> Unix.waitpid [] pid)
            in
            ignore (CP.post_wait_call pc st ());
      done)
