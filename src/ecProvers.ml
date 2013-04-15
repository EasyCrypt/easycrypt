(* -------------------------------------------------------------------- *)
(* ---------------------- Calling prover ------------------------------ *)
(* -------------------------------------------------------------------- *)

open Why3

(* ----------------------------------------------------------------------*)
module Config : sig
  type prover =
    string * Why3.Whyconf.config_prover * Why3.Driver.driver

  val load    : string option -> unit
  val config  : unit -> Whyconf.config
  val main    : unit -> Whyconf.main
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

  let config () =
    load None; EcUtils.oget !theconfig

  let main () =
    load None; EcUtils.oget !themain

  let w3_env () =
    load None; EcUtils.oget !thew3_env

  let provers () =
    load None; !theprovers

  let known_provers () =
    List.map (fun (p,_,_) -> p) (provers())

end

let initialize    = Config.load
let known_provers = Config.known_provers

let get_w3_th dirname name =
  Env.find_theory (Config.w3_env ()) dirname name

exception UnknownProver of string

let get_prover name =
  List.find (fun (s,_,_) -> s = name) (Config.provers ())

let check_prover_name name =
  try ignore(get_prover name); true with _ -> false

(* -------------------------------------------------------------------- *)
let restartable_syscall (call : unit -> 'a) : 'a =
  let output = ref None in
    while !output = None do
      try  output := Some (call ())
      with
      | Unix.Unix_error (errno, _, _) when errno = Unix.EINTR -> ()
    done;
    EcUtils.oget !output

let para_call max_provers provers timelimit task =
  let module CP = Call_provers in

  let pcs    = Array.create max_provers None in

  (* Run process, ignoring prover failing to start *)
  let run i prover =
    try
      let (_, pr, dr)  = get_prover prover in
(*      Format.printf "Start prover %s@." prover; *)
      let pc =
        Driver.prove_task ~command:pr.Whyconf.command ~timelimit dr task () in

      begin
        try
          ExtUnix.All.setpgid (CP.prover_call_pid pc) 0
        with Unix.Unix_error _ -> ()
      end;
      pcs.(i) <- Some(prover, pc)
 (*  Format.printf "Prover %s started and set at %i@." prover i *)
    with e ->
      Format.printf "Error when starting %s: %a" prover
        EcPException.exn_printer e;
      ()
  in

  (* Start the provers, at most max_provers run in the same time *)
  let nb_provers = Array.length provers in
  let min = if max_provers < nb_provers then max_provers else nb_provers in
  for i = 0 to min - 1 do run i provers.(i) done;
  (* Other provers are set in a queue *)
  let pqueue = Queue.create () in
  for i = min to nb_provers - 1 do Queue.add provers.(i) pqueue done;

  (* Wait for the first prover giving a definitive answer *)
  let status = ref None in
  EcUtils.try_finally
    (fun () ->
      let alives = ref (-1) in
      while !alives <> 0 && !status = None do
        let pid, st = restartable_syscall Unix.wait in
        alives := 0;
        for i = 0 to (Array.length pcs) - 1 do
          match pcs.(i) with
          | None -> ()
          | Some (_prover, pc) ->
              if CP.prover_call_pid pc = pid then begin
                pcs.(i) <- None;            (* DO IT FIRST *)
                let ans = (CP.post_wait_call pc st ()).CP.pr_answer in
                (*Format.eprintf "prover `%s' return %a@."
                  prover CP.print_prover_answer ans; *)
                match ans with
                | CP.Valid   -> status := Some true
                | CP.Invalid -> status := Some false
                | _          ->
                    if not (Queue.is_empty pqueue) then
                      run i (Queue.take pqueue)
              end;
              if pcs.(i) <> None then incr alives
        done
      done;
      !status)

    (* Clean-up: hard kill + wait for remaining provers *)
    (fun () ->
      for i = 0 to (Array.length pcs) - 1 do
        match pcs.(i) with
        | None    -> ()
        | Some (_prover,pc) ->
            let pid = CP.prover_call_pid pc in
            pcs.(i) <- None;
            begin try
(*              Format.printf
                "Killing (SIGTERM) prover `%s' (pid = %d)@."
                prover pid; *)
              Unix.kill (-pid) 15;      (* kill process group *)
            with Unix.Unix_error _ -> ()
            end;
(*            Format.printf "prover %s finished@." prover; *)
            let _, st =
              restartable_syscall (fun () -> Unix.waitpid [] pid)
            in
            ignore (CP.post_wait_call pc st ());
      done)

type prover_infos =
  { prover_max_run   : int;
    prover_names     : string array;
    prover_timelimit : int; }

let dft_prover_infos =
  { prover_max_run   = 7;
    prover_names     = [||];
    prover_timelimit = 3; }


let call_prover_task pi task =
  para_call pi.prover_max_run pi.prover_names pi.prover_timelimit task =
  Some true
