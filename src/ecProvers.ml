(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
open EcUtils
open Why3
open EcSymbols

(* -------------------------------------------------------------------- *)
module Version : sig
  type version

  val parse   : string -> version
  val compare : version -> version -> int

  val of_tuple  : int * int * int -> version
  val to_string : version -> string
end = struct
  type version = {
    v_major    : int;
    v_minor    : int;
    v_subminor : int;
    v_extra    : string;
  }

  let of_tuple (v_major, v_minor, v_subminor) =
    { v_major; v_minor; v_subminor; v_extra = ""; }

  let parse =
    let pop (version : string) =
      let re = Str.regexp "^\\([0-9]+\\)[.-]?\\(.*\\)" in
      match Str.string_match re version 0 with
      | false -> (0, version)
      | true  ->
        let g1 = Str.matched_group 1 version
        and g2 = Str.matched_group 2 version in
        (int_of_string g1, g2)
    in

    fun (version : string) ->
      let (major   , version) = pop version in
      let (minor   , version) = pop version in
      let (subminor, version) = pop version in
      { v_major    = major;
        v_minor    = minor;
        v_subminor = subminor;
        v_extra    = version; }

  let compare (v1 : version) (v2 : version) =
    match compare v1.v_major    v2.v_major    with n when n <> 0 -> n | _ ->
    match compare v1.v_minor    v2.v_minor    with n when n <> 0 -> n | _ ->
    match compare v1.v_subminor v2.v_subminor with n when n <> 0 -> n | _ ->
    compare v1.v_extra v2.v_extra

  let to_string (v : version) =
    Printf.sprintf "%d.%d.%d.%s"
      v.v_major v.v_minor v.v_subminor v.v_extra
      
end

module VP = Version

(* -------------------------------------------------------------------- *)
type prover_eviction = [
  | `Inconsistent
]

type prover_eviction_test = {
  pe_cause : prover_eviction;
  pe_test  : [ `ByVersion of string * ([`Eq | `Lt | `Le] * VP.version) ];
}

let test_if_evict_prover test (name, version) =
  let evict =
    match test.pe_test with
    | `ByVersion (tname, (trel, tversion)) when name = tname -> begin
        let cmp = VP.compare (VP.parse version) tversion in
        match trel with
        | `Eq -> cmp =  0
        | `Lt -> cmp <  0
        | `Le -> cmp <= 0
      end
  
    | `ByVersion (_, _) -> false

  in if evict then Some test.pe_cause else None

let test_if_evict_prover tests prover =
  let module E = struct exception Evict of prover_eviction end in
  try
    List.iter (fun test ->
      match test_if_evict_prover test prover with
      | None -> ()
      | Some cause -> raise (E.Evict cause))
      tests;
    None
  with E.Evict cause -> Some cause

(* -------------------------------------------------------------------- *)
module Evictions = struct
  let alt_ergo_lt_0_96 = {
    pe_cause = `Inconsistent;
    pe_test  = `ByVersion ("Alt-Ergo", (`Lt, VP.of_tuple (0, 96, 0)));
  }
end

let evictions : prover_eviction_test list = [
  Evictions.alt_ergo_lt_0_96;
]

(* -------------------------------------------------------------------- *)
type prover = {
  pr_name    : string;
  pr_version : string;
  pr_evicted : (prover_eviction * bool) option;
}

let is_evicted pr =
  match pr.pr_evicted with
  | None | Some (_, true) -> false
  | Some (_, false) -> true

type why3prover = {
  pr_prover  : prover;
  pr_config  : Why3.Whyconf.config_prover;
  pr_driver  : Why3.Driver.driver;
}

module Config : sig
  val load :
       ?ovrevict:string list
    -> ?why3conf:string
    -> unit -> unit

  val w3_env   : unit -> Env.env
  val provers  : unit -> why3prover list
  val known    : evicted:bool -> prover list
end = struct
  let theconfig  : (Whyconf.config option) ref = ref None
  let themain    : (Whyconf.main   option) ref = ref None
  let thew3_env  : (Env.env        option) ref = ref None
  let theprovers : (why3prover     list  ) ref = ref []

  let load ?(ovrevict = []) ?why3conf () =
    if !theconfig = None then begin
      let config  = Whyconf.read_config why3conf in
      let main    = Whyconf.get_main config in

      Whyconf.load_plugins main;

      let w3_env  = Env.create_env (Whyconf.loadpath main) in

      let load_prover p config =
        let name    = p.Whyconf.prover_name in
        let version = p.Whyconf.prover_version in
        let driver  = Driver.load_driver w3_env config.Whyconf.driver [] in
  
        { pr_prover  =
            { pr_name    = name;
              pr_version = version;
              pr_evicted = None; };
          pr_config  = config;
          pr_driver  = driver; }
      in

      let provers =
        Whyconf.Mprover.fold
          (fun p c acc -> load_prover p c :: acc)
          (Whyconf.get_provers config) [] in

      let provers =
        List.map (fun prover ->
            let prinfo   = prover.pr_prover in
            let eviction = test_if_evict_prover evictions in
            let eviction = eviction (prinfo.pr_name, prinfo.pr_version) in
            let eviction =
              eviction |> omap (fun x -> (x, List.mem prinfo.pr_name ovrevict)) in
            let prinfo   = { prover.pr_prover with pr_evicted = eviction; } in
            { prover with pr_prover = prinfo })
          provers in

      theconfig   := Some config;
      themain     := Some main;
      thew3_env   := Some w3_env;
      theprovers  := provers;
    end

  let w3_env () =
    load (); EcUtils.oget !thew3_env

  let provers () =
    load (); !theprovers

  let known ~evicted =
    let test p =
      if   not evicted && is_evicted p.pr_prover
      then None
      else Some p.pr_prover in

    List.pmap test (provers ())
end

let initialize = Config.load
let known      = Config.known

(* -------------------------------------------------------------------- *)
exception UnknownProver of string

type parsed_pname = {
  prn_name     : string;
  prn_ovrevict : bool;
}

let parse_prover_name name =
  if   name <> "" && name.[0] = '!'
  then { prn_name     = String.sub name 1 (String.length name - 1);
         prn_ovrevict = true; }
  else { prn_name = name; prn_ovrevict = false; }

let get_prover name =
  let name = parse_prover_name name in

  let test p =
       p.pr_prover.pr_name = name.prn_name
    && (name.prn_ovrevict || not (is_evicted p.pr_prover)) in

  try  List.find test (Config.provers ())
  with Not_found -> raise (UnknownProver name.prn_name)

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

let dft_prover_names = ["Z3"; "CVC4"; "Alt-Ergo"; "Eprover"; "Yices"]

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
let run_prover (pi : prover_infos) (prover : string) task =
  try
    let { pr_config = pr; pr_driver = dr; } = get_prover prover in
    let pc =
      let command = pr.Whyconf.command in
      let command =
        match pi.pr_wrapper with
        | None -> command
        | Some wrapper -> Printf.sprintf "%s %s" wrapper command
      in

      let timelimit =
        if pi.pr_timelimit <= 0 then None else Some pi.pr_timelimit in
      Driver.prove_task ~command ?timelimit dr task ()
    in
      Some (prover, pc)

  with e ->
    Format.printf "\nError when starting %s: %a" prover
      EcPException.exn_printer e;
    None

(* -------------------------------------------------------------------- *)
module type PExec = sig
  val execute_task : prover_infos -> Why3.Task.task -> bool option
end

(* -------------------------------------------------------------------- *)
module POSIX : PExec = struct
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
      run_prover pi prover task
        |> oiter (fun (prover, pc) -> pcs.(i) <- Some (prover, pc))
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
            | Some (prover, pc) ->
                if CP.prover_call_pid pc = pid then begin
                  pcs.(i) <- None;            (* DO IT FIRST *)
                  let result = CP.post_wait_call pc st () in
                  let answer = result.CP.pr_answer in
                  match answer with
                  | CP.Valid   -> status := Some true
                  | CP.Invalid -> status := Some false
                  | CP.Failure _ | CP.HighFailure ->
                    Format.printf "\n[info] Warning: prover %s exited with %a\n%!"
                      prover CP.print_prover_answer answer;
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
end

(* -------------------------------------------------------------------- *)
module Win32 : PExec = struct
  exception Answer of bool

  let execute_task (pi : prover_infos) task =
    let module CP = Call_provers in

    let wait1 (prover, pc) =
      let result = CP.wait_on_call pc () in
      let answer = result.CP.pr_answer in

      match answer with
      | CP.Valid   -> raise (Answer true)
      | CP.Invalid -> raise (Answer false)
      | CP.Failure _ | CP.HighFailure ->
          Format.printf "\n[info] Warning: prover %s exited with %a\n%!"
          prover CP.print_prover_answer answer;
      | _ -> ()

    in

    let do1 (prover : string) =
      run_prover pi prover task |> oiter (fun (prover, pc) ->
        try  wait1 (prover, pc)
        with e -> begin
          (try  Unix.kill (CP.prover_call_pid pc) Sys.sigkill
	   with Unix.Unix_error _ -> ());
          raise e
        end)
     in

     try  List.iter do1 pi.pr_provers; None
     with Answer b -> Some b
end

(* -------------------------------------------------------------------- *)
let execute_task =
  match Sys.os_type with
  | "Win32" -> Win32.execute_task
  | _       -> POSIX.execute_task
