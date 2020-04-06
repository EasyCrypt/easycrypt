(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
      let rex = EcRegexp.regexp "^([0-9]+)[.-]?(.*)" in
      match EcRegexp.exec (`C rex) version with
      | Some m ->
         let m = EcRegexp.Match.groups m in
         (int_of_string (oget m.(1)), (oget m.(2)))

      | None -> (0, version)
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
  let alt_ergo_le_0_99_1 = {
    pe_cause = `Inconsistent;
    pe_test  = `ByVersion ("Alt-Ergo", (`Le, VP.of_tuple (2, 3, 0)));
  }
end

let evictions : prover_eviction_test list = [
  Evictions.alt_ergo_le_0_99_1;
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
        let driver  = Whyconf.load_driver main w3_env config.Whyconf.driver [] in

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
  Env.read_theory (Config.w3_env ()) dirname name

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
type prover_infos = {
  pr_maxprocs  : int;
  pr_provers   : string list;
  pr_timelimit : int;
  pr_cpufactor : int;
  pr_quorum    : int;
  pr_verbose   : int;
  pr_all       : bool;
  pr_max       : int;
  pr_iterate   : bool;
  pr_wanted    : hints;
  pr_unwanted  : hints;
  pr_selected  : bool;
}


let dft_prover_infos = {
  pr_maxprocs  = 3;
  pr_provers   = [];
  pr_timelimit = 3;
  pr_cpufactor = 1;
  pr_quorum    = 1;
  pr_verbose   = 0;
  pr_all       = false;
  pr_iterate   = false;
  pr_max       = 50;
  pr_wanted    = Hints.empty;
  pr_unwanted  = Hints.empty;
  pr_selected  = false;
}

let dft_prover_names = ["Z3"; "CVC4"; "Alt-Ergo"; "Eprover"; "Yices"]

(* -------------------------------------------------------------------- *)
type notify = EcGState.loglevel -> string Lazy.t -> unit

let rec run_prover
  ?(notify : notify option) (pi : prover_infos) (prover : string) task
=
  let sigdef = Sys.signal Sys.sigint Sys.Signal_ignore in

  EcUtils.try_finally (fun () ->
    try
      let { pr_config = pr; pr_driver = dr; } = get_prover prover in
      let pc =
        let command = pr.Whyconf.command in

        let limit = { Call_provers.empty_limit with
          Call_provers.limit_time =
            let limit = pi.pr_timelimit * pi.pr_cpufactor in
            if limit <= 0 then 0 else limit;
        } in

        let rec doit gcdone =
          try  Driver.prove_task ~command ~limit dr task
          with Unix.Unix_error (Unix.ENOMEM, "fork", _) when not gcdone ->
            Gc.compact (); doit true
        in

        if EcUtils.is_some (Os.getenv "EC_SMT_DEBUG") then begin
          let stream = open_out (Printf.sprintf "%s.smt" prover) in
          let fmt = Format.formatter_of_out_channel stream in
          EcUtils.try_finally
            (fun () -> Format.fprintf fmt "%a@." (Driver.print_task dr) task)
            (fun () -> close_out stream)
        end;

        doit false

      in
        Some (prover, pc)

    with e ->
      notify |> oiter (fun notify -> notify `Warning (lazy (
        let buf = Buffer.create 0 in
        let fmt = Format.formatter_of_buffer buf in
        Format.fprintf fmt "error when starting `%s': %a%!"
          prover EcPException.exn_printer e;
        Buffer.contents buf)));
      None)

  (fun () ->
     let _ : Sys.signal_behavior = Sys.signal Sys.sigint sigdef in ())

(* -------------------------------------------------------------------- *)
let execute_task ?(notify : notify option) (pi : prover_infos) task =
  let module CP = Call_provers in

  Prove_client.set_max_running_provers pi.pr_maxprocs;

  let pcs = Array.make pi.pr_maxprocs None in

  (* Run process, ignoring prover failing to start *)
  let run i prover =
      run_prover ?notify pi prover task
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
      let status = ref 0 in
      let alives = ref (Array.count is_some pcs) in

      while (   (!alives <> 0 || not (Queue.is_empty pqueue))
             && (0 <= !status && !status < pi.pr_quorum)) do

        if not (Queue.is_empty pqueue) && !alives < Array.length pcs then begin
          for i = 0 to (Array.length pcs) - 1 do
            if is_none pcs.(i) && not (Queue.is_empty pqueue) then begin
              run i (Queue.take pqueue)
            end
          done
        end;

        let infos = CP.get_new_results ~blocking:true in

        alives := 0;

        for i = 0 to (Array.length pcs) - 1 do
          match pcs.(i) with
          | None -> ()
          | Some (prover, pc) ->
              let myinfos = List.pmap
                (fun (pc', upd) -> if pc = pc' then Some upd else None)
                infos in

              let handle_answer = function
                | CP.Valid   -> incr status
                | CP.Invalid -> status := (-1)
                | (CP.Failure _ | CP.HighFailure) as answer->
                  notify |> oiter (fun notify -> notify `Warning (lazy (
                    let buf = Buffer.create 0 in
                    let fmt = Format.formatter_of_buffer buf in
                    Format.fprintf fmt "prover %s exited with %a%!"
                      prover CP.print_prover_answer answer;
                    Buffer.contents buf)));
                | _ ->
                    ()
              in

              let rec handle_info upd =
                match upd with
                | CP.NoUpdates
                | CP.ProverStarted ->
                    ()

                | CP.ProverInterrupted
                | CP.InternalFailure _ ->
                    pcs.(i) <- None

                | CP.ProverFinished answer ->
                    pcs.(i) <- None;
                    handle_answer answer.CP.pr_answer
              in

              let rec handle_infos myinfos =
                match myinfos with
                | [] -> ()
                | myinfo :: myinfos ->
                    handle_info myinfo;
                    if is_some pcs.(i) then handle_infos myinfos in

              handle_infos myinfos;
              if pcs.(i) <> None then incr alives
        done
      done;

           if !status < 0 then Some false
      else if !status = 0 then None
      else if !status < pi.pr_quorum then None else Some true)

    (* Clean-up: hard kill + wait for remaining provers *)
    (fun () ->
      for i = 0 to (Array.length pcs) - 1 do
        match pcs.(i) with
        | None -> ()
        | Some (_prover, pc) ->
            CP.interrupt_call pc;
            (try ignore (CP.wait_on_call pc : CP.prover_result) with _ -> ());
      done)
