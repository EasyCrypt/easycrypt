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
    let parts = [v.v_major; v.v_minor; v.v_subminor] in
    let parts = List.map string_of_int parts in
    let parts =
      let extra = if String.is_empty v.v_extra then None else Some v.v_extra in
      ofold (fun extra parts -> parts @ [extra]) parts extra in

    String.concat "." parts
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
        let cmp = VP.compare version tversion in
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
  pr_version : Version.version;
  pr_alt     : string;
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
  val config   : unit -> Whyconf.config
  val main     : unit -> Whyconf.main
  val known    : evicted:bool -> prover list
end = struct
  let theconfig  : (Whyconf.config option) ref = ref None
  let themain    : (Whyconf.main   option) ref = ref None
  let thew3_env  : (Env.env        option) ref = ref None
  let theprovers : (why3prover     list  ) ref = ref []

  let load ?(ovrevict = []) ?why3conf () =
    if !theconfig = None then begin
      let config  = Whyconf.init_config why3conf in
      let main    = Whyconf.get_main config in

      Whyconf.load_plugins main;

      let w3_env  = Env.create_env (Whyconf.loadpath main) in

      let load_prover p config =
        let name    = p.Whyconf.prover_name in
        let version = p.Whyconf.prover_version in
        let driver  = Driver.load_driver_for_prover main w3_env config in

        { pr_prover  =
            { pr_name    = name;
              pr_version = Version.parse version;
              pr_alt     = p.Whyconf.prover_altern;
              pr_evicted = None; };
          pr_config  = config;
          pr_driver  = driver; }
      in

      let provers =
        Whyconf.Mprover.fold
          (fun p c acc -> load_prover p c :: acc)
          (Whyconf.get_provers config) [] in

      let provers =
        let key_of_prover (p : why3prover) =
          let p = p.pr_prover in
          (p.pr_name, p.pr_version, p.pr_alt) in

        List.sort
          (fun p1 p2 -> compare (key_of_prover p1) (key_of_prover p2))
          provers in

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

  let config () =
    load (); EcUtils.oget !theconfig

  let main () =
    load (); EcUtils.oget !themain

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
  prn_alt      : string;
  prn_version  : Version.version option;
  prn_ovrevict : bool;
}

let parse_prover_name name =
  let name, version =
    if String.contains name '@' then
      let index   = String.index name '@' in
      let name    = String.sub name 0 index
      and version = String.sub name (index+1) (String.length name - (index+1)) in
      (name, Some version)
    else
      (name, None) in

  let version = omap Version.parse version in

  let ovrevict, name =
      if name <> "" && name.[0] = '!' then
        true, String.sub name 1 (String.length name - 1)
      else false, name in

  let name, alt =
    let re = EcRegexp.regexp "^(.*)\\[(.*)\\]$" in
    match EcRegexp.exec (`C re) name with
    | None ->
      name, ""
    | Some m ->
      let name = oget (EcRegexp.Match.group m 1) in
      let alt  = oget (EcRegexp.Match.group m 2) in
      name, alt in

  { prn_name     = name;
    prn_version  = version;
    prn_alt      = alt;
    prn_ovrevict = ovrevict; }

let get_prover (rawname : string) =
  let name = parse_prover_name rawname in

  let test p =
       p.pr_prover.pr_name = name.prn_name
    && p.pr_prover.pr_alt  = name.prn_alt
    && (name.prn_ovrevict || not (is_evicted p.pr_prover)) in

  let provers = List.filter test (Config.provers ()) in

  let provers = List.sort (fun p1 p2 ->
      let v1 = p1.pr_prover.pr_version in
      let v2 = p2.pr_prover.pr_version in
      Version.compare v1 v2
    ) provers
  in

  let exception CannotFindProver in

  try
    match name.prn_version with
    | None ->
        oget ~exn:CannotFindProver (List.Exceptionless.hd (List.rev provers))

    | Some version -> begin
        try
          List.find
            (fun p ->
               Version.compare version p.pr_prover.pr_version <= 0)
          provers

        with Not_found -> raise CannotFindProver
      end

  with CannotFindProver ->
    raise (UnknownProver rawname)

let is_prover_known name =
  try ignore (get_prover name); true with UnknownProver _ -> false

(* -------------------------------------------------------------------- *)

let get_w3_main = Config.main
let get_w3_conf = Config.config
let get_w3_env = Config.w3_env

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
type coq_mode =
  | Check (* Check scripts *)
  | Edit  (* Edit then check scripts *)
  | Fix   (* Try to check script, then edit script on non-success *)

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
  pr_dumpin    : string EcLocation.located option;
  pr_selected  : bool;
  gn_debug     : bool;
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
  pr_dumpin    = None;
  pr_selected  = false;
  gn_debug     = false;
}

let dft_prover_names = ["Z3"; "CVC4"; "Alt-Ergo"; "Eprover"; "Yices"]

(* -------------------------------------------------------------------- *)
type notify = EcGState.loglevel -> string Lazy.t -> unit

(* -------------------------------------------------------------------- *)
let maybe_start_why3_server_ (pi : prover_infos) =
  if not (Prove_client.is_connected ()) then begin
    let sockname = Filename.temp_file "easycrypt.why3server." ".socket" in
    let exec = Filename.concat (Whyconf.libdir (Config.main ())) "why3server" in
    let pid = ref (-1) in

    begin
      let rd, wr = Unix.pipe ~cloexec:true () in

      EcUtils.try_finally (fun () ->
        pid := Unix.fork ();

        if !pid = 0 then begin
          Unix.close rd;
          EUnix.setpgid 0 0;
          Unix.chdir (Filename.get_temp_dir_name ());
          Unix.execvp exec [|
            exec; "--socket"; sockname; "--single-client";
            "-j"; string_of_int pi.pr_maxprocs
          |]
        end else begin
          Unix.close wr;
          ignore (Unix.select [rd] [] [] (-1.0))
        end)
      (fun () ->
        (try Unix.close rd with Unix.Unix_error _ -> ());
        (try Unix.close wr with Unix.Unix_error _ -> ()))
    end;

    let connected = ref false in

    EcUtils.try_finally (fun () ->
      let n, d = ref 5, ref 0.1 in

      while 0 < !n && not !connected do
        if Sys.file_exists sockname then begin
          try
            Prove_client.connect_external sockname;
            connected := true
          with Prove_client.ConnectionError _ -> ()
        end;
        if not !connected then begin
          ignore (Unix.select [] [] [] !d);
          n := !n - 1;
          d := 2.0 *. !d
        end
      done)

    (fun () ->
      if not !connected then begin
        try
          Unix.kill !pid Sys.sigkill
        with Unix.Unix_error _ -> ()
      end);

    if not !connected then
      raise (Prove_client.ConnectionError "cannot start & connect to why3server")
  end

(* -------------------------------------------------------------------- *)

let maybe_start_why3_server (pi : prover_infos) =
  let sigdef = Sys.signal Sys.sigint Sys.Signal_ignore in

  EcUtils.try_finally
    (fun () -> maybe_start_why3_server_ pi)
    (fun () -> ignore (Sys.signal Sys.sigint sigdef : Sys.signal_behavior))

(* -------------------------------------------------------------------- *)
let run_prover
  ?(notify : notify option) (pi : prover_infos) (prover : string) task
=
  maybe_start_why3_server pi;

  try
    let { pr_config = pr; pr_driver = dr; } = get_prover prover in

    let pc =
      let command = pr.Whyconf.command in

      let limit = { Call_provers.empty_limit with
        Call_provers.limit_time =
          let limit = pi.pr_timelimit * pi.pr_cpufactor in
          if limit <= 0 then 0. else float_of_int limit;
      } in

      let rec doit gcdone =
        try
          Driver.prove_task
            ~config:(Config.main ())
            ~command ~limit dr task
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
    None

(* -------------------------------------------------------------------- *)
let execute_task ?(notify : notify option) (pi : prover_infos) task =
  let module CP = Call_provers in

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
              let myinfos =
                List.pmap
                  (fun (pc', upd) -> if pc = pc' then Some upd else None)
                  infos in

              let handle_answer = function
                | CP.Valid   ->
                    if pi.gn_debug then begin
                      notify |> oiter (fun notify -> notify `Warning (lazy (
                        let buf = Buffer.create 0 in
                        let fmt = Format.formatter_of_buffer buf in
                        Format.fprintf fmt "success: %s%!" prover;
                      Buffer.contents buf)))
                    end;
                    if (0 <= !status) then incr status


                | CP.Invalid ->
                    status := (-1);
                    notify |> oiter (fun notify -> notify `Warning (lazy (
                      let buf = Buffer.create 0 in
                      let fmt = Format.formatter_of_buffer buf in
                      Format.fprintf fmt "prover %s disproved this goal." prover;
                    Buffer.contents buf)));
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

              let handle_info upd =
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
            CP.interrupt_call ~config:(Config.main ()) pc;
            (try ignore (CP.wait_on_call pc : CP.prover_result) with _ -> ());
      done)
