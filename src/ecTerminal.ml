(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils

module L = Lexing

(* -------------------------------------------------------------------- *)
type status =[
  | `ST_Ok
  | `ST_Failure of exn
]

type loglevel = EcGState.loglevel

class type terminal =
object
  method interactive : bool
  method next        : EcParsetree.prog EcLocation.located
  method notice      : immediate:bool -> loglevel -> string -> unit
  method finish      : status -> unit
  method finalize    : unit
end

(* -------------------------------------------------------------------- *)
let interactive (t : terminal) =
  t#interactive

let next (t : terminal) =
  t#next

let notice ~immediate lvl msg (t : terminal) =
  t#notice ~immediate lvl msg

let finish status (t : terminal) =
  t#finish status

let finalize (t : terminal) =
  t#finalize

(* -------------------------------------------------------------------- *)
class from_emacs () : terminal =
object(self)
  val mutable startpos = 0
  val mutable notices  = []
  val (*---*) iparser  = EcIo.from_channel ~name:"<emacs>" stdin

  method interactive = true

  method private _notice (lvl, msg) =
    let prefix =
      match lvl with
      | `Debug | `Warning -> "[W]"
      | `Info -> ""
    in
      List.iter
        (fun x -> Printf.printf "%s%s\n%!" prefix x)
        (String.splitlines msg)

  method next =
    begin
      let lexbuf = EcIo.lexbuf iparser in
        EcIo.drain iparser;
        startpos <- lexbuf.L.lex_curr_p.L.pos_cnum
    end;

    Printf.printf "[%d|%s]>\n%!" (EcCommands.uuid ()) (EcCommands.mode ());
    EcIo.parse iparser

  method notice ~(immediate:bool) (lvl : loglevel) (msg : string) =
    match immediate with
    | true  -> self#_notice (lvl, msg)
    | false -> notices <- (lvl, msg) :: notices

  method finish (status : status) =
    List.iter self#_notice (List.rev notices);

    match status with
    | `ST_Ok ->
        EcCommands.pp_maybe_current_goal Format.std_formatter

    | `ST_Failure e ->
        let (loc, e) =
          match e with
          | EcCommands.TopError (loc, e) -> (loc, e)
          | _ -> (EcLocation._dummy, e)
        in
          Format.fprintf Format.err_formatter
            "[error-%d-%d]%s\n%!"
            (max 0 (loc.EcLocation.loc_bchar - startpos))
            (max 0 (loc.EcLocation.loc_echar - startpos))
            (EcPException.tostring e)

  method finalize =
    EcIo.finalize iparser
end

let from_emacs () = new from_emacs ()

(* -------------------------------------------------------------------- *)
class from_tty () : terminal =
object
  val iparser  = EcIo.from_channel ~name:"<tty>" stdin

  method interactive = true

  method next =
    Printf.printf "[%d|%s]>\n%!" (EcCommands.uuid ()) (EcCommands.mode ());
    EcIo.drain iparser;
    EcIo.parse iparser

  method notice ~(immediate:bool) (_ : loglevel) (msg : string) =
    ignore immediate;
    List.iter
      (fun x -> Printf.fprintf stderr "%s\n%!" x)
      (String.splitlines msg)

  method finish (status : status) =
    match status with
    | `ST_Ok ->
        EcCommands.pp_maybe_current_goal Format.std_formatter

    | `ST_Failure e ->
        EcPException.exn_printer Format.err_formatter e

  method finalize =
    EcIo.finalize iparser
end

let from_tty () = new from_tty ()

(* -------------------------------------------------------------------- *)
class from_webui () : terminal =
object(self)
  val mutable startpos = 0
  val (*---*) iparser  = EcIo.from_channel ~name:"<webui>" stdin

  method private _print_raw s =
    assert (String.length s < 16777216);
    Printf.printf "%08d%s%!" (String.length s) s

  method interactive =
    true

  method next =
    begin
      let lexbuf = EcIo.lexbuf iparser in
        EcIo.drain iparser;
        startpos <- lexbuf.L.lex_curr_p.L.pos_cnum
    end;

    let prompt =
      Yojson.Safe.to_string ~std:true
        (`Assoc [ ("type", `String "step");
                  ("step", `Int (EcCommands.uuid ()));
                  ("mode", `String (EcCommands.mode ())) ]);
    in
      self#_print_raw prompt;
      EcIo.parse iparser

  method notice ~(immediate:bool) (_ : loglevel) (msg : string) =
    ignore immediate;
    let msg =
      Yojson.Safe.to_string ~std:true
        (`Assoc [ ("type" , `String "notice");
                  ("value", `String (String.strip msg)) ]);
    in self#_print_raw msg

  method finish (status : status) =
    match status with
    | `ST_Ok ->
        EcCommands.pp_maybe_current_goal Format.str_formatter;
        let proof_info = (Format.flush_str_formatter ()) in
          if String.length proof_info > 0 then
            let msg =
              Yojson.Safe.to_string ~std:true
                (`Assoc [ ("type" , `String "proof");
                          ("value", `String proof_info) ])
            in self#_print_raw msg

    | `ST_Failure e ->
        let (loc, e) =
          match e with
          | EcCommands.TopError (loc, e) -> (loc, e)
          | _ -> (EcLocation._dummy, e)
        in

        let msg =
          Yojson.Safe.to_string ~std:true
            (`Assoc [ ("type" , `String "error");
                      ("value", `String (EcPException.tostring e));
                      ("start", `Int (max 0 (loc.EcLocation.loc_bchar - startpos)));
                      ("stop" , `Int (max 0 (loc.EcLocation.loc_echar - startpos))) ])
        in self#_print_raw msg

  method finalize =
    EcIo.finalize iparser
end

let from_webui () = new from_webui ()

(* -------------------------------------------------------------------- *)
class from_channel ~name (stream : in_channel) : terminal =
object(self)
  val ticks = "-\\|/"

  val (*---*) iparser = EcIo.from_channel ~name stream
  val mutable sz    = -1
  val mutable tick  = -1
  val mutable loc   = EcLocation._dummy
  val mutable doprg =
    (Sys.os_type = "Unix") &&
    (Unix.isatty (Unix.descr_of_out_channel stdout))


  method private _update_progress =
    let lineno   = fst (loc.EcLocation.loc_end) in
    let position = loc.EcLocation.loc_echar in

    let mem = (Gc.stat ()).Gc.live_words in
    let mem = (float_of_int mem) *. (float_of_int (Sys.word_size / 8)) in

    let unu = (Gc.stat ()).Gc.fragments  in
    let unu = (float_of_int unu) *. (float_of_int (Sys.word_size / 8)) in

    let rec human x st all =
      match all with
      | [] -> (x, st)
      | _ when x < 1024.-> (x, st)
      | st' :: all -> human (x /. 1024.) st' all in

    let mem, memst = human mem "B" ["kB"; "MB"; "GB"] in
    let unu, unust = human unu "B" ["kB"; "MB"; "GB"] in

    if sz >= 0 && doprg then begin
      tick <- (tick + 1) mod (String.length ticks);
      Format.eprintf "[%c] [%.4d] %.1f %% (%.1f%s / [frag %.1f%s])\r%!"
        ticks.[tick] lineno
        (100. *. ((float_of_int position) /. (float_of_int sz)))
        mem memst unu unust
    end

  method private _clear_update =
    let fmt = "[*] [----] ---.- (------.-?B% - [---- ------.-?B%])" in
      if sz >= 0 && doprg then
        Format.eprintf "%*s\r%!" (String.length fmt) "";
      doprg <- false

  method interactive = false

  method next =
    let aout = EcIo.parse iparser in
    loc <- aout.EcLocation.pl_loc;
    self#_update_progress; aout

  method notice ~(immediate:bool) (lvl : loglevel) (msg : string) =
    let (_ : unit) = ignore immediate in

    if EcGState.accept_log ~level:`Warning ~wanted:lvl then
      let prefix = EcGState.string_of_loglevel lvl in

      self#_clear_update;
      Printf.printf "[%.7s] [%s:%d] %s\n%!"
        prefix name (fst (loc.EcLocation.loc_end)) msg

  method finish (status : status) =
    match status with
    | `ST_Ok -> ()

    | `ST_Failure e -> begin
        self#_clear_update;
        match e with
        | EcCommands.TopError (loc, e) ->
            Format.eprintf "%s: %a\n%!"
              (EcLocation.tostring loc)
              EcPException.exn_printer e

        | _ ->
            Format.eprintf "%a\n%!"
              EcPException.exn_printer e
      end

  method finalize =
    self#_clear_update;
    EcIo.finalize iparser;

  initializer begin
    try
      let fd   = Unix.descr_of_in_channel stream in
      let stat = Unix.fstat fd in
        sz <- stat.Unix.st_size
    with Unix.Unix_error _ -> ()
  end
end

let from_channel ~name stream = new from_channel ~name stream
