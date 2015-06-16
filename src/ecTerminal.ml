(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils

module L  = Lexing
module LC = EcLocation

(* -------------------------------------------------------------------- *)
type status =[
  | `ST_Ok
  | `ST_Failure of exn
]

type loglevel = EcGState.loglevel

class type terminal =
object
  method interactive : bool
  method next        : EcParsetree.prog
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
      | `Debug | `Warning | `Critical -> "[W]"
      | `Info -> ""
    in
      List.iter
        (fun x -> Printf.printf "%s%s\n%!" prefix x)
        (String.split_lines msg)

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
          | EcScope.TopError (loc, e) -> (loc, e)
          | _ -> (LC._dummy, e)
        in
          Format.fprintf Format.err_formatter
            "[error-%d-%d]%s\n%!"
            (max 0 (loc.LC.loc_bchar - startpos))
            (max 0 (loc.LC.loc_echar - startpos))
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
      (String.split_lines msg)

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
class from_channel ~name (stream : in_channel) : terminal =
object(self)
  val ticks = "-\\|/"

  val (*---*) iparser = EcIo.from_channel ~name stream
  val mutable sz    = -1
  val mutable tick  = -1
  val mutable loc   = LC._dummy
  val mutable doprg =
    (Sys.os_type = "Unix") &&
    (Unix.isatty (Unix.descr_of_out_channel stdout))


  method private _update_progress =
    let lineno   = fst (loc.LC.loc_end) in
    let position = loc.LC.loc_echar in

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
      Printf.eprintf "[%c] [%.4d] %.1f %% (%.1f%s / [frag %.1f%s])\r%!"
        ticks.[tick] lineno
        (100. *. ((float_of_int position) /. (float_of_int sz)))
        mem memst unu unust
    end

  method private _clear_update ?(erase = true) ~final () =
    if erase then begin
      let fmt = "[*] [----] ---.- (------.-?B% - [---- ------.-?B%])" in
        if sz >= 0 && doprg then
          Printf.eprintf "%*s\r%!" (String.length fmt) ""
    end else Printf.eprintf "\n%!";
    doprg <- not final

  method private _notice ?subloc ~immediate (lvl : loglevel) (msg : string) =
    let (_ : unit) = ignore immediate in

    if EcGState.accept_log ~level:`Warning ~wanted:lvl then
      let prefix = EcGState.string_of_loglevel lvl in
      let strloc =
        match subloc with
        | None -> Printf.sprintf "%s:%d" name (fst (loc.LC.loc_end))
        | Some loc -> LC.tostring loc
      in
        self#_clear_update ~final:false ();
        Printf.eprintf "[%.8s] [%s] %s\n%!" prefix strloc msg;
        self#_update_progress

  method interactive = false

  method next =
    let aout = EcIo.parse iparser in
    loc <- aout.LC.pl_loc;
    self#_update_progress; aout

  method notice ~immediate lvl msg =
    self#_notice ~immediate lvl msg

  method finish (status : status) =
    match status with
    | `ST_Ok -> ()

    | `ST_Failure e -> begin
        let (subloc, e) =
          match e with
          | EcScope.TopError (loc, e) -> (Some loc, e)
          | _ -> (None, e) in
        let msg = String.strip (EcPException.tostring e) in

        self#_clear_update ~final:false ();
        self#_notice ?subloc ~immediate:true `Critical msg;
        self#_update_progress;
        self#_clear_update ~erase:false ~final:true ()
      end

  method finalize =
    self#_clear_update ~final:true ();
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
