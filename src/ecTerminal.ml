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
  method setwidth    : int -> unit
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

let setwidth (t : terminal) (i : int) =
  t#setwidth i

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
      List.iteri
        (fun i x ->
          Format.printf "%s%s%s\n%!"
          prefix (if i = 0 then "+ " else "| ") x)
        (String.split_lines msg)

  method next =
    begin
      let lexbuf = EcIo.lexbuf iparser in
        EcIo.drain iparser;
        startpos <- lexbuf.L.lex_curr_p.L.pos_cnum
    end;

    Format.printf "[%d|%s]>\n%!" (EcCommands.uuid ()) (EcCommands.mode ());
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

  method setwidth (i : int) =
    Format.pp_set_margin Format.std_formatter i;
    Format.pp_set_margin Format.err_formatter i
end

let from_emacs () = new from_emacs ()

(* -------------------------------------------------------------------- *)
class from_tty () : terminal =
object
  val iparser = EcIo.from_channel ~name:"<tty>" stdin

  method interactive = true

  method next =
    Format.printf "[%d|%s]>\n%!" (EcCommands.uuid ()) (EcCommands.mode ());
    EcIo.drain iparser;
    EcIo.parse iparser

  method notice ~(immediate:bool) (_ : loglevel) (msg : string) =
    ignore immediate;
    List.iter
      (fun x -> Format.eprintf "%s\n%!" x)
      (String.split_lines msg)

  method finish (status : status) =
    match status with
    | `ST_Ok ->
        EcCommands.pp_maybe_current_goal Format.std_formatter

    | `ST_Failure e ->
        EcPException.exn_printer Format.err_formatter e

  method finalize =
    EcIo.finalize iparser

  method setwidth (i : int) =
    Format.pp_set_margin Format.std_formatter i;
    Format.pp_set_margin Format.err_formatter i
end

let from_tty () = new from_tty ()

(* -------------------------------------------------------------------- *)
type progress = [ `Human | `Script | `Silent ]

class from_channel
  ?(gcstats  : bool = true)
  ?(progress : progress option)
  ~(name     : string)
   (stream   : in_channel)
  : terminal

= object(self)
  val ticks = "-\\|/"

  val (*---*) iparser = EcIo.from_channel ~name stream
  val mutable sz       = -1
  val mutable tick     = -1
  val mutable loc      = LC._dummy
  val mutable gc       = None
  val mutable progress =
    progress |> ofdfl (fun () ->
      if
        (Sys.os_type = "Unix") &&
        (Unix.isatty (Unix.descr_of_out_channel stderr))
      then `Human else `Silent)

  method private _do_update_progress =
    match progress with
    | (`Human | `Script) as progress -> begin
        let lineno   = fst (loc.LC.loc_end) in
        let position = loc.LC.loc_echar in
        let ratio    =
          match sz with
          | _ when sz < 0 -> None
          | _ when sz = 0 -> Some 1.0
          | _ -> Some ((float_of_int position) /. (float_of_int sz)) in

        let mem, unu =
          if not gcstats then -1., -1. else
          match gc with
          | Some (mem, unu, btick) when btick > tick-20 ->
             (mem, unu)
          | _ ->
             let mem = (Gc.stat ()).Gc.live_words in
             let mem = (float_of_int mem) *. (float_of_int (Sys.word_size / 8)) in
             let unu = (Gc.stat ()).Gc.fragments  in
             let unu = (float_of_int unu) *. (float_of_int (Sys.word_size / 8)) in
             gc <- Some (mem, unu, tick); (mem, unu)
        in

        tick <- tick + 1;

        match progress with
        | `Human -> begin
            let rec human x st all =
              match all with
              | [] -> (x, st)
              | _ when x < 1024.-> (x, st)
              | st' :: all -> human (x /. 1024.) st' all in

            let mem, memst = human mem "B" ["kB"; "MB"; "GB"] in
            let unu, unust = human unu "B" ["kB"; "MB"; "GB"] in
            let ratio = ratio
               |> omap (( *. ) 100.)
               |> omap (Format.sprintf "%.1f")
               |> odfl "?.?" in

            Format.eprintf "[%c] [%.4d] %s%% (%.1f%s / [frag %.1f%s])\r%!"
              ticks.[tick mod (String.length ticks)] lineno
              ratio mem memst unu unust
          end

        | `Script -> begin
            let lineno   = fst (loc.LC.loc_end) in
            let position = loc.LC.loc_echar in
            let ratio    =
              ratio
              |> omap (fun x -> Format.sprintf "%.5f" x)
              |> odfl "-" in

            Format.eprintf
              "P %d %d %s %.2f %.2f@."
              lineno position ratio mem unu
          end
      end

    | _ -> ()

  method private _update_progress =
    if loc !=(*phy*) LC._dummy then
      self#_do_update_progress

  method private _clean_progress_line ?(erase = true) () =
    match progress with
    | `Human when erase ->
       if sz >= 0 then
         let fmt = "[*] [----] ---.- (------.-?B% - [---- ------.-?B%])" in
         Format.eprintf "%*s\r%!" (String.length fmt) ""

    | `Human ->
       Format.eprintf "\n%!"

    | `Script | `Silent ->
       ()

  method private _notice ?subloc ~immediate (lvl : loglevel) (msg : string) =
    let (_ : unit) = ignore immediate in

    if EcGState.accept_log ~level:`Warning ~wanted:lvl then
      let prefix = EcGState.string_of_loglevel lvl in
      let strloc =
        match subloc with
        | None -> Format.sprintf "%s:%d" name (fst (loc.LC.loc_end))
        | Some loc -> LC.tostring loc
      in
        self#_clean_progress_line ();
        begin match progress with
        | `Human ->
           Format.eprintf "[%s] [%s] %s\n%!" prefix strloc msg;
        | `Script ->
           Format.eprintf "E %s %s %s\n%!" prefix strloc (String.escaped msg)
        | `Silent ->
           ()
        end;
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

        self#_clean_progress_line ();
        self#_notice ?subloc ~immediate:true `Critical msg;
        self#_update_progress;
        self#_clean_progress_line ~erase:false ();
        progress <- `Silent
      end

  method finalize =
    self#_clean_progress_line ();
    progress <- `Silent;
    EcIo.finalize iparser

  initializer begin
    try
      let fd   = Unix.descr_of_in_channel stream in
      let stat = Unix.fstat fd in
      sz <- stat.Unix.st_size
    with Unix.Unix_error _ -> ()
  end

  method setwidth (i : int) =
    Format.pp_set_margin Format.std_formatter i;
    Format.pp_set_margin Format.err_formatter i
end

let from_channel ?gcstats ?progress ~name stream =
  new from_channel ?gcstats ?progress ~name stream
