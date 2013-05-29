(* -------------------------------------------------------------------- *)
module L = Lexing

(* -------------------------------------------------------------------- *)
type status =[
  | `ST_Ok
  | `ST_Failure of exn
]

class type terminal =
object
  method interactive : bool
  method next        : EcParsetree.prog
  method notice      : immediate:bool -> string -> unit
  method finish      : status -> unit
  method finalize    : unit
end

(* -------------------------------------------------------------------- *)
let interactive (t : terminal) =
  t#interactive

let next (t : terminal) =
  t#next

let notice ~immediate msg (t : terminal) =
  t#notice ~immediate msg

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

  method private _notice (msg : string) =
    Printf.printf "%s\n%!" msg

  method next =
    begin
      let lexbuf = EcIo.lexbuf iparser in
        EcIo.drain iparser;
        startpos <- lexbuf.L.lex_curr_p.L.pos_cnum
    end;

    Printf.printf "[%d]>\n%!" (EcCommands.uuid ());
    EcIo.parse iparser

  method notice ~(immediate:bool) (msg : string) =
    match immediate with
    | true  -> self#_notice msg
    | false -> notices <- msg :: notices

  method finish (status : status) =
    List.iter self#_notice (List.rev notices);

    match status with
    | `ST_Ok ->
        EcCommands.pp_current_goal Format.std_formatter

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
    Printf.printf "[%d]>\n%!" (EcCommands.uuid ());
    EcIo.drain iparser;
    EcIo.parse iparser

  method notice ~(immediate:bool) (_msg : string) =
    ignore (immediate)

  method finish (status : status) =
    match status with
    | `ST_Ok ->
        EcCommands.pp_current_goal Format.std_formatter

    | `ST_Failure e ->
        EcPException.exn_printer Format.err_formatter e

  method finalize =
    EcIo.finalize iparser
end

let from_tty () = new from_tty ()

(* -------------------------------------------------------------------- *)
class from_channel ~name (stream : in_channel) : terminal =
object
  val iparser = EcIo.from_channel ~name stream

  method interactive = false

  method next =
    EcIo.parse iparser

  method notice ~(immediate:bool) (_msg : string) =
    ignore (immediate)

  method finish (status : status) =
    match status with
    | `ST_Ok -> ()

    | `ST_Failure e -> begin
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
    EcIo.finalize iparser
end

let from_channel ~name stream = new from_channel ~name stream
