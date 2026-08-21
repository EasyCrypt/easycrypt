(* -------------------------------------------------------------------- *)
(* The LLM coding-agent REPL. See [ecLlm.mli] for the entry point.

   This is the text front-end only: line parsing, the OK/ERROR/<END>
   envelope, the multi-line block buffer, QUIET, HELP and the -eval
   driver. Everything engine-facing lives in [EcLlmCore], which the
   MCP front-end shares. *)

open EcUtils

(* -------------------------------------------------------------------- *)
(* Path to the bundled LLM-agent guide. *)
let llm_guide_path () =
  let (module Sites) = EcRelocate.sites in
  match EcRelocate.sourceroot with
  | Some root ->
    Filename.concat (Filename.concat root "doc/llm") "CLAUDE.md"
  | None ->
    Filename.concat Sites.doc "llm-guide.md"

(* Print the bundled guide to stdout. Used by [-help]. *)
let print_llm_guide () =
  let path = llm_guide_path () in
  try
    let ic = open_in path in
    begin try while true do
      print_char (input_char ic)
    done with End_of_file -> () end;
    close_in ic
  with Sys_error e ->
    Printf.eprintf "cannot read LLM guide: %s\n%!" e

(* -------------------------------------------------------------------- *)
(* Surface command vocabulary. Parsing turns each stdin line into one
   of these, and dispatch is a flat pattern-match. Argument
   parsing/validation lives here; commands that interact with mutable
   session state (checkpoints table) carry only the raw user-supplied
   data and let [EcLlmCore] do the lookup. *)
module Parse = struct
  type command =
    | Quit
    | Help
    | Undo
    | Goals      of [`One | `All]
    | Tree       of [`One | `All]
    | Commit
    | Focus      of int list  (* dotted path; [k] = "FOCUS k" *)
    | Next
    | Checkpoint of string
    | Revert     of string   (* uuid-or-name; the core resolves *)
    | Quiet      of bool
    | Search     of string   (* trailing "." already stripped *)
    | Load       of load     (* parsed LOAD arguments *)
    | Ec         of string   (* fall-through: raw EasyCrypt input *)
    | Begin_multi
    | Done_multi
    | Multi_line of string
    | Blank

  and load = {
    ld_file  : string;
    ld_upto  : (int * int option) option;
    ld_nosmt : bool;
    ld_trace : bool;
  }

  exception Parse_error of string

  (* Match [kw] as a prefix: succeeds on exactly [kw] (no argument)
     or [kw ^ " " ^ ...] (with argument), returning the stripped
     argument tail. Returns [None] otherwise. This recognises both
     "CHECKPOINT" and "CHECKPOINT foo" the same way, so we can
     diagnose the missing-name case ourselves instead of falling
     through to EC's parser. *)
  let keyword_arg kw line =
    if line = kw then Some ""
    else if String.starts_with line (kw ^ " ") then
      let n = String.length kw + 1 in
      Some (String.strip
        (String.sub line n (String.length line - n)))
    else None

  let parse_focus arg =
    if arg = "" then
      raise (Parse_error "FOCUS: missing argument");
    let parts = String.split_on_char '.' arg in
    let path =
      try List.map int_of_string parts
      with Failure _ ->
        raise (Parse_error
          (Printf.sprintf "FOCUS: not a path of integers: %s" arg))
    in
    if List.exists (fun k -> k < 1) path then
      raise (Parse_error
        (Printf.sprintf "FOCUS: path indices must be >= 1: %s" arg));
    Focus path

  let parse_checkpoint name =
    if name = "" then
      raise (Parse_error "CHECKPOINT: missing name");
    Checkpoint name

  let parse_revert spec =
    if spec = "" then
      raise (Parse_error
        "REVERT: missing uuid or checkpoint name");
    Revert spec

  let parse_search query =
    if query = "" then
      raise (Parse_error "SEARCH: missing query");
    let query =
      if String.ends_with query "."
      then String.sub query 0 (String.length query - 1)
      else query
    in
    Search query

  (* LOAD "file.ec" [LINE[:COL]] [-nosmt] [-trace]. Argument errors are
     signalled with [failwith] and turned into [Parse_error] below, so
     they reach the wire exactly as any other line-parse error does
     (including the bare "int_of_string" of a malformed LINE:COL). *)
  let parse_load args =
    try
      let args = String.strip args in
      if args = "" then failwith "LOAD: missing filename";
      (* Parse quoted or unquoted filename. *)
      let filename, rest =
        if args.[0] = '"' then
          let close =
            try String.index_from args 1 '"'
            with Not_found ->
              failwith "LOAD: unterminated filename"
          in
          let fn = String.sub args 1 (close - 1) in
          let rest = String.strip (
            String.sub args (close + 1)
              (String.length args - close - 1)) in
          (fn, rest)
        else
          match String.split_on_char ' ' args with
          | [] -> failwith "LOAD: missing filename"
          | [f] -> (f, "")
          | f :: rest -> (f, String.concat " " rest)
      in
      if filename = "" then failwith "LOAD: missing filename";
      (* Checked here, before anything else touches the session: the
         reader would otherwise raise [Sys_error] far downstream, and
         the REPL would report it as an anomaly after having already
         reset the scope. *)
      if not (Sys.file_exists filename) then
        failwith
          (Printf.sprintf "LOAD: no such file: %s" filename);

      (* Parse optional LINE[:COL] and flags (-nosmt, -trace). *)
      let upto, nosmt, trace =
        let words =
          String.split_on_char ' ' rest
            |> List.filter (fun s -> s <> "")
        in
        let nosmt = List.mem "-nosmt" words in
        let trace = List.mem "-trace" words in
        let words =
          List.filter
            (fun s -> s <> "-nosmt" && s <> "-trace")
            words
        in
        let upto = match words with
          | [] -> None
          | [w] ->
            begin match String.split_on_char ':' w with
            | [line] ->
              Some (int_of_string line, None)
            | [line; col] ->
              Some (int_of_string line, Some (int_of_string col))
            | _ -> failwith "LOAD: invalid LINE[:COL] format"
            end
          | _ -> failwith "LOAD: unexpected arguments"
        in
        (upto, nosmt, trace)
      in
      Load { ld_file = filename; ld_upto = upto;
             ld_nosmt = nosmt; ld_trace = trace; }
    with Failure msg -> raise (Parse_error msg)

  let of_line ~multi_active (raw : string) : command =
    let line = String.strip raw in
    if multi_active then
      if line = "<DONE>" then Done_multi
      else Multi_line line
    else
      match line with
      | "<BEGIN>"   -> Begin_multi
      | ""          -> Blank
      | "QUIT"      -> Quit
      | "HELP"      -> Help
      | "UNDO"      -> Undo
      | "GOALS"     -> Goals `One
      | "GOALS ALL" -> Goals `All
      | "TREE"      -> Tree `One
      | "TREE ALL"  -> Tree `All
      | "COMMIT"    -> Commit
      | "NEXT"      -> Next
      | "QUIET ON"  -> Quiet true
      | "QUIET OFF" -> Quiet false
      | _ ->
        match keyword_arg "FOCUS"      line with Some a -> parse_focus      a | None ->
        match keyword_arg "CHECKPOINT" line with Some a -> parse_checkpoint a | None ->
        match keyword_arg "REVERT"     line with Some a -> parse_revert     a | None ->
        match keyword_arg "SEARCH"     line with Some a -> parse_search     a | None ->
        match keyword_arg "LOAD"       line with Some a -> parse_load       a | None ->
        Ec line
end

(* -------------------------------------------------------------------- *)
let run ~relocdir ~boot ~projini (llmopts : EcOptions.llm_option) =
  if llmopts.llmo_help then begin
    print_llm_guide ();
    exit 0
  end;

  let prvopts = llmopts.llmo_provers in

  let st =
    try EcLlmCore.create ~relocdir ~boot ~projini ~prvopts
    with EcLlmCore.Init_error msg ->
      Format.eprintf "%s" msg;
      exit 1
  in

  (* True iff replies should suppress goal bodies. Toggled by QUIET. *)
  let quiet = ref false in

  (* ------------------------------------------------------------------ *)
  (* OK/ERROR/<END> wire envelope: the only printers. *)
  let had_error = ref false in

  let module Wire = struct
    let reply_ok (r : EcLlmCore.reply) =
      let body =
        match r.EcLlmCore.body with
        | EcLlmCore.Text body -> body
        | EcLlmCore.Goals ->
          if !quiet then "" else EcLlmCore.current_goals st
      in
      Printf.printf "OK [uuid:%d]%s\n" r.EcLlmCore.uuid r.EcLlmCore.tag;
      let n = r.EcLlmCore.notices in
      if n <> "" then print_string n;
      if body <> "" then begin
        print_string body;
        let len = String.length body in
        if len > 0 && body.[len - 1] <> '\n' then
          print_char '\n'
      end;
      Printf.printf "<END>\n%!"

    let reply_failure (f : EcLlmCore.failure) =
      had_error := true;
      let goals = f.EcLlmCore.goals in
      Printf.printf "ERROR [uuid:%d]\n%s\n"
        f.EcLlmCore.uuid f.EcLlmCore.message;
      if goals <> "" then begin
        print_string goals;
        let len = String.length goals in
        if len > 0 && goals.[len - 1] <> '\n' then
          print_char '\n'
      end;
      Printf.printf "<END>\n%!"

    (* Render an operation's outcome. *)
    let reply = function
      | Ok reply     -> reply_ok reply
      | Error failed -> reply_failure failed

    (* Same, for operations that may end the session. *)
    let answer = function
      | EcLlmCore.Quit      -> exit 0
      | EcLlmCore.Done outcome -> reply outcome

    let reply_error msg =
      reply_failure (EcLlmCore.make_failure st msg)
  end in

  (* ------------------------------------------------------------------ *)
  (* Command handlers. Each takes (already-parsed) data and produces a
     wire reply via [Wire] (or exits the process). Multi-line state is
     held here so [Parse] can stay pure. *)
  let multi_buf = Buffer.create 256 in
  let in_multi  = ref false in

  let module Dispatch = struct
    let do_help () =
      EcLlmCore.clear_notices st;
      let buf = Buffer.create 4096 in
      let path = llm_guide_path () in
      begin try
        let ic = open_in path in
        begin try while true do
          Buffer.add_char buf (input_char ic)
        done with End_of_file -> () end;
        close_in ic;
        Wire.reply_ok
          (EcLlmCore.make_reply st (EcLlmCore.Text (Buffer.contents buf)))
      with Sys_error e ->
        Wire.reply_error (Printf.sprintf "cannot read guide: %s" e)
      end

    let do_quiet on =
      EcLlmCore.clear_notices st;
      quiet := on;
      Wire.reply_ok (EcLlmCore.make_reply st (EcLlmCore.Text ""))

    let do_begin_multi () =
      Buffer.clear multi_buf;
      in_multi := true

    let do_done_multi () =
      let input = Buffer.contents multi_buf in
      Buffer.clear multi_buf;
      in_multi := false;
      if input <> "" then Wire.answer (EcLlmCore.step st input)

    let do_multi_line s =
      if Buffer.length multi_buf > 0 then
        Buffer.add_char multi_buf ' ';
      Buffer.add_string multi_buf s

    let run (cmd : Parse.command) =
      match cmd with
      | Blank        -> ()
      | Quit         -> exit 0
      | Help         -> do_help ()
      | Undo         -> Wire.reply (EcLlmCore.undo st)
      | Goals `One   -> Wire.reply (EcLlmCore.goals st ~all:false)
      | Goals `All   -> Wire.reply (EcLlmCore.goals st ~all:true)
      | Tree `One    -> Wire.reply (EcLlmCore.tree st ~all:false)
      | Tree `All    -> Wire.reply (EcLlmCore.tree st ~all:true)
      | Commit       -> Wire.reply (EcLlmCore.commit st)
      | Focus path   -> Wire.reply (EcLlmCore.focus st (`Path path))
      | Next         -> Wire.reply (EcLlmCore.focus st `Next)
      | Checkpoint n -> Wire.reply (EcLlmCore.checkpoint st ~name:n)
      | Revert s     -> Wire.reply (EcLlmCore.revert st s)
      | Quiet on     -> do_quiet on
      | Search q     -> Wire.reply (EcLlmCore.search st ~pattern:q)
      | Load args    ->
        Wire.reply (EcLlmCore.load st
          ~file:args.Parse.ld_file
          ~upto:args.Parse.ld_upto
          ~nosmt:args.Parse.ld_nosmt
          ~trace:args.Parse.ld_trace)
      | Ec input     -> Wire.answer (EcLlmCore.step st input)
      | Begin_multi  -> do_begin_multi ()
      | Done_multi   -> do_done_multi ()
      | Multi_line s -> do_multi_line s
  end in

  (* ------------------------------------------------------------------ *)
  (* Main loop. *)

  Printf.printf "READY [uuid:%d]\n<END>\n%!" (EcLlmCore.uuid st);

  (* Input source: stdin by default, or the -eval string when given.
     For -eval, we split on newlines up front (no lazy channel), which
     keeps the driver simple and avoids ever touching stdin. *)
  let read_line : unit -> string =
    match llmopts.llmo_eval with
    | None ->
      fun () -> input_line stdin
    | Some script ->
      let lines = ref (String.split_on_char '\n' script) in
      fun () ->
        match !lines with
        | []      -> raise End_of_file
        | l :: tl -> lines := tl; l
  in

  begin try while true do
    let line = read_line () in
    (try
       let cmd = Parse.of_line ~multi_active:!in_multi line in
       Dispatch.run cmd
     with Parse.Parse_error msg ->
       Wire.reply_error msg)
  done with
  | End_of_file -> ()
  end;

  (* Scripted runs (-eval) report in-band errors through the exit
     status, so that automation does not mistake an ERROR reply for
     success. Interactive sessions keep exiting 0. *)
  exit (if llmopts.llmo_eval <> None && !had_error then 1 else 0)
