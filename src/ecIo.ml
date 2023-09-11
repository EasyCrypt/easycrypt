(* -------------------------------------------------------------------- *)
open EcUtils

module P = EcParser
module L = Lexing

(* -------------------------------------------------------------------- *)
let parserfun = fun () ->
    MenhirLib.Convert.Simplified.traditional2revised EcParser.prog

type 'a parser_t =
  (P.token * L.position * L.position, 'a) MenhirLib.Convert.revised

(* -------------------------------------------------------------------- *)
let isbinop_fun = fun () ->
    MenhirLib.Convert.Simplified.traditional2revised EcParser.is_binop

let isuniop_fun = fun () ->
    MenhirLib.Convert.Simplified.traditional2revised EcParser.is_uniop

(* -------------------------------------------------------------------- *)
type 'a ecreader_gr = {
  (*---*) ecr_lexbuf  : Lexing.lexbuf;
  (*---*) ecr_parser  : 'a parser_t;
  (*---*) ecr_source  : Buffer.t;
  mutable ecr_tokens  : EcParser.token list;
  mutable ecr_atstart : bool;
}

type 'a ecreader_g = 'a ecreader_gr Disposable.t
type    ecreader   = EcParsetree.prog ecreader_g

(* -------------------------------------------------------------------- *)
let lexbuf (reader : 'a ecreader_g) =
  (Disposable.get reader).ecr_lexbuf

(* -------------------------------------------------------------------- *)
let from_channel ~name channel =
  let buffer = Buffer.create 0 in

  let refill (bytes : bytes) (len : int) =
    let aout = input channel bytes 0 len in
    Buffer.add_bytes buffer (Bytes.sub bytes 0 aout);
    aout
  in

  let lexbuf = Lexing.from_function refill in

  Lexing.set_filename lexbuf name;

  Disposable.create
    { ecr_lexbuf  = lexbuf;
      ecr_parser  = parserfun ();
      ecr_source  = buffer;
      ecr_atstart = true;
      ecr_tokens  = []; }

(* -------------------------------------------------------------------- *)
let from_file filename =
  let channel = open_in filename in

  try
    from_channel ~name:filename channel

  with
    | e ->
        (try close_in channel with _ -> ());
        raise e

(* -------------------------------------------------------------------- *)
let from_string data =
  let lexbuf = Lexing.from_string data in
  let buffer = Buffer.create (String.length data) in

  Buffer.add_string buffer data;

  Disposable.create
    { ecr_lexbuf  = lexbuf;
      ecr_source  = buffer;
      ecr_parser  = parserfun ();
      ecr_atstart = true;
      ecr_tokens  = []; }

(* -------------------------------------------------------------------- *)
let finalize (ecreader : 'a ecreader_g) =
  Disposable.dispose ecreader

(* -------------------------------------------------------------------- *)
let lexer = fun ecreader ->
  let lexbuf = ecreader.ecr_lexbuf in

  let isfinal = function
    | EcParser.FINAL _ -> true
    | _ -> false in

  if ecreader.ecr_tokens = [] then
    ecreader.ecr_tokens <- EcLexer.main lexbuf;

  match ecreader.ecr_tokens with
  | [] ->
      failwith "short-read-from-lexer"

  | token :: queue -> begin
      ecreader.ecr_tokens  <- queue;
      ecreader.ecr_atstart <- (isfinal token);
      (token, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
  end

(* -------------------------------------------------------------------- *)
let drain (ecreader : 'a ecreader_g) =
  let ecreader = Disposable.get ecreader in
  let rec drain () =
    try
      match lexer ecreader with
      | (EcParser.FINAL _, _, _) -> ()
      | _ -> drain ()
    with EcLexer.LexicalError _ -> drain ()
  in
    if not ecreader.ecr_atstart then
      drain ()

(* -------------------------------------------------------------------- *)
let xparse (ecreader : 'a ecreader_g) =
  let ecreader = Disposable.get ecreader in

  let p1 = ecreader.ecr_lexbuf.Lexing.lex_curr_p.pos_cnum in
  let cd = ecreader.ecr_parser (fun () -> lexer ecreader) in
  let p2 = ecreader.ecr_lexbuf.Lexing.lex_curr_p.pos_cnum in

  (Buffer.sub ecreader.ecr_source p1 (p2 - p1), cd)

(* -------------------------------------------------------------------- *)
let parse (ecreader : 'a ecreader_g) =
  snd (xparse ecreader)

(* -------------------------------------------------------------------- *)
let parseall (ecreader : 'a ecreader_g) =
  let rec aux acc =
    match EcLocation.unloc (parse ecreader) with
    | EcParsetree.P_Prog (commands, terminate) ->
        let acc = List.rev_append commands acc in
          if terminate then List.rev acc else aux acc
    | EcParsetree.P_DocComment _ ->
        aux acc
    | EcParsetree.P_Undo _ | EcParsetree.P_Exit ->
        assert false                    (* FIXME *)
  in
    aux []

(* -------------------------------------------------------------------- *)
let lex_single_token name =
  try
    let ecr = from_string name in
    let (token, _, _) = lexer (Disposable.get ecr) in

    match lexer (Disposable.get ecr) with
    | (EcParser.EOF, _, _) -> Some token
    | _ -> None

  with EcLexer.LexicalError _ -> None

(* -------------------------------------------------------------------- *)
let is_sym_ident x =
  match lex_single_token x with
  | Some (EcParser.LIDENT _) -> true
  | Some (EcParser.UIDENT _) -> true
  | _ -> false

let is_op_ident x =
  match lex_single_token x with
  | Some (EcParser.LIDENT _) -> true
  | Some (EcParser.UIDENT _) -> true
  | Some (EcParser.NOP _) -> true
  | _ -> false

let is_mem_ident x =
  match lex_single_token x with
  | Some (EcParser.MIDENT _) -> true
  | _ -> false

let is_mod_ident x =
  match lex_single_token x with
  | Some (EcParser.UIDENT _) -> true
  | _ -> false

(* -------------------------------------------------------------------- *)
type lexer1 = {
  (*---*) l1_lexbuf : Lexing.lexbuf;
  mutable l1_buffer : EcParser.token list;
}

let lexer1_of_lexbuf (lexbuf : Lexing.lexbuf) =
  { l1_lexbuf = lexbuf; l1_buffer = []; }

let lexer1 (lexbuf : lexer1) =
  if lexbuf.l1_buffer = [] then
    lexbuf.l1_buffer <- EcLexer.main lexbuf.l1_lexbuf;

  match lexbuf.l1_buffer with
  | [] ->
      failwith "short-read-from-lexer"

  | token :: queue ->
      lexbuf.l1_buffer <- queue;
      (token,
         Lexing.lexeme_start_p lexbuf.l1_lexbuf,
         Lexing.lexeme_end_p   lexbuf.l1_lexbuf)

(* -------------------------------------------------------------------- *)
let is_uniop (x : string) =
  match lex_single_token x with
  | Some (EcParser.PUNIOP x) -> begin
    try
      let x =
        EcRegexp.exec (`S "^\\[(.+)\\]$") x
          |> omap (fun m -> oget (EcRegexp.Match.group m 1))
          |> odfl x
      in

      let parse  = isuniop_fun () in
      let lexbuf = lexer1_of_lexbuf (Lexing.from_string x) in
      parse (fun () -> lexer1 lexbuf); `Yes
    with EcLexer.LexicalError _  | EcParser.Error -> `Invalid
  end

  | _ -> `No

(* -------------------------------------------------------------------- *)
let is_binop (x : string) =
  match lex_single_token x with
  | Some (EcParser.PBINOP x) -> begin
    try
      let parse  = isbinop_fun () in
      let lexbuf = lexer1_of_lexbuf (Lexing.from_string x) in
      parse (fun () -> lexer1 lexbuf); `Yes
    with EcLexer.LexicalError _  | EcParser.Error -> `Invalid
  end

  | _ -> `No
