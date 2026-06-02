(* -------------------------------------------------------------------- *)
open EcUtils

module P = EcParser
module L = Lexing
module I = EcParser.MenhirInterpreter

(* -------------------------------------------------------------------- *)
let lexbuf_from_channel = fun name channel ->
  let lexbuf = Lexing.from_channel channel in
    lexbuf.Lexing.lex_curr_p <- {
        Lexing.pos_fname = name;
        Lexing.pos_lnum  = 1;
        Lexing.pos_bol   = 0;
        Lexing.pos_cnum  = 0
      };
    lexbuf

(* -------------------------------------------------------------------- *)
type 'a parser_t =
  (P.token * L.position * L.position, 'a) MenhirLib.Convert.revised

(* -------------------------------------------------------------------- *)
let parserfun () : EcParsetree.prog parser_t =
  MenhirLib.Convert.Simplified.traditional2revised EcParser.prog

(* -------------------------------------------------------------------- *)
let isbinop_fun () : unit parser_t =
    MenhirLib.Convert.Simplified.traditional2revised EcParser.is_binop

let isuniop_fun () : unit parser_t =
    MenhirLib.Convert.Simplified.traditional2revised EcParser.is_uniop

(* -------------------------------------------------------------------- *)
type ecreader_r = {
  (*---*) ecr_lexbuf  : Lexing.lexbuf;
  (*---*) ecr_source  : Buffer.t;
  mutable ecr_atstart : bool;
  mutable ecr_trim    : int;
  mutable ecr_tokens  : EcParser.token list;
  (* Pre-positioned triples produced by expanding a quotation.  These are
     emitted (front-first) before any token is read from [ecr_lexbuf], so a
     single quotation can expand to several EC sentences across successive
     [parse] calls.  Positions are already remapped into the original file. *)
  mutable ecr_expand  : (EcParser.token * L.position * L.position) list;
}

type ecreader = ecreader_r Disposable.t

(* -------------------------------------------------------------------- *)
let ecreader_of_lexbuf (buffer : Buffer.t) (lexbuf : L.lexbuf) : ecreader_r =
  { ecr_lexbuf  = lexbuf;
    ecr_source  = buffer;
    ecr_atstart = true;
    ecr_trim    = 0;
    ecr_tokens  = [];
    ecr_expand  = []; }

(* -------------------------------------------------------------------- *)
let lexbuf (reader : ecreader) =
  (Disposable.get reader).ecr_lexbuf

(* -------------------------------------------------------------------- *)
let from_channel ?(close = false) ~name channel =
  let buffer = Buffer.create 0 in

  let refill (bytes : bytes) (len : int) =
    let aout = input channel bytes 0 len in
    Buffer.add_bytes buffer (Bytes.sub bytes 0 aout);
    aout
  in

  let lexbuf = Lexing.from_function refill in

  Lexing.set_filename lexbuf name;

  Disposable.create
    ~cb:(fun _ -> if close then close_in channel)
    (ecreader_of_lexbuf buffer lexbuf)

(* -------------------------------------------------------------------- *)
let from_file (filename : string) =
  let channel = open_in filename in

  try
    from_channel ~close:true ~name:filename channel

  with e ->
    (try close_in channel with _ -> ());
    raise e

(* -------------------------------------------------------------------- *)
let from_string data =
  let lexbuf = Lexing.from_string data in
  let buffer = Buffer.create (String.length data) in

  Buffer.add_string buffer data;

  Disposable.create (ecreader_of_lexbuf buffer lexbuf)

(* -------------------------------------------------------------------- *)
let finalize (ecreader : ecreader) =
  Disposable.dispose ecreader

(* -------------------------------------------------------------------- *)
let debug (q : EcQuotation.quotation) (expanded : string) : unit =
  Printf.printf
  ("---------- quotation ----------\n" ^^
   "handler: %s\nbody:\n----------\n%s\n----------\n" ^^
   "expansion:\n----------\n%s\n----------\n")
  q.q_name (String.trim q.q_body) expanded

(* -------------------------------------------------------------------- *)
(* Expand a quotation into a list of pre-positioned token triples.       *)
(* The handler output is lexed in its own buffer; each token's positions  *)
(* are remapped into the original file via the source map.               *)
(*                                                                        *)
(* A quotation expands to a FRAGMENT that is spliced into the surrounding *)
(* sentence: it may stand for only part of a sentence, and the sentence   *)
(* terminator ('.') is always written by the user, never produced by the *)
(* expansion.  Hence the fragment must contain no FINAL.                  *)
let expand_quotation (q : EcQuotation.quotation)
  : (EcParser.token * L.position * L.position) list
=
  let (expanded, sm) = EcQuotation.run q in
  let () = if q.q_debug then debug q expanded in
  let sub = Lexing.from_string expanded in
  Lexing.set_filename sub (EcQuotation.sentinel_fname q);

  let remap o = EcQuotation.remap_position sm q o in

  let rec collect acc =
    let toks =
      try EcLexer.main sub
      with EcLexer.LexicalError (_, msg) ->
        EcQuotation.error q
          (Printf.sprintf "lexical error in expansion: %s" msg)
    in
    (* positions of the lexeme just consumed by EcLexer.main *)
    let sp = remap (Lexing.lexeme_start sub) in
    let ep = remap (Lexing.lexeme_end   sub) in
    let acc =
      List.fold_left (fun acc tk -> (tk, sp, ep) :: acc) acc toks in
    match toks with
    | [EcParser.EOF] -> List.rev acc
    | _              -> collect acc
  in
  let triples = collect [] in

  (* drop the lexed EOF; the surrounding stream supplies sentence flow *)
  let body = List.filter (fun (t, _, _) -> t <> EcParser.EOF) triples in
  (* a fragment must not terminate the sentence: the '.' is the user's *)
  let isfinal = function EcParser.FINAL _ -> true | _ -> false in
  if List.exists (fun (t, _, _) -> isfinal t) body then
    EcQuotation.error q
      "quotation expansion must be a sentence fragment (it must not contain '.')";
  body

(* -------------------------------------------------------------------- *)
let rec lexer ?(checkpoint : _ I.checkpoint option) (ecreader : ecreader_r) =
  let lexbuf = ecreader.ecr_lexbuf in

  let isfinal = function
    | EcParser.FINAL _ -> true
    | _ -> false in

  (* Emit the next pre-positioned expansion triple, if any. *)
  let emit_expand () =
    match ecreader.ecr_expand with
    | [] -> None
    | triple :: rest ->
        ecreader.ecr_expand <- rest;
        Some triple
  in

  match emit_expand () with
  | Some triple -> triple
  | None ->

  if ecreader.ecr_atstart then
    ecreader.ecr_trim <- ecreader.ecr_lexbuf.Lexing.lex_curr_p.pos_cnum;

  while List.is_empty (ecreader.ecr_tokens) do
    match EcLexer.main lexbuf with
    | [COMMENT] ->
      if ecreader.ecr_atstart then
        ecreader.ecr_trim <- (Lexing.lexeme_end_p ecreader.ecr_lexbuf).pos_cnum
    | [DOCCOMMENT _] as tokens ->
      if ecreader.ecr_atstart then
        ecreader.ecr_tokens <- tokens
    | tokens ->
        ecreader.ecr_tokens <- tokens
  done;

  (* Intercept a quotation token: expand it into a fragment and splice it.
     A quotation always sits at the head of [ecr_tokens] (its lexer rule
     returns a singleton list).  An empty fragment is allowed -- recurse to
     produce the next real token. *)
  match ecreader.ecr_tokens with
  | EcParser.QUOTATION q :: queue ->
      ecreader.ecr_tokens <- queue;
      ecreader.ecr_expand <- expand_quotation q;
      lexer ?checkpoint ecreader
  | _ ->

  let token, queue = List.destruct ecreader.ecr_tokens in

  let token, prequeue =
    match checkpoint, token with
    | Some checkpoint, P.DECIMAL (pre, (_, post)) ->
      if I.acceptable checkpoint token lexbuf.lex_curr_p then
        token, []
      else
        List.destruct P.[UINT pre; DOT; UINT post]
    | _ ->
      token, []
  in

  ecreader.ecr_tokens  <- prequeue @ queue;

  if isfinal token then
    ecreader.ecr_atstart <- true
  else
    ecreader.ecr_atstart <- ecreader.ecr_atstart && (
      match token with
      | P.DOCCOMMENT _ | P.COMMENT -> true
      | _ -> false
    );

  (token, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)

(* -------------------------------------------------------------------- *)
let drain (ecreader : ecreader) =
  let ecreader = Disposable.get ecreader in

  let rec drain () =
    match lexer ecreader with
    | (EcParser.FINAL _, _, _) -> ()
    | _ | exception EcLexer.LexicalError _ -> drain ()
  in
    if not ecreader.ecr_atstart then
      drain ()

(* -------------------------------------------------------------------- *)
let parse (ecreader : ecreader) : EcParsetree.prog =
  let ecreader = Disposable.get ecreader in

  let rec parse (checkpoint : EcParsetree.prog I.checkpoint) : EcParsetree.prog =
    match checkpoint with
    | Accepted pst ->
      pst

    | InputNeeded _ ->
      parse (I.offer checkpoint (lexer ~checkpoint ecreader))

    | Shifting _ | AboutToReduce _ | HandlingError _ ->
      parse (I.resume checkpoint)

    | Rejected ->
      raise EcParser.Error

  in parse (EcParser.Incremental.prog ecreader.ecr_lexbuf.lex_curr_p)

(* -------------------------------------------------------------------- *)
let xparse (ecreader : ecreader) : string * EcParsetree.prog =
  let ecr = Disposable.get ecreader in

  let p1 = ecr.ecr_lexbuf.Lexing.lex_curr_p.pos_cnum in
  let cd = parse ecreader in
  let p2 = ecr.ecr_lexbuf.Lexing.lex_curr_p.pos_cnum in
  let p1 = max p1 ecr.ecr_trim in

  (Buffer.sub ecr.ecr_source p1 (p2 - p1), cd)

(* -------------------------------------------------------------------- *)
let parseall (ecreader : ecreader) =
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
let lex_single_token (name : string) =
  match EcLexer.main (Lexing.from_string name) with
  | token :: _ -> Some token
  | _ | exception EcLexer.LexicalError _ -> None

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
