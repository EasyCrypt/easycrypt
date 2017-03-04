(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils

module P = EcParser
module L = Lexing

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
  let lexbuf = lexbuf_from_channel name channel in

    Disposable.create
      { ecr_lexbuf  = lexbuf;
        ecr_parser  = parserfun ();
        ecr_atstart = true;
        ecr_tokens  = []; }

(* -------------------------------------------------------------------- *)
let from_file filename =
  let channel = open_in filename in
    try
      let lexbuf = lexbuf_from_channel filename channel in

        Disposable.create ~cb:(fun _ -> close_in channel)
          { ecr_lexbuf  = lexbuf;
            ecr_parser  = parserfun ();
            ecr_atstart = true;
            ecr_tokens  = []; }

    with
      | e ->
          (try close_in channel with _ -> ());
          raise e

(* -------------------------------------------------------------------- *)
let from_string data =
  let lexbuf = Lexing.from_string data in

    Disposable.create
      { ecr_lexbuf  = lexbuf;
        ecr_parser  = parserfun ();
        ecr_atstart = true;
        ecr_tokens  = []; }

(* -------------------------------------------------------------------- *)
let finalize (ecreader : 'a ecreader_g) =
  Disposable.dispose ecreader

(* -------------------------------------------------------------------- *)
let lexer = fun ecreader ->
  let lexbuf = ecreader.ecr_lexbuf in

  if ecreader.ecr_tokens = [] then
    ecreader.ecr_tokens <- EcLexer.main lexbuf;

  match ecreader.ecr_tokens with
  | [] ->
      failwith "short-read-from-lexer"

  | token :: queue -> begin
      ecreader.ecr_tokens  <- queue;
      ecreader.ecr_atstart <- (token = EcParser.FINAL);
      (token, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
  end

(* -------------------------------------------------------------------- *)
let drain (ecreader : 'a ecreader_g) =
  let ecreader = Disposable.get ecreader in
  let rec drain () =
    try
      match lexer ecreader with
      | (EcParser.FINAL, _, _) -> ()
      | _ -> drain ()
    with EcLexer.LexicalError _ -> drain ()
  in
    if not ecreader.ecr_atstart then
      drain ()

(* -------------------------------------------------------------------- *)
let parse (ecreader : 'a ecreader_g) =
  let ecreader = Disposable.get ecreader in
    ecreader.ecr_parser (fun () -> lexer ecreader)

(* -------------------------------------------------------------------- *)
let parseall (ecreader : 'a ecreader_g) =
  let rec aux acc =
    match EcLocation.unloc (parse ecreader) with
    | EcParsetree.P_Prog (commands, terminate) ->
        let acc = List.rev_append commands acc in
          if terminate then List.rev acc else aux acc
    | EcParsetree.P_Undo _ ->
        assert false                    (* FIXME *)
  in
    aux []

(* -------------------------------------------------------------------- *)
let lex_single_token name =
  try
    let ecr =
      { ecr_lexbuf  = Lexing.from_string name;
        ecr_parser  = parserfun ();
        ecr_atstart = true;
        ecr_tokens  = []; } in

    let (token, _, _) = lexer ecr in

    match lexer ecr with
    | (EcParser.EOF, _, _) -> Some token
    | _ -> None

  with EcLexer.LexicalError _ -> None

(* -------------------------------------------------------------------- *)
let is_sym_ident x =
  match lex_single_token x with
  | Some (EcParser.LIDENT _) -> true
  | Some (EcParser.UIDENT _) -> true
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
