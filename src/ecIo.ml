(* -------------------------------------------------------------------- *)
open EcUtils

module A = EcParsetree
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
type lctoken = EcParser.token * L.position * L.position

type ecreader_r = {
  (*---*) ecr_lexbuf      : Lexing.lexbuf;
  (*---*) ecr_source      : Buffer.t;
  mutable ecr_atstart     : bool;
  mutable ecr_trim        : int;
  mutable ecr_tokens      : lctoken list;
  mutable ecr_lkahead     : lctoken option;
  mutable ecr_is_nt_name  : string -> bool;
  mutable ecr_prev_token  : EcParser.token option;
}

type ecreader = ecreader_r Disposable.t

(* -------------------------------------------------------------------- *)
let ecreader_of_lexbuf (buffer : Buffer.t) (lexbuf : L.lexbuf) : ecreader_r =
  { ecr_lexbuf      = lexbuf;
    ecr_source      = buffer;
    ecr_atstart     = true;
    ecr_trim        = 0;
    ecr_tokens      = [];
    ecr_lkahead     = None;
    ecr_is_nt_name  = (fun _ -> false);
    ecr_prev_token  = None; }

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
let lexer ?(checkpoint : _ I.checkpoint option) (ecreader : ecreader_r) =
  let lexbuf = ecreader.ecr_lexbuf in

  let isfinal = function
    | EcParser.FINAL _ -> true
    | _ -> false in

  if ecreader.ecr_atstart then
    ecreader.ecr_trim <- ecreader.ecr_lexbuf.Lexing.lex_curr_p.pos_cnum;

  while List.is_empty (ecreader.ecr_tokens) do
    let tokens = EcLexer.main lexbuf in
    let lstart = Lexing.lexeme_start_p lexbuf in
    let lend   = Lexing.lexeme_end_p   lexbuf in
    let locate (tks : P.token list) : lctoken list =
      List.map (fun tk -> (tk, lstart, lend)) tks in
    match tokens with
    | [COMMENT] ->
      if ecreader.ecr_atstart then
        ecreader.ecr_trim <- (Lexing.lexeme_end_p ecreader.ecr_lexbuf).pos_cnum
    | [DOCCOMMENT _] ->
      if ecreader.ecr_atstart then
        ecreader.ecr_tokens <- locate tokens
    | tokens ->
        ecreader.ecr_tokens <- locate tokens
  done;

  let token, queue = List.destruct ecreader.ecr_tokens in

  let token, prequeue =
    match checkpoint, token with
    | Some checkpoint, ((P.DECIMAL (pre, (_, post))) as tk, lstart, lend) ->
      if I.acceptable checkpoint tk lexbuf.lex_curr_p then
        token, []
      else
        let tokens = P.[UINT pre; DOT; UINT post] in
        let tokens = List.map (fun tk -> (tk, lstart, lend)) tokens in
        List.destruct tokens
    | Some checkpoint, (P.NIDENT n, lstart, lend)
      when ecreader.ecr_prev_token <> Some P.DOT
        && not (ecreader.ecr_is_nt_name n)
        && I.acceptable checkpoint P.SHARP lexbuf.lex_curr_p ->
      let suffix = String.sub n 1 (String.length n - 1) in
      let tokens = P.[SHARP; LIDENT suffix] in
      let tokens = List.map (fun tk -> (tk, lstart, lend)) tokens in
      List.destruct tokens
    | _ ->
      token, []
  in

  ecreader.ecr_tokens  <- prequeue @ queue;

  let raw = proj3_1 token in
  if isfinal raw then
    ecreader.ecr_atstart <- true
  else
    ecreader.ecr_atstart <- ecreader.ecr_atstart && (
      match raw with
      | P.DOCCOMMENT _ | P.COMMENT -> true
      | _ -> false
    );

  ecreader.ecr_lkahead <- Some token;
  ecreader.ecr_prev_token <- Some raw;
  token

(* -------------------------------------------------------------------- *)
let drain (ecreader : ecreader) =
  let ecreader = Disposable.get ecreader in

  let rec drain () =
    match lexer ecreader with
    | (EcParser.FINAL _, _, _) -> ()
    | _ | exception EcLexer.LexicalError _ -> drain ()
  in
    if not ecreader.ecr_atstart then
      drain ();
    ecreader.ecr_lkahead <- None

(* -------------------------------------------------------------------- *)
(* Notation parse-time dispatcher. Reads a `#name [...]` call site by
   driving the menhir parser's [N_nttstart] reduction: collects the
   notation name, consumes template punctuation, reads identifier slots
   and recursively-parsed form slots, then synthesizes the
   [NTTINSTANCE] token the grammar expects. *)
module Notations = struct

type t = EcSymbols.qsymbol -> EcDecl.nt_template_item list option

let empty : t = fun _ -> None

(* -------------------------------------------------------------------- *)
(* Low-level lookahead/error helpers, used only by the dispatcher. *)

let pushback_lookahead (ecreader : ecreader_r) : unit =
  ecreader.ecr_tokens  <- Option.to_list ecreader.ecr_lkahead @ ecreader.ecr_tokens;
  ecreader.ecr_lkahead <- None

let show_qsymbol ((ns, x) : EcSymbols.qsymbol) : string =
  String.concat "." (ns @ [x])

let punct_kind_name : EcDecl.nt_punct_kind -> string = function
  | `LBRACKET  -> "`['"
  | `RBRACKET  -> "`]'"
  | `COLON     -> "`:'"
  | `PIPE      -> "`|'"
  | `COMMA     -> "`,'"
  | `SEMICOLON -> "`;'"

let parse_error_loc (loc : EcLocation.t) (msg : string) : 'a =
  raise (EcParsetree.ParseError (loc, Some msg))

let cur_loc (ecreader : ecreader_r) : EcLocation.t =
  let lexbuf = ecreader.ecr_lexbuf in
  EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p

(* -------------------------------------------------------------------- *)
(* Consume the next token and require it to be the punct [p]. Returns
   the end position (for instance-span tracking). Raises a located
   ParseError on mismatch. *)
let eat
    ~(notation : string)
    (ecreader  : ecreader_r)
    (p         : EcDecl.nt_punct)
  : L.position
=
  pushback_lookahead ecreader;
  let (tk, startp, endp) = lexer ecreader in
  let ok =
    match tk, p.EcDecl.np_kind with
    | EcParser.LBRACKET , `LBRACKET
    | EcParser.RBRACKET , `RBRACKET
    | EcParser.COLON    , `COLON
    | EcParser.PIPE     , `PIPE
    | EcParser.COMMA    , `COMMA
    | EcParser.SEMICOLON, `SEMICOLON -> true
    | _ -> false
  in
  if ok then begin
    ecreader.ecr_lkahead <- None;
    endp
  end else
    parse_error_loc (EcLocation.make startp endp)
      (Printf.sprintf "in notation `%s': expected %s" notation
         (punct_kind_name p.EcDecl.np_kind))

(* Reads an lident (or `_` for a fresh anonymous name) for a binder
   slot. Returns (arg, end_pos). *)
let read_ident_slot
    ~(notation : string)
    ~(slot     : string)
    (ecreader  : ecreader_r)
  : A.pformula option * L.position
=
  pushback_lookahead ecreader;
  match lexer ecreader with
  | (EcParser.LIDENT x, lstart, lend) ->
    ecreader.ecr_lkahead <- None;
    let loc = EcLocation.make lstart lend in
    let sym = EcLocation.mk_loc loc ([], x) in
    Some (EcLocation.mk_loc loc (A.PFident (sym, None))), lend
  | (EcParser.UNDERSCORE, lstart, lend) ->
    ecreader.ecr_lkahead <- None;
    let loc = EcLocation.make lstart lend in
    let name = Printf.sprintf "_%s" slot in
    let sym = EcLocation.mk_loc loc ([], name) in
    Some (EcLocation.mk_loc loc (A.PFident (sym, None))), lend
  | (_, lstart, lend) ->
    parse_error_loc (EcLocation.make lstart lend)
      (Printf.sprintf
        "in notation `%s': expected identifier for binder slot `%s'"
        notation slot)

(* Peek the next non-consumed token without consuming it. Returns the
   punctuation kind if the next token is one of the six template
   puncts, [None] otherwise. Used by [collect_instance] to decide
   whether an optional group's trigger fires. *)
let peek_punct (ecreader : ecreader_r) : EcDecl.nt_punct_kind option =
  pushback_lookahead ecreader;
  let (tk, _, _) as lc = lexer ecreader in
  ecreader.ecr_lkahead <- Some lc;
  match tk with
  | EcParser.LBRACKET  -> Some `LBRACKET
  | EcParser.RBRACKET  -> Some `RBRACKET
  | EcParser.COLON     -> Some `COLON
  | EcParser.PIPE      -> Some `PIPE
  | EcParser.COMMA     -> Some `COMMA
  | EcParser.SEMICOLON -> Some `SEMICOLON
  | _ -> None

(* Mark every slot inside a non-triggered optional group as absent, so
   the typechecker substitutes the stored default for each. [acc] is
   the running list of [(slot_name, arg_opt)] entries in REVERSE order
   (the [collect_instance] caller reverses it at the end). *)
let rec mark_absent
    (acc   : (EcSymbols.symbol * A.pformula option) list)
    (items : EcDecl.nt_template_item list)
  : (EcSymbols.symbol * A.pformula option) list
=
  match items with
  | [] -> acc
  | EcDecl.NTI_Slot (s, _) :: tl -> mark_absent ((s, None) :: acc) tl
  | EcDecl.NTI_Punct _      :: tl -> mark_absent acc tl
  | EcDecl.NTI_Optional sub :: tl -> mark_absent (mark_absent acc sub) tl

(* -------------------------------------------------------------------- *)
(* Collect the notation name and slot args, then synthesize the
   NTTINSTANCE token payload with the real source span. Returns the
   updated menhir env. *)
let collect_instance
    (ecreader        : ecreader_r)
    (notations       : t)
    (parse_form_slot :
       level:[`Form | `SForm] -> ecreader_r -> A.pformula)
    (env             : 'a I.env)
    (production      : I.production)
  : 'a I.env
=
  let env = I.force_reduction production env in
  let name, name_loc, startp =
    let Element (s, ntt, startp, _endp) = Option.get (I.top env) in
    match I.incoming_symbol s with
    | N (N_nttstart) ->
      (EcLocation.unloc ntt, EcLocation.loc ntt, startp)
    | _ -> assert false in
  let name_str = show_qsymbol name in
  let template =
    match notations name with
    | None ->
      parse_error_loc name_loc
        (Printf.sprintf "unknown notation `%s'" name_str)
    | Some t -> t in

  (* Walk template items consuming input. [present] accumulates
     (slot_name, arg_opt) entries in REVERSE order. *)
  let endp = ref startp in
  let rec step present = function
    | [] -> present

    | EcDecl.NTI_Slot (slot, EcDecl.NTS_Ident) :: rest ->
      let arg, e = read_ident_slot ~notation:name_str ~slot ecreader in
      endp := e;
      step ((slot, arg) :: present) rest

    | EcDecl.NTI_Slot (slot, EcDecl.NTS_Form _) :: rest ->
      (* A form slot is "fenced" at form-level iff the next thing that
         might appear is a PUNCT (either immediately or as the trigger
         of an optional group). Otherwise it's trailing; parse at
         sform-level so it doesn't absorb outer operators. *)
      let level =
        match rest with
        | EcDecl.NTI_Punct _ :: _ -> `Form
        | EcDecl.NTI_Optional (EcDecl.NTI_Punct _ :: _) :: _ -> `Form
        | _ -> `SForm in
      let f = parse_form_slot ~level ecreader in
      step ((slot, Some f) :: present) rest

    | EcDecl.NTI_Punct tk :: rest ->
      endp := eat ~notation:name_str ecreader tk;
      step present rest

    | EcDecl.NTI_Optional items :: rest ->
      let trigger =
        match items with
        | EcDecl.NTI_Punct t :: _ -> t.EcDecl.np_kind
        | _ -> assert false in
      match peek_punct ecreader with
      | Some k when k = trigger ->
        (* Splice the group's items into the continuation so trailing
           form slots inside the group see the outer [rest] as their
           fence. *)
        step present (items @ rest)
      | _ ->
        step (mark_absent present items) rest in
  let args = List.rev (step [] template) in

  pushback_lookahead ecreader;
  I.feed (T T_NTTINSTANCE) startp args !endp env

(* Parse a quoted form appearing inside a notation slot; delimited by
   the `form error` production so parsing accepts once the next token
   doesn't continue the form. Nested notations resolve recursively.

   [level] selects the precedence bracket at which the slot's form is
   parsed: [`Form] lets the form greedily slurp low-precedence operators
   (equality, chained orderings) up to the next token that the form
   grammar can't extend with; [`SForm] stops at sform boundaries so
   operators like [=] are left to the outer context. Use [`Form] for
   slots fenced by a following punct, [`SForm] for trailing slots. *)
let rec parse_quoted_formula
    ~(level    : [`Form | `SForm])
    (ecreader  : ecreader_r)
    (notations : t)
  : A.pformula
=
  let rec go (checkpoint : A.pformula I.checkpoint) : A.pformula =
    match checkpoint with
    | Accepted pst -> pst

    | I.Rejected ->
      parse_error_loc (cur_loc ecreader)
        "parse error in notation slot"

    | InputNeeded _ ->
      go (I.offer checkpoint (lexer ~checkpoint ecreader))

    | HandlingError _ | Shifting _ ->
      go (I.resume checkpoint)

    | AboutToReduce (env, production) ->
      match I.lhs production with
      | X (N N_nttstart) ->
        let env =
          collect_instance ecreader notations
            (fun ~level:inner r ->
               parse_quoted_formula ~level:inner r notations)
            env production in
        go (I.offer (I.input_needed env) (lexer ecreader))
      | _ ->
        go (I.resume checkpoint)
  in
  pushback_lookahead ecreader;
  let start =
    match level with
    | `Form  -> EcParser.Incremental.ntt_form
    | `SForm -> EcParser.Incremental.ntt_sform in
  go (start ecreader.ecr_lexbuf.lex_curr_p)

end

(* -------------------------------------------------------------------- *)
let parse ?(notations : Notations.t = Notations.empty) (ecreader : ecreader) =
  let ecreader = Disposable.get ecreader in
  ecreader.ecr_is_nt_name <-
    (fun n -> Option.is_some (notations ([], n)));

  let rec parse (checkpoint : A.prog I.checkpoint) : EcParsetree.prog =
    match checkpoint with
    | Accepted pst ->
      pst

    | Rejected ->
      raise (EcParsetree.ParseError (Notations.cur_loc ecreader, None))

    | InputNeeded _ ->
      parse (I.offer checkpoint (lexer ~checkpoint ecreader))

    | HandlingError _ | Shifting _ ->
      parse (I.resume checkpoint)

    | AboutToReduce (env, production) ->
      match I.lhs production with
      | X (N N_nttstart) ->
        let env =
          Notations.collect_instance ecreader notations
            (fun ~level r -> Notations.parse_quoted_formula ~level r notations)
            env production in
        parse (I.offer (I.input_needed env) (lexer ecreader))
      | _ -> parse (I.resume checkpoint)

  in parse (EcParser.Incremental.prog ecreader.ecr_lexbuf.lex_curr_p)

(* -------------------------------------------------------------------- *)
let xparse ?notations (ecreader : ecreader) : string * EcParsetree.prog =
  let ecr = Disposable.get ecreader in

  let p1 = ecr.ecr_lexbuf.Lexing.lex_curr_p.pos_cnum in
  let cd = parse ?notations ecreader in
  let p2 = ecr.ecr_lexbuf.Lexing.lex_curr_p.pos_cnum in
  let p1 = max p1 ecr.ecr_trim in

  (Buffer.sub ecr.ecr_source p1 (p2 - p1), cd)

(* -------------------------------------------------------------------- *)
let parseall ?notations (ecreader : ecreader) =
  let rec aux acc =
    match EcLocation.unloc (parse ?notations ecreader) with
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

(* Lex the entire string and require it to produce exactly one token (with
   only whitespace around it). Returns [None] if the string contains more
   than one token, a lexical error, or nothing. Trailing EOF is tolerated. *)
let lex_only_token (name : string) : EcParser.token option =
  let is_trailing_noise = function
    | EcParser.EOF
    | EcParser.COMMENT -> true
    | _ -> false in
  let lexbuf = Lexing.from_string name in
  match EcLexer.main lexbuf with
  | exception EcLexer.LexicalError _ -> None
  | [] -> None
  | token :: rest ->
    if not (List.is_empty rest) then None
    else
      match EcLexer.main lexbuf with
      | exception EcLexer.LexicalError _ -> None
      | toks when List.for_all is_trailing_noise toks -> Some token
      | _ -> None

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
