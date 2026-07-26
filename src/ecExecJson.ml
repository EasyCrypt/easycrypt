(** Addition 13 — EXEC-JSON: structured execution meta-command.

    Accepts a JSON-encoded EC command (tactic invocation or
    directive) and, in v0, renders it to EC source text fed through
    the normal text-path parser. The wire contract is the commitment:
    clients speak JSON, server understands JSON, and unsupported
    commands return [UnsupportedExecJson] explicitly rather than
    silently falling back.

    v0 coverage: ten tactics and four directives (see [render] at the
    bottom of this module). v1 and beyond incrementally replace the
    text-rendering dispatch with direct [EcParsetree] AST construction
    per tactic, so parse-error risk goes away for commands that
    migrate. The wire format is stable across that migration. *)

(* -------------------------------------------------------------------- *)
(* Result type                                                            *)
(* -------------------------------------------------------------------- *)

(* On [Err (code, detail)] the caller emits an ERROR reply with
   [ERROR-JSON.code = code]. On [Ok_render (text, payload)] the caller
   feeds [text] through [process_ec_input] and populates the next
   OK-JSON with [payload]. [payload] is always a valid JSON object. *)

type result =
  | Ok_render of string * string
  | Err of string * string

(* -------------------------------------------------------------------- *)
(* Small JSON helpers. Inline rather than sharing with ec.ml's since     *)
(* the library file compiles ahead of the executable.                    *)
(* -------------------------------------------------------------------- *)

let json_escape s =
  let buf = Buffer.create (String.length s + 4) in
  String.iter (fun c ->
    match c with
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 ->
      Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c) s;
  Buffer.contents buf

let member_opt j name =
  match j with
  | `Assoc kvs -> List.assoc_opt name kvs
  | _ -> None

let to_string_opt = function `String s -> Some s | _ -> None
let to_int_opt    = function `Int n    -> Some n | _ -> None
let to_list_opt   = function `List l   -> Some l | _ -> None

let get_string j name = match member_opt j name with
  | Some v -> to_string_opt v
  | None -> None

let get_list j name = match member_opt j name with
  | Some v -> to_list_opt v
  | None -> None

(* -------------------------------------------------------------------- *)
(* Error constructors                                                    *)
(* -------------------------------------------------------------------- *)

let unsupported ?arg_index ~name fmt =
  Printf.ksprintf
    (fun detail ->
       let suffix = match arg_index with
         | None -> ""
         | Some i -> Printf.sprintf " (arg_index=%d)" i
       in
       Err ("UnsupportedExecJson",
            Printf.sprintf "%s%s: %s" name suffix detail))
    fmt

let malformed fmt =
  Printf.ksprintf (fun detail -> Err ("MalformedExecJson", detail)) fmt

(* -------------------------------------------------------------------- *)
(* Arg decoding                                                          *)
(* -------------------------------------------------------------------- *)

type arg =
  | A_qname of string
  | A_int   of int
  | A_flag  of string
  | A_text  of string

let decode_arg ~cmd_name ~index (j : Yojson.Safe.t) =
  let kind = match get_string j "kind" with Some s -> Some s | None -> None in
  let value = member_opt j "value" in
  match kind, value with
  | Some "qname", Some (`String s) -> Stdlib.Ok (A_qname s)
  | Some "int",   Some (`Int n)    -> Stdlib.Ok (A_int n)
  | Some "flag",  Some (`String s) -> Stdlib.Ok (A_flag s)
  | Some "text",  Some (`String s) -> Stdlib.Ok (A_text s)
  | Some k, _ ->
    Stdlib.Error
      (unsupported ~arg_index:index ~name:cmd_name
         "unknown or malformed arg kind %S" k)
  | None, _ ->
    Stdlib.Error
      (malformed "%s arg %d: missing `kind` field" cmd_name index)

let decode_args ~cmd_name json_args =
  let rec loop i = function
    | [] -> Stdlib.Ok []
    | j :: rest ->
      match decode_arg ~cmd_name ~index:i j with
      | Stdlib.Error e -> Stdlib.Error e
      | Stdlib.Ok a ->
        match loop (i + 1) rest with
        | Stdlib.Error e -> Stdlib.Error e
        | Stdlib.Ok rest' -> Stdlib.Ok (a :: rest')
  in
  loop 0 json_args

(* -------------------------------------------------------------------- *)
(* Rendering — one helper per supported command shape                    *)
(* -------------------------------------------------------------------- *)

let ok_metadata ~command_kind ~command_name =
  Printf.sprintf
    "{\"kind\":\"exec-json\",\"command_kind\":\"%s\",\"command_name\":\"%s\"}"
    command_kind (json_escape command_name)

let ok text ~command_kind ~command_name =
  Ok_render (text, ok_metadata ~command_kind ~command_name)

let render_name_only ~cmd_name ~command_kind args =
  match args with
  | [] -> ok (cmd_name ^ ".") ~command_kind ~command_name:cmd_name
  | _ ->
    unsupported ~name:cmd_name "%s takes no arguments" cmd_name

let render_one_qname_required ~cmd_name ~command_kind args =
  match args with
  | [A_qname q] ->
    ok (Printf.sprintf "%s %s." cmd_name q)
      ~command_kind ~command_name:cmd_name
  | [A_text t] ->
    ok (Printf.sprintf "%s %s." cmd_name t)
      ~command_kind ~command_name:cmd_name
  | _ ->
    unsupported ~name:cmd_name
      "expected exactly one qname-or-text argument"

let render_one_qname_optional ~cmd_name ~command_kind args =
  match args with
  | [] -> ok (cmd_name ^ ".") ~command_kind ~command_name:cmd_name
  | [A_qname q] ->
    ok (Printf.sprintf "%s %s." cmd_name q)
      ~command_kind ~command_name:cmd_name
  | _ ->
    unsupported ~name:cmd_name
      "expected zero or one qname argument"

let render_qnames_one_or_more ~cmd_name ~command_kind args =
  let names = List.filter_map
      (function A_qname q -> Some q | _ -> None) args
  in
  if names = [] || List.length names <> List.length args then
    unsupported ~name:cmd_name
      "expected one or more qname arguments"
  else
    ok (Printf.sprintf "%s %s." cmd_name (String.concat " " names))
      ~command_kind ~command_name:cmd_name

let render_rewrite args =
  match args with
  | [A_flag dir; A_qname q] when dir = "->" || dir = "<-" ->
    ok (Printf.sprintf "rewrite %s %s." dir q)
      ~command_kind:"tactic" ~command_name:"rewrite"
  | _ ->
    unsupported ~name:"rewrite"
      "v0 signature: [flag \"->\" or \"<-\"] [qname]"

let render_move args =
  match args with
  | A_flag dir :: rest when dir = "=>" || dir = ":" ->
    let names = List.filter_map
        (function A_qname q -> Some q | A_flag "_" -> Some "_" | _ -> None)
        rest
    in
    if List.length names <> List.length rest then
      unsupported ~name:"move"
        "v0 signature: [flag \"=>\" or \":\"] [qname]*"
    else
      ok (Printf.sprintf "move %s %s." dir (String.concat " " names))
        ~command_kind:"tactic" ~command_name:"move"
  | _ ->
    unsupported ~name:"move"
      "v0 signature: [flag \"=>\" or \":\"] [qname]*"

let render_pragma args =
  match args with
  | [A_qname name] ->
    ok (Printf.sprintf "pragma %s." name)
      ~command_kind:"directive" ~command_name:"pragma"
  | [A_flag f; A_qname name] when f = "+" || f = "-" ->
    ok (Printf.sprintf "pragma %s%s." f name)
      ~command_kind:"directive" ~command_name:"pragma"
  | [A_qname name; A_int n] ->
    ok (Printf.sprintf "pragma %s = %d." name n)
      ~command_kind:"directive" ~command_name:"pragma"
  | [A_qname name; A_qname v] ->
    ok (Printf.sprintf "pragma %s = %s." name v)
      ~command_kind:"directive" ~command_name:"pragma"
  | _ ->
    unsupported ~name:"pragma"
      "v0: [qname] | [flag+/-][qname] | [qname][int] | [qname][qname]"

let render_search args =
  match args with
  | [A_qname q] ->
    ok (Printf.sprintf "search %s." q)
      ~command_kind:"directive" ~command_name:"search"
  | [A_text t] ->
    ok (Printf.sprintf "search %s." t)
      ~command_kind:"directive" ~command_name:"search"
  | _ ->
    unsupported ~name:"search"
      "v0 signature: [qname or text pattern]"

(* -------------------------------------------------------------------- *)
(* Top-level dispatch                                                    *)
(* -------------------------------------------------------------------- *)

let render_tactic ~name args =
  match name with
  | "reflexivity" | "trivial" | "assumption" | "congr" ->
    render_name_only ~cmd_name:name ~command_kind:"tactic" args
  | "apply" | "exact" ->
    render_one_qname_required ~cmd_name:name ~command_kind:"tactic" args
  | "elim" | "case" ->
    render_one_qname_optional ~cmd_name:name ~command_kind:"tactic" args
  | "generalize" | "clear" ->
    render_qnames_one_or_more ~cmd_name:name ~command_kind:"tactic" args
  | "rewrite" -> render_rewrite args
  | "move"    -> render_move args
  | _ ->
    unsupported ~name "tactic not in v0 EXEC-JSON coverage"

let render_directive ~name args =
  match name with
  | "print" | "locate" ->
    render_one_qname_required ~cmd_name:name ~command_kind:"directive" args
  | "search" -> render_search args
  | "pragma" -> render_pragma args
  | _ ->
    unsupported ~name "directive not in v0 EXEC-JSON coverage"

let render (j : Yojson.Safe.t) =
  let kind = get_string j "kind" in
  let name = get_string j "name" in
  let args_raw = match get_list j "args" with
    | Some l -> l
    | None -> []
  in
  match kind, name with
  | None, _ -> malformed "missing top-level `kind` field"
  | _, None -> malformed "missing top-level `name` field"
  | Some "tactic", Some n ->
    (match decode_args ~cmd_name:n args_raw with
     | Stdlib.Error e -> e
     | Stdlib.Ok args -> render_tactic ~name:n args)
  | Some "directive", Some n ->
    (match decode_args ~cmd_name:n args_raw with
     | Stdlib.Error e -> e
     | Stdlib.Ok args -> render_directive ~name:n args)
  | Some k, _ ->
    malformed "unknown top-level `kind`: %S (expected \"tactic\" or \"directive\")" k
