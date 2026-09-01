(* -------------------------------------------------------------------- *)
(* The Model Context Protocol front-end. See [ecMcp.mli].

   This module is to MCP what [EcLlm] is to the text protocol: a wire
   layer only. Every engine-facing operation goes through [EcLlmCore],
   which the two front-ends share.

   The loop is synchronous and single-threaded, which is not an
   implementation shortcut but the correctness anchor: the proof engine
   is a global mutable singleton and uuid ordering is what makes
   [ec_revert] meaningful, so tool calls must run strictly in arrival
   order even when a client pipelines them. *)

module J = Yojson.Safe

(* -------------------------------------------------------------------- *)
(* Protocol revisions.

   We speak the handshake-based ("legacy", in the vocabulary of the
   2026-07-28 spec) era: [initialize] / [notifications/initialized],
   with the negotiated version fixed for the life of the process. Every
   deployed client speaks it.

   Revision 2026-07-28 replaced the handshake with per-request [_meta]
   and a mandatory [server/discover]; supporting it is a separate piece
   of work. A dual-era client probes with [server/discover], gets our
   [-32601] -- not a recognized modern error -- and falls back to
   [initialize], which is exactly the intended detection path. *)
let protocol_latest = "2025-11-25"

let protocol_supported = [
  "2025-11-25";
  "2025-06-18";
  "2025-03-26";
]

let server_name = "easycrypt"

let server_version =
  match EcVersion.hash with "n/a" -> "dev" | v -> v

(* -------------------------------------------------------------------- *)
(* JSON-RPC 2.0 error codes. *)
let e_parse_error     = -32700
let e_invalid_request = -32600
let e_method_not_found = -32601
let e_invalid_params  = -32602

(* Raised by argument validation: a malformed [tools/call] is a
   *protocol* failure, and must not be dressed up as a prover error. *)
exception Invalid_params of string

(* Raised by the checks a tool performs on its own behalf before
   reaching the engine (a missing file, say). Those are EasyCrypt-level
   failures and travel as successful responses with [isError]. *)
exception Tool_error of string

(* -------------------------------------------------------------------- *)
(* [-help]. Where [llm -help] prints the whole agent guide, we print the
   one section of it that describes this server: from its heading down
   to the next heading of the same level. A guide in which that heading
   cannot be found is printed whole, rather than not at all. *)
let usage_section = "## Using the MCP mode"

let extract_usage (guide : string) =
  let is_heading line =
    String.length line >= 3 && String.sub line 0 3 = "## " in
  let rec seek = function
    | [] -> None
    | line :: rest when String.trim line = usage_section ->
      Some (line :: keep rest)
    | _ :: rest -> seek rest
  and keep = function
    | [] -> []
    | line :: _ when is_heading line -> []
    | line :: rest -> line :: keep rest
  in
  match seek (String.split_on_char '\n' guide) with
  | None       -> guide
  | Some lines -> String.concat "\n" lines

let print_usage () =
  let path = EcLlm.llm_guide_path () in
  try
    let ic = open_in_bin path in
    let guide = really_input_string ic (in_channel_length ic) in
    close_in ic;
    print_string (extract_usage guide)
  with Sys_error e ->
    Printf.eprintf "cannot read LLM guide: %s\n%!" e

(* -------------------------------------------------------------------- *)
(* UTF-8 repair.

   A JSON string is UTF-8 by definition, and OCaml strings are bytes.
   Reply text is engine output, which is not ours to trust: EasyCrypt
   echoes source text verbatim (a traced sentence, an error message
   quoting its input), so one Latin-1 comment in a loaded file is
   enough to put a raw 0xe9 inside a JSON string and make the whole
   response line unparseable. Every invalid byte is replaced by U+FFFD
   on the way out; a message that is already valid UTF-8 is returned
   unchanged, allocating nothing. *)

(* Length of the well-formed UTF-8 sequence starting at [i], or 0. The
   bounds are the Unicode standard's: no overlong encodings, no
   surrogates, nothing past U+10FFFF. *)
let utf8_width (s : string) (i : int) =
  let n = String.length s in
  let byte k = Char.code (String.unsafe_get s k) in
  let cont k = k < n && byte k land 0xc0 = 0x80 in
  let b0 = byte i in
  if b0 < 0x80 then 1
  else if b0 < 0xc2 then 0            (* stray continuation, or overlong *)
  else if b0 <= 0xdf then
    (if cont (i + 1) then 2 else 0)
  else if b0 <= 0xef then
    let lo = if b0 = 0xe0 then 0xa0 else 0x80 in
    let hi = if b0 = 0xed then 0x9f else 0xbf in
    if i + 2 < n && byte (i + 1) >= lo && byte (i + 1) <= hi && cont (i + 2)
    then 3 else 0
  else if b0 <= 0xf4 then
    let lo = if b0 = 0xf0 then 0x90 else 0x80 in
    let hi = if b0 = 0xf4 then 0x8f else 0xbf in
    if i + 3 < n && byte (i + 1) >= lo && byte (i + 1) <= hi
       && cont (i + 2) && cont (i + 3)
    then 4 else 0
  else 0

let utf8_repair (s : string) =
  let n = String.length s in
  let rec valid i =
    i >= n || (let k = utf8_width s i in k > 0 && valid (i + k))
  in
  if valid 0 then s
  else begin
    let buf = Buffer.create (n + 8) in
    let rec copy i =
      if i < n then
        match utf8_width s i with
        | 0 -> Buffer.add_string buf "\xef\xbf\xbd"; copy (i + 1)
        | k -> Buffer.add_substring buf s i k; copy (i + k)
    in
    copy 0; Buffer.contents buf
  end

(* -------------------------------------------------------------------- *)
(* JSON schema fragments for the tool declarations. *)
module Schema = struct
  let str ?description () =
    `Assoc (("type", `String "string")
            :: (match description with
                | None   -> []
                | Some d -> [("description", `String d)]))

  let int ~description () =
    `Assoc [("type", `String "integer");
            ("description", `String description)]

  let bool ~description ~default () =
    `Assoc [("type", `String "boolean");
            ("description", `String description);
            ("default", `Bool default)]

  let obj ?(required = []) props =
    `Assoc ([("type", `String "object");
             ("properties", `Assoc props)]
            @ (match required with
               | [] -> []
               | _  -> [("required",
                         `List (List.map (fun s -> `String s) required))])
            @ [("additionalProperties", `Bool false)])

  (* Every tool answers with the same structured payload: the reply
     text, the engine state the call left behind, and whether it moved.

     [text] repeats [content[0].text] verbatim. The duplication is
     deliberate: Claude Code, our primary client, hands the model the
     [structuredContent] object alone and drops [content] whenever both
     are present, so a payload that lives only in [content] never
     reaches the agent. See tests/mcp/README.md. *)
  let output ?(reverted = false) () =
    let base = [
      ("text", str ~description:"the reply body -- goal state, proof \
                                 body, search results, error text; the \
                                 same string as content[0].text" ());
      ("uuid", int ~description:"engine state identifier after the call; \
                                 pass it to ec_revert to come back here" ());
      ("changed", `Assoc [("type", `String "boolean");
                          ("description",
                           `String "whether the engine state advanced")]);
    ] in
    let base =
      if not reverted then base
      else base @ [
        ("reverted",
         `Assoc [("type", `String "boolean");
                 ("description",
                  `String "set when the phrase failed and the engine was \
                           rolled back to its pre-call state")]);
      ]
    in
    `Assoc [("type", `String "object");
            ("properties", `Assoc base);
            ("required", `List [`String "text"; `String "uuid";
                                `String "changed"])]
end

(* -------------------------------------------------------------------- *)
(* The static tool table, in [tools/list] order. Descriptions are
   agent-facing and track the wording of doc/llm/CLAUDE.md. *)
let tools : J.t list =
  let tool ~name ~description ~input ?(annotations = []) ~output () =
    `Assoc ([
      ("name", `String name);
      ("description", `String description);
      ("inputSchema", input);
      ("outputSchema", output);
    ] @ (match annotations with
         | [] -> []
         | _  -> [("annotations", `Assoc annotations)]))
  in [
    tool
      ~name:"ec_load"
      ~description:
        "Reset the session and compile FILE from the top, stopping after \
         the last sentence that ends on or before LINE (and column COL \
         when given). This is the entry point: every other tool needs a \
         loaded file, and tactics need the position to land inside a \
         proof. Set nosmt to weaken SMT calls while replaying a prefix \
         that was already verified, which is much faster on large files. \
         Set trace to have the reply describe the last loaded sentence as \
         BEFORE / TACTIC / AFTER / SUMMARY blocks. The reply reports \
         where compilation stopped and the resulting goal state; note the \
         uuid it returns, reverting to it is the instant way back to the \
         start of the proof."
      ~input:(Schema.obj ~required:["file"] [
        ("file", Schema.str ~description:"path to the .ec/.eca file" ());
        ("line", Schema.int
                   ~description:"stop after the last sentence ending on \
                                 or before this line; omit to compile the \
                                 whole file" ());
        ("col", Schema.int
                  ~description:"column bound within `line'; requires \
                                `line'" ());
        ("nosmt", Schema.bool
                    ~description:"weaken SMT calls while compiling the \
                                  prefix" ~default:false ());
        ("trace", Schema.bool
                    ~description:"report the proof state around the last \
                                  loaded sentence" ~default:false ());
      ])
      ~annotations:[("destructiveHint", `Bool true)]
      ~output:(Schema.output ())
      ();

    tool
      ~name:"ec_step"
      ~description:
        "Run EasyCrypt sentences -- tactics, declarations, require, \
         print, ... -- against the current session. Every complete \
         sentence in the argument is executed, in order, exactly as if \
         the text had been appended to the source file, and a single \
         reply describes the state they leave behind; sentences may \
         span several lines. Requires a file loaded with ec_load, and, \
         for tactics, an open proof. On success the reply carries the \
         new goal state; on failure the prover's error text comes back \
         with isError set, the sentences before the failing one stay \
         applied and the engine is left wherever that sentence left it \
         -- use ec_try when you want a guaranteed rollback. Successful \
         non-query phrases are recorded for ec_commit."
      ~input:(Schema.obj ~required:["phrase"] [
        ("phrase", Schema.str
                     ~description:"one or more complete EasyCrypt \
                                   sentences, each ending with `.'" ());
      ])
      ~annotations:[("destructiveHint", `Bool false);
                    ("idempotentHint", `Bool false)]
      ~output:(Schema.output ())
      ();

    tool
      ~name:"ec_try"
      ~description:
        "Like ec_step, but the engine is rolled back to the state it had \
         before the call whenever a sentence fails, including input that \
         failed only after having already advanced the proof. The \
         failure reply sets structuredContent.reverted to true, and its \
         uuid and goal text describe the restored state, not the point \
         of failure. Use this to probe a tactic without having to \
         ec_revert afterwards; use ec_step when you mean to keep \
         whatever progress the phrase makes. A successful phrase behaves \
         exactly as under ec_step and is recorded for ec_commit."
      ~input:(Schema.obj ~required:["phrase"] [
        ("phrase", Schema.str
                     ~description:"one complete EasyCrypt sentence, \
                                   ending with `.'" ());
      ])
      ~annotations:[("destructiveHint", `Bool false)]
      ~output:(Schema.output ~reverted:true ())
      ();

    tool
      ~name:"ec_goals"
      ~description:
        "Print the current proof state: the focused subgoal alone, or, \
         with all set, every open subgoal. Requires an open proof, and \
         does not advance the engine."
      ~input:(Schema.obj [
        ("all", Schema.bool
                  ~description:"print every open subgoal instead of the \
                                focused one" ~default:false ());
      ])
      ~annotations:[("readOnlyHint", `Bool true)]
      ~output:(Schema.output ())
      ();

    tool
      ~name:"ec_tree"
      ~description:
        "List the open subgoals as a tree of dotted-path labels -- [1], \
         [1.2], [2.1.1] -- showing how the splits nest, and marking the \
         focused one. Those labels are exactly what ec_focus accepts. \
         Set full for whole goal bodies rather than one-line \
         conclusions. The labels are not stable across focus changes: \
         the tree always shows the focused goal first, so re-read it \
         after every ec_focus. Does not advance the engine."
      ~input:(Schema.obj [
        ("full", Schema.bool
                   ~description:"print full goal bodies instead of \
                                 one-line conclusions" ~default:false ());
      ])
      ~annotations:[("readOnlyHint", `Bool true)]
      ~output:(Schema.output ())
      ();

    tool
      ~name:"ec_focus"
      ~description:
        "Rotate the focus onto the subgoal at dotted path PATH, as \
         printed by ec_tree (\"2\", \"1.2\", \"1.1.1\"). The path walks \
         the tree, one component per level, so a single integer selects \
         the k-th TOP-LEVEL node -- not the k-th open goal: with four \
         goals nested under two top-level nodes, \"3\" is out of range. \
         Selecting a node that is an internal frame rather than a leaf \
         goal is an error. The special value \"next\" is a different \
         operation, not a synonym for \"2\": it moves to the next open \
         subgoal in ec_goals-with-all order, whatever the nesting, and \
         the two coincide only when the tree is flat. Subsequent \
         tactics act on the focused goal."
      ~input:(Schema.obj ~required:["path"] [
        ("path", Schema.str
                   ~description:"\"N\", a dotted path \"N1.N2...\", or \
                                 \"next\"" ());
      ])
      ~annotations:[("destructiveHint", `Bool false)]
      ~output:(Schema.output ())
      ();

    tool
      ~name:"ec_undo"
      ~description:
        "Undo the last engine step, returning to the immediately \
         preceding state. The ec_commit transcript is trimmed to match. \
         Fails when there is nothing left to undo."
      ~input:(Schema.obj [])
      ~annotations:[("destructiveHint", `Bool false)]
      ~output:(Schema.output ())
      ();

    tool
      ~name:"ec_revert"
      ~description:
        "Return the session to an earlier state, named either by a uuid \
         reported in some previous structuredContent or by a name given \
         to ec_checkpoint. Reverting is instant, unlike re-running \
         ec_load, so going back to the uuid ec_load returned is the cheap \
         way to restart a proof from scratch after a failed experiment. \
         The ec_commit transcript is trimmed to match."
      ~input:(Schema.obj ~required:["target"] [
        ("target", Schema.str
                     ~description:"a uuid (as a decimal string) or a \
                                   checkpoint name" ());
      ])
      ~annotations:[("destructiveHint", `Bool true)]
      ~output:(Schema.output ())
      ();

    tool
      ~name:"ec_checkpoint"
      ~description:
        "Record the current uuid under NAME, so that ec_revert can \
         address it by name later. Worth doing before a branching \
         experiment, when carrying the bare uuid around is awkward. Does \
         not change the proof state."
      ~input:(Schema.obj ~required:["name"] [
        ("name", Schema.str ~description:"checkpoint name" ());
      ])
      ~annotations:[("readOnlyHint", `Bool true)]
      ~output:(Schema.output ())
      ();

    tool
      ~name:"ec_commit"
      ~description:
        "Emit the phrases recorded since the last ec_load as a proof \
         body, with bullets inserted at every multi-child split: the \
         result compiles under `pragma +strict_bullets' and can be \
         pasted straight into the source file. Queries (search, print, \
         locate, ec_search) are never recorded, so looking things up \
         mid-proof does not pollute the body, and ec_undo / ec_revert \
         trim the transcript. Still works after `qed.'. Does not change \
         the proof state."
      ~input:(Schema.obj [])
      ~annotations:[("readOnlyHint", `Bool true)]
      ~output:(Schema.output ())
      ();

    tool
      ~name:"ec_search"
      ~description:
        "Search the environment for lemmas matching an EasyCrypt search \
         pattern. This is pattern syntax, not keyword search: use _ as \
         the wildcard, as in \"(fdom _)\", \"(_ %/ _)\" or \"(mu _ _) (_ \
         <= _)\". Requires a loaded file. The query neither advances the \
         proof nor enters the ec_commit transcript."
      ~input:(Schema.obj ~required:["pattern"] [
        ("pattern", Schema.str
                      ~description:"an EasyCrypt search pattern" ());
      ])
      ~annotations:[("readOnlyHint", `Bool true)]
      ~output:(Schema.output ())
      ();
  ]

(* -------------------------------------------------------------------- *)
(* Argument access. Everything here reports through [Invalid_params]:
   these are failures to satisfy the declared input schema, which the
   spec classifies as protocol errors, not tool-execution errors. *)
module Args = struct
  let of_params (params : J.t option) =
    match params with
    | None | Some `Null -> []
    | Some (`Assoc fields) -> fields
    | Some _ -> raise (Invalid_params "`params' must be an object")

  let arguments (params : J.t option) =
    match List.assoc_opt "arguments" (of_params params) with
    | None | Some `Null -> []
    | Some (`Assoc fields) -> fields
    | Some _ -> raise (Invalid_params "`arguments' must be an object")

  let bad tool name expected =
    raise (Invalid_params
      (Printf.sprintf "%s: `%s' must be %s" tool name expected))

  let string_req tool args name =
    match List.assoc_opt name args with
    | Some (`String s) -> s
    | Some _ -> bad tool name "a string"
    | None ->
      raise (Invalid_params
        (Printf.sprintf "%s: missing required argument `%s'" tool name))

  let bool_opt tool args name ~default =
    match List.assoc_opt name args with
    | None | Some `Null -> default
    | Some (`Bool b)    -> b
    | Some _            -> bad tool name "a boolean"

  let int_opt tool args name =
    match List.assoc_opt name args with
    | None | Some `Null -> None
    | Some (`Int i)     -> Some i
    | Some _            -> bad tool name "an integer"
end

(* The [ec_focus] path is a string in the schema, so its shape is ours
   to check: "next", or a dotted sequence of positive integers. Only
   "next" is MCP's own -- the REPL spells it as a separate command --
   so the path itself goes through the shared parser. *)
let focus_target (arg : string) =
  if String.lowercase_ascii arg = "next" then `Next
  else
    match EcLlmCore.parse_goal_path ~what:"ec_focus" arg with
    | Ok path   -> `Path path
    | Error msg -> raise (Invalid_params msg)

(* -------------------------------------------------------------------- *)
let run ~relocdir ~boot ~projini (mcpopts : EcOptions.mcp_option) =
  if mcpopts.mcpo_help then begin
    print_usage ();
    exit 0
  end;

  (* stdout carries the protocol and nothing else. Rather than trust
     every code path under the engine to stay silent, keep a private
     descriptor for the protocol and point the process's stdout at
     stderr, so a stray [print_string] anywhere lands in the client's
     log instead of corrupting the message stream. *)
  let wire =
    let fd = Unix.dup Unix.stdout in
    Unix.dup2 Unix.stderr Unix.stdout;
    Unix.out_channel_of_descr fd
  in

  let prvopts = mcpopts.mcpo_provers in

  let st =
    try EcLlmCore.create ~relocdir ~boot ~projini ~prvopts
    with EcLlmCore.Init_error msg ->
      Printf.eprintf "%s\n%!" msg;
      exit 1
  in

  (* ------------------------------------------------------------------ *)
  (* The wire: one JSON value per line, flushed at once. Yojson escapes
     newlines inside strings, so a message never contains one, as the
     stdio transport requires. *)
  let module Wire = struct
    (* Repair every string in the message rather than the reply text
       alone: this is the one point every byte leaves through, so no
       future tool or error path can put invalid UTF-8 on the wire by
       forgetting to sanitize. *)
    (* Only the constructors we build are named: [Tuple] and [Variant]
       are non-standard extensions we never emit, and yojson 3 dropped
       them from the type, so naming them here would not compile there. *)
    let rec repair (msg : J.t) : J.t =
      match msg with
      | `String s -> `String (utf8_repair s)
      | `List l   -> `List (List.map repair l)
      | `Assoc l  -> `Assoc (List.map (fun (k, v) -> (k, repair v)) l)
      | msg       -> msg

    let send (msg : J.t) =
      output_string wire (J.to_string (repair msg));
      output_char wire '\n';
      flush wire

    let result id (result : J.t) =
      send (`Assoc [
        ("jsonrpc", `String "2.0");
        ("id", id);
        ("result", result);
      ])

    let error ?data id code message =
      send (`Assoc [
        ("jsonrpc", `String "2.0");
        ("id", id);
        ("error", `Assoc ([
           ("code", `Int code);
           ("message", `String message);
         ] @ (match data with None -> [] | Some d -> [("data", d)])));
      ])
  end in

  (* ------------------------------------------------------------------ *)
  (* Rendering [EcLlmCore] outcomes as tool results. *)
  let module Result_of = struct
    let content text =
      `List [`Assoc [("type", `String "text"); ("text", `String text)]]

    (* [text] appears twice, once in each half of the result, and the
       two copies are the same string by construction. Clients that read
       [content] are served by the first; Claude Code, which drops
       [content] as soon as [structuredContent] is present, is served
       only by the second. *)
    let make ~text ~uuid ~changed ~is_error ~extra =
      `Assoc [
        ("content", content text);
        ("structuredContent",
         `Assoc ([("text", `String text);
                  ("uuid", `Int uuid);
                  ("changed", `Bool changed)] @ extra));
        ("isError", `Bool is_error);
      ]

    (* The notice buffer holds whatever the engine said while the
       operation ran; it precedes the body, as it does in the REPL. *)
    let join notices body =
      if notices = "" then body
      else if body = "" then notices
      else if String.length notices > 0
           && notices.[String.length notices - 1] = '\n'
      then notices ^ body
      else notices ^ "\n" ^ body

    let reply (r : EcLlmCore.reply) =
      let body =
        match r.EcLlmCore.body with
        | EcLlmCore.Text body -> body
        | EcLlmCore.Goals     -> EcLlmCore.current_goals st
      in
      make
        ~text:(join r.EcLlmCore.notices body)
        ~uuid:r.EcLlmCore.uuid
        ~changed:r.EcLlmCore.changed
        ~is_error:false ~extra:[]

    (* A prover error is data, not a protocol failure: it comes back as
       a successful response the agent can read and act on. *)
    let failure ~extra (f : EcLlmCore.failure) =
      let body =
        if f.EcLlmCore.goals = "" then f.EcLlmCore.message
        else f.EcLlmCore.message ^ "\n" ^ f.EcLlmCore.goals
      in
      make
        ~text:(join f.EcLlmCore.notices body)
        ~uuid:f.EcLlmCore.uuid
        ~changed:f.EcLlmCore.changed
        ~is_error:true ~extra:(extra f)

    let outcome ?(extra = fun _ -> []) = function
      | Ok r      -> reply r
      | Error f   -> failure ~extra f
  end in

  (* ------------------------------------------------------------------ *)
  (* Tool dispatch.

     Argument checking happens here, before the engine is touched: the
     core trusts what it is handed, [EcLlmCore.load] resetting the
     session before it so much as opens the file. Schema violations
     raise [Invalid_params] and become JSON-RPC errors; checks a tool
     makes on its own behalf raise [Tool_error] and become [isError]
     results. The checks the REPL makes too live in [EcLlmCore] and are
     only reported here. *)

  (* Set by a phrase that ends the session ([exit.]): the response still
     goes out, then the process stops. *)
  let quitting = ref false in

  let answer ?(extra = fun _ -> []) = function
    | EcLlmCore.Quit ->
      quitting := true;
      Result_of.make ~text:"session terminated"
        ~uuid:(EcLlmCore.uuid st) ~changed:false ~is_error:false ~extra:[]
    | EcLlmCore.Done outcome ->
      Result_of.outcome ~extra outcome
  in

  let call_tool (name : string) (params : J.t option) : J.t =
    let args = Args.arguments params in
    let outcome = Result_of.outcome in

    match name with
    | "ec_load" ->
      let file  = Args.string_req name args "file" in
      let line  = Args.int_opt    name args "line" in
      let col   = Args.int_opt    name args "col"  in
      let nosmt = Args.bool_opt   name args "nosmt" ~default:false in
      let trace = Args.bool_opt   name args "trace" ~default:false in
      if line = None && col <> None then
        raise (Invalid_params "ec_load: `col' requires `line'");
      (match EcLlmCore.check_load_file file with
       | Ok ()     -> ()
       | Error msg -> raise (Tool_error msg));
      let upto = Option.map (fun line -> (line, col)) line in
      outcome (EcLlmCore.load st ~file ~upto ~nosmt ~trace)

    | "ec_step" ->
      answer (EcLlmCore.step st (Args.string_req name args "phrase"))

    | "ec_try" ->
      answer
        ~extra:(fun (f : EcLlmCore.failure) ->
          [("reverted", `Bool f.EcLlmCore.reverted)])
        (EcLlmCore.try_step st (Args.string_req name args "phrase"))

    | "ec_goals" ->
      outcome (EcLlmCore.goals st
        ~all:(Args.bool_opt name args "all" ~default:false))

    | "ec_tree" ->
      outcome (EcLlmCore.tree st
        ~all:(Args.bool_opt name args "full" ~default:false))

    | "ec_focus" ->
      outcome (EcLlmCore.focus st
        (focus_target (Args.string_req name args "path")))

    | "ec_undo" ->
      outcome (EcLlmCore.undo st)

    | "ec_revert" ->
      outcome (EcLlmCore.revert st (Args.string_req name args "target"))

    | "ec_checkpoint" ->
      outcome (EcLlmCore.checkpoint st
        ~name:(Args.string_req name args "name"))

    | "ec_commit" ->
      outcome (EcLlmCore.commit st)

    | "ec_search" ->
      outcome (EcLlmCore.search st
        ~pattern:(Args.string_req name args "pattern"))

    | _ ->
      raise (Invalid_params (Printf.sprintf "unknown tool: %s" name))
  in

  (* ------------------------------------------------------------------ *)
  (* Requests. *)
  let initialize (params : J.t option) =
    let requested =
      match List.assoc_opt "protocolVersion" (Args.of_params params) with
      | Some (`String v) -> Some v
      | _                -> None
    in
    (* Spec: answer with the requested version when we speak it,
       otherwise with the latest one we do speak. *)
    let negotiated =
      match requested with
      | Some v when List.mem v protocol_supported -> v
      | _ -> protocol_latest
    in
    `Assoc [
      ("protocolVersion", `String negotiated);
      ("capabilities", `Assoc [("tools", `Assoc [])]);
      ("serverInfo", `Assoc [
         ("name", `String server_name);
         ("version", `String server_version);
       ]);
    ]
  in

  let request id (meth : string) (params : J.t option) =
    try
      match meth with
      | "initialize" ->
        Wire.result id (initialize params)
      | "ping" ->
        Wire.result id (`Assoc [])
      | "tools/list" ->
        (* The tool set is static and short: no pagination, and a
           [cursor] argument is simply ignored. *)
        Wire.result id (`Assoc [("tools", `List tools)])
      | "tools/call" ->
        let name =
          match List.assoc_opt "name" (Args.of_params params) with
          | Some (`String s) -> s
          | Some _ -> raise (Invalid_params "`name' must be a string")
          | None   -> raise (Invalid_params "missing tool `name'")
        in
        let result =
          try call_tool name params with
          | Tool_error msg ->
            Result_of.make ~text:msg ~uuid:(EcLlmCore.uuid st)
              ~changed:false ~is_error:true ~extra:[]
        in
        Wire.result id result;
        if !quitting then exit 0
      | _ ->
        Wire.error id e_method_not_found
          (Printf.sprintf "method not found: %s" meth)
    with
    | Invalid_params msg -> Wire.error id e_invalid_params msg
  in

  (* Notifications never get a reply, whatever they are. The ones the
     spec has us tolerate ([initialized], [cancelled],
     [roots/list_changed]) are no-ops here, and so is anything else:
     cancellation cannot preempt a synchronous tool call. *)
  let notification (_ : string) (_ : J.t option) = () in

  (* ------------------------------------------------------------------ *)
  let dispatch (msg : J.t) =
    match msg with
    | `List _ ->
      (* Batching was removed from the protocol in revision 2025-06-18
         and has not come back. *)
      Wire.error `Null e_invalid_request
        "JSON-RPC batches are not supported by this protocol revision"
    | `Assoc fields ->
      let params = List.assoc_opt "params" fields in
      let id =
        (* A message is a request exactly when it carries a usable id;
           MCP forbids a null id, so we read one as "no id" and stay
           silent rather than answer a malformed request. *)
        match List.assoc_opt "id" fields with
        | None | Some `Null -> None
        | Some id           -> Some id
      in
      begin match List.assoc_opt "method" fields, id with
      | Some (`String meth), Some id -> request id meth params
      | Some (`String meth), None    -> notification meth params
      | Some _, Some id ->
        Wire.error id e_invalid_request "`method' must be a string"
      | Some _, None -> ()
      | None, Some id ->
        Wire.error id e_invalid_request "missing `method'"
      | None, None -> ()
      end
    | _ ->
      Wire.error `Null e_invalid_request
        "a JSON-RPC message must be an object"
  in

  (* ------------------------------------------------------------------ *)
  (* Main loop. A blank line is not a message; skipping it keeps a
     client's trailing newline from drawing a parse error. *)
  begin try while true do
    let line = input_line stdin in
    if String.trim line <> "" then
      match J.from_string line with
      | exception _ ->
        Wire.error `Null e_parse_error "invalid JSON"
      | msg -> dispatch msg
  done with End_of_file -> () end;

  exit 0
