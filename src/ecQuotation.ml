(* -------------------------------------------------------------------- *)
(* Black-box quotation preprocessor support.                            *)
(*                                                                      *)
(* Quotations are either fragmented (generating a fragment of a         *)
(* sentence) or whole (generating a sequence of sentences). See         *)
(* ecLexer.mll for the syntax, and see doc/quotations.rst for more      *)
(* information.                                                         *)

(* EcIo expands a quotation by shelling out to an external              *)
(* handler over stdin/stdout, re-lexes the produced EC source, and      *)
(* remaps every position back into the original source file using the   *)
(* segment map returned by the handler.                                 *)
(* -------------------------------------------------------------------- *)
open EcUtils

module L = Lexing

(* -------------------------------------------------------------------- *)
(* Raw quotation as produced by the lexer.                              *)
(*                                                                      *)
(* [q_bpos] is the [Lexing.position] of the first byte of the body in   *)
(* the original file; its [pos_cnum] is the absolute body-start offset  *)
(* referred to as [q0] in the design.                                   *)
type quotation = {
  q_name  : string;
  q_body  : string;
  q_debug : bool;        (* should expansion be printed for user?   *)
  q_frag  : bool;        (* quotation fragment?                     *)
  q_bpos  : L.position;  (* position of body start in original file *)
  q_epos  : L.position;  (* position just after the closing "%}"    *)
}

(* -------------------------------------------------------------------- *)
exception QuotationError of EcLocation.t * string

let () =
  EcPException.register (fun fmt exn ->
    match exn with
    | QuotationError (_, msg) ->
        Format.fprintf fmt "quotation error: %s" msg
    | _ -> raise exn)

let qloc (q : quotation) : EcLocation.t =
  EcLocation.make q.q_bpos q.q_epos

let error (q : quotation) msg =
  raise (QuotationError (qloc q, msg))

(* -------------------------------------------------------------------- *)
(* A source-map segment.  Offsets are relative to the start of their    *)
(* respective buffers: [out] into the expanded EC source, [in] into the *)
(* quotation body.                                                      *)
type segment = {
  s_out : int * int;          (* [ob, oe) in expanded output *)
  s_in  : int * int;          (* [ib, ie) in original body   *)
  s_verbatim : bool;          (* true => char-for-char (oe-ob = ie-ib) *)
}

type segmap = {
  sm_segments : segment array;   (* sorted by s_out start *)
  sm_body_len : int;             (* length of the original body *)
}

(* Coarse fallback: the whole expansion maps to the whole body. *)
let coarse_segmap ~(body_len : int) : segmap =
  { sm_segments =
      [| { s_out = (0, max_int);
           s_in  = (0, body_len);
           s_verbatim = false } |];
    sm_body_len = body_len; }

(* -------------------------------------------------------------------- *)
(* Parse the JSON source-map section emitted by the handler.            *)
let segmap_of_json ~(body_len : int) (json : Yojson.Safe.t) : segmap =
  let open Yojson.Safe.Util in
  let pair name j =
    match to_list (member name j) with
    | [a; b] -> (to_int a, to_int b)
    | _ -> failwith (Printf.sprintf "bad %s range in source map" name)
  in
  let seg j =
    let (ob, oe) = pair "out" j in
    let (ib, ie) = pair "in"  j in
    let kind =
      match member "kind" j with
      | `String s -> s
      | `Null     -> "verbatim"
      | _         -> failwith "bad kind in source map"
    in
    { s_out = (ob, oe);
      s_in  = (ib, ie);
      s_verbatim = (kind = "verbatim" && oe - ob = ie - ib); }
  in
  let segs = List.map seg (to_list (member "segments" json)) in
  let segs = List.sort (fun a b -> compare (fst a.s_out) (fst b.s_out)) segs in
  match segs with
  | [] -> coarse_segmap ~body_len
  | _  -> { sm_segments = Array.of_list segs; sm_body_len = body_len; }

(* -------------------------------------------------------------------- *)
(* Reverse mapping: an offset [o] in the expanded output -> an absolute *)
(* offset in the original file.  [q0] is the body-start offset.         *)
let remap_offset (sm : segmap) ~(q0 : int) (o : int) : int =
  let n = Array.length sm.sm_segments in
  (* find the last segment whose out-start <= o *)
  let rec find lo hi best =
    if lo > hi then best else
      let mid = (lo + hi) / 2 in
      let (ob, _) = sm.sm_segments.(mid).s_out in
      if ob <= o then find (mid + 1) hi mid else find lo (mid - 1) best
  in
  if n = 0 then q0 else
  let idx = find 0 (n - 1) 0 in
  let s = sm.sm_segments.(idx) in
  let (ob, oe) = s.s_out and (ib, ie) = s.s_in in
  let in_off =
    if s.s_verbatim && o >= ob && o < oe then
      ib + (o - ob)
    else
      (* synthesized / out-of-range: collapse to the originating in-span,
         biased to the start so error markers land at the responsible region *)
      if o <= ob then ib
      else if o >= oe then ie
      else ib
  in
  q0 + (max 0 (min sm.sm_body_len in_off))

(* -------------------------------------------------------------------- *)
(* Line-start table of the ORIGINAL file, to turn an absolute offset    *)
(* into a (line, bol) pair for a Lexing.position.  Built lazily per     *)
(* original filename and cached.                                        *)
type linetab = int array        (* bol offset of each line, line 1 at idx 0 *)

let linetab_cache : (string, linetab) Hashtbl.t = Hashtbl.create 0

let build_linetab (fname : string) : linetab option =
  try
    let ic = open_in_bin fname in
    let len = in_channel_length ic in
    let data = really_input_string ic len in
    close_in ic;
    let bols = ref [0] in
    String.iteri (fun i c -> if c = '\n' then bols := (i + 1) :: !bols) data;
    Some (Array.of_list (List.rev !bols))
  with _ -> None

let linetab (fname : string) : linetab option =
  match Hashtbl.find_opt linetab_cache fname with
  | Some t -> Some t
  | None ->
      match build_linetab fname with
      | None -> None
      | Some t -> Hashtbl.replace linetab_cache fname t; Some t

(* (line, bol) for an absolute offset using the original file's table. *)
let line_of_offset (fname : string) (off : int) : int * int =
  match linetab fname with
  | None -> (1, 0)
  | Some tab ->
      let n = Array.length tab in
      let rec find lo hi best =
        if lo > hi then best else
          let mid = (lo + hi) / 2 in
          if tab.(mid) <= off then find (mid + 1) hi mid else find lo (mid - 1) best
      in
      let idx = find 0 (n - 1) 0 in
      (idx + 1, tab.(idx))

(* -------------------------------------------------------------------- *)
(* Turn an expanded-output offset into a remapped Lexing.position that  *)
(* refers into the original file.                                       *)
let remap_position (sm : segmap) (q : quotation) (o : int) : L.position =
  let q0 = q.q_bpos.L.pos_cnum in
  let abs = remap_offset sm ~q0 o in
  let (lnum, bol) = line_of_offset q.q_bpos.L.pos_fname abs in
  { L.pos_fname = q.q_bpos.L.pos_fname;
    L.pos_lnum  = lnum;
    L.pos_bol   = bol;
    L.pos_cnum  = abs; }

(* -------------------------------------------------------------------- *)
(* Sentinel filename for the expanded buffer (Mechanism B).             *)
let sentinel_fname (q : quotation) : string =
  Printf.sprintf "<quotation:%s@%d>" q.q_bpos.L.pos_fname q.q_bpos.L.pos_cnum

let is_sentinel (fname : string) : bool =
  let prefix = "<quotation:" in
  let pn = String.length prefix in
  String.length fname >= pn && String.sub fname 0 pn = prefix

(* -------------------------------------------------------------------- *)
(* Quotations run arbitrary external programs, so the feature is OFF by   *)
(* default and must be enabled explicitly by the user (a command-line     *)
(* flag or an environment variable).  It is deliberately NOT enableable   *)
(* from easycrypt.project: that file ships inside the checked-out tree,   *)
(* so letting it turn the feature on would defeat the safeguard.  While   *)
(* disabled, encountering a quotation is a hard error -- never a silent   *)
(* skip or a silent execution.                                            *)
let enabled : bool ref = ref false

let set_enabled (b : bool) : unit =
  enabled := b

(* -------------------------------------------------------------------- *)
(* Registry of handler commands declared in easycrypt.project (or via    *)
(* the API).  Populated at startup, consulted by [resolve_command].      *)
let registry : (string, string) Hashtbl.t = Hashtbl.create 0

let register ~(name : string) ~(command : string) : unit =
  Hashtbl.replace registry name command

(* -------------------------------------------------------------------- *)
(* Handler resolution.  In order:                                        *)
(*   1. a binding from easycrypt.project (the registry);                 *)
(*   2. environment variable EC_QUOTE_<NAME> (uppercased name);          *)
(*   3. environment variable EC_QUOTE_CMD (catch-all);                   *)
(*   4. an executable [handlers/<name>] (optionally with a known script  *)
(*      extension) sitting next to the source file -- this makes a test  *)
(*      directory self-contained, with no environment to set up.         *)
let resolve_command (q : quotation) : string option =
  let name = q.q_name in
  match Hashtbl.find_opt registry name with
  | Some _ as c -> c
  | None ->
  match Sys.getenv_opt ("EC_QUOTE_" ^ String.uppercase_ascii name) with
  | Some _ as c -> c
  | None ->
  match Sys.getenv_opt "EC_QUOTE_CMD" with
  | Some _ as c -> c
  | None ->
      let dir = Filename.dirname q.q_bpos.L.pos_fname in
      let candidates =
        List.map (Filename.concat (Filename.concat dir "handlers"))
          [name; name ^ ".py"; name ^ ".sh"]
      in
      List.find_opt
        (fun p -> try Unix.access p [Unix.X_OK]; true with _ -> false)
        candidates

(* -------------------------------------------------------------------- *)
(* Run the external handler.  Returns (expanded_source, segmap).        *)
let run (q : quotation) : string * segmap =
  if not !enabled then
    error q
      "quotations are disabled; they run external programs and must be \
       enabled explicitly with --enable-quotations (or EC_ENABLE_QUOTATIONS=1)";
  let cmd =
    match resolve_command q with
    | Some c -> c
    | None ->
        error q (Printf.sprintf
          "no handler bound for quotation '%s' (set EC_QUOTE_%s, EC_QUOTE_CMD, \
           or provide handlers/%s next to the source file)"
          q.q_name (String.uppercase_ascii q.q_name) q.q_name)
  in
  let header =
    Printf.sprintf "#ec-quote v1 name=%s file=%s line=%d col=%d off=%d\n"
      q.q_name q.q_bpos.L.pos_fname
      q.q_bpos.L.pos_lnum
      (q.q_bpos.L.pos_cnum - q.q_bpos.L.pos_bol)
      q.q_bpos.L.pos_cnum
  in
  let (ic, oc) = Unix.open_process cmd in
  let raw =
    try
      output_string oc header;
      output_string oc q.q_body;
      close_out oc;
      let buf = Buffer.create 1024 in
      let chunk = Bytes.create 4096 in
      let rec loop () =
        let n = input ic chunk 0 (Bytes.length chunk) in
        if n > 0 then (Buffer.add_subbytes buf chunk 0 n; loop ())
      in
      loop ();
      Buffer.contents buf
    with e ->
      ignore (Unix.close_process (ic, oc));
      error q (Printf.sprintf "handler '%s' failed: %s" cmd (Printexc.to_string e))
  in
  let status = Unix.close_process (ic, oc) in
  (match status with
   | Unix.WEXITED 0 -> ()
   | Unix.WEXITED n -> error q (Printf.sprintf "handler exited with code %d:\n%s" n raw)
   | Unix.WSIGNALED n -> error q (Printf.sprintf "handler killed by signal %d" n)
   | Unix.WSTOPPED n -> error q (Printf.sprintf "handler stopped by signal %d" n));
  (* The handler writes a single JSON object on stdout:
       { "expanded": <string>, "segments": [ ... ] }
     [expanded] is the replacement source; [segments] (optional) is the
     source map -- absent or unparsable segments fall back to a coarse map. *)
  let body_len = String.length q.q_body in
  let json =
    try Yojson.Safe.from_string raw
    with _ ->
      error q "handler output is not valid JSON \
               (expected { \"expanded\": ..., \"segments\": ... })"
  in
  let expanded =
    match Yojson.Safe.Util.member "expanded" json with
    | `String s -> s
    | _ -> error q "handler output has no string \"expanded\" field"
  in
  let sm =
    try segmap_of_json ~body_len json
    with _ -> coarse_segmap ~body_len
  in
  (expanded, sm)
