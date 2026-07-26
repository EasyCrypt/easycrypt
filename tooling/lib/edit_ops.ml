(* See .mli for contract and rationale. *)

type error = Error.t

let executables_of (doc : Document.t) =
  List.filter
    (fun (sn : Document.sentence) -> sn.parsed.cls <> `Meta)
    doc.sentences

(* Splice offset for an insert-before-cursor operation: the start of
   the executable sentence at [idx], or end-of-file when idx is past
   the last executable. Post-addition-16 this is just the parsed
   [start_offset] — no whitespace scan needed. *)
let insert_offset (doc : Document.t) ~before_executable_index =
  let executables = executables_of doc in
  match List.nth_opt executables before_executable_index with
  | Some (sn : Document.sentence) -> sn.parsed.start_offset
  | None -> String.length doc.source

(* Compose the insert splice: add a leading newline if the preceding
   byte isn't one, and a trailing newline if the content doesn't end
   in one and the following byte isn't one. Keeps blank-line
   structure around the splice sane without demanding clients
   pre-format their content. *)
let splice_insert ~source ~at ~content =
  let len = String.length source in
  let at = max 0 (min len at) in
  let before = String.sub source 0 at in
  let after  = String.sub source at (len - at) in
  let needs_leading_nl = at > 0 && before.[at - 1] <> '\n' in
  let content_ends_nl =
    String.length content > 0
    && content.[String.length content - 1] = '\n'
  in
  let needs_trailing_nl =
    after <> "" && after.[0] <> '\n' && not content_ends_nl
  in
  String.concat ""
    [ before
    ; (if needs_leading_nl then "\n" else "")
    ; content
    ; (if needs_trailing_nl then "\n" else "")
    ; after
    ]

let reparse session doc new_source =
  Document.parse session
    ~uri:doc.Document.uri
    ~version:(doc.version + 1)
    ~source:new_source

let insert_before ~session ~doc ~before_executable_index ~content =
  let at = insert_offset doc ~before_executable_index in
  let new_source = splice_insert ~source:doc.Document.source ~at ~content in
  reparse session doc new_source

let replace ~session ~doc ~target ~content =
  let source = doc.Document.source in
  let len = String.length source in
  let s = max 0 (min len target.Document.parsed.start_offset) in
  let e = max s (min len target.Document.parsed.end_offset) in
  let new_source =
    String.sub source 0 s ^ content ^ String.sub source e (len - e)
  in
  reparse session doc new_source

let delete ~session ~doc ~target =
  let source = doc.Document.source in
  let len = String.length source in
  let s = max 0 (min len target.Document.parsed.start_offset) in
  let e0 = max s (min len target.Document.parsed.end_offset) in
  (* Consume the sentence's terminating newline if present, so the
     line structure doesn't leave an empty line behind. *)
  let e = if e0 < len && source.[e0] = '\n' then e0 + 1 else e0 in
  let new_source =
    String.sub source 0 s ^ String.sub source e (len - e)
  in
  reparse session doc new_source
