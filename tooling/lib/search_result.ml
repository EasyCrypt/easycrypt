type hit = {
  qname      : string;
  kind       : string;
  short_name : string;
  signature  : string;
}

(* True iff [s] starts with "(* " and ends with " *)" — EC's qname
   marker. Returns the stripped qname on success. *)
let qname_of_marker s =
  let n = String.length s in
  if n >= 6
     && String.sub s 0 3 = "(* "
     && String.sub s (n - 3) 3 = " *)"
  then Some (String.sub s 3 (n - 6))
  else None

(* True iff [s] opens a declaration. EC's search emits hits two
   ways: theory-qualified ones get a `(* qname *)` marker on the
   preceding line; directly-accessible ones come with no marker,
   starting directly with `lemma foo:`, `axiom bar:`, etc. We
   recognize declaration heads by the first token being one of
   a known set of decl keywords. Returns the short name or [None]
   if the line doesn't look like a decl-head. *)
let is_decl_head s =
  let s = String.trim s in
  if s = "" then None
  else
    let len = String.length s in
    let rec tok_end i =
      if i >= len then i
      else match s.[i] with
      | ' ' | '\t' -> i
      | _ -> tok_end (i + 1)
    in
    let k_end = tok_end 0 in
    let kind = String.sub s 0 k_end in
    match kind with
    | "lemma" | "axiom" | "operator" | "op" | "abbrev"
    | "predicate" | "pred" | "type" | "module"
    | "theorem" ->
      (* Skip whitespace, grab the next token (the short name),
         stopping at whitespace, colon, open-paren, or bracket. *)
      let rec skip_ws i =
        if i >= len then i
        else match s.[i] with
        | ' ' | '\t' -> skip_ws (i + 1)
        | _ -> i
      in
      let n_start = skip_ws k_end in
      let rec n_end i =
        if i >= len then i
        else match s.[i] with
        | ':' | ' ' | '\t' | '(' | '[' -> i
        | _ -> n_end (i + 1)
      in
      let ne = n_end n_start in
      if ne > n_start then Some (String.sub s n_start (ne - n_start))
      else None
    | _ -> None

(* Group boundaries: either a `(* qname *)` marker OR a line that
   starts a new declaration (lemma / axiom / operator / ...). If
   a decl-head arrives while another group is open, that ends the
   old group and starts a new one — EC emits unmarked decls back
   to back for directly-accessible lemmas, and we need to split
   them correctly rather than piling them into one blob. *)

type start_kind =
  | Start_marker of string  (* qname from the marker *)
  | Start_implicit of string  (* short-name decl-head *)
  | Continuation

let classify_line line =
  match qname_of_marker line with
  | Some qn -> Start_marker qn
  | None ->
    match is_decl_head line with
    | Some short -> Start_implicit short
    | None -> Continuation

let group_notices notices =
  let groups = ref [] in
  let current : (string * string list) option ref = ref None in
  let flush () =
    match !current with
    | None -> ()
    | Some (qn, lines) ->
      groups := (qn, List.rev lines) :: !groups;
      current := None
  in
  List.iter
    (fun line ->
       match classify_line line with
       | Start_marker qn ->
         flush ();
         current := Some (qn, [])
       | Start_implicit short ->
         (* The marker line (if any) was the PREVIOUS line; it
            opened an empty group. If current is an empty group
            opened by a marker, this decl-head is its body — don't
            start a new group. Otherwise, flush and start implicit. *)
         (match !current with
          | Some (qn, []) ->
            current := Some (qn, [ line ])
          | _ ->
            flush ();
            current := Some (short, [ line ]))
       | Continuation ->
         (match !current with
          | None -> ()  (* noise before any group; drop *)
          | Some (qn, lines) ->
            current := Some (qn, line :: lines)))
    notices;
  flush ();
  List.rev !groups

(* Extract (kind, short_name) from a declaration body like
   "lemma addz0:" or "operator (<=) : int -> int -> bool". First
   whitespace-separated token is kind; second (up to first colon or
   space) is the short name. *)
let split_kind_and_name body =
  let body = String.trim body in
  if body = "" then ("", "")
  else
    let len = String.length body in
    let kind_end =
      let rec scan i =
        if i >= len then i
        else match body.[i] with
        | ' ' | '\t' -> i
        | _ -> scan (i + 1)
      in
      scan 0
    in
    let kind = String.sub body 0 kind_end in
    let rec skip_ws i =
      if i >= len then i
      else match body.[i] with
      | ' ' | '\t' -> skip_ws (i + 1)
      | _ -> i
    in
    let name_start = skip_ws kind_end in
    let name_end =
      let rec scan i =
        if i >= len then i
        else match body.[i] with
        | ':' | ' ' | '\t' -> i
        | _ -> scan (i + 1)
      in
      scan name_start
    in
    let short_name =
      if name_end > name_start then String.sub body name_start (name_end - name_start)
      else ""
    in
    (kind, short_name)

let of_notices notices =
  List.map
    (fun (qname, body_lines) ->
       let signature =
         body_lines
         |> List.map String.trim
         |> List.filter (fun s -> s <> "")
         |> String.concat " "
       in
       let (kind, short_name) = split_kind_and_name signature in
       { qname; kind; short_name; signature })
    (group_notices notices)
