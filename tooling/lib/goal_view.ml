type hyp_kind =
  | Var
  | Mem
  | Modty
  | Hyp
  | Abs_st
  | Other of string

type hypothesis = {
  name : string;
  kind : hyp_kind;
  pp   : string;
}

(* Conclusion tree (UPSTREAM #23). v0 emits two node kinds:
   [Cn_pp] for opaque text leaves and [Cn_judgment] for the outermost
   PHL judgment when present. v1+ extends the variant with
   propositional connectives (implies, and, or, forall, ...); v_full
   makes sub-trees structured. The OCaml type is the source of truth;
   [conclusion_pp] is a derived flat-text view computed via
   [to_pp_text]. *)
type conclusion_node =
  | Cn_pp       of string
  | Cn_judgment of judgment_node
  | Cn_stmt     of stmt_node list

(* UPSTREAM #24 (STMT-JSON): per-instruction structured statement
   nodes. Replaces the Cn_pp leaf in stmt-bearing positions of
   judgment children (FhoareS / FbdHoareS / FeHoareS / FequivS /
   FeagerF). Block constructs (if / while / match) carry nested
   stmt_node lists. Source positions (`loc`) emitted as None until
   EC's IR threads parsetree positions through typecheck. *)
and stmt_node =
  | Sn_asgn     of { pp : string; loc : stmt_loc option }
  | Sn_rnd      of { pp : string; loc : stmt_loc option }
  | Sn_call     of { pp : string; loc : stmt_loc option }
  | Sn_raise    of { pp : string; loc : stmt_loc option }
  | Sn_abstract of { pp : string; loc : stmt_loc option }
  | Sn_if       of { cond_pp   : string;
                     then_body : stmt_node list;
                     else_body : stmt_node list;
                     loc       : stmt_loc option }
  | Sn_while    of { cond_pp : string;
                     body    : stmt_node list;
                     loc     : stmt_loc option }
  | Sn_match    of { target_pp : string;
                     branches  : stmt_match_branch list;
                     loc       : stmt_loc option }

and stmt_match_branch = {
  pattern_pp : string;
  body       : stmt_node list;
}

and stmt_loc = {
  start_line : int;
  start_col  : int;
  end_line   : int;
  end_col    : int;
}

and judgment_node =
  | J_hoare  of { pre  : conclusion_node;
                  stmt : conclusion_node;
                  post : conclusion_node }
  | J_phoare of { pre   : conclusion_node;
                  stmt  : conclusion_node;
                  post  : conclusion_node;
                  bound : conclusion_node;
                  cmp   : string }
  | J_ehoare of { pre  : conclusion_node;
                  stmt : conclusion_node;
                  post : conclusion_node }
  | J_equiv  of { pre        : conclusion_node;
                  stmt_left  : conclusion_node;
                  stmt_right : conclusion_node;
                  post       : conclusion_node }
  | J_eager  of { pre               : conclusion_node;
                  stmt_left         : conclusion_node;
                  stmt_right        : conclusion_node;
                  transferred_left  : conclusion_node;
                  transferred_right : conclusion_node;
                  post              : conclusion_node }

type subgoal = {
  index      : int;
  hypotheses : hypothesis list;
  conclusion : conclusion_node;
}

type t = {
  active        : bool;
  subgoal_count : int;
  current_index : int;
  subgoals      : subgoal list;
}

(* Best-effort flattening for consumers that want plain text. Tries
   to mimic EC's pp output for judgments; not byte-identical to
   EC's pp_form output but semantically equivalent and good enough
   for log lines / scripted-test snippets. *)
let rec stmt_node_to_pp_text (s : stmt_node) : string =
  match s with
  | Sn_asgn { pp; _ } | Sn_rnd { pp; _ } | Sn_call { pp; _ }
  | Sn_raise { pp; _ } | Sn_abstract { pp; _ } -> pp
  | Sn_if { cond_pp; then_body; else_body; _ } ->
    let pp_branch xs =
      String.concat " " (List.map stmt_node_to_pp_text xs)
    in
    if List.length else_body = 0 then
      Printf.sprintf "if (%s) { %s }" cond_pp (pp_branch then_body)
    else
      Printf.sprintf "if (%s) { %s } else { %s }"
        cond_pp (pp_branch then_body) (pp_branch else_body)
  | Sn_while { cond_pp; body; _ } ->
    Printf.sprintf "while (%s) { %s }"
      cond_pp
      (String.concat " " (List.map stmt_node_to_pp_text body))
  | Sn_match { target_pp; branches; _ } ->
    let pp_br b =
      Printf.sprintf "| %s => %s"
        b.pattern_pp
        (String.concat " " (List.map stmt_node_to_pp_text b.body))
    in
    Printf.sprintf "match (%s) with %s end"
      target_pp (String.concat " " (List.map pp_br branches))

let stmt_list_to_pp_text (xs : stmt_node list) : string =
  String.concat "; " (List.map stmt_node_to_pp_text xs)

let rec to_pp_text = function
  | Cn_pp s -> s
  | Cn_stmt body -> stmt_list_to_pp_text body
  | Cn_judgment (J_hoare { pre; stmt; post }) ->
    Printf.sprintf "hoare[%s : %s ==> %s]"
      (to_pp_text stmt) (to_pp_text pre) (to_pp_text post)
  | Cn_judgment (J_phoare { pre; stmt; post; bound; cmp }) ->
    Printf.sprintf "phoare[%s : %s ==> %s] %s %s"
      (to_pp_text stmt) (to_pp_text pre) (to_pp_text post)
      cmp (to_pp_text bound)
  | Cn_judgment (J_ehoare { pre; stmt; post }) ->
    Printf.sprintf "ehoare[%s : %s ==> %s]"
      (to_pp_text stmt) (to_pp_text pre) (to_pp_text post)
  | Cn_judgment (J_equiv { pre; stmt_left; stmt_right; post }) ->
    Printf.sprintf "equiv[%s ~ %s : %s ==> %s]"
      (to_pp_text stmt_left) (to_pp_text stmt_right)
      (to_pp_text pre) (to_pp_text post)
  | Cn_judgment (J_eager { pre; stmt_left; stmt_right;
                           transferred_left; transferred_right; post }) ->
    Printf.sprintf "eager[ %s, %s ~ %s, %s : %s ==> %s ]"
      (to_pp_text transferred_left) (to_pp_text stmt_left)
      (to_pp_text stmt_right) (to_pp_text transferred_right)
      (to_pp_text pre) (to_pp_text post)

let hyp_kind_of_string = function
  | "var"    -> Var
  | "mem"    -> Mem
  | "modty"  -> Modty
  | "hyp"    -> Hyp
  | "abs_st" -> Abs_st
  | other    -> Other other

let hyp_kind_to_string = function
  | Var      -> "var"
  | Mem      -> "mem"
  | Modty    -> "modty"
  | Hyp      -> "hyp"
  | Abs_st   -> "abs_st"
  | Other s  -> s

let opt_string = function `String s -> Some s | _ -> None
let opt_int    = function `Int n    -> Some n | _ -> None
let opt_bool   = function `Bool b   -> Some b | _ -> None
let opt_list   = function `List l   -> Some l | _ -> None

let member j k =
  match j with
  | `Assoc kvs -> List.assoc_opt k kvs
  | _ -> None

let field_string j k =
  match member j k with Some v -> opt_string v | None -> None

let field_int ?(default=0) j k =
  match member j k with Some v -> (match opt_int v with Some n -> n | None -> default) | None -> default

let field_bool ?(default=false) j k =
  match member j k with Some v -> (match opt_bool v with Some b -> b | None -> default) | None -> default

let field_list j k =
  match member j k with Some v -> (match opt_list v with Some l -> l | None -> []) | None -> []

let decode_hypothesis j =
  match j with
  | `Assoc _ ->
    let name = match field_string j "name" with
      | Some s -> s
      | None -> raise (Invalid_argument "hypothesis: missing name")
    in
    let kind =
      match field_string j "kind" with
      | Some s -> hyp_kind_of_string s
      | None -> Other ""
    in
    let pp =
      match field_string j "pp" with
      | Some s -> s
      | None -> ""
    in
    { name; kind; pp }
  | _ -> raise (Invalid_argument "hypothesis: not an object")

(* UPSTREAM #24: stmt_node decoder. Mirrors the per-instr JSON
   shape emitted by EC's stmt_node_to_json walker. Defensive on
   missing fields — emits Sn_abstract with the kind name as pp on
   unknown variants so the renderer can still display something. *)
let rec decode_stmt_node (j : Yojson.Safe.t) : stmt_node =
  match j with
  | `Assoc _ -> begin
    let kind = match field_string j "kind" with
      | Some s -> s
      | None -> raise (Invalid_argument "stmt_node: missing kind")
    in
    let pp_field () =
      match field_string j "pp" with Some s -> s | None -> ""
    in
    let cond_pp_field () =
      match field_string j "cond_pp" with Some s -> s | None -> ""
    in
    let body_field name =
      List.map decode_stmt_node (field_list j name)
    in
    let loc = decode_stmt_loc (member j "loc") in
    match kind with
    | "asgn"     -> Sn_asgn     { pp = pp_field (); loc }
    | "rnd"      -> Sn_rnd      { pp = pp_field (); loc }
    | "call"     -> Sn_call     { pp = pp_field (); loc }
    | "raise"    -> Sn_raise    { pp = pp_field (); loc }
    | "abstract" -> Sn_abstract { pp = pp_field (); loc }
    | "if" ->
      Sn_if { cond_pp = cond_pp_field ();
              then_body = body_field "then_body";
              else_body = body_field "else_body";
              loc }
    | "while" ->
      Sn_while { cond_pp = cond_pp_field ();
                 body = body_field "body";
                 loc }
    | "match" ->
      let target_pp = match field_string j "target_pp" with
        | Some s -> s | None -> "" in
      let branches =
        List.map (fun b ->
          { pattern_pp = (match field_string b "pattern_pp" with
                          | Some s -> s | None -> "");
            body = List.map decode_stmt_node (field_list b "body") })
          (field_list j "branches")
      in
      Sn_match { target_pp; branches; loc }
    | other ->
      (* Unknown stmt kind — degrade to abstract with the kind name
         as pp so the renderer shows SOMETHING. Future EC variants
         that add new instr kinds work via this fallback until
         decode_stmt_node is updated. *)
      Sn_abstract { pp = Printf.sprintf "<unknown stmt kind: %s>" other;
                    loc }
  end
  | _ -> raise (Invalid_argument "stmt_node: not an object")

and decode_stmt_loc (j : Yojson.Safe.t option) : stmt_loc option =
  match j with
  | None | Some `Null -> None
  | Some (`Assoc _ as obj) ->
    Some {
      start_line = field_int obj "start_line";
      start_col  = field_int obj "start_col";
      end_line   = field_int obj "end_line";
      end_col    = field_int obj "end_col";
    }
  | _ -> None

let rec decode_conclusion j =
  match j with
  | `Assoc _ -> begin
    match field_string j "kind" with
    | Some "pp" ->
      let text = match field_string j "text" with Some s -> s | None -> "" in
      Cn_pp text
    | Some "stmt" ->
      Cn_stmt (List.map decode_stmt_node (field_list j "body"))
    | Some "judgment" -> begin
      let kind = match field_string j "judgment_kind" with
        | Some s -> s
        | None -> raise (Invalid_argument "judgment: missing judgment_kind")
      in
      let child name =
        match member j name with
        | Some sub -> decode_conclusion sub
        | None -> raise (Invalid_argument
                           (Printf.sprintf "judgment %s: missing field %s"
                              kind name))
      in
      match kind with
      | "hoare" ->
        Cn_judgment (J_hoare {
          pre  = child "pre";
          stmt = child "stmt";
          post = child "post";
        })
      | "phoare" ->
        let cmp = match field_string j "cmp" with
          | Some s -> s
          | None -> raise (Invalid_argument "phoare: missing cmp")
        in
        Cn_judgment (J_phoare {
          pre  = child "pre";
          stmt = child "stmt";
          post = child "post";
          bound = child "bound";
          cmp;
        })
      | "ehoare" ->
        Cn_judgment (J_ehoare {
          pre  = child "pre";
          stmt = child "stmt";
          post = child "post";
        })
      | "equiv" ->
        Cn_judgment (J_equiv {
          pre        = child "pre";
          stmt_left  = child "stmt_left";
          stmt_right = child "stmt_right";
          post       = child "post";
        })
      | "eager" ->
        Cn_judgment (J_eager {
          pre               = child "pre";
          stmt_left         = child "stmt_left";
          stmt_right        = child "stmt_right";
          transferred_left  = child "transferred_left";
          transferred_right = child "transferred_right";
          post              = child "post";
        })
      | other ->
        raise (Invalid_argument
                 (Printf.sprintf "judgment: unknown kind %s" other))
    end
    | Some other ->
      raise (Invalid_argument
               (Printf.sprintf "conclusion: unknown kind %s" other))
    | None ->
      raise (Invalid_argument "conclusion: missing kind")
  end
  | _ -> raise (Invalid_argument "conclusion: not an object")

let decode_subgoal j =
  match j with
  | `Assoc _ ->
    let index = field_int j "index" in
    let hypotheses = List.map decode_hypothesis (field_list j "hypotheses") in
    let conclusion =
      match member j "conclusion" with
      | Some sub -> decode_conclusion sub
      | None -> raise (Invalid_argument "subgoal: missing conclusion")
    in
    { index; hypotheses; conclusion }
  | _ -> raise (Invalid_argument "subgoal: not an object")

let of_json j =
  match j with
  | `Assoc _ ->
    (try
       let active = field_bool j "active" in
       let subgoal_count = field_int j "subgoal_count" in
       let current_index = field_int j "current_index" in
       let subgoals = List.map decode_subgoal (field_list j "subgoals") in
       Ok { active; subgoal_count; current_index; subgoals }
     with Invalid_argument msg -> Error msg)
  | _ -> Error "GOALS-JSON: not a JSON object"

let of_string s =
  match Yojson.Safe.from_string s with
  | exception Yojson.Json_error msg -> Error ("JSON parse: " ^ msg)
  | j -> of_json j

let focused t =
  if not t.active then None
  else
    let i = max 0 (min (List.length t.subgoals - 1) t.current_index) in
    List.nth_opt t.subgoals i

let hypothesis_to_json (h : hypothesis) : Yojson.Safe.t =
  `Assoc [
    "name", `String h.name;
    "kind", `String (hyp_kind_to_string h.kind);
    "pp",   `String h.pp;
  ]

let stmt_loc_to_json (loc : stmt_loc option) : Yojson.Safe.t =
  match loc with
  | None -> `Null
  | Some l -> `Assoc [
      "start_line", `Int l.start_line;
      "start_col",  `Int l.start_col;
      "end_line",   `Int l.end_line;
      "end_col",    `Int l.end_col;
    ]

let rec stmt_node_to_json (s : stmt_node) : Yojson.Safe.t =
  let leaf kind pp loc =
    `Assoc [ "kind", `String kind;
             "pp",   `String pp;
             "loc",  stmt_loc_to_json loc ]
  in
  match s with
  | Sn_asgn     { pp; loc } -> leaf "asgn"     pp loc
  | Sn_rnd      { pp; loc } -> leaf "rnd"      pp loc
  | Sn_call     { pp; loc } -> leaf "call"     pp loc
  | Sn_raise    { pp; loc } -> leaf "raise"    pp loc
  | Sn_abstract { pp; loc } -> leaf "abstract" pp loc
  | Sn_if { cond_pp; then_body; else_body; loc } ->
    `Assoc [
      "kind",      `String "if";
      "cond_pp",   `String cond_pp;
      "then_body", `List (List.map stmt_node_to_json then_body);
      "else_body", `List (List.map stmt_node_to_json else_body);
      "loc",       stmt_loc_to_json loc;
    ]
  | Sn_while { cond_pp; body; loc } ->
    `Assoc [
      "kind",    `String "while";
      "cond_pp", `String cond_pp;
      "body",    `List (List.map stmt_node_to_json body);
      "loc",     stmt_loc_to_json loc;
    ]
  | Sn_match { target_pp; branches; loc } ->
    let br_to_json b = `Assoc [
      "pattern_pp", `String b.pattern_pp;
      "body",       `List (List.map stmt_node_to_json b.body);
    ] in
    `Assoc [
      "kind",      `String "match";
      "target_pp", `String target_pp;
      "branches",  `List (List.map br_to_json branches);
      "loc",       stmt_loc_to_json loc;
    ]

let rec conclusion_to_json (c : conclusion_node) : Yojson.Safe.t =
  match c with
  | Cn_pp text -> `Assoc [ "kind", `String "pp"; "text", `String text ]
  | Cn_stmt body ->
    `Assoc [ "kind", `String "stmt";
             "body", `List (List.map stmt_node_to_json body) ]
  | Cn_judgment (J_hoare { pre; stmt; post }) ->
    `Assoc [
      "kind", `String "judgment";
      "judgment_kind", `String "hoare";
      "pre",  conclusion_to_json pre;
      "stmt", conclusion_to_json stmt;
      "post", conclusion_to_json post;
    ]
  | Cn_judgment (J_phoare { pre; stmt; post; bound; cmp }) ->
    `Assoc [
      "kind", `String "judgment";
      "judgment_kind", `String "phoare";
      "pre",   conclusion_to_json pre;
      "stmt",  conclusion_to_json stmt;
      "post",  conclusion_to_json post;
      "bound", conclusion_to_json bound;
      "cmp",   `String cmp;
    ]
  | Cn_judgment (J_ehoare { pre; stmt; post }) ->
    `Assoc [
      "kind", `String "judgment";
      "judgment_kind", `String "ehoare";
      "pre",  conclusion_to_json pre;
      "stmt", conclusion_to_json stmt;
      "post", conclusion_to_json post;
    ]
  | Cn_judgment (J_equiv { pre; stmt_left; stmt_right; post }) ->
    `Assoc [
      "kind", `String "judgment";
      "judgment_kind", `String "equiv";
      "pre",        conclusion_to_json pre;
      "stmt_left",  conclusion_to_json stmt_left;
      "stmt_right", conclusion_to_json stmt_right;
      "post",       conclusion_to_json post;
    ]
  | Cn_judgment (J_eager { pre; stmt_left; stmt_right;
                           transferred_left; transferred_right; post }) ->
    `Assoc [
      "kind", `String "judgment";
      "judgment_kind", `String "eager";
      "pre",               conclusion_to_json pre;
      "stmt_left",         conclusion_to_json stmt_left;
      "stmt_right",        conclusion_to_json stmt_right;
      "transferred_left",  conclusion_to_json transferred_left;
      "transferred_right", conclusion_to_json transferred_right;
      "post",              conclusion_to_json post;
    ]

let subgoal_to_json (sg : subgoal) : Yojson.Safe.t =
  `Assoc [
    "index", `Int sg.index;
    "hypotheses", `List (List.map hypothesis_to_json sg.hypotheses);
    "conclusion", conclusion_to_json sg.conclusion;
  ]

let to_json (t : t) : Yojson.Safe.t =
  `Assoc [
    "active", `Bool t.active;
    "subgoal_count", `Int t.subgoal_count;
    "current_index", `Int t.current_index;
    "subgoals", `List (List.map subgoal_to_json t.subgoals);
  ]
