(** Structured accessor over `GOALS-JSON` (additions 3 + 23).

    GOALS-JSON emits a single-line JSON record describing the active
    proof state. Hypotheses are structured (`name`, `kind`); types
    and formulas are pretty-printed text in v0 (until the typed
    formula serializer lands). The conclusion is a recursive tree
    (UPSTREAM #23) — opaque pp leaves at v0, propositional/structured
    nodes added in v1+. This module decodes the JSON into typed
    records so every consumer reads from one stable shape instead of
    re-parsing the JSON ad-hoc. *)

type hyp_kind =
  | Var
  | Mem
  | Modty
  | Hyp
  | Abs_st
  | Other of string
  (** [Other] preserves the raw string when EC adds a new kind tag;
      the consumer can pass it through unchanged rather than fail. *)

type hypothesis = {
  name : string;
  kind : hyp_kind;
  pp   : string;
  (** Type (for [Var]) or formula (for [Hyp]) pretty-printed. pp-text
      in v0; the typed formula serializer will add a typed companion. *)
}

(** Conclusion tree (UPSTREAM #23 + #24). Node kinds:
    - [Cn_pp]: opaque pp text leaf.
    - [Cn_judgment]: outermost PHL judgment with structured children.
    - [Cn_stmt]: structured statement-list (UPSTREAM #24) — used in
      the stmt / stmt_left / stmt_right / transferred_* positions of
      judgment children. Each list element is a recursive
      [stmt_node] carrying per-instruction structure (asgn / if /
      while / match / etc.).
    v1+ extends the variant with propositional connectives +
    quantifiers; v_full adds structured terms inside judgment leaf
    positions. Every future stage is a strict superset of v0. *)
type conclusion_node =
  | Cn_pp       of string
  | Cn_judgment of judgment_node
  | Cn_stmt     of stmt_node list

(** Per-instruction structured node (UPSTREAM #24). Mirrors EC's
    [EcAst.instr_node] variants. Block constructs (if / while /
    match) carry recursive [stmt_node list] children. [loc] carries
    source position when available — currently always [None]
    because EC's IR drops parsetree positions during typecheck;
    populated in a future amendment. *)
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
                  cmp   : string  (** "<=" | "=" | ">=" *) }
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

(** [of_json j] decodes a GOALS-JSON payload. Returns [Error <detail>]
    if the shape is malformed. *)
val of_json : Yojson.Safe.t -> (t, string) result

(** [of_string s] parses [s] as JSON first, then decodes. *)
val of_string : string -> (t, string) result

(** [to_json t] encodes [t] back to a GOALS-JSON-shaped Yojson value.
    Round-trips with [of_json] (modulo `Other` reduction to its
    string tag). Used by LSP method handlers that return goal views
    inside their response payload (e.g. [tryTactic.goalsAfter]). *)
val to_json : t -> Yojson.Safe.t

(** [focused g] returns the currently-focused subgoal, or [None] if
    the proof is inactive or has zero subgoals. *)
val focused : t -> subgoal option

(** [hyp_kind_to_string] reverses [Other] faithfully. *)
val hyp_kind_to_string : hyp_kind -> string

(** [to_pp_text c] flattens a conclusion tree to a best-effort text
    rendering. For consumers that want text but don't care about
    structure (logs, scripted-test snippets, the TUI). The output
    mimics EC's pp shape for judgments but isn't byte-identical. *)
val to_pp_text : conclusion_node -> string

(** [decode_conclusion j] decodes a conclusion-subtree JSON node
    in isolation. Useful for consumers that read raw GOALS-JSON
    out-of-band (REPL view of the daemon's stdout) without going
    through [of_json] for the whole envelope. Raises
    [Invalid_argument] on malformed shape. *)
val decode_conclusion : Yojson.Safe.t -> conclusion_node
