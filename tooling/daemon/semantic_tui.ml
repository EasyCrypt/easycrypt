(** Semantic-edit picker overlay for `ecd tui`. PoC scope covers four
    tactics — apply-hyp, move-intros, rewrite, apply-lemma — with live
    speculation against the primary session and finalize-writes-to-
    buffer behavior.

    Demo-grade UI: built on top of the [Goal_view / Speculation /
    Fuzzy_filter / Search_result] shared-lib substrate. The shared
    modules carry the reusable logic; this file is the notty-specific
    picker rendering. *)

open Ecd_core
module N = Notty
module A = N.A
module I = N.I
module P = Proof_speculation

(* --- Tactic catalog (re-exported from Proof_speculation) ----------- *)

type tactic = P.tactic =
  | Apply_hyp
  | Move_intros
  | Rewrite
  | Apply_lemma
  | Rewrite_lemma
  | Suggest_closers

let tactic_label = P.tactic_label
let tactic_catalog = P.tactic_catalog

(* --- Speculation reporting (TUI-local — adds Trial_pending) -------- *)

type trial_outcome =
  | Trial_pending
  | Trial_ok of { goals : Goal_view.t option; body : string }
  | Trial_err of string

(* Convert from the daemon-side cumulative-session outcome (no
   Trial_pending) into the TUI's renderer state. *)
let trial_of_p : P.trial_outcome -> trial_outcome = function
  | P.Trial_ok { goals; body } -> Trial_ok { goals; body }
  | P.Trial_err msg -> Trial_err msg

(* --- Picker state machine ---------------------------------------- *)

(* Rewrite used to have a direction picker + hypothesis picker.
   Now it's an incremental token-builder: user types rewrite
   arguments one at a time (`H`, `-H'`, `!L`, `/foo`, etc.), each
   tried speculatively, just like move's intro picker. *)

(* Preview state for apply-lemma: when the cursor lands on a hit in
   Results focus, we capture + speculatively apply that lemma so
   the user sees whether it would close the goal, leave subgoals,
   or error. Rolled back when cursor moves / focus leaves / picker
   exits. *)
type apply_lemma_preview =
  | Preview_none
  | Preview_ok of { goals_after : Goal_view.t option; body : string }
  | Preview_err of string

type apply_lemma_state = {
  verb           : [ `Apply | `Rewrite ];
  (** Which tactic the picker is building. Both share the same
      search + fzf + preview machinery; only the submitted source
      and the header label differ. *)
  search_prompt  : string;
  filter_prompt  : string;
  results        : Search_result.hit list;
  filtered       : Search_result.hit Fuzzy_filter.match_result list;
  cursor         : int;
  focus          : [ `Search | `Filter | `Results ];
  preview_handle : P.session option;
  preview_cursor : int;  (* cursor position at preview time *)
  preview        : apply_lemma_preview;
}

(* Closer-suggester types: aliased to Proof_speculation so the
   renderer pattern-matches on Suggest_closes / _open / _err
   unqualified. *)
type suggest_outcome = P.suggest_outcome =
  | Suggest_closes
  | Suggest_open of int
  | Suggest_err of string

type suggest_row = P.suggest_row = {
  src : string;
  label : string;
  outcome : suggest_outcome;
}

type stage =
  | S_pick_tactic  of { cursor : int }
  | S_apply_hyp    of { cursor : int; hyps : Goal_view.hypothesis list }
  | S_move_intros  of {
      input           : string;
      tokens          : string list;  (* accumulated tokens, oldest first *)
      speculation     : P.session;
      last_command    : string;
      last_outcome    : trial_outcome;
    }
  | S_rewrite_build of {
      input        : string;
      tokens       : string list;
      speculation  : P.session;
      last_command : string;
      last_outcome : trial_outcome;
    }
  | S_apply_lemma  of apply_lemma_state
  | S_suggest      of {
      cursor  : int;
      rows    : suggest_row list;
      pending : int;             (** remaining candidates to try *)
      current : string option;   (** label of the candidate in flight *)
    }

type t = {
  mutable stage  : stage;
  (* Log pane for diagnostic messages from the picker itself. *)
  mutable log    : string list;  (* newest-first *)
  mutable redraw : unit -> unit;
  (** Callback that repaints the TUI frame against the current
      [t.stage]. Default: no-op. [Tui] patches this with the real
      [T.image term (render ui)] closure when the user enters
      semantic mode, so long-running picker operations (e.g. the
      closer-suggester sweep) can push intermediate frames from
      inside their own synchronous loop. *)
}

let log_cap = 50
let push_log t s =
  t.log <- s :: (List.filteri (fun i _ -> i < log_cap - 1) t.log)

(* --- GOALS-JSON helpers ------------------------------------------- *)

let fetch_goals (session : Ec_llm_session.t) : Goal_view.t option =
  match Ec_llm_session.goals ~structured:true session with
  | Error _ -> None
  | Ok s ->
    (match Goal_view.of_string s with
     | Error _ -> None
     | Ok gv -> Some gv)

let focused_hyps (session : Ec_llm_session.t) : Goal_view.hypothesis list =
  match fetch_goals session with
  | None -> []
  | Some gv ->
    (match Goal_view.focused gv with
     | None -> []
     | Some sg -> sg.hypotheses)

(* --- Stage constructors ------------------------------------------- *)

let begin_ () = {
  stage = S_pick_tactic { cursor = 0 };
  log = [];
  redraw = (fun () -> ());
}

let enter_apply_hyp session =
  let hyps = focused_hyps session in
  S_apply_hyp { cursor = 0; hyps }

let enter_move_intros session =
  S_move_intros {
    input = "";
    tokens = [];
    speculation = P.begin_session session;
    last_command = "";
    last_outcome = Trial_pending;
  }

let enter_rewrite_build session =
  S_rewrite_build {
    input = "";
    tokens = [];
    speculation = P.begin_session session;
    last_command = "";
    last_outcome = Trial_pending;
  }

let enter_lemma_picker ~verb () : stage = S_apply_lemma {
  verb;
  search_prompt = "";
  filter_prompt = "";
  results = [];
  filtered = [];
  cursor = 0;
  focus = `Search;
  preview_handle = None;
  preview_cursor = -1;
  preview = Preview_none;
}

let enter_apply_lemma () = enter_lemma_picker ~verb:`Apply ()
let enter_rewrite_lemma () = enter_lemma_picker ~verb:`Rewrite ()

(* --- Command assembly -------------------------------------------- *)

(* Source builders re-exported from Proof_speculation. *)
let apply_hyp_source = P.apply_hyp_source
let move_cumulative_source = P.move_cumulative_source
let rewrite_cumulative_source = P.rewrite_cumulative_source
let verb_keyword = P.verb_keyword
let lemma_picker_source = P.lemma_picker_source

(* Sort: closers first, then opens, then errors. Re-exported. *)
let sort_suggest_rows = P.sort_suggest_rows

(* Speculative apply/rewrite of [h] on [session]. Rolls any prior
   preview session back first, captures fresh, runs, returns the
   TUI's preview type plus the new handle. Caller is responsible for
   discarding the returned handle on next preview / exit. *)
let run_preview_lemma
    ~verb
    (session : Ec_llm_session.t)
    (prev : P.session option)
    (h : Search_result.hit)
  : apply_lemma_preview * P.session
  =
  match P.preview_lemma session ~verb ?prev h with
  | Error e ->
    (* Rollback of [prev] failed — surface as Preview_err. The fresh
       capture didn't happen, so re-capture so the caller has a handle
       to discard later. *)
    (Preview_err (Error.to_string e), P.begin_session session)
  | Ok (P.Preview_ok { goals_after; body }, sess) ->
    (Preview_ok { goals_after; body }, sess)
  | Ok (P.Preview_err msg, sess) ->
    (Preview_err msg, sess)

(* Progressive closer-sweep over Proof_speculation's [suggest_closers]
   API. Two callbacks drive the rolling UI:
   - [before_candidate] sets [current = Some label] before the
     candidate runs, so the user sees "trying smt()…".
   - [on_progress] (decision 1: AFTER rollback) appends the row,
     clears [current], updates the counter.
   Both fire at session-stable points.

   Input is still blocked during the sweep (notty's event loop only
   reads between handle_event calls) — cancellation and interleaved
   input require the Eio-fiber path listed in the plan's Deferrals. *)
let run_closer_suggestions_progressive (t : t) (session : Ec_llm_session.t) =
  let acc = ref [] in
  let before_candidate ~label ~remaining =
    t.stage <- S_suggest {
      cursor = 0;
      rows = List.rev !acc;
      pending = remaining;
      current = Some label;
    };
    t.redraw ()
  in
  let on_progress (row : suggest_row) ~remaining =
    acc := row :: !acc;
    t.stage <- S_suggest {
      cursor = 0;
      rows = List.rev !acc;
      pending = remaining;
      current = None;
    };
    t.redraw ()
  in
  match
    P.suggest_closers session ~before_candidate ~on_progress ()
  with
  | Error e ->
    push_log t ("suggest_closers: " ^ Error.to_string e);
    t.stage <- S_suggest {
      cursor = 0;
      rows = sort_suggest_rows (List.rev !acc);
      pending = 0;
      current = None;
    };
    t.redraw ()
  | Ok rows ->
    t.stage <- S_suggest {
      cursor = 0;
      rows = sort_suggest_rows rows;
      pending = 0;
      current = None;
    };
    t.redraw ()

let enter_suggest (t : t) (session : Ec_llm_session.t) : unit =
  (* Set initial "sweep starting" frame so the user sees something
     immediately after hitting Enter on the picker entry. *)
  t.stage <- S_suggest {
    cursor = 0; rows = [];
    pending = List.length P.default_closer_candidates;
    current = None;
  };
  t.redraw ();
  run_closer_suggestions_progressive t session

let clear_preview _session (r : apply_lemma_state) : apply_lemma_state =
  (match r.preview_handle with
   | None -> ()
   | Some s ->
     (match P.discard s with
      | Ok () -> () | Error _ -> ()));
  { r with preview_handle = None; preview_cursor = -1;
           preview = Preview_none }

(* --- Speculation: try a text command, return outcome -------------- *)

(* For [Move_intros] / [S_rewrite_build]: each step rolls back to the
   capture, submits the cumulative command via text exec, shows
   result. Thin shim over [P.try_] that converts to the TUI-local
   [trial_outcome] (which has [Trial_pending] for the no-trial-yet
   UI state). *)
let try_text_cumulative
    (_session : Ec_llm_session.t)
    ~(handle : P.session)
    (source : string)
  : trial_outcome
  =
  trial_of_p (P.try_ handle ~source)

(* --- Finalize / write-to-buffer ---------------------------------- *)

(* On finalize, the primary already holds the speculative state.
   We discard the speculation and then feed through Repl_core's
   cmd_insert so the sentence lands in the document buffer properly
   (same code path interactive `:insert` takes). *)
let finalize_write_and_insert
    (repl_state : Repl_core.state)
    ~(handle : P.session)
    ~(source : string)
  : (unit, string) result
  =
  match P.discard handle with
  | Error e -> Error (Error.to_string e)
  | Ok () ->
    (* Repl_core.cmd_insert does parse + exec + buffer update. *)
    Repl_core.cmd_insert repl_state source;
    Ok ()

(* --- Key handling ------------------------------------------------- *)

type key = Notty.Unescape.key

(* Result of handling a key: continue in the picker, exit keeping
   the speculative state (rare — mostly for finalize paths), or
   exit cancelling (rollback any in-flight speculation). *)
type key_result =
  | Continue
  | Continue_refresh  (** Session state advanced; caller should
                          refresh the goals pane. *)
  | Exit_finalize of string
  | Exit_cancel_with_rollback of Speculation.handle option
  | Exit_cancel

let clamp_cursor i n =
  if n = 0 then 0 else max 0 (min (n - 1) i)

let handle_key_pick_tactic (t : t) (_ : Repl_core.state) (k : key) =
  match k with
  | `Escape, _ -> Exit_cancel
  | `Arrow `Down, _ | `ASCII 'j', _ ->
    let n = List.length tactic_catalog in
    let cursor = match t.stage with
      | S_pick_tactic { cursor } -> clamp_cursor (cursor + 1) n
      | _ -> 0
    in
    t.stage <- S_pick_tactic { cursor };
    Continue
  | `Arrow `Up, _ | `ASCII 'k', _ ->
    let cursor = match t.stage with
      | S_pick_tactic { cursor } -> clamp_cursor (cursor - 1) (List.length tactic_catalog)
      | _ -> 0
    in
    t.stage <- S_pick_tactic { cursor };
    Continue
  | _ -> Continue

(* --- Render ------------------------------------------------------- *)

let pad_to n s =
  let len = String.length s in
  if len >= n then String.sub s 0 n
  else s ^ String.make (n - len) ' '

(* notty's [I.string] rejects control characters. EC's pp output can
   contain newlines / tabs / CR for multi-line hypothesis types and
   conclusions; flatten to spaces so the picker never takes out the
   whole process with an Invalid_argument. Multi-line rendering is
   out of scope for the demo pane. *)
let sanitize s =
  String.map
    (function '\n' | '\r' | '\t' -> ' ' | c -> c)
    s

let truncate_to n s =
  let s = sanitize s in
  if String.length s > n then String.sub s 0 (max 0 (n - 1)) ^ "…"
  else s

let hline w = I.uchar A.(fg lightblack) (Uchar.of_int 0x2500) w 1

let bar ~w label =
  let head  = I.string A.(fg lightblack) "───" in
  let lbl   = I.string A.(fg lightblack) (" " ^ label ^ " ") in
  let fill  = max 0 (w - 3 - 2 - String.length label) in
  let tail  = if fill > 0 then hline fill else I.empty in
  I.hcat [ head; lbl; tail ]

let render_pick_tactic ~w ~cursor =
  let rows =
    List.mapi
      (fun i tac ->
         let marker = if i = cursor then "▶ " else "  " in
         let attr   = if i = cursor then A.(fg lightyellow ++ st bold) else A.empty in
         I.string attr (truncate_to w (marker ^ tactic_label tac)))
      tactic_catalog
  in
  I.vcat rows

let render_outcome ~w outcome =
  match outcome with
  | Trial_pending ->
    I.string A.(fg lightblack) "(no trial yet — submit a command to see its effect)"
  | Trial_ok { goals; body } ->
    let goals_summary =
      match goals with
      | None -> "(goals unavailable)"
      | Some gv ->
        (match Goal_view.focused gv with
         | None -> "(no active goal)"
         | Some sg ->
           Printf.sprintf "goal: %s  [%d hyps]"
             (truncate_to (w - 20) (Goal_view.to_pp_text sg.conclusion))
             (List.length sg.hypotheses))
    in
    let body_summary =
      if body = "" then "" else " / body: " ^ truncate_to 40 body
    in
    I.string A.(fg green) (truncate_to w (goals_summary ^ body_summary))
  | Trial_err msg ->
    I.string A.(fg red) (truncate_to w ("error: " ^ msg))

let render_apply_hyp ~w ~cursor ~(hyps : Goal_view.hypothesis list) =
  if hyps = [] then
    I.string A.(fg lightblack)
      "(no hypotheses in current goal — close the picker with Esc)"
  else
    I.vcat (List.mapi
              (fun i (h : Goal_view.hypothesis) ->
                 let marker = if i = cursor then "▶ " else "  " in
                 let attr = if i = cursor then A.(fg lightyellow ++ st bold) else A.empty in
                 let sig_ = truncate_to (max 10 (w - 15 - String.length h.name)) h.pp in
                 I.string attr (truncate_to w
                                  (Printf.sprintf "%s%-10s : %s" marker h.name sig_)))
              hyps)

let render_move_intros ~w ~input ~tokens ~last_command ~last_outcome =
  let tokens_view =
    if tokens = [] then "(none yet)"
    else String.concat " " tokens
  in
  let running =
    if last_command = "" then ""
    else "  (last tried: " ^ last_command ^ ")"
  in
  I.vcat [
    I.string A.(fg lightblack)
      (truncate_to w ("tokens so far: " ^ tokens_view ^ running));
    I.string A.empty
      (truncate_to w ("type next intro (Enter = try, Ctrl+F = finalize): " ^ input ^ "█"));
    render_outcome ~w last_outcome;
  ]

let render_rewrite_build ~w ~input ~tokens ~last_command ~last_outcome =
  let tokens_view =
    if tokens = [] then "(none yet)"
    else String.concat " " tokens
  in
  let running =
    if last_command = "" then ""
    else "  (last tried: " ^ last_command ^ ")"
  in
  I.vcat [
    I.string A.(fg lightblack)
      (truncate_to w ("tokens so far: " ^ tokens_view ^ running));
    I.string A.empty
      (truncate_to w
         ("type next arg (Enter = try, Enter on empty = finalize): "
          ^ input ^ "█"));
    render_outcome ~w last_outcome;
  ]

let render_apply_lemma ~w ~search_prompt ~filter_prompt ~filtered ~cursor ~focus =
  let prompt_bar label value is_focused =
    let arrow = if is_focused then "▶ " else "  " in
    let attr = if is_focused then A.(fg lightyellow) else A.(fg lightblack) in
    I.string attr
      (truncate_to w (Printf.sprintf "%s%s: %s%s"
                        arrow label value
                        (if is_focused then "█" else "")))
  in
  let hint =
    I.string A.(fg lightblack)
      (truncate_to w
         "  tip: wrap op patterns in parens, \
          e.g. (_ + _) / Int.(<=) / (_ = _)")
  in
  let rows =
    if filtered = [] then
      [ I.string A.(fg lightblack)
          "(no results — type a search pattern and press Enter)" ]
    else
      List.mapi
        (fun i (m : Search_result.hit Fuzzy_filter.match_result) ->
           let marker = if i = cursor then "▶ " else "  " in
           let attr = if i = cursor && focus = `Results
             then A.(fg lightyellow ++ st bold) else A.empty
           in
           let sig_ = truncate_to (max 10 (w - 20 - String.length m.item.qname))
                        m.item.signature
           in
           I.string attr (truncate_to w
                            (Printf.sprintf "%s%-20s  %s" marker m.item.qname sig_)))
        (List.filteri (fun i _ -> i < 10) filtered)
  in
  I.vcat (
    prompt_bar "search"  search_prompt (focus = `Search)
    :: prompt_bar "filter" filter_prompt (focus = `Filter)
    :: hint
    :: I.string A.(fg lightblack) "" :: rows)

let render_stage ~w (stage : stage) =
  match stage with
  | S_pick_tactic { cursor } ->
    I.vcat [
      bar ~w "semantic edit — pick tactic";
      I.string A.(fg lightblack)
        "  ↑/↓ select   Enter confirm   Esc cancel";
      I.string A.empty "";
      render_pick_tactic ~w ~cursor;
    ]
  | S_apply_hyp { cursor; hyps } ->
    I.vcat [
      bar ~w "apply <hypothesis>";
      I.string A.(fg lightblack)
        "  ↑/↓ select   Enter confirm   Esc back";
      I.string A.empty "";
      render_apply_hyp ~w ~cursor ~hyps;
    ]
  | S_move_intros { input; tokens; last_command; last_outcome; _ } ->
    I.vcat [
      bar ~w "move => <intro tokens>";
      I.string A.(fg lightblack)
        "  type + Enter = try   Backspace = drop last   Enter on empty = finalize   Esc back";
      I.string A.empty "";
      render_move_intros ~w ~input ~tokens ~last_command ~last_outcome;
    ]
  | S_rewrite_build { input; tokens; last_command; last_outcome; _ } ->
    I.vcat [
      bar ~w "rewrite <args>";
      I.string A.(fg lightblack)
        "  type + Enter = try   Backspace = drop last   \
         Enter on empty = finalize   Esc back";
      I.string A.(fg lightblack)
        "  args can include `H`, `-H`, `!H`, `/foo`, `(H 3)`, ...";
      I.string A.empty "";
      render_rewrite_build ~w ~input ~tokens ~last_command ~last_outcome;
    ]
  | S_apply_lemma r ->
    let verb_word = verb_keyword r.verb in
    I.vcat [
      bar ~w (Printf.sprintf "%s <lemma by search>" verb_word);
      I.string A.(fg lightblack)
        (Printf.sprintf
           "  Tab = switch field   Enter on search = fetch   ↑/↓ + Enter = %s   Esc back"
           verb_word);
      I.string A.empty "";
      render_apply_lemma ~w
        ~search_prompt:r.search_prompt ~filter_prompt:r.filter_prompt
        ~filtered:r.filtered ~cursor:r.cursor ~focus:r.focus;
    ]
  | S_suggest { cursor; rows; pending; current } ->
    let render_row i (row : suggest_row) =
      let marker = if i = cursor then "▶ " else "  " in
      let outcome_str, attr = match row.outcome with
        | Suggest_closes ->
          "★ closes the goal", A.(fg green ++ st bold)
        | Suggest_open n ->
          (Printf.sprintf "opens %d subgoal(s)" n),
          A.(fg lightyellow)
        | Suggest_err msg ->
          (Printf.sprintf "error: %s" (truncate_to (max 10 (w - 40)) msg)),
          A.(fg lightblack)
      in
      let cursor_attr = if i = cursor then A.(attr ++ st bold) else attr in
      I.string cursor_attr
        (truncate_to w
           (Printf.sprintf "%s%-14s  —  %s" marker row.label outcome_str))
    in
    let progress_line =
      if pending = 0 then I.empty
      else
        let status = match current with
          | None ->
            Printf.sprintf "running sweep (%d remaining)…" pending
          | Some label ->
            Printf.sprintf "trying %s… (%d remaining after this)"
              label (pending - 1)
        in
        I.string A.(fg lightblack ++ st italic) (truncate_to w ("  " ^ status))
    in
    I.vcat [
      bar ~w "suggest closers";
      I.string A.(fg lightblack)
        "  ↑/↓ select (closing entries first)   Enter inserts   Esc back";
      I.string A.empty "";
      I.vcat (List.mapi render_row rows);
      progress_line;
    ]

(* Wrap a single line to [w] columns, breaking at the last space on
   or before the column limit. Falls back to a hard break at [w] if
   the line contains no spaces (e.g., an unbroken qualified name).
   Collapses \t / \r to spaces but preserves structure otherwise. *)
let word_wrap_line w s =
  let s =
    String.map (function '\t' | '\r' -> ' ' | c -> c) s
  in
  let len = String.length s in
  if len <= w then [s]
  else
    let rec loop i acc =
      if i >= len then List.rev acc
      else
        let remaining = len - i in
        if remaining <= w then
          List.rev (String.sub s i remaining :: acc)
        else
          let hard = i + w in
          let rec find_space j =
            if j <= i then -1
            else if s.[j] = ' ' then j
            else find_space (j - 1)
          in
          let break = find_space hard in
          if break < 0 then
            (* no space; hard break *)
            loop hard (String.sub s i w :: acc)
          else
            let chunk = String.sub s i (break - i) in
            loop (break + 1) (chunk :: acc)
    in
    loop 0 []

(* Wrap a potentially multi-line [s] to [w] columns. Preserves
   original line breaks; each source line is independently
   word-wrapped. Used by the apply-lemma preview to render long
   signatures and multi-line error messages readably. *)
let word_wrap w s =
  match String.split_on_char '\n' s with
  | [] -> [""]
  | lines -> List.concat_map (word_wrap_line w) lines

let render_apply_lemma_preview ~w (r : apply_lemma_state) =
  (* The picker's lower pane replaces the diagnostic log with a
     preview of what the cursor-selected lemma is and what applying
     it would do. Only meaningful in Results focus or post-fetch. *)
  let selected_hit =
    if r.filtered = [] then None
    else
      let idx = clamp_cursor r.cursor (List.length r.filtered) in
      Some (List.nth r.filtered idx).item
  in
  match selected_hit with
  | None -> I.empty
  | Some (h : Search_result.hit) ->
    let sig_lines =
      ("  " ^ h.qname) ::
      ("  " ^ (if h.kind = "" then "(decl)" else h.kind)
         ^ " — " ^ h.short_name ^ ":") ::
      List.map (fun l -> "    " ^ l) (word_wrap (w - 4) h.signature)
    in
    let outcome_lines = match r.preview with
      | Preview_none ->
        [ "  (preview: focus Results and pick a hit to see the effect)" ]
      | Preview_ok { goals_after; body } ->
        let g_summary = match goals_after with
          | None -> "(goals unavailable)"
          | Some gv ->
            if gv.subgoal_count = 0 then "★ closes the goal"
            else
              Printf.sprintf "%d subgoal(s) remaining"
                gv.subgoal_count
        in
        let g_detail = match goals_after with
          | None -> []
          | Some gv ->
            match Goal_view.focused gv with
            | None -> []
            | Some sg ->
              [ "    conclusion: " ^ Goal_view.to_pp_text sg.conclusion ]
        in
        let verb_word = verb_keyword r.verb in
        (Printf.sprintf "  would %s cleanly:" verb_word)
        :: ("    " ^ g_summary)
        :: g_detail
        @ (if body = "" then []
           else [ "    body: " ^ truncate_to (w - 10) body ])
      | Preview_err msg ->
        (Printf.sprintf "  would NOT %s:" (verb_keyword r.verb)) ::
        List.map (fun l -> "    " ^ l) (word_wrap (w - 6) msg)
    in
    let attr_header = A.(fg cyan ++ st bold) in
    let attr_ok = A.(fg green) in
    let attr_err = A.(fg red) in
    let outcome_attr = match r.preview with
      | Preview_none -> A.(fg lightblack)
      | Preview_ok _ -> attr_ok
      | Preview_err _ -> attr_err
    in
    I.vcat (
      bar ~w "selected lemma preview"
      :: List.map (fun l -> I.string attr_header (truncate_to w l)) sig_lines
      @ I.string A.empty ""
        :: List.map (fun l -> I.string outcome_attr (truncate_to w l)) outcome_lines)

let render_diagnostic_log ~w (t : t) =
  let visible = List.filteri (fun i _ -> i < 15) t.log in
  if visible = [] then I.empty
  else I.vcat (
    bar ~w "picker log"
    :: List.rev_map (fun l ->
        I.string A.(fg lightblack) (truncate_to w l)) visible)

let render_log ~w (t : t) =
  (* In apply-lemma stage, the lower pane switches content based on
     which field has focus:
     - Search / Filter focus → diagnostic log (shows search errors,
       hit counts, parse details — essential while typing patterns).
     - Results focus → per-hit lemma preview (signature + speculative
       outcome).
     Other stages always show the diagnostic log. *)
  match t.stage with
  | S_apply_lemma r when r.focus = `Results ->
    render_apply_lemma_preview ~w r
  | _ -> render_diagnostic_log ~w t

let render (t : t) ~w ~h =
  let body = render_stage ~w t.stage in
  let logs = render_log ~w t in
  let stack = I.(body <-> void w 1 <-> logs) in
  (* Pad vertically so layout aligns in the TUI frame. *)
  let cur = I.height stack in
  if cur >= h then I.vcrop 0 (cur - h) stack
  else I.(stack <-> void w (h - cur))

(* --- Full key handling dispatch ---------------------------------- *)

let handle_key (t : t) (repl : Repl_core.state) (k : key) : key_result =
  let refresh_apply_lemma_filter (state : stage) : stage =
    match state with
    | S_apply_lemma r ->
      let filtered =
        Fuzzy_filter.filter r.filter_prompt r.results
          ~key:(fun (h : Search_result.hit) -> h.qname ^ " " ^ h.signature)
      in
      S_apply_lemma { r with filtered; cursor = 0 }
    | other -> other
  in
  let fetch_search_results (r : apply_lemma_state) =
    (* Strip trailing punctuation/whitespace from the user's pattern
       before building the EC command. Users instinctively type `.`
       at the end of an EC sentence — but the body template already
       supplies it, so a double period was parse-erroring. *)
    let trimmed =
      let s = String.trim r.search_prompt in
      let n = String.length s in
      let rec back i =
        if i <= 0 then 0
        else match s.[i - 1] with
        | '.' | ' ' | '\t' -> back (i - 1)
        | _ -> i
      in
      String.sub s 0 (back n)
    in
    if trimmed = "" then r
    else begin
      let corr = Correlation.of_client "sem-search" in
      let body = "search " ^ trimmed ^ "." in
      push_log t ("send: " ^ body);
      match
        Ec_llm_session.exec repl.session ~corr
          ~sentence_class:`Directive ~source:body
      with
      | Error e ->
        (* EC returns a TypeError with a candidate list embedded in
           the detail string when the pattern is ambiguous — the
           user's pattern matched multiple operators and EC wants
           disambiguation. Surface the error text so the user sees
           the candidates, same as `:try search`. Split on newlines
           and push each to the log pane. *)
        let detail = Error.to_string e in
        push_log t "search failed:";
        List.iter (fun line ->
          if String.trim line <> "" then push_log t ("  " ^ line))
          (String.split_on_char '\n' detail);
        { r with results = []; filtered = []; cursor = 0 }
      | Ok ok ->
        let hits = Search_result.of_notices ok.notices in
        push_log t (Printf.sprintf "search %S → %d hits (from %d notices)"
                      trimmed (List.length hits)
                      (List.length ok.notices));
        { r with results = hits; cursor = 0 }
    end
  in
  match t.stage, k with
  | S_pick_tactic { cursor }, (`Arrow `Down, _) ->
    t.stage <- S_pick_tactic { cursor = clamp_cursor (cursor + 1) (List.length tactic_catalog) };
    Continue
  | S_pick_tactic { cursor }, (`Arrow `Up, _) ->
    t.stage <- S_pick_tactic { cursor = clamp_cursor (cursor - 1) (List.length tactic_catalog) };
    Continue
  | S_pick_tactic { cursor }, (`Enter, _) ->
    let chosen =
      try Some (List.nth tactic_catalog cursor) with _ -> None
    in
    (match chosen with
     | None -> Continue
     | Some Apply_hyp ->
       t.stage <- enter_apply_hyp repl.session;
       Continue
     | Some Move_intros ->
       t.stage <- enter_move_intros repl.session;
       Continue
     | Some Rewrite ->
       t.stage <- enter_rewrite_build repl.session;
       Continue
     | Some Apply_lemma ->
       t.stage <- enter_apply_lemma ();
       Continue
     | Some Rewrite_lemma ->
       t.stage <- enter_rewrite_lemma ();
       Continue
     | Some Suggest_closers ->
       enter_suggest t repl.session;
       Continue_refresh)
  | S_pick_tactic _, (`Escape, _) -> Exit_cancel

  | S_apply_hyp { cursor; hyps }, (`Arrow `Down, _) ->
    t.stage <- S_apply_hyp { cursor = clamp_cursor (cursor + 1) (List.length hyps); hyps };
    Continue
  | S_apply_hyp { cursor; hyps }, (`Arrow `Up, _) ->
    t.stage <- S_apply_hyp { cursor = clamp_cursor (cursor - 1) (List.length hyps); hyps };
    Continue
  | S_apply_hyp { cursor; hyps }, (`Enter, _) when hyps <> [] ->
    let h = List.nth hyps cursor in
    Exit_finalize (apply_hyp_source h)
  | S_apply_hyp _, (`Escape, _) ->
    t.stage <- S_pick_tactic { cursor = 0 };
    Continue

  | S_move_intros r, (`Enter, _) when r.input = "" && r.tokens <> [] ->
    (* Enter on empty input with at least one token = finalize.
       Robust across terminals that swallow Ctrl+F. *)
    let cmd = move_cumulative_source r.tokens in
    (match finalize_write_and_insert repl ~handle:r.speculation ~source:cmd with
     | Ok () -> Exit_cancel
     | Error e ->
       push_log t ("finalize failed: " ^ e);
       Continue)
  | S_move_intros r, (`Enter, _) when r.input <> "" ->
    let candidate_tokens = r.tokens @ [ String.trim r.input ] in
    let cmd = move_cumulative_source candidate_tokens in
    let outcome = try_text_cumulative repl.session ~handle:r.speculation cmd in
    (match outcome with
     | Trial_ok _ ->
       (* Candidate worked — commit it, clear input for the next token. *)
       t.stage <- S_move_intros {
         r with input = ""; tokens = candidate_tokens;
                last_command = cmd; last_outcome = outcome
       }
     | Trial_err _ | Trial_pending ->
       (* Candidate failed — don't promote the token. try_text_
          cumulative rolled back before attempting, so session is
          currently at the capture. Re-apply the previously-good
          tokens so the goals pane matches what the UI is still
          showing. Preserve the user's input so they can edit it. *)
       (if r.tokens <> [] then
          let good_cmd = move_cumulative_source r.tokens in
          ignore (try_text_cumulative repl.session
                    ~handle:r.speculation good_cmd));
       t.stage <- S_move_intros {
         r with last_command = cmd;  (* show the bad attempt *)
                last_outcome = outcome  (* error message visible *)
       });
    Continue_refresh
  | S_move_intros r, (`Backspace, _) when r.input <> "" ->
    let len = String.length r.input in
    t.stage <- S_move_intros { r with input = String.sub r.input 0 (len - 1) };
    Continue
  | S_move_intros r, (`Backspace, _) when r.tokens <> [] ->
    (* Drop last committed token, re-try cumulative. *)
    let tokens' = List.rev (List.tl (List.rev r.tokens)) in
    let cmd =
      if tokens' = [] then "" else move_cumulative_source tokens'
    in
    let outcome =
      if cmd = "" then (
        (* Back to empty — just rollback and clear. *)
        (match P.discard r.speculation with
         | Ok _ -> () | Error _ -> ());
        Trial_pending)
      else try_text_cumulative repl.session ~handle:r.speculation cmd
    in
    t.stage <- S_move_intros { r with tokens = tokens';
                                      last_command = cmd;
                                      last_outcome = outcome };
    Continue_refresh
  | S_move_intros r, (`ASCII 'f', mods)
  | S_move_intros r, (`ASCII 'F', mods) when List.mem `Ctrl mods ->
    (* Ctrl+F = finalize. notty reports Ctrl+F as (`ASCII 'f',
       [`Ctrl]); matching on raw \006 never fired. *)
    if r.tokens = [] then begin
      push_log t "finalize: no tokens yet";
      Continue
    end
    else begin
      let cmd = move_cumulative_source r.tokens in
      match finalize_write_and_insert repl ~handle:r.speculation ~source:cmd with
      | Ok () -> Exit_cancel
      | Error e ->
        push_log t ("finalize failed: " ^ e);
        Continue
    end
  | S_move_intros r, (`ASCII c, _) ->
    t.stage <- S_move_intros { r with input = r.input ^ String.make 1 c };
    Continue
  | S_move_intros r, (`Uchar u, _) ->
    let buf = Buffer.create 4 in
    Buffer.add_utf_8_uchar buf u;
    t.stage <- S_move_intros { r with input = r.input ^ Buffer.contents buf };
    Continue
  | S_move_intros r, (`Escape, _) ->
    (* Rollback any partial speculation and return to tactic picker. *)
    (match P.discard r.speculation with
     | Ok _ -> () | Error _ -> ());
    t.stage <- S_pick_tactic { cursor = 1 };  (* remember Move_intros cursor *)
    Continue_refresh

  | S_rewrite_build r, (`Enter, _) when r.input = "" && r.tokens <> [] ->
    (* Enter on empty input with at least one token = finalize. *)
    let cmd = rewrite_cumulative_source r.tokens in
    (match finalize_write_and_insert repl ~handle:r.speculation ~source:cmd with
     | Ok () -> Exit_cancel
     | Error e ->
       push_log t ("finalize failed: " ^ e);
       Continue)
  | S_rewrite_build r, (`Enter, _) when r.input <> "" ->
    let candidate_tokens = r.tokens @ [ String.trim r.input ] in
    let cmd = rewrite_cumulative_source candidate_tokens in
    let outcome = try_text_cumulative repl.session ~handle:r.speculation cmd in
    (match outcome with
     | Trial_ok _ ->
       t.stage <- S_rewrite_build {
         r with input = ""; tokens = candidate_tokens;
                last_command = cmd; last_outcome = outcome
       }
     | Trial_err _ | Trial_pending ->
       (* Don't promote a bad token. Re-apply good tokens so goals
          pane reflects the visible token list. Preserve input. *)
       (if r.tokens <> [] then
          let good_cmd = rewrite_cumulative_source r.tokens in
          ignore (try_text_cumulative repl.session
                    ~handle:r.speculation good_cmd));
       t.stage <- S_rewrite_build {
         r with last_command = cmd; last_outcome = outcome
       });
    Continue_refresh
  | S_rewrite_build r, (`Backspace, _) when r.input <> "" ->
    let len = String.length r.input in
    t.stage <- S_rewrite_build { r with input = String.sub r.input 0 (len - 1) };
    Continue
  | S_rewrite_build r, (`Backspace, _) when r.tokens <> [] ->
    let tokens' = List.rev (List.tl (List.rev r.tokens)) in
    let cmd =
      if tokens' = [] then "" else rewrite_cumulative_source tokens'
    in
    let outcome =
      if cmd = "" then begin
        (match P.discard r.speculation with
         | Ok _ -> () | Error _ -> ());
        Trial_pending
      end
      else try_text_cumulative repl.session ~handle:r.speculation cmd
    in
    t.stage <- S_rewrite_build { r with tokens = tokens';
                                        last_command = cmd;
                                        last_outcome = outcome };
    Continue_refresh
  | S_rewrite_build r, (`ASCII c, _) ->
    t.stage <- S_rewrite_build { r with input = r.input ^ String.make 1 c };
    Continue
  | S_rewrite_build r, (`Uchar u, _) ->
    let buf = Buffer.create 4 in
    Buffer.add_utf_8_uchar buf u;
    t.stage <- S_rewrite_build { r with input = r.input ^ Buffer.contents buf };
    Continue
  | S_rewrite_build r, (`Escape, _) ->
    (match P.discard r.speculation with
     | Ok _ -> () | Error _ -> ());
    t.stage <- S_pick_tactic { cursor = 2 };
    Continue_refresh

  | S_apply_lemma r, (`Tab, _) ->
    let next = match r.focus with
      | `Search -> `Filter
      | `Filter -> `Results
      | `Results -> `Search
    in
    (* Kill the preview when leaving Results focus so the goals
       pane reflects the pre-apply state again. *)
    let r' = if r.focus = `Results && next <> `Results
      then clear_preview repl.session r else r
    in
    let r'' = { r' with focus = next } in
    (* Entering Results with a non-empty list: fire first preview. *)
    let r_final =
      if next = `Results && r''.filtered <> [] && r''.preview_handle = None
      then begin
        let idx = clamp_cursor r''.cursor (List.length r''.filtered) in
        let hit = (List.nth r''.filtered idx).item in
        let (outcome, handle) =
          run_preview_lemma ~verb:r.verb repl.session None hit
        in
        { r'' with preview_handle = Some handle;
                   preview_cursor = idx;
                   preview = outcome }
      end
      else r''
    in
    t.stage <- S_apply_lemma r_final;
    Continue_refresh
  | S_apply_lemma r, (`Enter, _) when r.focus = `Search ->
    (* Any in-flight preview (from a prior cursor position) is
       invalidated by a new search; clear it so the search re-run
       starts from clean state. *)
    let r = clear_preview repl.session r in
    let r' = fetch_search_results r in
    t.stage <- refresh_apply_lemma_filter (S_apply_lemma { r' with focus = `Filter });
    Continue_refresh
  | S_apply_lemma r, (`Enter, _) when r.focus = `Results && r.filtered <> [] ->
    let pick : Search_result.hit Fuzzy_filter.match_result =
      List.nth r.filtered (clamp_cursor r.cursor (List.length r.filtered))
    in
    (* Rollback preview so finalize can cmd_insert from a clean
       session state — otherwise cmd_insert's exec would be
       double-applying. *)
    let _ = clear_preview repl.session r in
    Exit_finalize (lemma_picker_source ~verb:r.verb pick.item)
  | S_apply_lemma r, (`Arrow `Down, _) when r.focus = `Results ->
    let new_cursor = clamp_cursor (r.cursor + 1) (List.length r.filtered) in
    let r' =
      if new_cursor <> r.preview_cursor && r.filtered <> [] then begin
        let hit = (List.nth r.filtered new_cursor).item in
        let (outcome, handle) =
          run_preview_lemma ~verb:r.verb repl.session r.preview_handle hit
        in
        { r with cursor = new_cursor;
                 preview_handle = Some handle;
                 preview_cursor = new_cursor;
                 preview = outcome }
      end
      else { r with cursor = new_cursor }
    in
    t.stage <- S_apply_lemma r';
    Continue_refresh
  | S_apply_lemma r, (`Arrow `Up, _) when r.focus = `Results ->
    let new_cursor = clamp_cursor (r.cursor - 1) (List.length r.filtered) in
    let r' =
      if new_cursor <> r.preview_cursor && r.filtered <> [] then begin
        let hit = (List.nth r.filtered new_cursor).item in
        let (outcome, handle) =
          run_preview_lemma ~verb:r.verb repl.session r.preview_handle hit
        in
        { r with cursor = new_cursor;
                 preview_handle = Some handle;
                 preview_cursor = new_cursor;
                 preview = outcome }
      end
      else { r with cursor = new_cursor }
    in
    t.stage <- S_apply_lemma r';
    Continue_refresh
  | S_apply_lemma r, (`Backspace, _) when r.focus = `Search ->
    let n = String.length r.search_prompt in
    t.stage <- S_apply_lemma {
      r with search_prompt =
               if n = 0 then "" else String.sub r.search_prompt 0 (n - 1)
    };
    Continue
  | S_apply_lemma r, (`Backspace, _) when r.focus = `Filter ->
    let n = String.length r.filter_prompt in
    let filter_prompt = if n = 0 then "" else String.sub r.filter_prompt 0 (n - 1) in
    t.stage <- refresh_apply_lemma_filter
        (S_apply_lemma { r with filter_prompt });
    Continue
  | S_apply_lemma r, (`ASCII c, _) when r.focus = `Search ->
    t.stage <- S_apply_lemma { r with search_prompt = r.search_prompt ^ String.make 1 c };
    Continue
  | S_apply_lemma r, (`ASCII c, _) when r.focus = `Filter ->
    let filter_prompt = r.filter_prompt ^ String.make 1 c in
    t.stage <- refresh_apply_lemma_filter
        (S_apply_lemma { r with filter_prompt });
    Continue
  | S_apply_lemma r, (`Escape, _) ->
    let _ = clear_preview repl.session r in
    t.stage <- S_pick_tactic { cursor = 3 };
    Continue_refresh

  | S_suggest ({ cursor; rows; _ } as r), (`Arrow `Down, _) ->
    t.stage <- S_suggest
        { r with cursor = clamp_cursor (cursor + 1) (List.length rows) };
    Continue
  | S_suggest ({ cursor; rows; _ } as r), (`Arrow `Up, _) ->
    t.stage <- S_suggest
        { r with cursor = clamp_cursor (cursor - 1) (List.length rows) };
    Continue
  | S_suggest { cursor; rows; _ }, (`Enter, _) when rows <> [] ->
    let row = List.nth rows (clamp_cursor cursor (List.length rows)) in
    Exit_finalize row.src
  | S_suggest _, (`Escape, _) ->
    t.stage <- S_pick_tactic { cursor = 4 };
    Continue

  | _ -> Continue
