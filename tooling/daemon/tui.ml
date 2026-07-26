(** `ecd tui` — notty-based terminal UI over [Repl_core].

    Layout (height-adapts to terminal size):

      ┌─ source (left, scrolling) ───┬─ goals (right-top) ──────┐
      │  · 1 require import …         │  current goal            │
      │  · 2 op one : int = 1.        │    one = 1               │
      │  ▶ 3 lemma l : one = 1.       ├─ result (right-bottom) ──┤
      │    4 proof.                   │  output of :try / :feed  │
      │    5 qed.                     │                          │
      ├─ log (full width) ───────────┴──────────────────────────┤
      │  [executable Goperator uuid=2]                           │
      ├─ cmd line ───────────────────────────────────────────────┤
      │  [space]step  [b]back  [r]reload  [:]cmd  [q]quit        │
      └──────────────────────────────────────────────────────────┘

    Source scrolls so the cursor ▶ stays in view. Every keybind
    dispatches a REPL command string through [Repl_core.dispatch] —
    parity rule (memory: feedback_tui_matches_repl). *)

open Ecd_core
open Eio.Std
module N = Notty
module T = Notty_unix.Term
module A = N.A
module I = N.I

(* --- UI state ------------------------------------------------------ *)

type ui = {
  st : Repl_core.state;
  mutable log : string list;       (** newest-first, capped *)
  mutable result : string list;    (** newest-first, capped *)
  mutable goals_cache : string;
  mutable goals_structured : bool;
  mutable mode : [ `Normal | `Command of string | `Semantic of Semantic_tui.t ];
  mutable redraw : unit -> unit;
  (** Patched by [run] once the terminal + render closure exist.
      Handlers that need to push intermediate frames (e.g. the
      semantic-TUI's closer-suggester sweep) invoke this. *)
  mutable history : string list;
  (** Previously-dispatched command-mode strings, newest-first. *)
  mutable history_cursor : int option;
  (** [None] when the user is typing a fresh command. [Some i] when
      browsing history; [i=0] is the most recent entry. *)
  mutable history_typing : string;
  (** Buffer saved when the user starts browsing history, so Down
      can return to it past the newest entry. *)
}

let log_cap = 500
let result_cap = 500

let clamp_cap cap xs =
  if List.length xs > cap then List.filteri (fun i _ -> i < cap) xs else xs

let push_log ui s = ui.log <- clamp_cap log_cap (s :: ui.log)
let push_result ui s = ui.result <- clamp_cap result_cap (s :: ui.result)

let refresh_goals ui =
  if ui.goals_structured then
    match Ec_llm_session.goals ~structured:true ui.st.session with
    | Ok s    -> ui.goals_cache <- s
    | Error e -> ui.goals_cache <- "goals: " ^ Error.to_string e
  else
    (* Route the TUI goals pane through the same focused-goal
       renderer used by the REPL's [:goals] so the two frontends
       show identical content (per the parity rule). *)
    ui.goals_cache <- Repl_core.focused_goal_text ui.st

(* --- Small helpers ------------------------------------------------- *)

let pad_to n s =
  let len = String.length s in
  if len >= n then String.sub s 0 n
  else s ^ String.make (n - len) ' '

let truncate_to n s =
  if String.length s > n then String.sub s 0 (max 0 (n - 1)) ^ "…"
  else s

(* A full-width horizontal rule using the U+2500 box-drawing glyph
   for proper line fill (strings don't pad with box glyphs, only
   spaces). *)
let hline w = I.uchar A.(fg lightblack) (Uchar.of_int 0x2500) w 1

let bar ~w label =
  (* Label segment: "─── <label> ". The head is 3 "─" columns, then
     the label text padded by a space on each side. Tail: fill the
     rest of the width with "─" so separators look continuous. *)
  let head_cols = 3 in
  let label_cols = 2 + String.length label in
  let fill_cols = max 0 (w - head_cols - label_cols) in
  let head  = I.string A.(fg lightblack) "───" in
  let lbl   = I.string A.(fg lightblack) (" " ^ label ^ " ") in
  let tail  = if fill_cols > 0 then hline fill_cols else I.empty in
  I.hcat [ head; lbl; tail ]

(* One-column tall vertical separator of height [h]. *)
let vsep h =
  let line = I.string A.(fg lightblack) "│" in
  let rec stack n acc =
    if n <= 0 then acc else stack (n - 1) I.(acc <-> line)
  in
  stack (max 0 (h - 1)) line

(* Pad an image vertically to exactly [h] rows. Crops if too tall,
   adds blank rows at the bottom if too short. Ensures each pane
   occupies its advertised cell so the cmd-line docks to the terminal
   bottom regardless of content length. *)
let fit_height ~w ~h img =
  let cur = I.height img in
  if cur >= h then I.vcrop 0 (cur - h) img
  else I.(img <-> void w (h - cur))

(* Lines of newest-first list, oldest-at-top for display; capped to
   [height] most recent entries. *)
let recent_lines xs height =
  let rec take n = function
    | [] -> []
    | _ when n <= 0 -> []
    | x :: rest -> x :: take (n - 1) rest
  in
  List.rev (take height xs)

(* --- Rendering ----------------------------------------------------- *)

let render_source ui ~w ~h =
  match ui.st.doc with
  | None ->
    I.string A.(fg lightblack) "(no document loaded — :load PATH)"
  | Some d ->
    let cursor = List.length ui.st.executed in
    let executables =
      List.filter (fun (sn : Document.sentence) -> sn.parsed.cls <> `Meta)
        d.sentences
    in
    let total = List.length executables in
    (* Scroll window: keep cursor one third from the top when possible. *)
    let window_start =
      let ideal = cursor - (h / 3) in
      max 0 (min ideal (max 0 (total - h)))
    in
    let window_end = min total (window_start + h) in
    let row i (sn : Document.sentence) =
      let marker =
        if i = cursor then "▶"
        else if i < cursor then "·"
        else " "
      in
      let attr =
        if i < cursor then A.(fg lightblack)
        else if i = cursor then A.(fg lightyellow ++ st bold)
        else A.empty
      in
      let src = String.map (function '\n' -> ' ' | c -> c) sn.parsed.src in
      I.string attr
        (truncate_to w
           (Printf.sprintf "%s %3d %-10s %s"
              marker (i + 1) sn.parsed.kind src))
    in
    let rows =
      List.filteri
        (fun i _ -> i >= window_start && i < window_end)
        executables
      |> List.mapi (fun off sn -> row (window_start + off) sn)
    in
    I.vcat rows

let render_goals ui ~w ~h =
  let lines = String.split_on_char '\n' ui.goals_cache in
  let imgs =
    List.map (fun l -> I.string A.empty (truncate_to w l)) lines
  in
  let full = I.vcat imgs in
  I.vcrop 0 (max 0 (I.height full - h)) full

let render_result ui ~w ~h =
  let lines = recent_lines ui.result h in
  I.vcat (List.map (fun l -> I.string A.empty (truncate_to w l)) lines)

let render_log ui ~w ~h =
  let lines = recent_lines ui.log h in
  I.vcat
    (List.map (fun l -> I.string A.(fg lightblack) (truncate_to w l)) lines)

let render_cmdline ui ~w =
  match ui.mode with
  | `Normal ->
    let hint =
      " [space/Enter]step  [b]back  [r]reload  [R]restart  \
       [t]try  [i]insert  [e]edit  [d]delete  [s]emantic  [S]ave  [D]iff  \
       [ [ ] ]goal±  [g]goals  [:]cmd  [?]help  [q]quit"
    in
    I.string A.(bg lightblack ++ fg white) (pad_to w (truncate_to w hint))
  | `Command buf ->
    let text = ":" ^ buf ^ "█" in
    I.string A.(bg black ++ fg lightyellow) (pad_to w (truncate_to w text))
  | `Semantic _ ->
    I.string A.(bg black ++ fg cyan)
      (pad_to w (truncate_to w "semantic edit — Esc to exit"))

(* Layout:
     ─── source … ───────────┬─── goals ──────
     [source pane]           │ [goals pane]
                             │────── result ──
                             │ [result pane]
     ─── log ────────────────┴────────────────
     [log pane]
     [cmd line]
   Vertical `│` separator runs the full height of the top area; per-
   column horizontal bars sit inside each column so the junction is
   visually clean (even though we don't draw ┬/┴ box glyphs). *)
let render ui ~w ~h =
  let cmd = render_cmdline ui ~w in
  let cmd_h = I.height cmd in
  let log_h = 6 in
  let section_h = 1 in
  let sep_w = 1 in
  (* top_h = (source bar + source rows) = (goals bar + goals rows +
     result bar + result rows). We pick an overall top-area height
     and distribute within each column. *)
  (* Bottom stack = log-bar + log_h + log-close-bar + cmd.
     [section_h] counts each of the two log bars. *)
  let top_h = max 5 (h - cmd_h - section_h - log_h - section_h) in
  let left_w = max 20 ((w - sep_w) * 3 / 5) in
  let right_w = max 20 (w - left_w - sep_w) in
  let source_h = max 3 (top_h - section_h) in
  let goals_h = max 3 ((top_h - section_h - section_h) / 2) in
  let result_h = max 2 (top_h - section_h - section_h - goals_h) in
  let source_label =
    match ui.st.doc with
    | None -> "source"
    | Some d ->
      let cursor = List.length ui.st.executed in
      Printf.sprintf "source  %s  (%d/%d)"
        d.uri cursor (List.length d.sentences)
  in
  let left_col =
    match ui.mode with
    | `Semantic sem ->
      (* Picker replaces the source-browsing pane on the left;
         goals + result stay visible on the right so the user sees
         the effect of each speculative exec live. *)
      I.vcat [
        bar ~w:left_w "semantic edit";
        fit_height ~w:left_w ~h:source_h
          (Semantic_tui.render sem ~w:left_w ~h:source_h);
      ]
    | _ ->
      I.vcat [
        bar ~w:left_w source_label;
        fit_height ~w:left_w ~h:source_h
          (render_source ui ~w:left_w ~h:source_h);
      ]
  in
  let right_col =
    I.vcat [
      bar ~w:right_w "goals";
      fit_height ~w:right_w ~h:goals_h
        (render_goals ui ~w:right_w ~h:goals_h);
      bar ~w:right_w "result";
      fit_height ~w:right_w ~h:result_h
        (render_result ui ~w:right_w ~h:result_h);
    ]
  in
  let sep = vsep top_h in
  let top =
    fit_height ~w ~h:top_h
      (I.hcat [ left_col; sep; right_col ])
  in
  let log_pane =
    fit_height ~w ~h:log_h (render_log ui ~w ~h:log_h)
  in
  (* Fixed bottom stack: log-bar (1) + log_pane (log_h) + close-bar
     (1) + cmd (1). The close-bar visually separates the log from
     the key-hint / command-input line. Padding lives inside [top];
     the cmd row always lands at terminal-row h-1. *)
  I.vcat [ top; bar ~w "log"; log_pane; hline w; cmd ]

(* --- Event handling ------------------------------------------------ *)

let run_cmd ui line =
  try
    Repl_core.dispatch ui.st line;
    refresh_goals ui;
    `Continue
  with
  | Repl_core.Quit -> `Quit
  | e ->
    push_log ui (Printf.sprintf "error: %s" (Printexc.to_string e));
    `Continue

let enter_command ui prefix =
  ui.mode <- `Command prefix;
  ui.history_cursor <- None;
  ui.history_typing <- ""

let history_cap = 200

let push_history ui entry =
  if entry = "" then ()
  else
    let deduped =
      match ui.history with
      | h :: _ when h = entry -> ui.history  (* no consecutive dup *)
      | _ -> entry :: ui.history
    in
    ui.history <-
      (if List.length deduped > history_cap
       then List.filteri (fun i _ -> i < history_cap) deduped
       else deduped)

(* Replace the current command buffer from history at position [i],
   where i=0 is the newest entry. Returns the new buffer to render. *)
let history_at ui i =
  match List.nth_opt ui.history i with
  | Some s -> s
  | None -> ui.history_typing

let handle_normal ui (k : N.Unescape.key) =
  match k with
  | `ASCII 'q', _      -> `Quit
  | `ASCII ' ', _
  | `Enter, _
  | `ASCII 'j', _      -> run_cmd ui ":step"
  | `ASCII 'b', _
  | `Arrow `Left, _
  | `ASCII 'k', _      -> run_cmd ui ":back"
  | `ASCII 'r', _      -> run_cmd ui ":reload"
  | `ASCII 'R', _      -> run_cmd ui ":restart"
  | `ASCII 'g', _      ->
    ui.goals_structured <- false;
    refresh_goals ui;
    `Continue
  | `ASCII 'J', _      ->
    ui.goals_structured <- not ui.goals_structured;
    refresh_goals ui;
    `Continue
  | `ASCII 'p', _      -> run_cmd ui ":pos"
  | `ASCII 't', _      -> enter_command ui "try "; `Continue
  | `ASCII 'i', _      -> enter_command ui "insert "; `Continue
  | `ASCII 'e', _      -> enter_command ui "edit "; `Continue
  | `ASCII 'd', _      -> run_cmd ui ":delete"
  | `ASCII 'S', _      -> run_cmd ui ":save"
  | `ASCII 'D', _      -> run_cmd ui ":diff"
  | `ASCII ']', _      -> run_cmd ui ":next-goal"
  | `ASCII '[', _      -> run_cmd ui ":prev-goal"
  | `ASCII '?', _
  | `ASCII 'h', _      -> run_cmd ui ":help"
  | `ASCII ':', _      -> enter_command ui ""; `Continue
  | `ASCII 's', _      ->
    let sem = Semantic_tui.begin_ () in
    sem.redraw <- ui.redraw;
    ui.mode <- `Semantic sem;
    `Continue
  | _ -> `Continue

let handle_command ui buf (k : N.Unescape.key) =
  match k with
  | `Enter, _ ->
    ui.mode <- `Normal;
    push_history ui buf;
    ui.history_cursor <- None;
    ui.history_typing <- "";
    if buf = "" then `Continue
    else run_cmd ui (":" ^ buf)
  | `Escape, _ ->
    ui.mode <- `Normal;
    ui.history_cursor <- None;
    ui.history_typing <- "";
    `Continue
  | `Backspace, _ ->
    let n = String.length buf in
    ui.mode <- `Command (if n = 0 then "" else String.sub buf 0 (n - 1));
    ui.history_cursor <- None;
    `Continue
  | `Arrow `Up, _ ->
    if ui.history = [] then `Continue
    else begin
      let next =
        match ui.history_cursor with
        | None ->
          ui.history_typing <- buf;
          0
        | Some i -> min (i + 1) (List.length ui.history - 1)
      in
      ui.history_cursor <- Some next;
      ui.mode <- `Command (history_at ui next);
      `Continue
    end
  | `Arrow `Down, _ ->
    (match ui.history_cursor with
     | None -> `Continue
     | Some 0 ->
       ui.history_cursor <- None;
       ui.mode <- `Command ui.history_typing;
       `Continue
     | Some i ->
       let next = i - 1 in
       ui.history_cursor <- Some next;
       ui.mode <- `Command (history_at ui next);
       `Continue)
  | `ASCII c, _ ->
    ui.mode <- `Command (buf ^ String.make 1 c);
    ui.history_cursor <- None;
    `Continue
  | _ -> `Continue

let handle_semantic ui (sem : Semantic_tui.t) (k : N.Unescape.key) =
  match Semantic_tui.handle_key sem ui.st k with
  | Semantic_tui.Continue -> `Continue
  | Semantic_tui.Continue_refresh ->
    refresh_goals ui;
    `Continue
  | Semantic_tui.Exit_cancel | Semantic_tui.Exit_cancel_with_rollback _ ->
    ui.mode <- `Normal;
    refresh_goals ui;
    `Continue
  | Semantic_tui.Exit_finalize source ->
    (* Treat like `:insert <source>`: goes through the shared code
       path so the document buffer updates correctly. *)
    Repl_core.cmd_insert ui.st source;
    ui.mode <- `Normal;
    refresh_goals ui;
    `Continue

let handle_event ui = function
  | `Key k ->
    (match ui.mode with
     | `Normal -> handle_normal ui k
     | `Command buf -> handle_command ui buf k
     | `Semantic sem -> handle_semantic ui sem k)
  | `Resize _ -> `Continue
  | `Mouse _ | `Paste _ -> `Continue
  | `End -> `Quit

(* --- Entry point --------------------------------------------------- *)

let run ?load_file ~bin ~extra_args () =
  Eio_main.run @@ fun env ->
  Switch.run @@ fun sw ->
  Transcript.configure (Transcript.devnull ());
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr ~executable:bin ~extra_args ();
  let session = Ec_llm_session.start ~sw ~label:"tui" in
  let st = Repl_core.make ~session ~sw in
  let ui = {
    st;
    log = [];
    result = [];
    goals_cache = "(no goals yet)";
    goals_structured = false;
    mode = `Normal;
    history = [];
    history_cursor = None;
    history_typing = "";
    redraw = (fun () -> ());
  } in
  st.out <- push_log ui;
  st.result <- push_result ui;
  st.clear_result <- (fun () -> ui.result <- []);
  (* Optional startup file: load immediately so user can iterate
     without typing `:load` every run. Same code path as the
     interactive `:load` command. *)
  (match load_file with
   | None -> ()
   | Some path -> Repl_core.cmd_load st path);
  let term = T.create () in
  let cleanup () =
    T.release term;
    (try Ec_llm_session.close st.session with _ -> ())
  in
  let redraw () =
    let (w, h) = T.size term in
    T.image term (render ui ~w ~h)
  in
  ui.redraw <- redraw;
  refresh_goals ui;
  redraw ();
  let quit = ref false in
  (try
     while not !quit do
       match T.event term with
       | ev ->
         (match handle_event ui ev with
          | `Quit -> quit := true
          | `Continue -> redraw ())
     done
   with e ->
     cleanup ();
     raise e);
  cleanup ()
