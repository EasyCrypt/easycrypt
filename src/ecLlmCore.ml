(* -------------------------------------------------------------------- *)
(* Engine-facing core of the LLM interaction protocol. See
   [ecLlmCore.mli]. This module owns the session state and implements
   one function per meta-command; it never prints and never exits. The
   text envelope ([OK]/[ERROR]/[<END>]) is the front-end's business. *)

open EcUtils

module EP = EcParsetree

(* -------------------------------------------------------------------- *)
type body =
  | Goals
  | Text of string

type reply = {
  uuid    : int;
  tag     : string;
  notices : string;
  body    : body;
  changed : bool;
}

type failure = {
  uuid     : int;
  message  : string;
  goals    : string;
  notices  : string;
  reverted : bool;
  changed  : bool;
}

type answer =
  | Done of (reply, failure) result
  | Quit

exception Init_error of string

(* -------------------------------------------------------------------- *)
(* One recorded REPL phrase, as [Commit] needs to see it again.

   [en_penv] is the proof DAG as of just after the phrase ran, and it
   is per entry rather than per session on purpose: a session holding
   several lemmas has one DAG per lemma, handles are only meaningful in
   their own, and a single newest-wins snapshot answered "no parent"
   for every handle of every earlier proof -- which rendered those
   proofs flat, without their bullets. *)
type entry = {
  (* Engine uuid right before the phrase; UNDO/REVERT trim on it. *)
  en_uuid   : int;
  en_src    : string;
  (* Focused handle right before the phrase; [None] iff outside a
     proof, which is also what separates one proof from the next. *)
  en_parent : EcCoreGoal.handle option;
  (* Full open-handle list (focused first) right before the phrase,
     used to seed the sibling map when the first recorded phrase of a
     proof already sits inside a frame opened by the LOAD prefix. *)
  en_opens  : EcCoreGoal.handle list;
  en_penv   : EcCoreGoal.proofenv option;
}

(* -------------------------------------------------------------------- *)
(* Session state. The proof engine ([EcCommands]) is a global mutable
   singleton, so at most one [state] may exist per process. *)
type state = {
  (* Prover options as given on the command line: the base [LOAD]
     overlays the loaded file's [easycrypt.project] settings onto. *)
  base_prvopts : EcOptions.prv_options;

  (* Resolves the [easycrypt.project] context of a file path. *)
  projini : string option -> EcOptions.ini_context option;

  boot : bool;

  (* Prover options in effect: refreshed by [LOAD] with the loaded
     file's [easycrypt.project] settings overlaid on the command-line
     options, as the batch compiler does at option-parsing time. *)
  cur_prvopts : EcOptions.prv_options ref;

  (* Messages emitted by the engine during a phrase; flushed into the
     next reply. *)
  notices : Buffer.t;

  (* Has [EcCommands.initialize] been called? Subsequent calls pass
     [~restart:true]. *)
  initialized : bool ref;

  (* The include path as the session started: the prelude and stdlib
     roots, the command line's -I/-R/-stdlib entries, and the working
     directory. Every [LOAD] rewinds the (process-global) loader to it
     before adding the loaded file's own directory and its project's,
     so one file's neighbours are never visible to the next. *)
  base_loadpath : EcCommands.loadpath_mark;

  (* CHECKPOINT name -> uuid. *)
  checkpoints : (string, int) Hashtbl.t;

  (* Transcript of REPL-typed phrases that succeeded, newest first.
     Trimmed by UNDO/REVERT; cleared on LOAD/Restart. *)
  transcript : entry list ref;

  (* The bullet stack of the active proof at the moment REPL input
     took over. Captured the first time [disable_repl_bullets] clears
     a non-empty stack. Used by [Commit] to pick bullet characters
     that don't collide with frames opened by the LOAD prefix.
     Cleared with the transcript on LOAD/Restart. *)
  prior_bullets : EcBullets.stack option ref;
}

(* -------------------------------------------------------------------- *)
let checkmode_of (prvopts : EcOptions.prv_options) = {
  EcCommands.cm_checkall  = prvopts.prvo_checkall;
  EcCommands.cm_timeout   = odfl 3 prvopts.prvo_timeout;
  EcCommands.cm_cpufactor = odfl 1 prvopts.prvo_cpufactor;
  EcCommands.cm_nprovers  = odfl 4 prvopts.prvo_maxjobs;
  EcCommands.cm_provers   = prvopts.prvo_provers;
  EcCommands.cm_quorum    = prvopts.prvo_quorum;
  EcCommands.cm_profile   = prvopts.prvo_profile;
}

let notifier (st : state) =
  fun (_ : EcGState.loglevel) (lazy msg) ->
    Buffer.add_string st.notices msg;
    Buffer.add_char st.notices '\n'

let do_initialize (st : state) =
  let initialized = st.initialized in
  let cur_prvopts = st.cur_prvopts in
  EcCommands.initialize
    ~restart:!initialized ~undo:true
    ~boot:st.boot ~checkmode:(checkmode_of !cur_prvopts) ~checkproof:true;
  initialized := true;
  (try
     List.iter EcCommands.apply_pragma_option !cur_prvopts.prvo_pragmas
   with EcCommands.InvalidPragma x ->
     EcScope.hierror "invalid pragma: `%s'\n%!" x);
  EcCommands.addnotifier (notifier st);
  oiter (fun ppwidth ->
    let gs = EcEnv.gstate (EcScope.env (EcCommands.current ())) in
    EcGState.setvalue "PP:width" (`Int ppwidth) gs)
    !cur_prvopts.prvo_ppwidth

(* -------------------------------------------------------------------- *)
let create ~relocdir ~boot ~projini ~prvopts =
  Random.self_init ();

  prvopts.EcOptions.prvo_why3server |> oiter (fun server ->
    try
      Why3.Prove_client.connect_external server
    with Why3.Prove_client.ConnectionError e ->
      raise (Init_error (Format.asprintf
        "cannot connect to Why3 server `%s': %s" server e)));

  (match relocdir with
   | None     -> EcCommands.addidir Filename.current_dir_name
   | Some pwd -> EcCommands.addidir pwd);

  let st = {
    base_prvopts  = prvopts;
    projini;
    boot;
    cur_prvopts   = ref prvopts;
    notices       = Buffer.create 256;
    initialized   = ref false;
    base_loadpath = EcCommands.loadpath_mark ();
    checkpoints   = Hashtbl.create 16;
    transcript    = ref [];
    prior_bullets = ref None;
  } in

  (* [print] renders on the process's stdout by default, which in the
     REPL lands *before* the reply's status line -- outside the frame --
     and under MCP is swallowed whole, stdout being pointed at stderr
     there. Send it to the notice buffer, where the engine's other
     messages, [search] and [locate] included, already arrive. *)
  EcCommands.set_print_formatter (Format.formatter_of_buffer st.notices);

  do_initialize st; st

(* -------------------------------------------------------------------- *)
(* Goal/error formatting: shared between the reply layer and the
   -trace block. *)
module Goals = struct
  let format_error ?(src="") e =
    let base = match e with
      | EcScope.TopError (loc, e) ->
        let msg = String.strip (EcPException.tostring e) in
        if loc = EcLocation._dummy then msg
        else Format.asprintf "%s: %s" (EcLocation.tostring loc) msg
      | e ->
        String.strip (EcPException.tostring e)
    in
    if src = "" then base
    else Printf.sprintf "%s\nsource: %s" base src

  let goals_to_string ?(all=false) () =
    let buf = Buffer.create 256 in
    let fmt = Format.formatter_of_buffer buf in
    EcCommands.pp_current_goal_or_noproof ~all fmt;
    Format.pp_print_flush fmt ();
    Buffer.contents buf

  (* Inline focus annotation ([focus: 1/N]) appended to reply tags
     whenever the active proof has >=2 open subgoals. *)
  let focus_tag () =
    match EcCommands.pp_tree () with
    | _ :: _ :: _ as entries ->
      Printf.sprintf " [focus: 1/%d]" (List.length entries)
    | _ -> ""
end

(* -------------------------------------------------------------------- *)
(* Frame tree: group currently-open goals by their shared multi-child
   ancestors. Used by [Tree] (rendering) and [Focus] (path lookup).
   The tree is a *derivation*: it depends only on [pr_opened] and
   [parent_of], no recorded transcript. *)
module FrameTree = struct
  (* Internal nodes are split-point frames; leaves carry a handle
     (the open goal), its index in [pr_opened] (1-based, used by
     [EcCoreGoal.rotate_focus]), and its rendered text. *)
  type node =
    | Frame of node list                (* >=2 child branches *)
    | Leaf  of
        { idx     : int                 (* 1-based in pr_opened *)
        ; focused : bool                (* idx = 1 *)
        ; text    : string }            (* one-line conclusion *)

  (* Multi-child ancestors of [h], outermost first (= root-most
     split first, deepest split last). This ordering means leaves
     sharing the same OUTER frame will agree on the chain's first
     element, which is what [group] partitions on. *)
  let split_chain h =
    let rec walk h acc =
      match EcCommands.parent_of h with
      | None -> acc
      | Some p ->
        match EcCommands.children_of p with
        | [_] -> walk p acc
        | _   -> walk p (p :: acc)
    in
    (* [walk] prepends each ancestor as we go up; the result has
       outermost at the FRONT (we add it last). No reverse needed. *)
    walk h []

  (* Build the tree by grouping leaves with a common ancestor prefix.
     [leaves] is a list of (chain, leaf) in [pr_opened] order. The
     grouping is done recursively on the head of each chain. *)
  let rec group (leaves : (EcCoreGoal.handle list * node) list) : node list =
    let rec runs acc = function
      | [] -> List.rev acc
      | (chain, leaf) :: rest ->
        match chain with
        | [] -> runs (`Bare leaf :: acc) rest
        | hd :: tl ->
          let same_head, others =
            List.partition_map (fun (c, l) ->
              match c with
              | h :: tail when EcCoreGoal.eq_handle h hd ->
                Left (tail, l)
              | _ -> Right (c, l))
              rest
          in
          runs (`Group ((tl, leaf) :: same_head) :: acc) others
    in
    List.map
      (function
        | `Bare leaf -> leaf
        | `Group children -> Frame (group children))
      (runs [] leaves)

  (* Strip leading singleton frames so the top-level forest's
     indices match what the user thinks of as "top-level subgoals
     of the current frame." When all open leaves descend from a
     single outermost split, the top-level forest has one Frame
     containing the actual user-visible siblings; unwrap it. *)
  let rec unwrap forest =
    match forest with
    | [Frame children] -> unwrap children
    | _ -> forest

  let build () =
    let handles = EcCommands.open_handles () in
    let texts = EcCommands.pp_tree () in
    if handles = [] then []
    else
      let leaves =
        List.mapi (fun i (h, (_, focused, text)) ->
          let leaf = Leaf { idx = i + 1; focused; text } in
          (split_chain h, leaf))
          (List.combine handles texts)
      in
      unwrap (group leaves)

  (* Render the tree with dotted-path labels matching what FOCUS
     accepts. [all] requests full goal bodies (we re-query via
     [pp_tree ~all:true] keyed by leaf index). *)
  let render ?(all=false) () =
    let forest = build () in
    if forest = [] then "No active proof.\n"
    else
      let texts_all =
        if all then Some (EcCommands.pp_tree ~all:true ())
        else None
      in
      let one_line s =
        let s =
          match String.index_opt s '\n' with
          | None -> s
          | Some k -> String.sub s 0 k
        in
        let limit = 80 in
        if String.length s > limit
        then String.sub s 0 (limit - 1) ^ "…"
        else s
      in
      let buf = Buffer.create 256 in
      let rec emit ~depth ~path = function
        | Leaf { idx; focused; text } ->
          let label = String.concat "." (List.rev_map string_of_int path) in
          let marker = if focused then " <- focused" else "" in
          for _ = 1 to depth do Buffer.add_string buf "  " done;
          (match texts_all with
           | None ->
             Buffer.add_string buf
               (Printf.sprintf "[%s] %s%s\n"
                  label (one_line text) marker)
           | Some entries ->
             let (_, _, full) =
               List.nth entries (idx - 1)
             in
             Buffer.add_string buf
               (Printf.sprintf "[%s]%s\n%s\n" label marker full))
        | Frame children ->
          List.iteri (fun i child ->
            emit ~depth:(depth + 1) ~path:((i + 1) :: path) child)
            children
      in
      List.iteri (fun i node ->
        emit ~depth:0 ~path:[i + 1] node)
        forest;
      Buffer.contents buf

  (* Resolve a dotted path against the tree. Returns [Ok idx] where
     [idx] is the 1-based position in [pr_opened] of the selected
     leaf, or [Error msg]. *)
  let resolve_path (path : int list) : (int, string) result =
    let forest = build () in
    let rec walk ~components nodes =
      match components with
      | [] -> Error "FOCUS: path must select a leaf goal"
      | k :: rest ->
        if k < 1 || k > List.length nodes then
          Error (Printf.sprintf
            "FOCUS: index %d out of range (1..%d)"
            k (List.length nodes))
        else
          match List.nth nodes (k - 1), rest with
          | Leaf { idx; _ }, [] -> Ok idx
          | Leaf _, _ ->
            Error "FOCUS: path overshoots a leaf goal"
          | Frame _, [] ->
            Error "FOCUS: path must select a leaf goal, \
                   not a frame"
          | Frame kids, _ -> walk ~components:rest kids
    in
    if forest = [] then Error "FOCUS: no active proof"
    else walk ~components:path forest
end

(* -------------------------------------------------------------------- *)
(* Reply construction. The notice buffer is captured and cleared at
   exactly the points the text front-end used to print it, so that
   engine messages keep interleaving with replies as before. *)
let mk_reply (st : state) ~(pre : int) ?(tag = "") (body : body) =
  let notices = Buffer.contents st.notices in
  Buffer.clear st.notices;
  let uuid = EcCommands.uuid () in
  { uuid; tag; notices; body; changed = uuid <> pre; }

(* The body of a reply that ends on the current goals. The front-end
   decides whether to render them (QUIET is a presentation setting). *)
let mk_reply_goals (st : state) ~(pre : int) =
  let tag = Goals.focus_tag () in
  mk_reply st ~pre ~tag Goals

let mk_failure (st : state) ~(pre : int) (message : string) =
  let notices = Buffer.contents st.notices in
  Buffer.clear st.notices;
  let uuid = EcCommands.uuid () in
  { uuid; message; goals = Goals.goals_to_string (); notices;
    reverted = false; changed = uuid <> pre; }

(* -------------------------------------------------------------------- *)
(* Transcript manipulation. *)
module Transcript = struct
  let trim (st : state) target =
    let transcript = st.transcript in
    transcript :=
      List.filter (fun e -> e.en_uuid < target) !transcript

  let clear (st : state) =
    st.transcript := [];
    st.prior_bullets := None
end

(* -------------------------------------------------------------------- *)
(* Process a single EasyCrypt command, respecting [gl_fail]. When
   [~record:true], append a transcript entry on success: the parent
   handle (focused goal before the phrase) and the open-handle list,
   which together let [Commit] reconstruct bullet structure. *)
let process_action (st : state) ?(record=false) ~src (p : EP.global) =
  let transcript = st.transcript in
  let loc = p.EP.gl_action.EcLocation.pl_loc in
  let pre_uuid = EcCommands.uuid () in
  let opens_pre =
    if record then EcCommands.open_handles () else []
  in
  let parent =
    match opens_pre with h :: _ -> Some h | [] -> None
  in
  (* Queries only inspect the environment: they neither advance the
     proof nor belong in the body COMMIT emits. *)
  let is_query =
    match EcLocation.unloc p.EP.gl_action with
    | EP.Gprint _ | EP.Gsearch _ | EP.Glocate _ -> true
    | _ -> false
  in
  let succeeded = ref false in
  begin try
    ignore (EcCommands.process ~src p.EP.gl_action : float option);
    succeeded := true
  with
  | EcCommands.Restart -> raise EcCommands.Restart
  | _ when p.EP.gl_fail -> ()
  | e -> raise (EcScope.toperror_of_exn ~gloc:loc e)
  end;
  (* The engine pushes an undo context for every command it runs, a
     query included -- with the *same* scope, since a query returns the
     scope it was handed. Pop it back off: a read-only command must not
     spend a uuid, or REVERT targets and the MCP [readOnlyHint] would
     both be lying. A no-op when the query failed (nothing was pushed). *)
  if is_query then EcCommands.undo pre_uuid;
  if !succeeded && p.EP.gl_fail then
    raise (EcScope.toperror_of_exn ~gloc:loc
      (EcScope.HiScopeError (None,
        "this command is expected to fail")));
  if record && !succeeded && not p.EP.gl_fail && not is_query then
    (* The DAG is snapshot here, per phrase: a [proofenv] is immutable
       and cumulative *within one proof*, so this entry's snapshot
       answers for every handle its own proof can mention -- and, being
       its own, keeps answering after [qed] has discarded the proof and
       a later lemma has replaced it. A phrase that ends the proof
       leaves none active and so records [None]; such a phrase is
       outside a proof ([en_parent = None]) and its DAG is never
       consulted. *)
    transcript :=
      { en_uuid   = pre_uuid;
        en_src    = src;
        en_parent = parent;
        en_opens  = opens_pre;
        en_penv   = EcCommands.current_proofenv (); } :: !transcript

(* -------------------------------------------------------------------- *)
(* COMMIT: replay the transcript against the proof DAG (parent_of /
   children_of, backed by [EcCoreGoal.pr_parent]), inserting bullets
   at multi-child splits. Levels the LOAD prefix's [puc_bullets] stack
   already opened are addressed with that frame's own token; deeper
   levels get fresh tokens, chosen so they collide with neither the
   stack nor each other. *)
module Commit = struct
  (* Token order matches PR 1017's lexer: -, +, *, --, ++, **,
     ---, +++, *** ... *)
  let token_at_index i =
    let chars = [| "-"; "+"; "*" |] in
    let rep = i / 3 + 1 in
    let chr = chars.(i mod 3) in
    String.concat "" (List.init rep (fun _ -> chr))

  (* DAG queries go through the snapshot the entry recorded, so COMMIT
     still sees the structure of a proof [qed] has since discarded --
     and sees the *right* one when the session holds several. Fall back
     to the live proof for an entry that recorded no snapshot. *)
  let parent_of penv h =
    match penv with
    | Some penv -> EcCoreGoal.parent_of_handle penv h
    | None      -> EcCommands.parent_of h

  let children_of penv h =
    match penv with
    | Some penv -> EcCoreGoal.children_of_handle penv h
    | None      -> EcCommands.children_of h

  (* Position of [h] in the proof DAG: the child indices on the path
     from the root down to [h]. Lexicographic order on those paths is
     the DAG's preorder, which is the order in which a proof body has
     to discharge the subgoals -- and, FOCUS/NEXT being free to jump
     between open goals, not the order the phrases were typed in. *)
  let dag_path penv (h : EcCoreGoal.handle) =
    let rec walk h acc =
      match parent_of penv h with
      | None   -> acc
      | Some p ->
        let rec index i = function
          | []      -> i
          | c :: cs ->
            if EcCoreGoal.eq_handle c h then i else index (i + 1) cs
        in
        walk p (index 0 (children_of penv p) :: acc)
    in
    walk h []

  (* Cut the transcript at its proof boundaries. A phrase typed outside
     a proof ([en_parent = None]) is a [`Barrier] -- the lemma statement
     that opens a proof, the [qed] that closes it -- and each run of
     in-proof phrases between two of them belongs to exactly one proof.
     Both the DAG sort and the bullet state below are per proof, and
     this is what delimits one. *)
  let blocks entries =
    let close acc run = if run = [] then acc else `Run (List.rev run) :: acc in
    let rec walk acc run = function
      | [] -> List.rev (close acc run)
      | ({ en_parent = None; _ } as e) :: rest ->
        walk (`Barrier e :: close acc run) [] rest
      | e :: rest -> walk acc (e :: run) rest
    in
    walk [] [] entries

  (* Reorder one proof's phrases into DAG order, so that a body typed
     out of order (FOCUS 2, prove the second goal, come back to the
     first) still replays top to bottom. The sort is stable, so entries
     the DAG does not order keep their typing order. *)
  let dag_order run =
    let key e =
      match e.en_parent with
      | None   -> []
      | Some h -> dag_path e.en_penv h
    in
    List.stable_sort
      (fun a b -> compare (key a : int list) (key b))
      run

  let bullet_to_string (b : EcParsetree.bullet) =
    let ch =
      match b.b_kind with
      | `Minus -> "-"
      | `Plus  -> "+"
      | `Star  -> "*"
    in
    String.concat "" (List.init b.b_count (fun _ -> ch))

  let proof_text (st : state) =
    let buf = Buffer.create 1024 in
    let emit_indent depth =
      for _ = 1 to depth do Buffer.add_string buf "  " done
    in
    let module Hmap =
      Map.Make (struct
        type t = EcCoreGoal.handle
        let compare = compare
      end)
    in
    (* Render one proof's phrases. Every piece of bullet state --
       the sibling map, the current depth, the token reserved at each
       depth -- is local to this call, so one lemma can neither inherit
       another's indentation nor exhaust its token supply.
       [frames] are the bullet frames the LOAD prefix left open; they
       belong to the proof that was in progress when the REPL took
       over, hence to the first run only. *)
    let render_run ~(frames : EcBullets.frame list) run =
      let sibling_depth : int Hmap.t ref = ref Hmap.empty in
      let current_depth = ref 0 in
      let in_use_tokens =
        List.map
          (fun (f : EcBullets.frame) -> bullet_to_string f.bf_bullet)
          frames
      in
      let depth_cache : (int, string) Hashtbl.t = Hashtbl.create 8 in
      let next_tok_idx = ref 0 in
      let assigned_tokens = ref [] in
      (* Depths 1..k address the next sibling of a frame the prefix
         already opened, and strict bullets accepts nothing but that
         frame's own token there. Deeper levels get fresh tokens, so
         pre-populate the cache before any fresh pick happens. *)
      List.iteri (fun i (f : EcBullets.frame) ->
        let t = bullet_to_string f.bf_bullet in
        Hashtbl.replace depth_cache (i + 1) t;
        assigned_tokens := t :: !assigned_tokens)
        frames;
      let bullet_for_depth d =
        match Hashtbl.find_opt depth_cache d with
        | Some t -> t
        | None ->
          let rec pick () =
            let t = token_at_index !next_tok_idx in
            incr next_tok_idx;
            if List.mem t in_use_tokens || List.mem t !assigned_tokens
            then pick ()
            else t
          in
          let t = pick () in
          assigned_tokens := t :: !assigned_tokens;
          Hashtbl.add depth_cache d t;
          t
      in
      (* Seed: the goals already open when this proof's first recorded
         phrase ran were left there by the LOAD prefix, so COMMIT must
         place each of them at the depth the prefix's own bullets put it
         at. A frame with floor [f] is discharged once [f] goals remain,
         hence it still owns the first [n - f] goals of the focused-first
         list; a goal covered by [c] frames sits at depth [c + 1].
         Nothing to seed when the prefix left no frame and a single goal
         (the REPL just continues on the prefix's own focus). *)
      (match run with
       | { en_parent = Some _; en_opens = (_ :: _ as opens); en_penv; _ } :: _
         when frames <> [] || List.length opens >= 2 ->
         (* [pr_opened] is focused-first, so a FOCUS/NEXT run before the
            first recorded phrase leaves it rotated. The floors below
            count goals in the order the prefix's bullets consume them,
            which is DAG order. *)
         let opens =
           List.stable_sort
             (fun a b ->
                compare (dag_path en_penv a : int list) (dag_path en_penv b))
             opens
         in
         let n = List.length opens in
         List.iteri (fun i h ->
           let pos = i + 1 in
           let covering =
             List.length
               (List.filter
                  (fun (f : EcBullets.frame) -> pos <= n - f.bf_floor)
                  frames)
           in
           sibling_depth := Hmap.add h (covering + 1) !sibling_depth)
           opens
       | _ -> ());
      List.iter (fun e ->
        match e.en_parent with
        | None -> assert false        (* [blocks] keeps these out *)
        | Some parent ->
          let parent_of = parent_of e.en_penv in
          let children_of = children_of e.en_penv in
          (* Walk upward via pr_parent until we hit a registered
             sibling ancestor. If found, emit its bullet and consume
             the registration. *)
          let rec find_ancestor h =
            match Hmap.find_opt h !sibling_depth with
            | Some d -> Some (h, d)
            | None ->
              match parent_of h with
              | Some p -> find_ancestor p
              | None -> None
          in
          (match find_ancestor parent with
           | Some (h, d) ->
             emit_indent (d - 1);
             Buffer.add_string buf (bullet_for_depth d);
             Buffer.add_char buf ' ';
             current_depth := d;
             sibling_depth := Hmap.remove h !sibling_depth
           | None ->
             emit_indent !current_depth);
          Buffer.add_string buf e.en_src;
          Buffer.add_char buf '\n';
          (* Register fresh siblings: walk the subtree rooted at
             [parent], finding every multi-child split, and register
             each such child at the right depth. Single-child links
             are continuations and don't bump depth; multi-child
             links do. A compound phrase like [split; split.] can
             produce nested splits within one phrase. *)
          let rec walk h d =
            match children_of h with
            | [c] -> walk c d
            | (_ :: _ :: _) as cs ->
              List.iter
                (fun c ->
                  sibling_depth :=
                    Hmap.add c d !sibling_depth;
                  walk c (d + 1))
                cs
            | [] -> ()
          in
          walk parent (!current_depth + 1))
        (dag_order run)
    in
    let prefix_frames : EcBullets.frame list =
      (* The stack stores the innermost frame at its head; [render_run]
         wants them OUTERMOST first, frame [t_d] being the one whose
         siblings live at emitted depth [d]. *)
      match !(st.prior_bullets) with
      | None       -> []
      | Some stack -> List.rev stack
    in
    let first_run = ref true in
    List.iter
      (function
        | `Barrier e ->
          Buffer.add_string buf e.en_src;
          Buffer.add_char buf '\n'
        | `Run run ->
          let frames = if !first_run then prefix_frames else [] in
          first_run := false;
          render_run ~frames run)
      (blocks (List.rev !(st.transcript)));
    Buffer.contents buf
end

(* -------------------------------------------------------------------- *)
(* Accessors used by front-ends to build their own replies (HELP,
   QUIET, parse errors) and to render a [Goals] body. *)
let uuid (_ : state) =
  EcCommands.uuid ()

let clear_notices (st : state) =
  Buffer.clear st.notices

let current_goals (_ : state) =
  Goals.goals_to_string ()

let make_reply (st : state) ?tag (body : body) =
  mk_reply st ~pre:(EcCommands.uuid ()) ?tag body

let make_failure (st : state) (message : string) =
  mk_failure st ~pre:(EcCommands.uuid ()) message

(* -------------------------------------------------------------------- *)
(* Process EasyCrypt input typed at the prompt. The input is a file
   fragment, not a single phrase: every sentence it holds runs, in
   order, and one reply describes the state they leave behind. A
   failure stops the run there; the sentences before it stay applied,
   exactly as they would in a compiled file. *)
let step (st : state) input =
  let notices = st.notices in
  let prior_bullets = st.prior_bullets in
  let pre = EcCommands.uuid () in
  Buffer.clear notices;
  (* On the first REPL phrase of each proof, capture the bullet stack
     the LOAD prefix left so COMMIT can avoid token collisions with
     it. Subsequent calls return [None] and don't clobber the snapshot. *)
  (match EcCommands.disable_repl_bullets () with
   | None -> ()
   | Some _ as snapshot -> prior_bullets := snapshot);
  let reader = EcIo.from_string input in
  let last_src = ref "" in
  (* Reply body, decided by the last item that did something: a run of
     sentences ends on the goals, a doc comment on an empty body. The
     end-of-input marker is an empty [P_Prog], and must not count. *)
  let body = ref Goals in
  let quit = ref false in
  let answer =
    begin try
      begin try while true do
        last_src := "";
        let (src, prog) = EcIo.xparse reader in
        let src = String.strip src in
        last_src := src;
        match EcLocation.unloc prog with
        | EP.P_Prog (commands, locterm) ->
          if commands <> [] then begin
            body := Goals;
            List.iter (process_action st ~record:true ~src) commands
          end;
          if locterm then raise Exit
        | EP.P_Undo i ->
          body := Goals;
          EcCommands.undo i;
          Transcript.trim st i
        | EP.P_Exit ->
          (* Everything before [exit.] stays applied; the front-end
             owns what happens next. *)
          quit := true; raise Exit
        | EP.P_DocComment doc ->
          body := Text "";
          EcCommands.doc_comment doc
      done with Exit | End_of_file -> () end;
      if !quit then Quit else
        match !body with
        | Goals      -> Done (Ok (mk_reply_goals st ~pre))
        | Text _ as b -> Done (Ok (mk_reply st ~pre b))
    with
    | EcCommands.Restart ->
      do_initialize st;
      Transcript.clear st;
      Done (Ok (mk_reply st ~pre (Text "Session restarted")))
    | e ->
      Done (Error (mk_failure st ~pre (Goals.format_error ~src:!last_src e)))
    end
  in
  EcIo.finalize reader;
  answer

(* -------------------------------------------------------------------- *)
(* [step] with an automatic rollback on failure. A phrase can fail
   after having advanced the engine, so nothing short of the state on
   entry is a faithful notion of "unchanged".

   Rolling back with [undo pre] was not enough: [undo] only pops, so
   input that *lowered* the uuid before failing -- [undo 3.] followed
   by a bad tactic -- left the engine at that lower state while the
   reply claimed [reverted = true]. Take a mark of the whole engine
   context instead, which restores forward as readily as backward, and
   restore the session's own bookkeeping (the transcript, whose entries
   carry COMMIT's proof-DAG snapshots, and the prefix's bullet stack)
   alongside it rather than
   trimming it, since trimming is likewise one-directional. Checkpoints
   need nothing: EasyCrypt input cannot reach them, and the uuids they
   name are valid again once the engine is back.

   The failure is then re-stamped, because its uuid, goal text and
   [changed] flag described the point of failure, which no longer
   exists. [changed] is [false] by construction now: the restore always
   reaches [pre]. *)
let try_step (st : state) input =
  let pre        = EcCommands.uuid () in
  let mark       = EcCommands.undo_mark () in
  let transcript = !(st.transcript) in
  let bullets    = !(st.prior_bullets) in
  match step st input with
  | Quit                  -> Quit
  | Done (Ok _) as answer -> answer
  | Done (Error failure)  ->
    EcCommands.undo_restore mark;
    st.transcript    := transcript;
    st.prior_bullets := bullets;
    let uuid = EcCommands.uuid () in
    Done (Error { failure with
      uuid;
      goals    = Goals.goals_to_string ();
      reverted = true;
      changed  = uuid <> pre; })

(* -------------------------------------------------------------------- *)
(* LOAD: run [file] up to [upto], optionally with SMT calls weakened
   ([nosmt]) or with the last sentence of the prefix traced. The
   argument string is parsed by the front-end. *)
let load (st : state) ~file ~upto ~nosmt ~trace =
  let notices = st.notices in
  let cur_prvopts = st.cur_prvopts in
  let checkpoints = st.checkpoints in
  let pre = EcCommands.uuid () in
  Buffer.clear notices;
  let filename = file in
  let last_src = ref "" in
  let trace_prefix = ref "" in
  let exception Trace_failed of exn in

  try
    begin try
      ignore (EcLoader.getkind
        (Filename.extension filename) : EcLoader.kind)
    with EcLoader.BadExtension ext ->
      failwith (Format.sprintf
        "unknown file extension: %s" ext)
    end;

    (* Apply the configuration attached to the loaded file's
       [easycrypt.project], as the batch compiler does when the
       file is given on the command line: refresh the prover
       options (timeout, provers, pragmas, ...) and extend the
       load path with the project's include dirs.

       The include path is rewound first. It is process-global and
       [addidir] only grows it, so without this a previously loaded
       file's directory -- and its project's -- stayed searchable
       here, and `require'ing one of its neighbours silently
       succeeded in a session that has nothing to do with it. LOAD
       resets the session, and the load path is part of the session. *)
    let ini = Option.to_list (st.projini (Some filename)) in
    cur_prvopts :=
      EcOptions.prv_options_with_ini ini st.base_prvopts;
    EcCommands.loadpath_reset st.base_loadpath;
    List.iter (fun (nm, dir, isrec) ->
      EcCommands.addidir
        ?namespace:(omap (fun nm -> `Named nm) nm)
        ~recursive:isrec dir)
      (EcOptions.ini_loadpath ini);

    do_initialize st;
    Hashtbl.clear checkpoints;
    Transcript.clear st;
    EcCommands.addidir (Filename.dirname filename);
    EcCommands.set_current_path (Filename.dirname filename);

    let reader = EcIo.from_file filename in

    let past_upto (loc : EcLocation.t) =
      match upto with
      | None -> false
      | Some (line, col) ->
        let (el, ec) = loc.loc_end in
        el > line || (el = line && match col with
          | None -> false
          | Some c -> ec > c)
    in

    (* [upto] stops the prefix at the requested position whatever kind
       of sentence sits past it. This is applied to every item the
       reader yields, not only to the [P_Prog] commands: an `undo N.`
       on the line after [upto] used to run all the same, silently
       rewinding the very prefix the caller asked for, so that LOAD
       returned a state that was not the state at that line. *)
    let stop_at_upto (item : _ EcLocation.located) =
      if past_upto (EcLocation.loc item) then raise Exit
    in

    let last_loc = ref None in

    (* For -trace: lazy whole-file bytes, used to slice the exact
       source text of a sentence by byte offsets. *)
    let input_bytes = lazy (
      let ic = open_in_bin filename in
      let n  = in_channel_length ic in
      let b  = Bytes.create n in
      really_input ic b 0 n;
      close_in ic;
      Bytes.unsafe_to_string b)
    in
    let sentence_source (loc : EcLocation.t) =
      let s = Lazy.force input_bytes in
      let lo = max 0 loc.EcLocation.loc_bchar in
      let hi = min (String.length s) loc.EcLocation.loc_echar in
      if hi <= lo then "" else String.sub s lo (hi - lo)
    in

    (* For -trace: defer execution of the last sentence within the
       prefix so we can capture goals before and after it. *)
    let pending : (string * EP.global) option ref = ref None in
    let flush_pending () =
      match !pending with
      | None -> ()
      | Some (src, p) ->
        last_src := src;
        process_action st ~src p;
        last_loc := Some p.EP.gl_action.EcLocation.pl_loc;
        pending := None
    in
    let step src p =
      let loc = p.EP.gl_action.EcLocation.pl_loc in
      if past_upto loc then raise Exit;
      if trace then begin
        flush_pending ();
        pending := Some (src, p)
      end else begin
        last_src := src;
        process_action st ~src p;
        last_loc := Some loc
      end
    in

    if nosmt then EcCommands.pragma_check `WeakCheck;

    begin try while true do
      let (src, prog) = EcIo.xparse reader in
      let src = String.strip src in
      match EcLocation.unloc prog with
      | EP.P_Prog (commands, locterm) ->
        List.iter (step src) commands;
        if locterm then raise Exit
      | EP.P_Undo i ->
        stop_at_upto prog;
        last_src := src;
        EcCommands.undo i
      | EP.P_Exit ->
        raise Exit
      | EP.P_DocComment doc ->
        stop_at_upto prog;
        last_src := src;
        EcCommands.doc_comment doc
    done with
    | Exit | End_of_file -> ()
    | e ->
      EcIo.finalize reader;
      if nosmt then EcCommands.pragma_check `Check;
      raise e
    end;

    EcIo.finalize reader;

    if nosmt then EcCommands.pragma_check `Check;

    (* If -trace is set, the last in-prefix sentence is still
       pending. Run it under goal capture and build the
       BEFORE/TACTIC/AFTER/SUMMARY response body. *)
    let body =
      if not trace then
        Goals.goals_to_string ()
      else
        let pre_state =
          match !pending with
          | None                            -> `Nothing
          | Some _ when not (EcCommands.in_proof ()) -> `NotInProof
          | Some (src, p)                   -> `Ready (src, p)
        in
        match pre_state with
        (* Tracing is off the table, but the prefix is not: run the
           sentence we deferred so that the session ends up exactly
           where a plain LOAD of the same prefix would leave it. A
           failure inside the flush is reported by the enclosing
           handler, as any prefix failure is. *)
        | `Nothing    ->
          flush_pending ();
          failwith "trace: nothing to trace"
        | `NotInProof ->
          flush_pending ();
          failwith
            "trace: target sentence is not in a proof context"
        | `Ready (src, p) ->
          let loc = p.EP.gl_action.EcLocation.pl_loc in
          let (sl, sc) = loc.EcLocation.loc_start in
          let (el, ec) = loc.EcLocation.loc_end in
          let before_goals = EcCommands.pp_all_goals () in
          let n1 = List.length before_goals in
          let buf = Buffer.create 1024 in
          let fmt = Format.formatter_of_buffer buf in
          Format.fprintf fmt
            "=== BEFORE: line %d (col %d) ===@\n" sl sc;
          EcCommands.pp_current_goal_or_noproof ~all:false fmt;
          Format.fprintf fmt
            "@\n=== TACTIC (lines %d:%d - %d:%d) ===@\n%s@\n@\n"
            sl sc el ec (sentence_source loc);
          last_src := src;
          begin
            try
              process_action st ~src p;
              last_loc := Some loc;
              pending := None;
              let after_goals = EcCommands.pp_all_goals () in
              let n2 = List.length after_goals in
              Format.fprintf fmt
                "=== AFTER: line %d (col %d) ===@\n" sl sc;
              let before_set =
                List.fold_left
                  (fun s g -> EcMaps.Sstr.add g s)
                  EcMaps.Sstr.empty before_goals
              in
              (* The new focused goal always counts as "modified"
                 (its focus status changed even if its text matches
                 an old sibling); the rest are printed only if they
                 didn't appear in BEFORE. *)
              let to_print =
                match after_goals with
                | []          -> []
                | head :: tl ->
                  head ::
                  List.filter
                    (fun g -> not (EcMaps.Sstr.mem g before_set))
                    tl
              in
              begin match to_print with
              | [] -> Format.fprintf fmt "(no open goals)@\n"
              | _  ->
                List.iteri (fun i g ->
                  if i > 0 then Format.fprintf fmt "@\n";
                  Format.fprintf fmt "%s@\n" g)
                  to_print
              end;
              Format.fprintf fmt
                "@\n=== SUMMARY ===@\nopen goals: %d -> %d@\n" n1 n2;
              Format.pp_print_flush fmt ();
              Buffer.contents buf
            with e ->
              Format.fprintf fmt
                "=== AFTER: line %d (col %d) ===@\n<sentence failed>@\n"
                sl sc;
              Format.pp_print_flush fmt ();
              trace_prefix := Buffer.contents buf;
              raise (Trace_failed e)
          end
    in

    let tag =
      let loaded =
        match !last_loc with
        | None -> ""
        | Some loc ->
          let (el, _) = loc.EcLocation.loc_end in
          Printf.sprintf " [loaded:%s:%d]" filename el
      in
      loaded ^ Goals.focus_tag ()
    in
    Ok (mk_reply st ~pre ~tag (Text body))

  with
  | EcCommands.Restart ->
    do_initialize st;
    Hashtbl.clear checkpoints;
    Transcript.clear st;
    Ok (mk_reply st ~pre (Text "Session restarted"))
  | Trace_failed e ->
    let msg = Goals.format_error ~src:!last_src e in
    Error (mk_failure st ~pre (!trace_prefix ^ msg))
  | Failure s ->
    Error (mk_failure st ~pre s)
  | e ->
    Error (mk_failure st ~pre (Goals.format_error ~src:!last_src e))

(* -------------------------------------------------------------------- *)
(* The remaining meta-commands. *)

let goals (st : state) ~all =
  let pre = EcCommands.uuid () in
  Buffer.clear st.notices;
  Ok (mk_reply st ~pre ~tag:(Goals.focus_tag ())
        (Text (Goals.goals_to_string ~all ())))

let tree (st : state) ~all =
  let pre = EcCommands.uuid () in
  Buffer.clear st.notices;
  Ok (mk_reply st ~pre ~tag:(Goals.focus_tag ())
        (Text (FrameTree.render ~all ())))

let commit (st : state) =
  let pre = EcCommands.uuid () in
  Buffer.clear st.notices;
  Ok (mk_reply st ~pre ~tag:(Goals.focus_tag ())
        (Text (Commit.proof_text st)))

let undo (st : state) =
  let pre = EcCommands.uuid () in
  Buffer.clear st.notices;
  let uuid = EcCommands.uuid () in
  if uuid > 0 then begin
    EcCommands.undo (uuid - 1);
    Transcript.trim st (uuid - 1);
    Ok (mk_reply_goals st ~pre)
  end else
    Error (mk_failure st ~pre "nothing to undo")

let focus (st : state) request =
  (* [request] is the user's intent normalized:
     - [`Next]   = rotate to the second open goal (or stay if <=1)
     - [`Path p] = resolve dotted path [p] against the frame tree
                   and focus the matching leaf. *)
  let pre = EcCommands.uuid () in
  Buffer.clear st.notices;
  let resolved =
    match request with
    | `Next ->
      let n = List.length (EcCommands.open_handles ()) in
      Ok (if n <= 1 then 1 else 2)
    | `Path path -> FrameTree.resolve_path path
  in
  match resolved with
  | Error msg -> Error (mk_failure st ~pre msg)
  | Ok target ->
    match EcCommands.focus_goal target with
    | Ok _      -> Ok (mk_reply_goals st ~pre)
    | Error msg -> Error (mk_failure st ~pre msg)

let checkpoint (st : state) ~name =
  let pre = EcCommands.uuid () in
  Buffer.clear st.notices;
  Hashtbl.replace st.checkpoints name (EcCommands.uuid ());
  Ok (mk_reply st ~pre (Text (Printf.sprintf
    "checkpoint '%s' set at uuid %d" name (EcCommands.uuid ()))))

let revert (st : state) spec =
  let pre = EcCommands.uuid () in
  Buffer.clear st.notices;
  let target =
    try Some (int_of_string spec)
    with Failure _ -> Hashtbl.find_opt st.checkpoints spec
  in
  match target with
  | None ->
    Error (mk_failure st ~pre (Printf.sprintf
      "REVERT: '%s' is not a valid uuid or checkpoint name" spec))
  | Some target ->
    let uuid = EcCommands.uuid () in
    if target < 0 || target > uuid then
      Error (mk_failure st ~pre (Printf.sprintf
        "REVERT: uuid %d out of range [0, %d]" target uuid))
    else begin
      EcCommands.undo target;
      Transcript.trim st target;
      Ok (mk_reply_goals st ~pre)
    end

(* SEARCH is handed a search pattern, not EasyCrypt input. Composing
   ["search " ^ pattern ^ "."] and running it through [step] made every
   sentence-ending '.' inside the pattern a statement separator, so a
   pattern like [(_ /\ _). split. admit] executed [split] and [admit]
   too. Parse the composed phrase here instead, and run it only if it
   is exactly one toplevel item whose action is a [search]: a pattern
   that closes the sentence on its own leaves trailing input, which
   this rejects. Screening the pattern for '.' would be wrong --
   qualified names (A.B.lem) are legitimate patterns. *)
let search (st : state) ~pattern =
  let pre = EcCommands.uuid () in
  Buffer.clear st.notices;
  let src = Printf.sprintf "search %s." pattern in
  let reject = "SEARCH: the argument must be a single search pattern" in
  let is_search (p : EP.global) =
    not p.EP.gl_fail
    && match EcLocation.unloc p.EP.gl_action with
       | EP.Gsearch _ -> true
       | _            -> false
  in
  let parsed =
    let reader = EcIo.from_string src in
    let next () =
      match EcIo.xparse reader with
      | exception End_of_file -> `End
      | (_, prog) ->
        match EcLocation.unloc prog with
        | EP.P_Prog ([ ], true ) -> `End
        | EP.P_Prog ([p], false) -> `Item p
        | _                      -> `Other
    in
    let result =
      try
        match next () with
        | `Item p when is_search p ->
          (match next () with
           | `End             -> Ok p
           | `Item _ | `Other -> Error reject)
        | `Item _ | `Other | `End -> Error reject
      with e -> Error (Goals.format_error e)
    in
    EcIo.finalize reader; result
  in
  match parsed with
  | Error msg -> Error (mk_failure st ~pre msg)
  | Ok p ->
    match process_action st ~src p with
    | ()            -> Ok (mk_reply_goals st ~pre)
    | exception e   -> Error (mk_failure st ~pre (Goals.format_error ~src e))
