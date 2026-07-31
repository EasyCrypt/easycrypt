(* -------------------------------------------------------------------- *)
(* The LLM coding-agent REPL. See [ecLlm.mli] for the entry point.

   Implementation note: the REPL holds a large amount of mutable state
   (notice buffer, transcript, checkpoints, ...). To keep that state
   sharable across the various helpers without resorting to a big
   record, [run] is a single closure that opens nested [module] blocks
   for grouping. The submodules are read-only views over the closed-
   over refs. *)

open EcUtils

module EP = EcParsetree

(* -------------------------------------------------------------------- *)
(* Path to the bundled LLM-agent guide. *)
let llm_guide_path () =
  let (module Sites) = EcRelocate.sites in
  match EcRelocate.sourceroot with
  | Some root ->
    Filename.concat (Filename.concat root "doc/llm") "CLAUDE.md"
  | None ->
    Filename.concat Sites.doc "llm-guide.md"

(* Print the bundled guide to stdout. Used by [-help]. *)
let print_llm_guide () =
  let path = llm_guide_path () in
  try
    let ic = open_in path in
    begin try while true do
      print_char (input_char ic)
    done with End_of_file -> () end;
    close_in ic
  with Sys_error e ->
    Printf.eprintf "cannot read LLM guide: %s\n%!" e

(* -------------------------------------------------------------------- *)
(* Machine-profile protocol version advertised in the READY handshake
   (addition 6). The daemon compares this against its own minimum and
   fails the handshake on a lower report — bump in lock-step with any
   wire-visible change. v3 = v2 (EcLlm command set + full JSON
   machine profile) + PARSE-JSON "name" on declaration sentences
   (from the AST) + STRICT single-phrase <BEGIN>/<DONE> blocks:
   trailing phrases are an ERROR instead of being silently dropped
   (field reports B4/B5). *)
let llm_protocol_version = 3

(* -------------------------------------------------------------------- *)
let run ~relocdir ~boot ~projini (llmopts : EcOptions.llm_option) =
  if llmopts.llmo_help then begin
    print_llm_guide ();
    exit 0
  end;

  let prvopts = llmopts.llmo_provers in
  Random.self_init ();

  prvopts.prvo_why3server |> oiter (fun server ->
    try
      Why3.Prove_client.connect_external server
    with Why3.Prove_client.ConnectionError e ->
      Format.eprintf
        "cannot connect to Why3 server `%s': %s" server e;
      exit 1);

  (match relocdir with
   | None     -> EcCommands.addidir Filename.current_dir_name
   | Some pwd -> EcCommands.addidir pwd);

  (* Prover options in effect: refreshed by [LOAD] with the loaded
     file's [easycrypt.project] settings overlaid on the command-line
     options, as the batch compiler does at option-parsing time. *)
  let cur_prvopts = ref prvopts in

  let checkmode_of (prvopts : EcOptions.prv_options) = {
    EcCommands.cm_checkall  = prvopts.prvo_checkall;
    EcCommands.cm_timeout   = odfl 3 prvopts.prvo_timeout;
    EcCommands.cm_cpufactor = odfl 1 prvopts.prvo_cpufactor;
    EcCommands.cm_nprovers  = odfl 4 prvopts.prvo_maxjobs;
    EcCommands.cm_provers   = prvopts.prvo_provers;
    EcCommands.cm_quorum    = prvopts.prvo_quorum;
    EcCommands.cm_profile   = prvopts.prvo_profile;
  } in

  (* ------------------------------------------------------------------ *)
  (* State. *)

  (* Messages emitted by the engine during a phrase; flushed into the
     next OK/ERROR reply. *)
  let notices = Buffer.create 256 in

  (* Has [EcCommands.initialize] been called? Subsequent calls pass
     [~restart:true]. *)
  let initialized = ref false in

  (* Project-file load-path entries already added to the (global)
     loader, so repeated [LOAD]s do not pile up duplicates. *)
  let projdirs : (string option * string * bool) list ref = ref [] in

  (* True iff replies should suppress goal bodies. Toggled by QUIET. *)
  let quiet = ref false in

  (* CHECKPOINT name -> uuid. *)
  let checkpoints : (string, int) Hashtbl.t = Hashtbl.create 16 in

  (* Transcript of REPL-typed phrases that succeeded. Each entry is
     [(uuid_before, src, parent, opens_at_entry)]:
       - [parent]: focused handle right before the phrase ([None] iff
         outside a proof);
       - [opens_at_entry]: full open-handle list (focused first), used
         by [Commit] to seed the sibling map when the first recorded
         phrase already sits inside a frame opened by the LOAD prefix.
     Trimmed by UNDO/REVERT; cleared on LOAD/Restart. *)
  let transcript :
    (int * string * EcCoreGoal.handle option
      * EcCoreGoal.handle list) list ref = ref [] in

  (* The bullet stack of the active proof at the moment REPL input
     took over. Captured the first time [disable_repl_bullets] clears
     a non-empty stack. Used by [Commit] to pick bullet characters
     that don't collide with frames opened by the LOAD prefix.
     Cleared with the transcript on LOAD/Restart. *)
  let prior_bullets : EcBullets.stack option ref = ref None in

  (* Machine profile (addition 4): stream notices as `NOTICE: ` lines
     immediately (one line per line, flushed) instead of buffering
     them into the next reply body — clients see progress during
     long-running commands and reply bodies stay payload-only. A
     NOTICE line may appear anywhere in the stream and is always
     identifiable by its prefix. The [notices] buffer above stays for
     the reply-shape code paths but now remains empty. *)
  let notifier (_ : EcGState.loglevel) (lazy msg) =
    let n = ref (String.length msg) in
    while !n > 0
          && (let c = msg.[!n - 1] in c = '\n' || c = '\r')
    do decr n done;
    if !n > 0 then begin
      List.iter
        (Printf.printf "NOTICE: %s\n")
        (String.split_on_char '\n' (String.sub msg 0 !n));
      flush stdout
    end
  in

  let do_initialize () =
    EcCommands.initialize
      ~restart:!initialized ~undo:true
      ~boot ~checkmode:(checkmode_of !cur_prvopts) ~checkproof:true;
    initialized := true;
    (try
       List.iter EcCommands.apply_pragma_option !cur_prvopts.prvo_pragmas
     with EcCommands.InvalidPragma x ->
       EcScope.hierror "invalid pragma: `%s'\n%!" x);
    EcCommands.addnotifier notifier;
    oiter (fun ppwidth ->
      let gs = EcEnv.gstate (EcScope.env (EcCommands.current ())) in
      EcGState.setvalue "PP:width" (`Int ppwidth) gs)
      !cur_prvopts.prvo_ppwidth
  in

  (* ------------------------------------------------------------------ *)
  (* Goal/error formatting: shared between the wire layer and the
     -trace block. *)
  let module Goals = struct
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
  end in

  (* ------------------------------------------------------------------ *)
  (* Frame tree: group currently-open goals by their shared multi-child
     ancestors. Used by [Tree] (rendering) and [Focus] (path lookup).
     The tree is a *derivation*: it depends only on [pr_opened] and
     [parent_of], no recorded transcript. *)
  let module FrameTree = struct
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
            (* Line ORDER here is structural (siblings grouped under
               their split frame), NOT the subgoal order — grouping
               pulls interleaved siblings together (field report
               B13). The #N annotation is the order authority: it is
               the 0-based index into GOALS-JSON's subgoals array
               (and focus rotation order). *)
            (match texts_all with
             | None ->
               Buffer.add_string buf
                 (Printf.sprintf "[%s] #%d %s%s\n"
                    label (idx - 1) (one_line text) marker)
             | Some entries ->
               let (_, _, full) =
                 List.nth entries (idx - 1)
               in
               Buffer.add_string buf
                 (Printf.sprintf "[%s] #%d%s\n%s\n"
                    label (idx - 1) marker full))
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
  end in


  (* ------------------------------------------------------------------ *)
  (* OK/ERROR/<END> wire envelope. *)
  let had_error = ref false in

  (* Addition 15: the next OK reply's `OK-JSON:` payload. EXEC-JSON
     (addition 13) stages structured metadata here before feeding its
     rendered text through [process_ec_input]; [Wire.reply_ok]
     consumes it one-shot and falls back to the `{}` stub. *)
  let next_ok_payload : string option ref = ref None in

  let module Wire = struct
    let reply_ok ?(tag="") body =
      let n = Buffer.contents notices in
      Printf.printf "OK [uuid:%d]%s\n" (EcCommands.uuid ()) tag;
      (* Addition 15: structured success envelope symmetric with
         ERROR-JSON. `{}` stub unless a producer (EXEC-JSON) staged a
         payload for this reply. *)
      let payload =
        match !next_ok_payload with
        | Some s -> next_ok_payload := None; s
        | None -> "{}"
      in
      Printf.printf "OK-JSON: %s\n" payload;
      if n <> "" then print_string n;
      if body <> "" then begin
        print_string body;
        let len = String.length body in
        if len > 0 && body.[len - 1] <> '\n' then
          print_char '\n'
      end;
      Printf.printf "<END>\n%!";
      Buffer.clear notices

    let reply_ok_goals ?(all=false) () =
      let tag = Goals.focus_tag () in
      if !quiet then reply_ok ~tag ""
      else reply_ok ~tag (Goals.goals_to_string ~all ())

    (* [?exn] carries the originating exception for structured-error
       classification (addition 8) on the `ERROR-JSON:` line;
       protocol-level errors (no exn) classify as Internal/protocol.
       [?tag] mirrors [reply_ok] — used for `[restarted]`
       (addition 4). *)
    let reply_error ?(tag="") ?exn ?error_json msg =
      had_error := true;
      let goals = Goals.goals_to_string () in
      Printf.printf "ERROR [uuid:%d]%s\n" (EcCommands.uuid ()) tag;
      let json =
        match error_json with
        | Some j -> j
        | None -> EcLlmJson.error_json_line ?exn ~fallback:msg ()
      in
      Printf.printf "ERROR-JSON: %s\n" json;
      Printf.printf "%s\n" msg;
      if goals <> "" then begin
        print_string goals;
        let len = String.length goals in
        if len > 0 && goals.[len - 1] <> '\n' then
          print_char '\n'
      end;
      Printf.printf "<END>\n%!";
      Buffer.clear notices
  end in

  (* ------------------------------------------------------------------ *)
  (* Transcript manipulation. *)
  let module Transcript = struct
    let trim target =
      transcript :=
        List.filter
          (fun (uuid_before, _, _, _) -> uuid_before < target)
          !transcript

    let clear () =
      transcript := [];
      prior_bullets := None
  end in

  (* ------------------------------------------------------------------ *)
  (* Recorded sources strip any leading bullet token (whitespace and
     one `+`/`-`/`*` run): under the REPL exemption a typed bullet is
     semantically ignored, and [Commit] owns bullet PRESENTATION —
     recording typed bullets produced double-bulleted output
     ("- + trivial.", field report B8). *)
  let strip_recorded_bullet (src : string) =
    let n = String.length src in
    let rec skip i =
      if i >= n then i
      else
        match src.[i] with
        | ' ' | '\t' | '\n' | '\r' | '+' | '-' | '*' -> skip (i + 1)
        | _ -> i
    in
    let b = skip 0 in
    if b = 0 then src else String.sub src b (n - b)
  in

  (* Process a single EasyCrypt command, respecting [gl_fail]. When
     [~record:true], append a transcript entry on success: the parent
     handle (focused goal before the phrase) and the open-handle list,
     which together let [Commit] reconstruct bullet structure. Any
     successful declaration opens a NEW authoring scope: the
     transcript is per-proof (field report B8 — a stale transcript
     spanning positioning replays and earlier lemmas is not a proof
     of anything). *)
  let process_action ?(record=false) ~src (p : EP.global) =
    let loc = p.EP.gl_action.EcLocation.pl_loc in
    let pre_uuid = EcCommands.uuid () in
    let opens_pre =
      if record then EcCommands.open_handles () else []
    in
    let parent =
      match opens_pre with h :: _ -> Some h | [] -> None
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
    if !succeeded && p.EP.gl_fail then
      raise (EcScope.toperror_of_exn ~gloc:loc
        (EcScope.HiScopeError (None,
          "this command is expected to fail")));
    (match EcLocation.unloc p.EP.gl_action with
     | EP.Gaxiom _ when !succeeded -> Transcript.clear ()
     | _ -> ());
    if record && !succeeded && not p.EP.gl_fail then
      transcript :=
        (pre_uuid, strip_recorded_bullet src, parent, opens_pre)
        :: !transcript
  in

  (* ------------------------------------------------------------------ *)
  (* COMMIT: re-render the transcript with bullet PRESENTATION derived
     from the recorded open-goal snapshots — the same frame model the
     strict-bullets checker itself uses (EcBullets), so the emitted
     layout is what the checker accepts. A phrase that leaves >= 2
     NEW goals open pushes a sibling frame one level deeper; a phrase
     whose parent is a pending sibling emits that frame's bullet
     (popping any inner frames); every other phrase is an unbulleted
     continuation at the current depth. Phrases that create-and-close
     within themselves (`have ... by ...`, `if; 1: ...` selectors,
     non-splitting steps like `proc.`) leave at most one new goal and
     therefore NEVER shift the level (field reports B10/B11 — the
     proof-DAG fan-out this used to walk counts internal refinements
     the file reader never sees). Bullet tokens skip any character
     already on the LOAD prefix's [puc_bullets] stack so emitted
     bullets cannot collide with frames opened by the prefix. *)
  let module Commit = struct
    (* Token order matches PR 1017's lexer: -, +, *, --, ++, **,
       ---, +++, *** ... *)
    let token_at_index i =
      let chars = [| "-"; "+"; "*" |] in
      let rep = i / 3 + 1 in
      let chr = chars.(i mod 3) in
      String.concat "" (List.init rep (fun _ -> chr))

    let proof_text () =
      let entries = List.rev !transcript in
      let buf = Buffer.create 1024 in
      let emit_indent depth =
        for _ = 1 to depth do Buffer.add_string buf "  " done
      in
      let module Hset =
        Set.Make (struct
          type t = EcCoreGoal.handle
          let compare = compare
        end)
      in
      (* Pair each entry with the open-handle set AFTER it: the next
         entry's at-entry snapshot, or the live set for the last. *)
      let entries =
        let rec annotate = function
          | [] -> []
          | [ e ] -> [ (e, EcCommands.open_handles ()) ]
          | e :: ((_, _, _, o2) :: _ as rest) ->
            (e, o2) :: annotate rest
        in
        annotate entries
      in
      (* Sibling frames, innermost first: (depth, pending handles). *)
      let frames : (int * Hset.t ref) list ref = ref [] in
      let current_depth = ref 0 in
      (* Pick a bullet token for each depth, skipping tokens already
         in scope from the LOAD prefix's bullet stack. *)
      let bullet_to_string (b : EcParsetree.bullet) =
        let ch =
          match b.b_kind with
          | `Minus -> "-"
          | `Plus  -> "+"
          | `Star  -> "*"
        in
        String.concat "" (List.init b.b_count (fun _ -> ch))
      in
      let in_use_tokens =
        match !prior_bullets with
        | None -> []
        | Some stack ->
          List.map
            (fun (f : EcBullets.frame) -> bullet_to_string f.bf_bullet)
            stack
      in
      let depth_cache : (int, string) Hashtbl.t = Hashtbl.create 8 in
      let next_tok_idx = ref 0 in
      let assigned_tokens = ref [] in
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
      (* Seed: if the first recorded phrase entered a state with
         multiple open goals, the LOAD prefix opened a split whose
         siblings are still pending — one depth-1 frame holding all
         of them, so each sibling's first phrase gets a bullet. *)
      (match entries with
       | ((_, _, Some _, (_ :: _ :: _ as opens)), _) :: _ ->
         frames := [ (1, ref (Hset.of_list opens)) ]
       | _ -> ());
      List.iter (fun ((_uuid, src, parent_opt, opens_pre), opens_after) ->
        (match parent_opt with
         | None -> ()
         | Some parent ->
           (* Does this phrase start a pending sibling? Search from
              the innermost frame outward; a hit pops the inner
              frames (their subproofs are over — or the layout was
              never linear, which verification rejects loudly). *)
           let rec find = function
             | [] -> None
             | ((d, pend) :: rest) as l ->
               if Hset.mem parent !pend then Some (d, pend, l)
               else find rest
           in
           (match find !frames with
            | Some (d, pend, tail) ->
              frames := tail;
              pend := Hset.remove parent !pend;
              emit_indent (d - 1);
              Buffer.add_string buf (bullet_for_depth d);
              Buffer.add_char buf ' ';
              current_depth := d
            | None ->
              emit_indent !current_depth));
        Buffer.add_string buf src;
        Buffer.add_char buf '\n';
        (* A phrase leaving >= 2 NEW open goals is a branch point the
           file needs bullets for; anything else (including
           create-and-close compounds) is not. *)
        let pre = Hset.of_list opens_pre in
        (match
           List.filter (fun h -> not (Hset.mem h pre)) opens_after
         with
         | _ :: _ :: _ as created ->
           frames :=
             (!current_depth + 1, ref (Hset.of_list created))
             :: !frames
         | _ -> ())
      ) entries;
      Buffer.contents buf
  end in

  (* ------------------------------------------------------------------ *)
  (* Process EasyCrypt input, in one of two modes (field report B7):

     - REPL (default): the phrase is AUTHORED text. Bullet
       enforcement is exempted for the phrase (scoped — the global
       pragma stays document truth), the active proof's bullet stack
       is cleared once (snapshotted for COMMIT's token selection),
       and the phrase is recorded in the authoring transcript.

     - document (~document:true, wire `<DOC-BEGIN>` block): the
       phrase is DOCUMENT text being replayed (resync tails, body
       verification, candidate bodies destined for the file). It is
       checked under exactly the rules the file establishes for
       itself — strict bullets included — and is NOT recorded: replay
       is not authoring. *)
  let process_ec_input ?(document = false) input =
    Buffer.clear notices;
    (* On the first REPL phrase of each proof, capture the bullet stack
       the LOAD prefix left so COMMIT can avoid token collisions with
       it. Subsequent calls return [None] and don't clobber the snapshot. *)
    if not document then
      (match EcCommands.disable_repl_bullets () with
       | None -> ()
       | Some _ as snapshot -> prior_bullets := snapshot);
    let reader = EcIo.from_string input in
    let last_src = ref "" in
    begin try
      let (src, prog) = EcIo.xparse reader in
      (* Strict single-phrase contract (proto 3): a block carries
         exactly one parse unit. Trailing phrases used to be
         SILENTLY dropped — the worst failure mode: the client
         believes its state advanced (field report B5). Sequences
         execute one phrase per block. *)
      let trailing =
        match EcIo.xparse reader with
        | exception End_of_file -> false
        | (_, prog2) ->
          (* At end of input the parser yields an EMPTY program with
             the terminal flag rather than raising — only a real
             second phrase counts as trailing. *)
          (match EcLocation.unloc prog2 with
           | EP.P_Prog ([], _) -> false
           | _ -> true)
      in
      if trailing then
        Wire.reply_error
          "block contains more than one phrase; send exactly one \
           '.'-terminated phrase per <BEGIN>/<DONE> block (execute \
           sequences one phrase at a time)"
      else begin
      let src = String.strip src in
      last_src := src;
      begin match EcLocation.unloc prog with
      | EP.P_Prog (commands, _) ->
        if document then
          List.iter (process_action ~record:false ~src) commands
        else
          EcCommands.with_strict_bullets false (fun () ->
            List.iter (process_action ~record:true ~src) commands);
        Wire.reply_ok_goals ()
      | EP.P_Undo i ->
        EcCommands.undo i;
        Transcript.trim i;
        Wire.reply_ok_goals ()
      | EP.P_Exit ->
        EcIo.finalize reader; exit 0
      | EP.P_DocComment doc ->
        EcCommands.doc_comment doc;
        Wire.reply_ok ""
      end end
    with
    | EcCommands.Restart ->
      do_initialize ();
      Transcript.clear ();
      Wire.reply_ok ~tag:" [restarted]" "Session restarted"
    | e ->
      Wire.reply_error ~exn:e (Goals.format_error ~src:!last_src e)
    end;
    EcIo.finalize reader
  in

  (* ------------------------------------------------------------------ *)
  (* LOAD "file.ec" [LINE[:COL]] [-nosmt] [-trace]. *)
  let module Load = struct
    let handle args =
      Buffer.clear notices;
      let args = String.strip args in
      let last_src = ref "" in
      let trace_prefix = ref "" in
      let exception Trace_failed of exn in

      try
        if args = "" then failwith "LOAD: missing filename";
        (* Parse quoted or unquoted filename. *)
        let filename, rest =
          if args.[0] = '"' then
            let close =
              try String.index_from args 1 '"'
              with Not_found ->
                failwith "LOAD: unterminated filename"
            in
            let fn = String.sub args 1 (close - 1) in
            let rest = String.strip (
              String.sub args (close + 1)
                (String.length args - close - 1)) in
            (fn, rest)
          else
            match String.split_on_char ' ' args with
            | [] -> failwith "LOAD: missing filename"
            | [f] -> (f, "")
            | f :: rest -> (f, String.concat " " rest)
        in
        if filename = "" then failwith "LOAD: missing filename";

        (* Parse optional LINE[:COL] and flags (-nosmt, -trace). *)
        let upto, nosmt, trace =
          let words =
            String.split_on_char ' ' rest
              |> List.filter (fun s -> s <> "")
          in
          let nosmt = List.mem "-nosmt" words in
          let trace = List.mem "-trace" words in
          let words =
            List.filter
              (fun s -> s <> "-nosmt" && s <> "-trace")
              words
          in
          let upto = match words with
            | [] -> None
            | [w] ->
              begin match String.split_on_char ':' w with
              | [line] ->
                Some (int_of_string line, None)
              | [line; col] ->
                Some (int_of_string line, Some (int_of_string col))
              | _ -> failwith "LOAD: invalid LINE[:COL] format"
              end
            | _ -> failwith "LOAD: unexpected arguments"
          in
          (upto, nosmt, trace)
        in

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
           load path with the project's include dirs. *)
        let ini = Option.to_list (projini (Some filename)) in
        cur_prvopts :=
          EcOptions.prv_options_with_ini ini llmopts.llmo_provers;
        List.iter (fun ((nm, dir, isrec) as entry) ->
          if not (List.mem entry !projdirs) then begin
            projdirs := entry :: !projdirs;
            EcCommands.addidir
              ?namespace:(omap (fun nm -> `Named nm) nm)
              ~recursive:isrec dir
          end)
          (EcOptions.ini_loadpath ini);

        do_initialize ();
        Hashtbl.clear checkpoints;
        Transcript.clear ();
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
            process_action ~src p;
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
            process_action ~src p;
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
            last_src := src;
            EcCommands.undo i
          | EP.P_Exit ->
            raise Exit
          | EP.P_DocComment doc ->
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
            | `Nothing    -> failwith "trace: nothing to trace"
            | `NotInProof ->
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
                  process_action ~src p;
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

        (* LOAD always [do_initialize]s, so every LOAD reply — success
           or error — carries `[restarted]`: the daemon invalidates its
           sentence→uuid map on it (addition 4). Error paths tag it
           even when the failure precedes re-initialization —
           over-invalidation is the safe direction. *)
        let tag =
          let loaded =
            match !last_loc with
            | None -> ""
            | Some loc ->
              let (el, _) = loc.EcLocation.loc_end in
              Printf.sprintf " [loaded:%s:%d]" filename el
          in
          " [restarted]" ^ loaded ^ Goals.focus_tag ()
        in
        Wire.reply_ok ~tag body

      with
      | EcCommands.Restart ->
        do_initialize ();
        Hashtbl.clear checkpoints;
        Transcript.clear ();
        Wire.reply_ok ~tag:" [restarted]" "Session restarted"
      | Trace_failed e ->
        let msg = Goals.format_error ~src:!last_src e in
        Wire.reply_error ~tag:" [restarted]" ~exn:e (!trace_prefix ^ msg)
      | Failure s ->
        Wire.reply_error ~tag:" [restarted]" s
      | e ->
        Wire.reply_error ~tag:" [restarted]" ~exn:e
          (Goals.format_error ~src:!last_src e)
  end in

  (* ------------------------------------------------------------------ *)
  (* Main loop: line-by-line dispatcher. *)

  (* ------------------------------------------------------------------ *)
  (* Surface command vocabulary. Parsing turns each stdin line into one
     of these, and dispatch is a flat pattern-match. Argument
     parsing/validation lives in [Parse]; commands that interact with
     mutable state (checkpoints table, multi-line buffer) carry only
     the raw user-supplied data and let [Dispatch] do the lookup. *)
  let module Parse = struct
    type command =
      | Quit
      | Help
      | Undo
      | Goals      of [`One | `All]
      | Tree       of [`One | `All]
      | Commit
      | Focus      of int list  (* dotted path; [k] = "FOCUS k" *)
      | Next
      | Checkpoint of string
      | Revert     of string   (* uuid-or-name; Dispatch resolves *)
      | Quiet      of bool
      | Search     of string   (* trailing "." already stripped *)
      | Load       of string   (* raw arg tail; Load.handle parses *)
      | Ec         of string   (* fall-through: raw EasyCrypt input *)
      | Goals_json             (* machine profile: GOALS-JSON *)
      | Parse_file   of string (* machine profile: PARSE-JSON "file" *)
      | Analyze_file of string (* machine profile: ANALYZE-JSON "file" *)
      | Exec_json    of string (* machine profile: EXEC-JSON <payload> *)
      | Begin_multi of [ `Ec | `Doc | `Parse | `Analyze ]
      | Done_multi
      | Multi_line of string
      | Blank

    exception Parse_error of string

    (* Match [kw] as a prefix: succeeds on exactly [kw] (no argument)
       or [kw ^ " " ^ ...] (with argument), returning the stripped
       argument tail. Returns [None] otherwise. This recognises both
       "CHECKPOINT" and "CHECKPOINT foo" the same way, so we can
       diagnose the missing-name case ourselves instead of falling
       through to EC's parser. *)
    let keyword_arg kw line =
      if line = kw then Some ""
      else if String.starts_with line (kw ^ " ") then
        let n = String.length kw + 1 in
        Some (String.strip
          (String.sub line n (String.length line - n)))
      else None

    let parse_focus arg =
      if arg = "" then
        raise (Parse_error "FOCUS: missing argument");
      let parts = String.split_on_char '.' arg in
      let path =
        try List.map int_of_string parts
        with Failure _ ->
          raise (Parse_error
            (Printf.sprintf "FOCUS: not a path of integers: %s" arg))
      in
      if List.exists (fun k -> k < 1) path then
        raise (Parse_error
          (Printf.sprintf "FOCUS: path indices must be >= 1: %s" arg));
      Focus path

    let parse_checkpoint name =
      if name = "" then
        raise (Parse_error "CHECKPOINT: missing name");
      Checkpoint name

    let parse_revert spec =
      if spec = "" then
        raise (Parse_error
          "REVERT: missing uuid or checkpoint name");
      Revert spec

    let parse_search query =
      if query = "" then
        raise (Parse_error "SEARCH: missing query");
      let query =
        if String.ends_with query "."
        then String.sub query 0 (String.length query - 1)
        else query
      in
      Search query

    let parse_load args =
      (* [Load.handle] accepts an empty argument and reports a
         specific error; keep that responsibility there. *)
      Load args

    let of_line ~multi_active (raw : string) : command =
      let line = String.strip raw in
      if multi_active then
        (* Enders match on the stripped view; body lines pass through
           RAW so indentation and blank lines are preserved verbatim —
           byte offsets reported by PARSE-JSON must line up with the
           caller's own source buffer (machine profile). *)
        if line = "<DONE>" || line = "<PARSE-DONE>"
           || line = "<ANALYZE-DONE>"
        then Done_multi
        else Multi_line raw
      else
        match line with
        | "<BEGIN>"         -> Begin_multi `Ec
        (* Document-mode phrase (field report B7): checked under the
           file's own rules — no REPL bullet exemption, no transcript
           recording. Same <DONE> closer as <BEGIN>. *)
        | "<DOC-BEGIN>"     -> Begin_multi `Doc
        | "<PARSE-BEGIN>"   -> Begin_multi `Parse
        | "<ANALYZE-BEGIN>" -> Begin_multi `Analyze
        | ""          -> Blank
        | "QUIT"      -> Quit
        | "HELP"      -> Help
        | "UNDO"      -> Undo
        | "GOALS"     -> Goals `One
        | "GOALS ALL" -> Goals `All
        | "GOALS-JSON"-> Goals_json
        | "TREE"      -> Tree `One
        | "TREE ALL"  -> Tree `All
        | "COMMIT"    -> Commit
        | "NEXT"      -> Next
        | "QUIET ON"  -> Quiet true
        | "QUIET OFF" -> Quiet false
        | _ ->
          match keyword_arg "FOCUS"      line with Some a -> parse_focus      a | None ->
          match keyword_arg "CHECKPOINT" line with Some a -> parse_checkpoint a | None ->
          match keyword_arg "REVERT"     line with Some a -> parse_revert     a | None ->
          match keyword_arg "SEARCH"     line with Some a -> parse_search     a | None ->
          match keyword_arg "LOAD"       line with Some a -> parse_load       a | None ->
          match keyword_arg "PARSE-JSON"   line with Some a -> Parse_file   a | None ->
          match keyword_arg "ANALYZE-JSON" line with Some a -> Analyze_file a | None ->
          match keyword_arg "EXEC-JSON"    line with Some a -> Exec_json    a | None ->
          Ec line
  end in

  (* ------------------------------------------------------------------ *)
  (* Command handlers. Each takes (already-parsed) data and produces a
     wire reply via [Wire] (or exits the process). Multi-line state is
     held here so [Parse] can stay pure. *)
  let multi_buf = Buffer.create 256 in
  let in_multi  = ref false in
  (* Which frame opened the active multi-line block: plain EasyCrypt
     input (<BEGIN>), document-mode input (<DOC-BEGIN>), or the
     machine-profile PARSE/ANALYZE frames. *)
  let multi_mode : [ `Ec | `Doc | `Parse | `Analyze ] ref = ref `Ec in

  let module Dispatch = struct
    let do_help () =
      Buffer.clear notices;
      let buf = Buffer.create 4096 in
      let path = llm_guide_path () in
      begin try
        let ic = open_in path in
        begin try while true do
          Buffer.add_char buf (input_char ic)
        done with End_of_file -> () end;
        close_in ic;
        Wire.reply_ok (Buffer.contents buf)
      with Sys_error e ->
        Wire.reply_error (Printf.sprintf "cannot read guide: %s" e)
      end

    let do_undo () =
      Buffer.clear notices;
      let uuid = EcCommands.uuid () in
      if uuid > 0 then begin
        EcCommands.undo (uuid - 1);
        Transcript.trim (uuid - 1);
        Wire.reply_ok_goals ()
      end else
        Wire.reply_error "nothing to undo"

    let do_focus_request request =
      (* [request] is the user's intent normalized:
         - [`Next]   = rotate to the second open goal (or stay if <=1)
         - [`Path p] = resolve dotted path [p] against the frame tree
                       and focus the matching leaf. *)
      Buffer.clear notices;
      let resolved =
        match request with
        | `Next ->
          let n = List.length (EcCommands.open_handles ()) in
          Ok (if n <= 1 then 1 else 2)
        | `Path path -> FrameTree.resolve_path path
      in
      match resolved with
      | Error msg -> Wire.reply_error msg
      | Ok target ->
        match EcCommands.focus_goal target with
        | Ok _      -> Wire.reply_ok_goals ()
        | Error msg -> Wire.reply_error msg

    let do_checkpoint name =
      Buffer.clear notices;
      Hashtbl.replace checkpoints name (EcCommands.uuid ());
      Wire.reply_ok (Printf.sprintf
        "checkpoint '%s' set at uuid %d" name (EcCommands.uuid ()))

    let do_revert spec =
      Buffer.clear notices;
      let target =
        try Some (int_of_string spec)
        with Failure _ -> Hashtbl.find_opt checkpoints spec
      in
      match target with
      | None ->
        Wire.reply_error (Printf.sprintf
          "REVERT: '%s' is not a valid uuid or checkpoint name" spec)
      | Some target ->
        let uuid = EcCommands.uuid () in
        if target < 0 || target > uuid then
          Wire.reply_error (Printf.sprintf
            "REVERT: uuid %d out of range [0, %d]" target uuid)
        else begin
          EcCommands.undo target;
          Transcript.trim target;
          Wire.reply_ok_goals ()
        end

    let do_quiet on =
      Buffer.clear notices;
      quiet := on;
      Wire.reply_ok ""

    let do_search query =
      process_ec_input (Printf.sprintf "search %s." query)

    let do_begin_multi kind =
      Buffer.clear multi_buf;
      multi_mode := kind;
      in_multi := true

    let do_done_multi () =
      let input = Buffer.contents multi_buf in
      Buffer.clear multi_buf;
      in_multi := false;
      match !multi_mode with
      | `Parse ->
        Buffer.clear notices;
        Wire.reply_ok (EcLlmJson.parse_to_json input)
      | `Analyze ->
        Buffer.clear notices;
        Wire.reply_ok
          (EcLlmJson.analyze_to_json
             ~checkmode:(checkmode_of !cur_prvopts) input)
      | `Ec ->
        if input <> "" then process_ec_input input
      | `Doc ->
        if input <> "" then process_ec_input ~document:true input

    let do_multi_line s =
      if Buffer.length multi_buf > 0 then
        Buffer.add_char multi_buf '\n';
      Buffer.add_string multi_buf s

    (* Addition 13: structured execution. Parse the payload, render it
       to EC source via [EcExecJson.render], and feed the text through
       [process_ec_input] exactly as if the client had typed it —
       staging the render metadata as the reply's OK-JSON payload.
       Render failures surface their structured code directly. *)
    let do_exec_json payload =
      Buffer.clear notices;
      let emit_error code detail =
        Wire.reply_error
          ~error_json:(EcLlmJson.protocol_error_json ~code ~detail)
          detail
      in
      match Yojson.Safe.from_string payload with
      | exception e ->
        emit_error "MalformedExecJson"
          (Printf.sprintf "EXEC-JSON: %s" (Printexc.to_string e))
      | json ->
        (match EcExecJson.render json with
         | EcExecJson.Err (code, detail) -> emit_error code detail
         | EcExecJson.Ok_render (text, metadata) ->
           next_ok_payload := Some metadata;
           process_ec_input text;
           (* If process_ec_input replied ERROR, the staged payload
              never fired; clear it so an unrelated later OK doesn't
              inherit it. *)
           next_ok_payload := None)

    (* PARSE-JSON / ANALYZE-JSON over a file argument (quoted or
       bareword). *)
    let do_json_file builder label args =
      Buffer.clear notices;
      let args = String.strip args in
      let filename =
        if String.length args > 1 && args.[0] = '"' then
          let close =
            try String.index_from args 1 '"'
            with Not_found -> String.length args - 1
          in
          String.sub args 1 (close - 1)
        else args
      in
      if filename = "" then
        Wire.reply_error (Printf.sprintf "%s: missing filename" label)
      else
        try
          let ic = open_in filename in
          let n = in_channel_length ic in
          let content = really_input_string ic n in
          close_in ic;
          Wire.reply_ok (builder content)
        with Sys_error msg ->
          Wire.reply_error (Printf.sprintf "%s: %s" label msg)

    let run (cmd : Parse.command) =
      match cmd with
      | Blank        -> ()
      | Quit         -> exit 0
      | Help         -> do_help ()
      | Undo         -> do_undo ()
      | Goals `One   ->
        Buffer.clear notices;
        Wire.reply_ok (Goals.goals_to_string ())
      | Goals `All   ->
        Buffer.clear notices;
        Wire.reply_ok (Goals.goals_to_string ~all:true ())
      | Tree `One    ->
        Buffer.clear notices;
        Wire.reply_ok (FrameTree.render ())
      | Tree `All    ->
        Buffer.clear notices;
        Wire.reply_ok (FrameTree.render ~all:true ())
      | Commit       ->
        Buffer.clear notices;
        Wire.reply_ok (Commit.proof_text ())
      | Focus path   -> do_focus_request (`Path path)
      | Next         -> do_focus_request `Next
      | Checkpoint n -> do_checkpoint n
      | Revert s     -> do_revert s
      | Quiet on     -> do_quiet on
      | Search q     -> do_search q
      | Load args    -> Load.handle args
      | Ec input     -> process_ec_input input
      | Goals_json   ->
        Buffer.clear notices;
        Wire.reply_ok (EcLlmJson.goals_to_json ())
      | Parse_file a ->
        do_json_file EcLlmJson.parse_to_json "PARSE-JSON" a
      | Analyze_file a ->
        do_json_file
          (EcLlmJson.analyze_to_json
             ~checkmode:(checkmode_of !cur_prvopts))
          "ANALYZE-JSON" a
      | Exec_json p  -> do_exec_json p
      | Begin_multi kind -> do_begin_multi kind
      | Done_multi   -> do_done_multi ()
      | Multi_line s -> do_multi_line s
  end in

  (* ------------------------------------------------------------------ *)
  (* Main loop. *)

  do_initialize ();

  Printf.printf "READY [uuid:%d] [proto:%d]\n<END>\n%!"
    (EcCommands.uuid ()) llm_protocol_version;

  (* Input source: stdin by default, or the -eval string when given.
     For -eval, we split on newlines up front (no lazy channel), which
     keeps the driver simple and avoids ever touching stdin. *)
  let read_line : unit -> string =
    match llmopts.llmo_eval with
    | None ->
      fun () -> input_line stdin
    | Some script ->
      let lines = ref (String.split_on_char '\n' script) in
      fun () ->
        match !lines with
        | []      -> raise End_of_file
        | l :: tl -> lines := tl; l
  in

  begin try while true do
    let line = read_line () in
    (try
       let cmd = Parse.of_line ~multi_active:!in_multi line in
       Dispatch.run cmd
     with Parse.Parse_error msg ->
       Wire.reply_error msg)
  done with
  | End_of_file -> ()
  end;

  (* Scripted runs (-eval) report in-band errors through the exit
     status, so that automation does not mistake an ERROR reply for
     success. Interactive sessions keep exiting 0. *)
  exit (if llmopts.llmo_eval <> None && !had_error then 1 else 0)
