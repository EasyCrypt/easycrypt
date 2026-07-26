(* -------------------------------------------------------------------- *)
(* Machine-profile JSON builders for the LLM REPL ([EcLlm]).

   Ported from the daemon-v1 line (archive/llm-interactive-20260726,
   src/ec.ml) onto the EcLlm base — see doc/ecllm-compat.md Appendix B
   and UPSTREAM.md additions 1 (PARSE-JSON), 3 (GOALS-JSON), 8
   (ERROR-JSON), 14 (ANALYZE-JSON + scope-tagging + synthetic-abort
   recovery), 16 (first-token start_offset), 20 (per-pregoal render
   env), 23 (conclusion tree), 24 (STMT-JSON).

   JSON is built by string concatenation on purpose: ecLib takes no
   new dependency, and every payload is assembled from [json_escape]d
   leaves. Consumers are the tooling daemon ([Ec_llm_session]) and any
   MCP-facing client; humans use the pp-text commands instead. *)

open EcUtils

(* -------------------------------------------------------------------- *)
let json_escape s =
  let buf = Buffer.create (String.length s + 4) in
  String.iter (fun c ->
    match c with
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 ->
      Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c) s;
  Buffer.contents buf

(* -------------------------------------------------------------------- *)
(* Structured error classification (addition 8). PoC classifier: peels
   one [TopError] layer, then classifies on the inner exception;
   everything unrecognized is [Internal]. *)
let classify_error e =
  let (loc, inner) = match e with
    | EcScope.TopError (loc, inner) -> (Some loc, inner)
    | _ -> (None, e)
  in
  let (code, phase) = match inner with
    | EcTyping.TyError _
    | EcTyping.TymodCnvFailure _
    | EcTyping.RestrictionError _             -> ("TypeError", "typecheck")
    | EcParser.Error
    | EcLexer.LexicalError _
    | EcParsetree.ParseError _                -> ("ParseError", "parse")
    | EcScope.HiScopeError _
    | EcCoreGoal.TcError _                    -> ("TacticFailure", "tactic")
    | _                                       -> ("Internal", "unknown")
  in
  (* When TopError didn't supply a location, fall back to whatever the
     inner exception carries. *)
  let loc = match loc with
    | Some _ -> loc
    | None ->
      match inner with
      | EcTyping.TyError (l, _, _)
      | EcParsetree.ParseError (l, _)         -> Some l
      | EcLexer.LexicalError (Some l, _)      -> Some l
      | EcScope.HiScopeError (Some l, _)      -> Some l
      | EcCoreGoal.TcError { tc_location = Some l; _ } -> Some l.plc_loc
      | _                                     -> None
  in
  let detail = String.strip (EcPException.tostring inner) in
  (code, phase, loc, detail)

let error_json_of_exn e =
  let (code, phase, loc, detail) = classify_error e in
  let loc_field = match loc with
    | Some l when l <> EcLocation._dummy ->
      let (sl, sc) = l.EcLocation.loc_start in
      let (el, ec) = l.EcLocation.loc_end in
      let file =
        if l.EcLocation.loc_fname = "" then "null"
        else Printf.sprintf "\"%s\"" (json_escape l.EcLocation.loc_fname)
      in
      Printf.sprintf
        "{\"file\":%s,\"start_line\":%d,\"start_col\":%d,\
         \"end_line\":%d,\"end_col\":%d}"
        file sl sc el ec
    | _ -> "null"
  in
  Printf.sprintf
    "{\"code\":\"%s\",\"phase\":\"%s\",\"location\":%s,\"detail\":\"%s\"}"
    code phase loc_field (json_escape detail)

(* The `ERROR-JSON:` line payload. Protocol-level errors (no exception
   in hand — e.g. "REVERT: uuid N out of range") classify as
   Internal/protocol with the wire message as detail. *)
let error_json_line ?exn ~fallback () =
  match exn with
  | Some e -> error_json_of_exn e
  | None ->
    Printf.sprintf
      "{\"code\":\"Internal\",\"phase\":\"protocol\",\
       \"location\":null,\"detail\":\"%s\"}"
      (json_escape fallback)

(* -------------------------------------------------------------------- *)
(* Structured JSON goals (addition 3, v0 + amendments 20/23/24).
   Schema:
     { "active": bool,
       "subgoal_count": N,
       "current_index": 0,                -- PoC: always 0 (head)
       "subgoals": [
         { "index": i,
           "hypotheses":
             [ { "name": <id>, "kind": <tag>, "pp": <type/formula> } ],
           "conclusion": <ConclusionNode> } ] }
   Hypotheses carry EC's `local_kind` as a tag (`var`/`mem`/`modty`/
   `hyp`/`abs_st`). The conclusion is a recursive tree: `pp` leaves,
   `judgment` nodes for outermost PHL judgments (hoare / phoare /
   ehoare / equiv / eager), and `stmt` nodes carrying per-instruction
   STMT-JSON walkers for inlined program bodies. *)
let goals_to_json () =
  let scope = EcCommands.current () in
  let no_goal = "{\"active\":false}" in
  match EcScope.xgoal scope with
  | None -> no_goal
  | Some { EcScope.puc_active = None; _ } -> no_goal
  | Some { EcScope.puc_active = Some (auc, _); _ } ->
    match auc.EcScope.puc_jdg with
    | EcScope.PSNoCheck -> no_goal
    | EcScope.PSCheck pf ->
      match EcCoreGoal.opened pf with
      | None -> no_goal
      | Some (count, _) ->
        let subgoals = EcCoreGoal.all_opened pf in
        (* Render env: must be the per-pregoal env enriched with the
           pregoal's hypothesis bindings (lemma module parameters like
           `(A <: D)`, memory tags `&m`, universally quantified vars,
           etc.). Using [EcScope.env scope] (the lexical/top-level env)
           misses those bindings and causes [LookupFailure] when
           pp_form resolves a proof-bound xpath inside an `abstract
           theory` lemma's conclusion (UPSTREAM addition 20). The ref
           is updated per-subgoal at the top of [subgoal_json].

           [safe_pp] still wraps [LookupFailure] as a last-resort
           guard for a separate failure mode: post-revert dangling
           xpaths (UPSTREAM § 20 v1 territory). The daemon stays
           alive; the user sees a placeholder and can step/back to
           fix the state. *)
        let ppe = ref (EcPrinting.PPEnv.ofenv (EcScope.env scope)) in
        let safe_pp render label =
          try render ()
          with
          | EcEnv.LookupFailure _ ->
            Printf.sprintf "<%s: stale env lookup>" label
          | _ -> Printf.sprintf "<%s: pp error>" label
        in
        let hyp_json (id, k) =
          let name = EcIdent.name id in
          let (kind, pp) = match k with
            | EcBaseLogic.LD_var (ty, _) ->
              ("var",
               safe_pp
                 (fun () ->
                    Format.asprintf "%a" (EcPrinting.pp_type !ppe) ty)
                 "type")
            | EcBaseLogic.LD_mem m ->
              ("mem",
               safe_pp
                 (fun () ->
                    Format.asprintf "%a"
                      (EcPrinting.pp_memtype !ppe) m)
                 "memtype")
            | EcBaseLogic.LD_modty _ ->
              ("modty", "<module type>")
            | EcBaseLogic.LD_hyp f ->
              ("hyp",
               safe_pp
                 (fun () ->
                    Format.asprintf "%a" (EcPrinting.pp_form !ppe) f)
                 "hyp")
            | EcBaseLogic.LD_abs_st _ ->
              ("abs_st", "<abstract statement>")
          in
          Printf.sprintf
            "{\"name\":\"%s\",\"kind\":\"%s\",\"pp\":\"%s\"}"
            (json_escape name) kind (json_escape pp)
        in
        let pp_text label render =
          let s = safe_pp render label in
          Printf.sprintf "{\"kind\":\"pp\",\"text\":\"%s\"}"
            (json_escape s)
        in
        let pp_form_node label f =
          pp_text label
            (fun () ->
               Format.asprintf "%a" (EcPrinting.pp_form !ppe) f)
        in
        (* UPSTREAM #24 (STMT-JSON): structured per-instruction walker.
           Block constructs (if/while/match) carry their nested stmt as
           `body` / `then_body` / `else_body` / `branches` children,
           recursively. Source positions (`loc`) currently null — EC's
           `instr` IR drops parsetree locations during typecheck;
           populating loc requires position threading through the
           typechecker (deferred follow-up; clients null-check). *)
        let pp_expr_text label e =
          safe_pp
            (fun () -> Format.asprintf "%a" (EcPrinting.pp_expr !ppe) e)
            label
        in
        let pp_instr_text label i =
          safe_pp
            (fun () -> Format.asprintf "%a" (EcPrinting.pp_instr !ppe) i)
            label
        in
        let rec stmt_node_to_json (i : EcAst.instr) : string =
          let leaf kind text =
            Printf.sprintf
              "{\"kind\":\"%s\",\"pp\":\"%s\",\"loc\":null}"
              kind (json_escape text)
          in
          match i.i_node with
          | Sasgn _   -> leaf "asgn"   (pp_instr_text "stmt-asgn" i)
          | Srnd _    -> leaf "rnd"    (pp_instr_text "stmt-rnd" i)
          | Scall _   -> leaf "call"   (pp_instr_text "stmt-call" i)
          | Sraise _  -> leaf "raise"  (pp_instr_text "stmt-raise" i)
          | Sabstract _ -> leaf "abstract" (pp_instr_text "stmt-abstract" i)
          | Sif (e, s1, s2) ->
            Printf.sprintf
              "{\"kind\":\"if\",\"cond_pp\":\"%s\",\
               \"then_body\":%s,\"else_body\":%s,\"loc\":null}"
              (json_escape (pp_expr_text "if-cond" e))
              (stmt_list_to_json s1.s_node)
              (stmt_list_to_json s2.s_node)
          | Swhile (e, s) ->
            Printf.sprintf
              "{\"kind\":\"while\",\"cond_pp\":\"%s\",\
               \"body\":%s,\"loc\":null}"
              (json_escape (pp_expr_text "while-cond" e))
              (stmt_list_to_json s.s_node)
          | Smatch (e, branches) ->
            let branch_to_json
                ((vars, s) : (EcIdent.t * EcAst.ty) list * EcAst.stmt) =
              (* Pattern_pp: just the bound variable names —
                 constructor-name lookup needs PPEnv internals that
                 aren't exposed (UPSTREAM #24 known gap). *)
              let pattern_pp =
                String.concat " "
                  (List.map (fun (id, _) -> EcIdent.name id) vars)
              in
              Printf.sprintf
                "{\"pattern_pp\":\"%s\",\"body\":%s}"
                (json_escape pattern_pp)
                (stmt_list_to_json s.s_node)
            in
            Printf.sprintf
              "{\"kind\":\"match\",\"target_pp\":\"%s\",\
               \"branches\":[%s],\"loc\":null}"
              (json_escape (pp_expr_text "match-target" e))
              (String.concat ","
                 (List.map branch_to_json branches))
        and stmt_list_to_json (instrs : EcAst.instr list) : string =
          Printf.sprintf "[%s]"
            (String.concat "," (List.map stmt_node_to_json instrs))
        in
        let stmt_struct_node (s : EcAst.stmt) : string =
          Printf.sprintf "{\"kind\":\"stmt\",\"body\":%s}"
            (stmt_list_to_json s.s_node)
        in
        let pp_xpath_node label xp =
          pp_text label
            (fun () ->
               Format.asprintf "%a" (EcPrinting.pp_funname !ppe) xp)
        in
        let cmp_string = function
          | EcAst.FHle -> "<="
          | EcAst.FHeq -> "="
          | EcAst.FHge -> ">="
        in
        (* UPSTREAM #23: structured conclusion tree. Outermost form
           classified: PHL judgments become `judgment` nodes with
           labeled children; anything else (prop, chain goals, ...)
           is a single `pp` leaf. *)
        let conclusion_to_json (f : EcCoreFol.form) =
          let judgment kind body =
            Printf.sprintf
              "{\"kind\":\"judgment\",\"judgment_kind\":\"%s\",%s}"
              kind body
          in
          match f.f_node with
          | FhoareF hf ->
            (* exnpost has a `main` postcondition + an exnmap. v0
               surfaces only `main`; v1 may add per-exception
               handlers as additional fields. *)
            judgment "hoare"
              (Printf.sprintf "\"pre\":%s,\"stmt\":%s,\"post\":%s"
                 (pp_form_node "pre" (EcAst.hf_pr hf).inv)
                 (pp_xpath_node "stmt" hf.hf_f)
                 (pp_form_node "post" (EcAst.hf_po hf).hsi_inv.main))
          | FhoareS hs ->
            judgment "hoare"
              (Printf.sprintf "\"pre\":%s,\"stmt\":%s,\"post\":%s"
                 (pp_form_node "pre" (EcAst.hs_pr hs).inv)
                 (stmt_struct_node hs.hs_s)
                 (pp_form_node "post" (EcAst.hs_po hs).hsi_inv.main))
          | FbdHoareF bhf ->
            judgment "phoare"
              (Printf.sprintf
                 "\"pre\":%s,\"stmt\":%s,\"post\":%s,\"bound\":%s,\
                  \"cmp\":\"%s\""
                 (pp_form_node "pre" (EcAst.bhf_pr bhf).inv)
                 (pp_xpath_node "stmt" bhf.bhf_f)
                 (pp_form_node "post" (EcAst.bhf_po bhf).inv)
                 (pp_form_node "bound" (EcAst.bhf_bd bhf).inv)
                 (cmp_string bhf.bhf_cmp))
          | FbdHoareS bhs ->
            judgment "phoare"
              (Printf.sprintf
                 "\"pre\":%s,\"stmt\":%s,\"post\":%s,\"bound\":%s,\
                  \"cmp\":\"%s\""
                 (pp_form_node "pre" (EcAst.bhs_pr bhs).inv)
                 (stmt_struct_node bhs.bhs_s)
                 (pp_form_node "post" (EcAst.bhs_po bhs).inv)
                 (pp_form_node "bound" (EcAst.bhs_bd bhs).inv)
                 (cmp_string bhs.bhs_cmp))
          | FeHoareF ehf ->
            judgment "ehoare"
              (Printf.sprintf "\"pre\":%s,\"stmt\":%s,\"post\":%s"
                 (pp_form_node "pre" (EcAst.ehf_pr ehf).inv)
                 (pp_xpath_node "stmt" ehf.ehf_f)
                 (pp_form_node "post" (EcAst.ehf_po ehf).inv))
          | FeHoareS ehs ->
            judgment "ehoare"
              (Printf.sprintf "\"pre\":%s,\"stmt\":%s,\"post\":%s"
                 (pp_form_node "pre" (EcAst.ehs_pr ehs).inv)
                 (stmt_struct_node ehs.ehs_s)
                 (pp_form_node "post" (EcAst.ehs_po ehs).inv))
          | FequivF ef ->
            judgment "equiv"
              (Printf.sprintf
                 "\"pre\":%s,\"stmt_left\":%s,\"stmt_right\":%s,\"post\":%s"
                 (pp_form_node "pre" (EcAst.ef_pr ef).inv)
                 (pp_xpath_node "stmt_left" ef.ef_fl)
                 (pp_xpath_node "stmt_right" ef.ef_fr)
                 (pp_form_node "post" (EcAst.ef_po ef).inv))
          | FequivS es ->
            judgment "equiv"
              (Printf.sprintf
                 "\"pre\":%s,\"stmt_left\":%s,\"stmt_right\":%s,\"post\":%s"
                 (pp_form_node "pre" (EcAst.es_pr es).inv)
                 (stmt_struct_node es.es_sl)
                 (stmt_struct_node es.es_sr)
                 (pp_form_node "post" (EcAst.es_po es).inv))
          | FeagerF eg ->
            judgment "eager"
              (Printf.sprintf
                 "\"pre\":%s,\"stmt_left\":%s,\"stmt_right\":%s,\
                  \"transferred_left\":%s,\"transferred_right\":%s,\
                  \"post\":%s"
                 (pp_form_node "pre" (EcAst.eg_pr eg).inv)
                 (pp_xpath_node "stmt_left" eg.eg_fl)
                 (pp_xpath_node "stmt_right" eg.eg_fr)
                 (stmt_struct_node eg.eg_sl)
                 (stmt_struct_node eg.eg_sr)
                 (pp_form_node "post" (EcAst.eg_po eg).inv))
          | _ ->
            pp_form_node "conclusion" f
        in
        let subgoal_json i pregoal =
          (* Switch [ppe] to this pregoal's enriched env (with the
             pregoal's hypothesis bindings) so [pp_form] et al.
             resolve proof-bound xpaths correctly (addition 20). *)
          ppe := EcPrinting.PPEnv.ofenv
                   (EcEnv.LDecl.toenv pregoal.EcCoreGoal.g_hyps);
          let hyps_raw =
            EcEnv.LDecl.tohyps pregoal.EcCoreGoal.g_hyps in
          (* h_local is stored innermost-first; reverse so the daemon
             sees them in declaration order. *)
          let hyps_strs =
            List.rev_map hyp_json hyps_raw.EcBaseLogic.h_local in
          let concl_json = conclusion_to_json pregoal.EcCoreGoal.g_concl in
          Printf.sprintf
            "{\"index\":%d,\"hypotheses\":[%s],\"conclusion\":%s}"
            i (String.concat "," hyps_strs) concl_json
        in
        let subgoal_strs = List.mapi subgoal_json subgoals in
        Printf.sprintf
          "{\"active\":true,\"subgoal_count\":%d,\
           \"current_index\":0,\"subgoals\":[%s]}"
          count
          (String.concat "," subgoal_strs)

(* -------------------------------------------------------------------- *)
(* Sentence classification for PARSE-JSON / ANALYZE-JSON (addition 1).
   `meta` covers P_Undo/P_Exit; unknown constructors classify as
   `executable` (conservative: expect uuid advance). The match is kept
   exhaustive on purpose: a new global_action constructor must be
   consciously classified here. *)
let classify_global (g : EcParsetree.global_action) =
  let kind, cls = match g with
    | Gmodule _      -> ("Gmodule",      "executable")
    | Ginterface _   -> ("Ginterface",   "executable")
    | Goperator _    -> ("Goperator",    "executable")
    | Gexception _   -> ("Gexception",   "executable")
    | Gprocop _      -> ("Gprocop",      "executable")
    | Gpredicate _   -> ("Gpredicate",   "executable")
    | Gnotation _    -> ("Gnotation",    "executable")
    | Gabbrev _      -> ("Gabbrev",      "executable")
    | Gaxiom _       -> ("Gaxiom",       "executable")
    | Gtype _        -> ("Gtype",        "executable")
    | Gsubtype _     -> ("Gsubtype",     "executable")
    | Gtycinstance _ -> ("Gtycinstance", "executable")
    | Gaddrw _       -> ("Gaddrw",       "executable")
    | Greduction _   -> ("Greduction",   "executable")
    | Ghint _        -> ("Ghint",        "executable")
    | GthOpen _      -> ("GthOpen",      "executable")
    | GthClose _     -> ("GthClose",     "executable")
    | GthClear _     -> ("GthClear",     "executable")
    | GthRequire _   -> ("GthRequire",   "executable")
    | GthImport _    -> ("GthImport",    "executable")
    | GthExport _    -> ("GthExport",    "executable")
    | GthClone _     -> ("GthClone",     "executable")
    | GthAlias _     -> ("GthAlias",     "executable")
    | GModImport _   -> ("GModImport",   "executable")
    | GsctOpen _     -> ("GsctOpen",     "executable")
    | GsctClose _    -> ("GsctClose",    "executable")
    | Grealize _     -> ("Grealize",     "executable")
    | Gtactics _     -> ("Gtactics",     "executable")
    | Gtcdump _      -> ("Gtcdump",      "executable")
    | Gprover_info _ -> ("Gprover_info", "executable")
    | Gsave _        -> ("Gsave",        "executable")
    | Goption _      -> ("Goption",      "executable")
    (* Circuits' constraint-rewriting binding (landed on main). It
       mutates the environment like any declaration. *)
    | Gcrbinding _   -> ("Gcrbinding",   "executable")
    | Gpragma _      -> ("Gpragma",      "directive")
    | Gprint _       -> ("Gprint",       "directive")
    | Gsearch _      -> ("Gsearch",      "directive")
    | Glocate _      -> ("Glocate",      "directive")
    | GdumpWhy3 _    -> ("GdumpWhy3",    "directive")
    (* `expect "<msg>" by <directive>`: runs the inner directive and
       asserts its output; no proof-state mutation. *)
    | Gexpect _      -> ("Gexpect",      "directive")
  in
  (kind, cls)

(* -------------------------------------------------------------------- *)
(* Compute (line, col) at byte [offset] in [source], 1-indexed. Used by
   addition 16: when [start_offset] advances past leading whitespace,
   the reported line/col stays consistent with it. *)
let line_col_of input offset =
  let len = String.length input in
  let offset = max 0 (min offset len) in
  let line = ref 1 in
  let col  = ref 1 in
  for i = 0 to offset - 1 do
    match input.[i] with
    | '\n' -> incr line; col := 1
    | _    -> incr col
  done;
  (!line, !col)

let loc_to_json ?source (loc : EcLocation.t) =
  let (el, ec) = loc.EcLocation.loc_end in
  (* Addition 16: advance [start_offset] past leading separator
     whitespace so it points at the sentence's first real token.
     Only fires when [source] is in hand (i.e., inside PARSE-JSON /
     ANALYZE-JSON over a buffer). *)
  let (sl, sc, b) = match source with
    | None ->
      let (sl, sc) = loc.EcLocation.loc_start in
      (sl, sc, loc.loc_bchar)
    | Some input ->
      let len = String.length input in
      let b0  = max 0 (min len loc.loc_bchar) in
      let e0  = max b0 (min len loc.loc_echar) in
      let rec skip i =
        if i >= e0 then i
        else match input.[i] with
          | ' ' | '\t' | '\n' | '\r' -> skip (i + 1)
          | _ -> i
      in
      let b = skip b0 in
      let (sl, sc) = line_col_of input b in
      (sl, sc, b)
  in
  let src_field = match source with
    | None -> ""
    | Some input ->
      let len = String.length input in
      let e = max b (min len loc.loc_echar) in
      let slice = if b < len then String.sub input b (e - b) else "" in
      Printf.sprintf ",\"src\":\"%s\"" (json_escape slice)
  in
  Printf.sprintf
    "\"start_line\":%d,\"start_col\":%d,\"end_line\":%d,\
     \"end_col\":%d,\"start_offset\":%d,\"end_offset\":%d%s"
    sl sc el ec b loc.loc_echar src_field

(* -------------------------------------------------------------------- *)
(* Sentence-granular parse endpoint (addition 1, v0). Runs EC's real
   parser over a string buffer and emits one JSON record per parsed
   top-level form. *)
let parse_to_json input =
  let reader = EcIo.from_string input in
  let sentences = ref [] in
  let error = ref None in
  let emit cls kind loc =
    sentences :=
      Printf.sprintf
        "{\"class\":\"%s\",\"kind\":\"%s\",%s}"
        cls kind (loc_to_json ~source:input loc)
      :: !sentences
  in
  let break = ref false in
  begin try
    while not !break do
      let (_src, prog) = EcIo.xparse reader in
      let ploc = prog.EcLocation.pl_loc in
      match EcLocation.unloc prog with
      | EcParsetree.P_Prog (commands, locterm) ->
        List.iter
          (fun (g : EcParsetree.global) ->
            let (kind, cls) =
              classify_global (EcLocation.unloc g.gl_action) in
            emit cls kind g.gl_action.EcLocation.pl_loc)
          commands;
        if locterm then break := true
      | EcParsetree.P_DocComment _ -> emit "doc_comment" "DocComment" ploc
      | EcParsetree.P_Undo _       -> emit "meta" "Undo" ploc
      | EcParsetree.P_Exit         -> emit "meta" "Exit" ploc; break := true
    done
  with
  | End_of_file -> ()
  | EcParsetree.ParseError (loc, msg) ->
    let detail = odfl "parse error" msg in
    error := Some
      (Printf.sprintf
         "{%s,\"detail\":\"%s\"}"
         (loc_to_json loc) (json_escape detail))
  | EcParser.Error | EcLexer.LexicalError _ ->
    error := Some "{\"detail\":\"parse error\"}"
  end;
  EcIo.finalize reader;
  let err_field = match !error with
    | None -> "null"
    | Some s -> s
  in
  Printf.sprintf
    "{\"sentences\":[%s],\"parse_error\":%s}"
    (String.concat "," (List.rev !sentences)) err_field

(* -------------------------------------------------------------------- *)
(* Addition 14: ANALYZE-JSON — stateless batch diagnostics. Parses a
   document, runs every sentence against a fresh scope, and returns
   one JSON envelope carrying every parse / type / tactic error keyed
   back to its sentence index.

   v0 scope: a parse error stops the loop (parse-recovery deferred);
   no cascade tagging. Pragmas inside the analyzed document still
   mutate global EC state (v1 isolates with a pragma-stack
   save/restore). Diagnostics carry [enclosing_scope] from a textual
   scope stack (proof/theory/section) so clients can collapse
   cascading errors; a failing proof closer triggers a synthetic
   `abort` so subsequent sentences are processed at outer scope
   (Tier-2 recovery). *)
let analyze_to_json ~(checkmode : EcCommands.checkmode) input =
  let reader = EcIo.from_string input in
  let next_idx = ref 0 in
  (* (idx, json_string) pairs for sentences[] (newest-first). *)
  let sentences = ref [] in
  (* (idx, class_str, parsed_action) for the dry-run pass. *)
  let actions = ref [] in
  let parse_diag = ref None in
  let break = ref false in
  let emit_sentence cls kind loc =
    let j =
      Printf.sprintf
        "{\"class\":\"%s\",\"kind\":\"%s\",%s}"
        cls kind (loc_to_json ~source:input loc)
    in
    sentences := (!next_idx, j) :: !sentences;
    incr next_idx
  in
  let push_action cls action =
    actions := (!next_idx - 1, cls, action) :: !actions
  in
  begin try
    while not !break do
      let (_src, prog) = EcIo.xparse reader in
      let ploc = prog.EcLocation.pl_loc in
      match EcLocation.unloc prog with
      | EcParsetree.P_Prog (commands, locterm) ->
        List.iter
          (fun (g : EcParsetree.global) ->
             let (kind, cls) =
               classify_global (EcLocation.unloc g.gl_action) in
             emit_sentence cls kind g.gl_action.EcLocation.pl_loc;
             push_action cls g.gl_action)
          commands;
        if locterm then break := true
      | EcParsetree.P_DocComment _ ->
        emit_sentence "doc_comment" "DocComment" ploc
      | EcParsetree.P_Undo _ -> emit_sentence "meta" "Undo" ploc
      | EcParsetree.P_Exit  ->
        emit_sentence "meta" "Exit" ploc; break := true
    done
  with
  | End_of_file -> ()
  | EcParsetree.ParseError (loc, msg) ->
    let detail = odfl "parse error" msg in
    let loc_str =
      let (sl, sc) = loc.EcLocation.loc_start in
      let (el, ec) = loc.EcLocation.loc_end in
      let file =
        if loc.EcLocation.loc_fname = "" then "null"
        else Printf.sprintf "\"%s\"" (json_escape loc.EcLocation.loc_fname)
      in
      Printf.sprintf
        "{\"file\":%s,\"start_line\":%d,\"start_col\":%d,\
         \"end_line\":%d,\"end_col\":%d}"
        file sl sc el ec
    in
    parse_diag := Some
      (Printf.sprintf
         "{\"sentence_index\":null,\"code\":\"ParseError\",\
          \"phase\":\"parse\",\"location\":%s,\"detail\":\"%s\"}"
         loc_str (json_escape detail))
  | EcParser.Error | EcLexer.LexicalError _ ->
    parse_diag := Some
      "{\"sentence_index\":null,\"code\":\"ParseError\",\
       \"phase\":\"parse\",\"location\":null,\"detail\":\"parse error\"}"
  end;
  EcIo.finalize reader;

  (* Scope tracking for diagnostic [enclosing_scope]. Openers/closers
     are recognized on textual structure (push/pop optimistically so
     the user-facing scope reflects the source even when the opener
     itself errored). *)
  let scope_kind_str = function
    | `Proof -> "proof"
    | `Theory -> "theory"
    | `Section -> "section"
  in
  let scope_change_of_action a =
    match EcLocation.unloc a with
    | EcParsetree.Gaxiom { pa_kind = EcParsetree.PLemma None; _ } ->
      `Open `Proof
    | EcParsetree.Grealize r
      when (EcLocation.unloc r).EcParsetree.pr_proof = None ->
      `Open `Proof
    | EcParsetree.Gsave _ -> `Close `Proof
    | EcParsetree.GthOpen _ -> `Open `Theory
    | EcParsetree.GthClose _ -> `Close `Theory
    | EcParsetree.GsctOpen _ -> `Open `Section
    | EcParsetree.GsctClose _ -> `Close `Section
    | _ -> `None
  in
  let scope_stack = ref [] in
  let current_scope_json () =
    match !scope_stack with
    | [] -> "null"
    | (k, opener_idx) :: _ ->
      Printf.sprintf
        "{\"kind\":\"%s\",\"opener_sentence_index\":%d}"
        (scope_kind_str k) opener_idx
  in

  (* Dry-run pass on a fresh scope (boot:false → prelude loaded). *)
  let scope = ref
    (EcCommands.initial ~checkmode ~boot:false ~checkproof:true) in
  let exec_diags = ref [] in
  let inject_envelope idx scope_json payload =
    (* payload is "{\"code\":...}" — splice sentence_index +
       enclosing_scope after the opening brace. *)
    let prefix =
      Printf.sprintf
        "{\"sentence_index\":%d,\"enclosing_scope\":%s,"
        idx scope_json
    in
    prefix ^ String.sub payload 1 (String.length payload - 1)
  in
  (* Synthetic abort — Tier-2 recovery (UPSTREAM addition 14): when a
     textual closer fails, EC still thinks we're inside the proof and
     every subsequent top-level sentence errors with "cannot process
     [...] inside a proof script". Force-discard the broken proof by
     feeding a synthetic `Gsave `Abort` at the closer's location. *)
  let synthetic_abort_at action =
    let loc = (action : _ EcLocation.located).EcLocation.pl_loc in
    EcLocation.mk_loc loc
      (EcParsetree.Gsave (EcLocation.mk_loc loc `Abort))
  in
  List.iter
    (fun (idx, cls, action) ->
       if cls = "executable" || cls = "doc_comment" then begin
         let change = scope_change_of_action action in
         (* [scope_at_error] is the scope this sentence sits in
            textually — for openers/closers, the OUTER scope. *)
         let scope_at_error = current_scope_json () in
         let closer_failed = ref false in
         (try
            scope :=
              EcCommands.process_internal EcCommands.loader !scope action
          with e ->
            let payload = error_json_of_exn e in
            exec_diags :=
              inject_envelope idx scope_at_error payload
              :: !exec_diags;
            (match change with
             | `Close `Proof -> closer_failed := true
             | _ -> ()));
         if !closer_failed then begin
           try
             scope :=
               EcCommands.process_internal EcCommands.loader !scope
                 (synthetic_abort_at action)
           with _ -> ()
         end;
         (* Update the scope stack from textual structure regardless
            of whether EC accepted the sentence. *)
         match change with
         | `Open k -> scope_stack := (k, idx) :: !scope_stack
         | `Close _ ->
           (match !scope_stack with
            | _ :: rest -> scope_stack := rest
            | [] -> ())
         | `None -> ()
       end)
    (List.rev !actions);

  let all_diags =
    let xs = List.rev !exec_diags in
    match !parse_diag with
    | Some p -> xs @ [p]
    | None -> xs
  in
  let sentences_str =
    String.concat ","
      (!sentences |> List.rev |> List.map snd)
  in
  Printf.sprintf
    "{\"sentences\":[%s],\"diagnostics\":[%s]}"
    sentences_str (String.concat "," all_diags)
