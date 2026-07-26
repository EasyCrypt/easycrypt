(** Smoke for ANALYZE-JSON (addition 14). Feeds a small document
    containing a clean preface plus a deliberate type error, asserts:
    - response is a JSON envelope with [sentences] + [diagnostics] arrays,
    - sentences[] enumerates every parsed top-level form,
    - diagnostics[] reports the expected TypeError keyed by sentence_index.

    Uses [Ec_llm_session.analyze_source]. v0 scope: parse error
    short-circuits the loop, no cascade tagging — both deferred to v1. *)

open Ecd_core
open Eio.Std

let binary_path () =
  match Sys.getenv_opt "EC_LLM_BIN" with
  | Some p -> Some p
  | None ->
    let candidate = Filename.concat (Sys.getcwd ()) "_build/default/src/ec.exe" in
    if Sys.file_exists candidate then Some candidate
    else
      let ic = Unix.open_process_in "command -v easycrypt 2>/dev/null" in
      let line = try Some (input_line ic) with End_of_file -> None in
      let _ = Unix.close_process_in ic in
      line

let pass = ref 0
let fail = ref 0
let check label cond detail =
  if cond then begin incr pass; Printf.printf "  ok  %s\n%!" label end
  else begin incr fail; Printf.printf "  FAIL %s — %s\n%!" label detail end

let parse_envelope raw =
  try
    let j = Yojson.Safe.from_string raw in
    let open Yojson.Safe.Util in
    let sentences = j |> member "sentences" |> to_list in
    let diagnostics = j |> member "diagnostics" |> to_list in
    Some (j, sentences, diagnostics)
  with _ -> None

let find_diagnostic_with_code code items =
  let open Yojson.Safe.Util in
  List.find_opt (fun d ->
    try d |> member "code" |> to_string = code with _ -> false)
    items

let () =
  match binary_path () with
  | None ->
    Printf.printf "skip: no ec llm binary found (set EC_LLM_BIN)\n%!";
    exit 0
  | Some bin ->
    Eio_main.run @@ fun env ->
    Switch.run @@ fun sw ->
    Transcript.configure (Transcript.devnull ());
    Ec_llm_session.configure
      ~process_mgr:(Eio.Stdenv.process_mgr env)
      ~executable:bin
      ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
    let s = Ec_llm_session.start ~sw ~label:"analyze-test" in

    (* Case 1 — happy path: clean document, no diagnostics. *)
    let clean =
      "require import AllCore.\n\
       op one : int = 1.\n\
       lemma triv : 1 = 1 by trivial.\n"
    in
    (match Ec_llm_session.analyze_source s ~source:clean with
     | Error e ->
       check "case 1 — analyze returns Ok" false (Error.to_string e)
     | Ok raw ->
       (match parse_envelope raw with
        | None ->
          check "case 1 — JSON envelope parses" false
            (Printf.sprintf "raw=%s" (String.sub raw 0 (min 80 (String.length raw))))
        | Some (_, sentences, diagnostics) ->
          check "case 1 — JSON envelope parses" true "";
          check "case 1 — sentences[] non-empty"
            (List.length sentences >= 3)
            (Printf.sprintf "got %d sentences" (List.length sentences));
          check "case 1 — diagnostics[] empty on clean document"
            (List.length diagnostics = 0)
            (Printf.sprintf "got %d diagnostics" (List.length diagnostics))));

    (* Case 2 — type error in the middle of the document. EC's
       per-sentence atomicity must keep the surrounding sentences
       parseable; ANALYZE-JSON must report the error against its
       sentence_index. *)
    let with_type_error =
      "require import AllCore.\n\
       op bad : int = true.\n\
       op good : int = 1.\n"
    in
    (match Ec_llm_session.analyze_source s ~source:with_type_error with
     | Error e ->
       check "case 2 — analyze returns Ok" false (Error.to_string e)
     | Ok raw ->
       (match parse_envelope raw with
        | None ->
          check "case 2 — JSON envelope parses" false ""
        | Some (_, sentences, diagnostics) ->
          check "case 2 — sentences[] enumerates all 3 forms"
            (List.length sentences = 3)
            (Printf.sprintf "got %d sentences" (List.length sentences));
          check "case 2 — at least one diagnostic"
            (List.length diagnostics >= 1)
            (Printf.sprintf "got %d diagnostics" (List.length diagnostics));
          (match find_diagnostic_with_code "TypeError" diagnostics with
           | None ->
             check "case 2 — TypeError diagnostic present" false
               (Yojson.Safe.to_string (`List diagnostics))
           | Some d ->
             check "case 2 — TypeError diagnostic present" true "";
             let open Yojson.Safe.Util in
             let idx =
               try Some (d |> member "sentence_index" |> to_int)
               with _ -> None
             in
             check "case 2 — sentence_index points at the bad sentence"
               (idx = Some 1)
               (match idx with
                | Some n -> Printf.sprintf "got %d" n
                | None -> "got null"))));

    (* Case 3 — confirm ANALYZE-JSON didn't mutate the live session.
       The state-mutating analysis ran against a fresh scope; back on
       the primary, uuid should still be 0 and a subsequent exec must
       advance it normally. *)
    let corr = Correlation.of_client "after-analyze" in
    let primary_uuid_before = Ec_llm_session.current_uuid s in
    check "case 3 — primary uuid unchanged after analyze"
      (primary_uuid_before = 0)
      (Printf.sprintf "got %d" primary_uuid_before);
    (match
       Ec_llm_session.exec s ~corr ~sentence_class:`Executable
         ~source:"require import AllCore."
     with
     | Error e ->
       check "case 3 — primary still functional" false (Error.to_string e)
     | Ok ok ->
       check "case 3 — primary still functional" true "";
       check "case 3 — primary advanced uuid"
         (ok.replied_uuid > primary_uuid_before)
         (Printf.sprintf "got %d (was %d)"
            ok.replied_uuid primary_uuid_before));

    (* Case 4 — enclosing_scope tagging. A failing tactic inside an
       interactive proof should be tagged with scope.kind = "proof"
       and opener_sentence_index pointing at the lemma. A type error
       at top level (post-qed) should have enclosing_scope = null. *)
    let with_proof_scope =
      "require import AllCore.\n\
       lemma foo : 1 + 1 = 2.\n\
       proof.\n\
       apply not_a_real_lemma.\n\
       qed.\n\
       op bad : int = true.\n"
    in
    (match Ec_llm_session.analyze_source s ~source:with_proof_scope with
     | Error e ->
       check "case 4 — analyze returns Ok" false (Error.to_string e)
     | Ok raw ->
       (match parse_envelope raw with
        | None ->
          check "case 4 — JSON envelope parses" false ""
        | Some (_, _sentences, diagnostics) ->
          let open Yojson.Safe.Util in
          let scope_of d =
            try Some (d |> member "enclosing_scope")
            with _ -> None
          in
          let scope_kind d =
            try Some (d |> member "enclosing_scope" |> member "kind" |> to_string)
            with _ -> None
          in
          let scope_opener d =
            try Some (d |> member "enclosing_scope"
                      |> member "opener_sentence_index" |> to_int)
            with _ -> None
          in
          let in_proof =
            List.find_opt
              (fun d -> scope_kind d = Some "proof")
              diagnostics
          in
          (match in_proof with
           | None ->
             check "case 4 — diagnostic inside proof tagged with proof scope"
               false
               (Yojson.Safe.to_string (`List diagnostics))
           | Some d ->
             check "case 4 — diagnostic inside proof tagged with proof scope"
               true "";
             check "case 4 — opener_sentence_index points at lemma (idx=1)"
               (scope_opener d = Some 1)
               (match scope_opener d with
                | Some n -> Printf.sprintf "got %d" n
                | None -> "no opener_sentence_index"));
          (* Top-level diagnostic (op bad : int = true.) should have
             enclosing_scope = null. *)
          let top_level =
            List.find_opt
              (fun d -> scope_of d = Some `Null)
              diagnostics
          in
          check "case 4 — diagnostic past qed has null enclosing_scope"
            (top_level <> None)
            (Yojson.Safe.to_string (`List diagnostics));
          (* Synthetic-abort recovery: the `op bad` past qed should
             produce its real TypeError (int = true is a type
             mismatch), NOT EC's bogus "cannot process [operator]
             inside a proof script" that you get without the
             recovery. *)
          (match top_level with
           | None -> ()  (* already failed above *)
           | Some d ->
             let code = try d |> member "code" |> to_string with _ -> "" in
             let detail = try d |> member "detail" |> to_string with _ -> "" in
             check "case 4 — post-qed diagnostic is real TypeError"
               (code = "TypeError")
               (Printf.sprintf "got code=%s" code);
             let contains needle haystack =
               let nlen = String.length needle in
               let hlen = String.length haystack in
               let rec scan i =
                 if i + nlen > hlen then false
                 else if String.sub haystack i nlen = needle then true
                 else scan (i + 1)
               in
               scan 0
             in
             check "case 4 — post-qed detail is not 'inside proof script'"
               (not (contains "inside a proof script" detail))
               (Printf.sprintf "detail=%s" detail))));

    Ec_llm_session.close s;
    Printf.printf "\n== analyze smoke ==\n";
    Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
    exit (if !fail = 0 then 0 else 1)
