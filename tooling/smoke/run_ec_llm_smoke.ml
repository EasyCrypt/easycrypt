(** End-to-end smoke for [Ec_llm_session].

    Spawns the real [ec llm] subprocess, drives the full session API
    ([exec], [goals], [revert_to], [close]), and verifies the wire
    protocol round-trips. Intended as a local integration check for
    Phase 1 — not part of the Phase-0b composition gate. Degrades
    gracefully when the EC binary is unavailable (prints "skip" and
    exits 0) so CI without a built EC still passes. *)

open Ecd_core

let binary_path () =
  match Sys.getenv_opt "EC_LLM_BIN" with
  | Some p -> Some p
  | None ->
    (* Default: prefer the in-tree dune build. *)
    let candidate = Filename.concat (Sys.getcwd ()) "_build/default/src/ec.exe" in
    if Sys.file_exists candidate then Some candidate
    else
      let which = Printf.sprintf "command -v easycrypt 2>/dev/null" in
      let ic = Unix.open_process_in which in
      let line = try Some (input_line ic) with End_of_file -> None in
      let _ = Unix.close_process_in ic in
      line

let expect_ok label = function
  | Ok x -> Printf.printf "ok: %s\n%!" label; x
  | Error e ->
    Printf.printf "FAIL: %s: %s\n%!" label (Error.to_string e);
    exit 1

let expect_err label = function
  | Error e -> Printf.printf "ok: %s (err: %s)\n%!" label (Error.to_string e)
  | Ok _ ->
    Printf.printf "FAIL: %s: expected error, got ok\n%!" label;
    exit 1

let () =
  match binary_path () with
  | None ->
    Printf.printf "skip: no ec llm binary found (set EC_LLM_BIN)\n%!";
    exit 0
  | Some bin ->
    Printf.printf "smoke: using binary %s\n%!" bin;
    Eio_main.run @@ fun env ->
    Eio.Switch.run @@ fun sw ->
    let process_mgr = Eio.Stdenv.process_mgr env in
    (* Capture the transcript into a buffer so we can inspect it. *)
    let transcript_buf = Buffer.create 4096 in
    Transcript.configure (Transcript.to_buffer transcript_buf);
    Ec_llm_session.configure ~process_mgr ~executable:bin
      ~extra_args:["-I"; Filename.concat (Sys.getcwd ()) "theories"] ();
    let s = Ec_llm_session.start ~sw ~label:"primary" in

    (* 1. exec a simple require — uuid should advance by 1. *)
    let ok = expect_ok "exec require"
      (Ec_llm_session.exec s
         ~corr:(Correlation.of_client "smoke-req")
         ~sentence_class:`Executable
         ~source:"require import AllCore.")
    in
    assert (ok.replied_uuid >= 1);
    assert (not ok.restarted);

    (* Directive: `pragma noop.` (no-op; read-only). uuid must NOT
       advance per addition 7 / protocol § 15.2. *)
    let pre = ok.replied_uuid in
    let dir = expect_ok "exec pragma noop (directive)"
      (Ec_llm_session.exec s
         ~corr:(Correlation.of_client "smoke-dir")
         ~sentence_class:`Directive
         ~source:"pragma noop.")
    in
    if dir.replied_uuid = pre then
      Printf.printf "ok: directive kept uuid at %d\n%!" pre
    else begin
      Printf.printf "FAIL: directive advanced uuid %d -> %d\n%!"
        pre dir.replied_uuid;
      exit 1
    end;

    (* 2. exec an axiom and start a proof. *)
    let _ = expect_ok "exec lemma open"
      (Ec_llm_session.exec s
         ~corr:(Correlation.of_client "smoke-lemma")
         ~sentence_class:`Executable
         ~source:"lemma foo (n : int) : 0 <= n => 0 < n + 1.")
    in
    let _ = expect_ok "exec proof."
      (Ec_llm_session.exec s
         ~corr:(Correlation.of_client "smoke-proof")
         ~sentence_class:`Executable
         ~source:"proof.")
    in

    (* 3. goals (GOALS-JSON) — structured JSON body. *)
    let g = expect_ok "goals (JSON)" (Ec_llm_session.goals s) in
    if String.length g > 0
       && (String.sub g 0 1 = "{" || String.sub g 0 2 = "{\"") then
      Printf.printf "ok: goals payload looks like JSON (%d chars)\n%!"
        (String.length g)
    else begin
      Printf.printf "FAIL: goals payload not JSON: %s\n%!" g;
      exit 1
    end;

    (* 4. revert to the earlier uuid — stub id encoding lets us
       target uuid=1 by constructing the matching sentence id. *)
    (* Revert to the first exec's sentence id. With the real id map
       (Phase 2), revert_to requires a sentence id previously issued
       by the session; we saved `ok` from step 1. *)
    let () = expect_ok "revert to first sentence"
      (Ec_llm_session.revert_to s ok.sentence_id)
    in

    (* 5. Post-revert: another exec should succeed and advance uuid. *)
    let after = expect_ok "exec after revert"
      (Ec_llm_session.exec s
         ~corr:(Correlation.of_client "smoke-req2")
         ~sentence_class:`Executable
         ~source:"lemma bar : 1 = 1.")
    in
    assert (after.replied_uuid >= 2);

    (* 6. Structured-error path: feed malformed input. *)
    let _ = expect_err "parse error propagates"
      (Ec_llm_session.exec s
         ~corr:(Correlation.of_client "smoke-err")
         ~sentence_class:`Executable
         ~source:"@@invalid.")
    in

    (* 7. [restarted] tag surfaces through `exec_ok.restarted`. *)
    let restart_ok = expect_ok "exec pragma restart"
      (Ec_llm_session.exec s
         ~corr:(Correlation.of_client "smoke-restart")
         ~sentence_class:`Executable
         ~source:"pragma restart.")
    in
    if restart_ok.restarted then
      Printf.printf "ok: restart tag surfaced (restarted=true)\n%!"
    else begin
      Printf.printf "FAIL: restart tag not surfaced\n%!";
      exit 1
    end;

    (* 7.5. Addition 16 sanity: PARSE-JSON's [start_offset] lands on
       the first real token of each sentence, not on leading
       separator whitespace. Feed a source with a deliberate blank
       line + indentation before the second sentence and check that
       its [start_offset] points at the `p` of `pragma`. *)
    let src16 = "pragma noop.\n\n   pragma noop." in
    let (parsed16, _perr16) = expect_ok "parse with leading ws"
      (Ec_llm_session.parse_source s src16)
    in
    (match List.filter
             (fun (p : Ec_llm_session.parsed_sentence) -> p.cls <> `Meta)
             parsed16
     with
     | [_; second] ->
       (* Skip the first sentence's bytes by searching for 'p' past
          the first '.', guaranteed to land on the second `pragma`. *)
       let dot = String.index src16 '.' in
       let expected = String.index_from src16 (dot + 1) 'p' in
       if second.start_offset = expected
          && String.length src16 > expected
          && src16.[expected] = 'p'
       then
         Printf.printf
           "ok: addition 16 — start_offset at first token (%d)\n%!"
           second.start_offset
       else begin
         Printf.printf
           "FAIL: addition 16 — second sentence start_offset=%d \
            (expected %d, byte=%c)\n%!"
           second.start_offset expected
           (if expected < String.length src16 then src16.[expected] else '?');
         exit 1
       end
     | other ->
       Printf.printf "FAIL: expected 2 non-meta sentences, got %d\n%!"
         (List.length other);
       exit 1);

    Ec_llm_session.close s;

    (* 8. Transcript sanity: required event kinds must be present. *)
    let transcript = Buffer.contents transcript_buf in
    let has_kind k =
      let marker = Printf.sprintf "\"kind\":\"%s\"" k in
      let rec search from =
        match String.index_from_opt transcript from marker.[0] with
        | None -> false
        | Some i ->
          if i + String.length marker <= String.length transcript
             && String.sub transcript i (String.length marker) = marker
          then true
          else search (i + 1)
      in
      search 0
    in
    let required =
      [ "session.spawn"; "session.exec"; "session.reply"; "session.restart" ]
    in
    List.iter (fun k ->
      if has_kind k then
        Printf.printf "ok: transcript has %s\n%!" k
      else begin
        Printf.printf "FAIL: transcript missing %s\n%!" k;
        exit 1
      end) required;

    Printf.printf "ec-llm smoke passed\n%!"
