(** Phase 2 Document smoke: parse a document, edit it, compute the
    diff, assert the common-prefix split is correct. *)

open Ecd_core
open Eio.Std

let binary_path () =
  match Sys.getenv_opt "EC_LLM_BIN" with
  | Some p -> Some p
  | None ->
    let candidate = Filename.concat (Sys.getcwd ())
                      "_build/default/src/ec.exe" in
    if Sys.file_exists candidate then Some candidate else None

let src_v1 =
  "require import AllCore.\n\
   op one : int = 1.\n\
   lemma l : one = 1.\n\
   proof. rewrite /one. trivial. qed.\n"

(* Edit: replace `op one = 1` with `op two = 2` and adapt the lemma.
   Prefix (require import) is unchanged; everything else differs. *)
let src_v2 =
  "require import AllCore.\n\
   op two : int = 2.\n\
   lemma l : two = 2.\n\
   proof. rewrite /two. trivial. qed.\n"

(* Edit 2: add a pragma after the require but leave the rest intact.
   Prefix = [require]; remainder all differs because splits shift. *)
let src_v3 =
  "require import AllCore.\n\
   pragma noop.\n\
   op one : int = 1.\n\
   lemma l : one = 1.\n\
   proof. rewrite /one. trivial. qed.\n"

let expect_ok label = function
  | Ok x -> Printf.printf "ok: %s\n%!" label; x
  | Error e ->
    Printf.printf "FAIL: %s: %s\n%!" label (Error.to_string e);
    exit 1

let () =
  match binary_path () with
  | None ->
    Printf.printf "skip: no ec llm binary found\n%!"; exit 0
  | Some bin ->
    Printf.printf "document-smoke: bin=%s\n%!" bin;
    Eio_main.run @@ fun env ->
    Switch.run @@ fun sw ->
    let process_mgr = Eio.Stdenv.process_mgr env in
    Ec_llm_session.configure ~process_mgr ~executable:bin
      ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
    let s = Ec_llm_session.start ~sw ~label:"splitter" in

    let d1 = expect_ok "parse v1"
      (Document.parse s ~uri:"file:///tmp/d1.ec" ~version:1 ~source:src_v1)
    in
    Printf.printf "  v1: %d sentences\n%!" (List.length d1.sentences);

    let d2 = expect_ok "parse v2"
      (Document.parse s ~uri:"file:///tmp/d1.ec" ~version:2 ~source:src_v2)
    in
    Printf.printf "  v2: %d sentences\n%!" (List.length d2.sentences);

    (* v1 → v2: require unchanged, rest differs. *)
    let diff12 = Document.diff ~old:d1 ~new_:d2 in
    Printf.printf "  diff(v1,v2): prefix=%d removed=%d added=%d\n%!"
      (List.length diff12.unchanged_prefix)
      (List.length diff12.removed)
      (List.length diff12.added);
    if List.length diff12.unchanged_prefix = 1
       && List.length diff12.removed >= 1
       && List.length diff12.added >= 1 then
      Printf.printf "ok: v1→v2 prefix=1, remainder swapped\n%!"
    else begin
      Printf.printf "FAIL: v1→v2 diff unexpected\n%!";
      exit 1
    end;

    (* v1 → v3: adds `pragma noop.` in position 2; prefix=1 because
       sentence 2 shifts. *)
    let d3 = expect_ok "parse v3"
      (Document.parse s ~uri:"file:///tmp/d1.ec" ~version:3 ~source:src_v3)
    in
    let diff13 = Document.diff ~old:d1 ~new_:d3 in
    Printf.printf "  diff(v1,v3): prefix=%d removed=%d added=%d\n%!"
      (List.length diff13.unchanged_prefix)
      (List.length diff13.removed)
      (List.length diff13.added);
    if List.length diff13.unchanged_prefix = 1
       && List.length diff13.added = List.length diff13.removed + 1 then
      Printf.printf "ok: v1→v3 prefix=1, added one pragma\n%!"
    else begin
      Printf.printf "FAIL: v1→v3 diff unexpected\n%!";
      exit 1
    end;

    (* v1 → v1: nothing changed. prefix=all, remainder empty. *)
    let d1' = expect_ok "reparse v1"
      (Document.parse s ~uri:"file:///tmp/d1.ec" ~version:1 ~source:src_v1)
    in
    let diff11 = Document.diff ~old:d1 ~new_:d1' in
    if List.length diff11.unchanged_prefix = List.length d1.sentences
       && diff11.removed = []
       && diff11.added = [] then
      Printf.printf "ok: v1→v1 no-op diff\n%!"
    else begin
      Printf.printf "FAIL: v1→v1 not a no-op\n%!";
      exit 1
    end;

    (* Workspace round-trip. *)
    let ws = Workspace.make ~load_path:[ "theories" ] in
    Workspace.open_document ws d1;
    let _ = expect_ok "get doc back from workspace"
      (match Workspace.get ws ~uri:d1.uri with
       | Some _ -> Ok () | None -> Error (Error.Internal { detail = "no doc" }))
    in
    (match Workspace.update_document ws d2 with
     | None ->
       Printf.printf "FAIL: workspace update returned None\n%!"; exit 1
     | Some _ ->
       Printf.printf "ok: workspace didChange v1→v2 returned a diff\n%!");
    (match Workspace.get ws ~uri:d2.uri with
     | Some doc when doc.version = 2 ->
       Printf.printf "ok: workspace now holds v2\n%!"
     | _ ->
       Printf.printf "FAIL: workspace didn't replace with v2\n%!"; exit 1);
    assert (List.length (Workspace.documents ws) = 1);
    Workspace.close_document ws ~uri:d1.uri;
    assert (Workspace.get ws ~uri:d1.uri = None);
    Printf.printf "ok: workspace close removes the doc\n%!";

    Ec_llm_session.close s;
    Printf.printf "document smoke passed\n%!"
