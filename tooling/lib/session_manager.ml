(** See [session_manager.mli]. *)

type entry = {
  proof_state : Proof_state.t;
  analyze    : Ec_llm_session.t;
  (* [project_root] is recorded for diagnostics only; not currently
     read back at runtime. Kept on the entry so debug dumps /
     post-beta LRU eviction policy have it without re-resolving. *)
  project_root : string [@warning "-69"];
}

type t = {
  (* Switch for spawned EC subprocesses. Currently only used when
     [spawn_entry] is called via [proof_state_for] / [analyze_session_for],
     which both take their own [~sw] argument. Kept here for the
     post-beta hot-reload path (eviction → re-spawn under the same
     switch without threading [sw] through). *)
  conn_sw           : Eio.Switch.t [@warning "-69"];
  connection_label  : string;
  (* Keyed by the canonicalized project_root absolute path. *)
  sessions          : (string, entry) Hashtbl.t;
  (* URI → project_root cache. Cleared on [invalidate_project]
     for URIs whose resolved root matches. *)
  uri_to_root       : (string, string) Hashtbl.t;
  mutable closed    : bool;
}

let create ~sw ~connection_label =
  { conn_sw = sw;
    connection_label;
    sessions = Hashtbl.create 4;
    uri_to_root = Hashtbl.create 16;
    closed = false;
  }

(* ---------------- URI → file-path → project_root --------------- *)

(* Strip a "file://" scheme + percent-decode. Returns [None] if
   [uri] doesn't look like a local file URI. *)
let path_of_file_uri (uri : string) : string option =
  let prefix = "file://" in
  let plen = String.length prefix in
  if String.length uri < plen
     || String.sub uri 0 plen <> prefix
  then None
  else begin
    let raw = String.sub uri plen (String.length uri - plen) in
    (* Skip optional "//host" host (always empty for local files in
       practice; tolerate it just in case). *)
    let stripped =
      if String.length raw > 0 && raw.[0] <> '/' then
        match String.index_opt raw '/' with
        | Some i -> String.sub raw i (String.length raw - i)
        | None -> raw
      else raw
    in
    (* Percent-decode: the only sequences VSCode emits in practice
       are %20 (space), but be defensive about all %xx. *)
    let buf = Buffer.create (String.length stripped) in
    let i = ref 0 in
    let n = String.length stripped in
    while !i < n do
      let c = stripped.[!i] in
      if c = '%' && !i + 2 < n then begin
        match int_of_string_opt ("0x" ^ String.sub stripped (!i + 1) 2) with
        | Some code -> Buffer.add_char buf (Char.chr code); i := !i + 3
        | None -> Buffer.add_char buf c; incr i
      end else begin
        Buffer.add_char buf c; incr i
      end
    done;
    Some (Buffer.contents buf)
  end

(* Canonicalize: realpath if accessible, else fall back to the
   given path. Avoids spurious key divergence from `.`/`..` /
   symlinks. *)
let canonicalize (path : string) : string =
  try Unix.realpath path
  with Unix.Unix_error _ -> path

(* Walk up the directory tree from [path] looking for
   `easycrypt.project`. Returns the full path to the closest hit,
   or [None] if none found before the filesystem root.

   DUPLICATE-OF-TRUTH: this MUST stay in sync with
   [EcOptions.find_project_file] in src/ecOptions.ml. We can't
   call EC's version because the daemon's boundary-allowlist
   ([tooling/.boundary-allowlist]) forbids linking ecLib — keeps
   the daemon ↔ ec.exe interaction restricted to the `ec llm`
   subprocess protocol, which is load-bearing for the eventual
   EC-merge plan. The 25-line walk has no edge cases and is
   well-exercised via EC's startup; the duplication cost is
   bounded. UPSTREAM § 14 carries a pinned TODO to share both via
   a small EC-merge-time shim. *)
let find_project_file (path : string option) : string option =
  let projname = "easycrypt.project" in
  let rec find (p : string) : string option =
    let candidate = Filename.concat p projname in
    if Sys.file_exists candidate then Some candidate
    else if Filename.dirname p = p then None
    else find (Filename.dirname p)
  in
  let root =
    match path with
    | Some p -> Filename.dirname p
    | None   -> Unix.getcwd ()
  in
  let root =
    if Filename.is_relative root
    then Filename.concat (Unix.getcwd ()) root
    else root
  in
  find root

(* Resolve a URI to its project_root. For URIs without an
   [easycrypt.project] up-tree, falls back to the file's
   containing directory (synthetic project). Caches the result. *)
let resolve_project_root (t : t) ~(uri : string) : string option =
  match Hashtbl.find_opt t.uri_to_root uri with
  | Some r -> Some r
  | None ->
    match path_of_file_uri uri with
    | None -> None
    | Some file_path ->
      let canon_file = canonicalize file_path in
      let project_root =
        match find_project_file (Some canon_file) with
        | Some projfile -> canonicalize (Filename.dirname projfile)
        | None ->
          (* Synthetic project: the file's containing directory.
             Bounds session count by directory. *)
          canonicalize (Filename.dirname canon_file)
      in
      Hashtbl.replace t.uri_to_root uri project_root;
      Some project_root

let project_root_for t ~uri = resolve_project_root t ~uri

(* ---------------- Spawn / lookup ------------------------------- *)

let spawn_entry (t : t) ~(sw : Eio.Switch.t) ~(project_root : string) : entry =
  let label_suffix =
    (* Last path component for readable per-session labels. *)
    let bn = Filename.basename project_root in
    if bn = "" || bn = "/" then "root" else bn
  in
  let primary_label =
    Printf.sprintf "lsp-primary-%s/%s" t.connection_label label_suffix
  in
  let analyze_label =
    Printf.sprintf "lsp-analyze-%s/%s" t.connection_label label_suffix
  in
  (* Spawn both EC subprocesses with [~cwd:project_root] so EC's
     [easycrypt.project] upward walk picks up the project's load
     paths (idirs, provers, etc.). UPSTREAM § 14′. *)
  let proof_state =
    Proof_state.create ~cwd:(Some project_root) ~sw ~primary_label
  in
  let analyze =
    Ec_llm_session.start_in_dir ~cwd:project_root ~sw ~label:analyze_label
  in
  { proof_state; analyze; project_root }

let entry_for (t : t) ~(sw : Eio.Switch.t) ~(uri : string) : entry option =
  if t.closed then None
  else
    match resolve_project_root t ~uri with
    | None -> None
    | Some project_root ->
      match Hashtbl.find_opt t.sessions project_root with
      | Some e -> Some e
      | None ->
        let e = spawn_entry t ~sw ~project_root in
        Hashtbl.replace t.sessions project_root e;
        Some e

let proof_state_for t ~sw ~uri =
  match entry_for t ~sw ~uri with
  | Some e -> e.proof_state
  | None ->
    failwith
      (Printf.sprintf
         "Session_manager.proof_state_for: cannot resolve URI %s \
          (manager closed or unparsable URI)" uri)

let analyze_session_for t ~sw ~uri =
  match entry_for t ~sw ~uri with
  | Some e -> e.analyze
  | None ->
    failwith
      (Printf.sprintf
         "Session_manager.analyze_session_for: cannot resolve URI %s \
          (manager closed or unparsable URI)" uri)

(* ---------------- Cancel + invalidate -------------------------- *)

let cancel_in_flight t ~uri =
  match resolve_project_root t ~uri with
  | None -> ()
  | Some project_root ->
    match Hashtbl.find_opt t.sessions project_root with
    | None -> ()
    | Some e -> Proof_state.cancel_in_flight e.proof_state

let close_entry (e : entry) : unit =
  (try Proof_state.close e.proof_state with _ -> ());
  (try Ec_llm_session.close e.analyze with _ -> ())

let invalidate_project t ~project_root =
  let canon = canonicalize project_root in
  match Hashtbl.find_opt t.sessions canon with
  | None -> ()
  | Some e ->
    Hashtbl.remove t.sessions canon;
    close_entry e;
    (* Drop URI cache entries pointing at this root so re-discovery
       picks up any [easycrypt.project] move/rename. *)
    let to_drop =
      Hashtbl.fold
        (fun uri root acc -> if root = canon then uri :: acc else acc)
        t.uri_to_root []
    in
    List.iter (Hashtbl.remove t.uri_to_root) to_drop

let close t =
  if not t.closed then begin
    t.closed <- true;
    Hashtbl.iter (fun _ e -> close_entry e) t.sessions;
    Hashtbl.clear t.sessions;
    Hashtbl.clear t.uri_to_root
  end
