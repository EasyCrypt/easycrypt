type t = {
  mu : Mutex.t;
  mutable settings : (string * Yojson.Safe.t) list;
}

let create () = { mu = Mutex.create (); settings = [] }

let with_lock t f =
  Mutex.lock t.mu;
  let r = try f () with e -> Mutex.unlock t.mu; raise e in
  Mutex.unlock t.mu;
  r

let set t key value =
  with_lock t (fun () ->
    t.settings <-
      (key, value) :: List.filter (fun (k, _) -> k <> key) t.settings)

let set_many t pairs =
  List.iter (fun (k, v) -> set t k v) pairs

let get_opt t key =
  with_lock t (fun () -> List.assoc_opt key t.settings)

let get_string t key default =
  match get_opt t key with
  | Some (`String s) -> s
  | _ -> default

let get_bool t key default =
  match get_opt t key with
  | Some (`Bool b) -> b
  | _ -> default

let get_int t key default =
  match get_opt t key with
  | Some (`Int i) -> i
  | _ -> default

let get_int_opt t key =
  match get_opt t key with
  | Some (`Int i) -> Some i
  | _ -> None

let file_mode t =
  match get_string t "proof.fileMode" "preservation" with
  | "realtime" -> `Realtime
  | _ -> `Preservation

let real_time_reload t =
  match get_string t "proof.realTimeReload" "instant" with
  | "prompt" -> `Prompt
  | _ -> `Instant

let cache_policy t =
  match get_string t "proof.cachePolicy" "lax" with
  | "strict" -> `Strict
  | _ -> `Lax

let goals_cache_budget_mb t = get_int t "proof.goalsCacheBudgetMB" 64

let recovery_strategy t =
  match get_string t "proof.recoveryStrategy" "halt" with
  | "best_effort_admit" -> `Best_effort_admit
  | _ -> `Halt

let auto_reconcile t = get_bool t "proof.autoReconcile" true
let debounce_ms t = get_int t "proof.debounceMs" 200
let max_exec_ms_per_sentence t = get_int_opt t "proof.maxExecMsPerSentence"
let speculation_enabled t = get_bool t "proof.speculation" true
let speculation_budget_ms t = get_int t "proof.speculationBudgetMs" 100

let bullet_semantics t =
  match get_string t "proof.bulletSemantics" "lenient" with
  | "strict" -> `Strict
  | "off" -> `Off
  | _ -> `Lenient

let g = ref (create ())
let configure t = g := t
let current () = !g
