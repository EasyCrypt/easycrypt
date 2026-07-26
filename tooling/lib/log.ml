type level = [ `Debug | `Info | `Warn | `Error ]

let level_to_string = function
  | `Debug -> "debug"
  | `Info  -> "info"
  | `Warn  -> "warn"
  | `Error -> "error"

let level_rank = function
  | `Debug -> 0
  | `Info  -> 1
  | `Warn  -> 2
  | `Error -> 3

type sink = string -> unit

type t = {
  mu       : Mutex.t;
  t0_ns    : int;
  min_rank : int;
  write    : sink;
}

let now_monotonic_ns () =
  int_of_float (Unix.gettimeofday () *. 1.0e9)

let make ?(level = `Info) (write : sink) : t =
  { mu = Mutex.create ();
    t0_ns = now_monotonic_ns ();
    min_rank = level_rank level;
    write }

let to_channel ?level oc =
  make ?level (fun line ->
    try
      output_string oc line;
      output_char oc '\n';
      flush oc
    with _ -> ())

let to_buffer ?level buf =
  make ?level (fun line ->
    Buffer.add_string buf line;
    Buffer.add_char buf '\n')

let devnull () = make ~level:`Error (fun _ -> ())

let g = ref (devnull ())
let configure t = g := t
let current () = !g

let emit t lvl ?corr msg =
  if level_rank lvl < t.min_rank then ()
  else begin
    let dt_micros = (now_monotonic_ns () - t.t0_ns) / 1_000 in
    let cid_field =
      match corr with
      | None -> `Null
      | Some c -> `String (Correlation.to_string c)
    in
    let line =
      Yojson.Safe.to_string (`Assoc [
        "t",     `Int dt_micros;
        "level", `String (level_to_string lvl);
        "corr",  cid_field;
        "msg",   `String msg;
      ])
    in
    Mutex.lock t.mu;
    (try t.write line with _ -> ());
    Mutex.unlock t.mu
  end

let log lvl ?corr fmt =
  Format.kasprintf (fun msg -> emit !g lvl ?corr msg) fmt

let debug ?corr fmt = log `Debug ?corr fmt
let info  ?corr fmt = log `Info  ?corr fmt
let warn  ?corr fmt = log `Warn  ?corr fmt
let err   ?corr fmt = log `Error ?corr fmt
