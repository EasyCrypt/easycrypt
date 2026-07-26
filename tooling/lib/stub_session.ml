(** No-op [Session.BACKEND] for composition smoke and unit tests.
    Every [exec] succeeds, advances a local uuid counter, and returns a
    synthetic sentence id derived from the uuid. Cancellation marks the
    session as cancelled; subsequent [exec]s on a cancelled session
    yield [Error.Cancelled]. *)

type t = {
  label : string;
  mutable uuid : int;
  mutable cancelled : bool;
}

let start ~sw:_ ~label = { label; uuid = 0; cancelled = false }

let exec t ~corr:_ ~sentence_class ~source:_ =
  if t.cancelled then Error (Error.Cancelled { reason = "session killed" })
  else
    match sentence_class with
    | `Directive ->
        (* No uuid advance. *)
        Ok
          Session.{
            sentence_id = Sentence_id.stub_of_int t.uuid;
            replied_uuid = t.uuid;
            notices = [];
            restarted = false;
            output = "";
          }
    | `Executable | `Doc_comment ->
        t.uuid <- t.uuid + 1;
        Ok
          Session.{
            sentence_id = Sentence_id.stub_of_int t.uuid;
            replied_uuid = t.uuid;
            notices = [];
            restarted = false;
            output = "";
          }

let revert_to t sid =
  (* Parse the stub id to get the target uuid. *)
  let s = Sentence_id.to_string sid in
  match String.split_on_char '-' s with
  | [ "stub"; n ] -> (
      try
        t.uuid <- int_of_string n;
        Ok ()
      with Failure _ ->
        Error (Error.Unknown_sentence_id { id = s }))
  | _ -> Error (Error.Unknown_sentence_id { id = s })

let goals t =
  Ok (Printf.sprintf "stub goals at uuid %d (session %s)" t.uuid t.label)

let cancel t ~corr:_ = t.cancelled <- true

let close _t = ()
