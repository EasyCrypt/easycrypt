type event =
  | State_changed of {
      document_uri : string;
      cas : string;
      current_sentence : Sentence_id.t;
      seq : int;
      origin_correlation : Correlation.t option;
    }
  | Server_restarted of {
      document_uri : string;
      new_cas : string;
      reason : string;
      seq : int;
    }
  | Session_crashed of {
      label : string;
      exit_kind : string;
      seq : int;
    }

type snapshot = {
  cas : string;
  current_sentence : Sentence_id.t option;
  overlay_stack : string list;
}

type t = {
  publish : event -> unit;
  snapshot : unit -> snapshot;
  subscribe : (event -> unit) -> unit;
}

module type POINT = sig
  type state
  val publish : state -> event -> unit
  val snapshot : state -> snapshot
  val subscribe : state -> (event -> unit) -> unit
end

let of_impl
    (type a)
    (module M : POINT with type state = a)
    (state : a) : t =
  {
    publish = M.publish state;
    snapshot = (fun () -> M.snapshot state);
    subscribe = M.subscribe state;
  }
