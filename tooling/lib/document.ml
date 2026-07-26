type sentence = {
  id      : Sentence_id.t;
  parsed  : Ec_llm_session.parsed_sentence;
}

type t = {
  uri       : string;
  version   : int;
  source    : string;
  sentences : sentence list;
}

let sentence_of_parsed (p : Ec_llm_session.parsed_sentence) : sentence =
  { id = Sentence_id.of_source p.src; parsed = p }

let parse session ~uri ~version ~source =
  match Ec_llm_session.parse_source session source with
  | Error e -> Error e
  | Ok (ps, _perr) ->
    Ok {
      uri;
      version;
      source;
      sentences = List.map sentence_of_parsed ps;
    }

type diff = {
  unchanged_prefix : sentence list;
  removed          : sentence list;
  added            : sentence list;
}

let diff ~old ~new_ =
  let rec split_prefix acc o n =
    match o, n with
    | a :: at, b :: bt when Sentence_id.equal a.id b.id ->
      split_prefix (a :: acc) at bt
    | _ -> (List.rev acc, o, n)
  in
  let unchanged_prefix, removed, added = split_prefix [] old.sentences new_.sentences in
  { unchanged_prefix; removed; added }
