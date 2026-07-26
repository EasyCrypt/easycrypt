(** Generic fuzzy-subsequence filter for pickers.

    [filter query items ~key] keeps items whose [key] string contains
    the characters of [query] in order (not necessarily contiguous),
    ranked by a simple score that prefers contiguous matches, earlier
    matches, and shorter keys. Case-insensitive.

    Used by the semantic-TUI's apply-lemma and apply-hyp pickers and
    by anything else that needs live filter-as-you-type over a
    fixed list. *)

(** A scored match. [score] is higher = better; [indices] are the
    positions in the key where query chars landed — useful for
    highlighting in the UI. *)
type 'a match_result = {
  item    : 'a;
  score   : int;
  indices : int list;
}

val filter :
  string ->
  'a list ->
  key:('a -> string) ->
  'a match_result list
