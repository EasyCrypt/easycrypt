(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcMatching
open EcGenRegexp

(* -------------------------------------------------------------------- *)
let default_start_name = "$start"
let default_end_name = "$end"
let default_name = "$default"

(*-------------------------------------------------------------------- *)
let any_stmt  = Repeat (Any, (None, None), `Greedy)
let any_block = (With_anchor, With_anchor), IM_Any

let set_default_name pattern = Named (pattern, default_name)

let default_start_without_anchor =
  Named (Repeat (Any, (None, None), `Lazy), default_start_name)

let default_end_without_anchor =
  Named (Repeat (Any, (None, None), `Greedy), default_end_name)

(*-------------------------------------------------------------------- *)
let default_stmt x = odfl any_stmt x

(*-------------------------------------------------------------------- *)
let add_default_names (at_begin, at_end) pattern =
  let pattern_sequence = [ set_default_name pattern ] in
  let pattern_sequence =
    if   at_begin = With_anchor
    then Named (Seq [], default_start_name) :: pattern_sequence
    else default_start_without_anchor       :: pattern_sequence in
  let pattern_sequence =
    if at_end = With_anchor
    then pattern_sequence @ [Named (Seq [], default_end_name)]
    else pattern_sequence @ [default_end_without_anchor] in
  pattern_sequence

(*-------------------------------------------------------------------- *)
let add_anchors (at_begin, at_end) pattern_sequence =
  let pattern =
    if at_begin = With_anchor then Anchor Start :: pattern_sequence
    else pattern_sequence in
  if at_end = With_anchor then pattern @ [Anchor End]
  else pattern

(*-------------------------------------------------------------------- *)
let rec trans_block (anchors, pattern_parsed) =
  let pattern = trans_stmt pattern_parsed in
  match pattern with
  | Seq ps -> Seq (add_anchors anchors ps)
  | _      -> Seq (add_anchors anchors [ pattern ])

(*-------------------------------------------------------------------- *)
and trans_stmt = function
  | IM_Any      -> any_stmt
  | IM_Parens r -> trans_stmt r
  | IM_Assign   -> Base RAssign
  | IM_Sample   -> Base RSample
  | IM_Call     -> Base RCall

  | IM_If (bt, bf)  ->
     let branch_true  = trans_block (odfl any_block bt) in
     let branch_false = trans_block (odfl any_block bf) in
     Base (RIf (branch_true, branch_false))

  | IM_While b     ->
     let branch = odfl any_block b in
     let branch = trans_block branch in
     Base (RWhile branch)

  | IM_Named (s, r) ->
     let r = odfl IM_Any r in
     let r = trans_stmt r in
     Named (r, EcLocation.unloc s)

  | IM_Repeat ((a,b),c) ->
     trans_repeat ((a,b),c)

  | IM_Seq l ->
     Seq (List.map trans_stmt l)

  | IM_Choice l    ->
     Choice (List.map trans_stmt l)

(*-------------------------------------------------------------------- *)
and trans_repeat ((is_greedy, repeat_kind), r) =
  match r with
  | IM_Any -> begin
      let greed = if is_greedy then `Greedy else `Lazy in
      match repeat_kind with
      | IM_R_Repeat info -> Repeat (Any, info, greed)
      | IM_R_May    info -> Repeat (Any, (None, info), greed)
    end

  | IM_Named (s, r) ->
     let r = odfl IM_Any r in
     let r = trans_repeat ((is_greedy, repeat_kind), r) in
     Named (r, EcLocation.unloc s)

  | _ -> begin
      let r = trans_stmt r in
      let greed = if is_greedy then `Greedy else `Lazy in
      match repeat_kind with
      | IM_R_Repeat info -> Repeat (r, info, greed)
      | IM_R_May    info -> Repeat (r, (None, info), greed)
    end

(*-------------------------------------------------------------------- *)
let trans_block (anchors, pattern_parsed) =
  let pattern = trans_stmt pattern_parsed in
  Seq (add_anchors anchors (add_default_names anchors pattern))
