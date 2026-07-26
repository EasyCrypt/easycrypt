type 'a match_result = {
  item    : 'a;
  score   : int;
  indices : int list;
}

(* Greedy left-to-right match of [query]'s chars (lowercased) against
   [key]'s chars (lowercased). Returns (indices, score) on success
   where [indices] is the positions in key that matched each query
   char, and [score] is higher for better matches — contiguous runs
   get a bonus, earlier starts get a bonus, shorter keys get a
   bonus. Returns [None] if any query char can't be matched in
   order. *)
let score_match query key =
  let ql = String.length query in
  let kl = String.length key in
  if ql = 0 then Some ([], 100 - min 100 kl)
  else begin
    let lq c = Char.lowercase_ascii c in
    let indices = Array.make ql (-1) in
    let qi = ref 0 in
    let ki = ref 0 in
    while !qi < ql && !ki < kl do
      if lq query.[!qi] = lq key.[!ki] then begin
        indices.(!qi) <- !ki;
        incr qi;
      end;
      incr ki
    done;
    if !qi < ql then None
    else begin
      let contiguous_bonus =
        let r = ref 0 in
        for i = 1 to ql - 1 do
          if indices.(i) = indices.(i - 1) + 1 then r := !r + 5
        done;
        !r
      in
      let earliness_bonus =
        if ql > 0 then max 0 (50 - indices.(0)) else 0
      in
      let shortness_bonus = max 0 (50 - kl) in
      let score = contiguous_bonus + earliness_bonus + shortness_bonus in
      Some (Array.to_list indices, score)
    end
  end

let filter query items ~key =
  List.filter_map
    (fun item ->
       match score_match query (key item) with
       | None -> None
       | Some (indices, score) -> Some { item; score; indices })
    items
  |> List.sort (fun a b -> compare b.score a.score)
