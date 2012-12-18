(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type ppdebug = {
  ppindent : bool list;
  ppstream : out_channel;
}

(* -------------------------------------------------------------------- *)
let ppup pp b = { pp with ppindent = b :: pp.ppindent }

(* -------------------------------------------------------------------- *)
let ppindent bs =
  match bs with
  | []      -> ""
  | b :: bs -> begin
    let b  = if b then "`-" else "+-" in
    let bs = List.map (fun b -> if b then "  " else "| ") bs in
      String.concat "" (List.rev (b :: bs))
  end

(* -------------------------------------------------------------------- *)
let initial =
  { ppindent = [];
    ppstream = stderr; }

(* -------------------------------------------------------------------- *)
let onseq (pp : ppdebug) ?extra (txt : string) seq =
  let rec aux first =
    let next = Stream.next_opt seq in
    let pp   = ppup pp (next = None) in
      first pp; oiter next aux
  in

  let txt =
    match extra with
    | None -> txt
    | Some extra -> Printf.sprintf "%s (%s)" txt extra
  in
    Printf.fprintf pp.ppstream "%s%s\n%!"
      (ppindent pp.ppindent)
      txt;
    oiter (Stream.next_opt seq) aux

(* -------------------------------------------------------------------- *)
let onhseq (pp : ppdebug) ?extra (txt : string) cb seq =
  let next (i : int) =
    match Stream.next_opt seq with
    | None   -> None
    | Some x -> Some (cb^~ x)
  in
    onseq pp ?extra txt (Stream.from next)

(* -------------------------------------------------------------------- *)
let onhlist (pp : ppdebug) ?extra (txt : string) cb xs =
  onhseq pp ?extra txt cb (Stream.of_list xs)

(* -------------------------------------------------------------------- *)
let single (pp : ppdebug) ?extra (txt : string) =
  onseq pp ?extra txt (Stream.of_list [])
