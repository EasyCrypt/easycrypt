(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type ppdebug = {
  ppindent : bool list;
  ppstream : out_channel;
  ppenum   : int option;
}

(* -------------------------------------------------------------------- *)
let ppup pp ?enum b =
  { ppindent = b :: pp.ppindent;
    ppstream = pp.ppstream     ;
    ppenum   = enum            ; }

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
  { ppindent = []    ;
    ppstream = stderr;
    ppenum   = None  ; }

(* -------------------------------------------------------------------- *)
let onseq (pp : ppdebug) ?(enum = false) ?extra (txt : string) seq =
  let rec aux first =
    let next = Stream.next_opt seq in
    let enum = if enum then Some (Stream.count seq) else None in
    let pp   = ppup pp ?enum (next = None) in
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
let onhseq (pp : ppdebug) ?enum ?extra (txt : string) cb seq =
  let next (i : int) =
    match Stream.next_opt seq with
    | None   -> None
    | Some x -> Some (cb^~ x)
  in
    onseq pp ?enum ?extra txt (Stream.from next)

(* -------------------------------------------------------------------- *)
let onhlist (pp : ppdebug) ?enum ?extra (txt : string) cb xs =
  onhseq pp ?enum ?extra txt cb (Stream.of_list xs)

(* -------------------------------------------------------------------- *)
let single (pp : ppdebug) ?extra (txt : string) =
  onseq pp ?extra txt (Stream.of_list [])
