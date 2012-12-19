(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type ppdebug = {
  ppindent : (bool * int option) list;
  ppstream : out_channel;
  ppmode   : [`ATree];
}

(* -------------------------------------------------------------------- *)
let ppup pp ?enum b =
  { pp with ppindent = (b, enum) :: pp.ppindent }

(* -------------------------------------------------------------------- *)
let initial =
  { ppindent = []; ppstream = stderr; ppmode = `ATree; }

(* -------------------------------------------------------------------- *)
module ATree = struct
  (* ------------------------------------------------------------------ *)
  let ppidxwd = 2

  (* ------------------------------------------------------------------ *)
  let ppindent =
    let prefix p (b, i) = 
      let prefix =
        match p, b with
        | true , false -> "+-"
        | true , true  -> "`-"
        | false, false -> "| "
        | false, true  -> "  "
      and postfix =
        match p, i with
        | true , None   -> ""
        | true , Some i -> Printf.sprintf "[%.*d] " ppidxwd i
        | false, None   -> ""
        | false, Some _ -> String.make (3+ppidxwd) ' '
      in
        prefix ^ postfix
    in
      fun bs ->
        match bs with
        | [] -> ""
        | (b, i) :: bs -> begin
            let b  = prefix true (b, i)
            and bs = List.map (prefix false) bs in
              String.concat "" (List.rev (b :: bs))
        end

  (* ------------------------------------------------------------------ *)
  let onseq (pp : ppdebug) ?(enum = false) ?extra (txt : string) seq =
    let rec aux first =
      let next = Stream.next_opt seq in
      let enum = if enum then Some ((Stream.count seq) - 1) else None in
      let pp   = ppup pp ?enum (next = None) in
        first pp; oiter next aux
    in
  
    let txt =
      match extra with
      | None -> txt
      | Some extra -> Printf.sprintf "%s (%s)" txt extra
    in
      Printf.fprintf pp.ppstream "%s%s\n%!"
        (ppindent pp.ppindent) txt;
      oiter (Stream.next_opt seq) aux
end

(* -------------------------------------------------------------------- *)
let onseq (pp : ppdebug) ?(enum = false) ?extra (txt : string) seq =
  match pp.ppmode with
  | `ATree -> ATree.onseq pp ~enum ?extra txt seq

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
