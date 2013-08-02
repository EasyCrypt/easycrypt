(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type dnode = [`Node of string * dnode list]

let dnode (s : string) (c : dnode list) = `Node (s, c)


let dleaf x =
  Printf.ksprintf (fun s -> `Node (s, [])) x

(* -------------------------------------------------------------------- *)
type ppdebug = {
  ppindent : (bool * int option) list;
  ppstream : out_channel;
  ppmode   : [`ATree | `Xml];
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
        first pp; next |> oiter aux
    in
  
    let txt =
      match extra with
      | None -> txt
      | Some extra -> Printf.sprintf "%s (%s)" txt extra
    in
      Printf.fprintf pp.ppstream "%s%s\n%!"
        (ppindent pp.ppindent) txt;
       Stream.next_opt seq |> oiter aux
end

(* -------------------------------------------------------------------- *)
module Xml = struct
  let escape s =
    let buf = Buffer.create (String.length s) in
      String.iter
        (function
         | '"'  -> Buffer.add_string buf "&quot;"
         | '\'' -> Buffer.add_string buf "&apos;"
         | '<'  -> Buffer.add_string buf "&lt;"
         | '>'  -> Buffer.add_string buf "&gt;"
         | '&'  -> Buffer.add_string buf "&amp;"
         | c    -> Buffer.add_char buf c)
        s;
      Buffer.contents buf

  (* ------------------------------------------------------------------ *)
  let onseq (pp : ppdebug) ?(enum = false) ?extra (txt : string) seq =
    let rec aux first =
      let next = Stream.next_opt seq in
      let enum = if enum then Some ((Stream.count seq) - 1) else None in
      let pp   = ppup pp ?enum (next = None) in
        first pp; next |> oiter aux
    in
  
    let txt =
      match extra with
      | None -> txt
      | Some extra -> Printf.sprintf "%s (%s)" txt extra
    and indent = 2 * (List.length pp.ppindent) in
      Printf.fprintf pp.ppstream
        "%.*s<node data=\"%s\">\n%!" indent "" (escape txt);
      Stream.next_opt seq |> oiter aux;
      Printf.fprintf pp.ppstream "%.*s</node>\n%!" indent "";
end

(* -------------------------------------------------------------------- *)
let onseq (pp : ppdebug) ?(enum = false) ?extra (txt : string) seq =
  match pp.ppmode with
  | `ATree -> ATree.onseq pp ~enum ?extra txt seq
  | `Xml   -> Xml  .onseq pp ~enum ?extra txt seq

(* -------------------------------------------------------------------- *)
let onhseq (pp : ppdebug) ?enum ?extra (txt : string) cb seq =
  let next (_i : int) =
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

(* -------------------------------------------------------------------- *)
let rec ondnode (pp : ppdebug) (node : dnode) =
  let `Node (txt, ns) = node in
    onhseq pp txt ondnode (Stream.of_list ns)
