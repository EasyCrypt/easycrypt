(* -------------------------------------------------------------------- *)
open Utils
open Symbols

let s_equal : symbol -> symbol -> bool = (=)

type path =
  | Pident of symbol
  | Pqname of symbol * path

let to_list = 
  let rec aux l = function
  | Pident s -> s::l
  | Pqname(s,p) -> aux (s::l) p in
  aux []

let rec create (path : string) =
  match try_nf (fun () -> String.index path '.') with
    | None   -> Pident path
    | Some i ->
      let qname = String.sub path 0 i in
      let path  = String.sub path i (String.length path - i) in
        Pqname (qname, create path)

let toqsymbol =
  let rec toqsymbol scope = function
    | Pident x       -> (List.rev scope, x)
    | Pqname (nm, p) -> toqsymbol (nm :: scope) p
  in
    fun (p : path) -> toqsymbol [] p

let path_equal = (=)

module Mp = Map.Make (struct type t = path let compare = compare end)


type subst_path = symbol list * symbol list (* second in reverse order *)

let mk_subst pre npre = List.rev (to_list pre), to_list npre

let extend_path l p = 
  List.fold_left (fun p s -> Pqname(s, p)) p l 

let subst_path (pre, npre) p = 
  let rec aux pre p1 = 
    match pre, p1 with
    | [], _ -> extend_path npre p1
    | [s1], Pident s2 when s_equal s1 s2 ->
        begin match npre with
        | s :: npre -> extend_path npre (Pident s)
        | _ -> assert false
        end
    | s1 :: pre, Pqname(s2, p1) when s_equal s1 s2 -> aux pre p1 
    | _, _ -> p in
  aux pre p



