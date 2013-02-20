(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type path = {
  p_node : path_desc;
  p_tag  : int
}

and path_desc =
| Pident of symbol
| Pqname of path * symbol

(* -------------------------------------------------------------------- *)
let p_equal (p : path) (q : path) = (p == q)
let p_hash  (p : path) = p.p_tag

module Hspath = Why3.Hashcons.Make(struct 
  type t = path

  let equal_node p1 p2 = 
    match p1, p2 with
    | Pident id1, Pident id2 ->
        EcSymbols.equal id1 id2

    | Pqname (p1, id1), Pqname(p2, id2) -> 
        EcSymbols.equal id1 id2 && p_equal p1 p2

    | _, _ -> false

  let equal p1 p2 = equal_node p1.p_node p2.p_node

  let hash p = 
    match p.p_node with
    | Pident id ->
        Hashtbl.hash id

    | Pqname (p, id) ->
        Why3.Hashcons.combine p.p_tag (Hashtbl.hash id)
          
  let tag n p = { p with p_tag = n }
end)

module Path = MakeMSH (struct
  type t  = path
  let tag = p_hash
end)

module Sp = Path.S
module Mp = Path.M
module Hp = Path.H

let p_compare (p1 : path) (p2 : path) =
  p_hash p1 - p_hash p2

let mk_path node =
  Hspath.hashcons { p_node = node; p_tag = -1; }

let pident id      = mk_path (Pident id)
let pqname (p, id) = mk_path (Pqname(p,id))

let rec p_tostring (p : path) =
  match p.p_node with
  | Pident x ->
      Printf.sprintf "%s" x
  | Pqname (p, x) ->
      Printf.sprintf "%s.%s" (p_tostring p) x

let p_tolist =
  let rec aux l p = 
    match p.p_node with 
    | Pident x      -> x :: l
    | Pqname (p, x) -> aux (x :: l) p in
  aux []

let p_toqsymbol (p : path) =
  match p.p_node with
  | Pident x      -> ([], x)
  | Pqname (p, x) -> (p_tolist p, x)

let p_prefix (p : path) =
  match p.p_node with 
  | Pident _ -> None
  | Pqname (p, _) -> Some p

let p_basename (p : path) =
  match p.p_node with
  | Pident x      -> x
  | Pqname (_, x) -> x

let p_extend (p : path option) (x : symbol) =
  match p with
  | None   -> pident x
  | Some p -> pqname (p, x)

(* -------------------------------------------------------------------- *)
type mpath = {
  mp_node : mpath_desc;
  mp_tag  : int;
}

and mpath_desc =
| MCtop of topmcsymbol
| MCDot of mpath * mcsymbol

and mcsymbol    = symbol    * mpath list
and topmcsymbol = topsymbol * mpath list

and topsymbol =
| TopIdent  of EcIdent.t
| TopSymbol of symbol

let mp_equal (p : mpath) (q : mpath) = (p == q)
let mp_hash  (p : mpath) = p.mp_tag

module Hsmpath = Why3.Hashcons.Make(struct 
  type t = mpath

  let rec equal_mcsymbol
      ((id1, l1) : mcsymbol) ((id2, l2) : mcsymbol)
    =
       EcSymbols.equal id1 id2
    && (List.length l1 == List.length l2)
    && List.for_all2 mp_equal l1 l2

  and equal_topmcsymbol
      ((id1, l1) : topmcsymbol) ((id2, l2) : topmcsymbol)
    =
       equal_topsymbol id1 id2
    && (List.length l1 == List.length l2)
    && List.for_all2 mp_equal l1 l2

  and equal_topsymbol id1 id2 =
    match id1, id2 with
    | TopIdent  id1, TopIdent  id2 -> EcIdent.id_equal id1 id2
    | TopSymbol id1, TopSymbol id2 -> EcSymbols.equal id1 id2
    | _            , _             -> false

  let equal_node p1 p2 = 
    match p1, p2 with
    | MCtop id1, MCtop id2 ->
        equal_topmcsymbol id1 id2

    | MCDot (p1, id1), MCDot(p2, id2) ->
        equal_mcsymbol id1 id2 && mp_equal p1 p2

    | _, _ -> false

  let equal p1 p2 = equal_node p1.mp_node p2.mp_node

  let rec hash p = 
    match p.mp_node with
    | MCtop id ->
        hash_topmcsymbol id

    | MCDot (p, id) ->
        Why3.Hashcons.combine p.mp_tag (hash_mcsymbol id)

  and hash_mcsymbol ((id, p) : mcsymbol) =
    Why3.Hashcons.combine_list
      (fun p -> p.mp_tag) (Hashtbl.hash id) p

  and hash_topmcsymbol ((id, p) : topmcsymbol) =
    Why3.Hashcons.combine_list
      (fun p -> p.mp_tag) (Hashtbl.hash id) p

  let tag n p = { p with mp_tag = n }
end)

module MPath = MakeMSH (struct
  type t  = mpath
  let tag = mp_hash
end)

module Smp = MPath.S
module Mmp = MPath.M
module Hmp = MPath.H

let mp_compare (p1 : mpath) (p2 : mpath) =
  mp_hash p1 - mp_hash p2

let mk_mpath node =
  Hsmpath.hashcons { mp_node = node; mp_tag = -1; }

let mctop id      = mk_mpath (MCtop id)
let mcdot (p, id) = mk_mpath (MCDot (p, id))
let mcident id    = mctop (TopIdent id, [])

let rec mpath_of_path (p : path) =
  match p.p_node with
  | Pident x      -> mctop (TopSymbol x, [])
  | Pqname (p, x) -> mcdot (mpath_of_path p, (x, []))

let rec mp_tostring (p : mpath) =
  match p.mp_node with
  | MCtop id ->
      topmcsymbol_tostring id

  | MCDot (p, id) ->
      Printf.sprintf "%s.%s" (mp_tostring p) (mcsymbol_tostring id)

and mcsymbol_tostring (id, args) =
  topmcsymbol_tostring (TopSymbol id, args)

and topmcsymbol_tostring (id, args) =
  let id =
    match id with
    | TopSymbol id -> id
    | TopIdent  id -> EcIdent.tostring id
  in
    match args with
    | [] -> id
    | _  -> Printf.sprintf "%s(%s)" id
              (String.concat ", " (List.map mp_tostring args))

(* -------------------------------------------------------------------- *)
type xpath = {
  xp_node : xpath_desc;
  xp_tag  : int;
}

and xpath_desc = {
  xp_context : mpath;
  xp_symbol  : symbol;
}

(* -------------------------------------------------------------------- *)
let xp_equal (p : xpath) (q : xpath) = (p == q)
let xp_hash  (p : xpath) = p.xp_tag

module Hsxpath = Why3.Hashcons.Make(struct 
  type t = xpath

  let equal_node p1 p2 = 
       EcSymbols.equal p1.xp_symbol p2.xp_symbol
    && mp_equal p1.xp_context p2.xp_context

  let equal p1 p2 = equal_node p1.xp_node p2.xp_node

  let hash p =
    let p = p.xp_node in
      Why3.Hashcons.combine
        (mp_hash p.xp_context) (Hashtbl.hash p.xp_symbol)
          
  let tag n p = { p with xp_tag = n }
end)

module XPath = MakeMSH (struct
  type t  = xpath
  let tag = xp_hash
end)

module Sxp = XPath.S
module Mxp = XPath.M
module Hxp = XPath.H

let xp_compare (p1 : xpath) (p2 : xpath) =
  xp_hash p1 - xp_hash p2

let mk_xpath node =
  Hsxpath.hashcons { xp_node = node; xp_tag = -1; }

let xpath ctxt id = mk_xpath {
  xp_context = ctxt;
  xp_symbol  = id;
}

let xp_tostring (p : xpath) =
  let p = p.xp_node in
    Printf.sprintf "%s.%s"
      (mp_tostring p.xp_context) p.xp_symbol

let xp_basename x = x. xp_node.xp_symbol
