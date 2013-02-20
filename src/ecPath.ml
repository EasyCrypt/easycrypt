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

(* -------------------------------------------------------------------- *)
type mcpath = {
  mcp_node : mcpath_desc;
  mcp_tag  : int;
}

and mcpath_desc =
| MCtop of mcsymbol
| MCDot of mcpath * mcsymbol

and mcsymbol = symbol * mcpath list

let mcp_equal (p : mcpath) (q : mcpath) = (p == q)
let mcp_hash  (p : mcpath) = p.mcp_tag

module Hsmcpath = Why3.Hashcons.Make(struct 
  type t = mcpath

  let equal_mcsymbol (id1, l1) (id2, l2) =
       EcSymbols.equal id1 id2
    && (List.length l1 == List.length l2)
    && List.for_all2 mcp_equal l1 l2

  let equal_node p1 p2 = 
    match p1, p2 with
    | MCtop id1, MCtop id2 ->
        equal_mcsymbol id1 id2

    | MCDot (p1, id1), MCDot(p2, id2) ->
        equal_mcsymbol id1 id2 && mcp_equal p1 p2

    | _, _ -> false

  let equal p1 p2 = equal_node p1.mcp_node p2.mcp_node

  let rec hash p = 
    match p.mcp_node with
    | MCtop id ->
        hash_mcsymbol id

    | MCDot (p, id) ->
        Why3.Hashcons.combine p.mcp_tag (hash_mcsymbol id)

  and hash_mcsymbol (id, p) =
    Why3.Hashcons.combine_list
      (fun p -> p.mcp_tag) (Hashtbl.hash id) p

  let tag n p = { p with mcp_tag = n }
end)

module MCPath = MakeMSH (struct
  type t  = mcpath
  let tag = mcp_hash
end)

module Smcp = MCPath.S
module Mmcp = MCPath.M
module Hmcp = MCPath.H

let mcp_compare (p1 : mcpath) (p2 : mcpath) =
  mcp_hash p1 - mcp_hash p2

let mk_mcpath node =
  Hsmcpath.hashcons { mcp_node = node; mcp_tag = -1; }

let mctop id      = mk_mcpath (MCtop id)
let mcdot (p, id) = mk_mcpath (MCDot (p, id))

(* -------------------------------------------------------------------- *)
type mpath = {
  mp_node : mpath_desc;
  mp_tag  : int;
}

and mpath_desc =
| MCIdent of EcIdent.t
| MCPath  of mcpath

let mp_equal (p : mpath) (q : mpath) = (p == q)
let mp_hash  (p : mpath) = p.mp_tag

module Hsmpath = Why3.Hashcons.Make(struct 
  type t = mpath

  let equal_node p1 p2 = 
    match p1, p2 with
    | MCIdent id1, MCIdent id2 ->
        EcIdent.id_equal id1 id2

    | MCPath p1, MCPath p2 ->
        mcp_equal p1 p2

    | _, _ -> false

  let equal p1 p2 = equal_node p1.mp_node p2.mp_node

  let hash p = 
    match p.mp_node with
    | MCIdent id ->
        Hashtbl.hash id

    | MCPath p ->
       mcp_hash p
          
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

let mpident id = mk_mpath (MCIdent id)
let mppath  p  = mk_mpath (MCPath p)

(* -------------------------------------------------------------------- *)
type xpath = {
  xp_node : xpath_desc;
  xp_tag  : int;
}

and xpath_desc = {
  xp_context : mcpath;
  xp_symbol  : symbol;
}

(* -------------------------------------------------------------------- *)
let xp_equal (p : xpath) (q : xpath) = (p == q)
let xp_hash  (p : xpath) = p.xp_tag

module Hsxpath = Why3.Hashcons.Make(struct 
  type t = xpath

  let equal_node p1 p2 = 
       EcSymbols.equal p1.xp_symbol p2.xp_symbol
    && mcp_equal p1.xp_context p2.xp_context

  let equal p1 p2 = equal_node p1.xp_node p2.xp_node

  let hash p =
    let p = p.xp_node in
      Why3.Hashcons.combine
        (mcp_hash p.xp_context) (Hashtbl.hash p.xp_symbol)
          
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
