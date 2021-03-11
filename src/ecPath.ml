(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
open EcIdent

(* -------------------------------------------------------------------- *)
type path = {
  p_node : path_node;
  p_tag  : int
}

and path_node =
| Psymbol of symbol
| Pqname  of path * symbol

(* -------------------------------------------------------------------- *)
let p_equal   = ((==) : path -> path -> bool)
let p_hash    = fun p -> p.p_tag
let p_compare = fun p1 p2 -> p_hash p1 - p_hash p2

module Hspath = Why3.Hashcons.Make (struct
  type t = path

  let equal_node p1 p2 =
    match p1, p2 with
    | Psymbol id1, Psymbol id2 ->
        sym_equal id1 id2
    | Pqname (p1, id1), Pqname(p2, id2) ->
        sym_equal id1 id2 && p_equal p1 p2
    | _ -> false

  let equal p1 p2 = equal_node p1.p_node p2.p_node

  let hash p =
    match p.p_node with
    | Psymbol id    -> Hashtbl.hash id
    | Pqname (p,id) -> Why3.Hashcons.combine p.p_tag (Hashtbl.hash id)

  let tag n p = { p with p_tag = n }
end)

module Path = MakeMSH (struct
  type t  = path
  let tag = p_hash
end)

let rec p_ntr_compare (p1 : path) (p2 : path) =
  match p1.p_node, p2.p_node with
  | Psymbol _, Pqname  _ -> -1
  | Pqname  _, Psymbol _ -> +1

  | Psymbol x1, Psymbol x2 ->
       String.compare x1 x2

  | Pqname (p1, x1), Pqname (p2, x2) -> begin
      match p_ntr_compare p1 p2 with
      | 0 -> String.compare x1 x2
      | n -> n
    end

(* -------------------------------------------------------------------- *)
module Mp = Path.M
module Hp = Path.H

module Sp = struct
  include Path.S

  let ntr_elements s =
    List.ksort ~key:identity ~cmp:p_ntr_compare (elements s)
end

(* -------------------------------------------------------------------- *)
let mk_path node =
  Hspath.hashcons { p_node = node; p_tag = -1; }

let psymbol id   = mk_path (Psymbol id)
let pqname  p id = mk_path (Pqname(p,id))

let rec pappend p1 p2 =
  match p2.p_node with
  | Psymbol id -> pqname p1 id
  | Pqname(p2,id) -> pqname (pappend p1 p2) id

let pqoname p id =
  match p with
  | None   -> psymbol id
  | Some p -> pqname p id

(* -------------------------------------------------------------------- *)
let rec tostring p =
  match p.p_node with
  | Psymbol x    -> x
  | Pqname (p,x) -> Printf.sprintf "%s.%s" (tostring p) x

let tolist =
  let rec aux l p =
    match p.p_node with
    | Psymbol x     -> x :: l
    | Pqname (p, x) -> aux (x :: l) p in
  aux []

let toqsymbol (p : path) =
  match p.p_node with
  | Psymbol x     -> ([], x)
  | Pqname (p, x) -> (tolist p, x)

let fromqsymbol ((nm, x) : qsymbol) =
  pqoname
    (List.fold_left
       (fun p x -> Some (pqoname p x)) None nm)
    x

let basename p =
  match p.p_node with
  | Psymbol x     -> x
  | Pqname (_, x) -> x

let extend p s =
  List.fold_left pqname p s

let prefix p =
  match p.p_node with
  | Psymbol _ -> None
  | Pqname (p, _) -> Some p

let rec getprefix_r acc p q =
  match p_equal p q with
  | true  -> Some acc
  | false ->
      match q.p_node with
      | Psymbol _     -> None
      | Pqname (q, x) -> getprefix_r (x::acc) p q

let getprefix p q = getprefix_r [] p q

let isprefix p q =
  match getprefix p q with
  | None   -> false
  | Some _ -> true

let rec rootname p =
  match p.p_node with
  | Psymbol x     -> x
  | Pqname (p, _) -> rootname p

let rec p_size p =
  match p.p_node with
  | Psymbol _     -> 1
  | Pqname (p, _) -> 1 + (p_size p)

(* -------------------------------------------------------------------- *)
type mpath = {
  m_top  : mpath_top;
  m_args : mpath list;
  m_tag  : int;
}

and mpath_top =
[ | `Local of ident
  | `Concrete of path * path option ]

let m_equal   = ((==) : mpath -> mpath -> bool)

let mt_equal mt1 mt2 =
  match mt1, mt2 with
  | `Local id1, `Local id2 -> EcIdent.id_equal id1 id2
  | `Concrete(p1, o1), `Concrete(p2, o2) ->
    p_equal p1 p2 && oall2 p_equal o1 o2
  | _, _ -> false

let m_hash    = fun p -> p.m_tag
let m_compare = fun p1 p2 -> m_hash p1 - m_hash p2

module Hsmpath = Why3.Hashcons.Make (struct
  type t = mpath

  let equal m1 m2 =
    mt_equal m1.m_top m2.m_top  && List.all2 m_equal m1.m_args m2.m_args

  let hash m =
    let hash =
      match m.m_top with
      | `Local id -> EcIdent.id_hash id
      | `Concrete(p, o) ->
        o |> ofold
              (fun s h -> Why3.Hashcons.combine h (p_hash s))
              (p_hash p)
    in
    Why3.Hashcons.combine_list m_hash hash m.m_args

  let tag n p = { p with m_tag = n }
end)

module MPath = MakeMSH (struct
  type t  = mpath
  let tag = m_hash
end)

let m_top_ntr_compare (mt1 : mpath_top) (mt2 : mpath_top) =
  match mt1, mt2 with
  | `Local    _, `Concrete _ -> -1
  | `Concrete _, `Local    _ -> +1

  | `Local id1, `Local id2 ->
       id_ntr_compare id1 id2

  | `Concrete (p1, op1), `Concrete (p2, op2) -> begin
       match p_ntr_compare p1 p2 with
       | 0 -> ocompare p_ntr_compare op1 op2
       | n -> n
end

let rec m_ntr_compare (m1 : mpath) (m2 : mpath) =
  match m_top_ntr_compare m1.m_top m2.m_top with
  | 0 -> List.compare m_ntr_compare m1.m_args m2.m_args
  | n -> n

(* -------------------------------------------------------------------- *)
module Mm = MPath.M
module Hm = MPath.H

module Sm = struct
  include MPath.S

  let ntr_elements s =
    List.ksort ~key:identity ~cmp:m_ntr_compare (elements s)
end

(* -------------------------------------------------------------------- *)
let mpath p args =
  Hsmpath.hashcons { m_top = p; m_args = args; m_tag = -1; }

let mpath_abs id args = mpath (`Local id) args
let mident id = mpath_abs id []

let mpath_crt p args sp = mpath (`Concrete(p,sp)) args

let mqname mp x =
  match mp.m_top with
  | `Concrete(top,None) -> mpath_crt top mp.m_args (Some (psymbol x))
  | `Concrete(top,Some sub) -> mpath_crt top mp.m_args (Some (pqname sub x))
  | _ -> assert false

let mastrip mp = { mp with m_args = [] }

let m_apply mp args =
  let args' = mp.m_args in
  mpath mp.m_top (args'@args)
(* PY check that it is safe. previous code *)
(* if args' = [] then mpath mp.m_top args
  else (assert (args = []); mp) *)

let m_functor mp =
  let top =
    match mp.m_top with
    | `Concrete(p,Some _) -> `Concrete(p,None)
    | t -> t in
  mpath top []

let mget_ident mp =
  match mp.m_top with
  | `Local id -> id
  | _ -> assert false

let rec m_fv fv mp =
  let fv =
    match mp.m_top with
    | `Local id -> EcIdent.fv_add id fv
    | `Concrete _  -> fv in
  List.fold_left m_fv fv mp.m_args

let rec pp_list sep pp fmt xs =
  let pp_list = pp_list sep pp in
    match xs with
    | []      -> ()
    | [x]     -> Format.fprintf fmt "%a" pp x
    | x :: xs -> Format.fprintf fmt "%a%(%)%a" pp x sep pp_list xs

let rec pp_m fmt mp =
  let pp_args fmt args =
    if args <> [] then
      Format.fprintf fmt "@[(%a)@]" (pp_list "," pp_m) args in
  match mp.m_top with
  | `Local id ->
    Format.fprintf fmt "%s%a" (EcIdent.tostring id) pp_args mp.m_args
  | `Concrete(p,None) ->
    Format.fprintf fmt "%s%a" (tostring p) pp_args mp.m_args
  | `Concrete(p,Some sub) ->
    Format.fprintf fmt "%s%a.%s" (tostring p) pp_args mp.m_args (tostring sub)

(* -------------------------------------------------------------------- *)
type xpath = {
  x_top : mpath;
  x_sub : symbol;
  x_tag : int;
}

let x_equal   = ((==) : xpath -> xpath -> bool)
let x_hash    = fun p -> p.x_tag
let x_compare = fun p1 p2 -> x_hash p1 - x_hash p2

let x_equal_na x1 x2 =
     mt_equal x1.x_top.m_top x2.x_top.m_top
  && EcSymbols.sym_equal x1.x_sub x2.x_sub

let x_compare_na x1 x2 =
  x_compare x1 x2 (* FIXME: doc says something about x_top being normalized *)

module Hsxpath = Why3.Hashcons.Make (struct
  type t = xpath

  let equal m1 m2 =
    m_equal m1.x_top m2.x_top && EcSymbols.sym_equal m1.x_sub m2.x_sub

  let hash m =
    Why3.Hashcons.combine (m_hash m.x_top) (Hashtbl.hash m.x_sub)

  let tag n p = { p with x_tag = n }
end)

module XPath = MakeMSH (struct
  type t  = xpath
  let tag = x_hash
end)

let x_ntr_compare (xp1 : xpath) (xp2 : xpath) =
  match m_ntr_compare xp1.x_top xp2.x_top with
  | 0 -> String.compare xp1.x_sub xp2.x_sub
  | n -> n

let xpath top sub =
  Hsxpath.hashcons { x_top = top; x_sub = sub; x_tag = -1; }

let x_fv fv xp = m_fv fv xp.x_top

let xastrip x = { x with x_top = mastrip x.x_top }
let xbasename xp = xp.x_sub

(* -------------------------------------------------------------------- *)
module Mx = XPath.M
module Hx = XPath.H

module Sx = struct
  include XPath.S

  let ntr_elements s =
    List.ksort ~key:identity ~cmp:x_ntr_compare (elements s)
end

(* -------------------------------------------------------------------- *)
let rec m_tostring (m : mpath) =
  let top, sub =
    match m.m_top with
    | `Local id -> (EcIdent.tostring id, "")

    | `Concrete (p, sub) ->
      let strsub =
        sub |> ofold (fun p _ -> Format.sprintf ".%s" (tostring p)) ""
      in
        (tostring p, strsub)
  in

  let args =
    let a = m.m_args in
      match a with
      | [] -> ""
      | _  ->
        let stra = List.map m_tostring a in
          Printf.sprintf "(%s)" (String.concat ", " stra)
  in
    Printf.sprintf "%s%s%s" top args sub

let x_tostring x =
  Printf.sprintf "%s./%s"
    (m_tostring x.x_top) x.x_sub

(* -------------------------------------------------------------------- *)
let p_subst (s : path Mp.t) =
  if Mp.is_empty s then identity
  else
    let p_subst aux p =
      try  Mp.find p s
      with Not_found ->
        match p.p_node with
        | Psymbol _ -> p
        | Pqname(p1, id) ->
          let p1' = aux p1 in
          if p1 == p1' then p else pqname p1' id in
    Hp.memo_rec 107 p_subst

(* -------------------------------------------------------------------- *)
let rec m_subst (sp : path -> path) (sm : mpath EcIdent.Mid.t) m =
  let args = List.Smart.map (m_subst sp sm) m.m_args in
  match m.m_top with
  | `Concrete(p,sub) ->
    let p' = sp p in
    let top = if p == p' then m.m_top else `Concrete(p',sub) in
    if m.m_top == top && m.m_args == args then m else
      mpath top args
  | `Local id ->
    try
      let m' = EcIdent.Mid.find id sm in
      m_apply m' args
    with Not_found ->
      if m.m_args == args then m else
        mpath m.m_top args

let m_subst (sp : path -> path) (sm : mpath EcIdent.Mid.t) =
  if sp == identity && EcIdent.Mid.is_empty sm then identity
  else m_subst sp sm

(* -------------------------------------------------------------------- *)
let x_subst (sm : mpath -> mpath) =
  if sm == identity then identity
  else fun x ->
    let top = sm x.x_top in
    if x.x_top == top then x
    else xpath top x.x_sub

let x_substm sp sm =
  x_subst (m_subst sp sm)
