(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
module Enum = BatEnum

(* -------------------------------------------------------------------- *)
exception Unexpected

let unexpected () = raise Unexpected

(* -------------------------------------------------------------------- *)
type 'data cb = Cb : 'a * ('data -> 'a -> unit) -> 'data cb

(* -------------------------------------------------------------------- *)
type 'a eq  = 'a -> 'a -> bool
type 'a cmp = 'a -> 'a -> int

(* -------------------------------------------------------------------- *)
let clamp ~min ~max i =
  Pervasives.min max (Pervasives.max min i)

(* -------------------------------------------------------------------- *)
let tryexn (ignoreexn : exn -> bool) (f : unit -> 'a) =
  try  Some (f ())
  with e -> if ignoreexn e then None else raise e

let try_nf (f : unit -> 'a) =
  tryexn (function Not_found -> true | _ -> false) f

let try_finally (body : unit -> 'a) (cleanup : unit -> unit) =
  let aout =
    try  body ()
    with e -> cleanup (); raise e
  in
    cleanup (); aout

let timed f x =
  let t1   = Unix.gettimeofday () in
  let aout = f x in
  let t2   = Unix.gettimeofday () in
  (t2 -. t1, aout)

let identity x = x

let pred0 (_ : 'a) = false
let predT (_ : 'a) = true

let (^~) f = fun x y -> f y x

let (-|) f g = fun x -> f (g x)
let (|-) g f = fun x -> g (f x)

let (|>) x f = f x
let (<|) f x = f x

let (|?) = BatPervasives.(|?)

let curry   f (x, y) = f x y
let uncurry f x y = f (x, y)

let curry3   f (x, y, z) = f x y z
let uncurry3 f x y z = f (x, y, z)

(* -------------------------------------------------------------------- *)
let copy (x : 'a) : 'a =
  Obj.obj (Obj.dup (Obj.repr x))

(* -------------------------------------------------------------------- *)
let reffold (f : 'a -> 'b * 'a) (r : 'a ref) : 'b =
  let (x, v) = f !r in r := v; x

let postincr (i : int ref) = incr i; !i

(* -------------------------------------------------------------------- *)
let compare_tag (x1 : 'a) (x2 : 'a) =
  match Obj.tag (Obj.repr x1), Obj.tag (Obj.repr x2) with
  | n1, n2 when (n1, n2) = (Obj.int_tag, Obj.int_tag) ->
      Pervasives.compare (Obj.magic x1 : int) (Obj.magic x2 : int)

  | n1, _ when n1 = Obj.int_tag ->  1
  | _, n2 when n2 = Obj.int_tag -> -1

  | n1, n2 -> Pervasives.compare n1 n2

type lzcmp = int lazy_t

let compare2 (c1 : lzcmp) (c2 : lzcmp) =
  match c1 with
  | lazy 0 -> Lazy.force c2
  | lazy n -> n

let compare3 (c1 : lzcmp) (c2 : lzcmp) (c3 : lzcmp) =
  match c1 with
  | lazy 0 -> compare2 c2 c3
  | lazy n -> n

(* -------------------------------------------------------------------- *)
type 'a tuple0 = unit
type 'a tuple1 = 'a
type 'a tuple2 = 'a * 'a
type 'a tuple3 = 'a * 'a * 'a
type 'a tuple4 = 'a * 'a * 'a * 'a
type 'a tuple5 = 'a * 'a * 'a * 'a * 'a
type 'a tuple6 = 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple7 = 'a * 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple8 = 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple9 = 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a
type 'a pair   = 'a * 'a

(* -------------------------------------------------------------------- *)
let t2_map (f : 'a -> 'b) (x, y) =
  (f x, f y)

let t3_map (f : 'a -> 'b) (x, y, z) =
  (f x, f y, f z)

(* -------------------------------------------------------------------- *)
let in_seq1 (x : 'a) = [x]

(* -------------------------------------------------------------------- *)
let as_seq0 = function [] -> () | _ -> assert false
let as_seq1 = function [x] -> x | _ -> assert false
let as_seq2 = function [x1; x2] -> (x1, x2) | _ -> assert false
let as_seq3 = function [x1; x2; x3] -> (x1, x2, x3) | _ -> assert false

let as_seq4 = function
  | [x1; x2; x3; x4] -> (x1, x2, x3, x4)
  | _ -> assert false

let as_seq5 = function
  | [x1; x2; x3; x4; x5] -> (x1, x2, x3, x4, x5)
  | _ -> assert false

let as_seq6 = function
  | [x1; x2; x3; x4; x5; x6] -> (x1, x2, x3, x4, x5, x6)
  | _ -> assert false

let as_seq7 = function
  | [x1; x2; x3; x4; x5; x6; x7] -> (x1, x2, x3, x4, x5, x6, x7)
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let int_of_bool (b : bool) = if b then 1 else 0

(* -------------------------------------------------------------------- *)
let proj3_1 (x, _, _) = x
let proj3_2 (_, x, _) = x
let proj3_3 (_, _, x) = x

let proj4_1 (x, _, _, _) = x
let proj4_2 (_, x, _, _) = x
let proj4_3 (_, _, x, _) = x
let proj4_4 (_, _, _, x) = x

let fst_map (f : 'a -> 'c) ((x, y) : 'a * 'b) =
  (f x, y)

let snd_map (f : 'b -> 'c) ((x, y) : 'a * 'b) =
  (x, f y)

let pair_map (f : 'a -> 'b) ((x, y) : 'a * 'a) =
  (f x, f y)

let pair_equal tx ty (x1, y1) (x2, y2) =
  (tx x1 x2) && (ty y1 y2)

let swap (x, y) = (y, x)

(* -------------------------------------------------------------------- *)
module Option = BatOption

(* -------------------------------------------------------------------- *)
let opt_equal (f : 'a -> 'a -> bool) o1 o2 =
  match o1, o2 with
  | Some x1, Some x2 -> f x1 x2
  | None   , None    -> true
  | _      , _       -> false

(* -------------------------------------------------------------------- *)
let none = None
let some = fun x -> Some x

let is_none = function None   -> true | _ -> false
let is_some = function Some _ -> true | _ -> false

let funnone (_ : 'a) : 'b option = None

let oiter (f : 'a -> unit) (x : 'a option) =
  match x with None -> () | Some x -> f x

let obind (f : 'a -> 'b option) (x : 'a option) =
  match x with None -> None | Some x -> f x

let otolist (x : 'a option) =
  match x with None -> [] | Some x -> [x]

let ofold (f : 'a -> 'b -> 'b) (v : 'b) (x : 'a option) =
  match x with
  | None   -> v
  | Some x -> f x v

let omap (f : 'a -> 'b) (x : 'a option) =
  match x with None -> None | Some x -> Some (f x)

let opair (f : 'a -> 'b option) x y =
  match f x with
  | Some fx -> begin
      match f y with
      | Some fy -> Some (fx, fy)
      | None -> None
    end
  | _ -> None

let omap_dfl (f : 'a -> 'b) (d : 'b) (x : 'a option) =
  match x with None -> d  | Some x -> f x

let odfl (d : 'a) (x : 'a option) =
  match x with None -> d | Some x -> x

let ofdfl (d : unit -> 'a) (x : 'a option) =
  match x with None -> d () | Some x -> x

let oif (test : 'a -> bool) (x : 'a option) =
  match x with None -> false | Some x -> test x

let oget ?exn (x : 'a option) =
  match x, exn with
  | None  , None     -> assert false
  | None  , Some exn -> raise exn
  | Some x, _        -> x

let oall2 f x y =
  match x, y with
  | Some x, Some y -> f x y
  | None  , None   -> true
  | _     , _      -> false

let oeq f o1 o2 =
  match o1, o2 with
  | None   , None    -> true
  | Some x1, Some x2 -> f x1 x2
  | _      , _       -> false

let ocompare f o1 o2 =
  match o1, o2 with
  | None   , None    -> 0
  | None   , Some _  -> -1
  | Some _ , None    -> 1
  | Some x1, Some x2 -> f x1 x2

module OSmart = struct
  let omap (f : 'a -> 'b) (x : 'a option) =
    match x with
    | None   -> x
    | Some y ->
        let y' = f y in
          if y == y' then x else Some y'

  let omap_fold (f : 'a -> 'b -> 'a * 'c) (v : 'a) (x : 'b option) =
    match x with
    | None   -> (v, x)
    | Some y ->
        let (v, y') = f v y in
          (v, if y == y' then x else Some y')
end

(* -------------------------------------------------------------------- *)
type ('a, 'b) tagged = Tagged of ('a * 'b option)

let tg_val (Tagged (x, _)) = x
let tg_tag (Tagged (_, t)) = t
let tg_map f (Tagged (x, t)) = Tagged (f x, t)
let notag x = Tagged (x, None)

(* -------------------------------------------------------------------- *)
let iterop (op : 'a -> 'a) (n : int) (x : 'a) =
  let rec doit n x = if n <= 0 then x else doit (n-1) (op x) in
  if n < 0 then invalid_arg "[iterop]: n < 0";
  doit n x

(* -------------------------------------------------------------------- *)
let iter (op : 'a -> 'a) (x : 'a) =
  let rec doit x = doit (op x) in doit x

(* -------------------------------------------------------------------- *)
module OneShot : sig
  type t

  val mk  : (unit -> unit) -> t
  val now : t -> unit
end = struct
  type t = unit Lazy.t

  let mk (f : unit -> unit) : t =
    Lazy.from_fun f

  let now (susp : t) : unit =
    Lazy.force susp
end

(* -------------------------------------------------------------------- *)
module Counter : sig
  type t

  val create : unit -> t
  val next   : t -> int
end = struct
  type t = {
    mutable state : int;
  }

  let create () = { state = 0; }

  let next (state : t) =
    let aout = state.state in
      state.state <- state.state + 1;
      aout
end

(* -------------------------------------------------------------------- *)
module Disposable : sig
  type 'a t

  exception Disposed

  val create  : ?cb:('a -> unit) -> 'a -> 'a t
  val get     : 'a t -> 'a
  val dispose : 'a t -> unit
end = struct
  type 'a t = ((('a -> unit) option * 'a) option) ref

  exception Disposed

  let get (p : 'a t) =
    match !p with
    | None        -> raise Disposed
    | Some (_, x) -> x

  let dispose (p : 'a t) =
    let do_dispose p =
      match p with
      | Some (Some cb, x) -> cb x
      | _ -> ()
    in

    let oldp = !p in
      p := None; do_dispose oldp

  let create ?(cb : ('a -> unit) option) (x : 'a) =
    let r = ref (Some (cb, x)) in
      Gc.finalise (fun r -> dispose r) r; r
end

(* -------------------------------------------------------------------- *)
module ISet = BatISet

(* -------------------------------------------------------------------- *)
module List = struct
  include BatList

  (* ------------------------------------------------------------------ *)
  module Smart = struct
    let rec map f xs =
      match xs with
      | [] -> []
      | y :: ys ->
          let z  = f y in
          let zs = map f ys in
          if y == z && ys == zs then xs else (z :: zs)

    let map_fold f a xs =
      let r   = ref a in
      let f x = let (a, x) = f !r x in r := a; x in
      let xs  = map f xs in
      (!r, xs)
  end

  (* ------------------------------------------------------------------ *)
  let ohead = Exceptionless.hd
  let otail = Exceptionless.tl
  let olast = Exceptionless.last
  let ofind = Exceptionless.find
  let opick = Exceptionless.find_map

  let ocons o xs = match o with None -> xs | Some x -> x :: xs

  (* ------------------------------------------------------------------ *)
  let oindex (f : 'a -> bool) (xs : 'a list) : int option =
    Exceptionless.findi (fun _ -> f) xs |> omap fst

  let orindex (f : 'a -> bool) (xs : 'a list) : int option =
    omap (fun i -> List.length xs - i - 1) (oindex f (List.rev xs))

  (* ------------------------------------------------------------------ *)
  module Parallel = struct
    let iter2i f xs ys =
      let rec doit i = function
        | [], [] -> ()
        | x :: xs, y :: ys -> f i x y; doit (i + 1) (xs, ys)
        | _, _ -> failwith "List.iter2i"
      in doit 0 (xs, ys)

    let rec filter2 f la lb =
      match la, lb with
      | [], [] -> [], []
      | a :: la, b :: lb ->
          let ((la, lb) as r) = filter2 f la lb in
          if f a b then (a :: la, b :: lb) else r
      | _, _ -> invalid_arg "List.filter2"

    let map_fold2 f =
      let rec doit a xs1 xs2 =
        match xs1, xs2 with
        | [], [] -> (a, [])

        | x1 :: xs1, x2 :: xs2 ->
            let (a, x ) = f a x1 x2 in
            let (a, xs) = doit a xs1 xs2 in
            (a, x :: xs)

        | _, _ -> invalid_arg "List.map_fold2"

      in fun a xs1 xs2 -> doit a xs1 xs2

    let rec iter2o f xs ys =
      match xs, ys with
      | []   , []    -> ()
      | x::xs, []    -> f (Some x) (None  ); iter2o f xs []
      | []   , y::ys -> f (None  ) (Some y); iter2o f [] ys
      | x::xs, y::ys -> f (Some x) (Some y); iter2o f xs ys

    let all2 (f : 'a -> 'b -> bool) xs ys =
      let rec all2 = function
        | ([]     , []     ) -> true
        | (x :: xs, y :: ys) -> (f x y) && (all2 (xs, ys))
        | (_      , _      ) -> false
      in all2 (xs, ys)

    let prefix2 =
      let rec prefix2 (r1, r2) xs ys =
        match xs, ys with
        | [], _ | _, [] -> (List.rev r1, xs), (List.rev r2, ys)
        | x::xs, y::ys  -> prefix2 (x::r1, y::r2) xs ys
      in fun xs ys -> prefix2 ([], []) xs ys
  end

  include Parallel

  (* ------------------------------------------------------------------ *)
  let nth_opt (s : 'a list) (i : int) =
    try  Some (List.nth s i)
    with Failure _ | Invalid_argument _ -> None

  let last (s : 'a list) =
    match Exceptionless.last s with
    | None   -> failwith "List.last"
    | Some x -> x

  let mbfilter (p : 'a -> bool) (s : 'a list) =
    match s with [] | [_] -> s | _ -> List.filter p s

  let rec fusion f xs ys =
    match xs, ys with
    | zs, [] | [], zs  -> zs
    | x :: xs, y :: ys -> let z = f x y in z :: (fusion f xs ys)

  let pivot_at n l =
    let rec aux r n l =
      match n, l with
      | _, [] -> raise Not_found
      | 0, x::l -> r, x, l
      | _, x::l -> aux (x::r) (n-1) l
    in if n < 0 then invalid_arg "List.pivot_at"; aux [] n l

  let find_pivot f xs =
    let rec aux acc xs =
      match xs with
      | [] -> raise Not_found
      | y :: ys -> if f y then acc, y, ys else aux (y::acc) ys
    in aux [] xs

  let pmapi (f : int -> 'a -> 'b option) =
    let rec doit i xs =
      match xs with
      | [] -> []
      | x :: xs -> let v = f i x in ocons v (doit (i + 1) xs)
    in fun (xs : 'a list) -> doit 0 xs

  let pmap (f : 'a -> 'b option) (xs : 'a list) =
    pmapi (fun _ -> f) xs

  let rev_pmap (f : 'a -> 'b option) (xs : 'a list) =
    let rec aux acc xs =
      match xs with
      | []      -> acc
      | x :: xs -> aux (ocons (f x) acc) xs
    in aux [] xs

  let mapi_fold f a xs =
    let a  = ref a in
    let xs = List.mapi (fun i b ->
      let (a', b') = f i !a b in a := a'; b')
      xs
    in (!a, xs)

  let map_fold f a xs =
    mapi_fold (fun (_ : int) x -> f x) a xs

  let rec fpick (xs : (unit -> 'a option) list) =
    match xs with
    | []      -> None
    | x :: xs -> begin
        match x () with
        | None   -> fpick xs
        | Some v -> Some v
    end

  let rec is_unique ?(eq = (=)) (xs : 'a list) =
    match xs with
    | []      -> true
    | x :: xs -> not (List.exists (eq x) xs) && (is_unique ~eq xs)

  let sum  xs = List.fold_left (+)  0  xs
  let sumf xs = List.fold_left (+.) 0. xs

  let rotate (d : [`Left|`Right]) (i : int) (xs : 'a list) =
    if i < 0 then invalid_arg "List.rotate: [i < 0]";
    let i = i mod List.length xs in

    if i = 0 then (0, xs) else

    let mrev   = match d with `Left -> identity | `Right -> rev in
    let hd, tl = takedrop i (mrev xs) in
    (i, mrev (tl @ hd))

  let for_all2 f xs ys =
    List.length xs = List.length ys && for_all2 f xs ys

  (* ------------------------------------------------------------------ *)
  let ksort ?(stable = false) ?(rev = false) ~key ~cmp xs =
    let cmp  =
      match rev with
      | false -> (fun x y -> cmp (key x) (key y))
      | true  -> (fun y x -> cmp (key x) (key y)) in
    let sort = if stable then List.stable_sort else List.sort in
    sort cmp xs

  let min ?(cmp = Pervasives.compare) s =
    reduce (fun x y -> if cmp x y < 0 then x else y) s

  let max ?(cmp = Pervasives.compare) s =
    reduce (fun x y -> if cmp x y > 0 then x else y) s

  let is_singleton l =
    match l with
    | [_] -> true
    |  _  -> false

  (* ------------------------------------------------------------------ *)
  let fst xs = List.map fst xs
  let snd xs = List.map snd xs

  (* ------------------------------------------------------------------ *)
  let reduce1 (f : 'a list -> 'a) : 'a list -> 'a =
    function [x] -> x | xs  -> f xs
end

(* -------------------------------------------------------------------- *)
module Parray = struct
  type 'a parray = 'a array

  include Array

  let empty = [||]

  let of_array = Array.copy

  let fmap (f : 'a -> 'b) (xs : 'a list) =
    Array.map f (of_list xs)

  let split a =
    (Array.init (Array.length a) (fun i -> fst a.(i)),
     Array.init (Array.length a) (fun i -> snd a.(i)))

  let fold_left2 f a t1 t2 =
    if Array.length t1 <> Array.length t2 then
      raise (Invalid_argument "Parray.fold_left2");
    let rec aux i a t1 t2 =
      if i < Array.length t1 then f a t1.(i) t2.(i)
      else a in
    aux 0 a t1 t2

  let iter2 (f : 'a -> 'b -> unit) a1 a2 =
    for i = 0 to (min (length a1) (length a2)) - 1 do
      f a1.(i) a2.(i)
    done

  let exists f t =
    let rec aux i t =
      if i < Array.length t then f t.(i) || aux (i+1) t
      else false in
    aux 0 t

  let for_all f t =
    let rec aux i t =
      if i < Array.length t then f t.(i) && aux (i+1) t
      else true in
    aux 0 t
end

(* -------------------------------------------------------------------- *)
module String = struct
  include BatString

  let split_lines = nsplit ~by:"\n"

  let trim (s : string) =
    let aout = BatString.trim s in
    if s == aout then BatString.copy aout else s

  let rev (s:string) = init (length s) (fun i -> s.[length s - 1 - i])

  (* ------------------------------------------------------------------ *)
  module OptionMatching = struct
    let all_matching tomatch s =
      let matched = List.map (fun s -> (s, 0)) tomatch in

      let rec aux matched i =
        if   i = length s || List.is_empty matched
        then List.map fst matched
        else
          let c = s.[i] in
          let do1 (tomatch, k) =
            try Some (tomatch, index_from tomatch k c + 1)
            with Invalid_argument _ | Not_found -> None
          in aux (List.filter_map do1 matched) (i+1)
      in aux matched 0

    let first_matching tomatch s =
      let matched = List.map (fun s -> (s, 0)) tomatch in
      let rec aux matched i =
        if   i = length s || List.is_empty matched
        then List.map fst matched
        else
          let do1 (tomatch,k) =
            try Some (tomatch, index_from tomatch k s.[i] + 1)
            with Invalid_argument _ | Not_found -> None in

          let matched = List.filter_map do1 matched in

          if List.is_empty matched then [] else begin
            let min = snd (List.min ~cmp:(fun (_, x) (_, y) -> x - y) matched) in
            let oge = fun x -> if snd x <= min then Some x else None in
            let matched = List.filter_map oge matched in

            if   List.is_singleton matched
            then List.map fst matched
            else aux matched (i+1)
          end
      in aux matched 0

    let last_matching tomatch s =
      List.map rev (first_matching (List.map rev tomatch) (rev s))
  end

  let option_matching tomatch s =
    match OptionMatching.all_matching tomatch s with
    | [s] -> [s]
    | matched -> OptionMatching.first_matching matched s
end

(* -------------------------------------------------------------------- *)
module IO = BatIO

(* -------------------------------------------------------------------- *)
module File = struct
  include BatFile

  let read_from_file ~offset ~length source =
    try
      let input = Pervasives.open_in_bin source in
      try_finally
        (fun () ->
          Pervasives.seek_in input offset;
          Pervasives.really_input_string input length)
        (fun () -> Pervasives.close_in input)
    with
    | End_of_file
    | Invalid_argument _
    | Sys_error _ -> invalid_arg "File.read_from_file"

  let write_to_file ~output data =
    try
      let output = Pervasives.open_out_bin output in
      try_finally
        (fun () ->
          Pervasives.output_string output data;
          Pervasives.flush output)
        (fun () -> Pervasives.close_out output)
    with
    | Invalid_argument _
    | Sys_error _ -> invalid_arg "File.write_to_file"
end

(* -------------------------------------------------------------------- *)
module Buffer = struct
  include BatBuffer

  let from_string ?(size = 0) (s : string) : t =
    let buffer = BatBuffer.create size in
    BatBuffer.add_string buffer s; buffer

  let from_char ?(size = 0) (c : char) : t =
    let buffer = BatBuffer.create size in
    BatBuffer.add_char buffer c; buffer
end

(* -------------------------------------------------------------------- *)
module Os = struct
  let getenv (name : string) =
    try Some (Sys.getenv name) with Not_found -> None

  let listdir (dir : string) =
    BatEnum.fold (fun xs x -> x :: xs) [] (BatSys.files_of dir)
end

(* -------------------------------------------------------------------- *)
module Array = struct
  include BatArray

  let count f a =
    Array.fold_left (fun i x -> if f x then i+1 else i) 0 a
end
