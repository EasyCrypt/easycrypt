(* -------------------------------------------------------------------- *)
open Pprint

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

let identity x = x 

let (^~) f = fun x y -> f y x

let (-|) (f : 'a -> 'b) (g : 'c -> 'a) =
  fun x -> f (g x)

(* -------------------------------------------------------------------- *)
let proj3_1 (x, _, _) = x
let proj3_2 (_, x, _) = x
let proj3_3 (_, _, x) = x

let fst_map (f : 'a -> 'c) ((x, y) : 'a * 'b) =
  (f x, y)

let snd_map (f : 'b -> 'c) ((x, y) : 'a * 'b) =
  (x, f y)

let pair_equal tx ty (x1, y1) (x2, y2) =
  (tx x1 x2) && (ty y1 y2)

(* -------------------------------------------------------------------- *)
let opt_equal (f : 'a -> 'a -> bool) o1 o2 =
  match o1, o2 with
  | Some x1, Some x2 -> f x1 x2
  | None   , None    -> true
  | _      , _       -> false

(* -------------------------------------------------------------------- *)
module type IFlag = sig
  type flag

  val toint : flag -> int               (* \in {0..31} *)
end

module type IFlags = sig
  type flag
  type t

  val null      : t
  val singleton : flag -> t
  val fromlist  : flag list -> t
  val add       : flag -> t -> t
  val have      : flag -> t -> bool
  val included  : t -> t -> bool
  val equal     : t -> t -> bool
end

module Flags(X : IFlag) : IFlags
  with type flag = X.flag
= struct
  type flag = X.flag
  type t    = Flags of int

  let null = Flags 0

  let add (e : flag) (Flags f : t) =
    Flags (f lor (1 lsl (X.toint e)))

  let singleton (e : flag) =
    add e null

  let fromlist (es : flag list) =
    List.fold_left ((^~) add) null es

  let have (e : flag) (Flags f : t) =
    (f land (1 lsl (X.toint e))) != 0

  let included (Flags fin) (Flags fout) =
    (lnot fin) land fout == 0

  let equal (Flags fin) (Flags fout) =
    fin == fout
end

(* -------------------------------------------------------------------- *)
let none = None
let some = fun x -> Some x

let oiter (x : 'a option) (f : 'a -> unit) =
  match x with None -> () | Some x -> f x

let obind (x : 'a option) (f : 'a -> 'b option) =
  match x with None -> None | Some x -> f x

let otolist (x : 'a option) =
  match x with None -> [] | Some x -> [x]

let ofold (x : 'a option) (f : 'a -> 'b -> 'b) (v : 'b) =
  match x with
  | None   -> v
  | Some x -> f x v

let ocompare cmp x1 x2 =
  match x1, x2 with
  | None   , None    -> 0
  | Some x1, Some x2 -> cmp x1 x2
  | None   , Some _  -> -1
  | Some _ , None    -> 1

let omap (x : 'a option) (f : 'a -> 'b) =
  match x with None -> None | Some x -> Some (f x)

let omap_dfl (x:'a option) (d:'b) (f:'a -> 'b) =
  match x with None -> d  | Some x -> f x

let osmart_map (x : 'a option) (f : 'a -> 'b) =
  match x with 
  | None -> x 
  | Some y -> 
      let y' = f y in 
      if y == y' then x else Some y'

let odfl (d : 'a) (x : 'a option) =
  match x with None -> d | Some x -> x

let ofdfl (d : unit -> 'a) (x : 'a option) =
  match x with None -> d () | Some x -> x

let oget (x : 'a option) =
  match x with None -> assert false | Some x -> x

let oall2 f x y = 
  match x, y with
  | Some x, Some y -> f x y
  | None  , None   -> true
  | _     , _      -> false 

(* -------------------------------------------------------------------- *)
let fstmap f (x, y) = (f x, y)
let sndmap f (x, y) = (x, f y)

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
module List = struct
  include List

  let hd2 l = 
    match l with
    | a::b::_ -> a,b
    | _ -> assert false

  let ocons o l = 
    match o with
    | None -> l
    | Some e -> e :: l

  let isempty xs = xs == []

  let ohead (xs : 'a list) =
    match xs with [] -> None | x :: _ -> Some x

  let rec last = function
    | []      -> failwith "List.last"
    | [x]     -> x
    | _ :: xs -> last xs

  let create n x =
    let rec aux n xs =
      if n <= 0 then xs else aux (n-1) (x::xs)
    in
      aux n []

  let iteri f xs =
    let rec doit i = function
      | []      -> ()
      | x :: xs -> f i x; doit (i + 1) xs
    in
      doit 0 xs

  let iter2i f xs ys =
    let rec doit i = function
      | [], [] -> ()
      | x :: xs, y :: ys -> f i x y; doit (i + 1) (xs, ys)
      | _, _ -> failwith "List.iter2i"
    in
      doit 0 (xs, ys)

  let rec pmap (f : 'a -> 'b option) (xs : 'a list) =
    match xs with
    | []      -> []
    | x :: xs -> ocons (f x) (pmap f xs)

  let prmap f l = 
    let rec aux r l = 
      match l with 
      | [] -> r
      | x::l -> aux (ocons (f x) r) l in
    aux [] l

  let findopt (f : 'a -> bool) (xs : 'a list) =
    try  Some (List.find f xs)
    with Not_found -> None

  let rec pick (f : 'a -> 'b option) (xs : 'a list) =
    match xs with
      | []      -> None
      | x :: xs -> begin
        match f x with
          | None        -> pick f xs
          | Some _ as r -> r
      end

  let rec fpick (xs : (unit -> 'a option) list) =
    match xs with
    | []      -> None
    | x :: xs -> begin
        match x () with
        | None   -> fpick xs
        | Some v -> Some v
    end

  let index (v : 'a) (xs : 'a list) : int option =
    let rec index (i : int) = function
      | [] -> None
      | x :: xs -> if x = v then Some i else index (i+1) xs
    in
      index 0 xs

  let all2 (f : 'a -> 'b -> bool) xs ys =
    let rec all2 = function
      | ([]     , []     ) -> true
      | (x :: xs, y :: ys) -> (f x y) && (all2 (xs, ys))
      | (_      , _      ) -> false
    in
      all2 (xs, ys)

  let rec uniq (xs : 'a list) =
    match xs with
      | []      -> true
      | x :: xs -> (not (List.mem x xs)) && (uniq xs)

  let assoc_eq eq (x : 'a) (xs : ('a * 'b) list) =
    snd (List.find (fun (x',_) -> eq x x') xs) 

  let tryassoc_eq eq x xs = 
    try_nf (fun () -> assoc_eq eq x xs)

  let tryassoc (x : 'a) (xs : ('a * 'b) list) =
    tryassoc_eq (=) x xs

  let take_n (n : int) (xs : 'a list) =
    let rec take n xs acc =
      match n, xs with
      | 0, _ | _, [] -> List.rev acc, xs
      | _, x :: xs -> take (n-1) xs (x :: acc)
    in
    take n xs []

  let take (n : int) (xs : 'a list) = fst (take_n n xs)

  let split_n n l = 
    let rec aux r n l = 
      match n, l with
      | _, [] -> raise Not_found 
      | 0, x::l -> r, x, l
      | _, x::l -> aux (x::r) (n-1) l in
    aux [] n l 

  let find_split f l = 
    let rec aux r l = 
      match l with 
      | [] -> raise Not_found
      | x::l -> if f x then r, x, l else aux (x::r) l in
    aux [] l
 
  let map_fold (f : 'a -> 'b -> 'a * 'c) (a : 'a) (xs : 'b list) =
    let a = ref a in
    let f b = 
      let (a',c) = f !a b in
      a := a'; c in
    let l = List.map f xs in
    !a, l
  
  let map_combine
      (f1  : 'a -> 'c) (f2  : 'b -> 'd)
      (xs1 : 'a list ) (xs2 : 'b list )
  =
    let rec doit xs1 xs2 =
      match xs1, xs2 with
      | ([], []) -> []
      | (x1 :: xs1, x2 :: xs2) ->
        let y1, y2 = f1 x1, f2 x2 in
        let ys = doit xs1 xs2 in
          (y1, y2) :: ys
      | (_, _) -> invalid_arg "List.map_combine"

  in
      doit xs1 xs2

  let fold_lefti f a l = 
    let i = ref (-1) in
    let f a e =  incr i; f !i a e in
    List.fold_left f a l

  let rec filter2 f la lb = 
    match la, lb with
    | [], [] -> [], []
    | a::la, b::lb ->
        let (la,lb as r) = filter2 f la lb in
        if f a b then a::la, b::lb 
        else r
    | _, _ -> invalid_arg "List.filter2"

  let rec smart_map f l = 
    match l with
    | [] -> l
    | h::tl ->
        let h' = f h in
        let tl' = smart_map f tl in
	if h'==h && tl'==tl then l else 
        h'::tl'

  let smart_map_fold (f : 'a -> 'b -> 'a * 'c) (a : 'a) (xs : 'b list) =
    let r = ref a in
    let f b = 
      let (a,c) = f !r b in
      r := a; c in
    let l = smart_map f xs in
    !r, l

end

(* -------------------------------------------------------------------- *)
module Parray : sig 
  type 'a t

  val empty : 'a t
  val get : 'a t -> int -> 'a
  val length : 'a t -> int 
  val of_list : 'a list -> 'a t
  val to_list : 'a t -> 'a list
  val of_array : 'a array -> 'a t
  val init : int -> (int -> 'a) -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val fmap : ('a -> 'b) -> 'a list -> 'b t
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
  val fold_right : ('b -> 'a -> 'a) -> 'b t -> 'a -> 'a
  val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b t -> 'c t -> 'a
  val iter : ('a -> unit) -> 'a t -> unit 
  val iter2 : ('a -> 'b -> unit) -> 'a t -> 'b t -> unit
  val split : ('a * 'b) t -> ('a t * 'b t)
  val exists : ('a -> bool) -> 'a t -> bool
  val for_all : ('a -> bool) -> 'a t -> bool
end = struct
  type 'a t = 'a array

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
  include String

  let map f s =
    let r = String.create (String.length s) in
      for i = 0 to (String.length s) - 1 do
        r.[i] <- f s.[i]
      done;
      r

  let slice ?first ?last (s : string) =
    let first = odfl 0 first in
    let last  = odfl (String.length s) last in
      String.sub s first (last - first)

  let split (c : char) (s : string) =
    let rec split s acc =
      match try_nf (fun () -> rindex s c) with
      | None   -> if (s = "") then acc else (s :: acc)
      | Some i ->
          split
            (slice ~first:0 ~last:i s)
            ((slice ~first:(i+1) s) :: acc)
    in
      split s []
end

(* -------------------------------------------------------------------- *)
module Stream = struct
  include Stream

  let next_opt (stream : 'a Stream.t) =
    try  Some (Stream.next stream)
    with Stream.Failure -> None
end
