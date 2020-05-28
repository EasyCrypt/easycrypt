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

val unexpected : unit -> 'a

(* -------------------------------------------------------------------- *)
type 'data cb = Cb : 'a * ('data -> 'a -> unit) -> 'data cb

(* -------------------------------------------------------------------- *)
val tryexn : (exn -> bool) -> (unit -> 'a) -> 'a option
val try_nf : (unit -> 'a) -> 'a option

val try_finally : (unit -> 'a) -> (unit -> unit) -> 'a

val timed : ('a -> 'b) -> 'a -> float * 'b

(* -------------------------------------------------------------------- *)
val identity : 'a -> 'a

val pred0: 'a -> bool
val predT: 'a -> bool

val (^~) : ('a -> 'b -> 'c) -> ('b -> 'a -> 'c)
val (-|) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val (|-) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b

val (|>) : 'a -> ('a -> 'b) -> 'b
val (<|) : ('a -> 'b) -> 'a -> 'b
val (|?) : 'a option -> 'a -> 'a

val curry   : ('a1 -> 'a2 -> 'b) -> 'a1 * 'a2 -> 'b
val uncurry : ('a1 * 'a2 -> 'b) -> 'a1 -> 'a2 -> 'b

val curry3   : ('a1 -> 'a2 -> 'a3 -> 'b) -> 'a1 * 'a2 * 'a3 -> 'b
val uncurry3 : ('a1 * 'a2 * 'a3 -> 'b) -> 'a1 -> 'a2 -> 'a3 -> 'b

(* -------------------------------------------------------------------- *)
val clamp : min:int -> max:int -> int -> int

(* -------------------------------------------------------------------- *)
val copy : 'a -> 'a

(* -------------------------------------------------------------------- *)
val reffold  : ('a -> 'b * 'a) -> 'a ref -> 'b
val postincr : int ref -> int

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
type 'a pair   = 'a tuple2

(* -------------------------------------------------------------------- *)
val in_seq1: ' a -> 'a list

(* -------------------------------------------------------------------- *)
val as_seq0 : 'a list -> 'a tuple0
val as_seq1 : 'a list -> 'a tuple1
val as_seq2 : 'a list -> 'a tuple2
val as_seq3 : 'a list -> 'a tuple3
val as_seq4 : 'a list -> 'a tuple4
val as_seq5 : 'a list -> 'a tuple5
val as_seq6 : 'a list -> 'a tuple6
val as_seq7 : 'a list -> 'a tuple7

(* -------------------------------------------------------------------- *)
val t2_map : ('a -> 'b) -> 'a tuple2 -> 'b tuple2
val t3_map : ('a -> 'b) -> 'a tuple3 -> 'b tuple3

(* -------------------------------------------------------------------- *)
val int_of_bool : bool -> int

(* -------------------------------------------------------------------- *)
val proj3_1 : 'a * 'b * 'c -> 'a
val proj3_2 : 'a * 'b * 'c -> 'b
val proj3_3 : 'a * 'b * 'c -> 'c

val proj4_1 : 'a * 'b * 'c * 'd -> 'a
val proj4_2 : 'a * 'b * 'c * 'd -> 'b
val proj4_3 : 'a * 'b * 'c * 'd -> 'c
val proj4_4 : 'a * 'b * 'c * 'd -> 'd

val fst_map : ('a -> 'c) -> 'a * 'b -> 'c * 'b
val snd_map : ('b -> 'c) -> 'a * 'b -> 'a * 'c

val swap: 'a * 'b -> 'b * 'a

(* -------------------------------------------------------------------- *)
type 'a eq  = 'a -> 'a -> bool
type 'a cmp = 'a -> 'a -> int

val pair_map   : ('a -> 'b) -> 'a pair -> 'b pair
val pair_equal : 'a eq -> 'b eq -> ('a * 'b) eq
val opt_equal  : 'a eq -> 'a option eq

(* -------------------------------------------------------------------- *)
val compare_tag : 'a cmp
val compare2: int lazy_t -> int lazy_t -> int
val compare3: int lazy_t -> int lazy_t -> int lazy_t -> int

(* -------------------------------------------------------------------- *)
val none : 'a option
val some : 'a -> 'a option

val is_none : 'a option -> bool
val is_some : 'a option -> bool

val funnone : 'a -> 'b option

(* -------------------------------------------------------------------- *)
val oiter      : ('a -> unit) -> 'a option -> unit
val obind      : ('a -> 'b option) -> 'a option -> 'b option
val ofold      : ('a -> 'b -> 'b) -> 'b -> 'a option -> 'b
val omap       : ('a -> 'b) -> 'a option -> 'b option
val opair      : ('a -> 'b option) -> 'a -> 'a -> ('b * 'b) option
val oif        : ('a -> bool) -> 'a option -> bool
val odfl       : 'a -> 'a option -> 'a
val ofdfl      : (unit -> 'a) -> 'a option -> 'a
val oget       : ?exn:exn -> 'a option -> 'a
val oall2      : ('a -> 'b -> bool) -> 'a option -> 'b option -> bool
val otolist    : 'a option -> 'a list
val oeq        : ('a -> 'a -> bool) -> ('a option -> 'a option -> bool)
val ocompare   : 'a cmp -> 'a option cmp
val omap_dfl   : ('a -> 'b) -> 'b -> 'a option -> 'b

module OSmart : sig
  val omap : ('a -> 'a) -> 'a option -> 'a option
  val omap_fold : ('a -> 'b -> 'a * 'b) -> 'a -> 'b option -> 'a * 'b option
end

(* -------------------------------------------------------------------- *)
type ('a, 'b) tagged = Tagged of ('a * 'b option)

val tg_val : ('a, 'b) tagged -> 'a
val tg_tag : ('a, 'b) tagged -> 'b option
val tg_map : ('a -> 'b) -> ('a, 'c) tagged -> ('b, 'c) tagged
val notag  : 'a -> ('a, 'b) tagged

(* -------------------------------------------------------------------- *)
val iterop: ('a -> 'a) -> int -> 'a -> 'a
val iter: ('a -> 'a) -> 'a -> 'b

(* -------------------------------------------------------------------- *)
module OneShot : sig
  type t

  val mk  : (unit -> unit) -> t
  val now : t -> unit
end

(* -------------------------------------------------------------------- *)
module Counter : sig
  type t

  val create : unit -> t
  val next   : t -> int
end

(* -------------------------------------------------------------------- *)
module Disposable : sig
  type 'a t

  exception Disposed

  val create  : ?cb:('a -> unit) -> 'a -> 'a t
  val get     : 'a t -> 'a
  val dispose : 'a t -> unit
end

(* -------------------------------------------------------------------- *)
module Os : sig
  val getenv  : string -> string option
  val listdir : string -> string list
end

(* -------------------------------------------------------------------- *)
module ISet : sig
  include module type of BatISet
end

(* -------------------------------------------------------------------- *)
module String : sig
  include module type of BatString

  val split_lines : string -> string list

  val option_matching : string list -> string -> string list
end

(* -------------------------------------------------------------------- *)
module IO : sig
  include module type of BatIO
end

(* -------------------------------------------------------------------- *)
module File : sig
  include module type of BatFile

  val read_from_file :
    offset:int -> length:int -> string -> string

  val write_to_file :
    output:string -> string -> unit
end

(* -------------------------------------------------------------------- *)
module Buffer : sig
  include module type of BatBuffer

  val from_string : ?size:int -> string -> t
  val from_char   : ?size:int -> char -> t
end

(* -------------------------------------------------------------------- *)
module Array : sig
  include module type of BatArray

  val count : ('a -> bool) -> 'a array -> int
end

(* -------------------------------------------------------------------- *)
module List : sig
  include module type of BatList

  module Smart : sig
    val map      : ('a -> 'a) -> 'a list -> 'a list
    val map_fold : ('a -> 'b -> 'a * 'b) -> 'a -> 'b list -> 'a * 'b list
  end

  (* Aliases to exception-less functions *)
  val ocons   : 'a option -> 'a list -> 'a list
  val ohead   : 'a list -> 'a option
  val otail   : 'a list -> 'a list option
  val olast   : 'a list -> 'a option
  val ofind   : ('a -> bool) -> 'a list -> 'a option
  val opick   : ('a -> 'b option) -> 'a list -> 'b option
  val oindex  : ('a -> bool) -> 'a list -> int option
  val orindex : ('a -> bool) -> 'a list -> int option

  (* Functions working on 2 lists in parallel *)
  module Parallel : sig
    val iter2i    : (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> unit
    val iter2o    : ('a option -> 'b option -> 'c) -> 'a list -> 'b list -> unit
    val filter2   : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list * 'b list
    val all2      : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
    val map_fold2 : ('a -> 'b -> 'c -> 'a * 'd) -> 'a -> 'b list -> 'c list -> 'a * 'd list
    val prefix2   : 'a list -> 'b list -> ('a list * 'a list) * ('b list * 'b list)
  end

  include module type of Parallel

  (*------------------------------------------------------------------ *)
  val fst : ('a * 'b) list -> 'a list
  val snd : ('a * 'b) list -> 'b list

  val min : ?cmp:('a -> 'a -> int) -> 'a list -> 'a
  val max : ?cmp:('a -> 'a -> int) -> 'a list -> 'a

  val nth_opt    : 'a list -> int -> 'a option
  val mbfilter   : ('a -> bool) -> 'a list -> 'a list
  val fusion     : ('a -> 'a -> 'a) -> 'a list -> 'a list -> 'a list
  val is_unique  : ?eq:('a -> 'a -> bool) -> 'a list -> bool
  val fpick      : (unit -> 'a option) list -> 'a option
  val pivot_at   : int -> 'a list -> 'a list * 'a * 'a list
  val find_pivot : ('a -> bool) -> 'a list -> 'a list * 'a * 'a list
  val map_fold   : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val mapi_fold  : (int -> 'a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val pmapi      : (int -> 'a -> 'b option) -> 'a list -> 'b list
  val pmap       : ('a -> 'b option) -> 'a list -> 'b list
  val rev_pmap   : ('a -> 'b option) -> 'a list -> 'b list
  val rotate     : [`Left|`Right] -> int -> 'a list -> int * 'a list
  val reduce1    : ('a list -> 'a) -> 'a list -> 'a

  (* ------------------------------------------------------------------ *)
  val ksort:
        ?stable:bool -> ?rev:bool
     -> key:('a -> 'b)
     -> cmp:('b -> 'b -> int)
     -> 'a list -> 'a list
end

(* -------------------------------------------------------------------- *)
module Parray : sig
  type 'a parray

  val empty : 'a parray
  val get : 'a parray -> int -> 'a
  val length : 'a parray -> int
  val of_list : 'a list -> 'a parray
  val to_list : 'a parray -> 'a list
  val of_array : 'a array -> 'a parray
  val init : int -> (int -> 'a) -> 'a parray
  val map : ('a -> 'b) -> 'a parray -> 'b parray
  val fmap : ('a -> 'b) -> 'a list -> 'b parray
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b parray -> 'a
  val fold_right : ('b -> 'a -> 'a) -> 'b parray -> 'a -> 'a
  val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b parray -> 'c parray -> 'a
  val iter : ('a -> unit) -> 'a parray -> unit
  val iter2 : ('a -> 'b -> unit) -> 'a parray -> 'b parray -> unit
  val split : ('a * 'b) parray -> ('a parray * 'b parray)
  val exists : ('a -> bool) -> 'a parray -> bool
  val for_all : ('a -> bool) -> 'a parray -> bool
end
