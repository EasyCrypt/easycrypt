(* -------------------------------------------------------------------- *)
exception Unexpected

val unexpected : unit -> 'a

(* -------------------------------------------------------------------- *)
val tryexn : (exn -> bool) -> (unit -> 'a) -> 'a option
val try_nf : (unit -> 'a) -> 'a option

val try_finally : (unit -> 'a) -> (unit -> unit) -> 'a

(* -------------------------------------------------------------------- *)
val identity : 'a -> 'a

val (^~) : ('a -> 'b -> 'c) -> ('b -> 'a -> 'c)
val (-|) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val (|-) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b

val (|>) : 'a -> ('a -> 'b) -> 'b
val (<|) : ('a -> 'b) -> 'a -> 'b

(* -------------------------------------------------------------------- *)
val copy : 'a -> 'a

(* -------------------------------------------------------------------- *)
val reffold : ('a -> 'b * 'a) -> 'a ref -> 'b

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

(* -------------------------------------------------------------------- *)
val as_seq0 : 'a list -> 'a tuple0
val as_seq1 : 'a list -> 'a tuple1
val as_seq2 : 'a list -> 'a tuple2
val as_seq3 : 'a list -> 'a tuple3

(* -------------------------------------------------------------------- *)
val proj3_1 : 'a * 'b * 'c -> 'a
val proj3_2 : 'a * 'b * 'c -> 'b
val proj3_3 : 'a * 'b * 'c -> 'c

val fst_map : ('a -> 'c) -> 'a * 'b -> 'c * 'b
val snd_map : ('b -> 'c) -> 'a * 'b -> 'a * 'c

(* -------------------------------------------------------------------- *)
type 'a eq  = 'a -> 'a -> bool
type 'a cmp = 'a -> 'a -> int

val pair_equal : 'a eq -> 'b eq -> ('a * 'b) eq
val opt_equal  : 'a eq -> 'a option eq
 
(* -------------------------------------------------------------------- *)
val none : 'a option
val some : 'a -> 'a option

(* -------------------------------------------------------------------- *)
val oiter      : ('a -> unit) -> 'a option -> unit
val obind      : ('a -> 'b option) -> 'a option -> 'b option
val ofold      : ('a -> 'b -> 'b) -> 'b -> 'a option -> 'b
val omap       : ('a -> 'b) -> 'a option -> 'b option
val odfl       : 'a -> 'a option -> 'a
val ofdfl      : (unit -> 'a) -> 'a option -> 'a
val oget       : 'a option -> 'a
val oall2      : ('a -> 'b -> bool) -> 'a option -> 'b option -> bool
val otolist    : 'a option -> 'a list
val ocompare   : 'a cmp -> 'a option cmp
val omap_dfl   : ('a -> 'b) -> 'b -> 'a option -> 'b
val osmart_map : ('a -> 'a) -> 'a option -> 'a option

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
module List : sig
  include module type of List

  val ocons : 'a option -> 'a list -> 'a list

  val isempty : 'a list -> bool

  val ohead : 'a list -> 'a option

  val otail : 'a list -> 'a list option

  val iteri : (int -> 'a -> 'b) -> 'a list -> unit

  val iter2i : (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> unit

  val fusion : ('a -> 'a -> 'a) -> 'a list -> 'a list -> 'a list

  val iter2o : ('a option -> 'b option -> 'c) -> 'a list -> 'b list -> unit

  val findopt : ('a -> bool) -> 'a list -> 'a option

  val index :  'a -> 'a list -> int option

  val uniqf : ('a -> 'a -> bool) -> 'a list -> bool

  val uniq : 'a list -> bool

  val take_n : int -> 'a list -> 'a list

  val take : int -> 'a list -> 'a list

  val split_n : int -> 'a list -> 'a list * 'a * 'a list

  val find_split : (int -> 'a -> 'b -> 'a) -> 'a -> 'b list -> 'a

  val fold_lefti : (int -> 'a -> 'b -> 'a) -> 'a -> 'b list -> 'a

  val filter2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list * 'b list

  val create : int -> 'a -> 'a list

  val find_split : ('a -> bool) -> 'a list -> 'a list * 'a * 'a list

  val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list

  val map_fold : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list

  val map_combine : ('a -> 'c) -> ('b -> 'd) -> 'a list -> 'b list -> ('c * 'd) list

  val take_n : int -> 'a list -> 'a list * 'a list

  val all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

  val hd2 : 'a list -> 'a * 'a

  val pick : ('a -> 'b option) -> 'a list -> 'b option

  val fpick : (unit -> 'a option) list -> 'a option

  val assoc_eq : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> 'b

  val tryassoc_eq : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> 'b option

  val tryassoc : 'a -> ('a * 'b) list -> 'b option

  val pmap : ('a -> 'b option) -> 'a list -> 'b list

  val prmap : ('a -> 'b option) -> 'a list -> 'b list

  val sum : int list -> int

  val min : 'a -> 'a list -> 'a

  val max : 'a -> 'a list -> 'a

  module Smart : sig
    val map : ('a -> 'a) -> 'a list -> 'a list

    val map_fold : ('a -> 'b -> 'a * 'b) -> 'a -> 'b list -> 'a * 'b list
  end
end

(* -------------------------------------------------------------------- *)
module Stream : sig
  include module type of Stream with type 'a t = 'a Stream.t

  val next_opt : 'a Stream.t -> 'a option
end

(* -------------------------------------------------------------------- *)
module String : sig
  include module type of String

  val map : (char -> char) -> string -> string

  val startswith : string -> string -> bool

  val endswith : string -> string -> bool

  val slice : ?first:int -> ?last:int -> string -> string

  val split : char -> string -> string list
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
end

(* -------------------------------------------------------------------- *)
module Os : sig
  val listdir : string -> string list
end

