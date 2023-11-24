(* -------------------------------------------------------------------- *)
type symbol =
  string

type dep1 = Set.Int.t Map.String.t
type deps = dep1 Map.Int.t

(* -------------------------------------------------------------------- *)
val empty : size:int -> deps

val enlarge : min:int -> max:int -> deps -> deps

val clearout : min:int -> max:int -> deps -> deps

val restrict : min:int -> max:int -> deps -> deps

val recast : min:int -> max:int -> deps -> deps

val merge1 : dep1 -> dep1 -> dep1

val merge : deps -> deps -> deps

val merge1_all : dep1 Enum.t -> dep1

val merge_all : deps Enum.t -> deps

val copy : offset:int -> size:int -> symbol -> deps

val chunk : csize:int -> count:int -> deps -> deps

val perm : csize:int -> perm:int list -> deps -> deps

val collapse : csize:int -> count:int -> deps -> deps

val merge_all_deps : deps -> dep1

val constant : size:int -> dep1 -> deps

val offset : offset:int -> deps -> deps

val split : csize:int -> count:int -> deps -> deps Enum.t

val aggregate : csize:int -> deps Enum.t -> deps

(* -------------------------------------------------------------------- *)
type 'a pp = Format.formatter -> 'a -> unit

val bitintv_of_bitset : Set.Int.t -> (int * int) list

val pp_bitset : Set.Int.t pp

val pp_bitintv : (int * int) list pp

val pp_dep1 : dep1 pp

val pp_deps : deps pp
