(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type ident = private {
  id_symb : symbol;
  id_tag  : int;
}

type t = ident

val create   : symbol -> t
val fresh    : t -> t
val name     : t -> symbol
val tag      : t -> int
val tostring : t -> string

(* -------------------------------------------------------------------- *)
val id_equal : t -> t -> bool
val id_compare : t -> t -> int 
val id_hash : t -> int

(* -------------------------------------------------------------------- *)
module Mid : Map.S with type key = t
module Sid : Mid.Set with type elt = t

(* -------------------------------------------------------------------- *)
module Map : sig
  type key = t

  type 'a t

  val empty     : 'a t
  val add       : key -> 'a -> 'a t -> 'a t
  val allbyname : symbol -> 'a t -> (key * 'a) list
  val byname    : symbol -> 'a t -> (key * 'a) option
  val byident   : key -> 'a t -> 'a option
  val update    : key -> ('a -> 'a) -> 'a t -> 'a t
  val merge     : 'a t -> 'a t -> 'a t

  val dump :
       name:string
    -> (EcDebug.ppdebug -> 'a -> unit)
    -> EcDebug.ppdebug -> 'a t -> unit
end

(* -------------------------------------------------------------------- *)
val pp_ident : t EcFormat.pp
