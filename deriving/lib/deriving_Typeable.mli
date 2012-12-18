module TypeRep :
sig
  type t
  type delayed = t Lazy.t
  val compare : t -> t -> int
  val eq : t -> t -> bool
  val mkFresh : string -> delayed list -> t
  val mkTuple : delayed list -> t
  val mkPolyv : (string * delayed option) list -> delayed list -> t
end

exception CastFailure of string

type dynamic
val tagOf : dynamic -> TypeRep.t

module type Typeable =
sig
  type a
  val type_rep : TypeRep.t Lazy.t
  val has_type : dynamic -> bool
  val cast : dynamic -> a option
  val throwing_cast : dynamic -> a
  val make_dynamic : a -> dynamic
  val mk : a -> dynamic
end

module Defaults (T : (sig
                        type a
                        val type_rep : TypeRep.t Lazy.t
                      end))
  : Typeable with type a = T.a

module Typeable_list   (A : Typeable) : Typeable with type a = A.a list
module Typeable_option (A : Typeable) : Typeable with type a = A.a option
module Typeable_ref    (A : Typeable) : Typeable with type a = A.a ref

(*module Primitive_typeable (T : sig type t end): Typeable with type a = T.t *)

module Typeable_unit   : Typeable with type a = unit
module Typeable_int    : Typeable with type a = int
module Typeable_float  : Typeable with type a = float
module Typeable_bool   : Typeable with type a = bool
module Typeable_string : Typeable with type a = string
module Typeable_char   : Typeable with type a = char
module Typeable_int32     : Typeable with type a = int32
module Typeable_int64     : Typeable with type a = int64
module Typeable_nativeint : Typeable with type a = nativeint

(**/**)
module Primitive_typeable (T : sig type t val magic : string end) : Typeable with type a = T.t
