(* ==================================================================== *)
open Aig

(* ==================================================================== *)
val log2 : int -> int

(* ==================================================================== *)
val explode : size:int -> 'a list -> 'a list list

(* ==================================================================== *)
val sint_of_bools : bool list -> int

val uint_of_bools : bool list -> int

val bytes_of_bools : bool list -> bytes

(* ==================================================================== *)
val of_int : size:int -> int -> reg

val of_bigint : size:int -> Z.t -> reg

val of_int32s : int32 list -> reg

(* ==================================================================== *)
val w8 : int -> reg

val w16 : int -> reg

val w32 : int32 -> reg

val w64 : int64 -> reg

val w128 : string -> reg

val w256 : string -> reg

(* ==================================================================== *)
val mux2 : node -> node -> node -> node

val mux2_reg : reg -> reg -> node -> reg

val mux_reg : (node * reg) list -> reg -> reg

val ite : node -> reg -> reg -> reg

(* ==================================================================== *)
val reg : size:int -> name:int -> reg

(* ==================================================================== *)
val uextend : size:int -> reg -> reg

val sextend : size:int -> reg -> reg

(* ==================================================================== *)
val lnot_ : reg -> reg

val lor_ : reg -> reg -> reg

val land_ : reg -> reg -> reg

val lxor_ : reg -> reg -> reg

val lxnor_ : reg -> reg -> reg

val ors : node list -> node

val ands : node list -> node

(* ==================================================================== *)
val arshift : offset:int -> reg -> reg

val lsl_ : reg -> reg -> reg

val lsr_ : reg -> reg -> reg

val asl_ : reg -> reg -> reg

val asr_ : reg -> reg -> reg

val shift : side:[`L | `R] -> sign:[`L | `A] -> reg -> reg -> reg

val rol : reg -> reg -> reg

val ror : reg -> reg -> reg

(* ==================================================================== *)
val incr : reg -> node * reg

val incr_dropc : reg -> reg

val incrc : reg -> reg

(* ==================================================================== *)
val add : reg -> reg -> node * reg

val addc : reg -> reg -> reg

val add_dropc : reg -> reg -> reg

val ssadd : reg -> reg -> reg

val usadd : reg -> reg -> reg

(* ==================================================================== *)
val opp : reg -> reg

val sub : reg -> reg -> node * reg

val sub_dropc : reg -> reg -> reg

(* ==================================================================== *)
val umul : reg -> reg -> reg

val umull : reg -> reg -> reg

val umulh : reg -> reg -> reg

val smul : reg -> reg -> reg

val smull : reg -> reg -> reg

val smulh : reg -> reg -> reg

val usmul : reg -> reg -> reg

(* ==================================================================== *)
val ugte : node -> reg -> reg -> node

val ugt : reg -> reg -> node

val uge : reg -> reg -> node

val sgte : node -> reg -> reg -> node

val sgt : reg -> reg -> node

val sge : reg -> reg -> node

val bvueq : reg -> reg -> node

val bvseq : reg -> reg -> node

(* ==================================================================== *)
val sat : signed:bool -> size:int -> reg -> reg

val udiv_ : reg -> reg -> reg * reg

val udiv : reg -> reg -> reg

val umod : reg -> reg -> reg

val sdiv : reg -> reg -> reg

val srem : reg -> reg -> reg

val smod : reg -> reg -> reg

(* ==================================================================== *)
val popcount : size:int -> reg -> reg

val of_sbigint : size:int -> Z.t -> reg
