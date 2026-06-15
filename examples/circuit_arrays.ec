(* ==================================================================== *)
(* [circuit] over arrays.                                               *)
(*                                                                       *)
(* [bind array] connects a polymorphic type constructor to a fixed-size *)
(* array of bit-vectors, and auto-registers its [get]/[set] operators   *)
(* for circuit translation. Array-producing operators (like [init]) are *)
(* bound with the multi-type [bind op [Elt & Arr] ... "ainit"] form.    *)
(*                                                                       *)
(* As in examples/circuit.ec, the [bind] side conditions are admitted;  *)
(* the tactic invocations are real and run.                             *)
(* ==================================================================== *)
require import AllCore List QFABV IntDiv.

(* -------------------------------------------------------------------- *)
(* An abstract 8-bit element word, with xor. *)
type W8.

op to_bits   : W8 -> bool list.
op from_bits : bool list -> W8.
op of_int    : int -> W8.
op to_uint   : W8 -> int.
op to_sint   : W8 -> int.

bind bitstring to_bits from_bits to_uint to_sint of_int W8 8.

realize gt0_size    by admit.
realize tolistP     by admit.
realize oflistP     by admit.
realize touintP     by admit.
realize tosintP     by admit.
realize ofintP      by admit.
realize size_tolist by admit.

op (+^) : W8 -> W8 -> W8.
bind op W8 (+^) "xor".
realize bvxorP by admit.

(* -------------------------------------------------------------------- *)
(* A length-8 array of elements. [bind array] gives the read/write      *)
(* operators ["_.[_]"]/["_.[_<-_]"], the list view, and the size.       *)
theory A.
  type 'a t.

  op tolist : 'a t -> 'a list.
  op oflist : 'a -> 'a list -> 'a t.
  op "_.[_]"    : 'a t -> int -> 'a.
  op "_.[_<-_]" : 'a t -> int -> 'a -> 'a t.
end A.

bind array A."_.[_]" A."_.[_<-_]" A.tolist A.oflist A.t 8.

realize gt0_size  by admit.
realize tolistP   by admit.
realize oflistP   by admit.
realize eqP       by admit.
realize get_setP  by admit.
realize get_out   by admit.

(* Bring the array read/write operators into scope so the [a.[i]] and
   [a.[i <- v]] bracket notations resolve. *)
export A.

(* ==================================================================== *)
(* get / set                                                            *)
(*                                                                       *)
(* The array read/write operators translate directly once [bind array] *)
(* has registered them. Indices must be concrete (statically known).    *)
(* ==================================================================== *)

(* Reading back the slot just written returns the written value. *)
lemma get_set_same (a : W8 A.t) (v : W8) : a.[3 <- v].[3] = v.
proof. circuit. qed.

(* Writing one slot leaves another untouched. *)
lemma get_set_other (a : W8 A.t) (v : W8) : a.[3 <- v].[5] = a.[5].
proof. circuit. qed.

(* Two writes to the same slot: the last one wins. *)
lemma set_set_same (a : W8 A.t) (v w : W8) : a.[2 <- v].[2 <- w] = a.[2 <- w].
proof. circuit. qed.

(* Writes to distinct slots commute. *)
lemma set_set_swap (a : W8 A.t) (v w : W8) :
  a.[1 <- v].[6 <- w] = a.[6 <- w].[1 <- v].
proof. circuit. qed.

(* ==================================================================== *)
(* init (ainit)                                                         *)
(*                                                                       *)
(* [ainit f] builds the array whose slot [i] holds [f i]. Bound via the *)
(* multi-type [bind op [W8 & A.t] ... "ainit"].                         *)
(* ==================================================================== *)

op init (f : int -> W8) : W8 A.t.
bind op [W8 & A.t] init "ainit".
realize bvainitP by admit.

op get : W8 A.t -> int -> W8 = A."_.[_]".

(* Composing two index permutations under [init] collapses to a single
   pass: reading [_a] at [(i*5)%%8] then re-indexing by [(i*3)%%8] equals
   the direct composite permutation. The circuit checker verifies the
   two array-valued expressions agree slot-by-slot. *)
lemma init_compose (_a : W8 A.t) :
  init (fun i => get (init (fun k => get _a ((k * 5) %% 8))) ((i * 3) %% 8))
  = init (fun i => get _a (((i * 3) %% 8 * 5) %% 8)).
proof. circuit. qed.

(* ==================================================================== *)
(* Arrays in a program                                                  *)
(* ==================================================================== *)

module M = {
  proc swap2 (a : W8 A.t) : W8 A.t = {
    var t : W8;
    t <- a.[0];
    a <- a.[0 <- a.[1]];
    a <- a.[1 <- t];
    return a;
  }
}.

(* Swapping slots 0 and 1 via a temporary is the two commuted writes. *)
lemma hl_swap2 (a_ : W8 A.t) :
  hoare[M.swap2 : a = a_ ==> res = a_.[0 <- a_.[1]].[1 <- a_.[0]]].
proof. proc; circuit. qed.
