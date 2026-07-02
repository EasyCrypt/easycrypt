(* clinline (clone-inline) for types.

   A type cloned with the inline-keep override `<=` carries its body and
   is tagged [tyd_clinline]. When such a type is later used as the target
   of a `theory ... <=` override, the consumer receives the *body* of the
   type rather than a reference to it. The two stay convertible; the
   difference is only visible when printing.

   Contrast (checked below with `expect ... by print`):
     - K.t cloned with `type t <= int` (clinline)    -> consumer prints `int`
     - L.t cloned with `type t =  int` (plain alias)  -> consumer prints `L.t`
*)

require import AllCore.

abstract theory BV.
  type t.
end BV.

(* A theory with an abstract subtheory [P] and a use of [P.t]. *)
abstract theory Use.
  clone import BV as P.
  op probe : P.t.
end Use.

(* Two instances of BV: one clinline (<=), one a plain alias (=). *)
clone BV as K with type t <= int.   (* K.t is clinline, body = int *)
clone BV as L with type t =  int.   (* L.t is a plain alias        *)

(* Override Use's subtheory P, once by each, via a `theory <=` override. *)
clone import Use as UK with theory P <= K.
clone import Use as UL with theory P <= L.

(* UK.P.t receives K.t's *body* (K.t is clinline): prints `int`. *)
expect "type t = int." by print type UK.P.t.

(* UL.P.t keeps the reference to L.t (L.t is a plain alias): prints `L.t`. *)
expect "type t = L.t." by print type UL.P.t.
