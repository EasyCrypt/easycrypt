require import Int.

(* Security check: quotations are OFF by default.  A handler IS available
   (handlers/calc.py beside this file), so the ONLY reason this must fail is
   that -enable-quotations was not passed.  This file lives in a 'kodirs'
   scenario that deliberately omits the flag; it is expected to fail. *)
op forty_two = {% calc 6 * 7 %}.
