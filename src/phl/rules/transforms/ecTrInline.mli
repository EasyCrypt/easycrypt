(* -------------------------------------------------------------------- *)
open EcUtils

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

(* The calls to inline, as a resolved pattern over the statement: [s_pat]
   is a list of [(n, ip)], [n] being the number of instructions skipped
   since the previous selected one (or since the start of the block), and
   [ip] what to do with the selected instruction: inline it ([IPpat], a
   call), or descend into its branches ([IPif], [IPwhile], [IPmatch], one
   sub-pattern per branch, in order). *)
type i_pat =
  | IPpat
  | IPif    of s_pat pair
  | IPwhile of s_pat
  | IPmatch of s_pat list

and s_pat = (int * i_pat) list

type tr_inline = {
  tri_pat       : s_pat;   (* the calls to inline (resolved pattern) *)
  tri_use_tuple : bool;    (* assign a tuple result as a whole *)
}

(* [TrInline { tri_pat = sp; tri_use_tuple = ut }] — inlines the calls
   selected by [sp], at any depth. Each selected call
   [x <- f(e1, ..., en)], with [f] (normalized) defined by
   [proc f(a1, ..., an) = { var l1 ... lk; b; return r }], becomes

     a1', ..., an' <- e1, ..., en;  b';  x <- r'

   where [a1' ... an'], [l1' ... lk'] are fresh program variables added to
   the memory (in this order), [b'] and [r'] are [b] and [r] with the
   parameters and locals renamed to them, and the arguments are assigned
   one by one (when there are as many as parameters), as a tuple
   otherwise. The return assignment is omitted when there is no [x] or no
   [r]. When [x] is a tuple pattern [(x1, ..., xm)] and [not ut], it is
   instead

     t1 <- r'.`1; ...; tm <- r'.`m;  x1 <- t1; ...; xm <- tm

   with [t1 ... tm] fresh program variables named after [x1 ... xm], added
   to the memory after the locals. Calls are inlined in program order, so
   the memory grows in that order. No obligation.

   Fails with "abstract function `f' cannot be inlined" when a selected
   [f] has no concrete definition, and with "invalid inlining pattern"
   when [sp] does not match the statement (a skip out of range, an
   [IPpat] not on a call, a sub-pattern not on an instruction of that
   kind or with the wrong number of branches).

   A selected call inside a loop body is rejected ("function `f' cannot
   be inlined inside a loop") when [f] may read one of its locals before
   writing it: there, the fresh variables are shared by all iterations
   and hold the values left by the previous one, whereas a call starts
   with fresh locals. Otherwise, every read of a fresh variable in the
   inlined code follows a write in the same iteration. *)
type EcPlTransform.transform += TrInline of tr_inline
