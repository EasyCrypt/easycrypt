(* Unit tests for the `locate' report that `print' prefixes each object it
   displays with. Uses the `expect "..." by print ...' command
   (String.trim-based comparison). *)

require import Int.

theory A.
  op c : int = 1.

  lemma cP : c = 1 by done.
end A.

theory B.
  op c : int = 2.

  lemma cP : c = 2 by done.
end B.

import A B.

(* the name the object is known under, plus the shortest form that still
   resolves to it *)
expect "(* Int.max (shorten name: max) *)
op max (a b : int) : int = if a < b then b else a." by print op Int.max.

(* a symbolic operator gets its parentheses back, so that the reported name
   is valid syntax again -- `Int.+' does not parse, `Int.(+)' does *)
expect "(* Int.(+) (shorten name: (+)) *)
abbrev (+)  : int -> int -> int = CoreInt.add." by print op (+).

(* a prefix operator keeps its brackets, and takes the parentheses only
   under a namespace -- both forms parse *)
expect "(* Int.([-]) (shorten name: [-]) *)
abbrev [-]  : int -> int = CoreInt.opp." by print op Int.([-]).

(* every homonym gets its own report, right before its declaration -- only
   the one `c' resolves to has a shortest form *)
expect "(* B.c (shorten name: c) *)
op c : int = 2.

(* A.c *)
op c : int = 1." by print op c.

(* same for lemmas *)
expect "(* B.cP (shorten name: cP) *)
lemma cP: B.c = 2.

(* A.cP *)
lemma cP: A.c = 1." by print lemma cP.

(* a name with no namespace prefix says nothing the declaration does not,
   so it gets no report *)
op standalone : int = 0.

expect "op standalone : int = 0." by print op standalone.

(* the untyped `print x' searches every category, and reports in each one
   that answered *)
theory Q.
  type v = int.
  op v : int = 0.
end Q.

expect "* In [type declarations]:

(* Q.v *)
type v = int.

* In [operators, predicates or exceptions]:

(* Q.v *)
op v : int = 0." by print Q.v.

(* [locate] knows nothing about modules or procedures: printing one of
   those gets no report *)
module M = { proc f () : unit = { } }.

expect "module M = {
  proc f() : unit = {}
}." by print module M.

expect "proc f() : unit = {}" by print proc M.f.

(* a name that resolves to nothing keeps the plain `print' diagnostic *)
expect "no object `nosuchop' in the category [operators, predicates or exceptions]"
  by print op nosuchop.
