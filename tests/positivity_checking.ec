(* Simple type *)
type 'a list = [ Nil | Cons of 'a & 'a list ].

type 'a tree = [
  | Leaf
    (* Recursive occurrence within a pre-existing type constructor *)
  | Node of 'a tree list
    (* Positive occurrence in a function *)
  | Fun of (bool -> 'a tree)
].

theory Bad.
type ('a, 'b) permlist = [
 | N of ('a -> 'b) (* Aaaaah *)
 | C of 'a & ('a, 'b) permlist
 | P of ('b, 'a) permlist
].

fail type posrej = [ A | B of (bool, posrej) permlist ].
end Bad.

theory Good.
type ('a, 'b) permlist = [
 | N (* No problem *)
 | C of 'a & ('a, 'b) permlist
 | P of ('b, 'a) permlist list (* For the sake of nesting in a list *)
].

(* this type fails because of the same limitation,
   even though it is in fact strictly positive. *)
fail type posrej = [ A | B of (bool, posrej) permlist ].
end Good.

type ('a, 'b) arr = 'a -> 'b.
type ('a, 'b) orr = ('a, 'b) arr.
fail type 'a u = [ S | U of ('a u, bool) orr ].

type 'a t.
fail type tt = [ N | T of tt t ].
fail type 'a tt = [ N | T of 'a tt tt]. 
