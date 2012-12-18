(* Copyright Grégoire Henry 2011.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

(* A cluster is the finite set of recursive class instances needed for
   deriving a "regular" recursive type declaration. For example:

   type 'a t = A of 'a | B of 'a * 'a t | I of int t

   The corresponding cluster is:

   { 'a t ; int t }.

   For multiple recursives declarations, we may group clusters by the
   set of free variables involved in the required instances. For
   example:

   type 'a t1 = ('a, int) t2
   and ('a, 'b) t2 = A of 'a t1 | B of 'b deriving (Show)

   Types declaration t1 and t2 share the same clusters:

   { 'a t1; ('a, int) t2 }.

   This notion of clusters allows to be less restrictive with
   recursive type declaration than previous version of deriving. It's
   still not sufficient for handling "non-regular" datatypes like:

   type 'a nested = Z of nested | S of ('a * 'a) nested

   because the set of required instance would be infinite.

*)

type cluster = {
  params: Type.param list;
  decls: Type.decl list;
  instances: (Type.name * Type.expr list) list;
}

val make: Type.decl list -> cluster list
