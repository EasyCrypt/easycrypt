(* Record field projections must resolve from the record type alone, even when
   the theory declaring the type (and hence the projection operator) is not
   imported in the current scope. See issue #1011. *)

theory T.
  type t = { f : unit }.
  op e : t.
end T.

(* `T` is not imported: `f` is not in scope by its bare name, but the
   projection is determined by the type of `T.e`. *)
op test = T.e.`f.

(* Same field name in two unrelated records: the known type disambiguates. *)
theory A. type t = { g : int  }. op e : t. end A.
theory B. type t = { g : bool }. op e : t. end B.

op ta : int  = A.e.`g.
op tb : bool = B.e.`g.

(* Projection through a clone that inlines the record type. *)
theory U.
  type u.
  op e : u.
end U.

type u' = { h : int }.

clone U as U' with type u <- u'.

op tc : int = U'.e.`h.
