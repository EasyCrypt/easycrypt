(* Unfolding of indexed type aliases: [EcEnv.Ty.unfold] must
   substitute the alias's index parameters, not only its type
   parameters (a leaked formal index variable made [foo<:3>] fail to
   unify with its own unfolding). *)

type {n} 'a vec.

type {n} 'a foo = 'a vec<:n>.

(* alias <-> unfolding, concrete index *)
op test1 (x : int foo<:3>) : int vec<:3> = x.
op test2 (x : int vec<:3>) : int foo<:3> = x.

(* symbolic index through an op's index parameter *)
op test3 {n} ['a] (x : 'a foo<:n>) : 'a vec<:n> = x.

(* index arithmetic through the alias *)
op cons {n} ['a] (x : 'a) (xs : 'a vec<:n>) : 'a vec<:n+1>.
op test4 {n} ['a] (x : 'a) (xs : 'a foo<:n>) : 'a foo<:n+1> =
  cons x xs.
