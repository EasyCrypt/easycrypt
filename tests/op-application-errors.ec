(* Operator application failures must be diagnosed precisely. Each command
   below is ill-typed; [expect fail "..."] asserts the exact error it
   produces, so the messages are tested for regression. *)

require import AllCore List FSet.

(* --- result type mismatch ------------------------------------------ *)

expect fail "operator `Top.List.filter' cannot be applied to arguments of type:
  [1]: int -> bool
  [2]: int list
its type is
  ('a -> bool) -> 'a list -> 'a list
where the type parameters were inferred as:
  'a = int
it returns a value of type
  int list
but a value of type
  int fset
was expected"
op choose (s : int fset) : int fset =
  List.filter (fun (i : int) => i \in s) [1; 2; 3].

op h : 'a -> 'a * 'a.

expect fail "operator `Top.h' cannot be applied to arguments of type:
  [1]: int
its type is
  'a -> 'a * 'a
where the type parameters were inferred as:
  'a = int
it returns a value of type
  int * int
but a value of type
  int
was expected"
op bad_result : int = h 0.

(* --- argument mismatch --------------------------------------------- *)

expect fail "operator `Top.List.filter' cannot be applied to arguments of type:
  [1]: int -> int
  [2]: int list
its type is
  ('a -> bool) -> 'a list -> 'a list
where the type parameters were inferred as:
  'a = int
its #1 argument is expected to have type
  int -> bool
but is applied to a value of type
  int -> int"
op bad_arg (s : int list) : int list =
  List.filter (fun (i : int) => i) s.

expect fail "operator `Top.List.map' cannot be applied to arguments of type:
  [1]: int -> int
  [2]: bool list
its type is
  ('a -> 'b) -> 'a list -> 'b list
where the type parameters were inferred as:
  'b = int
  'a = int
its #2 argument is expected to have type
  int list
but is applied to a value of type
  bool list"
op bad_ho : bool list =
  List.map (fun (x : int) => x + 1) [true].

expect fail "operator `Top.List.foldr' cannot be applied to arguments of type:
  [1]: int -> bool -> bool
  [2]: int
  [3]: int list
its type is
  ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
where the type parameters were inferred as:
  'b = bool
  'a = int
its #2 argument is expected to have type
  bool
but is applied to a value of type
  int"
op bad_fold : int =
  List.foldr (fun (x : int) (acc : bool) => acc) 0 [1; 2; 3].

(* --- arity mismatch / under-application ---------------------------- *)

expect fail "operator `Top.List.size' cannot be applied to arguments of type:
  [1]: int list
  [2]: int list
its type is
  'a list -> int
where the type parameters were inferred as:
  'a = int
it is applied to 2 argument(s) but takes at most 1"
op bad_arity (s : int list) : int =
  List.size s s.

op k : int -> int -> int.

expect fail "operator `Top.k' cannot be applied to arguments of type:
  [1]: int
it returns a value of type
  int -> int
but a value of type
  int
was expected"
op bad_underapp : int = k 0.

(* --- partial instantiation of type parameters --------------------- *)

op poly : 'a -> 'a -> int.

expect fail "operator `Top.poly' cannot be applied to arguments of type:
  [1]: int
  [2]: bool
its type is
  'a -> 'a -> int
where the type parameters were inferred as:
  'a = int
its #2 argument is expected to have type
  int
but is applied to a value of type
  bool"
op bad_poly : int = poly 0 true + 2.

expect fail "operator `Top.poly' cannot be applied to arguments of type:
  [1]: #a * #b
  [2]: int
its type is
  'a -> 'a -> int
where the type parameters were inferred as:
  'a = #a * #b
its #2 argument is expected to have type
  #a * #b
but is applied to a value of type
  int"
op bad_partial : int = poly (witness, witness) 0.

op poly2 : 'a -> 'b -> 'b.

expect fail "operator `Top.poly2' cannot be applied to arguments of type:
  [1]: int
  [2]: bool
its type is
  'a -> 'b -> 'b
where the type parameters were inferred as:
  'b = bool
  'a = int
it returns a value of type
  bool
but a value of type
  int
was expected"
op bad_poly2 : int = poly2 0 true.

(* --- multiple candidates ------------------------------------------- *)

expect fail "`+' cannot be applied to arguments of type:
  [1]: bool
  [2]: int
the candidates cannot be applied:
  [operator `Top.Xint.+']:
    its #1 argument is expected to have type
      xint
    but is applied to a value of type
      bool
  [operator `Top.Real.+']:
    its #1 argument is expected to have type
      real
    but is applied to a value of type
      bool
  [operator `Top.Int.+']:
    its #1 argument is expected to have type
      int
    but is applied to a value of type
      bool"
op bad_overload : int = true + 1.

expect fail "`+' cannot be applied to arguments of type:
  [1]: int
  [2]: bool
the candidates cannot be applied:
  [operator `Top.Xint.+']:
    its #1 argument is expected to have type
      xint
    but is applied to a value of type
      int
  [operator `Top.Real.+']:
    its #1 argument is expected to have type
      real
    but is applied to a value of type
      int
  [operator `Top.Int.+']:
    its #2 argument is expected to have type
      int
    but is applied to a value of type
      bool"
lemma bad_form : List.size [true] = 0 + true.

theory A. op cand (x : int)  : int  = x. end A.
theory B. op cand (x : bool) : bool = x. end B.
import A B.

expect fail "`cand' cannot be applied to arguments of type:
  [1]: bool
the candidates cannot be applied:
  [operator `Top.B.cand']:
    it returns a value of type
      bool
    but a value of type
      int
    was expected
  [operator `Top.A.cand']:
    its #1 argument is expected to have type
      int
    but is applied to a value of type
      bool"
op bad_multi : int = cand true.

(* --- local variables ----------------------------------------------- *)

expect fail "local variable `x' cannot be applied to arguments of type:
  [1]: int
it has type
  int
it is applied to 1 argument(s) but takes at most 0"
op bad_local : int = let x = 0 in x 1.

expect fail "local variable `g' cannot be applied to arguments of type:
  [1]: bool
it has type
  int -> int
its #1 argument is expected to have type
  int
but is applied to a value of type
  bool"
op bad_local_fun : int =
  let g = (fun (n : int) => n) in g true.

(* --- program variables --------------------------------------------- *)

module M = {
  var xz : int
  var gf : int -> int
  proc f () : unit = {}
}.

expect fail "program variable `M.xz' cannot be applied to arguments of type:
  [1]: int
it has type
  int
it is applied to 1 argument(s) but takes at most 0"
lemma bad_pv     : hoare[M.f : M.xz 0 = 0 ==> true].

expect fail "program variable `M.gf' cannot be applied to arguments of type:
  [1]: bool
it has type
  int -> int
its #1 argument is expected to have type
  int
but is applied to a value of type
  bool"
lemma bad_pv_fun : hoare[M.f : M.gf true = 0 ==> true].

(* --- mixed candidate kinds (program variable + operator) ----------- *)

op mix : bool -> bool.

module N = {
  proc f (mix : bool) : unit = {}
}.

expect fail "`mix' cannot be applied to arguments of type:
  [1]: int
the candidates cannot be applied:
  [program variable `arg']:
    it has type
      bool
    it is applied to 1 argument(s) but takes at most 0
  [operator `Top.mix']:
    its #1 argument is expected to have type
      bool
    but is applied to a value of type
      int"
lemma bad_mix : hoare[N.f : mix 0 = 0 ==> true].

(* --- genuinely unknown operator ------------------------------------ *)

expect fail "no matching operator, named `List.frobnicate', for the following parameters' type:
  [1]: int list"
op unknown (s : int list) : int list =
  List.frobnicate s.

