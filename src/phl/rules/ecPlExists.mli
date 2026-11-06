(* -------------------------------------------------------------------- *)
open EcAst

(* -------------------------------------------------------------------- *)
(* Computations shared by the existential rules of every logic
   ([Ec<Logic>Exists]): eliminating the existentials of a precondition,
   and quantifying a precondition over the values of formulas. *)

(* [prenex_exists ?bound P] is [(xs, P')], [exists xs, P'] being [P] with
   its existential binders pulled to the front, as computed by
   [EcFol.destr_exists_prenex] (binders freshened): with [bound = n], at
   most [n] leading binders (also under the left operand of an ehoare
   precondition [_ `|` _]); with no bound, every binder reachable through
   [/\], [\/], the right operand of [=>] and the branches of [if] too. It
   is [([], P)] when there is no binder to pull. [P] entails [exists xs,
   P'] (types being inhabited), which makes the elimination rules sound. *)
val prenex_exists : ?bound:int -> form -> bindings * form

(* [intro_binders fs] pairs each formula of [fs] with a fresh local named
   after it when it is a program variable ([x] or [x_L] / [x_R]), [f]
   otherwise. *)
val intro_binders : inv list -> (EcIdent.t * inv) list

(* [intro_pre ~ehoare xs P], [xs] given by [intro_binders fs], is the
   precondition quantified over the values of [fs]:
   - [exists xs, (/\_i xs_i = fs_i) /\ P] ([true] for an empty
     conjunction);
   - [(exists xs, /\_i xs_i = fs_i) `|` P] when [ehoare]. *)
val intro_pre : ehoare:bool -> (EcIdent.t * inv) list -> inv -> inv
