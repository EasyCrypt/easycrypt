(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv
open EcLowCircuits

(* -------------------------------------------------------------------- *)
(* Circuit reasoning on statement judgements, shared by the [circuit]
   rules of every logic: the precondition and the program are translated
   to circuits, and the postcondition is decided by the circuit backend
   ([EcCircuits]). The translation and the decision are deterministic
   functions of the judgement and of its hypotheses (the bindings of the
   environment included), so that a checker can re-run them. *)

(* Raised by the builders of the [circuit] rules when the circuit backend
   does not establish the goal. *)
exception CircuitInvalid

(* Raised by the builders of the hoare [circuit] rules when the
   exceptional postconditions are not empty. *)
exception CircuitExceptions

(* [process_pre hyps ~st P] records in [st] the conjuncts of [P] of the
   form [x = v] ([x] a local program variable) as the value of [x], and
   returns the conjuncts of [P] translatable to circuits, as open circuits
   in that state. The conjuncts of [P] are its top-level conjunctions,
   [all p (iota_ n m)] being the conjunction of [p n], ..., [p (n+m-1)]
   (for [n] and [m] integer literals). *)
val process_pre :
  LDecl.hyps -> st:state -> form -> state * circuit list

(* [solve_post ~st ~pres hyps Q] decides whether each conjunct of [Q]
   (as in [process_pre]; equalities compared bit-wise) holds in the state
   [st] under the assumptions [pres]. Raises [EcCircuits.CircError] when
   a conjunct cannot be translated. *)
val solve_post :
  st:state -> pres:circuit list -> LDecl.hyps -> form -> bool
