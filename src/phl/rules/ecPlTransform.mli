(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv

(* -------------------------------------------------------------------- *)
(* Program transformations, shared by the transformation rules of every
   logic ([EcHoareTransform], [EcEHoareTransform], [EcBdHoareTransform],
   [EcEquivTransform]).

   A program transformation replaces the program [c] of a judgement by a
   program [c'] that behaves the same, under obligations [O_1 ... O_n],
   and keeps the judgement:

       J [c' : P ==> Q]        O_1 ... O_n
     --------------------------------------
                 J [c : P ==> Q]

   The transformations form a CATALOGUE: [transform] is an open type, each
   entry adds a constructor carrying its RESOLVED parameters (integer
   positions, typed data) and registers the function computing it. An
   entry is a pure, deterministic function of its context and of the
   statement [c]; it acts on the statement only and may extend the memory
   with fresh program variables. The rules record [(transformation,
   parameters)] in their proof-node, and their checkers re-run the entry
   on the goal's own program: the rebuilt subgoals are compared with the
   recorded ones up to conversion (programs up to alpha-equivalence).

   The obligations are ABSTRACT, from the closed set [obligation]; each
   logic's rule states them as premises of its own (see its [.mli]).

   Current catalogue: [EcTrRndSem] (semantic sampling of a straight-line
   suffix), [EcTrRCond] (deciding an [if] / [while]), [EcTrRMatch]
   (deciding a [match], its unframed form), [EcTrIfPush] and
   [EcTrMatchPush] (pushing the continuation of a leading conditional /
   [match] into its branches; the [if] and [match] tactics are push + rule
   on the conditional alone), [EcTrSwap] (moving a block of a possibly
   nested block), [EcTrInline] (inlining procedure calls), [EcTrKill],
   [EcTrAlias], [EcTrSet], [EcTrSetMatch], [EcTrCFold], [EcTrAsgnCase]
   and [EcTrSimplifyIf] (the code transformations), [EcTrFission] /
   [EcTrFusion] (splitting / merging loops), [EcTrUnroll] (unrolling the
   first iteration of a loop), [EcTrSplitWhile] (splitting a loop on an
   extra condition), [EcTrExprChange] (replacing expressions under
   equalities, [proc rewrite]), [EcTrStmtChange] (replacing a fragment
   under a local equivalence, [proc change]), [EcTrCircuitChange]
   (replacing a fragment by a circuit-equivalent one, [proc change
   circuit]) and [EcTrIdAssign] (inserting [x <- x]). Entries live
   in [rules/transforms/], as [EcTr<Name>]. The framed form of [match C k]
   changes the precondition: it is not a transformation, but a separate
   rule of each logic ([Ec<Logic>RMatch]). *)

(* -------------------------------------------------------------------- *)
(* An entry of the catalogue, with its resolved parameters. *)
type transform = ..

(* An obligation of a transformation, about the program [c] it is applied
   to, in the memory of the context (the memory of [c], not the possibly
   extended one of [c']), unless stated otherwise. *)
type obligation =
  | OPrefixPost of prefix_post
  | OLossless   of stmt
  | OExprEq     of expr_eq
  | OLocalEquiv of local_equiv

(* [OPrefixPost { opp_prefix = hd; opp_cond = cond }]: every terminating
   run of [hd] (a prefix of [c]) from the precondition ends in a state
   satisfying [cond].

   [OLossless ks]: the statement [ks] (a fragment of [c], over its memory)
   terminates with probability 1 from every state.

   [OExprEq { oee_locals = xs; oee_lhs = e; oee_rhs = e' }]: in every
   memory of the type of [c'] and for every value of the local
   identifiers [xs], [e] and [e'] evaluate to the same value ([e] and
   [e'] are over the memory of [c'], the [xs] free).

   [OLocalEquiv { ole_locals = xs; ole_orig = s; ole_new = s';
   ole_reads = R; ole_writes = W; ole_modi = M }]: for every value of the
   match-arm locals [xs] in scope at [s] (which [s] may mention), from
   states agreeing on [R] (and, on the side of [s], satisfying the frame:
   the part of the precondition independent from [M], see [frame] below),
   the fragment [s] of [c] (over the memory of [c]) and the fragment [s']
   (over the memory of [c']) end in states agreeing on [W]. *)
and prefix_post = {
  opp_prefix : stmt;     (* the prefix [hd] *)
  opp_cond   : ss_inv;   (* [cond] *)
}

and expr_eq = {
  oee_locals : (EcIdent.t * ty) list;   (* the locals [xs], with their types *)
  oee_lhs    : expr;                    (* [e] *)
  oee_rhs    : expr;                    (* [e'] *)
}

and local_equiv = {
  ole_locals : (EcIdent.t * ty) list; (* the arm locals [xs] in scope *)
  ole_orig   : stmt;       (* the original fragment [s] *)
  ole_new    : stmt;       (* the new fragment [s'] *)
  ole_reads  : EcPV.PV.t;  (* the shared reads [R] *)
  ole_writes : EcPV.PV.t;  (* the observable writes [W] *)
  ole_modi   : EcPV.PV.t;  (* [M]: what may be written before [s] runs *)
}

(* What an entry is given, besides the statement: computed by each logic's
   rule from its own judgement (so that the checker recomputes it from the
   goal). *)
type tr_ctxt = {
  trc_hyps : LDecl.hyps;           (* hypotheses of the goal *)
  trc_env  : env;                  (* its environment *)
  trc_me   : memenv;               (* memory of the transformed program *)
  trc_post : EcPV.PV.t Lazy.t;     (* program variables of [trc_me] read
                                      by the postcondition (for hoare,
                                      including the exceptional ones) *)
  trc_exn  : bool;                 (* the judgement observes exceptions:
                                      a hoare postcondition constraining
                                      some exception
                                      ([EcLowPhlGoal.hs_observes_exn]);
                                      otherwise, raising is as good as
                                      not terminating *)
}

(* The result of an entry: the (possibly extended) memory, the
   transformed statement [c'] and the obligations. *)
type tr_result = {
  trr_me  : memenv;
  trr_s   : stmt;
  trr_obl : obligation list;
}

(* Raised, with a user-facing message, when a transformation does not
   apply (by [apply], or by a rule when an obligation cannot be stated in
   its logic). *)
exception InvalidTransform of string

(* [register f] registers an entry: [f t] is [Some run] for the
   constructors [t] of that entry. *)
val register : (transform -> (tr_ctxt -> stmt -> tr_result) option) -> unit

(* [apply ctxt t c] runs the entry of [t] on [c]. Raises
   [InvalidTransform] when it does not apply (or no entry handles [t]). *)
val apply : tr_ctxt -> transform -> stmt -> tr_result

(* -------------------------------------------------------------------- *)
(* Premises shared by the transformation rules of every logic. *)

(* [frame env m modi pre]: the conjunction of the top-level conjuncts of
   the boolean precondition [pre] that only mention the memory [m] (of the
   transformed program) and are independent from the program variables
   [modi]; [None] when there is none. *)
val frame : env -> memory -> EcPV.PV.t -> form -> form option

(* [f_expr_eq me o]: the premise of [OExprEq o] in every logic,
   [forall &m, forall xs, e = e'], the memory binder being the memory
   identifier of [me] (the memory of the transformed program) and the
   local binders the identifiers [xs] of [o]. *)
val f_expr_eq : memenv -> expr_eq -> form

(* [f_local_equiv env me mt' pre o]: the premise of [OLocalEquiv o] in
   every logic,

     forall xs, equiv [s ~ s' : ={R} /\ frame{1} ==> ={W}]

   with left memory type that of [me] (the memory of [c]), right memory
   type [mt'] (the memory type of [c']), and [frame] computed by [frame]
   from the boolean precondition [pre] of the rule over the memory of [me]
   (no frame when [pre] is [None]). *)
val f_local_equiv :
  env -> memenv -> memtype -> form option -> local_equiv -> form
