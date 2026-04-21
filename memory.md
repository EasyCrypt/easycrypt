# Indexed-types branch — work-in-progress notes

This file tracks ongoing decisions and progress on the `indexed-types`
branch. The end goal is to add integer-indexed types to EasyCrypt:
types parametrised by both type variables and integer indices, with a
small index language and decidable equality on indices.

## Confirmed design decisions

- **`tindex` grammar.** `TIVar | TIConst zint | TIAdd | TIMul`
  ([src/ecAst.ml:60-64](src/ecAst.ml#L60-L64)). No `TINeg`/`TISub`;
  surface syntax must reject subtraction.
- **Indices are non-negative integers (ℕ).** `TIConst` should be
  guarded against negative `zint`.
- **Equality is decided by polynomial normal form.** Normalize to
  sorted sum-of-monomials with `EcBigInt` coefficients (all ≥ 1), then
  compare structurally. No SMT.
- **`TIVar` shares the term-level identifier namespace with `int`
  formula vars.** A substitution `n ↦ φ` is required at construction
  time to have `φ` representable as a `tindex` — i.e.
  `tindex_of_form φ` must succeed. `tindex_subst` may then
  `Option.get` the conversion.
- **Indices appear on every polymorphic declaration:** tydecls,
  operators (incl. predicates / abbreviations / notations),
  axioms / lemmas. Not modules.
- **No constraint annotations in the MVP.** `'a vec[n-3]` is not
  expressible (no subtraction); `'a vec[0]` is allowed and just
  useless.
- **SMT export: punted.** Block proof obligations touching indexed
  types until a later phase.

## Phase 0 — Stop the bleeding (DONE)

Goal: clean `dune build` with the existing `targs` /
`ty_params = {idxvars; tyvars}` data model, without changing semantics.

### What changed

- [src/ecInductive.ml](src/ecInductive.ml) — fixed the stray `)`
  syntax error at line 188; renamed `args.indexes` → `args.indices`;
  threaded `tyd_params.tyvars`; switched constructor calls to keyword
  form (`tconstr ~tyargs`, `f_op ~tyargs`).
- [src/ecDecl.ml](src/ecDecl.ml) — restored `gen_op` / `mk_op` bodies
  to match the existing mli (the WIP rewrite referenced unbound names
  `tparams` / `ty` / `lc` / `op_params`); threaded `tparams.tyvars` in
  `ty_instantiate` and `axiomatized_op`; `ax_tparams` now wraps a
  `ty_params` record.
- [src/ecUnify.ml](src/ecUnify.ml) — `UniEnv.create` / `opentvi` /
  `subst_tv` / `tparams` now consume / produce `ty_params` records
  (extracting `.tyvars` internally; `ue_decl` still stores the tyvar
  list).
- [src/ecEnv.ml](src/ecEnv.ml) — `Op.reduce`, `Ax.instantiate`,
  `Ty.unfold`, `Ty.scheme_of_ty`, `Ty.get_top_decl` thread
  `targs.types` / `tyvars` correctly; algebra instances and TC-op
  helpers wrap empty `ty_params`.
- Mechanical migration across
  [src/ecCallbyValue.ml](src/ecCallbyValue.ml),
  [src/ecReduction.ml](src/ecReduction.ml),
  [src/ecMatching.ml](src/ecMatching.ml),
  [src/ecPV.ml](src/ecPV.ml),
  [src/ecHiInductive.ml](src/ecHiInductive.ml),
  [src/ecHiGoal.ml](src/ecHiGoal.ml),
  [src/ecLowGoal.ml](src/ecLowGoal.ml),
  [src/ecProofTyping.ml](src/ecProofTyping.ml),
  [src/ecProofTerm.ml](src/ecProofTerm.ml),
  [src/ecSearch.ml](src/ecSearch.ml),
  [src/ecTyping.ml](src/ecTyping.ml),
  [src/ecScope.ml](src/ecScope.ml),
  [src/ecTheoryReplay.ml](src/ecTheoryReplay.ml),
  [src/ecAlgTactic.ml](src/ecAlgTactic.ml),
  [src/ecSection.ml](src/ecSection.ml),
  [src/ecSubst.ml](src/ecSubst.ml),
  [src/ecSmt.ml](src/ecSmt.ml),
  [src/ecPrinting.ml](src/ecPrinting.ml),
  [src/ecThCloning.ml](src/ecThCloning.ml), and several
  [src/phl/](src/phl/) modules:
    - `tyd_params` / `op_tparams` / `ax_tparams` → `.tyvars`
    - `targs` consumers → `.types` / `.indices`
    - positional `tconstr p tys` / `e_op p tys` / `f_op p tys` →
      keyword form (`~tyargs:` / `~indices:`)
    - `[]` placeholders for `ty_params` → `{idxvars=[]; tyvars=[]}`

### Notable Phase-0 design choices

- Kept `ue_decl : EcIdent.t list` inside `ecUnify` (only tyvars),
  wrapping into `ty_params` at the boundary.
- Several places that consume `targs` for type comparison currently
  `assert (List.is_empty tys.indices)` (e.g. `ecMatching`,
  `ecCallbyValue`, `ecReduction`'s rule patterns, `ecSmt`) — explicit
  panics where Phase 1 will replace with proper polynomial-equality
  logic.
- SMT translation now hard-asserts no indices (per the SMT-punt
  decision); a cleaner user-facing error belongs to Phase 5.

## Roadmap (remaining phases)

### Phase 1 — Polynomial normal form & equality (DONE)

#### What changed

- [src/ecAst.ml](src/ecAst.ml) — added `tindex_canonical` record
  (`{cn_konst : zint; cn_mons : (mono * zint) list}` with `mono =
  (ident * exponent) list`), the helpers `mono_compare` / `mono_mul`
  / `mons_normalize` / `canonical_const` / `canonical_var` /
  `canonical_add` / `canonical_mul`, and the entry point
  `tindex_canonicalize`. Coefficients are stored as `EcBigInt.zint`
  with the invariants `cn_konst ≥ 0`, every `mons` coefficient ≥ 1,
  `cn_mons` strictly sorted by `mono_compare`. `canonical_const`
  guards against negative `TIConst` with `invalid_arg`.
- `tindex_equal` now does `(==)` first, then compares canonical
  forms; `tindex_hash` hashes the canonical form so hashconsing of
  `Tconstr` agrees with equality.
- `targs_equal` checks lengths before `List.all2` (previously could
  raise `Invalid_argument`).
- [src/ecAst.mli](src/ecAst.mli) — exposed `tindex_hash`.
- [src/ecUnify.ml](src/ecUnify.ml) — fixed the inverted-polarity bug
  in the unification of `Tconstr` arms (was `if all2 ... then
  failure ()` instead of `if not all2`); now also length-checks
  indices before iterating types.
- [src/ecReduction.ml](src/ecReduction.ml) —
  `EqTest_base.for_targs` actually compares indices (previous FIXME).

#### Verified

Built `dune build`, then ran an ephemeral smoke executable (deleted
after success) covering: commutativity (`n+1 ≡ 1+n`), associativity
(`(n+m)+1 ≡ n+(m+1)`), distribution + constant folding
(`(n+1)·2 ≡ 2n+2`), monomials (`n·n`), binomial expansion
(`(n+m)² ≡ n²+2nm+m²`), inequality (`n ≢ n+1`, `2 ≢ 3`), and hash
consistency between equal canonical forms.

#### Deferred from Phase 1

- Index unification variables (a `TIUnivar` constructor and
  participation in `EcUnify.UF`) — only needed if Phase 3 lets users
  elide indices at applications. Defer until parser work surfaces a
  concrete need.

### Phase 2 — Substitution & FV (DONE)

#### What changed

- [src/ecCoreFol.ml](src/ecCoreFol.ml) + [src/ecCoreFol.mli](src/ecCoreFol.mli)
  — added `tindex_of_form : form -> tindex option` recognising the
  polynomial fragment over ℕ (`Fint n` with `n ≥ 0`, int-typed
  `Flocal`, `p_int_add`, `p_int_mul`); returns `None` on anything
  else.
- [src/ecCoreSubst.ml](src/ecCoreSubst.ml) — `is_ty_subst_id` now
  also checks `Mid.is_empty s.fs_loc`, since indices share the
  formula-locals namespace and so `fs_loc` can affect types via
  `Tconstr` indices. `tindex_subst` consults `s.fs_loc` per `TIVar`,
  converts via `tindex_of_form`, and panics with a descriptive
  message if a binding is non-polynomial. `targs_subst`'s
  short-circuit follows automatically.
- [src/ecCoreSubst.mli](src/ecCoreSubst.mli) — exposed
  `tindex_subst`.
- [src/ecSubst.ml](src/ecSubst.ml) — same treatment for
  `subst_tindex` against `sb_flocal`.
- [src/ecAst.ml](src/ecAst.ml) — added `tindex_fv_acc` / `tindex_fv`
  (each `TIVar` contributes its identifier with multiplicity 1).
  `targs_fv` now folds over `indices` too. `Hsty.fv` already routed
  through `targs_fv`, so `ty.ty_fv` now includes index-variable
  identifiers; `Fsubst.f_subst_local`'s per-formula
  `Mid.mem x f.f_fv` short-circuit therefore triggers correctly on
  types whose `Tconstr` carries `TIVar x`.
- [src/ecAst.mli](src/ecAst.mli) — exposed `tindex_fv`, `targs_fv`.

#### Verified

Built `dune build`, then ran an ephemeral smoke executable (deleted
after success) covering:
- `fv(n*m+1) = {n, m}` and `k ∉ fv`.
- `targs_fv` carries indices.
- `(n+1)[n:=5] ≡ 6` (constant folds via canonicalisation).
- `(n+1)[n:=1+m] ≡ m+2` (substitution composes with normalisation).
- `(2n+nm)[n:=5] ≡ 10+5m`.
- `targs_subst` actually rewrites `TIVar`.
- `ty_fv` of a `Tconstr` with an index reports the index variable.

#### Notable Phase-2 design choices

- `tindex_subst` does not re-canonicalise after substitution; the AST
  may hold non-canonical shapes (e.g. `(1+m)+1` rather than `m+2`)
  but `tindex_equal` / `tindex_hash` always canonicalise lazily, so
  hashconsing of `Tconstr` still identifies them. Pretty-printing
  (Phase 6) will canonicalise for display.
- Substitution looks at `fs_loc` only; `fs_eloc` (expression-only
  bindings) is not consulted. `f_bind_rename` writes both maps so
  α-renaming still propagates into indices.

#### Risk left for later

- Audit of `f_bind_local` callers for the substitution invariant: if
  any pass binds an `int`-typed local to a non-polynomial formula and
  that local later appears as a `TIVar` inside a type, EasyCrypt will
  crash mid-proof from `tindex_subst`. Worth a tactical sweep before
  merging to main.

### Phase 3 — Parser & typing (DONE)

#### Final concrete syntax

- **Index binders** are plain identifiers (no apostrophe) inside
  `[...]`, e.g. `type [n m] ('a, 'b) vec.`. On op / pred / axiom /
  lemma headers, `[...]` accepts a *mixed* list — apostrophe-prefixed
  → tyvar, plain → index — bucketed in the parser prelude:
  `op f [n 'a] (xs : 'a vec<:n>) : 'a vec<:n+1>`.
- **Index applications** use `<: ... >` framing (LTCOLON / GT), e.g.
  `'a vec<:n+1, m*2>`. We avoid `[...]` here because it would
  shift/reduce-conflict with the codepos brackets in
  `module M = N with { proc f [ var x : T [..] ] }`. The framing also
  matches the existing operator type-arg syntax `f<:int>`.
- **Index-expression sub-grammar**: literals, identifiers, `+`, `*`
  with standard precedence. The grammar guarantees only the
  polynomial fragment.
- **Disambiguation rule** (shared namespace): inside `[...]` and
  `<:...>` an identifier is read as an index variable; everywhere
  else it's a formula/expression local. Apostrophe-prefixed names are
  always type variables.

#### What changed

- [src/ecParsetree.ml](src/ecParsetree.ml) — `pindex_r` / `pindex`
  added, mutually recursive with `pty_r`. `PTapp` now carries
  `pindex list`. `ptydecl` / `poperator` / `ppredicate` / `paxiom`
  each grow an `*_idxvars : psymbol list` field.
- [src/ecParser.mly](src/ecParser.mly) — `idxvars_decl` (tydecl
  prefix), `idx_args` (postfix `<: ... >` on `simpl_type_exp`),
  `pindex` sub-grammar, `mixed_tyvars_item` / `mixed_tyvars_decl`
  (mixed binder list), and a `bucket_mixed` helper in the prelude.
  `tyd_name`, `operator`, `predicate`, `lemma_decl` updated to
  produce the new fields.
- [src/ecTyping.ml](src/ecTyping.ml) + [.mli](src/ecTyping.mli) —
  `transtyvars` gains `?idxparams:psymbol list`. `transtindex`
  translates a `pindex` to a `tindex`, looking variables up via
  `EcUnify.UniEnv.getnamed_idx`. `transty` `PTapp` validates index
  arity and translates each index argument. New `tyerror` variants:
  `InvalidIndexAppl`, `UnboundIndexVariable`, `DuplicatedIndexVar`,
  with printer entries in
  [src/ecUserMessages.ml](src/ecUserMessages.ml).
- [src/ecUnify.ml](src/ecUnify.ml) + [.mli](src/ecUnify.mli) —
  `unienv` carries a separate `ue_idxnamed` / `ue_idxdecl`. New
  `getnamed_idx`. `tparams` propagates `idxvars` into the returned
  `ty_params`.
- [src/ecScope.ml](src/ecScope.ml) — tydecl path threads
  `pty_idxvars` for abstract / alias bodies, refuses indices on
  datatype / record with a clean error. Op + axiom call sites pass
  `~idxparams`.
- [src/ecHiPredicates.ml](src/ecHiPredicates.ml) — predicate-decl
  passes `~idxparams`.
- [src/ecThCloning.ml](src/ecThCloning.ml) + [.mli](src/ecThCloning.mli)
  — new `CE_IndexedNotYetSupported` clone-error; `ty_ovrd` refuses
  cloning of indexed types with a clean printer entry.
- [tests/indexed-types.ec](tests/indexed-types.ec) — regression
  exercising tydecl binders + applications, op / pred / axiom
  binders.

#### Verified

- `_build/default/src/ec.exe compile -boot tests/indexed-types.ec`
  succeeds (12 indexed-type declarations and 3 indexed
  op/pred/axiom binders).
- Ad-hoc negative cases: unbound index, index arity mismatch,
  duplicated index variable, cloning of an indexed type — each
  raises a clean message at the right location.

#### Notable Phase-3 design choices

- The `<:...>` framing for index applications was chosen over the
  user-preferred `[...]` after a real shift/reduce conflict surfaced
  in `mod_update_fun`. Reuses the existing operator-tvi framing.
- `pindex` is its own AST (not a re-use of `pformula`) to avoid
  pulling `pformula` into `pty_r`'s mutual recursion.
- `transtyvars` keeps its existing positional `(loc, tparams option)`
  argument; the new `?idxparams` is an optional keyword. Backward
  compatible — every existing call site still compiles unchanged.

#### Risks left for later

- **Index inference at op application sites.** Indexed ops *declare*
  fine but *calling* them doesn't yet work — `EcUnify` has no
  `TIUnivar` machinery, so an op's index parameter stays as a fresh
  ident that can't be unified against the caller's index expression.
  This is the deferred Phase-1 question (introduce `TIUnivar`,
  decide polynomial-with-univars unification). Without it, indexed
  ops are mostly cosmetic.
- **Datatype / Record indexed types.** Refused with a clean error in
  `ecScope`. Adding support is mostly threading idxvars through
  `ecHiInductive.trans_datatype` / `trans_record`.
- **Cloning of indexed types/ops.** Refused with `CE_IndexedNotYetSupported`.
  Real support needs index-instantiation surface syntax in
  `clone with`, plus a way to substitute indices through the cloned
  declarations.

### Phase 3.5 — Index inference at op-application sites (DONE)

Added the `TIUnivar`-based machinery that Phase 3 deferred. Without
this, indexed ops could be *declared* but not *called* — the unifier
had no way to instantiate an op's index parameter against the
caller's index expression.

#### What changed

- [src/ecAst.ml](src/ecAst.ml) + [.mli](src/ecAst.mli) — new
  `TIUnivar of EcUid.uid` variant on `tindex`. The canonical-form
  monomial key is now `tindex_var = TVVar of EcIdent.t | TVUni of
  EcUid.uid`, so univars are first-class atoms in the polynomial.
  New helpers `tindex_naked_univar` (detects `TIUnivar u` modulo
  canonicalisation) and `tindex_occurs_univar` (occurs check).
  `tindex_canonicalize`, `tindex_fv_acc`, `dump_tindex` extended.
- [src/ecCoreSubst.ml](src/ecCoreSubst.ml) +
  [.mli](src/ecCoreSubst.mli) — `f_subst` gains `fs_idx : tindex
  Mid.t` (op-application instantiation, ident → tindex) and `fs_iu :
  tindex Muid.t` (univar resolution after unification).
  `tindex_subst` consults both.
  **Critical fix**: `ty_subst`'s `Tconstr` case now substitutes
  through `targs.indices` directly; the previous `ty_map` catch-all
  left them untouched, which silently dropped the op-application
  index substitution. This was the immediate cause of every "no
  matching operator" error on indexed op calls.
- [src/ecUnify.ml](src/ecUnify.ml) + [.mli](src/ecUnify.mli) —
  `unienv_r` gains `ue_iuf : tindex Muid.t` (assignments) and
  `ue_iuf_alloc : Suid.t` (alloc tracking, for the close-time
  check). `unify_core` rewritten to take a `unienv` directly and
  handle a new `IxUni` work-list case. `pb` extended to
  `[ TyUni | IxUni ]`. `idx_fresh` allocates fresh TIUnivars;
  `openidx` produces the ident → univar substitution map; `openty_r`
  threads it. `closed`/`close` now also require all index univars
  resolved; new `iu_close` / `iu_assubst` expose the assignment map.
- [src/ecTyping.ml](src/ecTyping.ml) + [.mli](src/ecTyping.mli) —
  `unify_or_fail` handles `IxUni`; new `IndexMismatch` tyerror with
  a printer in [src/ecUserMessages.ml](src/ecUserMessages.ml).
- [src/ecTypes.mli](src/ecTypes.mli) — exposed `dump_tindex`.
- [tests/indexed-types.ec](tests/indexed-types.ec) — extended with
  the polynomial-equality regression: single-call `cons`, the
  chained `concat (cons x ys) zs`, two variants annotated with
  `(n+1)+m` vs `n+(1+m)` proving normal-form equality across
  associativity.

#### MVP scope

- **Handled**: "naked `TIUnivar` ≟ arbitrary polynomial"
  (with occurs check), and canonical-equality after univar
  resolution. Covers the common chained-op pattern.
- **Not handled**: general polynomial unification.
  `?u + 1 ≟ n` would need to invert subtraction; refused with
  `IndexMismatch`.

#### Verified

55 declarations in `tests/indexed-types.ec` compile, including
`single`, `test1` (`(n+1)+m`) and `test2` (`n+(1+m)`).
Negative case (`vec<:n+2>` annotated as the result of `cons x ys`)
errors out cleanly (with a slightly misleading "no matching
operator" message — Phase-6 polish issue).

### Phase 4 — Theories & smoke tests (DONE)

Implemented cloning of indexed types and extended the regression
accordingly. `theories/Array.ec` migration deliberately skipped for
the first landing.

#### Final clone-with-type syntax

`clone T as T2 with type [k] 'a vec = body` — `[k]` is the optional
idxvar list (mirroring tydecl binder syntax), body is a type
expression that may reference the idx binders (and the tyvars).
Applied textually when `vec<:e>` occurs in the source theory: the
body's idx binders get bound to `e`.

#### What changed

- [src/ecParsetree.ml](src/ecParsetree.ml) — `ty_override_def`
  widened from `psymbol list * pty` to
  `psymbol list * psymbol list * pty` (idxvars, tyvars, body).
- [src/ecParser.mly](src/ecParser.mly) — `clone_override`'s TYPE
  rule accepts an optional `[<idxvars>]` prefix; reuses the existing
  `idxvars_decl` from Phase 3.
- [src/ecSubst.ml](src/ecSubst.ml) + [.mli](src/ecSubst.mli) —
  `subst` gains `sb_idxvar : tindex Mid.t`. `sb_tydef` widened to
  `(idxvars, tyvars, body)`. `subst_tindex` consults `sb_idxvar`
  first (then `sb_flocal` fallback). `subst_ty`'s `Tconstr`-with-
  tydef branch binds *both* the source idxvars (to `ta.indices`)
  and tyvars (to `ta.types`) before substituting through the body.
  `add_tydef`'s tuple widened correspondingly.
- [src/ecThCloning.ml](src/ecThCloning.ml) +
  [.mli](src/ecThCloning.mli) — `ty_ovrd` checks index *and* type
  arity. The Phase-3 blanket-refusal `CE_IndexedNotYetSupported` is
  replaced by the more precise `CE_IdxArgMism` (with a printer in
  [src/ecUserMessages.ml](src/ecUserMessages.ml)).
- [src/ecTheoryReplay.ml](src/ecTheoryReplay.ml) — `BySyntax` case
  threads `nidxs` through `transtyvars` and into the `add_tydef`
  tuple.
- [src/ecEnv.ml](src/ecEnv.ml), [src/ecAlgTactic.ml](src/ecAlgTactic.ml),
  [src/ecSection.ml](src/ecSection.ml),
  [src/ecScope.ml](src/ecScope.ml) — mechanical updates to existing
  `add_tydef` callers (widen `(ids, ty)` → `(idxs, ids, ty)`).
- [tests/indexed-types.ec](tests/indexed-types.ec) — added three
  indexed-type clone cases: drop-the-index to `int`, propagate as
  `'a coll<:k>`, use a polynomial `'a coll<:k+1>`.

#### Verified

77 declarations in `tests/indexed-types.ec` compile (was 55 after
Phase 3.5). `CE_IdxArgMism` correctly catches wrong-arity idx-binder
lists.

#### Gaps worth flagging

- Reaching *into* a cloned theory to call ops whose signature got
  touched by an indexed-type override is awkward: `T2.make_vec` came
  back as "unknown variable" in experimentation. Looks orthogonal to
  indexed types — likely a clone-with-substitution / namespace
  artefact — but worth a note.
- No explicit index-instantiation syntax at op call sites
  (`f<:idx, ty>`) yet; tests that need index-passing at the call
  site rely on inference. A Phase-6 polish could add this.

### Phase 5 — SMT gating (DONE)

Replaced the two `assert (List.is_empty *.indices)` panics in
[src/ecSmt.ml](src/ecSmt.ml) (`trans_ty` for `Tconstr`,
`trans_app` for `Fop`) with `raise CanNotTranslate`. Hoisted the
`CanNotTranslate` exception declaration above `trans_ty` so both
call sites are in scope. Wrapped `check`'s `init` and the inner
`make_task` call in `try/with CanNotTranslate` handlers — the user
now sees a `SMT: skipped goal containing constructs not yet
exported to Why3 (e.g. indexed types)` warning followed by
`cannot prove goal`, rather than an anomaly crash.

Verified: `lemma … (x y : 'a vec<:1>) : x = y \/ x <> y by smt()`
fails cleanly.

Out of scope (per the original Phase-0 punt): actually translating
indexed types to Why3 — would need monomorphisation per concrete
index used in the goal, or a polymorphic Why3 export taking int
arguments.

Other vestigial `assert (List.is_empty *.indices)` panics survive
in [src/ecReduction.ml:796](src/ecReduction.ml#L796),
[src/ecInductive.ml:161](src/ecInductive.ml#L161),
[src/ecInductive.ml:181](src/ecInductive.ml#L181),
[src/ecMatching.ml:685](src/ecMatching.ml#L685). These are not on
the SMT path — they belong in the Phase-6 polish pass.

### Phase 6 — Polish (DONE)

#### What changed

- [src/ecPrinting.ml](src/ecPrinting.ml) — new `pp_tindex_atom` /
  `pp_tindex_prod` / `pp_tindex_sum` / `pp_tindex` with
  `*`-tighter-than-`+` precedence. `pp_type_r`'s `Tconstr` branch
  now emits a `<:e, ...>` suffix when the type application carries
  indices. Errors and transcripts that formerly printed `'a vec`
  for `vec<:n>` (dropping the index entirely, a Phase-0 placeholder)
  now show `'a vec<:n>`.
- [src/ecReduction.ml](src/ecReduction.ml) — the Phase-0
  `assert (List.is_empty ta.indices)` in user-rewrite-rule matching
  (around line 796) becomes `if not empty then raise NotReducible`.
  Indexed-op heads in a rewrite rule no longer crash; they just
  fail to match.
- [src/ecMatching.ml](src/ecMatching.ml) — the Phase-0 assert in
  `Fop` pattern matching (line 685) becomes a proper length +
  polynomial-equality check, with a clean `failure ()` on mismatch.

#### Left as-is (deliberate)

- The two asserts in
  [src/ecInductive.ml:161](src/ecInductive.ml#L161) and
  [src/ecInductive.ml:181](src/ecInductive.ml#L181) — they guard a
  recursive-positivity case where the type being defined references
  itself. Since Phase-3 Slice-A refuses indexed binders on
  datatype/record declarations, the self-reference cannot carry
  indices; the asserts are "should never happen" internal-invariant
  guards.
- `IndexMismatch` error messages still use `EcTypes.dump_tindex`
  (the internal serialisation). Swapping to `EcPrinting.pp_tindex`
  would require ecUserMessages to gain a `PPEnv` dependency, which
  is out of proportion for an edge-case message. Acceptable for now.
- `CHANGELOG` update: out of scope, that's release admin.

#### Known remaining gaps (documented but not scheduled)

(none — Gaps B, C, F all landed.)

#### Plan for the remaining gaps (B → C → F)

Original A–F plan: A, D, E landed in the post-Phase-6 batch. The
remaining three are scheduled as follows.

- **Gap B — polynomial unification beyond naked TIUnivar.** Today
  only `?u = poly` is solved. Extend `IxUni` work-list to handle
  `?u + k = poly` and (more generally) any equation where exactly
  one TIUnivar appears in `lhs - rhs` with coefficient ±1 — solve
  `?u := ±(poly - other)` and fail if the result would be negative
  or non-integer. Defer multi-univar Diophantine to a separate
  constraint-set effort; not motivated by any current example.
  Files: [src/ecUnify.ml](src/ecUnify.ml) (`unify_core` IxUni case).
  Effort: ~0.5d.
- **Gap C — indexed datatypes / records (non-refining).** Lift the
  Phase-3 Slice-A refusal in [src/ecHiInductive.ml](src/ecHiInductive.ml)
  and the datatype/record paths in [src/ecScope.ml](src/ecScope.ml).
  Constructor signatures may reference idxvars; pattern match does
  *not* refine the index. Document explicitly that `vec<:0>` admits
  a `VCons`-shaped value at the type level; matches OCaml/Haskell
  parametric ADT semantics. Index-refining matches are a separate,
  much bigger feature (true dependent typing) and out of scope.
  Effort: ~1.5d (datatypes), records similar but smaller.
- **Gap F — SMT translation of indexed types.** Default strategy:
  monomorphize per concrete index. `'a vec<:e>` with closed `e`
  becomes a fresh memoized Why3 sort `vec_<canon(e)> 'a`; goals
  with free index variables still hit `CanNotTranslate`. Add a
  per-theory `[smt erase indices]` pragma as escape hatch for
  theories where the user has manually discharged the index
  discipline (drops indices, translates `'a vec<:e>` → `'a vec`).
  Files: [src/ecSmt.ml](src/ecSmt.ml) (the two `CanNotTranslate`
  raise sites, `trans_ty` Tconstr case, plus a small monomorphize
  cache module). Effort: ~1d for the default; +0.5d for the pragma.

Order: **B → C → F** (B is smallest and broadens unification;
C is the largest scope expansion but unblocks real ADT users;
F lands last to translate everything we now support).

### Post-Phase-6 — gaps B / C (DONE)

- **B** — polynomial unification beyond naked TIUnivar.
  New `EcAst.tindex_solve_for_univar` walks the signed difference
  of two canonical polynomials and returns `Some (u, value)` when
  exactly one TIUnivar has non-zero net coefficient ±1, every mixed
  monomial cancels, and the residual is non-negative. Wired into
  `unify_ix` *after* the original "naked univar = anything" fast
  path (the fast path stays because it handles `?u = ?v` which the
  new function refuses — two univars with non-zero net). MVP scope
  excludes multi-univar Diophantine and `?u + 1 = n` (free n) where
  the residual could be negative without symbolic guarantees.

  **Multi-univar Diophantine is a deliberate non-goal, not a punt.**
  Equations like `?m + ?n = 5` admit every `(k, 5-k)` for
  `0 <= k <= 5` as a nat solution — no canonical answer, nothing
  to "prefer". Guessing one would be wrong; the unifier correctly
  refuses. The MVP workaround is explicit index instantiation at
  the call site: `make_sum[:2, 3]` instead of bare `make_sum`. If
  ever revisited, the only sensible option is
  **constraint-accumulate-and-commit** — collect `?m + ?n = 5` as
  a pending equation and commit once a later context (arg type,
  scrutinee, …) pins one univar and makes the solution unique.
  Worth building only if a real use case surfaces; until then,
  explicit `[:...]` is the answer.
- **C** — non-refining indexed datatypes and records.
  `EcHiInductive.trans_datatype` and `trans_record` now take an
  optional `~idxparams` argument; `EcScope.add_types` threads it
  through both paths (the previous `no_indices_for` refusal is
  removed). Constructor and projector signatures in `EcEnv` build
  their result type as `tconstr ~indices ~tyargs path`, so
  `INil : 'a vec<:n>` is registered correctly. The positivity
  checker drops its `args.indices = []` asserts: indices play no
  role in positivity since the recursion is on the type, and indices
  carry no embedded type information.

  Match elaboration in `EcTyping.trans_branch` (and the matchfix
  twin in `EcHiInductive`) was bug-prone for 0-field constructors:
  `opentys` was being called with empty field list, allocating
  fresh index univars that never appeared in any unified type and
  so stayed dangling at `closed`-check time. Fix: prepend a hand-
  built result type to the opened list, anchoring the freshly
  allocated univars to a type that participates in the subsequent
  unification against the scrutinee's index.

  Out of scope (deliberate): index refinement on match. Pattern
  matching does not learn anything about the scrutinee's index from
  the constructor that fired; e.g., a `vec<:0>` value still admits
  an `ICons`-shaped pattern at the type level. Matches OCaml/Haskell
  parametric ADT semantics. True dependent matching is a separate,
  much larger feature and not on the roadmap.

  Also out of scope: **per-constructor result indices** (GADT-style).
  Every constructor's result type is hard-wired to
  `tconstr ~indices ~tyargs path` using the type's *own* idxvars
  (see [src/ecEnv.ml:794-798]). So every ctor is universally
  quantified over the index just like over type variables: `INil`
  has type `forall n 'a. 'a ivec<:n>`, valid at every index. The
  index carries no information about which constructor fired.
  Achieving the GADT-style declaration
  ```
  type [n] 'a vec =
    | VNil                       : 'a vec<:0>
    | VCons of 'a & 'a vec<:n>   : 'a vec<:n+1>
  ```
  would require (1) per-constructor result-type syntax (~1d of
  parser/elaborator plumbing) AND (2) index refinement on match
  (much larger — genuine dependent matching, intersects with SMT
  discharge of unification, new machinery in `trans_branch` and a
  refinement-aware unifier). Shipping (1) without (2) would be
  worse than the current uniform-indices behavior because users
  would expect refinement and not get it.

  Verified: 6 new declarations in `tests/indexed-types.ec` covering
  constructor application, plain match, matchfix, indexed records,
  and field projection (139 declarations total). Non-indexed
  datatypes and records continue to compile unchanged.

### Post-Phase-6 — gap F (DONE)

- **F** — SMT translation of indexed types via per-concrete-index
  monomorphisation.

  The two former `CanNotTranslate` raise sites in
  [src/ecSmt.ml](src/ecSmt.ml) (`trans_ty` Tconstr / `trans_app`
  Fop) now check whether all indices reduce to closed integers via
  the new `EcAst.tindex_to_int`. Closed indices dispatch to fresh
  monomorphised symbols; non-closed indices still raise
  `CanNotTranslate`, preserving the per-goal skip behaviour
  (warning emitted, lemma falls through to "no provers", no crash).

  New caches in `tenv`: `te_ty_idx` and `te_op_idx`, both
  string-keyed by `path<:i,j,...>`. New helpers `trans_pty_idx`,
  `trans_tydecl_idx`, `trans_op_idx`, `create_op_idx`. The
  declaration paths substitute idxvars by `TIConst` integers via
  `EcCoreSubst.f_subst_init ~idx:...` then build a fresh Why3
  sort/lsymbol named `<path>_<i>_<j>...`. Constructors and
  projectors of indexed datatypes/records get their per-index
  variants populated as a side-effect of `trans_tydecl_idx`;
  `trans_op_idx` checks `op_kind` and forces type monomorphisation
  before falling back to `create_op_idx` for plain ops.

  Plain indexed operators are translated as **abstract** Why3
  symbols (no body). This is sound but limits SMT's ability to
  unfold definitions across index instances. Lifting this would
  require substituting idxvars in the operator's body (form/expr)
  via `Fsubst.f_subst` and recursing through `trans_body`. Punted
  for now — concrete bodies for indexed ops are rare in practice
  and the user can add explicit lemmas if needed.

  Verified by 4 new SMT-discharge lemmas in `tests/indexed-types.ec`
  (160 declarations total): a simple equality on `vec<:5>`,
  equality on a constructor of an indexed datatype at index 0,
  conjunction of equalities on two distinct concrete-index sorts
  (`vec<:3>` and `vec<:5>`), and a use of explicit index
  instantiation `vfn[:5]`. Non-indexed SMT discharge unchanged
  (smoke-tested via list/match goals).

### Post-Phase-6 — gaps E / D / A (DONE)

- **E** — index binders on abbreviations and notations.
  `tyvars_decl` was already shared with ops/preds/axioms via
  Phase-3 Slice B; abbreviation and notation rules now use
  `mixed_tyvars_decl` too. New `ab_idx` / `nt_idx` fields on
  `pabbrev` / `pnotation`; `ecHiNotations` threads them via
  `~idxparams` on `transtyvars`.
- **D** — investigation. The Phase-4 "T2.make_vec unknown after
  clone-with-override" report turned out to be a misuse of the
  alias `=` operator instead of the inline `<-` operator (alias
  creates a new name that requires explicit qualification; inline
  propagates the body and adopts the source signature). Both modes
  work correctly. While tracing, `fresh_tparams` was found to
  freshen tyvars but not idxvars — fixed so op_tparams alpha-
  renaming covers both.
- **A** — explicit index instantiation at op call sites. New
  lexer token `LBRACKETCOLON` (matches `[:` glued, no whitespace).
  Grammar: `f[:n+1]` provides indices; `f<:int>` provides types
  (existing); `f[:n+1]<:int>` does both, in that order. Parsetree
  `TVIunamed` and ecUnify `tvar_inst.TVIunamed` both widened to
  `(idx list * ty list)`; producers updated mechanically.
  `EcUnify.openidx` now uses user-supplied indices when given,
  falling back to fresh `TIUnivar`s otherwise. Filter logic in
  `select_op` validates either side independently when non-empty.
  Useful when the op has indices that aren't reachable by argument-
  type inference (e.g. `op count [n 'a] : int` called as
  `count[:5]<:int>`).

  Verified: 91 declarations in `tests/indexed-types.ec` compile,
  including the new explicit-instantiation cases.

## Critical path & open risks

- Phases 0 → 1 → 2 are sequential; the rest can branch.
- **Risk:** the shared-namespace invariant (Phase 2 step 2) is
  enforced by panic. If any existing pass binds an int-typed local to
  a non-polynomial formula and that local later appears in a `tindex`
  context, EasyCrypt will crash mid-proof. Worth a tactical audit of
  `f_bind_local` / `f_subst_local` callers before merging.
- **Open:** index unification variables (Phase 1 step 4) — if the
  parser always demands an explicit index, you can defer this
  indefinitely. If you want `vec[]` inference, it's needed before
  Phase 3 is usable.
