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

### Phase 4 — Theories & smoke tests
1. Add a focused `.ec` test exercising:
    - declaration of an indexed type and indexed op
    - polynomial-equality path: `concat (concat a b) c : vec[(n+m)+k]`
      unifies with `vec[n+(m+k)]`
    - cloning with index instantiation
2. Recommend leaving `theories/Array.ec` etc. untouched for the first
   landing.

### Phase 5 — SMT gating
Replace the `assert (List.is_empty tys.indices)` calls in
[src/ecSmt.ml](src/ecSmt.ml) with a clean "indexed types not yet
supported by SMT" error.

### Phase 6 — Polish
1. Pretty-printer for indices in `EcPrinting` (canonical form).
2. Reduction error messages should print both normalised indices on
   mismatch.
3. `CHANGELOG`.

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
