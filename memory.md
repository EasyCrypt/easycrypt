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

### Phase 3 — Parser & typing
1. Concrete syntax for *binders*: propose `type ['n 'm] 'a vec`,
   `op f ['n] ('a) (xs : 'a vec['n]) : …`, `axiom ['n] foo : …`.
   Bracket order should match `dump_ty`'s `[indices|types]`.
2. Concrete syntax for *applications*: `'a vec[n+1]`.
3. `EcTyping`: parse index expressions through a restricted grammar —
   only `+`, `*`, non-negative literals, identifiers bound as indices.
   Reject subtraction, division, calls.
4. Resolution: when `n` is in scope as both an index binder and an int
   term variable (shared namespace), an occurrence in an index
   position becomes `TIVar n`, in a term position becomes
   `Flocal n` — disambiguated by syntactic position.
5. Cloning (`EcThCloning`, `EcSubst`): index parameters get
   instantiated alongside type parameters during clone-with.

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
