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

### Phase 1 — Polynomial normal form & equality
1. Add a `tindex` normalisation (sorted sum-of-monomials with
   `EcBigInt` coefficients ≥ 1) and hashcons canonical forms.
2. Make `tindex_equal` compare canonical forms; replace the
   `Hashtbl.hash` `tindex_hash` (structurally wrong once
   `1+2 ≡ 2+1`).
3. Replace the `(* FIXME *)` in
   [src/ecUnify.ml:146](src/ecUnify.ml#L146) (note: polarity also
   bugged today: `if all2 ... then failure ()` is inverted) and the
   `(* FIXME: compare indices *)` in `EcReduction.for_targs`
   ([src/ecReduction.ml:25-39](src/ecReduction.ml#L25-L39)).
4. Decide whether indices participate in `EcUnify.UF` for inference —
   probably needed only if Phase 3 lets users elide indices.

### Phase 2 — Substitution & FV
1. Add `tindex_of_form : form -> tindex option` recognising
   `Fint n (n≥0)`, `Flocal id (ty=int)`, `Fapp(p_int_add, [a;b])`,
   `Fapp(p_int_mul, [a;b])`. Returns `None` on anything else.
2. Implement `tindex_subst` in
   [src/ecCoreSubst.ml:185](src/ecCoreSubst.ml#L185) and
   [src/ecSubst.ml:153](src/ecSubst.ml#L153): for `TIVar id`, look up
   `fs_loc`/`fs_v`; if a binding exists, `tindex_of_form` it and
   `Option.get` (panic if the substitution invariant is violated).
   Re-normalise at the root.
3. Patch `targs_fv` in [src/ecAst.ml:1090](src/ecAst.ml#L1090) and
   `Hsty.fv` in [src/ecAst.ml:1147](src/ecAst.ml#L1147) to fold over
   `indices` (currently they only walk `types`, so
   `Tconstr (p, {indices=[TIVar n]; types=[]})` reports empty fv —
   wrong).
4. Audit smart-equality fast paths in `targs_subst`: `==` survives
   normalisation only when nothing changed *and* the input was already
   canonical.

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
