# Typeclass inference — design

Companion to [typeclasses.md](typeclasses.md). Covers what the unifier
does when it encounters a `\`TcCtt(uid, ty, tc)` problem, why the current
single-axis approach is insufficient for multi-parameter typeclasses,
and the strategy framework that resolves this.

---

## Background — `\`TcCtt` problems

Whenever the typer needs a typeclass witness, it generates a problem of
the form

```
TcCtt (uid, ty, tc)
```

meaning "find a witness for `ty : tc`, and bind it to the witness
univar `uid`". The unifier's job is to either resolve `uid` to a
concrete `tcwitness` or report failure.

Three things vary:

1. **`ty`** — the carrier. Can be ground (`int`), abstract (`Tvar a`,
   `Tconstr abs_p _`), or a univar (`Tunivar u`).
2. **`tc.tc_args`** — the type-class's auxiliary type parameters, for
   parametric typeclasses like `('a, 'b) embed`. Each can be ground or
   contain univars.
3. **The environment** — `tvtc` for `Tvar` carriers, the typeclass
   declaration for `Tconstr abs_p`, and the instance database for
   ground carriers.

The current resolver is in `ecUnify.ml`, in the `\`TcCtt` arm of
`unify_core`.

## Catalog of inference modes

Every TcCtt problem falls into one of these shapes. Each row says what
information the resolver has and what it should produce.

| #  | Carrier `ty`              | `tc.args`                | Status today              | Resolver action                                                |
|----|---------------------------|--------------------------|---------------------------|----------------------------------------------------------------|
| 1  | ground                    | ground                   | works                     | `EcTypeClass.infer env ty tc` → `TCIConcrete`                  |
| 2  | ground                    | partly univar            | partly works              | `infer` already pattern-matches instance args, fills univars   |
| 3  | univar                    | ground                   | **fails** (parks forever) | walk instances, find unique match by `tc.args`, unify carrier  |
| 4  | univar                    | partly univar            | parks                     | wait — too underdetermined to infer either side                |
| 5  | `Tvar a`, `a ∈ tvtc`      | any                      | works                     | walk `tvtc[a]`'s ancestors, return `TCIAbstract { Var a; .. }` |
| 6  | `Tconstr abs_p _`         | any                      | works                     | walk decl's `tcs`, return `TCIAbstract { Abs abs_p; .. }`      |
| 7  | ground tuple/fun          | any                      | upstream rejects instance | (n/a) — but `subst_tcw` has a latent `assert false`            |
| 8  | `Tvar a`, `a ∉ tvtc`      | any                      | failure                   | error: "unconstrained type variable"                           |

Modes #1, #2, #5, #6 are covered. Mode #3 is the bare-op gap. Modes #4
and #7 are deferred (#4 has no inference to do; #7 is upstream).

A future row would add *e.g.*:

| ?  | `Fapp` carrier (HO)       | any                      | not designed              | escape hatch / explicit tvi                                   |

## Why the current resolver doesn't cover Mode #3

The resolver's flow:

```
if TyUni.Suid.is_empty deps then
   (* Mode #1, #2, #5, #6 *)
   resolve and bind uid
else
   (* Mode #3, #4 *)
   for each univar in deps, register uid in byunivar map
   wait for the univar to resolve
```

When `ty = Tunivar u`, `deps = {u}`. The resolver parks the problem.
It re-fires only when `u` is bound by some other equation. For Mode #3
there is no such equation — the carrier's only constraint is the
typeclass itself.

The fix is to attempt **forward inference** in this case: if `tc.args`
are ground and exactly one instance of `tc` matches, bind `u` to its
`tci_type`.

## Strategy framework (Phase 2)

Replace the single big `\`TcCtt` arm with a list of strategies. Each
strategy is:

```ocaml
type tcw_strategy = {
  name       : string;
  applicable : tcenv -> tcuni -> ty -> typeclass -> bool;
  apply      : EcEnv.env -> ucore -> tcuni -> ty -> typeclass
             -> ucore * tcw_result;
  triggers   : tcw_trigger list;
}

and tcw_result =
  | Resolved  of tcwitness
  | Stuck                          (* park, retry on triggers *)
  | Failed    of failure_reason
  | NoSuchInstance

and tcw_trigger =
  | OnUnivarResolved of tyuni      (* re-fire when this tyuni binds  *)
  | OnTcUniResolved  of tcuni      (* re-fire when this tcuni binds  *)
```

The dispatcher iterates strategies in priority order, stops on the
first non-`Stuck` result.

Today's resolver becomes a list of strategies:

| Priority | Strategy           | Mode |
|----------|--------------------|------|
| 1        | `tvar_via_tvtc`    | #5   |
| 2        | `abs_via_decl`     | #6   |
| 3        | `infer_by_carrier` | #1, #2 |
| 4 *new*  | `infer_by_args`    | #3   |
| 5        | `defer`            | #4   |

Behaviour with strategies 1-3 + 5 is identical to today's resolver;
adding strategy 4 closes Mode #3.

The `triggers` field is what lets us avoid the current implicit
re-seeding (which today re-pushes every parked problem at the start of
every `unify_core` call). With explicit triggers we only re-fire what
the latest binding could have made progress on. This is performance
hygiene; not strictly required for correctness.

## By-args strategy (Phase 3)

```
applicable(tcenv, uid, ty, tc):
  ty is Tunivar u  AND
  tc.args contains no univars

apply(env, uc, uid, ty, tc):
  candidates =
    [ inst | inst ∈ TcInstance.get_all env,
             inst.tci_instance = `General (tgp, _),
             tgp.tc_name = tc.tc_name,
             etyargs_match env (List.fst inst.tci_params)
                ~patterns:tgp.tc_args ~etyargs:tc.tc_args
                  succeeds with map M ]

  match candidates:
  | []         -> NoSuchInstance
  | [inst, M]  -> let carrier = subst M inst.tci_type in
                  unify env uc ty carrier ;
                  Resolved (TCIConcrete { path = inst_path;
                                          etyargs = subst M inst.tci_params;
                                          lift = 0 })
  | _ :: _ :: _-> Stuck  (* multiple matches; later info may decide *)
```

**Soundness:** we only commit when the match is unique. With multiple
matches we stay parked; if no further constraint disambiguates, the
final close-time check raises an "ambiguous TC instance" error
(distinguishable from "no instance" by carrying the candidate list).

**Triggers:** none for now. The strategy is monotone — once a
candidate is excluded it stays excluded, since we only act when
`tc.args` are already ground. (Future: if `tc.args` start univar,
register `OnTcUniResolved` triggers.)

**Risk surface:**
- A user's instance-DB shape can change ("which instances are visible")
  via imports/cloning. The strategy must use whatever
  `TcInstance.get_all` returns at the moment the strategy fires —
  consistent with how current Mode #1 already works.
- Picking a non-canonical "exactly one" must be robust against import
  order. `etyargs_match` is structural; we are safe.

## Test matrix (Phase 3)

```
tests/tc/multi-param-bare-ops.ec
  - bare op, unique instance      → resolves
  - two competing instances       → "ambiguous TC instance" error
  - args still univar at start,
    resolved later by usage       → eventually resolves (deferred)
  - no matching instance          → "no instance" error
```

Plus the existing `tests/tc/`, `theories/`, and `tests/` regression
sweeps to ensure single-parameter TC behaviour does not change.

## Future work (Phase 4-5)

- **Functional dependencies** in TC syntax: `class ('a, 'b) embed | 'a 'b -> embed`
  declares the dependency explicitly. The By-args strategy is then
  *justified by the declaration*, not by enumeration. Also enables
  duplicate-instance detection at instance-binding time.

- **Anticipated future rows in the catalog:**
  - TC arg inference from operator bodies (axiom RHSs that mention TC ops).
  - Inference through hypotheses introduced by `intros`.
  - `Tglob` / module-type carriers.
  - Coercion across same-named ops in different TCs.

Each new gap follows the same recipe: add a row, add a test, add a
strategy, route diagnostics through the same `Failed` path.
