# Typeclasses — current status

Status snapshot of the typeclass implementation on the `deploy-tc` branch.
Every feature listed under "Implemented" is exercised by a test under
[`tests/tc/`](../tests/tc/); pointers given inline.

---

## Implemented

### 1. Declaration

A typeclass declares a set of operators and axioms parameterised over a
single carrier type, optionally inheriting from a parent class:

```
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

type class group <: addmonoid = {
  op opp : group -> group
  axiom addmN : forall (x : group), opp x + x = idm
}.
```

- The carrier is referenced by the typeclass name itself inside the body
  (`addmonoid`, `group`).
- Operators in the body are abstract; a concrete instance must realise
  them.
- Axioms must have all their type/typeclass variables bound; underconstrained
  axioms (`axiom foo : zero = zero`, where the carrier is left free) are
  rejected with a clear `axiom 'foo' is type-ambiguous` message.
  ([tests/tc/grandparent-op.ec](../tests/tc/grandparent-op.ec))
- Inheritance is by `<:`. Multiple ancestors form a chain via `tc_prt`.
- See: [tests/tc/basic.ec](../tests/tc/basic.ec),
  [tests/tc/inheritance.ec](../tests/tc/inheritance.ec).

### 2. Multi-parameter typeclasses

A typeclass may take leading type parameters in addition to the carrier:

```
type class ['a, 'b] embed = {
  op proj : embed -> 'a
  op inj  : 'b -> embed
  axiom dummy : true
}.
```

The carrier is still `embed`; `'a` and `'b` are auxiliary type parameters
of the class.
See: [tests/tc/multi-param.ec](../tests/tc/multi-param.ec).

### 3. Instances

An `instance` declaration realises a typeclass at a specific type:

```
op zero_int : int = 0.
op plus_int : int -> int -> int = Int.( + ).

instance addmonoid as int_inst with int
  op idm = zero_int
  op (+) = plus_int.

realize addmA by rewrite /plus_int; smt().
realize addmC by rewrite /plus_int; smt().
realize add0m by rewrite /plus_int /zero_int; smt().
```

For a multi-parameter typeclass, the leading parameters are bound
positionally:

```
instance (int, bool) embed as pair_inst with (int * bool)
  op proj = proj_pair
  op inj  = inj_pair.

realize dummy by trivial.
```

- The instance name (`as int_inst`) is optional; an auto-generated name
  is used otherwise.
- Multiple named instances for the same typeclass at different carrier
  types coexist.
  ([tests/tc/multi-instance.ec](../tests/tc/multi-instance.ec))
- Each axiom must be discharged via `realize`.

### 4. Polymorphic ops and lemmas over typeclasses

```
op double ['a <: addmonoid] (x : 'a) : 'a = x + x.

lemma idm_idem ['a <: addmonoid] (x : 'a) : idm + x = x.
proof. by apply add0m. qed.
```

Operators and lemmas can be parameterised by a type variable constrained
by a typeclass; they are usable at any type with a matching instance.

A type-parameter can also be constrained by a parametric typeclass that
references earlier type-parameters:

```
lemma round_trip
  ['a, 'b, 'c <: ('a, 'b) embed]
  (x : 'a) (y : 'b) :
  proj<:'a, 'b, 'c> (inj<:'a, 'b, 'c> y) = x =>
  proj<:'a, 'b, 'c> (inj<:'a, 'b, 'c> y) = x.
proof. by apply proj_inj. qed.
```

### 5. Instantiation at use sites

Explicit positional instantiation:

```
apply (idm_idem<:int> 5).
```

When a tparam is constrained by a typeclass and the user-supplied type
does not satisfy it, the diagnostic is clear:

```
type int does not satisfy typeclass constraint addmonoid
```

(Formerly produced a confusing "int doesn't match int" unification
diff.)
See: [tests/tc/explicit-tvi.ec](../tests/tc/explicit-tvi.ec).

When the constraint references earlier tparams (`'c <: ('a, 'b) embed`),
the user-supplied bindings for `'a, 'b` are substituted before the
instance lookup, so a multi-parameter `apply
(round_trip<:int, bool, (int * bool)>)` works.
See: [tests/tc/multi-param.ec](../tests/tc/multi-param.ec).

### 6. Sections

The `declare type t <: tc.` form abstracts a TC-constrained carrier
inside a section. Operators and lemmas using `t` survive section close
as TC-polymorphic forms:

```
section.
  declare type t <: addmonoid.

  op double (x : t) : t = x + x.

  lemma double_idm : double idm = idm.
  proof. by rewrite /double add0m. qed.
end section.

(* After close: *)
op test ['a <: addmonoid] (x : 'a) : 'a = double x.
```

See: [tests/tc/section.ec](../tests/tc/section.ec),
[tests/tc/declare-type.ec](../tests/tc/declare-type.ec).

### 7. Cloning abstract theories

An abstract theory parametrised by a TC-constrained carrier can be
cloned with a concrete instance carrier; the substitution threads
through TC witnesses, and the cloned operators reduce via the matching
instance:

```
abstract theory T.
  type t <: addmonoid.
  op double (x : t) : t = x + x.
end T.

clone T as TI with type t = int.

(* TI.double zero_int reduces to plus_int zero_int zero_int. *)
```

See: [tests/tc/clone-with-instance.ec](../tests/tc/clone-with-instance.ec),
[tests/tc/clone.ec](../tests/tc/clone.ec).

### 8. Reduction (`delta_tc`)

The reduction info exposes a `delta_tc` flag. When set, TC operators
applied at concrete (non-abstract) carriers reduce to the corresponding
instance body. When the witness was substituted to `\`Abs <concrete-path>`
(e.g. via theory cloning), the reducer infers the matching instance
on-the-fly.

### 9. SMT integration

When `smt()` (or `smt(...)`) is called over a goal whose context contains
type parameters constrained by typeclasses, every axiom of those
typeclasses (and their ancestors, deduplicated) is automatically added
to the Why3 task. This means `smt()` (no hints) closes goals over
abstract carriers that previously required `smt(addmA addmC add0m ...)`.

For concrete carriers, the `delta_tc` pre-reduction in the SMT init
collapses TC operators to their instance bodies before translation.

See: [tests/tc/smt.ec](../tests/tc/smt.ec).

### 10. Diamond and multi-level inheritance

```
type class base = { ... }
type class tc1 <: base = { ... }
type class tc2 <: base = { ... }
type class tc3 <: tc1 = { ... }
```

The ancestor walk reaches `base` from `tc3` (lift = 2) without
duplication. SMT auto-axiom inclusion deduplicates by axiom path.

See: [tests/tc/diamond.ec](../tests/tc/diamond.ec).

### 11. Pretty-printing

`type t.` prints as `type t.` for unconstrained abstract types and as
`type t <: addmonoid.` when constrained. Empty etyarg/witness brackets
are elided: `int[int_inst]` instead of `int[int_inst[]]`,
`addmonoid` instead of `addmonoid[]`. The `<:tc>` suffix on operators
appears only when the witness is a non-trivial reference (univar
placeholders, abstract carriers, parametric instances).

---

## Known limitations

### Polymorphic-body bare ops on parametric-carrier typeclasses

Inside a polymorphic body — say a lemma `['a, 'b, 'c <: ('a, 'b) embed]
... proj (inj y) ...` — bare ops still need explicit tvi
(`proj<:'a, 'b, 'c>`). The carrier is a type parameter, not a concrete
type, so the By-args strategy (which picks an instance from the
database) does not fire. At ground call sites the carrier is inferred
automatically; see [tests/tc/multi-param-bare-ops.ec](../tests/tc/multi-param-bare-ops.ec)
and [doc/typeclasses-inference.md](typeclasses-inference.md).

### Tuple/function carriers in instance declarations

Parser-side, `instance ... with (int * bool)` is accepted; the
resulting carrier type does flow through. But the upstream "carrier"
typing path does not currently accept declaring an instance directly on
a Tuple or Tfun type unless wrapped — see the `assert false` in
`subst_tcw` ([src/ecSubst.ml:226](../src/ecSubst.ml#L226)) which is
guarded behind an upstream rejection. This is a latent issue if upstream
loosens.

### Reverse-rewrite of bare-metavariable lemmas

A pattern like `rewrite -{1 2 3}mulrr` where `mulrr : forall x, x*x = x`
picks the first (largest) successful unification of `x`, which often
yields fewer occurrences than the user expects. Workaround: explicit
arg, `rewrite -{1 2 3}(mulrr (x + x))`. This is a pre-existing
matcher behaviour, not TC-specific (reproduces on `main` without
typeclasses); fix would touch the rewrite engine more broadly.

---

## Examples in `examples/tcstdlib/` and `examples/typeclasses/`

- [TcMonoid.ec](../examples/tcstdlib/TcMonoid.ec) — compiles cleanly.
- [TcRing.ec](../examples/tcstdlib/TcRing.ec) — compiles up through
  the comring section; the `boolring` lemma `addrr` at line 678 hits
  the bare-metavariable reverse-rewrite limitation above. Excluded
  from CI via `file_exclude`.
- [examples/typeclasses/monoidtc.ec](../examples/typeclasses/monoidtc.ec)
  and
  [examples/typeclasses/typeclass.ec](../examples/typeclasses/typeclass.ec)
  — compile cleanly.

---

## Files of interest

| Concern                       | File                          |
|-------------------------------|-------------------------------|
| AST: `tcwitness`, etyargs     | [src/ecAst.ml](../src/ecAst.ml) |
| Typeclass declarations        | [src/ecScope.ml `add_class`](../src/ecScope.ml) |
| Instance declarations         | [src/ecScope.ml `add_instance`](../src/ecScope.ml) |
| TC inference / ancestor walk  | [src/ecTypeClass.ml](../src/ecTypeClass.ml) |
| Unifier `\`TcCtt` resolution    | [src/ecUnify.ml](../src/ecUnify.ml) |
| Section close                 | [src/ecSection.ml `generalize_*`](../src/ecSection.ml) |
| Theory clone replay           | [src/ecTheoryReplay.ml](../src/ecTheoryReplay.ml) |
| Reduction (`delta_tc`)        | [src/ecReduction.ml](../src/ecReduction.ml) |
| SMT auto-axiom inclusion      | [src/ecSmt.ml `trans_tc_axioms`](../src/ecSmt.ml) |
| Pretty-printing               | [src/ecPrinting.ml](../src/ecPrinting.ml) |
| Tvi diagnostic                | [src/ecProofTyping.ml `pf_check_tvi`](../src/ecProofTyping.ml) |

---

## Test suite

Positive tests are under [`tests/tc/`](../tests/tc/) (scenario `unit`);
negative regression tests — files that must fail compilation with a
specific diagnostic — are under [`tests/tc-ko/`](../tests/tc-ko/)
(scenario `tc-ko`).

| File                       | What it covers                                  |
|----------------------------|-------------------------------------------------|
| `basic.ec`                 | Minimal class + instance + lemma                |
| `clone.ec`                 | Cloning a theory containing a TC declaration    |
| `clone-with-instance.ec`   | Cloning an abstract theory with TC carrier      |
| `declare-type.ec`          | Section closure with `declare type t <: tc`     |
| `diamond.ec`               | Diamond inheritance + SMT auto-axioms           |
| `explicit-tvi.ec`          | Explicit `<:int>` and bare apply                |
| `grandparent-op.ec`        | Underconstrained-axiom diagnostic + workarounds |
| `inheritance.ec`           | Two-level subclass chain                        |
| `instance.ec`              | Multiple ops/axioms in an instance              |
| `multi-instance.ec`        | Two named instances for one TC at different types |
| `multi-param.ec`           | `('a, 'b) embed` + polymorphic lemma + instance |
| `multi-param-bare-ops.ec`  | Bare-op carrier inference for multi-param TCs   |

Negative tests under `tests/tc-ko/`:

| File                         | Asserted error message                         |
|------------------------------|-------------------------------------------------|
| `bad-tvi.ec`                 | `type int does not satisfy typeclass constraint addmonoid` |
| `underconstrained-axiom.ec`  | `axiom 'tc3_extra' is type-ambiguous: ...`     |
| `ambiguous-instance.ec`      | `ambiguous typeclass instance for embed; candidates: ...` |
| `parametric.ec`            | Parametric TC `['a <: tc] action`               |
| `print.ec`                 | `print` does not crash on TC entities           |
| `section.ec`               | Typeclass declared inside a section             |
| `smt.ec`                   | SMT over abstract carriers (with/without hints) |
