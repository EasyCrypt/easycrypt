# The rules of probabilistic Hoare logic (pHL / `phoare`)

This is a reference catalogue of every rule of EasyCrypt's **bounded (probabilistic)
Hoare logic** — the judgement `bdHoareS` / `bdHoareF`, written

```
phoare[ c : P ==> Q ] <= b       phoare[ f : P ==> Q ] = b       phoare[ f : P ==> Q ] >= b
```

It exists because auditing "everything in the pHL logic" means opening about twenty files.
Every tactic that can act on a `phoare` goal is given here **as an inference rule** —
whether it is a primitive rule of the logic or a tactic derived by composing others.

**Scope.** bdHoare only. Rules of `hoare`, `ehoare`, `equiv` and `eager` are out of scope
except where a pHL rule produces or consumes them — which happens often, and is always
flagged.

---

## Contents

- [0. Preliminaries](#0-preliminaries)
- [1. The core pHL rules](#1-the-core-phl-rules)
- [2. The `conseq` family](#2-the-conseq-family)
- [3. Views and bound splitting](#3-views-and-bound-splitting)
- [4. Probability bridges](#4-probability-bridges)
- [5. Code transforms](#5-code-transforms)
- [6. Not applicable to pHL](#6-not-applicable-to-phl)
- [7. Footnotes: inconsistencies observed](#7-footnotes-inconsistencies-observed)
- [Appendix: how the rules in this file were checked](#appendix-how-the-rules-in-this-file-were-checked)

---

## 0. Preliminaries

### 0.1 The judgement

```ocaml
type hoarecmp = FHle | FHeq | FHge                        (* ecAst.ml:33 *)

and bdHoareF = {                                          (* ecAst.ml:265-272 *)
  bhf_m   : memory;   bhf_pr : form;   bhf_f  : xpath;
  bhf_po  : form;     bhf_cmp: hoarecmp; bhf_bd : form;
}

and bdHoareS = {                                          (* ecAst.ml:274-281 *)
  bhs_m   : memenv;   bhs_pr : form;   bhs_s  : stmt;
  bhs_po  : form;     bhs_cmp: hoarecmp; bhs_bd : form;
}
```

The form nodes are `FbdHoareF` / `FbdHoareS` (`ecAst.ml:196-197`). The `pr` / `po` / `bd`
**fields carry a privacy alert** (`ecAst.mli:277-299`); always go through the accessors
`bhf_pr` / `bhf_po` / `bhf_bd` and `bhs_pr` / `bhs_po` / `bhs_bd` (`ecAst.ml:702-708`,
declared `ecAst.mli:456-461`). They return

```ocaml
and ss_inv = { m : memory; inv : form }                   (* ecAst.ml:283-286 *)
```

a *single-sided* predicate paired with the one memory it is interpreted in. The two-sided
sibling `ts_inv` (`ecAst.ml:332-336`) belongs to `equiv`; the exception-aware `hs_inv`
(`ecAst.ml:461-464`) belongs to `hoare`. The logic-agnostic sum
`inv = Inv_ss | Inv_ts | Inv_hs` (`ecAst.ml:466-469`) is what `conseq`, `case` and
`exists` dispatch on.

Smart constructors: `f_bdHoareS mt pr s po cmp bd` (`ecCoreFol.ml:317-320`, which asserts
that the three `ss_inv`s share a memory) and `f_bdHoareF pr f po cmp bd`
(`ecCoreFol.ml:322-325`). Destructors `destr_bdHoareS` / `destr_bdHoareF`
(`ecCoreFol.ml:746-754`), tests `is_bdHoareS` / `is_bdHoareF` (`ecCoreFol.ml:913-914`).
Goal readers: `tc1_as_bdhoareS` / `tc1_as_bdhoareF` (`ecLowPhlGoal.ml:170-171`) and their
`pf_as_*` variants (`:159-160`).

### 0.2 Notation

Throughout, a pHL judgement is written

> `⊢ phoare[ c : P ==> Q ] ⋈ b`   with `⋈ ∈ {≤, =, ≥}` — the statement form (`bdHoareS`)
>
> `⊢ phoare[ f : P ==> Q ] ⋈ b`   — the procedure form (`bdHoareF`)

and a Hoare judgement `⊢ hoare[ c : P ==> Q ]`. `⋈ᵒᵖ` is the opposite comparison
(`hoarecmp_opp`, `ecCoreFol.ml:139-143`): `≤ᵒᵖ = ≥`, `≥ᵒᵖ = ≤`, `=ᵒᵖ = =`.
`∀&m.` abbreviates `EcSubst.f_forall_mems_ss_inv`, the quantification over the judgement's
memory that turns an `ss_inv` side condition into a closed formula. `∀mod(c).` abbreviates
`generalize_mod_ss_inv` (`ecLowPhlGoal.ml:698`), the quantification over the variables `c`
writes.

Two rule bars are used, and the distinction matters:

| bar | meaning |
|---|---|
| `─────` | **primitive**: this tactic closes the goal itself and *is* the rule |
| `═════` | **derived**: this is the *net* rule you get from composing other tactics |

A derived rule lists only the premises the user is actually left with. Premises that the
composition discharges internally are noted underneath. Each derived rule is followed by
its **expansion** — the tactics it is built from — so the derivation can be checked.

Premises are listed **in the order the tactic emits them**, because that is the order the
subgoals appear in.

### 0.3 How a rule is reached

Dispatch is by *parsetree constructor*, in `process1_phl` (`ecHiTacticals.ml:189-260`); it
knows nothing about which logic the goal is in. Per-logic routing happens one level down,
inside each `process_*`, in one of three styles:

- the `is_bdHoareS` / `is_bdHoareF` predicate (e.g. `ecPhlSeq.ml:258`, `ecPhlRCond.ml:110`);
- pattern-matching `concl.f_node` on `FbdHoareS` / `FbdHoareF` (e.g. `ecPhlCall.ml:449`);
- the combinators `t_hS_or_bhS_or_eS` / `t_hF_or_bhF_or_eF`
  (`ecLowPhlGoal.ml:430-462`), whose `~tbh:` argument is the bdHoare branch.

### 0.4 Legend

- **primitive** — the tactic closes the goal itself with ``FApi.xmutate1 tc `Tag [...]``
  (or `xmutate1_hyps`). It is a rule of the logic in its own right, and is trusted.
- **derived** — pure orchestration over other tactics. Its rule is a *theorem* about the
  primitives, not a new axiom.

Where a surface tactic is a thin wrapper around a primitive, both are given: the primitive
rule first, then the derived rule the user actually sees.

---

## 1. The core pHL rules

### 1.1 `skip`

**Primitive** — `t_bdhoare_skip_r_low` (`ecPhlSkip.ml:42`, `` `Skip ``):

```
        ∀&m. P ⇒ Q
  ──────────────────────────────
  ⊢ phoare[ [] : P ==> Q ] ⋈ b        [ b syntactically 1%r; ⋈ ∈ {=, ≥} ]
```

The statement must be empty. If `b` is *not* syntactically `1%r` the rule instead emits two
premises, `b = 1%r` and `∀&m. P ⇒ Q` (`ecPhlSkip.ml:52-56`); and `⋈ = ≤` is rejected
(`:47`). Neither case is reachable from the surface — see the derived rule.

**Derived** — the surface `skip` (`t_bdhoare_skip_r`, `ecPhlSkip.ml:61`,
`t_skip : backward`, `ecPhlSkip.ml:90`, `.mli:5`):

```
  ∀&m. P ⇒ (1%r ⋈ b)          ∀&m. P ⇒ Q
  ═══════════════════════════════════════
       ⊢ phoare[ [] : P ==> Q ] ⋈ b
```

*Expansion:* `t_bdHoareS_conseq_bd FHeq 1%r` (§2.2) — which normalises the bound to `1%r`,
producing the first premise — then `t_try t_trivial`, then `t_bdhoare_skip_r_low` on the
normalised goal (`ecPhlSkip.ml:65-68`). Because the bound is `1%r` by then, `_low` always
takes its one-premise branch.

Two consequences that are easy to get wrong:

- **`≤` is accepted at the surface.** `_low` rejects it, but the wrapper converts the goal
  to `= 1%r` first, so `skip` on a `≤ b` goal succeeds and leaves `∀&m. P ⇒ 1%r ≤ b`.
- The first premise is `t_try`-attempted by `t_trivial` and vanishes when the bound is
  literally `1%r`.

Instantiating `⋈` in the first premise via `bd_goal_r` (§2.2): `= 1%r` → discharged;
`≥ b` → `b ≤ 1%r`; `≤ b` → `1%r ≤ b`.

### 1.2 `seq` (a.k.a. `app`) — the four-bound rule

**Primitive** — `t_bdhoare_seq_r_low` (`ecPhlSeq.ml:44`, `` `HlApp ``). For `seq i : R f₁ f₂ g₁ g₂`
splitting `c` into `c₁; c₂` at position `i`, with `¬R` written `R̄` and the auxiliary
assertion `φ` (default `true`):

```
  ⊢ hoare[ c₁ : P ==> φ ]                                        (cond_phi)
  ⊢ phoare[ c₁ : P ==> R ]      ⋈ f₁                             (condf1)
  ⊢ phoare[ c₂ : φ ∧ R ==> Q ]  ⋈ f₂                             (condf2)
  ⊢ phoare[ c₁ : P ==> R̄ ]      ⋈ g₁                             (condg1)
  ⊢ phoare[ c₂ : φ ∧ R̄ ==> Q ]  ⋈ g₂                             (condg2)
  ∀&m. P ⇒ f₁·f₂ + g₁·g₂ ⋈ b                                     (condbd)
  ∀ r₁ r₂. ⊢ hoare[ c₁ : P ∧ f₂ = r₁ ∧ g₂ = r₂ ==> f₂ = r₁ ∧ g₂ = r₂ ]   (condnm)
  ──────────────────────────────────────────────────────────────
                ⊢ phoare[ c₁; c₂ : P ==> Q ] ⋈ b
```

`condbd` is `≤`-, `=`- or `≥`-shaped following `⋈` (`ecPhlSeq.ml:66-71`). `condnm` says the
prefix does not disturb the two second-phase bounds.

**Premise pruning** (`ecPhlSeq.ml:84-97`): if `g₁` is syntactically `0%r` only `condg1` is
kept (`condg2` is dropped), and dually for `g₂`; likewise for `f₁` / `f₂`. So the primitive
emits between **4 and 7** premises.

**Derived** — the surface `seq` (`t_bdhoare_seq_r`, `ecPhlSeq.ml:103`;
`t_bdhoare_seq : codegap1 -> ss_inv tuple6 -> backward`, `:119`, `.mli:11`) is the same rule
with `condnm` attempted automatically:

```
  … the premises above, except condnm …
  ═══════════════════════════════════════════
     ⊢ phoare[ c₁; c₂ : P ==> Q ] ⋈ b
                                        [ when f₂ and g₂ do not depend on vars c₁ writes ]
```

*Expansion:* `t_bdhoare_seq_r_low` then, on the **last** subgoal (`condnm`),
`t_try (t_intros_s_seq … (t_hoareS_conseq_nm … ; t_pl_trivial ; t_fail))`
(`ecPhlSeq.ml:103-117`). So `condnm` disappears whenever the two second-phase bounds are
constant, and survives otherwise. In practice `seq i : R` yields **5** goals and
`seq i : R f₁ f₂ g₁ g₂` with a variable `f₂` yields **6**.

**Surface-argument mapping** (the non-obvious part). `seq_info` is the tuple
`oside * pcodegap1 doption * pformula doption * p_seq_xt_info`
(`ecParsetree.ml:702-703`). In `seq i : R f₁ f₂ g₁ g₂` the formula after `:` is the
**case predicate** `R`, *not* `φ`; `φ` is the optional first component of `PSeqMult` and
defaults to `true`. `process_phl_bd_info` (`ecPhlSeq.ml:167-215`) resolves the three bound
shapes (`p_seq_xt_info`, `ecParsetree.ml:629-632`):

| surface | `φ` | `f₁` | `f₂` | `g₁` | `g₂` |
|---|---|---|---|---|---|
| `PSeqNone` (`seq i : R`) | `true` | `b` | `1%r` | `0%r` | `1%r` |
| `PSeqSingle f` (`seq i : R f`) | `true` | `b / f` | `f` | `0%r` | `1%r` |
| `PSeqMult` (`seq i : R f₁ f₂ g₁ g₂`) | given, else `true` | given | given | given | given |

Within `PSeqMult`, supplying only one of a pair forces the other to `1%r` and requires the
supplied one to be `0%r` (`check_0`, `ecPhlSeq.ml:190-210`). Dispatcher arm:
`ecPhlSeq.ml:258-263`; entry `process_seq` (`:218`, `.mli:16`); parse syntax
`ecParser.mly:3131-3132`, bound suffix `app_bd_info` `:2863-2874`.

### 1.3 `if`

**Derived** — `t_bdhoare_cond` (`ecPhlCond.ml:61`, `.mli:8`). The leading instruction must
be a conditional (`tc1_first_if`, `ecLowPhlGoal.ml:114`); otherwise "invalid first
instruction".

```
  ⊢ phoare[ s₁; tl : P ∧ e ==> Q ] ⋈ b     ⊢ phoare[ s₂; tl : P ∧ ¬e ==> Q ] ⋈ b
  ═══════════════════════════════════════════════════════════════════════════════
        ⊢ phoare[ if e then s₁ else s₂; tl : P ==> Q ] ⋈ b
```

Both branches keep the *same* bound — the rule is a precondition case-split, which is sound
at a fixed bound because the two preconditions are exclusive and exhaustive.

*Expansion* (`LowInternal.t_gen_cond`, `ecPhlCond.ml:25-44`): `EcPhlCase.t_hl_case
~simplify:false e` (§1.13) splits on the guard; in each branch `EcPhlRCond.t_rcond` (§1.4)
removes the now-decided conditional, and its Hoare guard premise is closed by
`EcPhlSkip.t_skip` (§1.1) plus a small `elim`/`apply` finaliser (`:17-20`, `:34-41`).

Elaboration: `process_cond` (`ecPhlHiCond.ml:10`, `~tbh:` at `:19`, `.mli:6`); the
`` `SeqOne `` arm (`:32-40`) first splits with `t_equiv_seq_onesided`. Parse syntax
`ecParser.mly:3164-3165`.

### 1.4 `match`

**Derived** — `t_bdhoare_match` (`ecPhlCond.ml:243`, `.mli:13`). For a leading
`match e with | C₁ x⃗₁ => s₁ | … | Cₙ x⃗ₙ => sₙ`:

```
  for each i:  ⊢ phoare[ sᵢ; tl : e = Cᵢ(x⃗ᵢ) ∧ P ==> Q ] ⋈ b
  ═══════════════════════════════════════════════════════════
    ⊢ phoare[ match e with … ; tl : P ==> Q ] ⋈ b
```

Each branch's pattern variables `x⃗ᵢ` are added to the goal's **memory** as fresh program
variables, and the precondition is strengthened with the constructor equation.

*Expansion* (`LowMatchInternal.t_gen_match`, `ecPhlCond.ml:125-233`):
`EcPhlExists.t_hr_exists_intro [e]` then `t_hr_exists_elim ~bound:1` (§1.12) generalise the
scrutinee into a quantified variable; `EcLowGoal.t_elimT_ind `Case` (`:230`) performs the
datatype case analysis; then per constructor `EcPhlRCond.t_rcond_match` (§1.4) selects the
branch, its Hoare premise is discharged by the `discharge` script (`:154-183`), and the
surviving pHL goal is tidied by `EcPhlConseq.t_conseq` (`:219`).

Elaboration: `process_match` (`ecPhlHiCond.ml:43`, `~tbh:` at `:46`, `.mli:7`).

### 1.5 `rcondt` / `rcondf`

**Primitive** — `Low.t_bdhoare_rcond_r` (`ecPhlRCond.ml:63`, `` `RCond ``;
`t_bdhoare_rcond : bool -> codepos1 -> backward`, `:101`, `.mli:11`). For the instruction at
position `i` being `if e then s₁ else s₂`, writing `e_b` for `e` (tactic `rcondt`) or `¬e`
(tactic `rcondf`), and `hd` for the prefix before `i`:

```
  ⊢ hoare[ hd : P ==> e_b ]        ⊢ phoare[ hd; s_b; tl : P ==> Q ] ⋈ b
  ──────────────────────────────────────────────────────────────────────
              ⊢ phoare[ hd; if e then s₁ else s₂; tl : P ==> Q ] ⋈ b
```

The first premise — that the guard is *determined* at that point — is a **hoare** goal, not
a pHL one (`ecPhlRCond.ml:70`); the second re-forms the pHL judgement with the branch
inlined. Dispatcher `t_rcond` (`:106-111`, `.mli:23`), elaboration `process_rcond`
(`.mli:24`). Surface names are `rcondt i` and `rcondf i`
(`ecParser.mly:3155-3159`, keywords at `ecLexer.mll:145-146`).

**`match` variant** — `Low.t_bdhoare_rcond_match_r` (`ecPhlRCond.ml:250`,
`` `RCondMatch ``; `.mli:18`), tactic `match C i` (`ecParser.mly:3161-3162`):

```
  ⊢ hoare[ hd : P ==> e = C(x⃗) ]     ⊢ phoare[ hd; s_C; tl : P ∧ e = C(x⃗) ==> Q ] ⋈ b
  ─────────────────────────────────────────────────────────────────────────────────────
              ⊢ phoare[ hd; match e with … ; tl : P ==> Q ] ⋈ b
```

The second premise runs in a memory extended with the pattern variables, and the
constructor equation is conjoined to the precondition (`ecPhlRCond.ml:255`). Dispatcher
`t_rcond_match` (`:319`, `.mli:28`).

### 1.6 `rnd`

**Primitive**, five shapes — `t_bdhoare_rnd_r` (`ecPhlRnd.ml:158`, `` `Rnd ``;
`t_bdhoare_rnd : bhl_infos_t -> backward`, `:643`, `.mli:21`), selected on
`(tac_info, cmp)`. In all shapes the statement ends with `x <$ d` and `s` is the prefix.

Two auxiliary notions are used throughout:

- `E(v)` — the *event*, a predicate on the sampled value. Given explicitly, or synthesised
  by `mk_event` (`ecPhlRnd.ml:198-206`) as `fun x => Q[x/lv]`, or `predT` when the post does
  not mention the assigned variable (`is_post_indep`, `:186-192`).
- `mk_event_cond E` (`ecPhlRnd.ml:165-180`) — the link between event and post, oriented by
  `⋈`:

  | `⋈` | `mk_event_cond E` |
  |---|---|
  | `≤` | `∀v. E v ⇒ v ∈ supp d ⇒ Q[v/lv]` |
  | `≥` | `∀v. Q[v/lv] ⇒ v ∈ supp d ⇒ E v` |
  | `=` | `∀v. v ∈ supp d ⇒ (E v ⇔ Q[v/lv])` |

`bound` and `pre_bound` (`ecPhlRnd.ml:207-214`) generalise the bound over a fresh `bd`
variable when the prefix writes variables the bound depends on (`is_bd_indep`, `:193-197`);
otherwise `bound = b` and `pre_bound = true`.

**(a) `rnd`, `⋈ = ≤`** (`ecPhlRnd.ml:216-230`). If `is_post_indep`, the sampling is dropped:

```
  ⊢ phoare[ s : P ==> Q ] ≤ b
  ───────────────────────────────────
  ⊢ phoare[ s; x <$ d : P ==> Q ] ≤ b
```

Otherwise it degrades to a **hoare** goal about `mu`:

```
  ⊢ ∀bd. hoare[ s : P ∧ pre_bound ==> mu d E ≤ bound ∧ mk_event_cond E ]
  ─────────────────────────────────────────────────────────────────────
              ⊢ phoare[ s; x <$ d : P ==> Q ] ≤ b
```

**(b) `rnd`, `⋈ ∈ {=, ≥}`** (`:231-247`). With `is_post_indep`, a losslessness condition is
folded into the post:

```
  ⊢ phoare[ s : P ==> Q ∧ mu d predT = 1%r ] ⋈ b
  ──────────────────────────────────────────────
     ⊢ phoare[ s; x <$ d : P ==> Q ] ⋈ b
```

Otherwise:

```
  ⊢ ∀bd. phoare[ s : P ∧ pre_bound ==> mu d E ⋈ bound ∧ mk_event_cond E ] ⋈ 1%r
  ─────────────────────────────────────────────────────────────────────────────
                  ⊢ phoare[ s; x <$ d : P ==> Q ] ⋈ b
```

**(c) `rnd E`, `⋈ = ≤`** (`:248-256`) — as (a)'s second form, with the supplied `E`.

**(d) `rnd E`, `⋈ ∈ {=, ≥}`** (`:257-264`) — as (b)'s second form with the supplied `E`;
note the residual judgement is forced to `= 1%r` (`:262`).

**(e) `rnd φ d₁ d₂ d₃ d₄ [E]`** — `PMultRndParams` (`:265-289`), **six** premises:

```
  ∀&m. d₁·d₂ + d₃·d₄ ⋈ b                                            (bd_sgoal)
  ⊢ phoare[ s : P ==> φ ] ⋈ d₁                                      (sgoal1)
  ∀&m. φ ⇒ (mu d E ⋈ d₂ ∧ mk_event_cond E)                          (sgoal2)
  ⊢ phoare[ s : P ==> ¬φ ] ⋈ d₃                                     (sgoal3)
  ∀&m. ¬φ ⇒ (mu d E ⋈ d₄ ∧ mk_event_cond E)                         (sgoal4)
  ∀&m. 0%r ≤ dᵢ ≤ 1%r  for i = 1..4                                 (sgoal5)
  ────────────────────────────────────────────────────────────────
             ⊢ phoare[ s; x <$ d : P ==> Q ] ⋈ b
```

Elaboration: `process_rnd` bdHoare arm (`ecPhlRnd.ml:649`, arm `:664-685`, `.mli:25`).
Argument shapes are `PNoRndParams` / `PSingleRndParam` / `PMultRndParams`
(`rnd_tac_info`, `ecParsetree.ml:634-638`); grammar `rnd_info`, `ecParser.mly:2792-2806`.
The fourth shape `PTwoRndParams` (`rnd f g`, `ecParsetree.ml:637`) is **equiv-only** — on a
pHL goal it falls through to `tc_error "invalid arguments"` (`ecPhlRnd.ml:291`).

### 1.7 `rndsem`

**Primitive** — `Core.t_bdhoare_rndsem_r` (`ecPhlRnd.ml:424`, `` `RndSem pos ``). Replaces a
trailing block of samplings by one semantic sampling, keeping pre, post, `⋈` and bound:

```
  ⊢ phoare[ s₁; semrnd(s₂) : P ==> Q ] ⋈ b
  ────────────────────────────────────────
      ⊢ phoare[ s₁; s₂ : P ==> Q ] ⋈ b
```

Not exported in `ecPhlRnd.mli`; reached through `process_rndsem` (`:723`, `.mli:28`,
bdHoare arm `:730-731`).

### 1.8 `while` — three rules

pHL has three distinct loop rules, chosen by how many arguments you supply
(`process_while`, `ecPhlWhile.ml:548`, bdHoare arm `:567-587`, `.mli:13`; grammar
`while_tac_info`, `ecParser.mly:2775-2783`):

| surface syntax | rule | admissible `⋈` | prefix before the loop |
|---|---|---|---|
| `while (inv) (vrnt)` | `t_bdhoare_while` | `≤`, `=`, `≥` | allowed |
| `while (inv)` | `t_bdhoare_while_rev` | `≤` only | allowed |
| `while (inv) (vrnt) k eps` | `t_bdhoare_while_rev_geq` | `=`, `≥` only | **must be empty** |

**(a) Variant rule** — `t_bdhoare_while_r inv vrnt` (`ecPhlWhile.ml:127`, `` `While ``,
2 premises; `t_bdhoare_while : ss_inv -> ss_inv -> backward`, `:540`, `.mli:8`). The body
must be *certain* (`= 1%r`) and strictly decrease the variant; the loop then reduces to a
`wp`-style postcondition on the prefix:

```
  ∀z. ⊢ phoare[ body : (I ∧ e) ∧ vrnt = z ==> I ∧ vrnt < z ] = 1%r
  ⊢ phoare[ s : P ==> I ∧ ∀mod(body). ((I ⇒ vrnt ≤ 0 ⇒ ¬e) ∧ (¬e ⇒ I ⇒ Q)) ] ⋈ b
  ────────────────────────────────────────────────────────────────────────────
                  ⊢ phoare[ s; while e do body : P ==> Q ] ⋈ b
```

Mind the implication order in the second premise: it is `I ⇒ vrnt ≤ 0 ⇒ ¬e` (the variant
reaching zero forces the guard false) conjoined with `¬e ⇒ I ⇒ Q`
(`ecPhlWhile.ml:144-147`).

**(b) Reverse rule, upper bounds only** — `t_bdhoare_while_rev_r inv`
(`ecPhlWhile.ml:157`, `` `While `` via **`xmutate1_hyps`**, 2 premises; not exported,
reached via `t_bdhoare_while_rev`, `:542`). Rejects any `⋈ ≠ ≤` (`:161`). It introduces an
*abstract statement* hypothesis `w` standing for the rest of the loop (`while_info`,
`LD_abs_st`, `:173-175`) and asks for one unfolding step:

```
  [w : abstract]  ⊢ phoare[ w : I ==> Q ] ≤ b  ⇒  phoare[ body; w : I ∧ e ==> Q ] ≤ b
  ⊢ hoare[ s : P ==> I ∧ ∀mod(body). (I ∧ ¬e ∧ Q ⇒ b = 1%r) ]
  ──────────────────────────────────────────────────────────────────────────────────
                     ⊢ phoare[ s; while e do body : P ==> Q ] ≤ b
```

The first subgoal is emitted under the *extended* hypotheses; the second under the original
ones. Note the second is a **hoare** goal.

**(c) Reverse rule with rate, lower/exact bounds** — `t_bdhoare_while_rev_geq_r inv vrnt k eps`
(`ecPhlWhile.ml:205`, `` `While `` via `xmutate1_hyps`, **6 premises**; not exported,
reached via `t_bdhoare_while_rev_geq`, `:541`). Rejects `⋈ = ≤` (`:210`), requires that
neither `eps` nor `k` depend on variables written by the body (`:220-228`), and requires the
loop to be the **whole** statement — `check_single_stmt` (`:230`, definition `:92-94`)
demands an empty remainder, despite its message "only single loop statements are accepted".

```
  ∀&m. P ⇒ I                                                              (pre-invariant)
  ∀&m. ∀mod(body). P ⇒ ¬e ⇒ ( b = (Q ? 1%r : 0%r) )       when ⋈ is =
                             ( ¬Q ⇒ b = 0%r )              when ⋈ is ≥    (pre-bound)
  ∀&m. ∀mod(body). I ⇒ (vrnt ≤ k ∧ (vrnt ≤ 0 ⇒ ¬e))                       (term-invariant)
  [w : abstract] ⊢ phoare[ w : P ==> Q ] ⋈ b ⇒ phoare[ body; w : P ∧ e ==> Q ] ⋈ b   (body)
  ⊢ phoare[ body : I ∧ e ==> I ] = 1%r                                    (out-invariant)
  (∀&m. I ⇒ 0%r < eps) ∧ ∀z. ⊢ phoare[ body : I ∧ e ∧ vrnt = z ==> vrnt < z ] ≥ eps   (vrnt)
  ────────────────────────────────────────────────────────────────────────────────────
                     ⊢ phoare[ while e do body : P ==> Q ] ⋈ b
```

`eps` is the per-iteration lower bound on the probability that the variant decreases, and
`k` its upper bound — together they make the loop almost-surely terminating at a
quantified rate.

> The equiv-side loop rules also *produce* pHL premises — `t_equiv_while_disj_r`
> (`ecPhlWhile.ml:309`, bound at `:340`), `t_equiv_ll_while_disj_r` (`:449`, `:470`, `:489`)
> and the async-while losslessness conditions (`:713`, `:723`) all build
> `phoare[ … ] = 1%r`. Those rules belong to `equiv`, but their side conditions land here.

### 1.9 `call`

**Primitive** — `t_bdhoare_call` (`ecPhlCall.ml:304`, `` `HlCall ``;
`t_bdhoare_call : ss_inv -> ss_inv -> ss_inv option -> backward`, `.mli:38`). Let the
statement end with `lv <@ f(args)` and `s` be the prefix:

```
  ⊢ phoare[ f : P' ==> Q' ] ⋈ b'          (b' = b when no explicit bound is given)
  ⊢ ⟨residual⟩
  ─────────────────────────────────────────────────────────────
      ⊢ phoare[ s; lv <@ f(args) : P ==> Q ] ⋈ b
```

The callee spec is built by `bdhoare_call_spec` (`:291-301`), which **rejects an explicit
bound when `⋈ = ≤`** (`:296`). The residual goal's *logic and bound* depend on `⋈` and on
whether a bound was supplied (`:346-358`):

| `⋈` | explicit bound `b'` | residual goal |
|---|---|---|
| `≤` | not allowed | `hoare[ s : P ==> wp ]` — **a Hoare goal; the logic changes** |
| `=` | none | `phoare[ s : P ==> wp ] = 1%r` |
| `=` | `b'` | `phoare[ s : P ==> wp ] = b / b'` |
| `≥` | none | `phoare[ s : P ==> wp ] = 1%r` |
| `≥` | `b'` | `phoare[ s : P ==> wp ] ≥ b / b'` |

`wp` is `P'[args] ∧ ∀result. ∀mod(f). (post ⋈-oriented-implication Q')`, where the
orientation is `post ⇒ Q'` for `≤`, `Q' ⇒ post` for `≥`, and for `=` it is `⇒` when `b = 0`,
`⇐` when `b = 1`, and `⇔` otherwise (`ecPhlCall.ml:326-336`).

Dispatcher `t_call` bdHoare arms (`ecPhlCall.ml:432`, arms `:449-453`, `:471-477`,
`.mli:41`); elaboration `process_call : oside * call_info gppterm -> backward`
(`:534`, `.mli:44`) — the `FbdHoareS, None` spec arm at `:538-545`, `FbdHoareS, Some _`
rejected at `:555`, the invariant arm at `:620-628`. `call_info` is
`ecParsetree.ml:624-627`; parse syntax `ecParser.mly:3149-3150`.
`process_call_concave` (`:726`, `.mli:46`) is **ehoare only** — no pHL arm.

### 1.10 `proc` — procedure to statement

**Primitive** — `t_bdhoareF_fun_def_r` (`ecPhlFun.ml:104`, `` `FunDef ``;
`t_bdhoareF_fun_def : backward`, `:144`, `.mli:46`):

```
  ⊢ phoare[ body(f) : P[args/params] ==> Q[res/ret] ] ⋈ b[args/params]
  ────────────────────────────────────────────────────────────────────
                 ⊢ phoare[ f : P ==> Q ] ⋈ b
```

Note the bound is substituted too (`ecPhlFun.ml:115`). `f` must be concrete
(`check_concrete`, `:108`). Dispatcher `t_fun_def_r` (`:148-154`), elaboration
`process_fun_def` (`:612`, `.mli:18`).

### 1.11 `proc *` — abstract procedures

**Primitive** — `t_bdhoareF_abs_ge_r` (`ecPhlFun.ml:263`, `` `FunAbs ``). For an abstract
`f` with oracle set `O`, given an invariant `I` not depending on `f`'s top-level module
state (`PV.check_depend`, `:183`):

```
  lossless_hyps(top, f)
  ⊢ phoare[ o : I ==> I ] ≥ 1%r      for each o ∈ O
  ──────────────────────────────────────────────────
       ⊢ phoare[ f : I ==> I ] ≥ 1%r
```

`bdhoareF_abs_spec` (`ecPhlFun.ml:179-189`, `.mli:30`) also runs `check_oracle_use` per
oracle (`:185`) and prepends `lossless_hyps` (`:189`, definition `:42`). Requires `⋈ = ≥`
**and** `b = 1%r` (`:268`). The goal's own pre/post are matched to `I` by a
`t_bdHoareF_conseq` wrapped around the node (`:273`).

**Derived** — `t_bdhoareF_abs_r` (`ecPhlFun.ml:277`; `t_bdhoareF_abs : ss_inv -> backward`,
`:304`, `.mli:41`) extends it to `= 1%r`:

```
  lossless_hyps(top, f)     ⊢ phoare[ o : I ==> I ] ≥ 1%r   for each o ∈ O
  ═══════════════════════════════════════════════════════════════════════════
       ⊢ phoare[ f : I ==> I ] = 1%r
```

*Expansion:* `t_bdHoareF_conseq_bd FHge 1%r` (§2.2) to weaken `= 1%r` to `≥ 1%r`, with its
bound premise closed by `t_trivial` (`:282`), then `_ge_r`, then
`t_bdHoareF_conseq_bd FHeq 1%r` on the per-oracle goals to restore `= 1%r` (`:285`).
A `≥ 1%r` goal goes straight to `_ge_r` (`:287`); any other bound is an error (`:288`).

Elaboration `process_fun_abs : pformula -> backward` (`ecPhlFun.ml:644`, `.mli:19`);
dispatcher `t_fun : inv -> backward` (`:565`, `.mli:53`). Parse syntax
`ecParser.mly:3122`, `:3128`.

> `t_equivF_abs_upto` (`ecPhlFun.ml:405`, `` `FunUpto ``, `.mli:50`) is an *equiv* rule, but
> two of its side conditions are pHL losslessness judgements (`:374`, `:380`).

### 1.12 `fun to code` — procedure to inlined statement

**Primitive** — `t_fun_to_code_bdhoare_r` (`ecPhlFun.ml:480`, `` `FunToCode ``):

```
  ⊢ phoare[ to_code(f) : P[a/arg] ==> Q[r/res] ] ⋈ b[a/arg]
  ─────────────────────────────────────────────────────────
              ⊢ phoare[ f : P ==> Q ] ⋈ b
```

Not exported; reached via `t_fun_to_code_bdhoare` (`:549`), `t_fun_to_code_r` (`:554`) and
`process_fun_to_code` (`:620`, `.mli:22`).

### 1.13 `elim*` and `exists*` — quantifiers in the precondition

**Primitive** — `elim*`, i.e. `t_hr_exists_elim_r` (`ecPhlExists.ml:39`, `` `HlExists ``;
`t_hr_exists_elim_r : ?bound:int -> backward`, `.mli:7`, `t_hr_exists_elim`, `:110`,
`.mli:8`) pulls a prenex `∃` out of the precondition into the ambient context:

```
  ⊢ ∀x⃗. phoare[ c : P' ==> Q ] ⋈ b
  ─────────────────────────────────
  ⊢ phoare[ c : ∃x⃗. P' ==> Q ] ⋈ b
```

The rule body is **logic-generic**: it goes through `tc1_get_pre` / `set_pre`
(`ecLowPhlGoal.ml:265`, `:290`, bdHoare cases `:259-260` and `:304-307`), so the same rule
serves hoare, ehoare, bdhoare and equiv. Parse syntax `ecParser.mly:3298-3299`.

**Derived** — `exists* f₁ … fₙ`, i.e. `t_hr_exists_intro_r`
(`ecPhlExists.ml:49`; `t_hr_exists_intro : inv list -> backward`, `:111`, `.mli:9`), the
converse:

```
  ⊢ phoare[ c : ∃x⃗. (⋀ᵢ xᵢ = fᵢ) ∧ P ==> Q ] ⋈ b
  ══════════════════════════════════════════════
        ⊢ phoare[ c : P ==> Q ] ⋈ b
```

*Expansion:* `EcPhlConseq.t_conseq pre post` (§2.1) with the reshaped precondition, whose
first two premises are closed by an `exists`-introduction script and `t_trivial`
(`ecPhlExists.ml:92-107`). Elaboration `process_exists_intro : elim:bool -> pformula list ->
backward` (`:114`, `.mli:12`; bdHoare arms `:119`, `:122`). Parse syntax
`ecParser.mly:3301-3304`.

### 1.14 `ecall` — apply a procedure contract given as a lemma

**Derived** — `process_ecall_bdhoare` (`ecPhlExists.ml:583`) via `t_ecall_bdhoare_bwd`
(`:469`). Given a lemma `L : phoare[ f : Pf ==> Qf ] = 1%r` and a statement ending in
`lv <@ f(args)`:

```
  ⊢ phoare[ s₁ : P ==> Pf[args] ∧ ∀res, x⃗ ∈ mod(f). (Qf ⇒ Q) ] = 1%r
  ══════════════════════════════════════════════════════════════════
        ⊢ phoare[ s₁; lv <@ f(args) : P ==> Q ] ⋈ b
```

Three requirements: the direction must be **backward** — `ecall` forward on a pHL goal is
rejected (`:588-589`); the contract must be a `bdHoareF` with `⋈ = =` and bound exactly
`1%r`, i.e. **lossless**, else "backward ecall on phoare goals requires a lossless
`= 1%r` contract" (`:510-512`); and the goal's own bound must satisfy `1%r ⋈ b`, since that
is what the internal `condbd` premise reduces to.

*Expansion* (`:524-580`): a `t_bdhoare_seq` (§1.2) at the last position with the trivial
probability split `φ = wp`, `R = true`, `f₁ = f₂ = 1%r`, `g₁ = g₂ = 0%r` (`:532-542`),
producing `[cond_phi; condf1; condf2; condg1; condbd; condnm]`. Then, by index (`:571-578`):
`cond_phi` — a *Hoare* goal on the prefix — is lifted back into pHL by
`EcPhlConseq.t_hoareS_conseq_bdhoare` (§3.3), which is what leaves the single premise above;
`condf2` (the suffix) is closed by `exists*`/`elim*` (§1.13) plus
`EcPhlCall.t_call` (§1.9) against the contract (`:549-558`); and everything else by
`EcPhlAuto.t_auto` (§4.6). The `wp` is built by `EcPhlCall.compute_hoare_call_post`
(`:518-521`, `ecPhlCall.mli:7`).

The contract's shape is validated by `check_contract_type ~phoare:true` (`:152`, called at
`:606`). Dispatcher `process_ecall : pdirection -> oside -> pecall -> backward`
(`:777`, `.mli:13`; bdHoare arm `:789-792`, which also rejects a `side` argument); the
Hoare and equiv arms are `process_ecall_hoare` (`:613`) and `process_ecall_equiv` (`:645`).
Parse syntax `ecParser.mly:3306-3307`.

### 1.15 `case`

**Primitive** — `t_bdhoare_case_r` (`ecPhlCase.ml:34`, `` `HlCase f ``;
`t_bdhoare_case : ?simplify:bool -> ss_inv -> backward`, `:59`, `.mli:7`):

```
  ⊢ phoare[ c : P ∧ φ ==> Q ] ⋈ b     ⊢ phoare[ c : P ∧ ¬φ ==> Q ] ⋈ b
  ────────────────────────────────────────────────────────────────────
                  ⊢ phoare[ c : P ==> Q ] ⋈ b
```

Sound here — unlike a *postcondition* split — because both branches keep the same bound and
the preconditions are exclusive. Dispatcher `t_hl_case : ?simplify:bool -> inv -> backward`
(`ecPhlCase.ml:66`, `.mli:10`; `~tbh:` at `:72`, `Inv_ts` rejected at `:81`).

### 1.16 `exfalso` — the `false` precondition axiom

**Primitive** — `t_core_exfalso_r` (`ecPhlTAuto.ml:43`, `` `ExFalso ``, **zero premises**;
`t_core_exfalso`, `:49`, `.mli:6`):

```
  ────────────────────────────────
  ⊢ phoare[ c : false ==> Q ] ⋈ b
```

Logic-generic via `tc1_get_pre` (`:44`).

**Derived** — the surface `exfalso` (`t_exfalso_r`, `ecPhlAuto.ml:16`; `t_exfalso`, `:27`,
`.mli:6`) also applies when the precondition is merely *equivalent* to `false`:

```
  ∀&m. P ⇒ false
  ══════════════════════════════
  ⊢ phoare[ c : P ==> Q ] ⋈ b
```

*Expansion:* `t_core_exfalso` directly if `P` is syntactically `false`; otherwise
`t_conseq false Q` (§2.1), whose post premise is closed by `t_trivial` and whose judgement
premise by `t_core_exfalso` (`ecPhlAuto.ml:20-25`). Parse syntax `ecParser.mly:3309-3310`.

Its siblings `t_hoare_true` (`ecPhlTAuto.ml:10`, `.mli:5`) and `t_ehoare_zero` (`:28`,
`.mli:7`) have **no** pHL arm — there is no "`phoare[… ==> true]` closes" axiom, because the
bound still has to be discharged. `prbounded` (§4.3) plays that role instead.

---

## 2. The `conseq` family

`conseq` routes on goal-form × invariant token over 11 variants; `process_conseq` is ~2.5k
lines. This section is only its pHL slice. All line numbers are in `ecPhlConseq.ml`.

### 2.1 Consequence (pre/post)

**Primitive** — `t_bdHoareF_conseq` / `t_bdHoareS_conseq` (`:243`, `:259`,
`` `HlConseq ``, 3 premises; `.mli:16-17`). The postcondition premise is oriented by `⋈` —
this is the one thing that distinguishes pHL consequence from Hoare consequence
(`bdHoare_conseq_conds`, `:218-231`, on top of the generic `conseq_cond_ss`, `:64-70`):

| `⋈` | postcondition premise |
|---|---|
| `≤` | `Q ⇒ Q'` |
| `=` | `Q ⇔ Q'` |
| `≥` | `Q' ⇒ Q` |

```
  ∀&m. P ⇒ P'      ∀&m. ⟨Q vs Q' per table⟩      ⊢ phoare[ f : P' ==> Q' ] ⋈ b
  ────────────────────────────────────────────────────────────────────────────
                        ⊢ phoare[ f : P ==> Q ] ⋈ b
```

The direction is forced: at an upper bound you may only *weaken* the postcondition, at a
lower bound only *strengthen* it, and at an exact bound it must be equivalent.

Dispatcher `t_conseq : inv -> inv -> backward` (`:353`, bdHoare arms `:369-370`, `.mli:44`).

### 2.2 Bound and comparison change

**Primitive** — `t_bdHoareF_conseq_bd` / `t_bdHoareS_conseq_bd`
(`:279`, `:293`, `` `HlConseq ``, 2 premises; `.mli:21-22`):

```
  ∀&m. P ⇒ ⟨bd_goal⟩       ⊢ phoare[ f : P ==> Q ] ⋈' b'
  ──────────────────────────────────────────────────────
             ⊢ phoare[ f : P ==> Q ] ⋈ b
```

`bd_goal_r` (`:95-106`) is a **partial** function of `(⋈, ⋈')` — the admissible changes:

| goal `⋈` | new `⋈'` | premise |
|---|---|---|
| `≤` | `≤` or `=` | `b' ≤ b` |
| `≥` | `≥` or `=` | `b ≤ b'` |
| `=` | `=` | `b' = b` |
| `=` | `≥` | `b = 1%r ∧ b' = 1%r` |
| `=` | `≤` | `b = 0%r ∧ b' = 0%r` |
| otherwise | — | user error (`bd_goal`, `:108-122`) |

This is the workhorse used internally by `skip` (§1.1), `proc *` (§1.11), `hoare` (§3.2),
`phoare split` (§3.4–§3.5) and `islossless` (§4.5) to normalise a bound before applying
their real rule.

### 2.3 Not-modified variants

**Primitive** — `t_bdHoareF_notmod` / `t_bdHoareS_notmod` (`:607`, `:623`, `` `HlNotmod ``,
2 premises; condition builders `cond_bdHoareF_notmod` `:590` and `cond_bdHoareS_notmod`
`:617`; *not exported*). Same as §2.1, but the postcondition premise is generalised over the
variables the statement (or procedure) writes, so it need only hold for the modified part of
memory:

```
  ∀&m. P ⇒ ∀res, x⃗ ∈ mod. ⟨Q vs Q' per the §2.1 table⟩
  ⊢ phoare[ f : P ==> Q' ] ⋈ b
  ──────────────────────────────────────────────────────
             ⊢ phoare[ f : P ==> Q ] ⋈ b
```

**Derived** — `t_bdHoareF_conseq_nm` / `t_bdHoareS_conseq_nm` (`:651`, `:652`, `.mli:33-34`)
combine the two, changing pre *and* post in the not-modified style:

```
  ∀&m. P ⇒ P'
  ∀&m. P ⇒ ∀res, x⃗ ∈ mod. ⟨Q vs Q' per the §2.1 table⟩
  ⊢ phoare[ f : P' ==> Q' ] ⋈ b
  ══════════════════════════════════════════════════════
             ⊢ phoare[ f : P ==> Q ] ⋈ b
```

*Expansion* (`gen_conseq_nm`, `:633-645`): `t_bdHoare*_notmod post` then
`t_bdHoare*_conseq pre post` on the residual, with the latter's own post premise closed by
`t_trivial`, and the two surviving goals swapped so the pre premise comes first.

### 2.4 Postcondition conjunction split

**Primitive** — `t_bdHoareS_conseq_conj` / `t_bdHoareF_conseq_conj` (`:992`, `:1013`,
`` `HlConseqBd ``, 2 premises; *not exported*). Splits a conjunct off the postcondition into
a *Hoare* side condition — sound because the Hoare part is certain and therefore consumes no
probability mass. Two directions (`~add`):

`~add:false` — strip `post` from a goal whose post is `post'`:

```
  ⊢ hoare[ c : P ==> post ]      ⊢ phoare[ c : P ==> post' ∧ post ] ⋈ b
  ─────────────────────────────────────────────────────────────────────
                ⊢ phoare[ c : P ==> post' ] ⋈ b
```

`~add:true` — factor `post` out of a goal whose post is already `post' ∧ post`:

```
  ⊢ hoare[ c : P ==> post ]      ⊢ phoare[ c : P ==> post' ] ⋈ b
  ──────────────────────────────────────────────────────────────
           ⊢ phoare[ c : P ==> post' ∧ post ] ⋈ b
```

The goal's actual postcondition is checked against the reconstruction with
`ss_inv_alpha_eq` (`:1002`, `:1025`).

### 2.5 Transitivity via an equivalence

**Primitive** — `t_bdHoareF_conseq_equiv` (`:1233`, `` `BdHoareFConseqEquiv ``, 4 premises;
*not exported*). Proves a pHL judgement about `f₁` from an equivalence with `f₂` plus a pHL
judgement about `f₂`. The bound is transferred by an equality inside `cond1` — the only
difference from the Hoare version (`transitivity_side_cond ?bds`, `:1164-1200`, bound
handling `:1180-1194`):

```
  ∀&m₁. P₁ ⇒ ∃&m₂. P &m₁ &m₂ ∧ P₂ &m₂ ∧ b₁ = b₂[&m₂]        (cond1)
  ∀&m₁ &m₂. Q &m₁ &m₂ ⇒ Q₂ &m₂ ⇒ Q₁ &m₁                     (cond2)
  ⊢ equiv[ f₁ ~ f₂ : P ==> Q ]                              (ef)
  ⊢ phoare[ f₂ : P₂ ==> Q₂ ] ⋈ b₂                           (hf2)
  ────────────────────────────────────────────────────────────
            ⊢ phoare[ f₁ : P₁ ==> Q₁ ] ⋈ b₁
```

The Hoare analogue is `t_hoareF_conseq_equiv` (`:1209`, `` `HoareFConseqEquiv ``).

### 2.6 The surface `conseq` — derived rules

`conseq` takes up to three proof-term arguments. On a pHL goal exactly two shapes are
accepted (the supported combinations are listed in the source at `:1536-1541` for the
statement form and `:1627-1633` for the procedure form). Both are **derived**, and both run
in *not-modified* style by default, discharging every premise that `t_hi_trivial` (`:1301`)
can close.

**(a) `conseq (: P' ==> Q')`, optionally `: ⋈' b'`** — one pHL cut:

```
  ∀&m. P ⇒ P'
  ∀&m. P ⇒ ∀res, x⃗ ∈ mod. ⟨Q vs Q' per the §2.1 table⟩
  ∀&m. P ⇒ ⟨bd_goal(⋈, b, ⋈', b') per the §2.2 table⟩
  ⊢ phoare[ f : P' ==> Q' ] ⋈' b'
  ═══════════════════════════════════════════════════════
             ⊢ phoare[ f : P ==> Q ] ⋈ b
```

*Expansion* (`t_hi_conseq_bdHoareS`, `:1543-1559`; `t_hi_conseq_bdHoareF`, `:1635-1651`):
`t_bdHoareS_conseq_bd ⋈' b'` (§2.2) then `t_bdHoareS_conseq_nm P' Q'` (§2.3), the supplied
judgement being discharged by its proof term. When the bound is unchanged the third premise
is `b ⋈ b` and vanishes; when `P ⇒ P'` is trivial the first vanishes too. So
`conseq (: P' ==> Q')` on an unchanged bound typically leaves **2** goals, and
`conseq (: _ ==> _ : ⋈' b')` leaves **2** as well.

**(b) `conseq (: P' ==> Q') (: Pₕ ==> Qₕ)`** — a pHL cut plus a **Hoare** cut, letting you
carry a certain fact alongside the bounded one:

```
  ∀&m. P ⇒ P' ∧ Pₕ
  ⊢ hoare[ c : P' ∧ Pₕ ==> Qₕ ]
  ∀&m. P ⇒ ⟨bd_goal per §2.2⟩
  ∀&m. P ⇒ ∀res, x⃗ ∈ mod. ⟨Q vs Q' ∧ Qₕ per the §2.1 table⟩
  ⊢ phoare[ c : P' ==> Q' ] ⋈ b
  ══════════════════════════════════════════════════════════
             ⊢ phoare[ c : P ==> Q ] ⋈ b
```

*Expansion* (`:1562-1622`): a `t_cut` of the pre implication, then `t_hoareS_conseq` on the
Hoare cut, `t_bdHoareS_conseq_bd`, and `t_bdHoareS_conseq_conj ~add:false` / `~add:true`
(§2.4) around `t_bdHoareS_conseq_nm` (§2.3) to graft `Qₕ` onto the postcondition and strip
it again.

**(c) From a Hoare goal into pHL** — `conseq (: _ ==> _ : ⋈ b)` applied to a `hoare` goal
builds a pHL cut instead (`process_conseq_hs`, `:2220`, bd arms `:2243-2247`, `:2261-2265`),
composing §3.3 then §2.2 then §2.1 (`t_hi_conseq_hoareS/F` bdHoare arms `:1398-1408`,
`:1457-1467`).

**(d) From an equiv goal into pHL** — `conseq` with a pHL cut on an `equiv` goal routes to
§3.7 (`t_hi_conseq_equivS` bdHoare arms `:1788`, `:1799`, `:1830`, `:1848`).

Other entry points: `t_hi_conseq` (`:1949`, bdHoare `:1962-1963`); `process_conseq_ss` cut
builders (`:2019`, bd arms `:2050`, `:2063`, `:2131`, `:2138`, `:2164`);
`process_conseq : bool -> conseq_ppterm option tuple3 -> backward` (`:2353`, `.mli:47`);
`process_conseq_opt` (`:2388`, `.mli:51`) — the parser entry;
`t_conseqauto : ?delta:bool -> ?tsolve:backward -> backward` (`:2408`, `.mli:55`, bdHoare
arms `:2420-2421`), which drives the §2.3 notmod rules automatically. `conseq_info` is
`ecParsetree.ml:768`; parse syntax `ecParser.mly:3272-3296`, the `: ⋈ b` suffix at
`:2614-2616`. `process_concave` (`:820`, `.mli:57`) is **ehoare only**.

---

## 3. Views and bound splitting

### 3.1 `hoare` — the `= 0%r` view, both directions

**Primitive**, four rules — `t_hoare_of_bdhoareS_r` / `…F_r` (`ecPhlCoreView.ml:9`, `:24`)
and `t_bdhoare_of_hoareS_r` / `…F_r` (`:37`, `:51`), all `` `ViewBdHoare ``, 1 premise;
exported as `t_hoare_of_bdhoareS` … (`:62-65`, `.mli:5-8`).

The two logics coincide at bound `0`: `phoare[c : P ==> Q] = 0%r` says `Q` is almost never
established, i.e. `hoare[c : P ==> ¬Q]`.

```
  ⊢ hoare[ c : P ==> ¬Q ]                      ⊢ phoare[ c : P ==> ¬Q ] = 0%r
  ─────────────────────────────                ─────────────────────────────
  ⊢ phoare[ c : P ==> Q ] = 0%r                    ⊢ hoare[ c : P ==> Q ]
```

Side conditions: left-to-right requires `⋈ = =` **and** `b = 0%r` syntactically
(`ecPhlCoreView.ml:11`, `:26`); right-to-left requires the Hoare postcondition to be
exception-free, `POE.is_empty` (`:40`, `:54`).

### 3.2 `hoare` — the surface tactic

**Derived** — `t_hoare_bd_hoare` (`ecPhlBdHoare.ml:16`, `.mli:9`). On a pHL goal:

```
  ∀&m. P ⇒ (0%r ⋈ b)         ⊢ hoare[ c : P ==> ¬Q ]
  ══════════════════════════════════════════════════
        ⊢ phoare[ c : P ==> Q ] ⋈ b
```

*Expansion:* if `⋈ = =` and `b` is syntactically `0%r`, the view of §3.1 applies directly and
the first premise is absent (`:21-22`, `:30-31`). Otherwise `t_bdHoare*_conseq_bd FHeq 0%r`
(§2.2) normalises the bound — producing the first premise, which is then `t_try`-attempted by
`t_pl_trivial` — and the view is applied to the result (`:24-27`, `:33-36`). On a **Hoare**
goal it applies the reverse view directly (`:38-39`). Instantiating via `bd_goal_r`:
`≤ b` → `0%r ≤ b`; `≥ b` → `b ≤ 0%r`; `= b` → `b = 0%r`. Parse syntax
`ecParser.mly:3365-3366`.

### 3.3 hoare ⇒ pHL at bound `1`

**Primitive** — `t_hoareS_conseq_bdhoare` / `t_hoareF_conseq_bdhoare`
(`ecPhlConseq.ml:904`, `:916`, `` `HlConseqBd ``, 1 premise; the statement form is exported
at `.mli:26`, the procedure form is not):

```
  ⊢ phoare[ c : P ==> Q ] = 1%r
  ─────────────────────────────
    ⊢ hoare[ c : P ==> Q ]
```

Requires the Hoare post to be exception-free (`:907`, `:919`). Reached from
`t_hi_conseq_hoareS/F` (§2.6c).

### 3.4 `phoare split` on a conjunctive or disjunctive postcondition

**Primitive** — `t_bdhoare_split_bop` (`ecPhlBdHoare.ml:55`, `` `BdHoareSplit ``,
3 premises). For a postcondition `A ∧ B` (or `A ∨ B`), with `⊕` the *dual* connective — `∨`
for a conjunctive post, `∧` for a disjunctive one:

```
  ⊢ phoare[ c : P ==> A ] ⋈ b₁
  ⊢ phoare[ c : P ==> B ] ⋈ b₂
  ⊢ phoare[ c : P ==> A ⊕ B ] ⋈ᵒᵖ b₃
  ────────────────────────────────────
  ⊢ phoare[ c : P ==> A ∧ B ] ⋈ b      (dually, A ∨ B)
                                       [ requires b syntactically b₁ + b₂ − b₃ ]
```

This is inclusion–exclusion: `Pr[A ∧ B] = Pr[A] + Pr[B] − Pr[A ∨ B]`. The identity is
*checked*, not proven — by a bare `assert` (`:65`, see §7.3). `and_dt` (`:109-121`) destructs
`∧` and rebuilds with `∨`; `or_dt` (`:129-141`) the converse.

**Derived** — the surface `phoare split b₁ b₂ [b₃]` (`t_bdhoare_split_bop_conseq`, `:69`;
`t_bdhoare_and` / `t_bdhoare_or`, `:123`, `:143`, `.mli:6-7`), which lifts the syntactic
requirement:

```
  ∀&m. P ⇒ (b₁ + b₂ − b₃ ⋈ b)
  ⊢ phoare[ c : P ==> A ] ⋈ b₁
  ⊢ phoare[ c : P ==> B ] ⋈ b₂
  ⊢ phoare[ c : P ==> A ⊕ B ] ⋈ᵒᵖ b₃
  ═══════════════════════════════════
  ⊢ phoare[ c : P ==> A ∧ B ] ⋈ b
```

*Expansion:* if `b` is already syntactically `b₁ + b₂ − b₃`, the primitive applies and the
first premise is absent; otherwise `t_bdHoare*_conseq_bd ⋈ (b₁+b₂−b₃)` (§2.2) runs first
(`:75-77`). `b₃` defaults to `0%r` when omitted (`ecPhlHiBdHoare.ml:38`).
`t_bdhoare_and` / `t_bdhoare_or` are S/F dispatchers over `gen_S` (`:87`) / `gen_F` (`:98`).

Confirmed against the implementation — for `phoare[ c : true ==> A ∧ B ] = 1%r/4%r` with
`phoare split (1%r/2%r) (1%r/2%r) (3%r/4%r)`, EasyCrypt emits exactly

```
forall _, 1%r / 2%r + 1%r / 2%r - 3%r / 4%r = 1%r / 4%r
phoare[ c : true ==> A ]      = 1%r / 2%r
phoare[ c : true ==> B ]      = 1%r / 2%r
phoare[ c : true ==> A \/ B ] = 3%r / 4%r
```

— note the **dual** connective in the third pHL goal.

> **`phoare split` is statement-only.** The rules are S/F-generic, and
> `process_bdhoare_split` accepts an `FbdHoareF` goal at its own dispatch
> (`ecPhlHiBdHoare.ml:21-22`), but the elaboration crashes before reaching them — see §7.6.
> Apply `proc` first.

### 3.5 `phoare split !` on a negation

**Primitive** — `t_bdhoare_split_not` (`ecPhlBdHoare.ml:149`, `` `BdHoareSplit ``,
2 premises):

```
  ⊢ phoare[ c : P ==> true ] ⋈ b₁      ⊢ phoare[ c : P ==> ¬Q ] ⋈ᵒᵖ b₂
  ──────────────────────────────────────────────────────────────────────
                   ⊢ phoare[ c : P ==> Q ] ⋈ b
                                        [ requires b syntactically b₁ − b₂ ]
```

`Pr[Q] = Pr[true] − Pr[¬Q]`. Again the identity is `assert`ed (`:155`, §7.3).

**Derived** — the surface `phoare split ! b₁ b₂` (`t_bdhoare_split_not_conseq`, `:158`;
`t_bdhoare_not : ss_inv -> ss_inv -> backward`, `:172`, `.mli:8`):

```
  ∀&m. P ⇒ (b₁ − b₂ ⋈ b)
  ⊢ phoare[ c : P ==> true ] ⋈ b₁      ⊢ phoare[ c : P ==> ¬Q ] ⋈ᵒᵖ b₂
  ═════════════════════════════════════════════════════════════════════
                   ⊢ phoare[ c : P ==> Q ] ⋈ b
```

*Expansion:* as §3.4, but the "already normalised" test uses `EcReduction.ss_inv_alpha_eq`
rather than `f_equal` (`:164`). Confirmed: for `phoare[ c : true ==> Q ] ≤ 1%r/2%r` with
`phoare split ! (1%r) (1%r/2%r)` EasyCrypt emits

```
forall _, true => 1%r - 1%r / 2%r <= 1%r / 2%r
phoare[ c : true ==> true ] <= 1%r
phoare[ c : true ==> !Q ]   >= 1%r / 2%r
```

### 3.6 `phoare split` case form

**Derived** — `BDH_split_or_case (b₁, b₂, φ)` (`ecPhlHiBdHoare.ml:42-72`), surface
`phoare split b₁ b₂ : φ`. It case-splits the postcondition on an arbitrary `φ`:

```
  ∀&m. P ⇒ (b₁ + b₂ ⋈ b)
  ⊢ phoare[ c : P ==> φ ∧ Q ]  ⋈ b₁
  ⊢ phoare[ c : P ==> ¬φ ∧ Q ] ⋈ b₂
  ══════════════════════════════════
     ⊢ phoare[ c : P ==> Q ] ⋈ b
```

*Expansion:* `t_conseq` (§2.1) rewrites the post to `(φ ∧ Q) ∨ (¬φ ∧ Q)` using the `orDandN`
lemma (`:63-66`); then §3.4's `t_bdhoare_or` with `b₃ = 0%r` (`:67`); the resulting
intersection premise `phoare[ c : P ==> (φ ∧ Q) ∧ (¬φ ∧ Q) ] ⋈ᵒᵖ 0%r` is closed by a further
`t_conseq` to `false` via `andDorN` plus `process_trivial` (`:68-71`).

Elaboration for all three forms: `process_bdhoare_split : EcParsetree.bdh_split -> backward`
(`ecPhlHiBdHoare.ml:13`, `.mli:5`); `bdh_split` is `ecParsetree.ml:688-691`. Parse syntax
`ecParser.mly:3371-3372` (`phoare split`) and the `bdhoare_split` production `:3414-3422`.

### 3.7 `phoare equiv` — equiv ⇒ pHL on one side

**Primitive** — `t_equivS_conseq_bd : side -> ss_inv -> ss_inv -> backward`
(`ecPhlConseq.ml:1115`, `` `HlBdEquiv ``, 1 premise, `.mli:41`). When the other side's
statement is empty, an equivalence collapses to a pHL judgement:

```
  ⊢ phoare[ c : P ==> Q ] = 1%r
  ─────────────────────────────────────
  ⊢ equiv[ c ~ [] : P⟨1⟩ ==> Q⟨1⟩ ]        (side = Left; dually for Right)
```

Side conditions: the *other* side's statement must be empty (`:1130-1133`), and the equiv
pre/post must be alpha-equal to the one-sided generalisations of `P` and `Q` (`:1134-1137`).
Elaboration `process_bd_equiv : side -> pformula pair -> backward` (`:2365`, `.mli:48`);
parse syntax `ecParser.mly:3374-3375`.

---

## 4. Probability bridges

These connect pHL to the `Pr[…]` language of the ambient logic.

### 4.1 `byphoare`

**Primitive** — `t_core_phoare_deno` (`ecPhlDeno.ml:37`, `` `HlDeno ``, 3 premises):

```
  ⊢ phoare[ f : P ==> Q ] ⋈ b        P[args/arg, &m/&hr]        ∀&m. ev ⟨↔ per ⋈⟩ Q
  ─────────────────────────────────────────────────────────────────────────────────
                          Pr[ f(args) @ &m : ev ] ⋈ b
```

The comparison `⋈` is **read off the goal shape** (`ecPhlDeno.ml:41-56`): `Pr[…] ≤ b` gives
`≤` with `ev ⇒ Q`, `b ≤ Pr[…]` gives `≥` with `Q ⇒ ev`, and `Pr[…] = b` gives `=` with
`ev ⇔ Q`. Any other shape is a user error (`:55`).

**Derived** — `t_phoare_deno_r` (`:76`; `t_phoare_deno : ss_inv -> ss_inv -> backward`,
`:177`, `.mli:7`) extends it to a goal written the other way round, `b = Pr[…]`:

```
  ⊢ phoare[ f : P ==> Q ] = b     P[args/arg]     ∀&m. ev ⇔ Q
  ═══════════════════════════════════════════════════════════
                 b = Pr[ f(args) @ &m : ev ]
```

*Expansion:* `t_symmetry` to flip the equation, then the primitive (`:79-84`).

Elaboration ``process_deno `PHoare`` (`:613`, `.mli:13`) / `process_phoare_deno` (`:182`);
it builds the cut at `:214` and reads it back with `pf_as_bdhoareF` at `:222`.
`deno_ppterm` is `ecParsetree.ml:766`; parse syntax `ecParser.mly:3254-3255`.

### 4.2 `bypr`

**Primitive** — `t_bdhoare_ppr_r` (`ecPhlPr.ml:21`, `` `PPR ``, 1 premise;
`t_bdhoare_ppr : backward`, `:78`, `.mli:9`). The converse direction — turn a pHL goal into
an ambient statement about `Pr`:

```
  ∀&hr. P ⇒ Pr[ f(args) @ &hr : Q ] ⋈ b
  ──────────────────────────────────────
       ⊢ phoare[ f : P ==> Q ] ⋈ b
```

**Derived** — `t_hoare_ppr_r` (`:44`, `.mli:8`) does the same for a Hoare goal:

```
  ∀&hr. P ⇒ Pr[ f(args) @ &hr : ¬Q ] = 0%r
  ═════════════════════════════════════════
         ⊢ hoare[ f : P ==> Q ]
```

*Expansion:* `EcPhlCoreView.t_bdhoare_of_hoareF` (§3.1) then `t_bdhoare_ppr_r` (`:46`).

Elaboration `process_ppr` (`:82`, `.mli:17`; `~tbh:` at `:85`, via
`t_hF_or_bhF_or_eF`). Parse syntax `ecParser.mly:3312-3316`.

### 4.3 `prbounded`

**Primitive** — `t_prbounded_r` (`ecPhlPr.ml:99`, `` `PrBounded ``, 0 or 1 premise;
`t_prbounded : bool -> backward`, `:128`, `.mli:13`). Closes a pHL goal whose bound is
trivially satisfied. With `conseq = false` only the first three rows apply
(`ecPhlPr.ml:114-124`):

```
  ────────────────────────────────         ────────────────────────────────
  ⊢ phoare[ c : P ==> Q ] ≤ 1%r            ⊢ phoare[ c : P ==> Q ] ≥ 0%r

  ────────────────────────────────
  ⊢ phoare[ c : P ==> false ] ⋈ 0%r        [ ⋈ arbitrary; requires b = 0%r ]
```

and, with `conseq = true` (the surface tactic), the two catch-alls

```
  ∀&m. P ⇒ 1%r ≤ b                       ∀&m. P ⇒ b ≤ 0%r
  ─────────────────────────────          ─────────────────────────────
  ⊢ phoare[ c : P ==> Q ] ≤ b            ⊢ phoare[ c : P ==> Q ] ≥ b
```

Anything else is a user error, "cannot solve the probabilistic judgement" (`:123`).

This is the pHL analogue of `t_hoare_true`, and the only rule in this file that is
*exclusively* pHL — its dispatcher accepts `FbdHoareF` / `FbdHoareS` and nothing else
(`:104-111`). Parse syntax `ecParser.mly:3368-3369`; `t_prbounded true` is what
`prbounded` runs (`ecHiTacticals.ml:239`).

Its sibling `t_prfalse` (`:131`, `` `PrFalse ``, `.mli:14`) operates on `Pr[…]` goals, not
pHL ones.

### 4.4 `fel` — the failure-event lemma

**Primitive** — `t_failure_event_r` (`ecPhlFel.ml:117`, emission `:250`,
`` `Fel (cntr, ash, q, f_event, pred_specs) ``). The goal is `Pr[…] ≤ bd`, not a pHL
judgement — but pHL is where its central obligation lives. Given a counter `cntr`, a
per-query bound function `ash`, a query bound `q`, a failure event `F`, per-oracle
preconditions `spec(·)`, an invariant `I`, and the split position `at_pos` (the body is
`s_hd; s_tl`, FEL applying to `s_tl`):

```
  big ash (range 0 q) ≤ bd                                               (bound_goal :155)
  ∀&m. I ⇒ ev ⇒ (F ∧ cntr ≤ q)                                           (post_goal :161)
  ⊢ hoare[ s_hd : args-and-globals-match ==> ¬F ∧ cntr = 0 ∧ I ]         (init_goal :177)
  for each callable oracle o:
    ⊢ phoare[ o : 0 ≤ cntr < q ∧ ¬F ∧ I ∧ spec(o) ==> F ] ≤ ash cntr     (not_F_to_F :205)
    ∀c. ⊢ hoare[ o : spec(o) ∧ cntr = c ∧ I ==> c < cntr ∧ I ]           (cntr_decr :219)
    ∀b c. ⊢ hoare[ o : ¬spec(o) ∧ F = b ∧ cntr = c ∧ I ==> F = b ∧ c ≤ cntr ∧ I ]
                                                                        (cntr_stable :228)
  ──────────────────────────────────────────────────────────────────────
                     Pr[ f(args) @ &m : ev ] ≤ bd
```

Only `not_F_to_F` (`:205-212`) is a pHL premise; the other per-oracle obligations are Hoare.
Premise order is `bound_goal :: post_goal :: init_goal :: os_goals` (`:249`), the oracle
triples appended per oracle (`:243`, `:247`). Side condition: the failure event, counter and
invariant must be modified *only* inside oracles (`PV.indep` check, `:147-152`). Requires the
`FelTactic` theory to be loaded (`:263-264`).

`t_failure_event` (`:255`, `.mli:9-14`); `process_fel` (`:260`, `.mli:17`); `fel_info` is
`ecParsetree.ml:756-763`; parse syntax `ecParser.mly:3318-3327`.

### 4.5 `islossless`

**Derived** — `t_lossless` (`ecPhlHiAuto.ml:123`, `.mli:5`). `islossless f` is notation for
the goal `phoare[ f : true ==> true ] = 1%r` (`ecParser.mly:1218`, keyword
`ecLexer.mll:63`). The tactic aims to close it outright:

```
  ═══════════════════════════════════════
  ⊢ phoare[ f : true ==> true ] = 1%r
                     [ f built only from assignments, samplings, calls to lossless
                       procedures, and conditionals thereof ]
```

*Expansion.* `t_lossless` first strips the procedure with `EcPhlFun.t_bdhoareF_fun_def`
(§1.10), possibly repeatedly (`:126-130`), then runs `t_lossless1_r` (`:102`). That wraps the
goal in `t_bdHoareS_conseq true true` (§2.1) and `t_bdHoareS_conseq_bd FHeq 1%r` (§2.2) to
normalise it (`:114-116`), and applies a syntax-directed strategy
(`ll_strategy_of_stmt`, `:21-40`) instruction by instruction, back to front:

| strategy step | for | rules composed | file:line |
|---|---|---|---|
| `LL_WP` | assignment | `wp` (§5.1) | `:57-58` |
| `LL_RND` | sampling | `rnd` with `PNoRndParams` (§1.6b) + `t_bdHoareS_conseq` | `:60-64` |
| `LL_CALL` | procedure call | `t_bdhoare_call true true None` (§1.9) | `:66-68` |
| `LL_JUMP` | anything else | `t_bdhoare_seq` with `(true, true, 1, 1, 0, 1)` (§1.2) | `:70-82` |
| `LL_COND` | conditional | `t_bdhoare_seq` then `t_bdhoare_cond` (§1.3) per branch | `:84-99` |

Every side goal the strategy raises is closed by `ll_trivial`
(`t_pl_trivial ~bases:["random"; "lossless"]`, `:43`), and each leaf is finished with
`t_skip` (§1.1) and `t_crush` (`:106-109`). On an `equiv` goal it splits both sides with
`t_equiv_seq_onesided` first and proves each separately (`:145-153`). Anything else is
"invalid initial goal for `islossless`" (`:132-133`). Parse syntax `ecParser.mly:3380-3381`.

### 4.6 `auto`, `trivial`, `exfalso`

**Derived.** These are the automation entry points; none introduces a rule of its own, they
just try the ones above. Their pHL content:

- `t_auto_rnd_bdhoare_r` (`ecPhlAuto.ml:38`) applies §1.6(c/d) with the event `predT`
  (`prnd_info`, `:30-31`) when the statement ends in a sampling, and errors otherwise;
  `t_auto_rnd` fans it over the logics (`:70-74`).
- `t_auto_phl_r` (`:77-83`) loops `wp` (§5.1) then either `auto_rnd` again or `skip` (§1.1).
- `t_auto : ?conv:… -> backward` (`:88`, `:97`, `.mli:9`) tries, in order,
  `t_hoare_true`, `t_core_exfalso` (§1.16), `t_prbounded false` (§4.3), `t_ehoare_zero`,
  `t_auto_phl` (`:90-94`). Of these, `t_core_exfalso` and `t_prbounded` are the two that can
  close a pHL goal. Parse syntax `ecParser.mly:3377-3378`.
- `t_phl_trivial` (`:100`, `:110`, `.mli:7`) is the same list with `t_skip` instead of
  `t_auto_phl`, wrapped in `t_try`; `t_pl_trivial` (`:112`, `:118`, `.mli:8`) adds
  `EcLowGoal.t_solve` and the ambient `t_trivial`. This is the tactic that silently
  discharges the bound premises of §1.1, §3.2 and §3.4.

### 4.7 `rewrite Pr[…]`

**Derived** — `t_pr_rewrite_i : symbol * ss_inv option -> backward` (`ecPhlPrRw.ml:342`,
`.mli:7`) is an ambient rewrite on `Pr[…]` terms, driven by `t_pr_rewrite_low` (`:218`); its
primitive leaf is `t_pr_lemma` (`:13`, `` `RwPr ``, 0 premises), which just checks the goal
against the instantiated lemma. It appears here because one of the lemmas it can instantiate,
`pr_mu1_le_eq_mu1` (`:97`), carries a pHL hypothesis
`phoare[ f : true ==> true ] = 1%r` (`:100`) — i.e. rewriting under it hands you a
losslessness obligation, normally closed by §4.5.

### 4.8 One-sided `call` from an equiv goal

**Primitive** — `t_equiv_call1 : side -> ss_inv -> ss_inv -> backward` (`ecPhlCall.ml:390`,
`` `HlCall ``, `.mli:40`) is an *equiv* rule, but its callee obligation is a pHL
losslessness spec `phoare[ f : P ==> Q ] = 1%r` (`:405`). Listed here because it is a common
source of pHL goals in relational proofs.

---

## 5. Code transforms

Every tactic in this section obeys one schema: transform the statement, rewrap the *same*
judgement. Pre, post, `⋈` and bound are carried through untouched.

```
  ⊢ phoare[ tx(c) : P ==> Q ] ⋈ b   [+ transform-specific premises]
  ─────────────────────────────────────────────────────────────────
            ⊢ phoare[ c : P ==> Q ] ⋈ b
```

The shared machinery lives in `ecLowPhlGoal.ml`: `tc1_get_stmt` (`:194`, bdHoare `:199`),
`hl_set_stmt` (`:242`, bdHoare `:247`), `t_code_transform` (`:797`, bdHoare arm `:816-821`),
and the two transform shapes `t_fold` (`:783`) / `t_zip` (`:790`).

### 5.1 `wp`

**Primitive** — `TacInternal.t_bdhoare_wp` (`ecPhlWp.ml:221`, `` `Wp ``, 1 premise):

```
  ⊢ phoare[ s_hd : P ==> wp(s_wp, Q) ] ⋈ b
  ────────────────────────────────────────
    ⊢ phoare[ s_hd; s_wp : P ==> Q ] ⋈ b
```

`s_wp` is the suffix from the given position (`o_split`, `ecLowPhlGoal.ml:409`), and at least
one instruction must be consumed (`check_wp_progress`, `ecPhlWp.ml:185-190`).

**`wp` is deliberately restricted for pHL.** `wp_instr` (`:62-118`) handles only
`Sasgn` (`:73`), `Sif` (`:76`) and `Smatch` (`:91`); `Sraise` is accepted only in the
`onesided` (Hoare) mode (`:115`), and everything else — in particular **`Srnd` and `Scall`** —
raises `No_wp` (`:118`). The `.mli` states the reason: "WP only operates over assignments and
conditional statements. Any weakening of this restriction may break the soundness of the
bounded hoare logic" (`ecPhlWp.mli:10-13`) — the note predates the `match` case.

Dispatcher `t_wp : ?uselet:bool -> (codegap1 doption) option -> backward` (`:262`, `:282`,
`.mli:15`), elaboration `process_wp` (`:287`, `.mli:17`); parse syntax
`ecParser.mly:3134-3135`.

### 5.2 `sp`

**Primitive** — the `FbdHoareS` arm of `t_sp_side` (`ecPhlSp.ml:259-267`, `` `Sp ``,
1 premise; `t_sp : (codegap1 doption) option -> backward`, `:301`, `.mli:8`). The dual of
`wp` — push the precondition forward through a prefix:

```
  ⊢ phoare[ s₁'; s₂ : sp(s₁, P) ==> Q ] ⋈ b
  ─────────────────────────────────────────
      ⊢ phoare[ s₁; s₂ : P ==> Q ] ⋈ b
                        [ s₁ must not write any variable the bound b reads ]
```

`s₁'` is the part of `s₁` that `sp` could not consume. The extra side condition is
`check_form_indep` (`:262`, definition `:236-240`): "the bound should not be modified by the
statement targeted by `sp`" — it has no counterpart in the Hoare rule, and exists precisely
because the bound is a formula over the same memory. Elaboration `process_sp` (`:306`,
`.mli:9`); parse syntax `ecParser.mly:3137-3138`.

### 5.3 `inline`

**Primitive** — `t_inline_bdhoare_r` (`ecPhlInline.ml:187`, `` `Inline ``, 1 premise;
`t_inline_bdhoare : use_tuple:bool -> s_pat -> backward`, `:215`, `.mli:16`):

```
  ⊢ phoare[ inline(c) : P ==> Q ] ⋈ b
  ───────────────────────────────────
   ⊢ phoare[ c : P ==> Q ] ⋈ b
```

Elaboration `process_inline` (`:499`, `.mli:21`; bdHoare arms `:374-381`, `:400-402`,
`:423-425`).

### 5.4 `kill`, `alias`, `set`, `set match`, `cfold`, `simplify if`, and the loop transforms

**Primitive**, all through the **same** rule — the `FbdHoareS` arm of
`EcLowPhlGoal.t_code_transform` (`ecLowPhlGoal.ml:816-821`), which rebuilds
`f_bdHoareS … bhs.bhs_cmp (bhs_bd bhs)` (`:820`) and emits
`FApi.xmutate1 tc (tr None) (cs @ [concl])` (`:821`). The tag and any extra premises `cs`
come from the caller:

| tactic | entry point | file:line | tag (`tr`) |
|---|---|---|---|
| `kill` | `t_kill_r` | `ecPhlCodeTx.ml:22`, `:80-81`, `.mli:11` | `` `Kill (side, cpos, olen) `` |
| `alias` | `t_alias_r` | `:109`, `:111-112`, `.mli:12` | `` `Alias (side, cpos) `` |
| `set` | `t_set_r` | `:137`, `:138-139`, `.mli:13` | `` `Set (side, cpos) `` |
| `set match` | `t_set_match_r` | `:182`, `:183-184`, `.mli:14` | `` `SetMatch (side, cpos) `` |
| `cfold` | `t_cfold` | `:418`, `:425-427`, `.mli:15` | `` `Fold (side, cpos, olen) `` |
| `simplify if` | `t_transform_if_r` | `:642`, `:644-645` | `` `TransformIf (side, cpos) `` |
| `fission` | `t_fission_r` | `ecPhlLoopTx.ml:115`, `:116-118`, `.mli:8` | `` `LoopFission (side, cpos, infos) `` |
| `fusion` | `t_fusion_r` | `:170`, `:171-173`, `.mli:9` | `` `LoopFusion (side, cpos, infos) `` |
| `unroll` | `t_unroll_r` | `:183`, `:184-185`, `.mli:10` | `` `LoopUnraoll (side, cpos) `` *(sic, §7.1)* |
| `splitwhile` | `t_splitwhile_r` | `:200`, `:201-202`, `.mli:11` | `` `SplitWhile (b, side, cpos) `` |

Only `kill` adds a premise, and it is a pHL one. **`kill` creates a losslessness goal:**

```
  ⊢ phoare[ ks : true ==> true ] = 1%r      ⊢ phoare[ c∖ks : P ==> Q ] ⋈ b
  ────────────────────────────────────────────────────────────────────────
              ⊢ phoare[ c : P ==> Q ] ⋈ b
```

built at `ecPhlCodeTx.ml:76` — **for every logic**, not only pHL. So `kill` on a `hoare` or
`equiv` goal still hands you a `phoare[ … : true ==> true ] = 1%r` obligation, normally
discharged by `islossless` (§4.5). `kill` also checks that the removed block writes nothing
the postcondition or an enclosing block reads (`:44-74`).

### 5.5 `swap` / `interleave`

**Primitive** — `t_swap_r : oside -> swap_kind -> backward` (`ecPhlSwap.ml:100`, `` `Swap ``,
1 premise, `.mli:14`). It does not use `t_code_transform`, but is logic-generic in the same
way, via `tc1_get_stmt` and `hl_set_stmt` (`:102-104`). Elaboration `process_swap` (`:145`)
and `process_interleave` (`:149`).

### 5.6 `weakmem`, `proc case`, `proc rewrite` / `proc change`, `change stmt`

**Primitive**, four rules that accept pHL through an explicit `kinds` list plus
`hl_set_stmt` rather than `t_code_transform`:

| tactic | entry point | file:line | tag |
|---|---|---|---|
| `weakmem` | `process_weakmem`, `FbdHoareS` arm | `ecPhlCodeTx.ml:465`, `:498-500`, emission `:518`, `.mli:26` | `` `WeakenMem `` |
| `proc case` | `process_case` | `:521`, kinds `:559`, emission `:569`, `.mli:23` | `` `ProcCase `` |
| `proc rewrite` / `proc change` | `t_change` | `ecPhlRewrite.ml:14`, kinds `:40`, emission `:52`, `.mli:6-10` | `` `ProcChange `` |
| `change stmt` | `t_change_stmt` | `:243`, emission `:352`, `.mli:11` | `` `ProcChangeStmt `` |

`proc case` and `proc change` emit their extra premises `goals` ahead of the rewrapped
judgement, so their rule is the §5 schema with those premises prepended.
`process_change_stmt` (`ecPhlRewrite.ml:355`) rejects `FbdHoareF` (`:369`) and rejects a side
argument on a `FbdHoareS` goal (`:372`); the accepting arm is `None, FbdHoareS` (`:376`).

---

## 6. Not applicable to pHL

Listed so the catalogue is provably complete. None of these has a bdHoare arm:

| tactic / file | why | evidence |
|---|---|---|
| `upto` — `ecPhlUpto.ml` | works on `Pr[_] = Pr[_]` / equiv | `t_uptobad_r` `:221` destructs `Pr` `:224`; tag `` `HlUpto `` `:250` |
| `eqobs-in` (`sim`) — `ecPhlEqobs.ml` | equiv only | `tc1_as_equivS` `:399`, `:471`, `:519`; `tc1_as_equivF` `:424`, `:544`, `:583` |
| `trans` / `repl` — `ecPhlTrans.ml` | equiv only | `tc1_as_equivS` `:45`, `:81`, `:170`; tag `` `Trans `` `:55`, `:71` |
| `sym` — `ecPhlSym.ml` | equiv only | `tc1_as_equivF` `:10`, `tc1_as_equivS` `:19` |
| `rwequiv` — `ecPhlRwEquiv.ml` | equiv only | `tc1_as_equivS` `:48`, `:137` |
| `outline` — `ecPhlOutline.ml` | equiv only | `tc1_as_equivS` `:30` |
| `eager` — `ecPhlEager.ml` | eager / equiv only | tags `` `EagerSeq `` … `` `EagerCall `` |
| `rwprgm` — `ecPhlRwPrgm.ml` | hoare only | `tc1_as_hoareS`; tag `` `IdAssign `` |
| `circuit` (`bdep`) — `ecPhlBDep.ml` | operates on circuits/bit-dependencies, not program logics | no `bdHoare` occurrence; dispatched from `ecHiTacticals.ml:257-258` |
| `hoare split` — `ecPhlHoare.ml` | **unsound for pHL by design** | `tc1_as_hoareS` `:10`; a conjunctive postcondition does not decompose into independent obligations here. The pHL counterpart is §3.4, which pays for the split with inclusion–exclusion |
| `concave` — `ecPhlConseq.ml:820` | ehoare only | `process_concave`, `.mli:57` |
| `call concave` — `ecPhlCall.ml:726` | ehoare only | errors at `:734`, `:743`, `:752`, `:799` |
| `t_hoare_true` / `t_ehoare_zero` — `ecPhlTAuto.ml:10`, `:28` | no pHL arm | see §1.16; `prbounded` (§4.3) plays this role |
| `rnd f g` (`PTwoRndParams`) | equiv only | `ecParsetree.ml:637`, used at `ecPhlRnd.ml:695`; a pHL goal falls through to `tc_error "invalid arguments"` (`:291`) |

---

## 7. Footnotes: inconsistencies observed

Recorded so that a reader comparing this document against the source does not mistake them
for errors here. **No code is changed by this document.**

1. **`ecPhlLoopTx.ml:184`** — the `unroll` tag is spelled `` `LoopUnraoll `` (transposed
   letters). Harmless today, since no code destructs the tag.
2. **`ecPhlRCond.ml:312`** — `t_bdhoare_rcond_match` is registered through
   `FApi.t_low2 "hoare-rcond-match"`, the label copied from the hoare variant; the debug
   trace therefore mislabels the pHL rule.
3. **`ecPhlBdHoare.ml:65`, `:155`** — `t_bdhoare_split_bop` and `t_bdhoare_split_not` verify
   the bound identity with a bare `assert (f_equal nb.inv bd.inv)` rather than `tc_error`.
   The `_conseq` wrappers (`:75`, `:164`) normally establish it first, so the assertion is
   unreachable from the surface tactic — but the two rules are callable directly within the
   module.
4. **`ecPhlCall.ml:346-349`** — with `⋈ = ≤` and no explicit bound, `t_bdhoare_call`'s
   residual goal is a **hoare** judgement, not a pHL one (§1.9). The rule silently changes
   logic; worth remembering when chaining tactics after a `call`.
5. **`ecPhlWhile.ml:92-94`** — `check_single_stmt`, used by the `while … k eps` rule (`:230`),
   errors with "only single loop statements are accepted" when what it actually requires is
   that the statement contain *nothing but* the loop (it tests `s_node` for emptiness).
6. **`ecPhlHiBdHoare.ml:36-38`, `:43-44`, `:75-76`** — `phoare split` cannot be applied to a
   procedure (`bdHoareF`) goal, even though every rule underneath it is S/F-generic
   (`gen_F`, `t_bdhoareF_and` / `_or` / `_not`, `ecPhlBdHoare.ml:98-176`) and
   `process_bdhoare_split` explicitly matches `FbdHoareF` to read the pre/post
   (`ecPhlHiBdHoare.ml:21-22`). The elaboration types its bound arguments with
   `EcProofTyping.tc1_process_Xhl_form` (`ecProofTyping.ml:201`), which calls
   `EcFol.destr_programS` (`:203`); that destructor handles only the **statement**
   judgements (`ecCoreFol.ml:761-771`), so an `FbdHoareF` goal raises
   `DestrError "programS"` — surfaced to the user as an *anomaly*, not a tactic error.
   Reproduced on this tree:

   ```
   lemma L : phoare [ M.f : true ==> res.`1 /\ res.`2 ] = (1%r/4%r).
   proof.
     phoare split (1%r/2%r) (1%r/2%r) (3%r/4%r).
   (* [critical] anomaly: EcLib.EcCoreFol.DestrError("programS") *)
   ```

   Applying `proc` first works. The `F` code paths in `EcPhlBdHoare` are therefore currently
   unreachable.
7. **`ecPhlHiBdHoare.ml:76`** — the `1%r` default for `b₁` in `phoare split ! b₁ b₂` is dead
   code: `BDH_split_not`'s first component is `pformula option`
   (`ecParsetree.ml:691`), but the only production that builds it always supplies
   `Some b1` (`ecParser.mly:3422`). Both bounds are mandatory at the surface.

---

## Appendix: how the rules in this file were checked

Every claim was re-verified against the current tree, not carried over from an earlier
revision. The procedure:

1. **Symbol resolution.** Every function, type and `val` cited was located by name with
   `grep`, and the line number in this document set from that result — rather than trusting
   a previous number. This caught shifts in `ecPhlSeq.ml`, `ecPhlFun.ml`, `ecPhlDeno.ml`,
   `ecPhlFel.ml`, `ecPhlCodeTx.ml`, `ecPhlRewrite.ml`, `ecLowPhlGoal.ml`, `ecCoreFol.ml`,
   `ecHiTacticals.ml`, and wholesale renumbering in `ecParser.mly` and `ecParsetree.ml`.
2. **Inner references.** Each cited line that is *not* a definition (a side condition, a
   match arm, an emission site) was checked by reading that line and matching it against
   what the text claims.
3. **Primitive vs derived.** Every rule called primitive was confirmed to contain
   `xmutate1` / `xmutate1_hyps` with the stated tag; every rule called derived was confirmed
   to contain no `xmutate` in its body.
4. **Premise counts.** For each primitive, the length of the emitted formula list was
   compared with the number of premises written above the bar.
5. **Signatures.** Every quoted type was copied from the current `.mli`. This caught
   `process_call` / `process_call_concave` becoming tuple-taking, and
   `t_hoareS_conseq_bdhoare` becoming exported.
6. **Execution.** Twenty-two tactic invocations were run and their goals compared
   premise-by-premise with the statements above:

   | rule | § | outcome |
   |---|---|---|
   | `skip`, bound `1%r` | 1.1 | 1 goal — as stated |
   | `skip`, bound `≥ 1/2` and `≤ 1/2` | 1.1 | 2 goals; **corrected** the doc: `≤` is accepted, and the extra premise is the `conseq_bd` one, not `b = 1%r` |
   | `seq i : R` | 1.2 | 5 goals — pruning of `condg2` and auto-discharge of `condnm` confirmed |
   | `seq i : R f₁ f₂ g₁ g₂` with variable `f₂` | 1.2 | 6 goals — `condnm` present, as predicted |
   | `if` | 1.3 | 2 goals, `P ∧ e` / `P ∧ ¬e`, same bound |
   | `match` | 1.4 | one goal per constructor, pattern vars in the memory |
   | `rcondt i` | 1.5 | hoare guard premise + pHL residual; **corrected** the surface name |
   | `rnd φ d₁ d₂ d₃ d₄` | 1.6e | 6 goals in the stated order |
   | `while (inv) (vrnt)` | 1.8a | 2 goals; **corrected** two implication orders |
   | `while (inv)` | 1.8b | 2 goals, abstract-statement hypothesis confirmed |
   | `while (inv) (vrnt) k eps` | 1.8c | 6 goals; **corrected** the syntax (no colon) and the empty-remainder requirement |
   | `call` | 1.9 | residual `= 1%r` for the `=`/no-bound row |
   | `elim*` / `exists*` | 1.13 | `∀x⃗.` introduced / `∃x⃗. x = f ∧ P` introduced |
   | `ecall` | 1.14 | 1 goal — the prefix `wp`; **corrected** the doc, which said pHL was unsupported |
   | `case` | 1.15 | 2 goals, exclusive preconditions, same bound |
   | `conseq (: P' ==> Q')` | 2.6a | 2 goals — confirmed the *not-modified* default |
   | `conseq (: _ ==> _ : ≤ b')` | 2.6a | 2 goals, `bd_goal` as tabulated |
   | `hoare`, bound `= 0%r` and `≤ 1/2` | 3.2 | 1 and 2 goals respectively |
   | `phoare split b₁ b₂ b₃` | 3.4 | 4 goals, dual connective confirmed |
   | `phoare split ! b₁ b₂` | 3.5 | 3 goals, `⋈ᵒᵖ` on the second |
   | `wp` | 5.1 | consumed an assignment; **no-op on a sampling**, confirming the restriction |
   | `sp` | 5.2 | consumed an assignment forward |

   Transcripts for §3.4, §3.5 and §1.6e are quoted inline in those sections. Four of these
   runs contradicted the previous revision of this document; the corrections are marked above
   and folded into the rules themselves.
7. **Tree state.** `dune build` clean; the only modified file is this one.

Two structural facts about the tree were also confirmed, since the document's earlier
revision assumed otherwise: `src/phl/` now contains no other documentation, and the
recheckable-proof-node scaffolding (`ecPhlRecheck`, `rules/`, `VRule` / `xrule` /
`register_rule_checker` / `recheck_proofenv`, the `EC_RECHECK` hook) is not present. The
primitive/derived distinction used here is therefore stated purely in terms of `xmutate1`.
