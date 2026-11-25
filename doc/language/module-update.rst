:orphan:

.. remove the :orphan: marker above once this page is referenced from a
   language-reference toctree.

========================================================================
Fine-grained module definitions: `module ... = ... with`
========================================================================

A module can be defined *incrementally*, as a patch over an existing
module: the new module copies the base module and applies a set of
declarative updates — adding or removing global variables, and editing
procedure bodies at designated code positions.

.. code-block:: easycrypt

  module M' = M with {
    var c : int                          (* add a module variable      *)
    proc f [ ^x<- + { c <- c + 1; } ]    (* patch the body of a proc   *)
  }.

This is the natural way to define instrumented variants of a scheme
(ghost counters, bad-event flags) and hybrid games that differ from the
previous game by a small, local change: the definition *is* the diff,
the unchanged code cannot drift out of sync with the base module, and
relational proofs between the base and the derived module close cheaply
(`sim`) on all unmodified procedures.

For a complete worked example of a game-hop proof structured this way,
see `examples/br93.ec` in the EasyCrypt distribution, where each hybrid
is defined as an update of the previous one.

.. contents::
   :local:

------------------------------------------------------------------------
Syntax
------------------------------------------------------------------------

.. admonition:: Syntax

  .. code-block:: easycrypt

    module M' = M with {
      - var x1, ..., xn                          (* remove variables    *)
      var y1 : ty1 ...                           (* add variables       *)
      proc f [ {var-decl}* {update}+ ] res ~ e   (* patch procedures    *)
      ...
    }.

  The three groups must appear in this order: variable removals (at most
  one `- var` clause), variable additions, procedure updates.  Each
  procedure update consists of optional *local* variable declarations,
  followed by one or more body updates, followed by an optional rewrite
  `res ~ e` of the returned expression.

Each body update is a *code position* (or a range of positions)
followed by an update action.  The actions come in two families.

**Statement updates** insert, replace or delete instructions:

- `{codepos} + { s }` — insert the statement `s` **after** the
  instruction at `{codepos}`;
- `{codepos} + ^ { s }` — insert `s` **before** it;
- `{codepos} ~ { s }` — **replace** it by `s`;
- `{codepos} -` — **delete** it.

Replacement and deletion also accept a range `[{codepos} ..
{codepos}]` (inclusive) or `[{codepos} +> n]` (the instruction at
`{codepos}` and the `n` following ones), acting on the whole selected
block.

**Condition updates** edit the control structure around the designated
instruction:

- `{codepos} + e` — keep the instruction at `{codepos}` and wrap the
  **rest of the block after it** in `if e { ... }`;
- `{codepos} + ^ e` — wrap the instruction itself **and** the rest of
  the block in `if e { ... }`;
- `{codepos} ~ e` — replace the guard of the `if`, the `while`, or the
  scrutinee of the `match` at `{codepos}` by `e` (the branches are kept
  unchanged);
- `{codepos} - {branch}` — collapse the conditional at `{codepos}` to
  one of its branches: `.` selects the true branch of an `if`, `?` its
  false branch, and `#C.` the branch of a `match` for constructor `C`
  (the constructor's pattern variables become fresh local variables,
  bound by projecting the scrutinee).

------------------------------------------------------------------------
Code positions
------------------------------------------------------------------------

Code positions use the same language as program tactics such as `swap`
or `wp` — plain indices, anchors (`^x<-`, `^<@{2}`, `^while`), offsets,
and nested positions descending into branches (`^while.^s<-`,
`^match#Some.^if.1`).  See :doc:`code-positions` for the full syntax,
including the whitespace pitfalls around `.`.

When a procedure update contains several body updates, they are applied
from the last to the first.  List them **in program order** (positions
increasing down the body): every position is then interpreted relative
to the original procedure body.

------------------------------------------------------------------------
Semantics
------------------------------------------------------------------------

The derived module elaborates to an ordinary structure: procedures and
variables that are not mentioned are copied over verbatim, so they are
definitionally identical to the base module's and relational goals
between the two close by `sim` or `proc; auto`.

Two points deserve attention:

- **The derived module owns fresh copies of the base's items — and only
  of those.**  What is copied is exactly the base module expression's
  own items: its variables, its procedures, its nested sub-modules.
  References to those items are re-rooted to the new module: if `M` has
  a variable `x`, then `M'.x` is a *distinct* global, and a relational
  invariant linking the two games is written `M.x{1} = M'.x{2}` (or
  `={x}(M, M')`).  Everything else stays **shared**: references to
  other modules (a joint random oracle), and — when the base is a
  sub-module — references to the *enclosing* module's state (see
  `Updating sub-modules and functors`_ below).

- **Updates are checked in the derived module's scope.**  Inserted code
  may mention the procedure's parameters and locals, the new local
  variables declared in the update, the (new and copied) module
  variables and procedures — unqualified — and any other module's
  global variables.  When the base is a sub-module, the enclosing
  module's variables must be written *qualified* (`P.g`), as they are
  not part of the derived module's own scope.  A `res ~ e` rewrite must
  preserve the return type.

------------------------------------------------------------------------
Restrictions
------------------------------------------------------------------------

- The base expression must be a **concrete, fully applied** module.  A
  functor cannot be updated directly; instead, re-bind its parameters
  in the header of the new module:

  .. code-block:: easycrypt

    module F2 (B : T) = F(B) with { ... }.

- Abstract (declared) modules cannot be updated.

- Only procedures of the base module's signature can be patched; new
  procedures cannot be added, and procedure signatures cannot change.
  A procedure defined by alias (`proc f = M.g`) is resolved to its
  concrete body before patching.

- Variable removal (`- var`) happens **before** the procedure updates
  are processed: the updates cannot mention the removed variables — not
  even in anchors, so use numeric positions to delete their uses — and
  it is the user's responsibility to patch out every use (a dangling
  reference is reported when the derived module is checked).

------------------------------------------------------------------------
Updating sub-modules and functors
------------------------------------------------------------------------

The base of an update may also be a **sub-module** (`P.O`), an
**applied functor** (`F(A)`), or a sub-module of an applied functor
(`F(A).O`).  The copy/share rule of the previous section decides the
semantics in every case:

- **Sub-module base.**  `module Q = P.O with { ... }` copies `O`'s
  items — `Q` gets fresh copies of `O`'s variables and nested
  sub-modules, and `O`'s internal (self-) references follow the copy.
  References to the *enclosing* module's state (`P.g`) are **shared**:
  `Q` reads and writes the same `P.g` as `P.O` does.  This is the
  natural shape for instrumenting one oracle of a larger construction
  in place.

- **Applied-functor base.**  `module Q = F(A) with { ... }` bakes the
  application into the copy: parameter references are already resolved
  to `A`, self-references (including calls between the functor's own
  procedures) land on `Q`, and `Q`'s state is fresh.  Note the
  difference with an *alias* `module G = F(A)`: the alias shares `F`'s
  state (in EasyCrypt, a functor's state is common to all its
  applications), whereas the update produces an independent copy.

- **Sub-module of an applied functor.**  `module Q = F(A).O with
  { ... }` combines the two: `O`'s state is copied, the enclosing
  functor's state `F.g` — which is application-independent — stays
  shared, and the application at `A` is baked in.

.. ecproof::

  require import AllCore.

  module type T = { proc run() : int }.

  module A0 : T = { proc run() : int = { return 7; } }.

  module F (B : T) = {
    var g : int                       (* enclosing state: SHARED    *)
    module O = {
      var x : int                     (* sub-module state: COPIED   *)
      proc f() : int = {
        var r;
        r <@ B.run();
        g <- g + r;
        x <- x + 1;
        return x;
      }
    }
  }.

  module Q = F(A0).O with {
    proc f [ 1 + ^ { x <- x + 2; } ]  (* x is Q's own copy;
                                         F.g would need qualification *)
  }.

  lemma Q_f : hoare[ Q.f : Q.x = 0 /\ F.g = 0 /\ F.O.x = 5
                       ==> Q.x = 3 /\ F.g = 7 /\ F.O.x = 5 ].
  proof.
  (*$*) proc.
  by inline *; auto.
  qed.

------------------------------------------------------------------------
Example: instrumenting a scheme with ghost state
------------------------------------------------------------------------

The derived module `Mc` adds a ghost counter `c`, initialised in
`init` and incremented on every call to `f`.  The base procedures are
otherwise unchanged: the equivalence between `M.f` and `Mc.f` — with
the two `x` copies related explicitly — closes by `auto`.

.. ecproof::

  require import AllCore.

  module M = {
    var x : int

    proc init() : unit = {
      x <- 0;
    }

    proc f(y : int) : int = {
      var a : int;
      a <- y + 1;
      x <- x + a;
      return a;
    }
  }.

  module Mc = M with {
    var c : int
    proc init [ ^x<- + { c <- 0; } ]        (* insert after the write  *)
    proc f    [ 1 + ^ { c <- c + 1; } ]     (* insert before instr 1   *)
  }.

  (* `+` inserted after the anchor: init runs  x <- 0; c <- 0. *)
  lemma Mc_init : hoare[ Mc.init : true ==> Mc.x = 0 /\ Mc.c = 0 ].
  proof.
  (*$*) proc.
  by auto.
  qed.

  (* Mc.x is a FRESH global, distinct from M.x: relate them explicitly. *)
  equiv M_Mc_f : M.f ~ Mc.f :
    ={arg} /\ M.x{1} = Mc.x{2} ==> ={res} /\ M.x{1} = Mc.x{2}.
  proof. by proc; auto. qed.

------------------------------------------------------------------------
Example: replacing an instruction and the result
------------------------------------------------------------------------

A statement replacement (`~ { ... }`) combined with a rewrite of the
returned expression (`res ~ ...`).

.. ecproof::

  require import AllCore.

  module M = {
    proc f(y : int) : int = {
      var a : int;
      a <- y + 1;
      return a;
    }
  }.

  module M2 = M with {
    proc f [ ^a<- ~ { a <- y + 2; } ] res ~ (a - 1)
  }.

  lemma M2_f (v : int) : hoare[ M2.f : y = v ==> res = v + 1 ].
  proof.
  (*$*) proc.
  by auto.
  qed.

------------------------------------------------------------------------
Example: editing a loop
------------------------------------------------------------------------

Nested code positions reach inside a loop body (`^while.^s<-`), and a
condition update (`~ e`) changes the guard while keeping the body.

.. ecproof::

  require import AllCore.

  module M = {
    proc g(n : int) : int = {
      var i, s : int;
      i <- 0;
      s <- 0;
      while (i < n) {
        s <- s + i;
        i <- i + 1;
      }
      return s;
    }
  }.

  (* double the summand, inside the loop body *)
  module Mbody = M with {
    proc g [ ^while.^s<- ~ { s <- s + 2 * i; } ]
  }.

  (* one more iteration, same body *)
  module Mguard = M with {
    proc g [ ^while ~ (i < n + 1) ]
  }.

  equiv M_Mbody_g : M.g ~ Mbody.g : ={arg} ==> res{2} = 2 * res{1}.
  proof.
  (*$*) proc.
  while (={i, n} /\ s{2} = 2 * s{1}); by auto => /#.
  qed.

------------------------------------------------------------------------
Example: collapsing a match to one branch
------------------------------------------------------------------------

`- #C.` specialises a `match` to its `C` branch; the pattern variables
are introduced as local variables bound by projecting the scrutinee.

.. ecproof::

  require import AllCore.

  module M = {
    proc h(o : int option) : int = {
      var r : int;
      r <- 0;
      match o with
      | None => { r <- 1; }
      | Some v => { r <- v; }
      end;
      return r;
    }
  }.

  module Msome = M with {
    proc h [ ^match - #Some.]
  }.

  lemma Msome_h (w : int) : hoare[ Msome.h : o = Some w ==> res = w ].
  proof.
  (*$*) proc.
  by auto.
  qed.

------------------------------------------------------------------------
Example: updating a functor
------------------------------------------------------------------------

Functors are updated by re-binding their parameters and patching the
applied body.

.. ecproof::

  require import AllCore.

  module type T = { proc run() : unit }.

  module F (B : T) = {
    var k : int
    proc go() : int = {
      k <- 0;
      B.run();
      return k;
    }
  }.

  module F2 (B : T) = F(B) with {
    proc go [ ^ <@ + { k <- k + 1; } ]
  }.

  lemma F2_go (B <: T{-F2}) : hoare[ F2(B).go : true ==> F2.k = 1 ].
  proof.
  (*$*) proc.
  by wp; call (: true); auto.
  qed.
