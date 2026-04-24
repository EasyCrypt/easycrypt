========================================================================
Notations
========================================================================

Notations are user-declared surface-syntax forms for formulas.  A
declaration binds a name prefixed by ``#`` to a template of literal
punctuation and slots; uses of the notation at the call site are parsed
against the template and expanded to an underlying body at type-checking
time.  Notations live in the same namespace as operators and
abbreviations: they follow ``import``/``export``/``clone`` rules, they
can be declared ``local`` inside a ``section``, and the pretty-printer
automatically renders expanded bodies back to template syntax whenever
possible.

------------------------------------------------------------------------
Anatomy of a declaration
------------------------------------------------------------------------

.. admonition:: Syntax

   | ``local``? ``notation`` ``#``\ *name*
   |   *tyvars*?
   |   *binder-slots*?
   |   *form-slots*\ *
   |   *template*
   |   (``:`` *codom*)?
   |   ``=`` *body* ``.``

   where a form slot is either ``(`` *name* ``:`` *ty* ``)`` or
   ``(`` *name* ``:`` *deps* ``==>`` *ty* ``)``, optionally extended
   with a default ``(`` *name* ``:`` *ty* ``=`` *default* ``)``; and
   a template item is a STRING punctuation, a slot name, or an
   optional group ``(`` *template-item*\ *  ``)?``.

Every piece except the name, template, and body is optional.  The
declaration mirrors an operator declaration with an extra *template*
section that describes the surface syntax.

Example::

  notation #pair (a : int) (b : int) " [" a ", " b "] " = (a, b).

  lemma L (x y : int) : #pair [x, y] = (x, y).
  proof. by trivial. qed.

------------------------------------------------------------------------
Template literals and punctuations
------------------------------------------------------------------------

A template is a sequence that alternates **STRING literals** and **slot
references**.  The first element of the template must be a STRING.

Each STRING must lex to exactly one of six punctuation tokens:

  ``[``   ``]``   ``:``   ``|``   ``,``   ``;``

Additional whitespace *inside* the string is ignored by the input
matcher but preserved verbatim by the pretty-printer.  For example,
``" [ "`` and ``"["`` both match a single ``[`` at the call site, but
the former pretty-prints with spaces on both sides.

A STRING that lexes to zero tokens, two or more tokens, or an
unsupported symbol is rejected at declaration time::

  notation #bad " @" a " @ " = a.
  (* rejected: notation punctuation `" @"' must lex to one of: [ ] : | , ; *)

------------------------------------------------------------------------
Slots
------------------------------------------------------------------------

A slot is a bare lowercase identifier inside the template.  Each slot
must be declared earlier in the notation as either a **form slot** or a
**binder slot**.

Form slots
   Declared with ``( name : ty )`` in the usual function-argument style.
   At the call site the slot consumes a formula; at typing time the
   formula is checked against ``ty``.

Binder slots
   Declared inside ``#< ... >`` before the form-slot block, for example
   ``#< i : int >`` or ``#< i : int, j : int >``.  A binder slot reads
   an *identifier* at the call site.  The chosen identifier becomes a
   locally-bound name visible to any form slot that depends on it.
   Writing ``_`` as the binder name at the call site introduces a
   fresh anonymous binder — useful when no dependent form slot
   actually uses it::

     lemma L (xs : int list) : #mapI [_ : 3 : 42] = [42; 42; 42].

Per-slot binder dependencies
   A form slot can declare that it depends on binder slots via
   ``==>``::

     notation #mapI #< i : int > (n : int) (f : i ==> int)
       " [" i " : " n " : " f "] " =
       map f (iota_ 0 n).

   At typing, ``f`` has type ``int -> int`` (curried over the binders
   it declares).  At the call site the user writes the body of the
   lambda in terms of the chosen binder name, and the expansion wraps
   it automatically::

     lemma M : #mapI [k : 4 : k + 1] = map (fun k => k + 1) (iota_ 0 4).
     proof. by trivial. qed.

**Template order is free.** A form slot may reference a binder that
appears anywhere in the template, including *after* the form slot.  At
expansion time binder slots are bound in a first pass and form slots in
a second, so a comprehension-style template like ``"[" f " | " x " : "
s "]"`` works even though ``f`` (which depends on ``x``) is printed
before ``x``.

**Slot kind is inferred from the declaration, not the template.** A
template reference like ``i`` means "ident slot" iff ``i`` is in the
``#< ... >`` group; otherwise it means "form slot".

------------------------------------------------------------------------
Type parameters
------------------------------------------------------------------------

Notations may be polymorphic.  Type parameters are declared in the same
``['a 'b]`` syntax used by operators, appearing before the slot lists::

  notation #ppair ['a 'b] (a : 'a) (b : 'b) " [" a ", " b "] " = (a, b).

  lemma L (x : int) (y : bool) : #ppair [x, y] = (x, y).
  proof. by trivial. qed.

Type parameters are freshened at every call site, so independent uses
do not leak type equalities.

------------------------------------------------------------------------
Optional template groups
------------------------------------------------------------------------

A sub-sequence of template items can be wrapped in ``( ... )?`` to
mark it optional.  The group must start with a punctuation literal
(its trigger) and can contain further form slots.  Any form slot that
appears only inside an optional group must declare a default via
``(x : ty = default)`` at the slot declaration::

  notation #big ['a] #< i : 'a >
      (r : 'a list)
      (P : i ==> bool = predT)
      (F : i ==> t)
    "[" i " : " r ("| " P)? "] " F =
    big P F r.

At a call site the dispatcher peeks one token at the group's trigger
position: present → parse the group, absent → the slots inside get
their declared defaults::

  #big [ i : xs | 0 <= i ] (F i)   (* P = fun i => 0 <= i *)
  #big [ i : xs ]          (F i)   (* P = predT           *)

Groups are mutually independent — each is triggered by its own
punctuation character and can appear or not regardless of sibling
groups.

Constraints at declaration time:

- the group must be non-empty and start with a punctuation literal;
- only form slots may be inside a group (ident/binder slots must
  always be present);
- a ``(x : ty = default)`` default may be attached only to a slot
  that appears solely inside optional groups; if the same slot also
  appears at a mandatory position, no default is needed (or
  allowed);
- every form slot that appears only inside optional groups must
  declare a default.

------------------------------------------------------------------------
Qualified and projected uses
------------------------------------------------------------------------

Notations participate in qualified operator lookup, so ``Mod.#foo``
is accepted wherever the module path makes the notation visible::

  clone Bigop as BRA with type t <- real, ...
  ...
  lemma L s : BRA.#big [ x : s ] (f x) = 0%r.

Projection after a notation call works at the simple-formula level::

  notation #pair ['a 'b] (a : 'a) (b : 'b) " [" a ", " b "] " = (a, b).

  lemma L (x y : int) : #pair [x, y].`1 = x.

------------------------------------------------------------------------
Slot holes and pattern uses
------------------------------------------------------------------------

Inside contexts that accept ``_`` patterns (``pose X := ...``,
``rewrite [PATTERN](...)`` and similar), slot arguments may be ``_``:

- A bare ``_`` as the *entire* slot body creates a meta-variable of
  the slot's full curried type — so ``#big [ i : _ | _ ] _`` matches
  any ``big P F s`` in the same way ``big _ _ _`` does.
- A ``_`` inside a compound slot body (e.g. ``f _ i``) stands for a
  sub-term meta-variable.

Typical use::

  (* positional pattern, equivalent to `pose c := big _ _ _' *)
  pose c := #big [ i : _ | _ ] _.

  (* targeted rewrite *)
  rewrite [#bigi [ i : _, (max _ _) | _ ] _] big_range0r.

Outside pattern-accepting contexts ``_`` is rejected at typing time
as usual.

------------------------------------------------------------------------
Semantics
------------------------------------------------------------------------

A notation is compiled to a regular operator of kind ``OB_nott`` that
records the template alongside the typed body.  At a call site
``#name [ ... ]``:

1. The parser looks up the template for ``#name`` and consumes tokens
   according to its items, collecting the slot arguments.  Form-slot
   contents are parsed as **formulas**, so they may contain memory
   references, ``Pr[...]`` expressions, and any other formula-level
   construct — not just expressions.
2. The resulting ``PFntt`` node is type-checked.  For each form slot
   with binder dependencies, the argument is type-checked in an
   environment extended with the user-chosen binder idents, then
   wrapped in ``fun`` over those idents.  Eta-reduction is applied
   when the slot body is ``f b_1 ... b_n`` with trailing args exactly
   matching the binders, so ``F i`` stores as ``F`` (and ``(P \o h) i``
   as ``P \o h``) while ``mem s i`` keeps its lambda wrap.  For each
   ident slot, a fresh local is created with the user-chosen name.
   The body is then obtained by substituting all slot idents with
   their resolved values and alpha-renaming each bound binder to the
   user-chosen name.

Because expansion happens at typing, slot-level errors attribute to the
user's source and not to the declaration's body.

Form slots outside a closing fence parse at **simple-formula** level so
that outer binary operators are not absorbed.  Consequently an
application like ``F i`` at a trailing slot position must be
parenthesised::

  #big [ i : s ] (F i) = 0%r     (* correct *)
  #big [ i : s ] F i = 0%r       (* rejected *)

Form slots that are fenced by a following punctuation token parse at
full formula level.

------------------------------------------------------------------------
Locality
------------------------------------------------------------------------

A declaration may be prefixed with ``local`` inside a ``section``; the
notation is then discharged when the section closes::

  section.
    local notation #tmp (a : int) " [" a "] " = a + 1.
    lemma inside : #tmp [3] = 4.
    proof. by trivial. qed.
  end section.
  (* #tmp is no longer visible here. *)

Outside a section, ``local notation`` is rejected, as for other
operators.

------------------------------------------------------------------------
Pretty-printing
------------------------------------------------------------------------

The pretty-printer reverse-matches the body of each registered notation
against each formula it prints.  When a formula matches the body of a
notation, the printer renders it using the template, honouring
whitespace from the declaration's STRING literals::

  notation #pair (a : int) (b : int) " [" a ", " b "] " = (a, b).

  lemma L (x y : int) : #pair [x, y] = (x, y).

  print L.
  (* lemma L: forall (x y : int), #pair [x, y]  = #pair [x, y] . *)

For notations with binder slots, the printer unwraps the matched
lambdas to recover the user's chosen binder names.

------------------------------------------------------------------------
Examples
------------------------------------------------------------------------

A polymorphic pair::

  notation #pair ['a 'b] (a : 'a) (b : 'b) " [" a ", " b "] " = (a, b).

  lemma L (x : int) (y : bool) : #pair [x, y] = (x, y).
  proof. by trivial. qed.

A polymorphic map notation with an explicit lambda::

  notation #pmap ['a 'b] (f : 'a -> 'b) (xs : 'a list)
    " [" f " : " xs "] " =
    map f xs.

  lemma L : #pmap [(fun x => x + 1) : [1; 2; 3]] = [2; 3; 4].
  proof. by trivial. qed.

A binder-slot map notation where the user-chosen name scopes into the
body form::

  notation #mapI #< i : int > (n : int) (f : i ==> int)
    " [" i " : " n " : " f "] " =
    map f (iota_ 0 n).

  lemma L : #mapI [k : 4 : k + 1] = map (fun k => k + 1) (iota_ 0 4).
  proof. by trivial. qed.

A notation with an optional predicate group (default ``predT``)::

  notation #filter ['a] #< i : 'a >
      (xs : 'a list)
      (P : i ==> bool = predT)
    "[" i " : " xs ("| " P)? "]" =
    filter P xs.

  lemma with_P (xs : int list) :
    #filter [ i : xs | 0 <= i ] = filter (fun i => 0 <= i) xs.
  proof. by trivial. qed.

  lemma without_P (xs : int list) :
    #filter [ i : xs ] = filter predT xs.
  proof. by trivial. qed.

A notation inside a section::

  section.

    notation #gpair (a : int) (b : int) " [" a ", " b "] " = (a, b).
    local notation #lpair (a : int) (b : int) " [" a ", " b "] " = (a, b).

    lemma t_g : #gpair [1, 2] = (1, 2).
    proof. by trivial. qed.

    lemma t_l : #lpair [1, 2] = (1, 2).
    proof. by trivial. qed.

  end section.

  lemma after : #gpair [3, 4] = (3, 4).
  proof. by trivial. qed.

------------------------------------------------------------------------
Error catalogue
------------------------------------------------------------------------

The following errors may appear at notation-declaration or call time.

``notation punctuation `"x"' must lex to one of: [ ] : | , ;``
   A template STRING could not be lexed to exactly one of the six
   accepted punctuation tokens.

``template references unknown slot: `x'``
   The template refers to a slot name that is not declared as either a
   binder slot (``#< ... >``) or a form slot (``( ... )``).

``parse error: unknown notation `#name'``
   The call site used a notation name that is not in scope.  The
   notation may not be ``import``-ed, may be ``local`` and out of
   scope, or simply not declared.

``parse error: in notation `#name': expected `:'``
   The call site did not match the template at the indicated punct.
   Check that the call reproduces the declaration template verbatim.

``parse error: in notation `#name': expected identifier for binder slot `i'``
   A binder slot consumes an identifier at the call site; another
   token was supplied.  A bare ``_`` is accepted here and yields a
   fresh anonymous binder name.

``notation's optional group must be non-empty and start with a punctuation``
   A ``( ... )?`` group was declared without leading punctuation
   (e.g. a slot first) or was empty.

``slot `x' can only have a default if it appears solely inside an optional group``
   ``(x : ty = default)`` was used for a slot that also occurs at a
   mandatory template position, where it cannot be absent.

``slot `x' must declare a default because it only appears inside optional groups``
   A form slot that lives exclusively inside optional groups must
   have a default value, so that a well-defined value is bound when
   the group is omitted.

------------------------------------------------------------------------
Limitations
------------------------------------------------------------------------

- The punctuation palette is fixed to the six tokens listed above.
  Arbitrary keywords or operator symbols are not accepted because the
  lexer tokenizes ahead of the notation-aware parser.

- Templates cannot describe iteration (e.g. ``item*`` or
  ``item, ...``).  Optional groups (``( ... )?``) are supported but
  repetition is not.  Each declaration has a fixed maximum arity.

- Explicit type-instantiation on a notation call site
  (``#foo<:'a * 'b> [...]``) is not accepted.  Type arguments must be
  inferred from the slot contents; when inference is insufficient,
  annotate one of the slot arguments or the enclosing binding.

- Notation lookup is not overloading-aware: when two clones of the
  same underlying theory are imported (e.g. ``BBOr`` and ``BRA`` both
  providing ``#big``), the unqualified ``#big`` resolves to a single
  candidate by name only, unlike the raw operator ``big`` which is
  disambiguated by type.  Use a qualified form
  (``StdBigop.Bigbool.BBOr.#big``) to select the intended
  instantiation.

- Within a single theory file loaded via ``require``, a notation
  declared on line *N* is visible from line *N + 1* onward.  In
  interactive mode the visibility is immediate.

- A ``local notation`` must appear inside a ``section``, as for other
  ``local`` operators.
