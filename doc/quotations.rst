========================================================================
Quotations (external preprocessor)
========================================================================

A *quotation* lets you embed, directly in an EasyCrypt source file, a
fragment written in some other surface syntax, and have EasyCrypt expand it
into ordinary EasyCrypt code by delegating to an **external tool**. The tool
is a black box: EasyCrypt communicates with it over standard input and
standard output, so it can be written in any language.

.. warning::

   Quotations run external programs, so the feature is **disabled by
   default**. Enable it explicitly with the command-line flag
   ``-enable-quotations`` or the environment variable
   ``EC_ENABLE_QUOTATIONS=1``. It cannot be enabled from ``easycrypt.project``
   (that file ships inside a checked-out tree, so allowing it to turn the
   feature on would defeat the safeguard). While disabled, encountering a
   quotation is a hard error, never a silent skip or a silent execution. Only
   enable quotations for sources you trust.

When using Proof General, the following code can be put in one's
`.emacs` file to allow the enabling of quotations to be toggled on and off::

  (defun easycrypt-enable-quotations-toggle ()
    "Toggle enabling quotations in easycrypt mode"
    (interactive)
    (if (member "-enable-quotations" easycrypt-prog-args)
        (progn
          (setq easycrypt-prog-args
                (remove "-enable-quotations" easycrypt-prog-args))
          (message "quotations disabled"))
      (setq easycrypt-prog-args
            (append easycrypt-prog-args (list "-enable-quotations")))
      (message "quotations enabled")))

(Note that one has to exit EasyCrypt to have the toggling take effect.)

Quotations are processed during lexing, before parsing. When the
external tool - or EasyCrypt's handling of its output — produces an
error, the location reported by EasyCrypt is mapped back to the
**original** quoted text, not to the generated code.

There are two kinds of quotations, **fragmented** and
**whole**.

------------------------------------------------------------------------
Kinds of quotations
------------------------------------------------------------------------

Fragmented Quotations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A fragmented quotation expands to a **sentence fragment**: its tokens
are spliced into the surrounding sentence, so a quotation may stand
for only *part* of a sentence and several quotations may appear in one
sentence. The sentence terminator (``.``) is always written by the
user - outside of a quotation - and never produced by a quotation.

A fragmented quotation is delimited by ``{%`` and ``%}``:

.. admonition:: Syntax

  ``{% {name} {body} %}``

Here:

- ``{name}`` is a lowercase identifier selecting which external *handler*
  expands the quotation (see `Configuring handlers`_).

- ``{body}`` is arbitrary text. It runs from the character following
  ``{name}`` up to the matching ``%}``. The delimiters nest: a ``{% ... %}``
  pair occurring inside the body is kept verbatim and does not close the
  outer quotation, so a body may itself contain quotation delimiters.

A quotation expands to a sentence *fragment*, so the ``.`` that ends the
sentence is written outside the quotation. For example, a ``calc`` handler
that returns the value of an arithmetic expression::

    op forty_two = {% calc 6 * 7 %}.

expands to ``op forty_two = 42.``. Because the expansion is only a fragment,
quotations compose with ordinary source and with each other within one
sentence::

    op mixed = {% calc 6 * 7 %} + ({% calc 2 + 3 %} * 10).

It is an error for a quotation's expansion to contain a sentence terminator
(``.``): the fragment must not close the sentence itself.

Whole Quotations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An whole quotation is terminated within the quotation by the
sentence terminator (``.``), of which there must be only one occurrence.
And it exands to a nonempty **sequence** of sentences.

A whole quotation has the form:

.. admonition:: Syntax

  ``{%! {name} {body} . !%} .``

Here ``{name}`` and ``{body}`` are as with fragmented quotations,
and ``{body}`` may not have any occurrences of the sentence terminator
(``.``).

A whole quotation consists of two EasyCrypt sentences.  The expansion
of ``{body}`` happens during the processing of the first
sentence, after which the resulting sentences are processed by
EasyCrypt. The second sentence, ``!%}.``, is just an abbreviation
for the `noop` pragma. In the case where the sentences in the expansion
are proof tactics, ``!%}.`` causes Proof General to display the
next open goal. (Undoing this noop takes one to a useless proof state;
instead undo both it and the first sentence.)

Note: although whole quotations can be used for purposes other than
parameterizing sequences of proof tactics, Proof General doesn't
display all the effects, say of the definition of multiple operators,
and so this isn't very easy to work with.

------------------------------------------------------------------------
Debugging quotations
------------------------------------------------------------------------

The user can view the expansions of quotations by beginning them with
``{%*`` (in the case of fragmented quotations) or ``{%!*`` (in the
case of whole quotations). In Proof General, the expansions of
quotations are printed in the ``*response*`` buffer.

------------------------------------------------------------------------
Configuring handlers
------------------------------------------------------------------------

A quotation ``name`` is resolved to a shell command in this order:

- a binding in ``easycrypt.project`` (see below);

- the enviroment variable ``EC_QUOTE_<NAME>`` — where ``<NAME>`` is
  ``name`` uppercased — gives the command for that specific quotation
  name;

- the environment variable ``EC_QUOTE_CMD`` — a fallback command used
  for any quotation whose specific variable is unset;

- otherwise, an executable ``handlers/<name>`` (also tried with the
  ``.py`` and ``.sh`` extensions) sitting in the same directory as the
  source file. This lets a directory of files be self-contained,
  needing no environment to set up — it is how the test suite binds
  its handlers.

The recommended way is the project file. In the ``[general]`` section of
``easycrypt.project``, add one repeatable ``quote`` entry per handler, of the
form ``name:command``::

  [general]
  quote = calc:handlers/calc.py
  quote = verbatim:python3 tools/verbatim.py

The ``command`` is a shell command (so it may include an interpreter and
arguments). When it is, verbatim, a relative path to an existing file, it is
resolved against the directory containing ``easycrypt.project``; otherwise it
is passed to the shell unchanged. Project-file bindings take precedence over
the environment, so the committed configuration is authoritative.

To bind a quotation ad hoc through the environment instead::

  export EC_QUOTE_CALC=/path/to/calc-handler

A quotation whose name resolves to no command raises an error located at the
quotation.

------------------------------------------------------------------------
The handler protocol
------------------------------------------------------------------------

For each quotation, EasyCrypt launches the bound command, writes a request to
its standard input, and reads the expansion from its standard output.

Request (sent by EasyCrypt)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A single header line, followed by the raw body::

  #ec-quote v1 name=<name> file=<orig-file> line=<L> col=<C> off=<O>
  <body bytes...>

where ``line``/``col`` are the 1-based line and 0-based column of the body's
first character in the original file, and ``off`` is its absolute character
offset.

Response (returned by the handler)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A single JSON object on standard output::

  { "expanded": "<expanded EasyCrypt source>",
    "segments": [ { "out": [ob, oe], "in": [ib, ie], "kind": "verbatim" },
                  ... ] }

``"expanded"`` (a string, required) is the replacement source. ``"segments"``
(optional) is the *source map*: each segment maps a half-open character range
``[ob, oe)`` of the **expanded** source back to a range ``[ib, ie)`` of the
**body** (offsets relative to the start of each, the body being the handler's
own stdin payload).

The two ``"kind"`` values answer one question: given an error at some offset
*inside* a segment's output range, can EasyCrypt compute the *exact*
corresponding input offset, or only point at the region as a whole? It depends
on whether the handler copied the text or invented it.

- ``"kind": "verbatim"`` — the output range is a **character-for-character
  copy** of the input range, so the two ranges have the same length
  (``oe - ob == ie - ib``). Output character *k* is input character *k*, so an
  error at output offset ``o`` maps to input offset ``ib + (o - ob)`` —
  **column-precise**. Mark a segment verbatim exactly when you pass input
  through unchanged.

- ``"kind": "synthesized"`` — the output range was **generated** by the
  handler (a computed value, boilerplate, glue), so it has no
  character-to-character relationship with the input and the ranges typically
  differ in length. There is no meaningful per-character offset to compute, so
  the whole output range is attributed to the whole input range: an error
  there points at the responsible region of the body rather than at a
  misleading column. Mark a segment synthesized whenever the output is not a
  literal copy.

Why distinguish them: collapsing *everything* to the region (as synthesized
does) is always safe but throws away precision; the ``+ (o - ob)`` arithmetic
is only valid when the copy is exact, which is what ``verbatim`` asserts. A
real handler mixes both — for example, expanding ``{% sugar foo %}`` into
``lemma foo_lemma : <user text>`` would mark the boilerplate
``lemma foo_lemma :`` synthesized and the copied ``<user text>`` verbatim, so
errors in the user's own text get exact columns while errors in the generated
glue fall back to the region. A handler that does not care about precision may
mark everything synthesized (coarse, but never wrong).

As a safety check, EasyCrypt treats a segment as verbatim only if it is
labelled ``"verbatim"`` **and** the two ranges actually have equal length; a
mislabelled (length-mismatched) verbatim segment is downgraded to the safe
collapse rather than producing bogus offsets.

If the response carries no (or an unparsable) ``"segments"`` field, the entire
expansion is attributed to the entire quotation (coarse mapping). Output that
is not a JSON object, or that lacks a string ``"expanded"`` field, is reported
as an error at the quotation.

Errors
~~~~~~

A handler that exits with a non-zero status makes EasyCrypt raise an error
located at the quotation, using the handler's standard-error output as the
message.

------------------------------------------------------------------------
Location mapping
------------------------------------------------------------------------

Because the expanded code is lexed and parsed in a separate buffer, the
positions EasyCrypt computes for it would, naively, refer to the generated
text. Using the source map and the body's original offset, EasyCrypt rewrites
those positions so that **every** location it reports — parse errors, type
errors, and printed locations alike — refers to the original source file.

For a ``verbatim`` segment this is exact down to the column; for a
``synthesized`` segment the location collapses to the originating region of
the body. Two examples make the difference concrete.

*Verbatim.* A handler that copies its body through unchanged reports::

  { "expanded": "op broken : int = no_such_op + 1",
    "segments": [ { "out": [0, 32], "in": [0, 32], "kind": "verbatim" } ] }

The error on ``no_such_op`` (output offset 18) maps to input offset 18, then
to the original file, so EasyCrypt points at the exact columns of
``no_such_op`` in the source — not at the quotation as a whole.

*Synthesized.* The ``calc`` handler turns the body ``6 * 7`` into ``42``::

  { "expanded": "42",
    "segments": [ { "out": [0, 2], "in": [0, 5], "kind": "synthesized" } ] }

Output and input have different lengths and ``42`` came from no particular
character of ``6 * 7``, so an error on ``42`` cannot be attributed to a column;
it points at the whole ``6 * 7`` region instead.

This is also why offset-range segments are used rather than line markers such
as ``#line``: a line marker can only say "this generated line came from input
line *N*", whereas reporting an error at the exact columns of ``no_such_op``
needs the character-level mapping a verbatim segment provides.

------------------------------------------------------------------------
Examples
------------------------------------------------------------------------

A ``calc`` handler that evaluates an integer expression returns the resulting
literal as a fragment, so::

  op forty_two = {% calc 6 * 7 %}.

expands to ``op forty_two = 42.``.

A ``verbatim`` handler that copies its body through with a single ``verbatim``
segment lets EasyCrypt point at the exact original character on error. Given::

  {% verbatim op broken : int = no_such_op + 1 %}.

EasyCrypt reports the unknown-identifier error at the column of ``no_such_op``
inside the quotation, even though that identifier sits at a different offset in
the generated buffer.

An ``ecm4`` handler that uses the m4 macro processor to process the
quotation's body using macros defined in an included m4 file. Suppose
we are given a file ``foo.m4`` with the macro definition::

  define(Test,
  $1.
  $2.
  )

Then processing::

  {%! ecm4 foo.m4
  Foo(left, right).

produces the expansion::

  left.
  right.

Finally, processing ``!%}.`` will cause Proof General to display the
next open goal.

.. note::

   The result of expanding a quotation is stored in the compiled ``.eco``
   file. When iterating on a handler, remove the stale ``.eco`` so the
   quotation is expanded afresh.
