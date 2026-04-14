.. _language-theories:

========================================================================
Theories and sections
========================================================================

EasyCrypt organizes definitions into *theories* and *sections*.
Theories provide namespacing and modularity -- grouping related
definitions under a name that can be required and imported. Sections
provide a scoping mechanism for local assumptions and abstract
declarations.

.. contents::
   :local:

------------------------------------------------------------------------
Theories
------------------------------------------------------------------------

A theory groups a sequence of declarations under a common name:

.. code-block:: easycrypt

   theory Arith.
     op double (x : int) = x + x.

     lemma doubleE (x : int) : double x = x + x.
     proof. by []. qed.
   end Arith.

After the theory is closed, its contents are accessed through
qualified names:

.. code-block:: easycrypt

   op y = Arith.double 3.

You can bring names into scope with ``import``:

.. code-block:: easycrypt

   import Arith.
   op y = double 3.     (* no qualification needed *)

Theories can be nested:

.. code-block:: easycrypt

   theory Outer.
     theory Inner.
       op f (x : int) = x.
     end Inner.
   end Outer.

   op y = Outer.Inner.f 1.

Local theories
~~~~~~~~~~~~~~

A ``local`` theory is not visible outside its enclosing theory:

.. code-block:: easycrypt

   theory T.
     local theory Helper.
       op aux (x : int) = x + 1.
     end Helper.

     op f (x : int) = Helper.aux (Helper.aux x).
   end T.

   (* Helper is not accessible here *)

------------------------------------------------------------------------
Abstract theories
------------------------------------------------------------------------

An *abstract* theory contains ``axiom`` declarations -- unproven
assumptions. It serves as a template that can be *cloned* (see
:ref:`language-cloning`) with concrete definitions replacing the
abstract ones.

.. code-block:: easycrypt

   abstract theory Group.
     type group.
     op e : group.                  (* identity *)
     op ( * ) : group -> group -> group.
     op inv : group -> group.

     axiom mulA (x y z : group) :
       x * (y * z) = (x * y) * z.
     axiom mul1 (x : group) : e * x = x.
     axiom mulV (x : group) : inv x * x = e.

     lemma mul1r (x : group) : x * e = x.
     proof. (* ... provable from the axioms ... *) admitted.
   end Group.

Abstract theories are the primary mechanism for generic,
reusable mathematics in EasyCrypt. The standard library uses them
extensively for algebraic structures, cryptographic primitives, and
game transformations.

------------------------------------------------------------------------
Sections
------------------------------------------------------------------------

A *section* opens a local scope in which you can introduce abstract
declarations (types, operators, modules) and local axioms. When the
section is closed, these abstractions are *discharged*: every lemma
proved in the section is generalized over the abstract declarations,
and the local axioms become hypotheses.

.. code-block:: easycrypt

   section.
     declare module A <: Adv {-Game}.

     declare axiom A_ll : islossless A.guess.

     lemma game_result &m :
       Pr[Game(A).main() @ &m : res] <= 1%r.
     proof. (* ... *) admitted.
   end section.

After the section closes, ``game_result`` becomes:

.. code-block:: easycrypt

   lemma game_result :
     forall (A <: Adv {-Game}),
       islossless A.guess =>
       forall &m, Pr[Game(A).main() @ &m : res] <= 1%r.

The ``declare`` keyword is used for all section-local abstractions:

``declare module``
  Introduces an abstract module (with an optional restriction).

``declare axiom``
  Introduces a local hypothesis that becomes a premise after the
  section closes.

``declare op``
  Introduces an abstract operator local to the section.

``declare type``
  Introduces an abstract type local to the section.

Named sections
~~~~~~~~~~~~~~

Sections can be given a name:

.. code-block:: easycrypt

   section Security.
     (* ... *)
   end section Security.

This is useful for documentation; it has no semantic effect beyond
matching the open/close delimiters.

------------------------------------------------------------------------
Namespaces and qualified names
------------------------------------------------------------------------

Every declaration lives in a namespace determined by the enclosing
theories. A fully qualified name has the form:

.. code-block:: text

   Theory1.Theory2. ... .name

When you ``import`` a theory, its names become available without
qualification. If two imported theories define the same name, you
must use qualification to disambiguate.

EasyCrypt resolves names by searching the current scope outward:
local definitions shadow imported ones, and more recently imported
theories take priority over earlier ones.

------------------------------------------------------------------------
Require, import, and export
------------------------------------------------------------------------

``require``
~~~~~~~~~~~

The ``require`` command loads an external ``.ec`` file and makes it
available as a theory:

.. code-block:: easycrypt

   require AllCore.

After this, the contents of ``AllCore`` are accessible via qualified
names (e.g., ``AllCore.List.size``).

``require import``
~~~~~~~~~~~~~~~~~~

Combines requiring with importing -- names are brought directly into
scope:

.. code-block:: easycrypt

   require import AllCore.

This is the most common form. Multiple theories can be required at
once:

.. code-block:: easycrypt

   require import AllCore List FSet Distr.

``require export``
~~~~~~~~~~~~~~~~~~

Combines requiring with exporting -- names are not only in scope
locally, but also re-exported to anyone who later imports the
current file:

.. code-block:: easycrypt

   require export AllCore.

``import`` and ``export`` (standalone)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

You can import or export a previously required theory:

.. code-block:: easycrypt

   require AllCore.
   import AllCore.

Or import a sub-theory:

.. code-block:: easycrypt

   require AllCore.
   import AllCore.List.

Aliasing on require
~~~~~~~~~~~~~~~~~~~

You can rename a theory on require:

.. code-block:: easycrypt

   require [AllCore as AC].

After this, the theory is known as ``AC`` instead of ``AllCore``.

``from`` clause
~~~~~~~~~~~~~~~

The ``from`` clause specifies a search path prefix:

.. code-block:: easycrypt

   require from Jasmin MyTheory.

This is used when theories are organized in subdirectories.
