========================================================================
Tactic: `clear`
========================================================================

The `clear` tactic can be used with any goal to remove hypotheses and
variables from the context. This is useful to simplify the context by 
removing assumptions and variables that are no longer needed.

There are two variants of the `clear` tactic: an opt-in variant where
specific hypotheses and variables are removed, and an opt-out variant 
where all hypotheses and variables except for the specified ones are removed.

.. admonition:: Syntax

  `clear`

When given no arguments, the `clear` tactic removes all hypotheses and 
all variables not transitively used in the goal from the context.

.. admonition:: Syntax

  `clear -{idents}`

Here, `{idents}` is a non-empty space separated list of identifiers of
the hypotheses and variables that should *not* be cleared. The tactic
removes all hypotheses and variables except for those in the list, and
those used transitively in the goal *or* in the objects in the list.

.. admonition:: Syntax

  `clear {idents}`

Here, `{idents}` is a non-empty space separated list of identifiers of
the hypotheses and variables to be cleared. If one of these is transitively
used in the goal, then it is not cleared and an error is raised.

.. ecproof::
   :title: Hoare logic example

   lemma L: true.
   pose x:=false.
   (*$*) clear x.
   (* `x` is now unbound *)
   pose x:=false.
   pose y:=x.
   pose z:=y.
   clear -y. 
   (* `z` is unbound, but `x` is not, since `y` depends on it *)
   pose z:=x.
   clear y.
   pose y:=z.
   clear. 
   (* everything is unbound, since nothing is in the goal *)
   pose x:=true.
   pose y:=false.
   clear. 
   (* we cannot clear `x` since it is in the goal,
       but `y` is not used so it becomes unbound *)
   pose y:= x.
   abort.
