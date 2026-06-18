Working through the chapter on ambient logic should give you a good
grasp of the ambient logic and tactics for reasoning with simple math.
Up until now, we were working with mathematical proofs that only used
logical reasoning. However, when working with programs and procedures we
need a way to reason with what the programs do.

For instance, let us think about an exponentiation program for integers
like so:

::

   exp(x, n):
     r = 1
     i = 0
     while (i < n):
       r = r * x
       i = i + 1
     return r

When presented with a program like this, our objective is to figure out
if the program behaves correctly. At first glance, this program seems
correct. However, a glaring mistake here is that the program will always
return :math:`1` as a result if we pass any negative integer as the
second argument. That isn’t the behaviour we expect from an
exponentiation function. So saying that the program is correct would be
a false claim. So to make claims about the behaviour of the program,
mathematically, we would say something like:

.. math::  \text{Given } \underbrace{x \in \mathbb{Z}, n \in \mathbb{Z} \text{ and } n \ge 0 }_a \ \ \ \underbrace{exp(x, n)}_b \text{  returns  } \underbrace{r = x ^{n}}_c 

.. math::  \text{Where } a \text{ is the precondition}, b \text{ is the program}, c \text{ is the postcondition} 

The Hoare triple
----------------

As marked in the statement above, claims that we make generally have
three distinct parts: preconditions, the program and postconditions.
Hoare logic formalises these three parts and introduces them as a
**Hoare triple**.

A Hoare triple is denoted like so:

.. math::   \{ P \} \  C \  \{ Q \} 

Here :math:`P,Q`, are conditions on the program variables used in
:math:`C`. Conditions on program variables are written using standard
mathematical notations together with logical operators like
:math:`\wedge` (‘and’), :math:`\vee` (‘or’), :math:`\neg` (‘not’) and
:math:`\implies` (‘implies’). Additionally, we have special conditions
:math:`true` or :math:`T` which always holds, and :math:`false` or
:math:`F` which never holds.

:math:`C` is a program in some specified language.

We say that a Hoare triple, :math:`\{P\} \ C \ \{Q\}`, holds if whenever
:math:`C` is executed from a state satisfying :math:`P` and if the
execution of :math:`C` terminates, then the state in which :math:`C`\ ’s
execution terminates satisfies :math:`Q`. We will limit our discussion
to programs which terminate.

Examples
~~~~~~~~

1. :math:`\{ x = n \} \  x:= x+1 \ \{ x = n+1 \}` holds. ( :math:`:=` is
   the assignment operator)
2. :math:`\{ x = n \} \ x:= x+1 \ \{ x = n+ 2 \}` doesn’t hold.
3. :math:`\{ true \} \ C \ \{ Q \}` is a triple in which the
   precondition always holds. So we’d say that this triple holds for
   every :math:`C` that satisfies the postcondition :math:`Q`.
4. :math:`\{ P \} \ C \ \{ true \}`, similarly, this triple holds for
   every precondition :math:`P` that is satisfied, and every program
   :math:`C`.
5. :math:`\{ false \} \ C \ \{ Q \}`, is an interesting triple which,
   according to our definitions, doesn’t hold since false is a statement
   that never holds. However, this is a slightly special case, as we
   will see in EasyCrypt.

Exercises
~~~~~~~~~

1. Does :math:`\{ x=1 \} \ x:=x+2 \ \{ x=3 \}` hold?
2. How about :math:`\{ true \} \ exp(x,a) \ \{ r=x^a \}`? Why?
3. What about :math:`\{ 2=3 \} \ x:=1 \  \{ x=1 \}`?

Strength of statements
----------------------

Informally, if a statement can be deduced from another, then the
statement that was deduced is a weaker statement.

Mathematically if we have :math:`P \implies Q`, we say that :math:`P` is
a stronger statement than :math:`Q`.

For example,

.. math::  x = 5 \implies x \ge 5

.. math::  x = 5 \text{ is a stronger statement than } x \ge 5

As discussed earlier, we have two special statements, :math:`true`,
which always holds, and :math:`false`, which never holds. These are the
weakest and the strongest statements there are, respectively.

Since any statement that holds can imply that :math:`true` holds. The
reason is that it always holds, :math:`true` is the weakest statement
there is.

Similarly, :math:`false` never holds. So, no statement can imply
:math:`false`; hence, it is the strongest statement there is.

Proof trees
-----------

So far, we looked at Hoare triples for simple statements, these can be
thought of “programs” with a single instruction as well. However, we
need to be able to work with multiple statements and more complex
statements. We achieve this by formalizing a set of axioms that we
believe to be true, and then we combine these axioms to make claims
about complex statements. We often visualize these series of steps in
which we put the axioms together into *schemas* or *proof trees*.

For example: For a statement :math:`S`, we say it is or provable by
denoting it with a turnstile (:math:`\vdash`) symbol like so
:math:`\vdash S`, and its proof can be denoted by:

.. math::  \dfrac{\vdash S_1, \vdash S_2, \dots ,\vdash S_n}{\vdash S} 

This says the conclusion :math:`S` may be deduced from the
:math:`S_1, \dots, S_n` which are the hypotheses of the rule. The
hypotheses can either all be theorems or axioms of Hoare Logic or
mathematics.

Now, we will take a look at some of the axioms of Hoare logic with
examples to give you a flavour of how they work. One of the reasons we
cover these is because these axioms form the basis for the tactics we
use in Hoare logic in EasyCrypt. Of course, the main idea is to
familiarize the reader with the basics since the main goal is for the
machine to take care of the specifics.

Axioms of Hoare logic
---------------------

1. **Assignment**:

   .. math::  \vdash \{P[E/V ]\} \ V :=E \ \{P\} 

   Where :math:`V` is any variable, :math:`E` is any expression,
   :math:`P` is any statement, and the notation :math:`P[E/V]` denotes
   the result of substituting the term :math:`E` for all occurrences of
   the variable :math:`V` in the statement :math:`P`.

   Example: :math:`\vdash \{ y = 5 \} \, x := 5 \,\{ y = x \}`

2. **Precondition strengthening**: When we have a Hoare triple
   :math:`\{ P ' \}\ C \ \{ Q \}`, where :math:`P'` is a statement that
   follows from a stronger statement, :math:`P`. Then we can say,

   .. math::  \dfrac{\vdash P \implies P', \vdash \{P'\}\ C \ \{Q\}} {\vdash \{P\} \ C \ \{Q\}} 

   Example: Let

   .. math:: C = [x:=x+2]  

   .. math:: P = \{x = 5\}

   .. math:: P' = \{x \ge 5\} \text{ , and}

   .. math:: Q = \{x \ge 7\}

   Using the precondition strengthening axiom we have,

   .. math::  \dfrac{\vdash \{x = 5\}  \implies \{x \ge 5\} ,\ \vdash \{x \ge 5\} \ x:=x+2 \ \{x \ge 7\} } {\vdash \{x=5\} \ x:= x + 2 \ \{x \ge 7\}} 

3. **Postcondition weakening**: Similarly, when we have a Hoare triple
   :math:`\{P\}\,
   C \,\{Q'\}`, where :math:`Q'` is a strong statement, and if :math:`Q`
   follows from :math:`Q'`. Then we can say,

   .. math::  \dfrac{\vdash \{P\}\ C \ \{Q'\}, \ \vdash Q' \implies Q}{ \vdash \{P\} \ C \ \{Q\}} 

   Example: Let

   .. math:: C = [x:=x+2]  

   .. math:: P = \{x = 5\}

   .. math:: Q' = \{x = 7\} \text{ , and}

   .. math:: Q = \{x \ge 7\}

   With the postcondition weakening axiom, we have,

   .. math::  \dfrac{\vdash \{x = 5\}\ x:=x+2 \ \{x =7\}, \ \vdash x = 7  \implies x \ge 7 } {\vdash \{x=5\} \ x:= x + 2 \ \{x \ge 7\}} 

   Together the precondition strengthening and postcondition weakening
   axioms are known as the

   .. math:: \textbf{consequence rules}

   .

4. **Sequencing**: For two programs :math:`C_1, C_2`, we have

   .. math::  \dfrac{ \vdash \{P\}\ C_1 \ \{Q'\}, \ \vdash \{Q'\}\ C_2 \ \{Q\}, }{ \vdash \{P\}\ C_1;C_2 \ \{Q\} } 

   Example: Let

   .. math:: C_1 = [x:=x+2] 

   .. math:: C_2 = [x:=x*2] 

   .. math:: P = \{x = 5\}

   .. math:: Q' = \{x = 7\}  \text{ , and}

   .. math:: Q = \{x = 14\}

   Using the sequencing axiom, we have,

   .. math::  \dfrac{ \vdash \{x = 5\} \ x:=x+2 \ \{x =7\}, \ \vdash \{x = 7\}\ x:=x * 2  ,\{x =14\} } {\vdash \{x=5\} \ x:= x + 2, x:= x * 2 \ \{x =14\}} 

We go through these examples to get a sense of what formal proof trees
look like and the theory that formal verification is based on. The proof
trees that we’ve used are already simplified to exclude the assignment
axiom and steps that we as humans can easily understand and gloss over.
Proof trees get quite large and unwieldy as soon as we do anything
non-trivial. This is exactly where formal verification tools come into
the picture. So, let us now switch to EasyCrypt and work with Hoare
triples.

Hoare logic has been studied quite extensively, and there are plenty of
good textbooks (`Textbook 1 <https://dl.acm.org/doi/10.5555/975331>`__,
`Texbook
2 <https://mitpress.mit.edu/books/foundations-programming-languages>`__)
that one can refer to for mathematical rigour and completeness. The
objective here is to give the reader an intuitive understanding of the
math, and enough working knowledge required to work with EasyCrypt.

HL in EasyCrypt
---------------

With a basic understanding of HL, we can now proceed to work with it in
EasyCrypt. We will work through the file
```hoare-logic.ec`` </docs/tutorials/introduction-itp-program-logics/hoare-logic.ec>`__.
As before, it is recommended to work with the file in the Proof General
+ Emacs environment. However, reading through this section provides the
basic ideas developed in the practice file.

Basic Hoare triples
~~~~~~~~~~~~~~~~~~~

Let us start small and first work with some examples that we saw
earlier. We first define a module to define two procedures for the
programs.

::

   module Func1 = {
     proc add_1 (x:int) : int = { return x+1; }
     proc add_2 (x: int) : int = { x <- x + 2; return x; }
   }.

A Hoare triple denoted by :math:`\{P\} \ C\ \{Q\}` in theory is
expressed as ``hoare [C : P ==> Q ]`` in EasyCrypt, with the usual
definitions. Additionally, the return value of the program, :math:`C`,
is stored in a special keyword called ``res``.

So the triple, :math:`\{x=1 \} \  \text{Func1.add}\_\text{1}
\  \{x=2\}`, would be expressed in EasyCrypt like so:

::

   lemma triple1: hoare [ Func1.add_1 : x = 1 ==> res = 2].

When working with Hoare logic or its variants, the goal will be
different from what a goal in ambient logic looks like. For instance,
evaluating the ``lemma triple1`` produces the following goal.

::

   Current goal
   Type variables: <none>
   ---------------------------------------------
   pre = x = 1

       Func1.add_1

   post = res = 2

We need to start stepping through the procedure or program that is being
reasoned about and change the preconditions and postconditions according
to axioms and lemmas that we have.

To make progress here, we first need to tell EasyCrypt what
``Func1.add_1`` is. The way to do that is by using the ``proc`` tactic.
It simply fills in the definitions of the procedures that we define.
Since ``Func1.add_1`` is made up of only a return statement, ``proc``
replaces ``res`` with the return value. This leaves us with an empty
program. This is what we want to work towards; using different tactics
we would like to change the preconditions and postconditions depending
on what the programs that we are reasoning with do. Once we have
consumed all the program statements, we can transform the goal from a HL
goal to a goal in ambient logic using the ``skip`` tactic. ``skip`` does
the following:

.. math:: \dfrac{ P \implies Q}{\{P\} \text{ skip; } \{Q\}}\texttt{skip}

.. math:: \text{skip;}

\ signifies an empty program, while

.. math:: \texttt{skip}

is the tactic itself.

This puts us back in the familiar territory of ambient logic, and we can
use all the tactics that we learnt in ``ambient-logic.ec``. The only
difference is that transitioning a goal from Hoare logic to ambient
logic introduces some qualifiers about the memory that the program works
on. Hence, we need to handle those as well. In this example, the goal
after evaluating ``skip`` will simply read:
``forall &hr, x{hr} = 1 => x{hr} + 1 = 2``. The proof for which follows
pretty trivially. The only difference is that we need to move the memory
into the assumption by prepending the & character in the ``move =>``
tactic.

So the full proof for this simple example looks like so:

::

   lemma triple1: hoare [ Func1.add_1 : x = 1 ==> res = 2].
   proof.
   proc.
   skip.
   move => &m H1. (* &m moves memory to the assumption *)
   subst. (* Substitutes variables from the assumptions *)
   trivial.
   qed.

Now let us work with a program where the body is not empty.

::

   lemma triple2: hoare [ Func1.add_2 : x = 1 ==> res = 3 ].

Using ``proc`` produces the following goal.

::

   Current goal
   Type variables: <none>
   ---------------------------------------------
   Context : Func1.add_2

   pre = x = 1

   (1)  x <- x + 2

   post = x = 3

When we are faced with :math:`\\{P\\} S1; S2; S3; \\{Q\\}` with the
usual definitions, applying the ``wp`` tactic consumes as many ordinary
statements as possible from the end. Then it replaces the postcondition
:math:`Q`, with a precondition :math:`R`. :math:`R` is chosen such that
it holds in conjunction with the consumed statements and the original
postcondition and it is as weak as possible (*w*\ eakest
*p*\ recondition). It is easier to visualize this in a proof tree.

For instance, when we have :math:`\{P\} S1; S2; S3; \{Q\}` and
:math:`S2; S3;` are statements that can be dealt with some axioms or
logical deductions, then ``wp`` does the following:

.. math::  \dfrac{\{P\} S1; \{R\} \ \ \dfrac{...}{\{R\} S2; S3; \{Q\}}\text{\tiny{(Other rules)}}}{\{P\} S1; S2; S3; \{Q\}}\texttt{seq}

The judgement :math:`\{R\} S2; S3; \{Q\}` is guaranteed to hold, and
hence the goal transforms to just :math:`\{P\} S1; \{R\}`.

In our context, ``wp`` consumes the only instruction that we have in the
program and produces the judgement
:math:`\{x = 1\} \ \text{skip;} \ \{x+2=3\}` to which we apply ``skip``.
This gives us the following proof-tree:

.. math:: \dfrac{x = 1  \implies x+2=3}{    \dfrac{    \{x = 1\} \ \text{skip;} \ \{x+2=3\}    }{    \{x = 1\} \ x:= x+2 \ \{x=3\}    }\texttt{wp}}\texttt{skip}

Putting us back in familiar territory, and the proof follows quite
easily.

::

   lemma triple2: hoare [ Func1.add_2 : x = 1 ==> res = 3 ].
   proof.
   proc.
   wp.
   skip.
   move => &m x.
   subst.
   trivial.
   qed.

Automation, and special cases
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Now that we have an understanding of how we can make progress, let us
take a look at how we can use automation since we still have powerful
external solvers at our disposal and we would like to use them whenever
we can. We will be working with the following procedures in this
section.

::

   module Func2 = {
     proc x_sq (x:int) : int = { return x*x; }
     proc x_0  (x:int) : int = { x <- x*x; x <- x-x; return x; }
     proc x_15 (x:int) : int = { x <- 15; return x; }
   }.

For instance, let us take a look at a triple, which states that if you
square any integer greater than or equal to 4, the result is greater
than or equal to 16. Pretty trivial and straightforward when you think
about it. However, the proof for something simple like this becomes
quite tiresome, hence we will simply ask ``smt`` to handle it. The only
issue however is that smt solvers can only work on goals in ambient
logic. So it is up to us to bring the goal to a state that doesn’t
involve Hoare logic. In this example, since ``x_sq`` consists of a
single ``return`` statement, ``proc`` and ``skip`` are enough.

::

   lemma triple3: hoare [ Func2.x_sq : 4 <= x ==> 16 <= res ].
   proof.
   proc.
   skip.
   smt().
   qed.

Let us now look at the triple
:math:`\{\text{false}\} \ x:=15 \ \{x = 0\}.`

Theoretically, we know that this triple doesn’t hold, since ``false``
never holds. We have the ``proc x_15`` in the ``module Func2`` that we
can use to express that triple in EasyCrypt. The interesting thing is
that we can actually write proof for the triple in question.

::

   lemma triple4: hoare [ Func2.x_15 : false ==> res=0 ].
   proof.
     proc.
     wp.
     skip.
     move => _ f.
     trivial.
   qed.

The reason we can do this is that we essentially force the assumption
that ``false`` holds and we want to prove the postcondition
:math:`15 = 0`. As absurd as it is, we know that ``false`` is the
strongest statement there is. By getting EasyCrypt to the state where
``false`` holds would imply that anything and everything can be derived
from it. Hence we can actually “prove” that :math:`15 = 0`.

The point to understand here is that we could only do this because we
moved ``false`` into the context manually when we used the ``move =>``.
So our math is still consistent and the world hasn’t exploded yet. The
way to think about this triple is assuming ``false`` holds implies that
:math:`15 = 0`.

Conditionals and loops
~~~~~~~~~~~~~~~~~~~~~~

Let us now work with some more interesting functions and triples. We
define a flipper function which simply returns the opposite of the
boolean value that it gets.

::

   module Flip = {

   proc flipper (x: bool) : bool =
     {
     var r: bool;
     if (x)
     { r <- false; }
     else
     { r <- true; }
     return r;
     }
   }.

Let us say that we would like to prove the fact related to this program,
that if the input is :math:`\{\text{true}\}`,
:math:`\texttt{Flip.flipper}` returns :math:`\{\text{false}\}`.

We use a slightly verbose proof here to demonstrate how to open up an
``if`` block. Using the ``if`` tactic in the proof script gives us two
goals, one in which the ``if`` condition holds, and another in which it
doesn’t. In our case, it splits into one goal with ``x = true``, and
another with ``x <> true``. Additionally, when the current goal is a HL,
pHL, pRHL statement the ``auto`` tactic uses various tactics in an
attempt to reduce the goal to a simpler one automatically. It never
fails, but it may fail to make any progress. For instance, in this first
usage of the tactic, it does the job of the ``wp, skip, and trivial``
tactics.

::

   lemma flipper_correct_t:
       hoare [ Flip.flipper : x = true ==> res = false ].
   proof.
   proc.
   if.
     (* Goal 1:  x = true *)
     auto.

     (* Goal 2: x <> true. *)
     auto.
     smt.
   qed.

Notice the repetition of proof steps in the branches. This can be
reduced by using tacticals. In order to tell EasyCrypt to repeatedly use
certain tactics on all resulting goals, we use the “;” tactical. So, we
can simplify the above proof like so

::

   lemma flipper_correct_f:
       hoare [ Flip.flipper : x = false ==> res = true ].
   proof.
   proc.
   if; auto; smt.
   qed.

However, since this program is quite simple we can actually make the
proof shorter. We can also make the logic more abstract like so:

::

   lemma flipper_correct (x0: bool):
       hoare [ Flip.flipper : x = x0  ==> res <> x0 ].
   proof.
   proc.
   auto.
   smt.
   qed.

This is how proofs are polished and made shorter. We first write a
verbose proof, then keep experimenting to find shorter and more elegant
proofs.

Let us now increase the difficulty and work with a slightly more
involved example. We define the exponentiation function that we saw
earlier in EasyCrypt.

::

   module Exp = {
   proc exp (x n: int) : int =
     {
     var r, i;
     r <- 1;
     i <- 0;
     while (i < n){
       r <- r*x;
       i <- i+1;
     }
     return r;
     }
   }.

Let us formulate a Hoare triple that says that ``exp(10, 2) = 100``,
since of course :math:`10^2 = 100`.

We would have the triple

.. math:: \{x = 10 \wedge n=2 \}\ \text{Exp.exp}\ \{\text{res}=100\}

. In EasyCrypt we would state the lemma like we have done earlier. For
the proof, we will employ loop unrolling. We adopt this method since we
know that the while loop will be executed twice, and we can work through
those manually. To unroll a loop with ``unroll n``, where ``n`` is the
line of code with the loop statement, a ``while`` loop in our case. With
the loops unrolled, we get two if conditions which we know will hold,
and a while loop for which the condition will not hold. To reason with
loops and conditions like these EasyCrypt provides two tactics
``rcondt``, and ``rcondf``. They can be read as “remove the condition
with a true/false assignment”. We will use the ``rcondf`` version. This
forces us to prove that the boolean in the ``while`` block, ``(i<n)``
evaluates to ``false`` in order for it to get rid of the block entirely.
So we are asked to prove that ``!(i<n)``, which is quite simple to
prove. The rest of the proof also comes through quite easily as well.

::

   lemma ten_to_two:
       hoare [ Exp.exp : x = 10 /\ n = 2 ==> res = 100 ].
   proof.
   proc.
   simplify. (* Makes the goal more readable *)
   unroll 3.
   unroll 4.
   rcondf 5.
   (* post = !(i<n) *)
   wp.
   skip.
   smt.
   (* post = r = 100  *)
   wp.
   skip.
   smt.
   qed.

As usual, we could have used some tacticals to shorten the proof. So let
us do that, to clean up the previous proof.

::

   lemma ten_to_two_clean:
       hoare [ Exp.exp : x = 10 /\ n = 2 ==> res = 100 ].
   proof.
   proc.
   unroll 3.
   unroll 4.
   rcondf 5; auto.
   qed.

For a loop that unrolls twice, it is easy to do it manually. However,
this strategy wouldn’t work for a different scenario. For instance, in
order to prove that the program works correctly, we need to prove the
correctness for every number, so we would prefer to work with abstract
symbols and not concrete numbers like :math:`10^2`. In order to work up
to it, let us try to prove that :math:`2^{10}` works as intended. But
first, we need to understand that EasyCrypt was not built for
computations. It can handle small calculations like we’ve seen so far
but asking EasyCrypt to do :math:`2^{10}` doesn’t work as we’d like it
to. For instance, take a look at the following lemma, and our attempt to
prove it.

::

   lemma twototen: 2^10 = 1024.
   proof.
   (* We can't make any progress with these. *)
   trivial.
   simplify.
   auto.
   (*
   smt fails as well, we will admit this result,
   since we know it is true.
   *)
   admit.
   qed.

Again, the point here is that EasyCrypt wasn’t built for tasks like
these. For the time being, we will admit this lemma, since we know that
:math:`2^{10}` is in fact 1024. We need this to prove the next few
lemmas relating to Hoare triples.

At this point, we’d like to prove that ``exp(2,10)`` works as expected,
however, we can’t do so with direct computation since it would be
painful and also not the purpose of using EasyCrypt, so to reason with
loops, we need to be able to think of loop invariants and think about
the program variables which change. For instance, we know that the
variable ``x`` remains the same throughout the computation. So let us
try to get rid of the ``while`` loop stating that this is the only
invariant. We know that this is obviously not enough, since doing this
will in a sense forget about what happens to the other variables.
However, examples that get stuck are instructive as well as they allow
us to understand what we did wrong. The following proof reaches a point
in which the postcondition states:

``post = ... forall (i0 r0 : int), ! i0 < n => x = 2 => r0 = 1024}``

This can’t hold since it states that the result ``r0`` is 1024 for every
``r0``, hence we abort this attempt.

::

   lemma two_to_ten:
       hoare [ Exp.exp : x = 2 /\ n = 10 ==> res = 1024 ].
   proof.
   proc.
   simplify.
   while ( x = 2 ).
   wp.
   auto.
   abort.

Similarly, we try another invariant which helps, but still gets stuck
since it doesn’t account for how the variable ``r`` changes after every
iteration of the loop. We abort this attempt as well.

::

   lemma two_to_ten:
       hoare [ Exp.exp : x = 2 /\ n = 10 ==> res = 1024 ].
   proof.
   proc.
   while ( x = 2  /\ 0 <= i <= n).
   wp.
   auto.
   smt.
   abort.

We know that after every iteration, the variable ``r`` is multiplied by
``x``. So in this case, since we have ``x = 2``, essentially at the end
of ``i`` iterations of the loop we have the fact that
:math:`\text{r} = 2^\text{i}`. This is an invariant, and it binds r to
the variables that are passed to the loop. With this, we finally have
all the ingredients for the invariant and we complete the proof, like
so:

::

   lemma two_to_ten:
       hoare [ Exp.exp : x = 2 /\ n = 10 ==> res = 1024 ].
   proof.
   proc.
   while (x = 2  /\ 0 <= i <= n /\  r = 2^i).

   wp.
   skip.
   smt.

   wp.
   simplify.
   auto.

   (*
   Sometimes, the goal can be quite complicated, and we
   can use "progress" to break it down into smaller goals
   *)
   progress.

   (* 2 ^ 0 = 1 *)
   smt.

   (* 2^10 = 1024 *)
   smt.
   qed.

Finally, we have an invariant that works. Let us clean up the proof, and
also if we think about it, the condition ``x=2`` isn’t really needed,
since the program never modifies the value of ``x``. Let us get rid of
that condition while we are at it.

::

   lemma two_to_ten_clean: hoare [ Exp.exp : x = 2 /\ n = 10 ==> res = 1024 ].
   proof.
   proc.
   simplify.
   while ( r = x^i /\ 0 <= i <= n); auto; smt.
   qed.

Now the proof seems so innocuous and straightforward. However, it is
important to understand that these proofs and figuring out the loop
invariants always takes a few tries, and sometimes crafting the right
invariant can be an art by itself. This also gets quite hard when there
are a lot of variables to keep track of. So it is good practice to work
with smaller examples first.

Now let us try to work with abstract symbols, the stuff that EC was
actually built for. In order to claim that the ``exp`` function is
correct, we need to have the condition that the exponent that we provide
is greater than zero. We use ``x0``, and ``n0``, in order to
differentiate from the program variables.

::

   lemma x0_to_n0_correct (x0 n0: int):
     0 <= n0 =>
     hoare [ Exp.exp : x = x0 /\ n = n0 ==> res = x0 ^ n0 ].
   proof.
   move => Hn0.
   proc.
   while (r=x^i /\ 0 <= i <= n).
   wp.
   skip.
   smt.

   wp.
   skip.
   progress.
   smt.
   smt.
   qed.

Again, we can clean up the proof like so:

::

   lemma x0_to_n0_correct_clean x0 n0:
     0 <= n0 =>
     hoare [ Exp.exp : x = x0 /\ n = n0 ==> res = x0 ^ n0 ].
   proof.
       move => Hn0.
       proc.
       while (r=x^i /\ 0 <= i <= n); auto; smt.
   qed.

With that we conclude this chapter on Hoare logic. In this chapter we
first presented the theory of Hoare logic, and we saw how to work with
HL in EasyCrypt. Starting with simple Hoare triples we worked our way up
to reasoning with more advanced Hoare triples, and along the way we
learnt some new tactics that allowed us to work with the HL goals.
