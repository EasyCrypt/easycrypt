pragma Goals: printall.

require import AllCore.

(*
Let us work with Relational Hoare Logic and see how
to handle it in EasyCryt. As usual let us start simple and
define two functions that swap variables.
*)

module Jumbled = {
  proc swap1 (x y: int) : int*int = {
  var z;
  z <- x;
  x <- y;
  y <- z;
  return (x,y);
  }

  proc swap2 (x y: int) : int*int = {
  var z;
  z <- y;
  y <- x;
  x <- z;
  return (x,y);
  }
}.

(*
A couple of things to observe in the definitions.
Firstly, they infact swap variables, however the order in which
they swap them is different.
Secondly, the return type of the functions is a tuple.
Notice the syntax of how it is done. (int*int)

On paper we define hoare quadruples like so:
{P} C1 ~ C2 {Q}
While in EC, we use the following syntax to say the same:
equiv [C1 ~ C2 : P ==> Q]
As with Hoare triples in EC, we access the results of
both the programs using the "res" keyword.
Let us first prove that swap1 is equivalent to itself.
*)

lemma swap1_equiv_swap1:
equiv [Jumbled.swap1 ~  Jumbled.swap1 : 
      x{1}=x{2} /\ y{1}=y{2} ==> res{1} = res{2}].
(*
The numbers in the curly braces are identifiers
for programs. So res{1} should be read as result 
from program 1, and res{2} is the result from program 2.
*)
proof.
  proc.
  simplify.
  auto.
qed.

(*
Let us now prove that both the swap functions are equivalent.
Notice the shorthand that we use for the conditions.
The eagle-eyed readers would've noticed this
shorthand in the goals pane in the previous exercise.
*)

lemma swaps_equivalent:
equiv [Jumbled.swap1 ~  Jumbled.swap2 : ={x, y} ==> ={res} ].
proof.
proc.
  simplify.
(*
Now we have different programs, and the way we work with them is by 
using similar tactics that we used for HL.
The only difference now is that we have to add identifiers
to the tactics for them to target specific sides and lines of code.
For instance, for the sake of a demonstration let us use the wp tactic
in an asymmetric way.
*)
  wp 2 3.
(*
The tactic "wp n1 n2" will try to consume code
up to the n1-th line from the left program,
up to the n2-th line from the right program.
As you can see here, using "wp 2 3"
knocks off the 3rd line from the left program,
and leaves the right program untouched.
Try C-c C-u to undo and then C-c C-n
to redo and notice how things change.
*)
  wp 2 2.
  wp 0 1.
  wp 0 0.
  skip.
  trivial.
qed.

(*
Let us clean up the proof since we will never use
wp in the way we did above. In general we will rely
on EC to automatically work with whatever it can.
*)

lemma swaps_equivalent2:
equiv [Jumbled.swap1 ~  Jumbled.swap2 : ={x, y} ==> ={res} ].
proof.
  proc.
  wp.
  skip.
  simplify.
  trivial.
qed.

(*
Now that we see the complete proof relies only on
"wp, skip, and trivial" tactics, we can replace them with "auto".
Let us clean up the proof further with auto.
*)

lemma swaps_equivalent_clean:
equiv [Jumbled.swap1 ~  Jumbled.swap2 : ={x, y} ==> ={res}  ].
proof.
  proc.
  auto.
qed.

(*
Now let us take a small detour here and build on the the module types
that we briefly introduced in the exercise file of HL.
When working with cryptography, we generally don't know about the
inner workings of an adversary or an oracle.
In order to model these in EC we have the module types.
*)

module type Adv = {
  proc eavesdrop_one(): bool
  proc eavesdrop_two(): bool
}.

(*
By defining the module type Adv, we are instructing EC that any
concrete module which is of the Adv type has to, at the very least,
implement eavesdrop_one, and eavesdrop_two procedures.
What is interesting is that EC allows us to reason with the
abstract module types as well. For example let us define a module
which expects an Adv as input, and has a procedure
*)

module Abstract_game(A:Adv) = {
  proc one(): bool = {
      var x;
      x <@ A.eavesdrop_one();
      return x;
  }
}.

(*
At this stage, we don't know what A.eavesdrop_one does.
Neither does EC. However, we can still prove certain facts
related to it. Let us take a look at a simple reflexivity
example to understand how that works.
Notice that we have a new term glob A, in the precondition.
It stands for the global variable of the module A.
So in this next lemma we claim that, if the global state of the A
which is of type Adv is equal at the beginning of the program
then running the same program yields us the same result.
Quite a simple lemma, however the point to note here is
that we haven't defined what the function is.
*)

lemma eavesdrop_reflex(A<:Adv):
equiv [Abstract_game(A).one ~ Abstract_game(A).one :
      ={glob A} ==> res{1} = res{2} ].
proof.
  proc.
  call (_: true).
(*
the call tactic does a few complicated things under the hood,
but at this point of time, what we can take away is that 
if there is a call to the same abstract function on both
sides, call (_: true), knocks them both off.
*)
  auto.
qed.

(*
However, let us also define a concrete instantiation of Adv,
and work with it. A is quite basic, and either always returns
true or always returns false.
*)

module A : Adv = {
  proc eavesdrop_one() = {
    return true;
  }

  proc eavesdrop_two() = {
    return false;
  }
}.

module Games = {
  proc t(): bool = { var x; x <@ A.eavesdrop_one(); return x; }
  proc f(): bool = { var x; x <@ A.eavesdrop_two(); return x; }
}.

lemma games_quadruple (A<:Adv):
    equiv [Games.t ~ Games.f : ={glob A} ==> res{1} <> res{2}].
proof.
  proc.
  inline *.
  wp.
  simplify.
  trivial.
(* auto can replace wp. simplify. trivial  *)
qed.

(*
The point of this detour is that,
when we work with cryptographic proofs we will
be dealing with adversaries both concrete and abstract ones.
With these exercises are warming up and building up those concepts.
*)

(*
Before we move on to other things, let us take a look at
something non-trivial in RHL.
As we discussed earlier, one of the use cases of RHL
is to ensure that compiler optimisations preserve program behaviour.
Let us take a look at an example of this with a simple compiler
optimisation called "invariant hoisting".
Take a look at the programs defined below.
*)

module Compiler = {
  proc unoptimised (x y z: int) : int*int = {
    while (y < z){
      y <- y + 1;
      x <- z + 1;
    }
    return (x,y);
  }

  (*
  As you can observe, if the condition of the while loops holds
  for even one iteration the variable x is set to z+1.
  However every subsequent iteration of the loop doesn't change x,
  since z is also constant. Hence to save on computation,
  the compiler hoists that line out of the scope of the while loop.
  Like so:
  *)

  proc optimised (x y z: int) : int*int = {
    if(y < z){
      x <- z + 1;
    }
    while (y < z){
      y <- y + 1;
    }
    return (x,y);
  }
}.

(*
Now let us try to prove the fact that
the behaviour of both the programs is equivalent.
At this point there can be two possibilities:
1. !(y < z) => (y = z) \/ (z < y):
In this case neither the while loop, nor the if condition are satisfied.
So both the programs effectively do nothing to the variables.

or

2. (y < z): 
The while loop and the if condition executed at least once.
In this case the variables are modified.

So in order to prove that the optimisation is indeed correct, we can
break our proof into these two cases, prove them independently
and then put them back together.

An important point to note here is that, this proof took multiple attempts
and a fair amount of time to polish. It is important to understand
that this is a normal process, and takes practice to be able
to work with logic. Anyway, let us trudge on.

Let us work with the first part in which the loops are never executed.
*)
lemma optimisation_correct_a:
equiv [Compiler.unoptimised ~ Compiler.optimised:
      ={x, y ,z} /\ !(y{1} < z{1}) ==> ={res}  ].
proof.
  proc.
  simplify.
(*
At this point we introduce the seq tactic.
The seq tactic does the following:

          {P} A1; A2; A3 ~ B1; B2; B3 {Q}
  ----------------------------------------------- seq 1 2: (R)
   {P} A1; ~ B1; B2; {R} /\ {R} A2; A3; ~ B3; {Q}

In general, the idea behind using the seq tactic is to
break the programs into manageable chunks, and deal with them
separately.
In our program, we have an if condition, that
we can effectively deal with and then work with the while
conditions.

In this part of the proof, we know that the code inside the conditions
is not executed. Hence know that
R will simply have the variables unchanged
*)
  seq 0 1: ( ={x, y ,z} /\ !(y{1} < z{1}) ).
(* Pause and see how the goal changed and now we have two goals to prove *)
  auto.
(*
Now we know that neither of the while conditions
hold. So like we did earlier, we will use the rcondf to work with them.
rcondf breaks the goal into two, first part keeps everything before the while
intact. In our case, there is nothing so it adds a "skip", and a post-condition
which is the negation of the boolean expression of the while.
So in our case !(y < z).
When working with RHL, we have to use program identifiers, so that
EC can target the correct side and lines of code.
*)
  rcondf {1} 1.
  auto.

  (* Similarly, we work with the right program. *)
  rcondf {2} 1.
  auto.

  auto.
qed.

(*
Now let us work with the second part of the proof which deals with
the part where the loops are executed.
The only complex part of this proof is the while loop.
So please pause before and after to ponder about the invariant.
*)

lemma optimisation_correct_b: 
equiv [Compiler.unoptimised ~ Compiler.optimised:
      ={x, y ,z} /\ y{1}<z{1} ==> ={res}  ].
proof.
  proc.
(*
As we did earlier, we will get rid of the if,
but this time we know that it will be executed,
hence we have x{2} = z{2} + 1 in the condition.
*)
  seq 0 1: (={y,z} /\ y{1}<z{1} /\ x{2} = z{2} + 1).
  simplify.
  auto.
  while (={y,z} /\ x{2} = z{2} + 1 /\ (y{1}<z{1} \/ x{1} = z{1} + 1)).
  auto.
  auto.
  smt().
qed.

(*
Here we have used "smt()." instead of "smt."
"smt()." simply sends only the goal (conclusion and hypothesis)
to the external solvers.
While "smt." tries to pick an extra set of lemmas to send as well.
If this process of picking what to send fails, the tactic will
send all lemmas of all the theories in the context.
This can be quite huge, and ultimately inefficient.

For smaller proofs, like ours, using either works fine, however
in the interest of efficiency, using "smt()." is recommended.
Often, if we know a certain lemma will be used for a proof,
we can send the specific lemmas to the external solvers like so:
smt(lemma_1,lemma_2,...,lemma_n).
*)

(*
Now let us put these two things together.
*)

lemma optimisation_correct:
equiv [Compiler.unoptimised ~ Compiler.optimised:
      ={x, y ,z} ==> ={res}  ].
proof.
  proc*.
(*
Here we introduce "proc*",
proc* modifies the goal in a way similar to "proc", but
without losing the fact that the code is infact a procedure call.
With proc, we usually lose this connection to the procedures.
*)

(*
Now we split on the boolean expression of the while loop.
Although we can't see it in the goal explicitly, we know this
is what we need to do since we put together two parts earlier.
*)
  case (y{1}<z{1}).
(*
Notice how the goals changed, and how these are the exactly our
previous two parts.
*)
    call optimisation_correct_b. simplify. auto.
    call optimisation_correct_a. simplify. auto.
qed.

(*
Exercises:
The compiler optimisation that we presented above
was called "invariant hoisting". These kinds of optimisations
are part of a larger set of optimisations that are called
dead store optimisations. You can read more about them
here.
https://en.wikipedia.org/wiki/Dead_store
However, as an exercise we suggest that you can try to implement
some other compiler optimisations and prove that
they preserve program behavior.
We provide another example here for the reader to complete.

There are two possible approaches here.
You could unroll the while loop 10 times, and continue on.
Or figure out an invariant to progress.
You might also need the tactic "sp", since we have some instructions
before the while loop, that can be knocked off automatically.
Alternatively, you could use the "seq" tactic as well.
*)

module Compiler2 = {
  proc unoptimised (x: int) : int = {
    var y, z;
    y<-10;
    z <-0;
    while(z<y){
      z<-z+1;
    }
    x <- x + 1;
    return x;
  }

  proc optimised (x: int) : int = {
    x <- x + 1;
    return x;
  }
}.

lemma optimisation2_correct:
equiv [Compiler2.unoptimised ~ Compiler2.optimised:
      ={x} ==> ={res}  ].
proof.
admit.
qed.

(*
Now we define two more code blocks with similar deadcode,
except this time the variables y,z are not fixed like in
the previous code.
Prove that both these code blocks acheive the same result.
You could make progress by breaking the proof into
two parts, one in which the while loop is never 
executed, and another in which it is executed at least once.
After that you could put them together.
*)
module Compiler3 = {
  proc unoptimised (x y z: int) : int = {
    while(z<y){
      z<-z+1;
    }
    x <- x + 1;
    return x;
  }

  proc optimised (x: int) : int = {
    x <- x + 1;
    return x;
  }
}.

