pragma Goals: printall.

require import AllCore.

(*
Let us start small and first work with some examples that we saw in the text.
Please pay attention to the syntax of the modules, and capitalization of names.
EasyCrypt (EC) expects the first letters of module names,
and module type names to be capitalized.
*)

module Func1 = {
  proc add_1 (x:int) : int = { return x+1; }

  (* 
     proc stands for procedure.
     Since EC is typed, we are required to mention the 
     return type of procedures in the definition.
  *)

  proc add_2 (x: int) : int = { x<- x + 2; return x; }
}.

(*
EC allows us to define concretely defined procedures like we did above.
But since we want to model adversaries about whom we know nothing,
we can also define abstract procedures like an eavesdrop procedure.
of an adversary. Like so: 
*)
module type Adv = {
  proc eavesdrop () : bool
}.

(*
We don't know what the procedure does, but we do know its return type.
Also notice that now we have a module type and not just a module.
This is because Adv is a type that we will need to instantiate.
We had similar ideas in the abstract-ind-ror.ec
Where the Adversary module type had a "guess" procedure.
We will return to this later when we start working with cryptographic protocols.
But this is an important fact that we need to keep in mind.
*)

(* 
Let us return to hoare triples and take a look at some triples and
try to prove them in EC.
A triple denoted by {P} C {Q} in theory is expressed as
hoare [C : P ==> Q ] in EC, with the usual definitions.
Additionally, the return value of the program C, is stored in a special 
keyword called res.
*)

lemma triple1: hoare [ Func1.add_1 : x = 1 ==> res = 2].
proof.
(*
When working with hoare logic, or its variants, the goal will be different from
what a goal in ambient logic looks like. We need to start stepping through
the procedure or program that is being reasoned about and change the
preconditions and postconditions according to the axioms and lemmas that we have.
To make progress here, we first need to tell EC what Func1.add_1 is.
The way to do that is by using the "proc" tactic.
It simply fills in the definitions of the procedures that we define.
*)
  proc.

(*
When the goal’s conclusion is a statement judgement whose program is empty,
like we have now the "skip" tactic reduces it to the goal whose conclusion
is the ambient logic formula P => Q,
where P is the original conclusion’s precondition, 
and Q is its postcondition.

Visually, skip works in the following way:

       P => Q
  ----------------- skip
     {P}  skip;  {Q}

skip; denotes an empty program.
While skip next to the line is the tactic itself.
*)
  skip.

(*
Now we are back in familiar territory, except the fact that
we have an interesting "&hr" lurking in the goal.
This refers to the memory in which the program acts.
When we deal with multiple programs, there is a possibility
that the variables come from different memories. So EC provides us
different namespaces to deal with them.
To introduce memory into the context we need to prepend "&" to a variable name.
Like so:
*)
  move => &m H1.

  subst.
(* The "subst" tactic simply substitutes variables *)
  trivial.
qed.


lemma triple2: hoare [ Func1.add_2 : x = 1 ==> res = 3 ].
proof.
  proc.

(*
Now we have a program which is not empty,
so we can't use the "skip" tactic directly.
Thankfully we learnt about the different axioms in hoare logic.

When we are faced with 
{P} S1; S2; S3; {Q} (with the usual definitions)
applying the "wp" tactic consumes as many ordinary statements as possible from
the end. Then it replaces the postcondition Q, with the weakest precondition R.
R is such that R in conjunction with the consumed statements and the original 
post condition hold. It is easier to visualize this in a proof-tree.
For instance, when we have
{P} S1; S2; S3; {Q} and
S2; S3 are statements that can be dealt with some axioms or logical deductions,
then wp does the following:

                       -----------------(Other rules)
   {P} S1; {R}          {R} S2; S3; {Q}
  --------------------------------------seq
            {P} S1; S2; S3 {Q}

The triple {R} S2; S3; {Q} is guaranteed to hold, and
hence the goal transforms to
just {P} S1; {R}
*)

(*
Let us see what happens in our context.
The "wp" tactic consumes the only statement in the program.
In this case an assignment, and replaces the variable like we'd expect.
When we have an empty program, we can simply use the "skip" tactic
and continue with our proof. 

                x = 1 => x+2=3
       -------------------------------skip
              {x = 1} skip; {x+2=3}
       -------------------------------wp
             {x = 1} x:= x+2 {x=3}
*)

  wp.
  skip.
  move => &m x.
  subst.
  trivial.
qed.

(*
Let us define some more simple functions and hoare triples to work with.
*)
module Func2 = {
  proc x_sq (x:int) : int = { return x*x; }
  proc x_0  (x:int) : int = { x <- x*x; x<- x-x; return x; }
  proc x_15 (x:int) : int = { x <- 15; return x; }
}.

(*
Exercises:
Define a few triples relating the behaviour of these functions.
For instance try to define the following triples and prove them:
1. {x =  2} Func2.x_sq {res = 4}
2. {x = 10} Func2.x_0  {res = 0}
3. {true}   Func2.x_15 {res = 15}
*)

(* Using some automation *)

(*
We generally don't want to be dealing with the low-level proofs,
so we will be combining Hoare logic with the external solvers
that we saw earlier. One thing to remember is that the external
solvers work only with ambient logic goals.
So we need to get the goals state to something that the smt solvers
can work with.
*)

lemma triple3: hoare [ Func2.x_sq : 4 <= x ==> 16 <= res ].
proof.
proc.
skip.
move => &m H1.
(*
Here this conclusion is trivial for us to understand and prove on paper
however it can be quite hard to do with EC, so we will simply outsource it to smt.
The external provers are quite powerful, and can make our life easier.
*)
smt.
qed.

(*
Now let us look at the special cases that we had in the text.
Namely: {true} C {Q}, and {false} C {Q}.
*)
lemma triple4: hoare [ Func2.x_0 : true ==> res=0 ].
proof.
proc.
wp.
skip.
move => &m T x.
by simplify.
(* Prepending the "by" keyword to a tactic
tries to close the goals by applying trivial
to the result of the tactic, and fails if the goal can't be closed *)
qed.

(*
"by" is called a tactical. Tacticals are commands that can work with
other tactics. We will see more later.
*)

(*
So far so good, that was pretty much what we expected.
However let us take a look at the next lemma. Now we are looking at the triple:
{false} x:=15 {x = 0}.
This shouldn't hold, but watch what happens.
*)

lemma triple5: hoare [ Func2.x_15 : false ==> res=0 ].
proof.
proc.
wp.
skip.
move => _ f.

(*
The underscore essentially is a pattern for introduction 
which tells EC to ignore whatever is in that position.
Here since we have a "forall _" in the goal already, we tell EC to ignore it.
You could also use a "?", to let EC decide what to call the variable being moved
to the assumptions.
*)

(*
Pause here for a moment and ponder about what the goal currently says.
It says that assuming that "false" holds, we want to prove that 15 = 0.
As absurd as it is, we know that "false" is the strongest statement there is.
And we have arrived at a state where "false" holds.
This would imply that anything and everything can be derived from false.
Hence we can actually "prove" that 15 = 0.
*)
trivial.
qed.

(*
The point to understand here is that we could only do this 
because we moved "false" into the context manually when we used the "move" tactic.
So our math is still consistent and the world hasn't exploded yet.
The way to think about this triple is assuming "false" holds implies that 15 = 0.
*)


(*
Let us now work with some more interesting functions and triples.
The flipper function simply returns the opposite of the boolean
value that it gets.
*)

module Flip = {

proc flipper (x: bool) : bool = 
  {
  var r: bool;
  if (x = true) 
  { r <- false; }
  else
  { r <- true; }
  return r;
  }
}.

lemma flipper_correct_t: hoare [ Flip.flipper : x = true ==> res = false ].
proof.
  proc.
  (*
  When the first statement of the program is an if condition, we can use the
  "if" tactic to branch into two different goals with appropriate truth values for
  the if condition.
  In our case, the goal branches into x = true, and x <> true based, and these
  conditions are added to the preconditions.
  *)
  if.
    (*Goal 1:  x = true *)
    auto.
 
    (*
    If the current goal is a HL, pHL, pRHL statement the "auto" tactic
    uses various program logic tactics in an attempt to reduce the goal
    to a simpler one. It never fails, but may fail to make any progress.
    In this usage, it replaces "wp. skip. and trivial."
    *)

    (* Goal 2: x <> true.
    Yields a contradiction in the assumptions.
    Since our precondition states that x = true /\ x <> true
    We will use some automation to deal with it.
    *)
    auto.
    smt.
qed.

(*
Notice the repetition of proof steps in the branches.
This can be reduced by using tacticals.
In order to tell EC to repeatedly use certain tactics on all
resulting goals, we use the ";" tactical.
So, we can simplify the above proof like so:
*)

lemma flipper_correct_f: hoare [ Flip.flipper : x = false ==> res = true ].
proof.
  proc.
  if; auto; smt.
qed.

(*
However, since this program is quite simple we can actually make the proof
shorter. We can also make the logic more abstract like so. Please note how we do this,
since we will use it again.
*)

lemma flipper_correct (x0:bool):
  hoare [ Flip.flipper : x = x0  ==> res <> x0 ].
proof.
  proc.
  auto.
  smt.
qed.

(*
This is how proofs are polished and made shorter. We first write a verbose proof,
then keep experimenting to find shorter and more elegant proofs.
*)

(*
Let us define the exponentiation function that we saw in the text.
*)

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


(*
Let us formulate a hoare triple that says that exp(10, 2) = 100.
The triple would be:
{x = 10 /\ n=2} Exp.exp {res=100}
and in EC, we would write it like so.
*)

lemma ten_to_two: hoare [ Exp.exp : x = 10 /\ n = 2 ==> res = 100 ].
proof.
  proc.

(*
When working with tuples EC has the syntax of using backticks (`) to address the tuple.
So (x,n).`1 refers to x.
Often the output from EC can be quite hard to read, simplifying it can sometimes help.
*)
  simplify.

(*
Now we want to reason with a while loop in the program.
Thankfully, we can see that the loop only runs twice, since n=2.
To get a feel of how the program runs we can step through a loop
using the "unroll" tactic. We need to mention the line number of the
program where we want the tactic to apply. Like so:
*)
  unroll 3.
  unroll 4.

(*
At this point, we now have two if conditions which we know will hold,
and a while loop for which the condition will not hold. To reason with
loops and conditions like these EC provides two tactics
rcondt, and rcondf.
You can read them as: remove condition with a true/false assignment.
Since here we know that the condition will evaluate to false, we will use the
rcondf version.
*)

  rcondf 5.
(*
Notice how the postcondition now requires the condition for the while loop
to be false.
Since it would evaluate to false, EC gets rid of the loop.
Now we can either use the if tactic that we used earlier to work with the
if conditions here, but wp is generally strong enough to reason with if conditions.
So let us make our lives a little easier and use that instead.
Here, since the program is quite simple, the smt solvers can complete the proof.
However, pay attention to how hard it gets to read the output
after the application of wp, and skip.
*)
  wp.
  skip.
  smt.

(*
Goal #2:
Again, we have two "if" conditions, that we need to work with.
The proof proceeds the same way as before. wp is strong enough to reason with it.
*)

  wp.
  skip.
  smt.
qed.

(*
As usual we could have used some tacticals to shorten the proof.
So let us do that, to clean up the previous proof.
*)

lemma ten_to_two_clean: hoare [ Exp.exp : x = 10 /\ n = 2 ==> res = 100 ].
proof.
  proc.
  unroll 3.
  unroll 4.
  rcondf 5; auto.
qed.

(*
For a loop that unrolls twice it is easy to do it manually.
However, this strategy wouldn't work for a different scenario.
For instance in order to prove that the program works correctly we need to prove
the correctness for every number, so we would prefer to work with abstract symbols
and not concrete numbers like 10^2.
In order to work up to it, let us prove that 2^10 works as intended.
But first, we need to understand that EC was not built for computations.
It can handle small calculations like we've seen so far but asking EC to do 2^10
doesn't work as we'd like it to.
For instance, take a look at the following lemma, and our attempt to prove it.
*)

lemma twototen: 2^10 = 1024.
proof.
  trivial.
  simplify.
  auto.
(*
None of those tactics do anything 
Even smt doesn't work.
You can try it as well.
Again, the point here is that, these kinds of tasks aren't what EC was
built for.
For the time being we will admit this lemma, since we know that
2^10 is in fact 1024.
We need this to prove the next few lemmas relating to hoare triples.
*)
  admit.
qed.

lemma two_to_ten: hoare [ Exp.exp : x = 2 /\ n = 10 ==> res = 1024 ].
proof.
  proc.
  simplify.
(* 
To get rid of the loop, we need to understand the behavior of the program, and 
figure out a loop invariant. This is because we have the tactic:
"while I"
Where "I" is the loop invariant, that holds before and after the loop. 
This essentially means thinking about what the loop actually does,
and the conditions that hold before and after the execution of the loop.
We want the invariant to help us prove the goal that we have.
Which is r = 1024. Let us try to see how we can get there.
Let us start small and say that we know that (x = 2) holds before
and after the execution of the loop.
*)
  while ( x = 2 ).
(*
Observe how the goals have changed.
In Goal #1, the invariant that we propose is in both the pre and post conditions.
The burden of the proof still lies on us however. Of course, since we don't
change x, this should hold quite naturally. And we can discharge Goal #1 quite
easily.
*)
  wp.
  auto.

(*
Now let us pay attention to what we have left.
The second part of the postcondition says 
forall (i0, r0 : int),
given that i0 is greater than or equal to n, and x = 2
then r0 = 1024. 
That is clearly incorrect, since r0 isn't bound or related to x or i0.
You are welcome to experiment and try to see how far you can get in
the proof. However in our attempt, the goal simply becomes harder to read.
Using wp, and skip introduces memory into the context making it quite difficult to
read. We will "abort" this attempt here, and try to think of a stronger invariant.
*)
abort.

lemma two_to_ten: hoare [ Exp.exp : x = 2 /\ n = 10 ==> res = 1024 ].
proof.
  proc.

(*
As an additional invariant, we know that the loop runs until our
loop variable i goes from 0, to n. So as an invariant, we have
0 <= i <= n, and the control exits the loop when ! (i < n).
Let us try to see what happens if we add this in.
*)
  while ( x = 2  /\ 0 <= i <= n).
  wp.
  auto.
  smt.

(*
Let us read what the goal says now.
Again it says something about r0 without bounding what r0 can be.
This attempt will also fail.
So we need to understand what happens to the variable r0, at the end of every
iteration of the loop.
*)
abort.


lemma two_to_ten: hoare [ Exp.exp : x = 2 /\ n = 10 ==> res = 1024 ].
proof.
  proc.
(*
We know that after every iteration, the variable r is multiplied by x.
So in this case, since we have x = 2, essentially at the end of
i iterations of the loop we have the fact that r = 2^i.
This is an invariant, and it binds r to the variables that are passed to the
loop. Let us see if this attempt works.
*)
  while (x = 2  /\ 0 <= i <= n /\  r = 2^i).

(*
Again, Goal #1 will go through quite easily.
*)
  wp.
  skip.
  smt.

(* Goal #2 *)
  wp.
  simplify.
  auto.
(*
When the goal is too complicated to read, we can apply the tactic "progress".
"progress" breaks the goals into simpler ones by repeatedly applying the
"split", "subst" and "move =>" tactics and trying to solve trivial goals automatically.
*)
  progress.

(* 2 ^ 0 = 1 *)
  smt.

(* 2^10 = 1024 *)
  smt.
qed.

(*
A point to note here:
Had we not admitted the lemma twototen the proof would get stuck
You are welcome to comment it out and try the proof again.
*)

(*
So finally, we have an invariant that works.
Let us clean up the proof, and also if we think about it,
the condition (x=2) isn't really needed, since the program never
modifies the value of x. So let us get rid of that condition as well.
*)

lemma two_to_ten_clean: hoare [ Exp.exp : x = 2 /\ n = 10 ==> res = 1024 ].
proof.
  proc.
  simplify.
  while ( r = x^i /\ 0 <= i <= n); auto; smt.
qed.

(*
Now the proof seems so innocuous and straightforward.
However, it is important to understand that these proofs and
figuring out the loop invariants always take a few tries, and
sometimes crafting the right invariant can be an art by itself.
This also gets quite hard when there are a lot of variables
to keep track of. So it is good practice to work with smaller examples first.
*)


(*
Now let us try to work with abstract symbols, the stuff that EC
was actually built for. Here we mentioned in the text, in order to claim
that the exp function is correct, we need to have the condition that
the exponent that we provide is greater than zero.
We use x0, and n0, in order to differentiate from the program variables.
*)
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


(*
Again, we can clean up the proof like so:
Notice that we omit the type declaration of x0 and n0,
since EasyCrypt can figure it out by itself.
*)
lemma x0_to_n0_correct_clean x0 n0: 
  0 <= n0 =>
  hoare [ Exp.exp : x = x0 /\ n = n0 ==> res = x0 ^ n0 ].
proof.
  move => Hn0.
  proc.
  while (r=x^i /\ 0 <= i <= n); auto; smt.
qed.

(*
As an exercise, you can do similar proofs for the following mathematical functions:
1. A program to decide if a given number is even or odd.
2. A program to compute the factorial of a given number.
*)
