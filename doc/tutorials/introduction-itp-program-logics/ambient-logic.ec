(* 
As we saw earlier in the abstract-ind-ror.ec file,
we use Emacs, and ProofGeneral to work with EasyCrypt.
We will need various commands/keybindings to work with Emacs.
All the keybindings begin either with the CONTROL key, denoted by "C",
or the META or ALT key denoted by "M".
So if you see "C-c C-n" it simply means: CONTROL + c and then CONTROL + n.
Go ahead, try it. This will evaluate the current comment, highlight it
to indicate that it has been evaluated and will place a small black dot on the
left margin at the beginning of the next block to be evaluated.
*)

(*
Most formal proofs are written interactively.
The proof-assistant, EC in our case, will keep track of the goals
(context, and conclusions) for us.
The front-end, Proof-General + Emacs in our case, will show us the 
goals and messages from the assistant, in the "goals" pane, and "response" pane 
on the right.
Our objective is to use different tactics to prove or "discharge" the goal.
Since we only have comments so far there are no goals for EC to work with.
We will change that in a short while.
*)
 
(*
Here is a short list of keystrokes that will come in handy for this file:
1. C-c C-n :  Evaluate next line or block of code 
2. C-c C-u :  Go back one line or block of code
3. C-c C-ENTER: Evaluate until the cursor position
4. C-c C-l: To reset the Proof-General layout
5. C-x C-s: Save file
6. C-x C-c: Exit Emacs (read the prompt at the bottom of the screen)
*)

(*
EC has a typed expression language, so everything we declare
should either explicitly have a type or it should be inferable
from the operators that are used.
To begin with let us import the built-in Integer theory file.
*)

require import Int.

(* The pragma line simply tells EC to print all goals *)
pragma Goals: printall.

(*
Now, let us start with something trivial to prove.
Let us start with the reflexivity of integers.
Reflexivity is simply the property that an integer is equal to itself.
Mathematically, we would write it like so:
For every integer x, x=x.
*)

(*
Here is how we declare something like that in EC.
C-c C-n multiple times to get EC to evaluate the lemma.
Or alternatively, move the cursor to the line with the lemma,
and hit C-c C-ENTER.
*)

lemma int_refl: forall (x: int), x = x.
(*
Notice how EC populates the goals pane on the right
with the context and the conclusion.
Keep stepping through the proof with C-c C-n.
*)
proof.
    trivial.
qed.

(*
We begin a formal proof with the tactic called "proof",
although it is optional to begin a proof with the "proof" keyword/tactic, 
it is considered good style to use it.

Then we use a set of tactics which transform the goal into zero or more subgoals.
In this case, we used the tactic "trivial", to prove our int_refl lemma.
Once there are no more goals, we can end the proof with "qed",
and EC saves the lemma for further use.
*)

(*
"trivial" tries to solve the goal using a mixture of other tactics.
So it can be hard to understand when to apply it, but the good news
is that trivial never fails. It either solves the goals or leaves the goal
unchanged. So you can always try it without harm.
*)

print int_refl.

(*
The "print" command prints out the request in the response pane.
We can print types, modules, operations, lemmas etc using the print keyword.
Here are some examples:
*)

print op (+).
print op min.
print axiom Int.fold0.

(* 
The keywords simply act as qualifiers and filters. 
You can print even without those. 
Like so:
*)
print (+).
print min.

(*
Now EC knows the lemma int_refl, and allows us to use it to prove other lemmas.
Although the next lemma is trivial, it illustrates the idea of this applying 
known results.
*)

print Int.

lemma forty_two_equal: 42 = 42.
proof.
   apply int_refl.
qed.

(*
"apply" tries to match the conclusion of what we are applying (the proof term), 
with the goal's conclusion. If there is a match, it replaces the goal
with the subgoals of the proof term.
In our case, EC matches int_refl to the goal's conclusion, sees that it
matches, and replaces the goal with what needs to be proven for int_relf which is
nothing, and it concludes the proof.
*)

(* 
EC comes with a lot of predefined lemmas and axioms that we can use.
Let us now look at axioms about commutativity and associativity for integers.
They are by the names addzC, and addzA. Print them out as an exercise.
*)


(* Simplifying goals *)

(*
In the proofs, sometimes tactics yield us something that can be simplified
We use the tactic "simplify", in order to carry out the simplification.

The simplify tactic reduces the goal to a normal form using lambda calculus.
We don't need to worry about the specifics of how, but it is important to
understand that EC can simplify the goals given it knows how to.
It will leave the goal unchanged if the goal is already in the normal form.

For instance, here is a contrived example that illustrates the idea.
We will get to more meaningful examples later, but going through these
simple examples will make writing complex proofs easier.
*)

(* Commutativity *)
lemma x_plus_comm (x: int): x + 2*3 = 6 + x.
proof.
    simplify.
    (* EC does the mathematical computation for us and simplifies the goal *)
    simplify.
    (* simplify doesn't fail, and leaves the goal unchanged *)
    trivial.
    (* trivial doesn't fail either, and leaves the goal unchanged *)
    apply addzC.
qed.

(* ---- Exercise ---- *)
(* 
"admit" is a tactic that closes the current goal by admitting it.
Replace admit in the following lemma and prove it using the earlier tactics.
*)
lemma x_minus_equal (x: int): x - 10 = x - 9 - 1.
proof.
admit.
qed.

(*
The goal list in EC is an ordered one, and you have to prove them
in the same order as EC lists it. "admit" can be used to bypass a certain 
goal and focus on something else in the goal list.
*)

(*
Use the tactic "split" to split the disjunction into two
and apply the previous axioms to discharge the goals.
Experiment with admiting the first goal after splitting
*)
lemma int_assoc_comm (x y z: int): x + (y + z) = (x + y) + z /\ x + y = y + x.
proof.
admit.
qed.

(*
To deal with disjunctions in EC, you can use the tactics "left" or "right"
to step into a proof of the left proof term, or the right proof term respectively.
*)

(* Searching in EC *)

(*
Since, there is a lot that is already done in EC,
we need a way to look for things. 
We do that using the "search" command. It prints out all axioms and lemmas 
involving the list of operators that give it.
*)

search [-].
(* [] - Square braces for unary operators  *)

search (+).

(*
As you can see the list can be quite overwhelming and difficult to navigate.
So we can limit the results using a list of operators, or patterns.
*)

search ( * ).
(*
() - Parentheses for binary operators. 
Notice the extra space for the "*" operator.
We need that since (* *) also indicates comments.
*)

search (+) (=) (=>).
(* List of operators "=>" is the implication symbol *)

search min.
(* By just the name of the operators. *)

(*---- Exercises ----*)

(* Distributivity *)
(* Search for the appropriate axiom and apply it to discharge this goal. *)
lemma int_distr (x y z: int): (x + y) * z = x * z + y * z.
proof.
    admit.
qed.

(*
So far, we saw lemmas without any assumptions 
except for that of the type of the variable in question.
More often than not we will have assumptions regarding variables.
We need to treat these assumptions as a given and introduce them into the context.
This is done by using "move => ..." followed by the name you want to give
the assumption.
*)

lemma x_pos (x: int): 0 < x => 0 < x+1.
proof.
    move => x_ge0.
    simplify.
    trivial.
    (* Both of those tactics don't work. We need something else here *)
    (* Let us see if EC has something that we can use. *)
    search (<) (+) (0) (=>).
    rewrite addz_gt0.
    (*
    "rewrite" simply rewrites the pattern provided, so in our case it
    rewrites our goal here (0 < x + 1), with the pattern that we provided
    which is addz_gt0, and then requires us to prove the assumptions of
    the pattern which are 0 < x and 0 < 1.
    *)
        (* Goal 1: 0 < x *)

        (*
        When we have a goal matches an assumption, we 
        can use the tactic assumption to discharge it.
        *)
        assumption.

        (* Goal 2: 0 < 1 *)
        trivial.
qed.

(* Let us see some variations *)

lemma int_assoc_rev (x y z: int): x + y + z = x + (y + z).
proof.
    print addzA.
    (* 
    We might have a lemma or an axiom that we can apply to the goal,
    but the LHS and RHS might be flipped, and EC will complain that
    they don't match to apply them.
    To rewrite a lemma or axiom in reverse, we simply add the "-" infront
    of the lemma to switch the sides like so.
    *)
    rewrite -addzA.
    trivial.
qed.

(*
Note that here "apply addzA." or "apply -addzA" do not work
We encourage you to try them.
*)

(*
Recap:
So far we have seen the following tactics:
trivial, simplify, apply, rewrite,
move, split, left, right, admit, and assumption.
We also saw how to print and search for patterns.
These are at the foundation of how we work with EC.
*)

(*
Intro to smt and external provers:
An important point to understand, however, is that EC
was built to work with cryptographic properties and more complex things.
So although other mathematical theorems and claims can be proven in EC,
it will be quite painful to do so. We will employ powerful automated tools
to take care of some of these low-level tactics and logic.
EC offers this in the form of the "smt" tactic.
When we run smt, EC sends the conclusion and the context to external smt solvers.
If they are able to solve the goal, then EC completes the proof.
If not smt fails and the burden of the proof is still on us.
*)

lemma x_pos_smt (x: int): 0 < x => 0 < x+1.
proof.
smt.
qed.

(*
As you can see, smt can make our lives much easier.
Now, here are some properties about logarithms that are mentioned in 
The Joy of Cryptography. We leave them to be completed as exercises,
without using the smt tactic. Most of them are straightforward and
serve the purpose of exercising the use of basic tactics.
*)

require import AllCore.


(* print AllCore to see what it includes *)

(* Logs and exponents: *)

lemma exp_product (x: real) (a b: int): x^(a*b) = x ^ a ^ b.
proof.
    search (^) (=).
    by apply RField.exprM.
qed.

lemma exp_product2 (x: real) (a b: int): x <> 0%r => x^a * x^b = x^(a + b).
proof.
    move => x_pos.
    search (^) (=).
    print  RField.exprD.
    rewrite -RField.exprD.
    assumption.
    trivial.
qed.

(* Logarithm exercises *)
require import RealExp.

(*
Print and search for "ln" to see how it is defined and
the results we have available already 
*)
lemma ln_product (x y: real) : 0%r < x  => 0%r < y => ln (x*y) = ln x + ln y.
proof.
    search (ln) (+).
    move => H1 H2.
    by apply lnM.
qed.

print log.
(*
Notice how log is defined. It is defined as an operator that expects two inputs
Since most of ECs axioms are written for natural logs (ln), inorder to reason with
log and inorder to work with the next lemma, you will need to rewrite log.
To do so the syntax is

rewrite /log.

The "/" will rewrite the pattern that follows.
*)

(*
This helper can come in handy in the next proof.
Sometimes it can be cumbersome to reason with a goal.
In cases like those, it is useful to reduce the complexity of the proof by using
helper lemmas like these.
*)

lemma helper (x y z: real): (x + y) / z = x/z + y/z.
proof.
smt.
qed.

lemma log_product (x y a : real):
    0%r < x  => 0%r < y => log a (x*y) = log a x + log a y.
proof.
    move => H1 H2.
    rewrite /log.
    rewrite lnM.
    assumption.
    assumption.
    by apply helper.
qed.

(* Or we can simply let smt do the heavy lifting for us *)
lemma log_product_smt (x y a : real):
    0%r < x  => 0%r < y => log a (x*y) = log a x + log a y.
proof.
    smt.
qed.

(*
Modulo arithmatic exercises:
This is one of the properties that is mentioned in the
 *)
require import IntDiv.

lemma mod_add (x y z: int): (x %% z + y %% z) %% z = (x + y) %% z.
proof.
    by apply modzDm.
qed.

(* 
A couple of more keystrokes that might be useful.

1. C-c C-r: Begin evaluating from the start
2. C-c C-b: Evaluate until the end of the file.

Go ahead and give these a try.
*)
