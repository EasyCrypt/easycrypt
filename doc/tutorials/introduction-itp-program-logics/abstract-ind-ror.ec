(* 
Welcome to ProofGeneral, the front-end that we use to
work with EasyCrypt. ProofGeneral runs on top of Emacs,
so most of keybindings of Emacs work as expected.

In this file, we go through an illustrative example of
modelling an IND-RoR game with EasyCrypt.

To interactively evaluate the script, you can either use the
toolbar at the top or use the following keybindings:
1. ctrl + c and then ctrl + n to evaluate one line/block of code (Next)
2. ctrl + c and then ctrl + u to undo evaluation of one line/block of code (Undo)
3. ctrl + x ctrl + s to save the file
4. ctrl + x ctrl + c to exit Emacs

We will look at more keybindings in the next file.
Evaluting the first line will split the interface to show three panes.

1. EasyCrypt script pane (left pane)
2. Goals pane (top right)
3. Response pane (bottom right)

Keep evaluating until the end of the file
and see how things change.
*)

(* We first import some core theory files *)
require import Real Bool DBool.

(* We define abstract data-types and operations *)
type msg.
type cip.

(* Encrypt and decrypt operations. *)
op enc: msg -> cip.
op dec: cip -> msg.

(* Compute operations for the adversary. *)
op comp: cip -> bool.

(*
Next we define the module types.
These are blueprints for concrete types
that we instantiate right after we define them.
*)

module type Challenger = {
  proc encrypt(m:msg): cip
  proc decrypt(c:cip): msg
}.

module C:Challenger = {

 proc encrypt(m:msg): cip = {
    return enc(m);
 }

 proc decrypt(c:cip): msg = {
   return dec(c);
 }
}.

(* Similarly we define an adversary. *)
module type Adversary = {
  proc guess(c:cip): bool
}.
(* and an instance of the same. *)
module Adv:Adversary = {

  proc guess(c:cip): bool = {
    return comp(c);
  }
}.

(* The game module and the claims related to it. *)
module Game(C:Challenger, Adv:Adversary) = {
  
  proc ind_ror(): bool = {
      var m:msg;
      var c:cip;
      var b,b_adv:bool;
      b <$ {0,1}; (* Pick b uniformly at random. *)
      if(b=true){
        (* Set m to be an authentic message. *)
      } else {
        (* Set m to be a random string. *)
      }
      c <@ C.encrypt(m);
      b_adv <@ Adv.guess(c);
      return (b_adv=b);
  }
}.

(*
At this point EasyCrypt will throw a warning
complaining about how there may be an uninitialized
variable. This happens because in our current
program definition, we haven't initialized
"m" to anything.
We skim past this warning, since this example
is only to illustrate the structure of EasyCrypt scripts.
Go ahead and keep evaluating the script.
Make sure to undo some evaluations as well,
just to get the keystrokes into your muscle memory.
*)

axiom ind_ror_pr_le1:
phoare [Game(C,Adv).ind_ror: true ==> res] <= 1%r.

lemma ind_ror_secure:
phoare [Game(C,Adv).ind_ror: true ==> res] <= (1%r/2%r).
(* Notice the changes in the goals pane *)
proof.
  admit.
qed.
