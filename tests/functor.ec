require import Int.
module type O = {
  proc o (x:int) : int
}.


module type IA (O1:O, O2:O) = {
  proc a1 (x:int, y:int) : int { O1.o }
  proc a2 (x:int) : int { O1.o O2.o }
}.

(*
module G(FA:IA, O1 : O, O2 : O) = {
  module A = FA(O1,O1) (* BUG : should not be accepted, FA(O1) can not be apply to O1 because they share memory *)
}.
*)

module H = { 
  var w : int 
}.

module O1 : O = { 
  proc o (x:int) : int = { return H.w; }
}.

module O2 : O = { 
  proc o (x:int) : int = { return H.w; }
}.

module type FOO = {
  proc f (x:int) : int { O1.o } (* Should not be accepted ? *)
}.


module G(FA:IA, O1 : O, O2 : O) = {
  module A = FA(O1,O2) 
}.

module H1 = {
 proc id (x:int) : int = { return x; }
}.

axiom foo : equiv [ H1.id ~ H1.id : true ==> true] .

module GG (FA:IA) = {
  module F = G(FA,O1,O2) (* BUG : O1, O2 share H.w *)
}.

axiom foo1 : forall (FA<:IA) (O1<:O) (O2<:O), 
   equiv [ G(FA,O1,O2).A.a1 ~ G(FA,O1,O2).A.a1 : true ==> true].





