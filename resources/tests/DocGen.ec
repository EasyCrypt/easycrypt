(*^ 
  This file is used for demonstrating 
  the documentation generation tooling.
  To generate the documentation file for an EC source file, issue command:
  `easycrypt compile -doc [filename]`
  Here, [filename] is a placeholder for the name of the EC source file.
^*)
(*^
  "File documentation comments" are delimited like this comment
  (whitespace/newlines not necessary) and cannot be nested. 
  These comments are not linked to any specific
  entity within the file, and are used to for the introduction
  in the generated documentation file.
^*)
(*^
  Each file documentation comment will be its own paragraph in the
  generated documentation file. Naturally, these paragraphs are in the same
  order as the corresponding file documentation comments in the source file.  
^*)

(** 
  "Item documentation comments" are linked to the next entity in the source file;
  these comments are delimited like this comment (whitespace/newlines not necessary)
  and, at the time of writing, cannot be nested.  
  Currenlty, the following are considered entities:
  Types, operators, axioms, lemmmas, module types, modules, and theories.
  Furthermore, only entities with a global scope are considered, i.e.,
  "local" or "declare" entitites are not documented.
  Indeed, this means that in the generated documentation file,
  this comment will be used as documentation for type foo (see below).
**)
(**
  As file documentation comments, item documentation comments can be chained; i.e., all
  item documentation comments before entity A (but after any other entity) 
  will be linked to entity B. In the generated documentation file, the
  first linked item documentation comment is always displayed; the subsequent
  item documentation comments are collapsed by default (but can be expanded,
  which, for all entities besides theories, will also show the source code) 
**)
(* 
  Any regular (non-documentation) comment between the last item documentation comment
  and the corresponding entity will be considered part of the source code for that
  entity (and documented as such). This also goes for regular comments inside
  the definition of the entity (e.g., comments inside modules/module types) 
*)
type foo.


(*^ 
  Note that file documentation comments do not necessarily need to be written
  in the beginning of the source file: This comment will become the final paragraph
  of the introduction in the generated documenation file.
^*)

(* 
  Non-documentation comments, like this one, will not be shown in the 
  generated documentation file.
*)

(* The following is a basic example *)
(* BEGIN BASIC EXAMPLE *)
(** Inputs **)
type X.

(** Outputs **)
type Y.

(** Function mapping inputs to outputs **)
op f : X -> Y.

(** Module formalizing/wrapping f **)
module F = {
  (* This is the actual procedure that computes f *)
  proc map(x : X) : Y = {
    return f x;
  }
}.

(** Module type for functions from inputs to outputs **)
module type Function = {
  (* Procedure computing the function *)
  proc map(x : X) : Y
}.

(** Another module formalizing/wrapping f **)
(** This time, it is explicitly typed **)
module F' : Function = {
  proc map(x : X) : Y = {
    return f x;
  }
}.

(** An axiom on the behavior of f **)
axiom f_behavior x : f x = witness.

(** Lemma on F following from axiom on f **)
lemma F_result_inv :
  hoare [F.map : true ==> res = witness].
proof.
proc.
skip.
move=> &hr _.
by apply f_behavior.
qed.
(* END BASIC EXAMPLE *)


(** 
  Unlike the more basic entities considered above, theories receive a
  dedicated documentation file. In the original generated documentation
  file (of the EC source file containing the theory), the theory
  is documented with its associated item documentation comments in the same
  way as other entities are, but instead of showing source code, it links to the
  dedicated documentation file.
**)
(**
  In the dedicated documentation file of a theory, the linked item documentation comments
  are used for the introduction (effectively turning these item documentation comments
  into file documentation comments for this dedicated documentation file).
**)
theory Foo.

(**
  The above mechanism works recursively, so for nested theories, 
  we treat the encompassing theory as if it was its own file. 
  In this case, this means that Bar will receive its own dedicated
  documentation file, which is linked to in the documentation file for Foo
  (where Bar shows up as a regular documented entity).
**)
abstract theory Bar.

end Bar.

end Foo.


(* Reminder: Sections are not entities. *)
section.

(** 
  Although, implicilty, documentation comments are still linked to 
  declared entities, they are currently discarded as soon as the entity
  is processed (this may change in the future).
**)
declare op g : X -> Y. 

(** 
  Similarly for local entities.
**)
local op h : Y -> X. 

(** 
  However, global (i.e., non-local, non-declared) entities 
  inside a section are still documented.
**)
lemma foobar : true.
proof.
trivial.
qed.

end section.
