(*^
  EasyCrypt_DocGen_Tutorial.ec

  To generate documentation for a source file, run the following command:
  {{
  <easycrypt-executable> docgen [-outdir <output-directory>] <source-file>
  }}
  Here, `<easycrypt-executable>` is the path to the EasyCrypt executable on your
  system, `<output-directory>` is the directory where the generated
  documentation files will be stored, and `<source-file>` is the path to the
  source file you want to generate documentation for. You may omit the output
  directory, in which case the tool defaults to the directory of the source file.

  This is a file documentation comment. In the generated documentation file, this
  comment appears at the top. File documentation comments are typically used for
  summaries, overviews, and meta-information about the file.
^*)

(*^
  This is an additional file-documentation comment. In the generated
  documentation, it is added as a paragraph below the (last paragraph of the)
  previous file documentation comment.
^*)

(*
  Regular, non-documentation comments like this one are excluded from the
  generated documentation file.
*)
require import FinType.

(*&
  This is a regular documentation comment, which is linked to the next
  "documentable" item. In the generated documentation file, it appears as
  documentation for the linked item.

  At the time of writing, the "documentable" items are:
  - types,
  - operators,
  - axioms,
  - lemmas,
  - module types,
  - modules, and
  - theories.

  Note that "scoped" items (those specified with, e.g., `local` or `declare`)
  are not "documentable", even if their "non-scoped" versions would be.

  This documentation comment is linked to `type t` below.
&*)
type t.

(*&
  It is not necessary to close a documentation comment with a matching closing
  delimiter. Only the opening delimiter determines the type of comment. However,
  it is good practice to use a matching closing delimiter.
*)
type u.

(*&
  Multiple documentation comments can be placed consecutively without any
  "documentable" items in between. All of these comments are linked to the next
  "documentable" item. However, starting with the second comment, each will be
  hidden under an un-foldable "details" section, indicated by a clickable arrow.
  Even if fewer than two documentation comments are linked to an item, this
  "details" section always contains the source code for the item, except in the
  case of (sub)theories.
&*)

(*&
  As an example, both the previous and this documentation comment are linked to
  `type v` below. The first comment is shown by default, while this second one
  is initially hidden, but can be revealed by unfolding the corresponding
  "details" section.
&*)
type v.

(*&
  Documentation comments can be interleaved with non-documentation comments,
  even before the item to which the documentation comments are linked.
&*)

(*
  This is a non-documentation comment between two documentation comments linked
  to the same item.
*)

(*&
  Both the previous and this __documentation__ comment are correctly linked to
  `type w` below, even though they are separated by a __non-documentation__
  comment.
&*)
type w.

(*^
  File documentation comments can be placed anywhere in the file. Each comment
  is added as a new paragraph below the previous one. However, it is
  considered good practice to place file documentation comments at the
  beginning of the file whenever possible.
^*)

(*&
  __Any__ comments nested inside documentation comments
  are excluded from the generated documentation file.
  (* This comment is excluded from the generated documentation file *)
  (*& This comment is excluded from the generated documentation file &*)
  (*^ This comment is excluded from the generated documentation file ^*)
  However, anything outside these nested comments (but within
  the documentation comment, of course) is included.
&*)
type x.

(*
  All "documentable" items are included in the generated documentation file, whether
  or not they have a corresponding documentation comment. The source code
  of each item is always included, though it is initially hidden under an
  un-foldable "details" section. If there is no corresponding documentation
  comment, a default message is shown, referring to the details section for the
  source code.
*)
type y.

(*&
 All documentation comments can be
 formatted using (a non-standard dialect of) Markdown.
 The following is supported.

 As first non-blank character on a line (followed by a space):
 - \! indicates a heading (one for largest heading, two for second-largest
 heading, etc.);
 - \*, \+, or \- indicate an item of an unordered list;
 - \# indicates an item of an ordered list; and
 - \> indicates (a line of) a blockquote.

 As delimiters:
 - \{\{ and \}\} delimit a code block (both the delimiters and content should be
 on separate lines);
 - \` delimits inline code (e.g., `inline code`);
 - \* delimits bold text (e.g., *bold text* ); and
 - \__ delimits emphasized text (e.g., __emph text__).

 Any special characters can be escaped with a backslash (e.g., \`).

 Hyperlinks are formatted as `[<link-text>](<link-target>)`
 (e.g., [EasyCrypt GitHub repository](https://github.com/EasyCrypt/easycrypt)).
&*)
type z.

(*&
  It is possible to link to other documented items *within
  the theory's scope* (i.e., items defined in the file itself or
  imported from other theories). The syntax is similar to
  that for hyperlinks: `[<link-text>](><item-kind>|<item-name>)`,
  Here, `<item-kind>` is one of the following:
  - `Ty` (or `Type`),
  - `Op` (or `Operator`),
  - `Ax` (or `Axiom`),
  - `Lem` (or `Lemma`),
  - `ModTy` (or `ModuleType`),
  - `Mod` (or `Module`), and
  - `Th` (or `Theory`).

  `<item-name>` is the name of the item as you would print it in the theory
  itself. Particularly, this means that the name may need to be qualified,
  depending on the imports in the theory. For example, `[go to type t above](>Ty|t)`
  becomes [go to type t above](>Ty|t). However, `[go to operator t below](>Op|t)`
  becomes [go to operator t below](>Op|t). (Note that, even though the linked
  type and operator are both referred to with the same name, the correct item is
  linked due to the specification of the item kind.)

  If you omit `<item-kind>`, the documentation tool checks each item kind in the
  order listed above for the given `<item-name>` and links to the first match.
  E.g., instead of `[go to type t above](>Ty|t)`, you can use `[go to type t
  above](>|t)` (proof: [go to type t above](>|t)). However, you still need
  to explicitly specify the `Op` kind for operator `t` below, because the
  documentation tool checks the `Type` kind before the `Operator` kind, which
  already results in a match.
&*)
op f : u -> v.

(*& This is a documented operator &*)
op t : v -> w.

(*&
  The generated documentation file contains a section for each item kind. Within each
  section, items are displayed in the order they appear in the source.
&*)
axiom ax : true.

(*&
  If there are no items of a certain kind,
  the generated documentation file does not contain a section for that kind.
  For example, the generated documentation file for this theory does not
  contain a section for module types.

  The navigation bar on the left-hand side of the generated documentation file
  shows only the sections that are present and provides links to them
  for convenience.
&*)
lemma lem : true.
proof. by trivial. qed.

(*&
  Currently, individual procedures inside of modules (and module types) cannot
  be documented using documentation comments. For the time being, a
  (unsatisfactory) workaround is to use regular comments within the module (or
  module type), which appear in the source code for the module (or module type)
  in the generated documentation file.
&*)
module M = {
  (*
    This regular comment appears in the source code
    for this module in the generated documentation file.
  *)
  proc p() : int = {
    return 1;
  }
}.

(*&
  Theories are special as "documentable" items. They appear as documented items
  in the generated documentation file for their parent theory __and__
  receive their own documentation file, in turn documenting all their
  "documentable" items. This file has a subheading indicating the subtheory and
  links to entry of the (sub)theory in the parent theory's documentation file.

  The file name for a (sub)theory follows this pattern: `Y!Z`, where `Y`, and
  `Z` represent the parent theory and (sub)theory, respectively. (This works
  recursively: `Y` may itself be a (sub)theory of another theory `X`, in which
  case the file name becomes `X!Y!Z`.)

  The "introductory text" for the (sub)theory, which you would usually put in
  file documentation comments, is drawn from the regular documentation comments
  in the parent theory. In the parent theory's documentation file, the
  (sub)theory's name links to the corresponding (sub)theory documentation file.

  No source code is shown for subtheories in the parent theory's documentation
  file.
&*)
theory T.

(*&
  This item is documented in the documentation file corresponding to
  (sub)theory `T'.
&*)
type s.

(*&
  Linking to items is done from the perspective of the outermost theory (`Top`),
  so names for items within (sub)theories that are not imported must be qualified.
  In other words, if a (sub)theory is not imported by the outermost theory,
  linking requires the item name to be qualified properly, even within the
  (sub)theory itself. For example, to link to `type s` above, something along
  the lines of `[go to s in T](>|s)` __does not__ work, but
  `[go to s in T](>|T.s)` __does__ (proof: [go to s in T](>|T.s)).
  However, if the (sub)theory would be imported at some point in the
  outermost theory, `[go to s in T](>|s)` __would work__, provided
  there are no naming collisions.
&*)
op a : s -> s.

(*&
  Linking to items in a parent theory works as expected. For example `[go to w
  in parent](>|w)` would create a link to the entry for `w` in the parent
  theory's documentation file (proof: [go to w in parent](>|w)).
&*)
op b : w -> w.

(*&
  The documentation mechanism for theories works recursively.
  For example, theory `U` below is treated in the documentation file for `T` in the
  same way that `T` is treated in the documentation file for the outermost theory.
  In addition to appearing in `T`'s documentation file, `U` also receives its own
  documentation file, similar to `T`, but now linking back to `T` rather than the
  outermost theory.
&*)
abstract theory U.

end U.

end T.


section.

(*
  As mentioned before, "scoped" items are never documented, even
  if their "non-scoped" version are.
*)
declare op lf : t -> t.

(*&
  If a documentation comment precedes (and would normally be linked to) an item
  that is "undocumentable" (e.g., due to its scope), the comment is discarded,
  effectively making it a regular, non-documentation comment.
&*)
local module M' = {

}.

(*&
  This operator is documented, but the previous documentation comment is
  not visible (indicating it has been dropped).
&*)
op foo = T.a.

end section.

(*&
  At present, similar to the previously discussed "scoped" items, clones are
  "undocumentable" items. As such, any preceding (would-be-linked) documentation
  comments are discarded, effectively making them regular, non-documentation
  comments.
&*)
clone FinType as FT with
  type t <- t.

(*&
  A documentation comment without any subsequent item is
  discarded, effectively making it a regular, non-documentation comment.
&*)
