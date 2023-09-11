EasyCrypt Documentation Tool (Based on rustdoc)
-----------------------------------------------------------------
- Two types of documentation comments: 
  * File documentation comment.
    Documents the complete file.
    Opened with (*^ and closed with ^*).
    Good practice would be to have exactly one file comment at the beginning of each file.
    Everything before the first blank line in the comment is displayed in search/print results containing that item.
    Complete comment is displayed in generated HTML output.	 
  * Item documentation comment.
    Documents the directly succeeding item (theory, section, module, procedure, type, operator, axiom, lemma).
    Opened with (** and closed with **)
    Must be followed by an item.
    Good practice would be to have an item comment for each item (excluding perhaps auxiliary items, e.g., certain "local" items inside sections).
    Everything before the first blank line in the comment is displayed in search/print results containing that item.
    Complete comment is displayed in generated HTML output.

- (Part of) Github Flavored Markdown (GFM) as doc comment language. See https://github.github.com/gfm/.

- Documentation comments allow for including links to items within scope by means of [`item`], where "item" denotes the (unique) identifier of the item.

- By default, all items (except "local" items inside sections) are included in the generated HTML output, even if they do not have an associated item documentation comment.
  To exclude an item that is included by default, tag it with ???; this will additionally exclude all encapsulated items, if any (e.g., if you exclude a module, the procedures of the module will also be excluded).
  To include an item that is excluded by default, tag it with ???; this will additionally include all encapsulated items, if any (e.g., if you include a local module, the procedures of the local module will also be included).

- The generated HTML output has the following section structure:
  * Title/introduction
    Contains the contents of the file documentation comment.
  * Dependencies
    Lists/links all of the required files (i.e., each library imported via 'require').
  * Types
    Lists/links each top-level type together with the content in the corresponding item documentation comment that occurs before the first blank line.
    Each identifier is a link to a page that shows the full content of the corresponding item documentation comment.
  * Operators
    Lists/links each top-level operator together with the content in the corresponding item documentation comment that occurs before the first blank line.
    Each identifier is a link to a page that shows the full content of the corresponding item documentation comment.
  * Modules
    Lists/links each top-level type together with the content in the corresponding item documentation comment that occurs before the first blank line.
    Each item is a link to a page that is structured as follows:
    > Title/introdcution
      Contains the  full content of the corresponding item documentation comment.
    > Variables
      Lists/links each of the module's variables together with the content in the corresponding item documentation comment that occurs before the first blank line.
      Each identifier is a link to a page that shows the full content of the corresponding item documentation comment.
    > Procedures
      Lists/links each of the module's procedures together with the content in the corresponding item documentation comment that occurs before the first blank line.
      Each identifier is a link to a page that shows the full content of the corresponding item documentation comment.
  * Axioms/Lemmas
    Lists/links each top-level axiom/lemma together with the content in the corresponding item documentation comment that occurs before the first blank line.
    Each identifier is a link to a page that shows the full content of the corresponding item documentation comment.
  * Theories
    Lists/links each top-level theory together with the content in the corresponding item documentation comment that occurs before the first blank line.
    Each identifier is a link to a page that is structured identically to the top-level page of a file, except that the first section shows the full content of the corresponding item documentation comment instead of the file documentation comment.
  * Sections
    Lists/links each top-level theory together with the content in the corresponding item documentation comment that occurs before the first blank line.
    Each identifier is a link to a page that is structured identically to the top-level page of a file, except that the first section shows the full content of the corresponding item documentation comment instead of the file documentation comment.
  
  
      
