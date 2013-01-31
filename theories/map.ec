require import list.

theory Fmap.
  import why3 "map" "Map"
    op "mixfix []" as "__get";
    op "mixfix [<-]" as "__set";
    op "const" as "empty".

  op dom ['a 'b] : ('a,'b) map -> 'a list.

  op in_dom ['a 'b] : (('a,'b) map, 'a) -> bool.

  (* Add axiom ... *)
  theory DomAxiom.
    axiom dom_empty : forall (dft:'b), dom(empty <:'a='a>(dft)) = [].
  end DomAxiom.

end Fmap.

