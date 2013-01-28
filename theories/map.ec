theory Fmap.
  import why3 "map" "Map"
    op "mixfix []" as "__get";
    op "mixfix [<-]" as "__set";
    op "const" as "empty".

  op dom ['a 'b] : ('a,'b) map -> 'a list.

  op in_dom ['a 'b] : (('a,'b) map, 'a) -> bool.

  (* Add axiom ... *)
  theory DomAxiom.
    axiom dom_empty : forall (x:a'), 
  end DomAxiom.

end Fmap.

