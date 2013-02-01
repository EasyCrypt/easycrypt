require Set.

import why3 "map" "Map"
   op "mixfix []" as "__get";
   op "mixfix [<-]" as "__set";
   op "const" as "empty".

op dom ['a 'b] : ('a,'b) map -> 'a Set.t.

op in_dom (x:'a, m:('a,'b) map) : bool = 
   Set.mem(x,dom(m)).

(* Add axiom ... *)
theory DomAxiom.
  axiom dom_empty : forall (dft:'b), dom(empty <:'a='a>(dft)) = Set.empty.
end DomAxiom.



