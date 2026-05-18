require import AllCore.

(* A typeclass declared inside a section that survives section close *)
section.
  type class my_monoid = {
    op my_id : my_monoid
    op my_op : my_monoid -> my_monoid -> my_monoid

    axiom my_left_id : forall (x : my_monoid), my_op my_id x = x
  }.
end section.

(* Reference the typeclass after the section *)
op double ['a <: my_monoid] (x : 'a) = my_op x x.

lemma id_double ['a <: my_monoid] : double my_id<:'a> = my_id.
proof. rewrite /double my_left_id //. qed.
