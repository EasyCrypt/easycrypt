type t.

section.

theory A.
  local theory B.
    local op o1 : t.
    (* local with or without keyword because theory is local *)
    op o2 : t.
  end B.
  local op o1 : t.
  op o2 : t.
end A.

(* this makes all fields from [B] global again *)
global clone A.B as B'.

(* This clone inherits [local] and thus disappears at section end *)
clone A.B as FinalTheory.

end section.

(* [FinalTheory] was local so its name is available *)
theory FinalTheory.
  clone include A.

  (* idem for [o1] *)
  op o1 = o2.

  (* idem for B *)
  clone import B' as B with
          (* [o1] is visible *)
	  op o1 <= o2.
end FinalTheory.
