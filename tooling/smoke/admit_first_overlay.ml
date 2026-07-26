(** Trivial [OVERLAY_KIND] smoke test. Replaces the first sentence of
    the input range with [admit.], keeping the rest unchanged. Exercises
    the OVERLAY_KIND shape without needing a real proof-block parser. *)

open Ecd_core

module O = struct
  let name = "admit-first"

  type config = unit

  let apply () = function
    | [] -> []
    | _first :: rest ->
        "admit." :: List.map (fun (s : Overlay.sentence) -> s.source) rest

  let compose () () = Ok ()
end

(* Verify at compile time that [O] satisfies [OVERLAY_KIND] without
   hiding the concrete [config] type from callers. *)
module _ : Overlay.OVERLAY_KIND = O
