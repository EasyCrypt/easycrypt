(* -------------------------------------------------------------------- *)
open EcTypes
open EcModules
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the identity assignment, resolved: the position is a
   normalized (possibly nested) code position, the variable a typed
   program variable. *)
type tr_idassign = {
  tria_at : EcMatching.Position.nm_codepos;
  tria_pv : prog_var * ty;
}

type EcPlTransform.transform += TrIdAssign of tr_idassign

(* -------------------------------------------------------------------- *)
(* Insert [x <- x], [x] being a variable of the memory when local. *)
let idassign (p : tr_idassign) (ctxt : tr_ctxt) (s : stmt) =
  let (pv, ty) = p.tria_pv in

  begin match pv with
  | PVloc x ->
      let bound =
        match EcMemory.lookup_me x ctxt.trc_me with
        | Some (v, _, _) -> ty_equal v.v_type ty
        | None -> false in
      if not bound then
        raise (InvalidTransform "invalid program variable")
  | PVglob _ -> ()
  end;

  let zpr =
    try  Zpr.zipper_of_nm_cpos p.tria_at s
    with EcMatching.Position.InvalidCPos ->
      raise (InvalidTransform "invalid code position") in

  let i = i_asgn (LvVar (pv, ty), e_var pv ty) in

  { trr_me  = ctxt.trc_me;
    trr_s   = Zpr.zip { zpr with Zpr.z_tail = i :: zpr.Zpr.z_tail; };
    trr_obl = []; }

let () =
  register (function
    | TrIdAssign p -> Some (idassign p)
    | _ -> None)
