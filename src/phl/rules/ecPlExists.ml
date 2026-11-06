(* -------------------------------------------------------------------- *)
open EcAst
open EcFol

open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
let prenex_exists ?(bound : int option) (pre : form) =
  try  destr_exists_prenex ?bound pre
  with DestrError _ -> ([], pre)

(* -------------------------------------------------------------------- *)
let intro_binders (fs : inv list) =
  let do1 (f : inv) =
    let id =
      match f with
      | Inv_ss f -> begin
          match f.inv.f_node with
          | Fpvar (pv, m) -> id_of_pv pv m
          | _             -> EcIdent.create "f"
        end
      | Inv_ts f -> begin
          match f.inv.f_node with
          | Fpvar (pv, m) -> id_of_pv ~mc:(f.ml, f.mr) pv m
          | _             -> EcIdent.create "f"
        end
      | Inv_hs _ -> assert false
    in (id, f)
  in List.map do1 fs

(* -------------------------------------------------------------------- *)
let intro_pre ~(ehoare : bool) (xs : (EcIdent.t * inv) list) (pre : inv) =
  let eqs =
    List.map
      (fun (x, f) -> map_inv1 (f_eq (f_local x (inv_of_inv f).f_ty)) f)
      xs in
  let bd = List.map (fun (x, f) -> (x, GTty (inv_of_inv f).f_ty)) xs in
  let eqs =
    match eqs with
    | [] -> map_inv1 (fun _ -> f_true) pre
    | _  -> map_inv f_ands eqs in
  if   ehoare
  then map_inv2 f_interp_ehoare_form (map_inv1 (f_exists bd) eqs) pre
  else map_inv1 (f_exists bd) (map_inv2 f_and eqs pre)
