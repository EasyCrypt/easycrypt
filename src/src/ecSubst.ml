(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcTypesmod

(* -------------------------------------------------------------------- *)
type subst = {
  sb_modules : EcPath.path EcIdent.Mid.t;
}

type subst1 = [
  | `Module of EcIdent.t * EcPath.path
]

type mode = PModule

(* -------------------------------------------------------------------- *)
let identity = {
  sb_modules = EcIdent.Mid.empty;
}

(* -------------------------------------------------------------------- *)
let bind1 (s : subst) = function
  | `Module (x, p) ->
      {(* s with *)
          sb_modules = EcIdent.Mid.add x p s.sb_modules }

let extend (s : subst) (bindings : subst1 list) =
  List.fold_left bind1 s bindings

let create (bindings : subst1 list) =
  extend identity bindings

(* -------------------------------------------------------------------- *)
let rec inpath (mode : mode) (s : subst) (p : EcPath.path) =
  match p with
  | EcPath.Pident x -> begin
      match mode with
      | PModule -> odfl p (EcIdent.Mid.find_opt x s.sb_modules)
  end

  | EcPath.Pqname (p, x) -> EcPath.Pqname (inpath mode s p, x)

(* -------------------------------------------------------------------- *)
let rec intymod (s : subst) (tymod : tymod) =
  match tymod with
  | Tym_sig tysig ->
      Tym_sig (intysig s tysig)

  | Tym_functor (args, tyres) ->
    let fresh = List.map  (fun (x, _) -> EcIdent.fresh x) args in
    let news  = List.map2 (fun y (x, _) -> `Module (x, EcPath.Pident y)) fresh args
    and args  = List.map2 (fun x (_, a) -> (x, intymod s a)) fresh args in
    let tyres = intysig (extend s news) tyres in
      Tym_functor (args, tyres)

and intysig (s : subst) (tysig : tysig) =
  List.map (intysig1 s) tysig

and intysig1 (s : subst) (item : tysig_item) =
  match item with
  | Tys_variable (x, ty) -> Tys_variable (x, ty)
  | Tys_function fsig    -> Tys_function (infunsig s fsig)

and infunsig (s : subst) (fsig : funsig) = {
  fs_name = fsig.fs_name;
  fs_sig  = fsig.fs_sig;
  fs_uses = List.map (fun (p, m) -> (inpath PModule s p, m)) fsig.fs_uses;
}

(* -------------------------------------------------------------------- *)
module ModType = struct
  let apply (s : subst) (tymod : tymod) =
    intymod s tymod
end
