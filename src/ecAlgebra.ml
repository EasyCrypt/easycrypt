(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcPath
open EcTypes
open EcFol
open EcRing
open EcField

(* -------------------------------------------------------------------- *)
module RState : sig
  type rstate

  val empty   : rstate
  val add     : form -> rstate -> int * rstate
  val get     : int -> rstate -> form option
  val current : rstate -> int
end = struct
  type rstate = {
    rst_map : int Mf.t;
    rst_inv : form Mint.t;
    rst_idx : int;
  }

  let empty = { rst_map = Mf.empty; rst_inv = Mint.empty; rst_idx = 0; }

  let add (form : form) (rmap : rstate) =
    match Mf.find_opt form rmap.rst_map with
    | Some i -> (i, rmap)
    | None ->
       let i = rmap.rst_idx+1 in
       let m = Mf  .add form i rmap.rst_map in
       let v = Mint.add i form rmap.rst_inv in
         (i, { rst_map = m; rst_inv = v; rst_idx = i; })

  let current (rmap : rstate) =
    rmap.rst_idx

  let get (i : int) (rmap : rstate) =
    Mint.find_opt i rmap.rst_inv
end

(* -------------------------------------------------------------------- *)
type ring = {
  r_type   : EcTypes.ty;
  r_zero   : path;
  r_one    : path;
  r_add    : path;
  r_opp    : path;
  r_mul    : path;
  r_exp    : path;
  r_sub    : path option;
  r_intmul : [`Embed | `IntMul of path];
}

type field = {
  f_ring : ring;
  f_inv  : path;
  f_div  : path option;
}

(* -------------------------------------------------------------------- *)
type eq  = form * form
type eqs = eq list

(* -------------------------------------------------------------------- *)
let rapp r op args =
  let opty = toarrow (List.map f_ty args) r.r_type in
    f_app (f_op op [] opty) args r.r_type

let rzero r = rapp r r.r_zero []
let rone  r = rapp r r.r_one  []

let radd r e1 e2 = rapp r r.r_add [e1; e2]
let ropp r e     = rapp r r.r_opp [e]
let rmul r e1 e2 = rapp r r.r_mul [e1; e2]
let rexp r e  i  = rapp r r.r_exp [e; f_int i]

let rsub r e1 e2 =
  match r.r_sub with
  | None   -> radd r e1 (ropp r e2)
  | Some p -> rapp r p [e1; e2]

let rintmul r i =
  match r.r_intmul with
  | `Embed    -> f_int i
  | `IntMul p -> rapp r p [f_int i]

(* -------------------------------------------------------------------- *)
type cringop = [`Zero | `One | `Add | `Opp | `Sub | `Mul | `Exp | `IntMul]
type cring   = ring * (cringop Mp.t)

(* -------------------------------------------------------------------- *)
type cfieldop = [cringop | `Inv | `Div]
type cfield   = field * (cfieldop Mp.t)

(* -------------------------------------------------------------------- *)
let cring_of_ring (r : ring) : cring =
  let cr = [(r.r_zero, `Zero);
            (r.r_one , `One );
            (r.r_add , `Add );
            (r.r_opp , `Opp );
            (r.r_mul , `Mul );
            (r.r_exp , `Exp )]
  in

  let cr = List.fold_left (fun m (p, op) -> Mp.add p op m) Mp.empty cr in
  let cr = odfl cr (r.r_sub |> omap (fun p -> Mp.add p `Sub cr)) in
  let cr = r.r_intmul |> (function `Embed -> cr | `IntMul p -> Mp.add p `IntMul cr) in
    (r, cr)

(* -------------------------------------------------------------------- *)
let cfield_of_field (r : field) : cfield =
  let cr = (snd (cring_of_ring r.f_ring) :> cfieldop Mp.t) in
  let cr = Mp.add r.f_inv `Inv cr in
  let cr = odfl cr (r.f_div |> omap (fun p -> Mp.add p `Div cr)) in
    (r, cr)

(* -------------------------------------------------------------------- *)
let toring ((r, cr) : cring) (rmap : RState.rstate) (form : form) =
  let rmap = ref rmap in

  let int_of_form form = reffold (RState.add form) rmap in

  let rec doit form =
    match sform_of_form form with
    | SFop ((op, _), args) -> begin
        match Mp.find_opt op cr with
        | None -> abstract form
        | Some op -> begin
            match op,args with
            | `Zero, []           -> PEc c0
            | `One , []           -> PEc c1
            | `Add , [arg1; arg2] -> PEadd (doit arg1, doit arg2)
            | `Opp , [arg1]       -> PEsub (PEc c0, doit arg1)
            | `Sub , [arg1; arg2] -> PEsub (doit arg1, doit arg2)
            | `Mul , [arg1; arg2] -> PEmul (doit arg1, doit arg2)
            | `Exp , [arg1; arg2] -> begin
                match arg2.f_node with
                | Fint n when n >= 0 -> PEpow (doit arg1, n)
                | _ -> abstract form
            end
            | _, _ -> abstract form
        end
    end
    | SFint i when r.r_intmul = `Embed -> PEc (Big_int.big_int_of_int i)
    | _ -> abstract form

  and abstract form = PEX (int_of_form form) in

  let form = doit form in (form, !rmap)

(* -------------------------------------------------------------------- *)
let tofield ((r, cr) : cfield) (rmap : RState.rstate) (form : form) =
  let rmap = ref rmap in

  let int_of_form form = reffold (RState.add form) rmap in

  let rec doit form =
    match sform_of_form form with
    | SFop ((op, _), args) -> begin
        match Mp.find_opt op cr with
        | None -> abstract form
        | Some op -> begin
            match op,args with
            | `Zero, []           -> FEc c0
            | `One , []           -> FEc c1
            | `Add , [arg1; arg2] -> FEadd (doit arg1, doit arg2)
            | `Opp , [arg1]       -> FEsub (FEc c0, doit arg1)
            | `Sub , [arg1; arg2] -> FEsub (doit arg1, doit arg2)
            | `Mul , [arg1; arg2] -> FEmul (doit arg1, doit arg2)
            | `Inv , [arg1]       -> FEdiv (FEc c1, doit arg1)
            | `Div , [arg1; arg2] -> FEdiv (doit arg1, doit arg2)
            | `Exp , [arg1; arg2] -> begin
                match arg2.f_node with
                | Fint n -> FEpow (doit arg1, n)
                | _ -> abstract form
            end
            | _, _ -> abstract form
        end
    end
    | SFint i when r.f_ring.r_intmul = `Embed -> FEc (Big_int.big_int_of_int i)
    | _ -> abstract form

  and abstract form = FEX (int_of_form form) in

  let form = doit form in (form, !rmap)

(* -------------------------------------------------------------------- *)
let ofring (r : ring) (rmap : RState.rstate) (e : pol) : form =
  let rec doit idx e =
    match e with
    | Pc c ->
      let c = Big_int.int_of_big_int c in (* FIXME: possible overflow *)
        rintmul r c

    | Pinj (j, e) -> doit (idx-j) e

    | PX (p, i, q) ->
        let f = oget (RState.get i rmap) in
        let f = match i with 1 -> f | _ -> rexp r f i in
        let f = if peq p (Pc c1) then f else rmul r (doit idx p) f in
        let f = if peq q (Pc c0) then f else radd r f (doit (idx-1) q) in
          f
  in
    doit (RState.current rmap) e

(* -------------------------------------------------------------------- *)
let ring_simplify (cr : cring) (eqs : eqs) (form : form) =
  let map = ref RState.empty in
  let toring form = reffold (fun map -> toring cr map form) map in

  let form = toring form in
  let eqs  = List.map (fun (f1, f2) -> (toring f1, toring f2)) eqs in
    ofring (fst cr) !map (norm form eqs)

(* -------------------------------------------------------------------- *)
let ring_eq (cr : cring) (eqs : eqs) (f1 : form) (f2 : form) =
  ring_simplify cr eqs (rsub (fst cr) f1 f2)

(* -------------------------------------------------------------------- *)
let get_field_equation (f1, f2) =
  match fnorm f1, fnorm f2 with
  | (n, PEc l, []), (m, PEc r, []) when (ceq l c1 && ceq r c1) -> Some (n, m)
  | _ -> None

(* -------------------------------------------------------------------- *)
let field_eq (cr : cfield) (eqs : eqs) (f1 : form) (f2 : form) =
  let map = ref RState.empty in

  let tofield form = reffold (fun map -> tofield cr map form) map in
  let ofring  form = ofring (fst cr).f_ring !map form in

  let (f1, f2) = (tofield f1, tofield f2) in

  let (num1, denum1, cond1) = fnorm f1 in
  let (num2, denum2, cond2) = fnorm f2 in

  let eqs = List.map (fun (f1, f2) -> (tofield f1, tofield f2)) eqs in
  let eqs = List.pmap get_field_equation eqs in

  let norm form = ofring (norm form eqs) in

  let num1   = norm num1   in
  let num2   = norm num2   in
  let denum1 = norm denum1 in
  let denum2 = norm denum2 in
  let cond1  = List.map norm cond1 in
  let cond2  = List.map norm cond2 in

    (cond1 @ cond2, (num1, num2), (denum1, denum2))

(* -------------------------------------------------------------------- *)
let field_simplify (cr : cfield) (eqs : eqs) (f : form) =
  let map = ref RState.empty in

  let tofield form = reffold (fun map -> tofield cr map form) map in
  let ofring  form = ofring (fst cr).f_ring !map form in

  let (num, denum, cond) = fnorm (tofield f) in
  let eqs = List.map (fun (f1, f2) -> (tofield f1, tofield f2)) eqs in
  let eqs = List.pmap get_field_equation eqs in

  let norm form = ofring (norm form eqs) in

    (List.map norm cond, norm num, norm denum)

(* -------------------------------------------------------------------- *)
module Axioms = struct
  open EcDecl

  let tmod  = "AlgTactic"
  let tname = "domain"

  let zero = "rzero"
  let one  = "rone"
  let add  = "add"
  let opp  = "opp"
  let sub  = "sub"
  let mul  = "mul"
  let inv  = "inv"
  let div  = "div"
  let expr = "expr"

  let core   = ("RingCore"    , ["oner_eq0"; "addr0"; "addrA"; "addrC"; "addrN";
                                 "mulr1"; "mulrA"; "mulrC"; "mulrDl"])
  let natmul = ("RingNatMul"  , ["expr0"; "exprS"])
  let ofint  = ("RingOfInt"   , ["ofint0"; "ofint1"; "ofintS"; "ofintN"])
  let ofsub  = ("RingWithSub" , ["subrE"])
  let field  = ("FieldCore"   , ["mulrV"; "exprN"])
  let ofdiv  = ("FieldWithDiv", ["divrE"])

  let subst_of_ring thname (cr : ring) =
    let crcore = [(zero, cr.r_zero);
                  (one , cr.r_one );
                  (add , cr.r_add );
                  (opp , cr.r_opp );
                  (mul , cr.r_mul );
                  (expr, cr.r_exp )] in

    let thpath = EcPath.fromqsymbol ([tmod], thname) in
    let xpath  = fun x -> EcPath.pqname thpath x in
    let add    = fun subst x p -> EcSubst.add_path subst (xpath x) p in

    let subst  = EcSubst.add_tydef EcSubst.empty (xpath tname) ([], cr.r_type) in
    let subst  = List.fold_left (fun subst (x, p) -> add subst x p) subst crcore in
    let subst  = odfl subst (cr.r_sub |> omap (fun p -> add subst sub p)) in
    let subst  = cr.r_intmul |> (function `Embed -> subst | `IntMul p -> add subst expr p) in
      subst

  let subst_of_field thname (cr : field) =
    let thpath = EcPath.fromqsymbol ([tmod], thname) in
    let xpath  = fun x -> EcPath.pqname thpath x in
    let add    = fun subst x p -> EcSubst.add_path subst (xpath x) p in

    let subst = subst_of_ring thname cr.f_ring in
    let subst = add subst inv cr.f_inv in
    let subst = odfl subst (cr.f_div |> omap (fun p -> add subst div p)) in
      subst

  (* FIXME: should use operators inlining when available *)
  let get (thname, axs) env cr =
    let thpath = EcPath.fromqsymbol ([tmod], thname) in
    let subst  =
      match cr with
      | `Ring  cr -> subst_of_ring  thname cr
      | `Field cr -> subst_of_field thname cr
    in

    let for1 axname =
      let ax = EcEnv.Ax.by_path (EcPath.pqname thpath axname) env in
        assert (ax.ax_tparams = [] && ax.ax_kind = `Axiom && ax.ax_spec <> None);
        (axname, EcSubst.subst_form subst (oget ax.ax_spec))
    in
      List.map for1 axs

  let get_core   = fun env cr -> get core   env (`Ring  cr)
  let get_natmul = fun env cr -> get natmul env (`Ring  cr)
  let get_ofint  = fun env cr -> get ofint  env (`Ring  cr)
  let get_ofsub  = fun env cr -> get ofsub  env (`Ring  cr)
  let get_field  = fun env cr -> get field  env (`Field cr)
  let get_ofdiv  = fun env cr -> get ofdiv  env (`Field cr)

  let ring_axioms env (cr : ring) =
    let axcore = (get_core env cr) @ (get_natmul env cr) in
    let axint  = match cr.r_intmul with `Embed -> [] | `IntMul _ -> get_ofint env cr in
    let axsub  = match cr.r_sub with None -> [] | Some _ -> get_ofsub env cr in
      List.flatten [axcore; axint; axsub]

  let field_axioms env (cr : field) =
    let axring = ring_axioms env cr.f_ring in
    let axcore = get_field env cr in
    let axdiv  = match cr.f_div with None -> [] | Some _ -> get_ofdiv env cr in
      List.flatten [axring; axcore; axdiv]
end

let ring_axioms  = Axioms.ring_axioms
let field_axioms = Axioms.field_axioms
