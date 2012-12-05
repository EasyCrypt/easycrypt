open EcUtils
open EcTypes

type lbinop = 
  | Land 
  | Lor
  | Limp
  | Liff

type quantif = 
  | Lforall
  | Lexists

type binding = (EcIdent.t * ty) list

module Side : sig
  type t = int
  (* For non relational formula *)
  val mono : t 
  (* For relational formula *)
  val left : t
  val right : t 
      
  type policy 
  val pmono : policy
  val prela : policy
  val pextra : policy
(*  val check_policy : policy -> int -> t *)
end = struct
  type t = int 
  let mono = 0
  let left = 1
  let right = 2
  type policy =
    | Pmono
    | Prela
    | Pextra 
  let pmono = Pmono
  let prela = Prela
  let pextra = Pextra
(*  let check_policy p n =
    match p with
    | Pmono -> error "not side allowed"
    | Prela ->
        if n = 1 || n = 2 then n
        else error "only relational side allowed"
    | Pextra ->
        if n > 0 then n
        else error "side start at 1" *)
end

(*type form = private {
    f_node : f_node;
    f_ty   : ty option;
  }
and*)
type fty = ty option

type lfpattern = 
  | LFPSymbol of EcIdent.t * ty 
  | LFPTuple of (EcIdent.t*ty) list

type form = 
  | Ftrue
  | Ffalse
  | Fnot   of form
  | Fbinop of form * lbinop * form
  | Fquant of quantif * binding * form
  | Fif    of form * form * form
  | Flet  of lfpattern * form * form
  | Funit                                        (* unit literal        *)
  | Fbool   of bool                              (* bool literal        *)
  | Fint    of int                               (* int. literal        *)
  | Flocal  of EcIdent.t * ty                    (* Local variable      *)
  | Fpvar   of EcPath.path * ty * Side.t         (* sided symbol        *)
  | Fapp    of EcPath.path * form list * ty option (* op/pred application *)
  | Ftuple  of form list                         (* tuple constructor     *)
  | Fofbool of form                              (* Cast an bool to prop  *)


let ftrue = Ftrue
let ffalse = Ffalse
let fbool b = Fbool b 
let fnot f = Fnot(f)
let fbinop f1 op f2 = Fbinop(f1,op,f2)
let flocal x ty = Flocal(x, ty)
let fpvar x ty s = Fpvar(x,ty,s)
let fofbool f =
  match f with
  | Fbool b -> 
      if b then ftrue else ffalse 
  | _ -> Fofbool f 

let fapp x args oty = Fapp(x,args,oty)
let fif f1 f2 f3 = Fif(f1,f2,f3)
let flet q f1 f2 = Flet(q,f1,f2)
let fquant q b f = Fquant(q,b,f)
let fexists b f = Fquant(Lexists, b, f)   
let fforall b f = Fquant(Lforall, b, f)   

let map gt g f = 
  match f with
  | Ftrue -> Ftrue
  | Ffalse -> Ffalse
  | Fnot f -> fnot (g f)
  | Fbinop(f1,op,f2) -> fbinop (g f1) op (g f2)
  | Fquant(q,b,f) -> 
      fquant q (List.map (fun (x,ty) -> x, gt ty) b) (g f)
  | Fif(f1,f2,f3) -> fif (g f1) (g f2) (g f3)
  | Flet(lp,f1,f2) -> 
      let lp = match lp with
      | LFPSymbol(id,ty) -> LFPSymbol(id,gt ty)
      | LFPTuple d -> LFPTuple (List.map (fun (x,ty) -> x, gt ty) d) in
      flet lp (g f1) (g f2)
  | Funit -> Funit
  | Fbool b -> Fbool b
  | Fint i -> Fint i
  | Flocal(id,ty) -> Flocal(id, gt ty)
  | Fpvar(id,ty,s) -> Fpvar(id, gt ty, s)
  | Fapp(p,es, oty) ->
      fapp p (List.map g es) (obind oty (fun ty -> Some (gt ty)))
  | Ftuple es -> Ftuple (List.map g es)
  | Fofbool e -> Fofbool (g e)

(* -------------------------------------------------------------------- *)
module Subst = struct
  let rec uni uidmap formula =
    map (EcTypes.Subst.uni uidmap) (uni uidmap) formula
end
