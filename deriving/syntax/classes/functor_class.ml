(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

open Pa_deriving_common
open Utils

module Description : Defs.ClassDescription = struct
  let classname = "Functor"
  let runtimename = "Deriving_Functor"
  let default_module = None
  let alpha = None
  let allow_private = false
  let predefs = [
    ["list"], ["Deriving_Functor";"list"];
    ["ref"], ["Deriving_Functor";"ref"];
    ["option"], ["Deriving_Functor";"option"];
  ]
  let depends = []
end

module Builder(Loc : Defs.Loc) = struct

  module Helpers = Base.AstHelpers(Loc)

  open Loc
  open Camlp4.PreCast
  open Description

  type context = {
    argmap : Type.qname Type.NameMap.t;
    params : Type.param list;
  }

  let substitute env =
    (object
       inherit Type.transform as default
       method expr = function
         | `Param (p,v) when Type.NameMap.mem p env ->
             `Param (Type.NameMap.find p env,v)
         | e -> default# expr e
     end) # expr

  let setup_context (_,params,_,_,_ : Type.decl) : context =
    let argmap =
      List.fold_right
        (fun (p,_) m -> Type.NameMap.add p [Printf.sprintf "V_%s" p] m)
        params
        Type.NameMap.empty in
    { argmap = argmap;
      params = params;
    }

  let param_map context : string Type.NameMap.t =
    List.fold_right
      (fun (name,_) map -> Type.NameMap.add name ("f_" ^ name) map)
      context.params
      Type.NameMap.empty

  let tdec, sigdec =
    let dec context name =
      ("f", context.params,
       `Expr (`Constr ([name], List.map (fun p -> `Param p) context.params)), [], false)
    in
      (fun context name -> Helpers.Untranslate.decl (dec context name)),
      (fun context name -> Helpers.Untranslate.sigdecl (dec context name))

  let wrapper context name expr =
    let param_map = param_map context in
    let patts :Ast.patt list =
      List.map
        (fun (name,_) -> <:patt< $lid:Type.NameMap.find name param_map$ >>)
        context.params in
    let rhs =
      List.fold_right (fun p e -> <:expr< fun $p$ -> $e$ >>) patts expr in
      <:module_expr< struct
        type $tdec context name$
        let map = $rhs$
      end >>
(*
   prototype: [[t]] : t -> t[b_i/a_i]


   [[a_i]]   = f_i

   [[C1|...CN]] = function [[C1]] ... [[CN]]               sum
   [[`C1|...`CN]] = function [[`C1]] ... [[`CN]]           variant

   [[{t1,...tn}]] = fun (t1,tn) -> ([[t1]],[[tn]])         tuple
   [[{l1:t1; ... ln:tn}]] =
         fun {l1=t1;...ln=tn} -> {l1=[[t1]];...ln=[[tn]]}  record

   [[(t1,...tn) c]] = c_map [[t1]]...[[tn]]                constructor

   [[a -> b]] = f . [[a]] (where a_i \notin fv(b))         function

   [[C0]]    = C0->C0                                      nullary constructors
   [[C1 (t1...tn)]]  = C1 t -> C0 ([[t1]] t1...[[tn]] tn)  unary constructor
   [[`C0]]   = `C0->`C0                                    nullary tag
   [[`C1 t]] = `C1 t->`C0 [[t]] t                          unary tag
*)
  let rec polycase context = function
    | Type.Tag (name, []) -> <:match_case< `$name$ -> `$name$ >>
    | Type.Tag (name, es) -> <:match_case< `$name$ x -> `$name$ ($expr context (`Tuple es)$ x) >>
    | Type.Extends t ->
        let patt, guard, exp = Helpers.cast_pattern context.argmap t in
          <:match_case< $patt$ when $guard$ -> $expr context t$ $exp$ >>

  and expr context : Pa_deriving_common.Type.expr -> Ast.expr = function
    | t when not (Type.contains_tvars t) -> <:expr< fun x -> x >>
    | `Param (p,_) -> <:expr< $lid:Type.NameMap.find p (param_map context)$ >>
    | `Function (f,t) when not (Type.contains_tvars t) ->
        <:expr< fun f x -> f ($expr context f$ x) >>
    | `Constr (qname, ts) ->
	let qname =
	  try List.assoc qname predefs
	  with Not_found -> qname in
        List.fold_left
          (fun fn arg -> <:expr< $fn$ $expr context arg$ >>)
          <:expr< $id:Helpers.modname_from_qname ~qname ~classname$.map >>
          ts
    | `Tuple ts -> tup context ts
    | _ -> raise (Base.Underivable "Functor cannot be derived for this type")

  and tup context = function
    | [t] -> expr context t
    | ts ->
        let args, exps =
          (List.fold_right2
             (fun t n (p,e) ->
                let v = Printf.sprintf "t%d" n in
                  Ast.PaCom (_loc, <:patt< $lid:v$ >>, p),
                  Ast.ExCom (_loc, <:expr< $expr context t$ $lid:v$ >>, e))
             ts
             (List.range 0 (List.length ts))
             (<:patt< >>, <:expr< >>)) in
        let pat, exp = Ast.PaTup (_loc, args), Ast.ExTup (_loc, exps) in
          <:expr< fun $pat$ -> $exp$ >>

  and case context = function
    | (name, []) -> <:match_case< $uid:name$ -> $uid:name$ >>
    | (name, args) ->
        let f = tup context args
        and _, tpatt, texp = Helpers.tuple (List.length args) in
          <:match_case< $uid:name$ $tpatt$ -> let $tpatt$ = ($f$ $texp$) in $uid:name$ ($texp$) >>

  and field context (name, (_,t), _) : Ast.expr =
    <:expr< $expr context t$ $lid:name$ >>

  let rhs context = function
    |`Fresh (_, _, `Private) -> raise (Base.Underivable "Functor cannot be derived for private types")
    |`Fresh (_, Type.Sum summands, _)  ->
       <:expr<  function $list:List.map (case context) summands$ >>
    |`Fresh (_, Type.Record fields, _) ->
       <:expr< fun $Helpers.record_pattern fields$ ->
                   $Helpers.record_expr (List.map (fun ((l,_,_) as f) -> (l,field context f)) fields)$ >>
    |`Expr e                  -> expr context e
    |`Variant (_, tags) ->
       <:expr< function $list:List.map (polycase context) tags$ | _ -> assert false >>
    | `Nothing -> raise (Base.Underivable "Cannot generate functor instance for the empty type")


  let maptype context name =
    let param_map = param_map context in
    let ctor_in = `Constr ([name], List.map (fun p -> `Param p) context.params) in
    let ctor_out = substitute param_map ctor_in  (* c[f_i/a_i] *) in
      List.fold_right (* (a_i -> f_i) -> ... -> c[a_i] -> c[f_i/a_i] *)
        (fun (p,_) out ->
           (<:ctyp< ('$lid:p$ -> '$lid:Type.NameMap.find p param_map$) -> $out$>>))
        context.params
        (Helpers.Untranslate.expr (`Function (ctor_in, ctor_out)))

   let signature context name : Ast.sig_item list =
     [ <:sig_item< type $list:sigdec context name$ >>;
       <:sig_item< val map : $maptype context name$ >> ]

 let decl (name, _, r, _, _ as decl) : Camlp4.PreCast.Ast.module_binding =
   let context = setup_context decl in
    if name = "f" then
      raise (Base.Underivable ("deriving: Functor cannot be derived for types called `f'.\n"
                          ^"Please change the name of your type and try again."))
    else
      <:module_binding<
         $uid:classname ^ "_" ^ name$
       : sig $list:signature context name$ end
       = $wrapper context name (rhs context r)$ >>

  let gen_sig (tname, params, _, _, generated as decl) =
    let context = setup_context decl in
    if tname = "f" then
      raise (Base.Underivable ("deriving: Functor cannot be derived for types called `f'.\n"
                          ^"Please change the name of your type and try again."))
    else
      if generated then
        <:sig_item< >>
      else
        <:sig_item< module $uid:classname ^ "_" ^ tname$ :
                    sig type $tdec context tname$ val map : $maptype context tname$ end >>

  let generate decls =
    <:str_item< module rec $list:List.map decl decls$ >>

  let generate_sigs decls =
    <:sig_item< $list:List.map gen_sig decls$>>

end

module Functor = Base.Register(Description)(Builder)
