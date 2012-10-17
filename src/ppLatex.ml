open EcUtil
open Format
open Ast
open AstYacc

type ep_blocks = 
  (** Basics blocks of 'ep' *)

  | EPPack   of ep_blocks list          (*  *)
  | EPIpack  of ep_blocks list
  | EPBlock  of ep_blocks list          (*  *)
  | EPSeq    of ep_blocks list          (*  *)
  | EPIseq   of ep_blocks list          (*  *)
  | EPInstr  of ep_blocks list          (*  *)
  | EPItem   of string             
  | EPItems  of ep_blocks list             
  | EPCascade of ep_blocks * ep_blocks
  | EPBreak
  | EPNewline 

  (** Other blocks are only using to generate better basics blocks *)

  | EPKw   of string       (** print with \mathsf{keyword} (style for keywords) *)
  | EPCmd  of string       (** LaTex command, when is printing we add "\ " *)
  | EPTac  of string       (** print with \mathsf{keyword} (style for tactics*)
  | EPInt  of int          (** print an int *)
  | EPStr  of string       (** print the string but escape LaTeX characters *)
  | EPOpen of string       (** Print the string ( like "(", "[", etc) : should
                              be use in fusion, to join all Open ... Close block 
                              in one item if its possible *)
  | EPClose of string       (** Print the string ")", "]" ,etc. See comments (EPOpen) *)
  | EPOp of string          (** Escape special infix operators *)
  | EPEmpty                 (** Nothing :) *)
  | EPList of ep_blocks list  

(* TODO: Make something more clever to escape special latex symbols
 * inside the different names*)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
      exp (String.length s - 1) []

let implode l =
  let res = String.create (List.length l) in
    let rec imp i = function
      | [] -> res
      | c :: l -> res.[i] <- c; imp (i + 1) l in
          imp 0 l

let special_symbols = ['_'; '#'; '{'; '}'; '%'; '$'; '&'  (*'\''*)]


let rec escape (lst : char list) : char list =
  match lst with
    [] ->  []
    | h :: t when (List.mem h special_symbols) -> '\\' :: (h :: (escape t))
    | h :: t -> h :: (escape t)

(* Basic functions for printing names *)
let pp_name fmt s = fprintf fmt "%s" (implode (escape (explode s)))

(** The basics blocks for 'ec-tex' files *)

let begin_block s fmt  = fprintf fmt "%s@\n" s; pp_open_vbox fmt 2; fprintf fmt "[@\n"
let end_block fmt   = pp_close_box fmt (); fprintf fmt "@\n]@\n"

let b_item fmt      = fprintf fmt "item \""
let e_item fmt      = fprintf fmt "\"@\n"
let b_cascade fmt   = pp_open_vbox fmt 2;  fprintf fmt "cascade@\n"
let e_cascade fmt   = pp_close_box fmt (); fprintf fmt "@\n"

(** Wrap something inside an item *)
let p_keyword fmt name         = fprintf fmt "\\mathsf{%a}" pp_name name
let p_string fmt name          = fprintf fmt "%a" pp_name name
let p_command fmt name         = fprintf fmt "\\%s " name
let p_int fmt d                = fprintf fmt "%d" d
let p_iprim_ident s            = EPStr s 
let p_fct_name (g,f)           = EPStr (g ^ "." ^ f) 
let p_p_var (_,s)              = [EPStr s]

(** Set-up tags for the formatter *)
let config fmt =
  Format.pp_set_tags fmt true;
  Format.pp_set_mark_tags fmt false;
  let defaults = Format.pp_get_formatter_tag_functions fmt () in
    let open_tag = function
       | "it"   -> b_item fmt
       | "ins"  -> begin_block "instr" fmt
       | "p"    -> begin_block "pack"  fmt
       | "ip"   -> begin_block "ipack" fmt
       | "seq"  -> begin_block "seq"   fmt
       | "iseq" -> begin_block "iseq"  fmt
       | "b"    -> begin_block "block" fmt
       | "c"    -> b_cascade fmt
       | x -> defaults.Format.print_open_tag x 
    and close_tag = function 
       | "it"  -> e_item  fmt
       | "ins" -> end_block fmt
       | "p"   -> end_block fmt
       | "ip"  -> end_block fmt
       | "seq" -> end_block fmt
       | "iseq" -> end_block fmt
       | "c"   -> e_cascade fmt
       | "b"   -> end_block fmt
       | x -> defaults.Format.print_close_tag x 
    in Format.pp_set_formatter_tag_functions fmt 
        {defaults with print_open_tag = open_tag; print_close_tag = close_tag}



let ep_string = (fun x -> [EPStr x])


let p_op_ident = function
  | "<>" -> "\\neq"
  | "||" -> "\\lor"
  | "<=" ->"\\leq"
  | ">=" ->"\\geq"
  | "=>" -> "\\Rightarrow"
  | "<=>" -> "\\Leftrightarrow"
  | "^"  -> "\\hat ~" 
  | "&&" -> "\\land" 
  | "^^" -> "\\oplus"
  | s    -> s

let make_op_ident = function
  | "^^"  -> [EPCmd "oplus"]
  | "<>"  -> [EPCmd "neq"]
  | "||"  -> [EPCmd "lor"]
  | "<="  -> [EPCmd "leq"]
  | ">="  -> [EPCmd "geq"]
  | "=>"  -> [EPCmd "Rightarrow"]
  | "<=>" -> [EPCmd "Leftrightarrow"]
(*  | "^"   -> EPmd "hat ~" *)
  | "&&"  -> [EPCmd "land"] 
  | s     -> [EPOp s]

(** When the 'sizes' of is greater than 'magic_number' try_fusion will join 
 * the structure  *)
let magic_number = 30

(** Make and approximation of the lenght of the structure *)
let rec magic_len = function
  | EPItem     x         -> String.length x
  | EPKw       s         -> String.length s
  | EPTac      s         -> String.length s 
  | EPStr      s         -> String.length s 
  | EPOp       s         -> String.length s
  | EPItems    xs        -> List.fold_right (fun x b -> (magic_len x) + b) xs 0
  | EPList     xs        -> List.fold_right (fun x b -> (magic_len x) + b) xs 0
  | EPPack     xs        -> List.fold_right (fun x b -> (magic_len x) + b) xs 0
  | EPCmd      _         -> 4 
  | EPInt      _         -> 2 
  | EPOpen     _         -> 2 
  | EPClose    _         -> 2
  | EPEmpty              -> 0 
  | EPBreak              -> 0
  | _                    -> magic_number

(** This is used only in fusion when we know that the structure is an item.*)
let fromItems  = function
  | EPItems x -> x
  | _         -> [] 

(** We create an item with all the basic pieces *)
let rec fusion = function
  | EPItem     xs        -> [EPItem xs]
  | EPBreak              -> []
  | EPKw       s         -> [EPKw s]
  | EPCmd      s         -> [EPCmd s]
  | EPTac      s         -> [EPTac s]
  | EPInt      i         -> [EPInt i]
  | EPStr      s         -> [EPStr s]
  | EPOpen     s         -> [EPOpen s]
  | EPClose    s         -> [EPClose s]
  | EPOp       s         -> [EPOp s]
  | EPEmpty              -> []
  | EPItems    xs        -> xs
  | EPPack     xs        -> 
    (List.fold_right (fun x b ->  ((fusion x)) @ b) xs []) 
  | EPList     xs        -> 
    (List.fold_right (fun x b ->  ((fusion x)) @ b) xs [])
  | _ -> not_implemented "PpLatex.fusion"

(**  When its possible we try to fusion a lot of items in one.
 * With this we ensure that inside this items 'ec-tex' don't put an enter*)
let try_fusion x =
  if ((magic_len x) < magic_number) then EPItems (fusion x) else x

let try_fusion2 xs =
  if ((magic_len (EPList xs)) < magic_number) 
  then [EPItems (fusion (EPList xs))] else xs

let rec ep_print_aux fmt = function
  | EPItem     xs        -> fprintf fmt "%s" xs
  | EPKw       s         -> p_keyword fmt s
  | EPCmd      s         -> p_command fmt s
  | EPTac      s         -> p_keyword fmt s
  | EPInt      i         -> p_int fmt i   
  | EPStr      s         -> p_string fmt s
  | EPOpen     s         -> p_string fmt s
  | EPClose    s         -> p_string fmt s
  | EPOp       s         -> p_string fmt (p_op_ident s)
  | EPEmpty              -> ()
  | _ -> not_implemented "PpLatex.fusion"



(** Print the 'ep' structure into a file.ep*)
let rec ep_print fmt = function
  | EPPack     xs        -> fprintf fmt "@{<p>%a@}"      (pp_list ~sep:"" ep_print) xs
  | EPIpack    xs        -> fprintf fmt "@{<ip>%a@}"     (pp_list ~sep:"" ep_print) xs
  | EPBlock    xs        -> fprintf fmt "@{<b>%a@}"      (pp_list ~sep:"" ep_print) xs
  | EPSeq      xs        -> fprintf fmt "@{<seq>%a@}"    (pp_list ~sep:"" ep_print) xs
  | EPIseq     xs        -> fprintf fmt "@{<iseq>%a@}"   (pp_list ~sep:"" ep_print) xs
  | EPInstr    xs        -> fprintf fmt "@{<ins>%a@}"    (pp_list ~sep:"" ep_print) xs
  | EPItem     xs        -> fprintf fmt "@{<it>%s@}"     xs
  | EPItems    xs        -> fprintf fmt "@{<it>%a@}"     (pp_list ~sep:" {} " ep_print_aux) xs 
  | EPCascade  (ep1,ep2) -> fprintf fmt "@{<c>%a%a@}"    ep_print ep1 ep_print ep2
  | EPKw       s         -> fprintf fmt "@{<it>%a \\ @}" p_keyword s
  | EPCmd      s         -> fprintf fmt "@{<it>%a@}"     p_command s
  | EPTac      s         -> fprintf fmt "@{<it>%a@}"     p_keyword s
  | EPInt      i         -> fprintf fmt "@{<it>%a@}"     p_int i   
  | EPStr      s         -> fprintf fmt "@{<it>%a@}"     p_string s
  | EPOpen     s         -> fprintf fmt "@{<it>%a@}"     p_string s
  | EPClose    s         -> fprintf fmt "@{<it>%a@}"     p_string s
  | EPOp       s         -> fprintf fmt "@{<it>%a@}"     p_string (p_op_ident s)
  | EPNewline            -> fprintf fmt "newline@\n"
  | EPBreak              -> fprintf fmt "break@\n"
  | EPEmpty              -> ()
  | EPList     xs when (magic_len (EPList xs) < magic_number) ->
     ep_print fmt (try_fusion (EPList xs))
  | EPList     xs -> List.iter (fun x -> ep_print fmt x) xs 


let add_keys xs      = try_fusion2 ([EPOpen "{"] @ xs @ [EPClose "}"])
let add_brackets xs  = try_fusion2([EPOpen "["] @ xs @ [EPClose "]"])
let add_parents  xs  = try_fusion2 ([EPOpen "("] @ xs @ [EPClose ")"])
(** Functions to remove unnecessary parentheses *)

let protect_on x xs = 
  if x then try_fusion2 (add_parents xs) else try_fusion2 xs

let op_char1 = ['=';'<';'>';'~']
let op_char2 = ['+';'-']
let op_char3 = ['*';'/';'%']

let string_contains chars s = List.exists (String.contains s) chars
  
let priority name  = 
  match name with
  | "=>" | "<=>" -> 1, 2, 1
  | "||"         -> 2, 3, 2
  | "&&"         -> 2, 4, 3
(*  | "!" -> 4 *)
  | _ ->
      if string_contains op_char1 name then 5,5,6
      else if string_contains op_char2 name then 6,6,7
      else if string_contains op_char3 name then 7,7,8
      else 8,8,9


(** An equivalent of pp_list but for the 'ep' structure *)
let rec p_list foo sep = function
  | []    -> []
  | [x]   -> foo x
  | x::xs -> (foo x) @ ( sep :: (p_list foo sep xs))

let rec p_list2 foo sep = function
  | []    -> []
  | [x]   -> [foo x]
  | x::xs -> (foo x) :: ( sep :: (p_list2 foo sep xs))


let space = [EPItem "\\ "]
let p_ident_list xs = (p_list ep_string (EPStr ",") xs)
let p_var_list xs = (p_list p_p_var (EPStr ",") xs)



(** Print cnst type *)
let p_cnst = function
  | Ebool b     -> [EPKw (if b then "true" else "false") ]
  | Eint  i     -> [EPInt i]
  | Ecst  _     -> [EPEmpty] 

(** Print general expressions, an try to fusion when its necessary  *)
let rec g_p_exp p_base p_var pri e =
  let p_pos_exp pri (_,exp) = g_p_exp p_base p_var pri exp in 
  match e with
  | Ecnst c -> p_cnst c 
  | Ebase v -> try_fusion2 (p_base pri v)
  | Ernd r  -> try_fusion2 (g_p_random p_pos_exp r)
  | Epair l -> add_parents (p_list (p_pos_exp 0) (EPStr ",") l)

  | Eapp("!",[(_,Eapp ("in_dom",[e1;e2]))]) ->
    add_parents ( (p_pos_exp 9 e1) @ [EPCmd "notin"; EPStr "dom"] @ (p_pos_exp 9 e2))

  | Eapp("!",[(_,Eapp ("in_rng",[e1;e2]))]) ->
    add_parents ( (p_pos_exp 9 e1) @ [EPCmd "notin"; EPStr "ran"] @ (p_pos_exp 9 e2))

  | Eapp("!",[e1]) ->
    protect_on (pri > 4) ([EPCmd  "lnot"] @ (p_pos_exp 4 e1))

  | Eapp ("get", [e1;e2]) ->
    protect_on (pri > 9) ((p_pos_exp 9 e1 ) @ (add_brackets ( p_pos_exp 0 e2 )))

  | Eapp ("udp", [e1;e2;e3]) ->
    protect_on (pri > 9) ((p_pos_exp 9 e1)
       @  (add_brackets (p_pos_exp 0 e2) @  [EPCmd "leftarrow"]
                         @ (p_pos_exp 0 e3))) 

  | Eapp ("abs",[e1]) -> [ EPOpen "|"] @ (p_pos_exp 0 e1) @ [EPClose "|"]
  | Eapp ("-",[e1])  ->  [ EPStr "-"] @  (p_pos_exp 9 e1)
  | Eapp("real_of_int" ,[e1]) -> (p_pos_exp 9 e1) @  [EPStr "%r"]

  | Eapp ("in_dom", [e1;e2]) ->
    add_parents ( (p_pos_exp 9 e1) @ [EPCmd "in"; EPStr "dom"] @ (p_pos_exp 9 e2))

  | Eapp ("in_rng", [e1;e2]) ->
    add_parents (
      (p_pos_exp 9 e1) @  [EPCmd "in"; EPStr "ran"]  @ (p_pos_exp 9 e2))

  | Eapp (f, args) -> 
    [ EPOp f;] @ (add_parents (p_list (p_pos_exp 0) (EPStr ",") args))

  | Eif (c, e1, e2) -> 
    protect_on (pri > 0) 
      ([EPKw "if"] @ (p_pos_exp 0 c) @ space @ [EPKw "then"]
       @ (p_pos_exp 0 e1)
       @ space @ [EPKw "else"] @ (p_pos_exp 0 e2))

  | Elet (xs, e1, e2) -> 
    protect_on (pri > 0)  (add_parents ( 
      [EPKw "let"]  @ (p_var_list xs) @ [EPStr "="] @ (p_pos_exp 4 e1) 
      @ [EPKw "in"] @ (p_pos_exp 0 e2)))

(** Print random expressions, an try to fusion when its necessary  *)
and g_p_random p_exp = function
  | Rinter(e1,e2)  -> add_brackets ((p_exp 0 e1) @ [EPCmd "dots"] @ (p_exp 0 e2))
  | Rbool          -> [EPStr "{0,1}"]
  | Rbitstr e      -> [EPStr "{0,1}"] @ [EPItem "^{"] @ (p_exp 9 e) @ [EPItem "}"]
  | Rexcepted(r,e) -> (g_p_random p_exp r) @ [EPStr "\\"] @ (p_exp 9 e)
  | Rapp (f, args) -> [EPOp f] @ (add_parents (p_list (p_exp 0) (EPStr ",") args))

(** Print base expressions, an try to fusion when its necessary  *)
let rec p_base_expr pri e = match e with 
  | Eident s            -> [EPStr s]
  | Ebinop (op,e1,e2)   -> 
    let p,p1,p2 = priority op in
    protect_on (pri > p) (
      (p_p_exp2 p1 e1) @ (make_op_ident op) @ (p_p_exp2 p2 e2))
  | Eat (p_exp , n)     -> (p_p_exp p_exp) @ (add_keys [EPInt n])
  | Epr (q_name, p_exp) -> [p_fct_name q_name] @ (add_brackets (p_p_exp p_exp))
  | Elist p_exp_list    ->  add_brackets (p_p_exp_list p_exp_list) 

  (* For formula only *)
  | Eforall ( param_list , trigger, p_exp) ->
    [EPCmd "forall"] @ (p_param_list param_list) @ (p_trigger trigger) 
    @ [EPStr ","] @ (try_fusion2(p_p_exp p_exp)) 

  | Eexists ( param_list , trigger ,p_exp) ->  
    [EPCmd "exists"] @ (p_param_list param_list) @ (p_trigger trigger) 
    @ [EPStr ","] @ (try_fusion2 (p_p_exp p_exp))

  | Eeqvar var_list ->  [EPStr "="] @ (add_keys (p_var_list  var_list))

and p_p_exp (_,e) = g_p_exp p_base_expr p_p_var 0 e
and p_p_exp2 pri (_,e) = g_p_exp p_base_expr p_p_var pri e

and p_p_exp_list p_exp_list = (p_list p_p_exp (EPStr ",") p_exp_list) 

and p_trigger = function 
  | [] -> [EPEmpty]
  | p_exp_list_list -> 
    add_brackets (p_list p_p_exp_list (EPStr "|") p_exp_list_list)

(** *)
and p_type_exp = function
  | Tbase s           -> [EPStr s] 
  | Tvar s            -> [p_iprim_ident s]
  | Tbitstring  p_exp -> [EPKw "bitstring"] @ (add_keys (p_p_exp p_exp)) 
  | Tpair   args      -> add_parents  (p_list p_type_exp (EPStr ",") args)
  | AstYacc.Tapp (args, s)    -> (add_parents (p_list p_type_exp (EPStr ",") args)) @
  space @ [ EPStr s]

and p_param_list typed_var_list = 
  try_fusion2 (add_parents (p_list p_typed_var (EPStr ",") typed_var_list))

and p_typed_var (p_var , type_exp) =
  (p_p_var p_var) @ [EPStr ":"] @  (p_type_exp type_exp)

let p_type_decl ((pnames, name), opt_type_exp)  = match opt_type_exp with
  | None when (List.length pnames = 0) ->   [EPKw "type"; EPStr name]
  | None -> 
    [EPKw "type"] @ (add_parents (p_ident_list pnames)) @ [EPStr  name]

  | Some type_exp when (List.length pnames = 0) -> 
    [EPKw "type"; EPStr name; EPStr "="] @ (p_type_exp type_exp)

  | Some type_exp -> 
    [EPKw "type"] @ (add_parents (p_ident_list pnames))
    @ [EPStr  name; EPStr "="]  @ (p_type_exp type_exp) 
        
let p_cnst_decl ((names,type_exp),opt_p_exp) = match opt_p_exp with
  | None -> 
    [EPKw "cnst"] @ (p_ident_list names) @ [EPStr ":"] @ (p_type_exp type_exp) 
  | Some p_exp -> 
    [EPKw "cnst"]@ (p_ident_list names) @ [EPStr ":"] 
     @ (p_type_exp type_exp) @ [EPStr "="] @ (p_p_exp p_exp) 

let p_fun_type (type_exp_list,type_exp) =
  (add_parents (p_list p_type_exp (EPStr ",") type_exp_list))
  @ [EPCmd "rightarrow"] @ (p_type_exp type_exp)

let p_op_decl_or_def = function
  | OpDecl (type_exp_list , type_exp) ->
    [ EPStr ":"] @  (p_fun_type (type_exp_list , type_exp))
  | OpDef (param_list , p_exp) -> 
    (p_param_list param_list) @ [EPStr "="] @ (p_p_exp  p_exp)

let p_op_decl (_,_,(infix, op_ident), op_decl_or_def, opt_name)  = 
  match opt_name ,infix with
  | None, false -> [EPKw "op"; EPOp op_ident] @ (p_op_decl_or_def  op_decl_or_def)
  | None, true  -> [EPKw "op"] @ (add_brackets [EPOp op_ident]) @ (p_op_decl_or_def  op_decl_or_def)
  | Some name, false -> 
    [EPKw "op"; EPOp op_ident] @ (p_op_decl_or_def op_decl_or_def)
    @ space @ [EPKw "as"; EPStr name]
  | Some name, true -> 
    [EPKw "op"] @ (add_brackets [EPOp op_ident]) @ (p_op_decl_or_def op_decl_or_def)
    @ space @ [EPKw "as"; EPStr name]

let p_pop_decl_or_def = function
  | PopDecl (type_exp_list , type_exp) ->
    [ EPStr ":"] @  (p_fun_type (type_exp_list , type_exp))
  | PopDef (param_list, param , p_exp) -> 
    (p_param_list param_list) @ [EPStr "="] @ add_parents (p_typed_var param) @ [EPStr "->"] @ (p_p_exp  p_exp)

let p_pop_decl (op_ident, pop_decl_or_def)  = 
  [EPKw "pop"; EPOp op_ident] @ (p_pop_decl_or_def  pop_decl_or_def)

      
let p_lasgn = function
  | Ltuple []  ->  [EPStr "()"]
  | Ltuple [e] ->  p_p_var e
  | Ltuple vs  ->  add_parents (p_var_list vs)
  | Lupd (v,e) ->  (p_p_var v) @ (add_brackets (p_p_exp e))

let rec p_instr = function
  | Sasgn  (l,e)   -> 
    EPInstr ((p_lasgn l) @ [EPCmd "leftarrow"] @ (p_p_exp e) @ [EPStr ";"])
  | Scall (l,f,es) ->
    EPInstr ( (p_lasgn l) @  [EPCmd "leftarrow"] @  (p_p_var f)
              @ (add_parents (p_list p_p_exp (EPStr ",") es))
              @ [EPStr ";"])
  | Sif (e,s1,[])    -> 
    EPCascade ( 
      EPInstr ([EPKw "if"]  @ (add_parents (p_p_exp e)) @ [EPKw "then"]), EPPack (p_stmt s1))

  | Sif (e,s1,s2)   ->  EPList [
    EPCascade ( 
     EPInstr ([EPKw "if"] @ (add_parents (p_p_exp e)) @  [EPKw "then"]),
     EPPack (p_stmt s1));

    EPCascade (EPKw "else",EPPack (p_stmt s2))]

  | Swhile (e,s)   -> 
    EPCascade ( EPInstr ([EPKw "while"] @  (add_parents (p_p_exp e))), EPPack (p_stmt s))
  | Sassert _      -> EPEmpty (*TODO*)

and p_p_instr (_,i) = [p_instr i]

and p_stmt stmt = (p_list p_p_instr EPEmpty stmt)

(** Print 'var' declarations *)
let p_decl_stmt (lvars, vtype, vdef) = match vdef with
  | None -> 
    EPInstr (
    [ EPKw "var"] @ (p_var_list lvars) @ [EPStr ":"] 
    @ (p_type_exp vtype) @ [EPStr ";"])

  | Some pos_exp -> 
    EPInstr ([ EPKw "var"] @ (p_var_list lvars) 
    @ [EPStr ":"] @ (p_type_exp vtype) @
    [EPStr "="] @ (p_p_exp pos_exp) @ [EPStr ";"])


(** Print a declaration of a function*)
let p_fun_decl ((_,name), tvars, texp) =
  [ EPStr name] @ (p_param_list tvars) @ [EPStr ":"] @ (p_type_exp texp)


 
(** Print the body of a function *)
let p_fun_def_body (decls, stmt, opt_exp) = match opt_exp with
  | None -> 
    EPIseq ((p_list2 p_decl_stmt (EPEmpty)  decls) @ (p_stmt stmt))
  | Some exp ->
    EPIseq ( (p_list2 p_decl_stmt (EPEmpty)  decls) 
              @ (p_stmt stmt)
              @  [EPInstr ([EPKw "return"] @ (p_p_exp exp) @ [EPStr ";"] )])


let p_ident_spec s =  
  EPList (p_list ep_string (EPStr ",") s)


let p_pg_elem = function
  | PEvar (pvars,texp)   -> p_decl_stmt (pvars,texp,None);
  | PEfun (fdecl, fdef)  -> 
    EPSeq [EPInstr [EPKw "fun"; EPList (p_fun_decl fdecl); EPStr "= {" ];
           p_fun_def_body fdef; EPStr "}"]
  | PEredef (n1, n2)     ->
    EPInstr [EPKw "fun"; EPStr n1; EPStr "="; p_fct_name n2]
  | PEabs (n1,n2,i_spec) ->
    EPInstr [ EPKw "abs"; EPStr n1; EPStr "=";  EPStr n2; 
              EPCmd "{" ;p_ident_spec i_spec; EPCmd "}"; EPStr ";"]

let p_pos_pg_elem (_,elem) = p_pg_elem elem

(** Print a redefinition function *)
let p_redef (name,body) =
  EPSeq [ EPPack [ EPKw "and"; EPStr name; EPStr "={"];
          p_fun_def_body body; EPStr "}" ]

(** Print the body of a game *)
let p_game_body = function
  | PGdef elems ->
    EPIseq (p_list2 p_pos_pg_elem (EPEmpty)  elems)

  | PGredef (_, (_,lvars) , []) ->
    EPIseq (List.map (fun (a,b) ->  p_decl_stmt (a,b,None)) lvars)

  | PGredef (_, (_,lvars) , (name,body) :: redef) ->
    EPPack [ EPList (List.map (fun (a,b) ->  p_decl_stmt (a,b,None)) lvars);
             EPSeq [ EPPack [ EPKw "where"; EPStr name; EPStr "={"];
                     p_fun_def_body body; EPStr "}" ];
             EPList (p_list2 p_redef (EPEmpty) redef)]


let aux_name = function
  | PGdef _             -> EPEmpty
  | PGredef (name, _,_) -> EPStr name

let p_game (name, iname, body) = 
  [ EPInstr [EPKw "game"; EPStr name; EPStr "="; EPStr iname;
             EPStr "="; aux_name body];
    p_game_body body]

let p_p_fol = p_p_exp

let p_hint  = function
  | Hauto                   -> space @ [EPKw "auto"]
  | Husing s                -> space @ [EPKw "using"; EPStr s]
  | Hadmit                  -> space @ [EPKw "admit"]
  | Hcompute                -> space @ [EPKw "compute"]
  | Hnone                   -> space @ [EPKw "none"]
  | Hsame                   -> space @ [EPKw "same"]
  | Hsplit                  -> space @ [EPKw "split"]
  | Hfailure (a,pexp,pexp',_) -> 
    space @ [ EPKw "compute"; EPInt a] @ 
            (p_p_exp pexp) @  [EPStr ","] @  (p_p_exp pexp')


let p_claim (name, (pexp,rhint)) = 
  [EPKw "claim"; EPStr name; EPStr ":"]@ (p_p_exp pexp) @ (p_hint rhint)

let p_axiom (name,b,pfol) = 
  [ EPKw (if b then "axiom" else "lemma"); EPStr name; EPStr ":"] @ (p_p_fol pfol)

let p_texps_texp (texps,texp) =
  (p_list p_type_exp (EPStr ",") texps) @ 
  [EPCmd "rightarrow "] @ (p_type_exp texp)

let p_adv_decl (fun_decl, xs) = 
  [EPKw "adversary"] @ (p_fun_decl fun_decl)
  @ [EPBlock (p_list p_texps_texp  (EPStr ",") xs)]


let p_inv = function
  | AstLogic.Inv_global p   -> p_p_fol p 
  | AstLogic.Inv_upto   ((p_fol1,p_fol2), opt) when (p_fol1 = p_fol2)-> 
    [ EPKw "upto"] @ (add_parents (p_p_fol p_fol1)) @ 
      (match opt with
        | None -> []
        | Some p_fol3 ->
          [ EPKw "with"] @ (add_parents (p_p_fol p_fol3)))

  | AstLogic.Inv_upto   ((p_fol1,p_fol2), opt) ->
    [ EPKw "upto"] @ (add_parents (p_p_fol p_fol1)) 
    @ space @ [EPKw "and"] @ (add_parents (p_p_fol p_fol2)) 
    @ (match opt with
        | None -> [] 
        | Some p_fol3 ->
          [ EPKw "with"] @ (add_parents (p_p_fol p_fol3)))
         

let p_equiv_concl = function
  | AstYacc.Aequiv_inv inv -> p_inv inv
  | AstYacc.Aequiv_spec (p_fol1,p_fol2,None) -> 
   (p_p_fol p_fol1) @ [EPCmd "Longrightarrow"] @  (p_p_fol p_fol2)
  | AstYacc.Aequiv_spec (p_fol1,p_fol2,Some(p_fol3,p_fol4)) -> 
    (p_p_fol p_fol1) @ [EPStr "="]
    @ (add_parents ((p_p_fol p_fol3) @ [EPStr ";"] @ (p_p_fol p_fol4)))
    @ [EPCmd "Rightarrow"] @ (p_p_fol p_fol2)

  
let p_auto_info  = function
  | (None, [])      -> []
  | (None, xs)      -> [ EPKw "using"] @ (p_ident_list xs) 
  | (Some inv, [])  ->  p_inv inv
  | (Some inv, xs)  -> [ EPKw "using"] @ (p_ident_list xs) @  (p_inv inv)

let p_auto_eager = function 
  | AstLogic.Helper_eager [e] -> [ EPKw "by"; EPKw "eager"] @ (p_p_instr e)
  | AstLogic.Helper_eager es  -> [ EPKw "by"; EPKw "eager"] @ (p_stmt es)
  | AstLogic.Helper_inv info  -> [ EPKw "by"; EPKw "auto" ] @ (p_auto_info info)



let p_equiv (name, fname1,fname2, equiv_concl, opt)  = 
  EPList [ EPKw "equiv"; EPStr name;  EPStr ":";
           p_fct_name fname1;  EPCmd "sim";  p_fct_name fname2;
           EPStr ":"; EPList (p_equiv_concl equiv_concl);
           (match opt with
             | None -> EPEmpty
             | Some auto_eager -> EPList (p_auto_eager auto_eager))]

let p_pred (name, param_decl, p_exp) =
  [ EPKw "pred"; EPStr name]
  @ (p_param_list param_decl) 
  @ [EPStr "="] @ (p_p_exp p_exp)

let p_apred (name, dom) =
    [EPKw "pred"; EPStr name; EPStr ":"]
  @ (add_parents (p_list p_type_exp (EPStr ",") dom))


(* Functions for tactics arguments *)


let p_side side  = match side with
  | ApiTypes.Left  -> add_keys [EPInt 1]
  | ApiTypes.Right -> add_keys [EPInt 0]
  | ApiTypes.Both  -> []

let p_interval a b =
  if a = b then 
    [EPInt a] 
  else 
    add_brackets ([EPInt a; EPStr "-" ; EPInt (b - 1 + a)])

let p_swap_kind = function
  | AstLogic.SKpop  i             -> [EPInt (-i)] 
  | AstLogic.SKpush i             -> [EPInt i]
  | AstLogic.SKswap (start,len,d) -> (p_interval (start - 1) len) @ [EPInt d] 

let p_swap_info = function
  | (side, swap_kind )   -> (p_side side) @ (p_swap_kind swap_kind)


let p_rnd_bij_info  = function
  | AstLogic.RIid                -> [EPEmpty]
  | AstLogic.RIidempotant (oname, p_exp)  -> 
      begin match oname with 
      | None -> add_parents (p_p_exp p_exp) 
      | Some _ -> not_implemented "p_rnd_bij_info : fun"
      end
  | AstLogic.RIbij ((oname1, e1),(oname2, e2))       -> 
      begin match oname1, oname2 with
      | None, None -> 
          (add_parents (p_p_exp e1)) @ [EPStr ","] @ (add_parents (p_p_exp e2))
      | Some _, Some _ -> not_implemented "p_rnd_bij_info : fun"
      | _, _ -> assert false
      end

let p_direction = function
  | AstLogic.Backwards -> [EPStr "<<"]
  | AstLogic.Forwards  -> [EPStr ">>"]

let p_rnd_info  = function
  | (direction,AstLogic.RIdisj side)         -> p_direction direction @ p_side side
  | (direction,AstLogic.RIpara rnd_bij_info) -> p_direction direction @ p_rnd_bij_info rnd_bij_info

let rec p_number_list = function
  | []      -> []
  | [x]     -> [EPInt x]
  | x :: xs -> (EPInt x) :: (EPStr ",") :: (p_number_list xs)

let p_at_pos = function
  | AstLogic.At_empty   -> []
  | AstLogic.At_pos ns  -> [EPKw "at"] @ (p_number_list ns)
  | AstLogic.At_last    -> [EPKw "last"]


let p_inline_kind = function
  | AstLogic.IKat at_pos         -> p_at_pos at_pos
  | AstLogic.IKfct ident_list    -> p_ident_list ident_list

let p_inline_info (side, inline_kind) = 
  (p_side side) @ (p_inline_kind  inline_kind)


let p_while = function
  | (side,direction,e, None) ->
    ( p_side side) @ (p_direction direction) @ [EPStr ":"] @ (p_p_exp e)
  | (side,direction,e1, Some (e2,e3)) ->
    (p_side side) @ (p_direction direction) @ [EPStr ":"] 
      @ (p_p_exp e1) @ [EPStr ":"] @ (p_p_exp e2) @ [EPStr ","] @ (p_p_exp e3)

let p_app = function
  | (n1,n2,e, None) -> [ EPInt n1; EPInt n2] @ (p_p_exp e)
  | (n1,n2,e, Some(e1,e2,e3,e4)) ->
    [ EPInt n1; EPInt n2] @ (p_p_exp e) @ [EPStr ":"] 
     @ (p_p_exp e1) @ [EPStr ","] @ (p_p_exp e2) @ [EPStr ":"]
     @ (p_p_exp e3) @ [EPStr ","] @ (p_p_exp e4) 

let p_wp = function
  | Some (n1,n2) -> [ EPInt n1; EPInt n2] 
  | None -> []

let p_while_app = function
  | (e1,e2,e3,e4,e5,e6) ->
    (p_list p_p_exp (EPStr ",") [e1;e2;e3;e4;e5])
    @ [EPStr ":"] @ (p_p_exp e6) 

let p_set = function
  | (side,at_pos, (_,ident), texp, pexp) ->
    (p_side side) @ (p_at_pos at_pos)  
    @ [EPStr ident;  EPStr ":"] @ (p_type_exp texp) 
    @ [EPStr "="] @  (p_p_exp pexp)

let rec p_tactic  = function
  | AstLogic.Tadmit                   -> [EPTac "admit"]
  | AstLogic.Tidtac                   -> [EPTac "idtac"]
  | AstLogic.Tasgn                    -> [EPTac "asgn"]
  | AstLogic.Tsimplify_post           -> [EPTac "simpl"]
  | AstLogic.Ttrivial                 -> [EPTac "trivial"]
  | AstLogic.Tprhl                    -> [EPTac "pRHL"]
  | AstLogic.Taprhl                   -> [EPTac "apRHL"]
  | AstLogic.Twp args                 -> [EPTac "wp"]     @ (p_wp args)
  | AstLogic.Tsp args                 -> [EPTac "wp"]     @ (p_wp args)
  | AstLogic.Tapp args                -> [EPTac "app"]    @ (p_app args)
  | AstLogic.Tset args                -> [EPTac "let"]    @ (p_set args)
  | AstLogic.Trnd rnd_info            -> [EPTac "rnd"]    @ (p_rnd_info rnd_info)
  | AstLogic.Tcall auto_info          -> [EPTac "call"]   @ (p_auto_info auto_info)
  | AstLogic.Tinline inline_info      -> [EPTac "inline"] @ (p_inline_info  inline_info)
  | AstLogic.Tswap  swap_info         -> [EPTac "swap"]   @ (p_swap_info swap_info)
  | AstLogic.Tauto auto_info  -> [EPTac "auto"]   @ (p_auto_info auto_info)
  | AstLogic.Tunfold ident_list       -> [EPTac "unfold"] @ (p_ident_list ident_list)
  | AstLogic.Ttry t                   -> [EPTac "try"]    @ (p_tactic t) 
  | AstLogic.Twhile args              -> [EPTac "while"]  @ (p_while args)
  | AstLogic.TwhileApp args           -> [EPTac "while"]  @ (p_while_app args)
  | AstLogic.Tif side                 -> [EPTac "if"]     @ (p_side side)
  | AstLogic.Trepeat t                -> [EPStr "*"]      @ (p_tactic t)
  | AstLogic.Tderandomize side        -> [EPTac "derandomize"] @ (p_side side)
  | AstLogic.Tcase (side, p_exp)      -> [EPTac "case"]   @ (p_side side) @ [EPStr ":"] @ (p_p_exp p_exp) 
  | AstLogic.Treduce (side, at_pos, false) -> [EPTac "condf"] @ (p_side side) @ (p_at_pos at_pos) 
  | AstLogic.Treduce (side, at_pos, true)  -> [EPTac "condt"] @ (p_side side) @ (p_at_pos at_pos) 
(*  | TwhileAppGen of ('v * 'e * 'e * 'e * int * int * 'e * 'e * 'p)
  | Tpopspec of (ApiTypes.side * (EcUtil.pos * string) * 'e list)*)
  | AstLogic.Tunroll (side, at_pos)  -> [EPTac "unroll"] @ (p_side side) @ (p_at_pos at_pos)
  | AstLogic.Tsplitwhile (side ,at_pos,e) ->  
   [EPTac "splitw"] @  (p_side side)  @ (p_at_pos at_pos) @
   [EPStr ":"] @  (p_p_exp e)
  | AstLogic.Tseq (t1,t2)       -> (p_tactic  t1) @ [ EPStr ";"] @ (p_tactic t2)
  | AstLogic.Tdo (i,t)          -> [EPStr "!"; EPInt i ] @ (p_tactic t)
  | _ -> [EPEmpty]


(*
let pop_spec =  function
  | (tvars, 
     p_var1,(_,op1),p_vars1,None,
     p_var2,(_,op2),p_vars2, None, 
     p_fol1, p_exp1, p_exp2,p_fol2)      -> 
 
    EPList [p_param_list tvars; EPStr ":";
            p_p_var p_var1; EPStr "="; EPOp op1; 
            EPList (p_list p_p_var (EPStr",") p_vars1); EPCmd "sim";
            p_p_var p_var2; EPStr "="; EPOp op2; 
            EPList (p_list p_p_var (EPStr",") p_vars2); EPStr ":";
            p_p_fol p_fol1; EPCmd "Longrightarrow"; 
            EPOpen "["; p_p_exp p_exp1; EPStr ","; p_p_exp p_exp2; EPClose "]";
            p_p_fol p_fol2 ]

    (p_var * type_exp) list *
    (p_var * (bool * op_ident) * p_var list * p_exp option) *
    (p_var * (bool * op_ident) * p_var list * p_exp option) *
      (p_fol * p_exp * p_exp * p_fol)
type proba = qualif_fct_name * exp


type pop_aspec = 
    (p_var * type_exp) list *
    (p_var * (bool * op_ident) * p_var list) *
      (p_fol * p_fol)

type global =
  | Gtactic of
      (p_fol, auto_info,type_exp, p_exp, op_ident list, p_var) AstLogic.tactic
  | Gsave
  | Gpop_spec of (string * pop_spec)
  | Gpop_aspec of (string * pop_aspec)

*)


let p_global = function
  | Ginclude file     -> EPInstr [ EPKw "include"; EPStr file; EPStr "."  ]
  | Gtype type_decl   -> EPInstr ( (p_type_decl type_decl) @   [EPStr "." ])
  | Gcnst cnst_decl   -> EPInstr ( (p_cnst_decl cnst_decl) @   [EPStr "." ])
  | Gop   (_,op_decl) -> EPInstr ( (p_op_decl  op_decl)    @   [EPStr "." ])
  | Gpop  pop_decl    -> EPInstr ( (p_pop_decl pop_decl)   @   [EPStr "." ])
  | Gadv adv          -> EPInstr ( (p_adv_decl adv)        @   [EPStr "." ])
  | Gaxiom axiom      -> EPInstr ( (p_axiom axiom)         @   [EPStr "." ])
  | Gclaim claim      -> EPList [EPNewline; EPInstr ( (p_claim claim)  @ [EPStr "." ])]
  | Gequiv equiv      -> EPList [EPNewline; EPInstr [ p_equiv equiv;  EPStr "." ]]
  | Gpred pred        -> EPInstr [ EPList (p_pred pred);                EPStr "."  ]
  | Gapred apred      -> EPInstr [ EPList (p_apred apred); EPStr "." ]
  | Gtactic tactic    -> EPIseq  [ EPInstr ( p_tactic tactic @ [EPStr "."]) ]
  | Ggame game        -> EPList (EPNewline :: (p_game game))
  | Gpop_spec (_,_,_) -> EPInstr [ EPKw "spec" ] (*TODO*)
  | Gpop_aspec(_,_)   -> EPInstr [ EPKw "aspec"] (*TODO*)
  | Gsave             -> EPInstr [EPKw "save."]
  | _                 -> EPEmpty 


let output = ref [] 

let rec process_file src =
  let src = Filename.concat "" src in
  let lexbuf = EcLexer.new_lexbuf (Some src) in
  try parse_and_add lexbuf
  with StopParsing -> () (* either a Drop global command or EOF *)
and parse_and_add lexbuf =
  let ast, stop = EcLexer.read lexbuf in
  List.iter process_global ast;
  if stop then raise StopParsing
  else parse_and_add lexbuf
and process_global (_, g) =
  output := (p_global g) :: !output

let parse_file filename = 
  let dir =  Filename.dirname filename in
  let name = Filename.basename filename in
  let file_ep = String.concat "" [Filename.chop_extension name; ".ep"] in
  let full_file_ep = Filename.concat dir file_ep in
  let cout = open_out full_file_ep  in
  let fmt = Format.formatter_of_out_channel cout in
  pp_set_margin fmt 300;
  config fmt;
  begin_block "seq" fmt;
  (try process_file filename with e -> catch_exn e);
  List.iter (fun x -> ep_print fmt x) (List.rev !output);
  end_block fmt;
  Format.fprintf fmt "@.";
  close_out cout

