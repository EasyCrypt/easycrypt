(** Ast for the parsing result only (transformed in real Ast by typing) *)

type pos = EcUtil.pos

type op_ident = string

type p_var = pos * string

type qualif_fct_name = string * string


type base_expr =
  | Eident of string
  | Ebinop of op_ident * p_exp * p_exp (* Infix operators *)
  | Eat of p_exp * int
  | Epr of qualif_fct_name * p_exp
  | Elist of p_exp list
  (* For formula only *)
  | Eforall of param_list * trigger * p_exp
  | Eexists of param_list * trigger * p_exp 
  | Eeqvar of p_var list
  
and exp = (p_var, unit, base_expr, op_ident, p_exp) Ast.g_exp
and p_exp = pos * exp

and trigger = p_exp list list

and type_exp =
  | Tbase of string
  | Tvar of string
  | Tbitstring of p_exp
  | Tpair of type_exp list
  | Tapp of type_exp list * string

and param_list = (p_var * type_exp) list


type type_decl = (string list * string) * type_exp option

type cnst_decl = (string list * type_exp) * p_exp option

type op_decl_or_def =
  | OpDecl of (type_exp list * type_exp)
  | OpDef of param_list * p_exp

type pop_decl_or_def =
  | PopDecl of (type_exp list * type_exp)
  | PopDef of param_list * (p_var * type_exp) * p_exp

type op_decl = 
  bool option * int * (bool * op_ident) * op_decl_or_def * string option
(* associativity, precedence, (infix?, ident), def, alias option *)

type pop_decl = op_ident * pop_decl_or_def

type lasgn = (p_var, p_exp) Ast.g_lasgn

type instr = (lasgn, p_exp, p_var, stmt) Ast.g_instr
and p_instr = pos * instr
and stmt = p_instr list



type decl_stmt = (p_var list * type_exp * p_exp option)


type fun_decl = (pos * string) * param_list * type_exp

type fun_def_body = decl_stmt list * stmt * p_exp option

type ident_spec = string list

type pg_elem =
  | PEvar of (p_var list * type_exp)
  | PEfun of (fun_decl * fun_def_body)
  | PEredef of string * qualif_fct_name
  | PEabs of (string * string * ident_spec)

type redef = string * fun_def_body

type game_body =
  | PGdef of (pos * pg_elem) list
  | PGredef of string * (p_var list * (p_var list * type_exp) list) * redef list

type game = string * game_body

type proba = qualif_fct_name * exp

(** Fol *)
type p_fol = p_exp


type hint =
  | Husing of string
  | Hadmit
  | Hcompute
  | Hnone
  | Hsame
  | Hsplit
  | Hauto
  | Hfailure of int * p_exp * p_exp * (string * p_exp) list


type inv = (p_fol, (p_fol * p_fol) * p_fol option) AstLogic.g_inv


type adv_decl = fun_decl * ((type_exp list * type_exp) list)


type equiv_concl = 
  | Aequiv_spec of p_fol * p_fol * (p_exp * p_exp) option
  | Aequiv_inv of inv

type auto_info = inv option * ident_spec 

type auto_eager = (auto_info, stmt) AstLogic.helper
      
type equiv = 
    string * qualif_fct_name * qualif_fct_name * equiv_concl * auto_eager option

type pop_spec = 
    (p_var * type_exp) list *
      (p_var * p_exp * p_exp option) *
      (p_var * p_exp * p_exp option) *
      equiv_concl


type claim =  string * (p_exp * hint)

type pop_aspec = 
    (p_var * type_exp) list
    * (p_var * (bool * op_ident) * p_var list)
    * (p_fol * p_fol)

type print_info = 
  | Pi_string of string
  | Pi_fct of qualif_fct_name
  | Pi_set_axiom of bool
  | Pi_all_axiom 
  | Pi_all_op 
  | Pi_all_cnst 
  | Pi_all_pred 
  | Pi_all_type 


type global =
  | Ginclude of string
  | Gtype of type_decl
  | Gcnst of cnst_decl
  | Gop of pos * op_decl
  | Gpop of pop_decl
  | Gadv of adv_decl
  | Ggame of game
  | Gclaim of claim
  | Gequiv of equiv
  | Gtactic of
      (p_fol, auto_info,type_exp, p_exp, (string option * p_exp),  op_ident list, p_var) AstLogic.tactic
  | Gsave
  | Gabort
  | Gaxiom of (string * bool * p_fol) (* true if axiom *)
  | Gpop_spec of (string * bool * pop_spec)
  | Gpop_aspec of (string * pop_aspec)
  | Gpred of (string * (p_var * type_exp) list * p_fol)
  | Gapred of (string * type_exp list)
  | Gset of (bool * string list)
  | Gprover of string list
  | Gwithproof
  | Gopacity of bool * string list (* true means opaque *)
  | Gundo of (int * int * string * int * int)
  | Gcheck of string
  | Gprint of print_info
  | Gset_all of bool
  | Gtimeout of int
  | Gdrop


type p_global = pos * global

type prog = p_global list








