%token <EcSymbols.symbol> LIDENT
%token <EcSymbols.symbol> UIDENT
%token <EcSymbols.symbol> TIDENT
%token <EcSymbols.symbol> MIDENT
%token <EcSymbols.symbol> PUNIOP
%token <EcSymbols.symbol> PBINOP
%token <EcSymbols.symbol> PNUMOP
%token <EcSymbols.symbol> PPSTOP

%token <EcBigInt.zint> UINT
%token <EcBigInt.zint * (int * EcBigInt.zint)> DECIMAL
%token <string> STRING

(* Tokens *)
%token ANDA AND (* asym : &&, sym : /\ *)
%token ORA  OR  (* asym : ||, sym : \/ *)

%token<[`Raw|`Eq]> RING
%token<[`Raw|`Eq]> FIELD

%token ABORT
%token ABBREV
%token ABSTRACT
%token ADMIT
%token ADMITTED
%token ALGNORM
%token ALIAS
%token AMP
%token APPLY
%token AS
%token ASSERT
%token ASSUMPTION
%token ASYNC
%token AT
%token AUTO
%token AXIOM
%token AXIOMATIZED
%token BACKS
%token BACKSLASH
%token BETA
%token BY
%token BYEQUIV
%token BYPHOARE
%token BYEHOARE
%token BYPR
%token BYUPTO
%token CALL
%token CASE
%token CBV
%token CEQ
%token CFOLD
%token CHANGE
%token CLASS
%token CLEAR
%token CLONE
%token COLON
%token COLONTILD
%token COMMA
%token CONGR
%token CONSEQ
%token CONST
%token DEBUG
%token DECLARE
%token DELTA
%token DLBRACKET
%token DO
%token DONE
%token DOT
%token DOTDOT
%token DOTTICK
%token DROP
%token DUMP
%token EAGER
%token ECALL
%token EHOARE
%token ELIF
%token ELIM
%token ELSE
%token END
%token EOF
%token EQ
%token EQUIV
%token ETA
%token EXACT
%token EXFALSO
%token EXIST
%token EXIT
%token EXLIM
%token EXPECT
%token EXPORT
%token FAIL
%token FEL
%token FIRST
%token FISSION
%token FOR
%token FORALL
%token FROM
%token FUN
%token FUSION
%token FWDS
%token GEN
%token GLOB
%token GOAL
%token HAT
%token HAVE
%token HINT
%token HOARE
%token IDTAC
%token IF
%token IFF
%token IMPL
%token IMPORT
%token IMPOSSIBLE
%token IN
%token INCLUDE
%token INDUCTIVE
%token INLINE
%token INTERLEAVE
%token INSTANCE
%token IOTA
%token IS
%token KILL
%token LARROW
%token LAST
%token LBRACE
%token LBRACKET
%token LEAT
%token LEFT
%token LEMMA
%token LESAMPLE
%token LET
%token LLARROW
%token LOCAL
%token LOCATE
%token LOGIC
%token LONGARROW
%token LOSSLESS
%token LPAREN
%token LPBRACE
%token MATCH
%token MINUS
%token MODPATH
%token MODULE
%token MOVE
%token NE
%token NOSMT
%token NOT
%token NOTATION
%token OF
%token OP
%token OUTLINE
%token PCENT
%token PHOARE
%token PIPE
%token PIPEGT
%token PIPEPIPEGT
%token PLUS
%token POSE
%token PR
%token PRAGMA
%token PRBOUNDED
%token PRED
%token PRINT
%token PROC
%token PROGRESS
%token PROOF
%token PROVER
%token QED
%token QUESTION
%token RARROW
%token RBOOL
%token RBRACE
%token RBRACKET
%token RCONDF
%token RCONDT
%token REALIZE
%token REFLEX
%token REMOVE
%token RENAME
%token REPLACE
%token REQUIRE
%token RES
%token RETURN
%token REWRITE
%token RIGHT
%token RND
%token RNDSEM
%token RPAREN
%token RPBRACE
%token RRARROW
%token RWNORMAL
%token SEARCH
%token SECTION
%token SELF
%token SEMICOLON
%token SEQ
%token SHARP
%token SHARPPIPE
%token SIM
%token SIMPLIFY
%token SKIP
%token SLASH
%token SLASHEQ
%token SLASHGT
%token SLASHSHARP
%token SLASHSLASHGT
%token SLASHTILDEQ
%token SLASHSLASH
%token SLASHSLASHEQ
%token SLASHSLASHTILDEQ
%token SLASHSLASHSHARP
%token SMT
%token SOLVE
%token SP
%token SPLIT
%token SPLITWHILE
%token STAR
%token SUBST
%token SUFF
%token SWAP
%token SYMMETRY
%token THEN
%token THEORY
%token TICKBRACE
%token TICKPIPE
%token TILD
%token TIME
%token TIMEOUT
%token TOP
%token TRANSITIVITY
%token TRIVIAL
%token TRY
%token TYPE
%token UNDERSCORE
%token UNDO
%token UNROLL
%token VAR
%token WEAKMEM
%token WHILE
%token WHY3
%token WITH
%token WLOG
%token WP
%token ZETA
%token <string> NOP LOP1 ROP1 LOP2 ROP2 LOP3 ROP3 LOP4 ROP4 NUMOP
%token LTCOLON DASHLT GT LT GE LE LTSTARGT LTLTSTARGT LTSTARGTGT
%token < Lexing.position> FINAL

%nonassoc prec_below_comma
%nonassoc COMMA ELSE

%nonassoc IN
%nonassoc prec_below_IMPL
%right    IMPL LEAT
%nonassoc IFF
%right    ORA  OR
%right    ANDA AND
%nonassoc NOT

%nonassoc EQ NE

%nonassoc prec_below_order

%left  NOP
%left  GT LT GE LE
%left  LOP1
%right ROP1
%right QUESTION
%left  LOP2 MINUS PLUS
%right ROP2
%right RARROW
%left  LOP3 STAR SLASH
%right ROP3
%left  LOP4 AT AMP HAT BACKSLASH
%right ROP4

%nonassoc LBRACE

%right SEMICOLON

%nonassoc prec_tactic

%type <EcParsetree.global> global
%type <EcParsetree.prog  > prog

%type <unit> is_uniop
%type <unit> is_binop
%type <unit> is_numop

%%
