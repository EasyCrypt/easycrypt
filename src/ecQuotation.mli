(* -------------------------------------------------------------------- *)
(* Black-box quotation preprocessor support.                            *)
(*                                                                      *)
(* Quotations are either fragmented (generating a fragment of a         *)
(* sentence) or whole (generating a sequence of sentences). See         *)
(* ecLexer.mll for the syntax, and see doc/quotations.rst for more      *)
(* information.                                                         *)

(* EcIo expands a quotation by shelling out to an external              *)
(* handler over stdin/stdout, re-lexes the produced EC source, and      *)
(* remaps every position back into the original source file using the   *)
(* segment map returned by the handler.                                 *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* Raw quotation as produced by the lexer.                              *)
(*                                                                      *)
(* [q_bpos] is the [Lexing.position] of the first byte of the body in   *)
(* the original file; its [pos_cnum] is the absolute body-start offset  *)
(* referred to as [q0] in the design.                                   *)
type quotation = {
  q_name  : string;
  q_body  : string;
  q_debug : bool;             (* should expansion be printed for user?   *)
  q_frag  : bool;             (* fragmented or whole quotation?          *)
  q_bpos  : Lexing.position;  (* position of body start in original file *)
  q_epos  : Lexing.position;  (* position just after the closing "%}"    *)
}

(* -------------------------------------------------------------------- *)
(* A source-map segment.  Offsets are relative to the start of their    *)
(* respective buffers: [out] into the expanded EC source, [in] into the *)
(* quotation body.                                                      *)
type segment = {
  s_out : int * int;          (* [ob, oe) in expanded output *)
  s_in  : int * int;          (* [ib, ie) in original body   *)
  s_verbatim : bool;          (* true => char-for-char (oe-ob = ie-ib) *)
}

type segmap = {
  sm_segments : segment array;   (* sorted by s_out start *)
  sm_body_len : int;             (* length of the original body *)
}

(* -------------------------------------------------------------------- *)
(* Quotations run arbitrary external programs, so the feature is OFF by   *)
(* default and must be enabled explicitly by the user (a command-line     *)
(* flag or an environment variable).  It is deliberately NOT enableable   *)
(* from easycrypt.project: that file ships inside the checked-out tree,   *)
(* so letting it turn the feature on would defeat the safeguard.  While   *)
(* disabled, encountering a quotation is a hard error -- never a silent   *)
(* skip or a silent execution.                                            *)
val set_enabled : bool -> unit

(* -------------------------------------------------------------------- *)
(* Sentinel filename for the expanded buffer (Mechanism B).             *)

val sentinel_fname : quotation -> string

val is_sentinel : string -> bool

(* -------------------------------------------------------------------- *)
(* Turn an expanded-output offset into a remapped Lexing.position that  *)
(* refers into the original file.                                       *)
val remap_position : segmap -> quotation -> int -> Lexing.position

(* -------------------------------------------------------------------- *)
(* Register handler commands declared in easycrypt.project (or via      *)
(* the API)                                                             *)
val register : name:string -> command:string -> unit

(* -------------------------------------------------------------------- *)
(* Run the external handler.  Returns (expanded_source, segmap).        *)
val run : quotation -> string * segmap

(* -------------------------------------------------------------------- *)
(* Issue an error message relating to a quotation.                      *)
val error : quotation -> string -> 'a
