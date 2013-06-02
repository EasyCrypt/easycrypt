(* -------------------------------------------------------------------- *)
(* Expressions / formulas matching for tactics                          *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcParsetree
open EcTypes
open EcModules

(* -------------------------------------------------------------------- *)
module Zipper = struct
  exception InvalidCPos

  module P = EcPath

  type ('a, 'state) folder =
    'a -> 'state -> instr -> 'state * instr list

  type ipath =
  | ZTop
  | ZWhile  of expr * spath
  | ZIfThen of expr * spath * stmt
  | ZIfElse of expr * stmt  * spath

  and spath = (instr list * instr list) * ipath

  type zipper = {
    z_head : instr list;                (* instructions on my left (rev)       *)
    z_tail : instr list;                (* instructions on my right (me incl.) *)
    z_path : ipath ;                    (* path (zipper) leading to me         *)
  }

  let zipper hd tl zpr = { z_head = hd; z_tail = tl; z_path = zpr; }
    
  let rec zipper_of_cpos ((i, sub) : codepos) zpr s =
    let (s1, i, s2) =
      try  List.split_n (i-1) s.s_node 
      with Not_found -> raise InvalidCPos
    in
    match sub with
    | None -> zipper s1 (i::s2) zpr
    | Some (b, sub) -> begin
      match i.i_node, b with
      | Swhile (e, sw), 0 ->
          zipper_of_cpos sub (ZWhile (e, ((s1, s2), zpr))) sw
      | Sif (e, ifs1, ifs2), 0 ->
          zipper_of_cpos sub (ZIfThen (e, ((s1, s2), zpr), ifs2)) ifs1
      | Sif (e, ifs1, ifs2), 1 ->
          zipper_of_cpos sub (ZIfElse (e, ifs1, ((s1, s2), zpr))) ifs2
      | _ -> raise InvalidCPos
    end

  let zipper_of_cpos cpos s = zipper_of_cpos cpos ZTop s

  let rec zip i ((hd, tl), ip) =
    let s = stmt (List.rev_append hd (List.ocons i tl)) in

    match ip with
    | ZTop -> s
    | ZWhile  (e, sp)     -> zip (Some (i_while (e, s))) sp
    | ZIfThen (e, sp, se) -> zip (Some (i_if (e, s, se))) sp
    | ZIfElse (e, se, sp) -> zip (Some (i_if (e, se, s))) sp

  let zip zpr = zip None ((zpr.z_head, zpr.z_tail), zpr.z_path)

  let rec fold env cpos f state s =
    let zpr = zipper_of_cpos cpos s in

      match zpr.z_tail with
      | []      -> raise InvalidCPos
      | i :: tl -> begin
          match f env state i with
          | (state', [i']) when i == i' && state == state' -> (state, s)
          | (state', si  ) -> (state', zip { zpr with z_tail = si @ tl })
      end
end

(* -------------------------------------------------------------------- *)
module IMatch = struct
  type spattern =
  | IM_Instr   of ipattern list
  | IM_Repeat  of spattern * int * int option
  | IM_Group   of spattern
  | IM_Concat  of spattern list

  and ipattern =
  | IP_While
  | IP_IfThen
  | IP_Any

  type t = spattern

  type token = [
    | `LParen | `RParen
    | `LBrace | `RBrace
    | `LBrack | `RBrack
    | `Any
    | `Plus
    | `Star
    | `QMark
    | `Int   of int
    | `CharS of string
  ]

  exception CompilationFailure
  exception LexError

  let isdigit = function '0' .. '9' -> true | _ -> false
  let islower = function 'a' .. 'z' -> true | _ -> false

  let lexwhile cond stream =
    let aout = Buffer.create 15 in
    let rec doit () =
      match Stream.peek stream with
      | Some c when cond c ->
          Stream.junk stream;
          Buffer.add_char aout c;
          doit ()
      | _ -> Buffer.contents aout
    in
      doit ()

  let lexint stream =
    int_of_string (lexwhile isdigit stream)

  let lexlow stream =
    lexwhile islower stream

  let lex (stream : char Stream.t) : token option =
    let aspunct = function
      | '(' -> Some `LParen
      | ')' -> Some `RParen
      | '{' -> Some `LBrace
      | '}' -> Some `RBrace
      | '[' -> Some `LBrack
      | ']' -> Some `RBrack
      | '+' -> Some `Plus
      | '*' -> Some `Star
      | '?' -> Some `QMark
      | '_' -> Some `Any
      | _   -> None
    in

    match Stream.peek stream with
    | None -> None
    | Some c when isdigit c -> Some (`Int   (lexint stream))
    | Some c when islower c -> Some (`CharS (lexlow stream))
    | Some c ->
      match aspunct c with
      | Some tk -> Stream.junk stream; Some tk
      | None    -> raise LexError

  let lexstream (stream : char Stream.t) : token Stream.t =
    let next (_ : int) = lex stream in
      Stream.from next

  let eat next stream =
    try  next (Stream.next stream)
    with Stream.Failure -> raise CompilationFailure

  let e_eq  tk1 tk2 = if tk1 <> tk2 then raise CompilationFailure
  let e_int tk = match tk with `Int i -> i | _ -> raise CompilationFailure
  let e_low tk = match tk with `CharS s -> s | _ -> raise CompilationFailure

  let ipattern_of_string (s : string) =
    let ipattern_of_char = function
      | 'i' -> IP_IfThen
      | 'w' -> IP_While
      | _   -> raise CompilationFailure
    in

    let acc = ref [] in
      for i = String.length s - 1 downto 0 do
        acc := (ipattern_of_char s.[i]) :: !acc
      done;
      !acc

  let rec compile (stream : token Stream.t) =
    let rec doit seq =
      let junk_and_doit seq = Stream.junk stream; doit seq in

      match Stream.peek stream, seq with
      | None       , _  -> IM_Concat (List.rev seq)
      | Some `Star , [] -> raise CompilationFailure
      | Some `QMark, [] -> raise CompilationFailure

      | Some `Star , r :: rs -> junk_and_doit ((IM_Repeat (r, 0, None  )) :: rs)
      | Some `QMark, r :: rs -> junk_and_doit ((IM_Repeat (r, 0, Some 1)) :: rs)
      | Some `Plus , r :: rs -> junk_and_doit ((IM_Repeat (r, 1, None  )) :: rs)

      | Some `Any, _ -> junk_and_doit ((IM_Instr [IP_Any]) :: seq)

      | Some `LParen, _ ->
          let () = Stream.junk stream in
          let r  = compile stream in
            eat (e_eq `RParen) stream; doit (r :: seq)

      | Some `LBrace, []      -> raise CompilationFailure
      | Some `LBrace, r :: rs ->
          let () = Stream.junk stream in
          let n  = eat (e_int) stream in
          let () = eat (e_eq `RBrace) stream in
            doit ((IM_Repeat (r, n, None)) :: rs)

      | Some `LBrack, _ ->
          let () = Stream.junk stream in
          let cs = eat (e_low) stream in
          let () = eat (e_eq `RBrack) stream in
            doit ((IM_Instr (ipattern_of_string cs)) :: seq)

      | Some (`CharS cs), _ ->
          let () = Stream.junk stream in
          let cs = ipattern_of_string cs in
          let cs = List.map (fun c -> IM_Instr [c]) cs in
            doit ((IM_Concat cs) :: seq)

      | _, _ -> raise CompilationFailure
    in
      doit []

  type mtch = unit

  exception InvalidPattern of string

  let compile pattern =
    try  compile (lexstream (Stream.of_string pattern))
    with CompilationFailure -> raise (InvalidPattern pattern)

  let match_ _ie _is = assert false

  let get _m _i = assert false

  let get_as_while _m _i = assert false

  let get_as_if _m _i = assert false
end
