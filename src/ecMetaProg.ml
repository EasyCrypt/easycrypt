(* -------------------------------------------------------------------- *)
(* Expressions / formulas matching for tactics                          *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcIdent
open EcTypes
open EcModules

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
