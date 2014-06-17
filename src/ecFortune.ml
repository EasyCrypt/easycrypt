(* --------------------------------------------------------------------- *)
open EcUtils

(* --------------------------------------------------------------------- *)
let thepick = ref (fun () -> failwith "fortune-uninit")

(* -------------------------------------------------------------------- *)
let pickfor values : unit -> string option =
  fun () ->
    match Array.length values with
    | n when n <= 0 -> None
    | n -> Some (values.(Random.int n))

(* --------------------------------------------------------------------- *)
let fortune_from_stream : in_channel -> string list =
  let rec aux acc stream =
    try
      let line = input_line stream in
      let line = String.strip line in

        if   String.length line = 0
        then aux acc stream
        else aux (line :: acc) stream

    with End_of_file -> acc

  in fun stream -> aux [] stream

(* --------------------------------------------------------------------- *)
let init () =
  let conffiles =
    XDG.Data.file
      ~exists:true ~appname:"easycrypt" ~mode:`All
      "fortune.conf"
  in

  let values =
    let for1 filename =
      try
        let stream = open_in filename in

          EcUtils.try_finally
            (fun () -> fortune_from_stream stream)
            (fun () -> close_in stream)
      with Sys_error _ ->
        []

    in List.flatten (List.map for1 conffiles)

  in thepick := pickfor (Array.of_list values)

(* --------------------------------------------------------------------- *)
let pick () : string option =
  !thepick ()
