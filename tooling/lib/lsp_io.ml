(* LSP framing on Eio. Native implementation; no Lsp.Io.Make
   functor; no identity-monad adapter. Consumes the [jsonrpc] opam
   package for [Jsonrpc.Packet.t] encoding/decoding only. *)

exception Framing_error of string

(* Read the LSP message header section. Returns the parsed
   Content-Length value or None on EOF. Raises [Framing_error] on
   malformed headers. *)
let read_header (buf : Eio.Buf_read.t) : int option =
  let content_length = ref None in
  let saw_any = ref false in
  let rec loop () =
    match Eio.Buf_read.line buf with
    | exception End_of_file ->
      if !saw_any then
        raise (Framing_error "EOF in mid-header")
      else `Eof
    | "" ->
      (* Blank line terminates the header section. *)
      `Done
    | line ->
      saw_any := true;
      (* "Content-Length: N" — case-insensitive header name. *)
      (match String.index_opt line ':' with
       | None ->
         raise (Framing_error
                  (Printf.sprintf "malformed header line: %S" line))
       | Some i ->
         let name = String.sub line 0 i |> String.trim |> String.lowercase_ascii in
         let value = String.sub line (i + 1) (String.length line - i - 1) |> String.trim in
         if name = "content-length" then begin
           match int_of_string_opt value with
           | Some n when n >= 0 -> content_length := Some n
           | _ ->
             raise (Framing_error
                      (Printf.sprintf "bad Content-Length: %S" value))
         end);
      loop ()
  in
  match loop () with
  | `Eof -> None
  | `Done ->
    match !content_length with
    | Some _ as v -> v
    | None -> raise (Framing_error "missing Content-Length header")

let read_body (buf : Eio.Buf_read.t) (n : int) : string =
  try Eio.Buf_read.take n buf
  with End_of_file ->
    raise (Framing_error
             (Printf.sprintf "short read: expected %d bytes" n))

let decode_packet (body : string) : Jsonrpc.Packet.t =
  match Yojson.Safe.from_string body with
  | exception Yojson.Json_error msg ->
    raise (Framing_error (Printf.sprintf "JSON parse: %s" msg))
  | json ->
    (try Jsonrpc.Packet.t_of_yojson json
     with exn ->
       raise (Framing_error
                (Printf.sprintf "Jsonrpc decode: %s"
                   (Printexc.to_string exn))))

let encode_packet (p : Jsonrpc.Packet.t) : string =
  let json = Jsonrpc.Packet.yojson_of_t p in
  Yojson.Safe.to_string json

type t = {
  buf  : Eio.Buf_read.t;
  sink : Eio.Flow.sink_ty Eio.Resource.t;
  mutable closed : bool;
}

let of_flows ~source ~sink =
  let source = (source :> Eio.Flow.source_ty Eio.Resource.t) in
  let sink   = (sink   :> Eio.Flow.sink_ty   Eio.Resource.t) in
  let buf = Eio.Buf_read.of_flow ~max_size:(1 lsl 24) source in
  { buf; sink; closed = false }

let read t =
  if t.closed then None
  else
    match read_header t.buf with
    | None -> None
    | Some n ->
      let body = read_body t.buf n in
      Some (decode_packet body)

let write t packet =
  if t.closed then ()
  else begin
    let body = encode_packet packet in
    let header =
      Printf.sprintf "Content-Length: %d\r\n\r\n" (String.length body)
    in
    Eio.Flow.copy_string header t.sink;
    Eio.Flow.copy_string body t.sink
  end

let close t =
  t.closed <- true
