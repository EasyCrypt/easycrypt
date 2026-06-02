type t =
  | Markdown
  | HTML

val all : (string * t) list
val choices : string list
val default : t

val to_string : t -> string
val of_string : string -> t option
