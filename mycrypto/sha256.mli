type t

val create : unit -> t
val add_bytes : t -> bytes -> pos:int -> len:int -> unit

(* add_string may be slow! use add_bytes if you're computing
   hash of something big *)
val add_string : t -> string -> unit
val hexdigest : t -> string
