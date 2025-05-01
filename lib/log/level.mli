open! Core

(** The level of a log or a message sent to a log. The ordering given to levels is 
    [`Debug < `Info < `Error], and a log set to a level will never display messages 
    at a lower log level. The default level is [`Info]. *)
type t =
  [ `Debug
  | `Error
  | `Info
  ]
[@@deriving equal, compare, sexp, enumerate]

include Stringable with type t := t

val arg : t Command.Arg_type.t
val as_or_more_verbose_than : log_level:t -> msg_level:t option -> bool
