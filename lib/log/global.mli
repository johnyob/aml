open! Import

(** A generic global log that writes to stderr. This log is blocking. *)

(** Sets the log level via a flag, if provided. *)
val set_level_via_param : unit Command.Param.t

(** Returns the last level passed to [set_level], used as the threshold level. *)
val level : unit -> Level.t

(** Sets the threshold level of the log. *)
val set_level : Level.t -> unit

(** [would_log] returns true if a message at the given log level would be logged. *)
val would_log : Level.t option -> bool

(** Synchronously writes a message to stderr. *)
val structured_message
  :  ?level:Level.t
  -> ?time:Time_float.t
  -> ?tags:(string * string) list
  -> Message_data.t
  -> Message_source.t
  -> unit
