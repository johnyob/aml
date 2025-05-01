open! Core

type t = [ `Use_global_log_instead ]
type time = Time_float.t
type return_type = [ `Use_global_log_instead ]

let would_log _ _ = false
let default = `Use_global_log_instead
let message ?level:_ ?time:_ ?tags:_ _ _ _ = `Use_global_log_instead

module Global = struct
  type return_type = unit

  let default = ()
  let would_log = Global.would_log
  let message = Global.structured_message
end
