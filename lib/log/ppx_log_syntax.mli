open! Core

include
  Ppx_log_types.S
  with type t = [ `Use_global_log_instead ]
   and type time = Time_float.t
   and type return_type = [ `Use_global_log_instead ]
   and type Global.return_type = unit
