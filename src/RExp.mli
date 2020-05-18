open Bigraph

val export_ss_csv : (TBrs.t*int*int) list -> (Big.t*int) list -> unit
val append_trans_csv : ?first_time:bool -> (TBrs.t *int * int ) list -> string -> unit