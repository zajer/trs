open Bigraph
type trans_raw = { is:Big.t; os:Big.t ; rf:Fun.t ; p:Iso.t ; rl:string}
type trans_exported = { in_state_idx:int;out_state_idx:int; react_label:string;participants:Iso.t;residue:Fun.t;actual_out_state:Big.t }
type state = { bigraph:Big.t;index:int }

val trans_to_string : trans_raw -> string
val export_ss_csv : ?trans_file_name:string -> ?states_file_name:string -> (trans_raw*int*int) list -> (Big.t*int) list -> unit
val append_trans_csv : ?first_time:bool -> (trans_raw*int*int) list -> string -> unit
val save_states_csv : (Big.t*int) list -> string -> unit
val import_states : string -> state list
val import_transitions : string -> trans_exported list
(*val parimport_transitions : string -> trans_exported list*)
