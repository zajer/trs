open Bigraph
type trans
type react

val parse_react : string -> lhs:Big.t -> rhs:Big.t -> f_sm:Fun.t option -> f_rnm:Fun.t -> react
val explore_ss : s0:Big.t -> rules:react list -> max_steps:int -> trans list* Big.t list*int
val trans_to_string : trans -> string
val step : Big.t -> react list -> trans list
val step_grouped_iso_res : Big.t -> react list -> (Big.t * trans list) list 
val step_unified_res : Big.t -> react list -> (Big.t * trans list) list 
val apply_trr : Big.t -> react -> trans list
val apply_trr_with_occ : Big.t -> react -> Big.occ -> trans
val parapply_trr : Big.t -> react -> int -> trans list
val parexplore_ss : s0:Big.t -> rules:react list -> max_steps:int -> trans list* Big.t list*int