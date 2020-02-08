open Bigraph
type t = { is:Big.t; rs:Big.t ; rf:Fun.t ; p:Iso.t ; rl:string}
type react

val parse_react : string -> lhs:Big.t -> rhs:Big.t -> f_sm:Fun.t option -> f_rnm:Fun.t -> react
val trans_to_string : t -> string
val step : Big.t -> react list -> t list
val step_grouped_iso_res : Big.t -> react list -> (Big.t * t list) list 
val step_unified_res : Big.t -> react list -> (Big.t * t list) list 
val apply_trr : Big.t -> react -> t list
val apply_trr_with_occ : Big.t -> react -> Big.occ -> t
val parexplore_ss : s0:Big.t -> rules:react list -> max_steps:int -> (t*int*int) list* (Big.t*int) list*(Big.t*int) list*int

