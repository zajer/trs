open Bigraph
(*type t = { is:Big.t; rs:Big.t ; rf:Fun.t ; p:Iso.t ; rl:string}*)
type react

val parse_react : string -> lhs:Big.t -> rhs:Big.t -> f_sm:Fun.t option -> f_rnm:Fun.t -> react
(*val trans_to_string : Export.t -> string*)
val step : Big.t -> react list -> Trans.t list
(*val step_grouped_iso_res : Big.t -> react list -> (Big.t * Trans.t list) list 
val step_unified_res : Big.t -> react list -> (Big.t * Trans.t list) list *)
val apply_trr : Big.t -> react -> Trans.t list
val apply_trr_with_occ : Big.t -> react -> Big.occ -> Trans.t
(*
val explore_ss : ?tools : (Big.t -> Digraph.t)*(Digraph.t->Z.t)*(Digraph.t->Digraph.t->bool) -> Big.t -> react list -> int -> (Trans.t*int*int) list * (Big.t*int) list * (Big.t*int) list * int
val explore_ss_const_explo_stack : ?tools : (Big.t -> Digraph.t)*(Digraph.t->Z.t)*(Digraph.t->Digraph.t->bool) -> Big.t -> react list -> int -> (Trans.t*int*int) list * (Big.t*int) list * (Big.t*int) list * int
val explore_ss_slim : ?trans_file_name:string -> ?states_file_name:string -> ?tools : (Big.t -> Digraph.t)*(Digraph.t->Z.t)*(Digraph.t->Digraph.t->bool) -> Big.t -> react list -> int -> int * (Big.t*int) list * (Big.t*int) list * int
val parexplore_ss : ?tools : (Big.t -> Digraph.t)*(Digraph.t->Z.t)*(Digraph.t->Digraph.t->bool) -> Big.t -> react list -> int -> (Trans.t*int*int) list * (Big.t*int) list * (Big.t*int) list * int
val parexplore_ss_const_explo_stack : ?tools : (Big.t -> Digraph.t)*(Digraph.t->Z.t)*(Digraph.t->Digraph.t->bool) -> Big.t -> react list -> int -> (Trans.t*int*int) list * (Big.t*int) list * (Big.t*int) list * int
val parexplore_ss_slim : ?trans_file_name:string -> ?states_file_name:string -> ?tools : (Big.t -> Digraph.t)*(Digraph.t->Z.t)*(Digraph.t->Digraph.t->bool) -> Big.t -> react list -> int -> int * (Big.t*int) list * (Big.t*int) list * int
*)
module type TRS_gen =
    sig 
    type converted
    val explore_ss : ?tools : (Big.t -> converted)*(converted->Z.t)*(converted->converted->bool) -> Big.t -> react list -> int -> (Trans.t*int*int) list * (Big.t*int) list * (Big.t*int) list * int
    val explore_ss_const_explo_stack : ?tools : (Big.t -> converted)*(converted->Z.t)*(converted->converted->bool) -> Big.t -> react list -> int -> (Trans.t*int*int) list * (Big.t*int) list * (Big.t*int) list * int
    val explore_ss_slim : ?trans_file_name:string -> ?states_file_name:string -> ?tools : (Big.t -> converted)*(converted->Z.t)*(converted->converted->bool) -> Big.t -> react list -> int -> int * (Big.t*int) list * (Big.t*int) list * int
    val parexplore_ss : ?tools : (Big.t -> converted)*(converted->Z.t)*(converted->converted->bool) -> Big.t -> react list -> int -> (Trans.t*int*int) list * (Big.t*int) list * (Big.t*int) list * int
    val parexplore_ss_const_explo_stack : ?tools : (Big.t -> converted)*(converted->Z.t)*(converted->converted->bool) -> Big.t -> react list -> int -> (Trans.t*int*int) list * (Big.t*int) list * (Big.t*int) list * int
    val parexplore_ss_slim : ?trans_file_name:string -> ?states_file_name:string -> ?tools : (Big.t -> converted)*(converted->Z.t)*(converted->converted->bool) -> Big.t -> react list -> int -> int * (Big.t*int) list * (Big.t*int) list * int
end

module Make ( T : Tools.ToolsBoilerplate) : TRS_gen with type converted = T.t

