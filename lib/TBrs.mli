open Bigraph
type react

val parse_react : string -> lhs:Big.t -> rhs:Big.t -> f_sm:Fun.t option -> f_rnm:Fun.t -> react