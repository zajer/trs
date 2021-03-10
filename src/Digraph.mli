type t

val big_2_dig : Bigraph.Big.t -> t
val hash_graph : t -> Z.t
val are_digraphs_iso :  t -> t -> bool