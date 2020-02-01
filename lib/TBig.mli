open Bigraph

val prepare_basic_fun_of_residue : c_n_n:int -> r1_n_n:int -> d_n_n:int -> iso_p2t_n:Iso.t -> iso_t2c_n:Iso.t -> iso_t2d_n:Iso.t -> Fun.t -> Fun.t
val prepare_insta_fun_of_residue: c_n_n:int -> r1_n_n:int -> d_n_n:int -> iso_p2t_n:Iso.t -> iso_t2c_n:Iso.t -> f_r1_r0:Fun.t -> rel_t2d:Rel.t -> Fun.t
val rewrite : Big.occ -> target:Big.t -> r0:Big.t -> r1:Big.t -> f_s:Fun.t option -> f_r1_r0:Fun.t -> Big.t*Fun.t
val translate_equal : from_b:Big.t -> to_b:Big.t -> Iso.t