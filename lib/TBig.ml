open Bigraph

let decomp ~(target:Big.t) ~(pattern:Big.t) ~i_n:i_n ~i_e:i_e f_e =
  let (p_c, p_d, p_id, i_t2c, i_t2d) = Place.decomp ~target:target.p ~pattern:pattern.p i_n in
  let (l_c, l_d, l_id) = Link.decomp ~target:target.l ~pattern:pattern.l ~i_e ~i_c:i_t2c ~i_d:i_t2d f_e
  and (n_c, n_d) = (Nodes.apply i_t2c target.n, Nodes.apply i_t2d target.n) 
  in
    let c = { Big.p = p_c; l = l_c; n = n_c }
      and d = { Big.p = p_d; l = l_d; n = n_d }
      and id = { Big.p = p_id; l = l_id; n = Nodes.empty }
    in
      c,d,id,i_t2c,i_t2d

let transform_fun_codom f i = 
  let id_dom = IntSet.fold (fun i res -> Iso.add i i res) (Fun.dom f) Iso.empty
  in
    Fun.transform ~iso_dom:id_dom ~iso_codom:i f
let transform_fun_dom f i = 
    let id_codom = IntSet.fold (fun i res -> Iso.add i i res) (Fun.codom f) Iso.empty
    in
      Fun.transform ~iso_dom:i ~iso_codom:id_codom f
let transform_iso_dom ~transformed:i_2transform ~applied:i_2apply =
  let id_codom = List.fold_left (fun res i -> Iso.add i i res) Iso.empty (Iso.codom i_2transform)
    in
      Iso.transform ~iso_dom:i_2apply ~iso_codom:id_codom i_2transform
let gen_iso_c_t' c_n_n =
  IntSet.fold (fun i res -> Iso.add i i res) (IntSet.of_int c_n_n) Iso.empty 
let gen_iso_r1_t' ~num_of_nodes_in_c:c_n_n ~num_of_nodes_in_reactum:r1_n_n = 
  IntSet.fold (fun i res -> Iso.add i (i+c_n_n) res) (IntSet.of_int r1_n_n) Iso.empty 
let gen_iso_d_t' ~num_of_nodes_in_c:c_n_n ~num_of_nodes_in_reactum:r1_n_n ~num_of_nodes_in_d:d_n_n=
  IntSet.fold (fun i res -> Iso.add i (i+c_n_n+r1_n_n) res) (IntSet.of_int d_n_n) Iso.empty 
let create_fun_of_residue ~iso_c_in_t'_2_t:i_c_t' ~iso_d_in_t'_2_t:i_d_t' f_r1_in_t'_2_t=
    let l_f_r1_t' = Fun.to_list f_r1_in_t'_2_t
    and l_i_c_t' = Iso.to_list i_c_t'
    and l_i_d_t' = Iso.to_list i_d_t'
    in
      Fun.of_list (l_f_r1_t'@l_i_c_t'@l_i_d_t')
let prepare_fun_of_residue ~c_n_n ~r1_n_n ~d_n_n ~iso_p2t_n:i_n ~iso_t2c_n:i_t2c ~iso_t2d_n:i_t2d f_r1_r0=
  let f_r1_t = transform_fun_codom f_r1_r0 (Iso.inverse i_n)
  and i_r1_t' = gen_iso_r1_t' 
    ~num_of_nodes_in_c:c_n_n
    ~num_of_nodes_in_reactum:r1_n_n
  and i_d_t' = gen_iso_d_t' 
    ~num_of_nodes_in_c:c_n_n 
    ~num_of_nodes_in_reactum:r1_n_n 
    ~num_of_nodes_in_d: d_n_n
  in
    let i_c_in_t'_2_t = Iso.inverse i_t2c
    and i_d_in_t'_2_t = transform_iso_dom ~transformed:(Iso.inverse i_t2d) ~applied:i_d_t'
    and f_r1_in_t'_2_t = transform_fun_dom f_r1_t i_r1_t'
    in
      create_fun_of_residue 
        ~iso_c_in_t'_2_t:i_c_in_t'_2_t 
        ~iso_d_in_t'_2_t:i_d_in_t'_2_t 
        f_r1_in_t'_2_t

let basic_rewrite (i_n, i_e, f_e) ~t ~r0 ~r1 f_r1_r0 =
  let (c, d, id, i_t2c, i_t2d) = decomp ~target:t ~pattern:r0 ~i_n ~i_e f_e 
  in
    let res_big = Big.comp c (Big.comp (Big.tens r1 id) d)
    and fun_residue = prepare_fun_of_residue ~c_n_n:(Nodes.size c.n) ~r1_n_n:(Nodes.size r1.n) ~d_n_n:(Nodes.size d.n) ~iso_p2t_n:i_n ~iso_t2c_n:i_t2c ~iso_t2d_n:i_t2d f_r1_r0
      in
      res_big,fun_residue
let rewrite (i_n, i_e, f_e) ~target ~r0 ~r1 ~f_s:eta ~f_r1_r0 =
    match eta with
    | None -> basic_rewrite (i_n, i_e, f_e) ~t:target ~r0 ~r1 f_r1_r0
    | Some _ -> raise (invalid_arg "eta not yet supported")