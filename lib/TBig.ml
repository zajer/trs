open Bigraph

let decomp ~(target:Big.t) ~(pattern:Big.t) ~i_n:i_n ~i_e:i_e f_e =
  let (p_c, p_d, p_id, i_c, i_d) = Place.decomp ~target:target.p ~pattern:pattern.p i_n in
  let (l_c, l_d, l_id) = Link.decomp ~target:target.l ~pattern:pattern.l ~i_e ~i_c ~i_d f_e
  and (n_c, n_d) = (Nodes.apply i_c target.n, Nodes.apply i_d target.n) 
  in
    let c = { Big.p = p_c; l = l_c; n = n_c }
      and d = { Big.p = p_d; l = l_d; n = n_d }
      and id = { Big.p = p_id; l = l_id; n = Nodes.empty }
    in
      c,d,id,i_c,i_d

let transform_codom f i = 
  let id_dom = IntSet.fold (fun i res -> Iso.add i i res) (Fun.dom f) Iso.empty
  in
    Fun.transform ~iso_dom:id_dom ~iso_codom:i f
let transform_dom f i = 
    let id_codom = IntSet.fold (fun i res -> Iso.add i i res) (Fun.codom f) Iso.empty
    in
      Fun.transform ~iso_dom:i ~iso_codom:id_codom f
let gen_iso_c_s' c_n_n =
  IntSet.fold (fun i res -> Iso.add i i res) (IntSet.of_int c_n_n) Iso.empty 
let gen_iso_r1_s' ~num_of_nodes_in_c:c_n_n ~num_of_nodes_in_reactum:r1_n_n = 
  IntSet.fold (fun i res -> Iso.add i (i+c_n_n) res) (IntSet.of_int r1_n_n) Iso.empty 
let gen_iso_d_s' ~num_of_nodes_in_c:c_n_n ~num_of_nodes_in_reactum:r1_n_n ~num_of_nodes_in_d:d_n_n =
  IntSet.fold (fun i res -> Iso.add i (i+c_n_n+r1_n_n) res) (IntSet.of_int d_n_n) Iso.empty 
let gen_fun_of_residue ~iso_c_s':i_c_s' ~iso_r1_s':i_r1_s' ~iso_d_s':i_d_s' f_r1_s=
  let tmp = transform_dom f_r1_s i_r1_s'
  in
    let l_tmp = Fun.to_list tmp
    and l_i_c_s' = Iso.to_list i_c_s'
    and l_i_d_s' = Iso.to_list i_d_s'
    in
      Fun.of_list (l_tmp@l_i_c_s'@l_i_d_s')
  
let basic_rewrite (i_n, i_e, f_e) ~s ~r0 ~r1 f_r1_r0 =
  let (c, d, id, _, _) = decomp ~target:s ~pattern:r0 ~i_n ~i_e f_e 
  in
    let res_big = Big.comp c (Big.comp (Big.tens r1 id) d)
    and f_r1_s = transform_codom f_r1_r0 (Iso.inverse i_n)
    and i_c_res_big = gen_iso_c_s' (Nodes.size c.n)
    and i_r1_res_big = gen_iso_r1_s' 
      ~num_of_nodes_in_c:(Nodes.size c.n) 
      ~num_of_nodes_in_reactum:(Nodes.size r1.n)
    and i_d_res_big = gen_iso_d_s' 
      ~num_of_nodes_in_c:(Nodes.size c.n) 
      ~num_of_nodes_in_reactum:(Nodes.size r1.n) 
      ~num_of_nodes_in_d:(Nodes.size d.n)
    in
      let fun_residue = gen_fun_of_residue ~iso_c_s':i_c_res_big ~iso_r1_s':i_r1_res_big ~iso_d_s':i_d_res_big f_r1_s
      in
      res_big,fun_residue
let rewrite (i_n, i_e, f_e) ~s ~r0 ~r1 ~f_s:eta ~f_r1_r0 =
    match eta with
    | None -> basic_rewrite (i_n, i_e, f_e) ~s ~r0 ~r1 f_r1_r0
    | Some _ -> raise (invalid_arg "eta not yet supported")