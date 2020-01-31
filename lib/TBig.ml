open Bigraph
open Utils

let prime_components_with_tracking (b:Big.t) =
  let (pgs, isos) =
    List.split (Place.prime_components b.p) 
    in
      let lgs = Link.prime_components b.l isos 
      in
        List.map (fun ((p, l), iso) ->
          print_endline "iso in prime components";
          print_endline (Iso.to_string iso);
          { Big.p = p;
            l = l;
            n = Nodes.apply iso b.n;
          },
          iso)
        (List.combine (List.combine pgs lgs) isos)
let instantiate_with_tracking eta b =
  let bsisos = prime_components_with_tracking b in
    let res_b, loiso = Fun.fold (fun _ s (acc_b,acc_i) ->
        try
          let (b, i) = (List.nth bsisos s)
          and num_of_nodes = acc_b.Big.p.n
          in
            let i_after_shift = shift_iso_codom i num_of_nodes
            in 
            print_endline "num of nodes so far:";
            print_endline (string_of_int num_of_nodes);
            print_endline "d'2pc iso:";
            print_endline (Iso.to_string i);
            print_endline "d'2pc iso after shifting:";
            print_endline (Iso.to_string i_after_shift);
            Big.ppar acc_b b, (i_after_shift::acc_i)
        with
        | Failure _ | Invalid_argument _ -> (*BISECT-IGNORE*)
          assert false (* eta is assumed total *)) (*BISECT-IGNORE*)
      eta (Big.id_eps,[])
    in
      res_b, 
      flat_isos_into_rel loiso 
let decomp_d_with_tracking (d:Big.t) id =
  let (p_d, p_id, iso_d, iso_id) = Place.decomp_d d.p id in
  let lgs = Link.prime_components d.l [iso_d; iso_id] in
  match lgs with
  | [l_d; l_id] ->
    print_endline "iso_d2d' i iso_d2d_id";
    print_endline (Iso.to_string iso_d);
    print_endline (Iso.to_string iso_id);
    ({ Big.p = p_d;
        l = l_d;
        n = Nodes.apply iso_d d.n;
      },
      { Big.p = p_id;
        l = l_id;
        n = Nodes.apply iso_id d.n;
      },
      iso_d,
      iso_id
    )
  | _ -> assert false (*BISECT-IGNORE*)
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
let prepare_basic_fun_of_residue ~c_n_n ~r1_n_n ~d_n_n ~iso_p2t_n:i_n ~iso_t2c_n:i_t2c ~iso_t2d_n:i_t2d f_r1_r0=
  let f_r1_t = transform_fun_codom f_r1_r0 i_n
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
    and fun_residue = prepare_basic_fun_of_residue ~c_n_n:(Nodes.size c.n) ~r1_n_n:(Nodes.size r1.n) ~d_n_n:(Nodes.size d.n) ~iso_p2t_n:i_n ~iso_t2c_n:i_t2c ~iso_t2d_n:i_t2d f_r1_r0
      in
      res_big,fun_residue
let create_insta_fun_of_residue ~iso_c_in_t'_2_t:i_c_t' ~rel_d_in_t_2_t':r_td_t' f_r1_in_t'_2_t=
  let l_f_r1_t' = Fun.to_list f_r1_in_t'_2_t
  and l_i_c_t' = Iso.to_list i_c_t'
  and l_r_td_t' = 
    Rel.to_list r_td_t' 
    |> List.fold_left 
      (fun res (t,is_t') -> 
        let t'2t = IntSet.fold (fun t' part_res -> (t',t)::part_res ) is_t'[]
        in
          t'2t@res
      ) 
      []
  in
    Fun.of_list (l_f_r1_t'@l_i_c_t'@l_r_td_t')
let prepare_insta_fun_of_residue ~c_n_n ~r1_n_n ~d_n_n ~iso_p2t_n:i_n ~iso_t2c_n:i_t2c ~f_r1_r0 ~rel_t2d =
  let f_r1_t = transform_fun_codom f_r1_r0 i_n
  and i_r1_t' = gen_iso_r1_t' 
    ~num_of_nodes_in_c:c_n_n
    ~num_of_nodes_in_reactum:r1_n_n
  and i_d_t' = gen_iso_d_t' 
    ~num_of_nodes_in_c:c_n_n 
    ~num_of_nodes_in_reactum:r1_n_n 
    ~num_of_nodes_in_d: d_n_n
  in
    let i_c_in_t'_2_t = Iso.inverse i_t2c
    and r_d_in_t_2_t' = transform_rel_codom rel_t2d i_d_t'
    and f_r1_in_t'_2_t = transform_fun_dom f_r1_t i_r1_t'
    in
      create_insta_fun_of_residue 
        ~iso_c_in_t'_2_t:i_c_in_t'_2_t 
        ~rel_d_in_t_2_t':r_d_in_t_2_t' 
        f_r1_in_t'_2_t
let create_rel_t2d ~iso_d2d':i_d2d' ~iso_d2d_id:i_d2did ~iso_t2d:i_t2d ~rel_d'2b_insta:r_d'2bi bi_n_n =
  let shifted_i_d2did = shift_iso_codom i_d2did bi_n_n
  and r_d2bi = transform_rel_dom r_d'2bi (Iso.inverse i_d2d')
  in
    let r_d2bi_did = merge_rel_with_iso r_d2bi shifted_i_d2did
    in
      print_endline "i_d2d'";
      print_endline (Iso.to_string i_d2d');
      print_endline "r_d'2bi";
      print_endline (Rel.to_string r_d'2bi);
      print_endline "r_d2bi";
      print_endline (Rel.to_string r_d2bi);
      transform_rel_dom r_d2bi_did (Iso.inverse i_t2d)
let insta_rewrite (i_n, i_e, f_e) ~t ~r0 ~r1 ~f_r1_r0 ~eta =
  if (Fun.is_id eta) && (Fun.is_surj (Big.inner r0 |> Big.ord_of_inter) eta) then
    basic_rewrite (i_n, i_e, f_e) ~t ~r0 ~r1 f_r1_r0
  else
    let (c, d, id, i_t2c, i_t2d) = decomp ~target:t ~pattern:r0 ~i_n ~i_e f_e 
    in
      let (omega_l, d_norm_l) = Link.norm d.l
      in
        let d_norm = { d with l = d_norm_l; }
        in
          let (d', d_id, iso_d2d', iso_d2d_id) = 
            Big.inner id 
            |> Big.ord_of_inter 
            |> decomp_d_with_tracking d_norm 
          in
            let b_insta,rel_d'2b_insta = instantiate_with_tracking eta d'
            in
              let d'' = Big.ppar b_insta d_id
              in
                let omega = 
                  { 
                    Big.p = Place.elementary_id (d''.p.Place.r);
                    l = omega_l;
                    n = Nodes.empty; 
                  }
                in
                  let res_big = Big.comp omega d'' 
                        |> Big.comp (Big.tens r1 id)
                        |> Big.comp c
                  and rel_t2d = create_rel_t2d ~iso_d2d' ~iso_d2d_id ~iso_t2d:i_t2d ~rel_d'2b_insta b_insta.p.n
                  in
                    let res_fun = prepare_insta_fun_of_residue 
                      ~c_n_n:(Nodes.size c.n) 
                      ~r1_n_n:(Nodes.size r1.n) 
                      ~d_n_n:(Nodes.size d''.n) 
                      ~iso_p2t_n:i_n
                      ~iso_t2c_n:i_t2c
                      ~f_r1_r0
                      ~rel_t2d
                    in
                      print_endline "iso_t2d";
                      print_endline (Iso.to_string i_t2d);
                      print_endline "iso_d2d'";
                      print_endline (Iso.to_string iso_d2d');
                      print_endline "rel_d'2b_insta";
                      print_endline (Rel.to_string rel_d'2b_insta);
                      print_endline "rel_t2d";
                      print_endline (Rel.to_string rel_t2d);
                      res_big,
                      res_fun        
let rewrite (i_n, i_e, f_e) ~target ~r0 ~r1 ~f_s:eta ~f_r1_r0 =
    match eta with
    | None -> basic_rewrite (i_n, i_e, f_e) ~t:target ~r0 ~r1 f_r1_r0
    | Some eta' -> insta_rewrite (i_n, i_e, f_e) ~t:target ~r0 ~r1 ~f_r1_r0 ~eta:eta'