open OUnit2
open Bigraph
open Tracking_bigraph

let test_prepare_fun_of_residue_1 _ =
  let i_t2c = Iso.empty |> Iso.add 0 0 |> Iso.add 1 1 
  and i_p2t = Iso.empty |> Iso.add 0 2 |> Iso.add 1 3 |> Iso.add 2 4
  and i_t2d = Iso.empty |> Iso.add 5 0 |> Iso.add 6 1 
  and f_r1_in_r0 = Fun.empty |> Fun.add 0 0 |> Fun.add 1 2
  and c_n_n = 2
  and r1_n_n = 2
  and d_n_n = 3
  in
    let exp_res = Fun.empty |> 
      Fun.add 0 0 |> 
      Fun.add 1 1 |> 
      Fun.add 2 2 |> 
      Fun.add 3 4 |> 
      Fun.add 4 5 |> 
      Fun.add 5 6
    and res = TBig.prepare_basic_fun_of_residue ~c_n_n ~r1_n_n ~d_n_n ~iso_p2t_n:i_p2t ~iso_t2c_n:i_t2c ~iso_t2d_n:i_t2d f_r1_in_r0
    in
      assert_equal ~cmp:(fun x y -> Fun.equal x y) exp_res res
let test_rewrite_1_no_eta _ =
  let s0_to_parse = "{(0, A:2),(1, A:2),(2, A:2),(3, A:2),(4, U:0)}\n0 5 0\n00000\n00000\n00001\n00000\n00000\n({}, {}, {(0, 1), (1, 1)})\n({}, {}, {(0, 1), (2, 1)})\n({}, {}, {(1, 1), (3, 1)})\n({}, {}, {(3, 1), (2, 1)})"
  and lhs_to_parse = "{(0, A:2),(1, A:2),(2, U:0)}\n1 3 0\n110\n001\n000\n000\n({}, {}, {(0, 1), (1, 1)})\n({}, {a}, {(0, 1)})\n({}, {d}, {(1, 1)})"
  and rhs_to_parse = "{(0, A:2),(1, A:2)}\n1 2 0\n11\n00\n00\n({}, {}, {(0, 1), (1, 1)})\n({}, {a}, {(0, 1)})\n({}, {d}, {(1, 1)})"
  in
    let s0 = Big.of_string s0_to_parse
    and lhs = Big.of_string lhs_to_parse
    and rhs = Big.of_string rhs_to_parse
    and f = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1  
    in
      let occs = Big.occurrences ~target:s0 ~pattern:lhs 
      in
        let res_funs_list = List.fold_left (fun res occ -> let _,part_res = TBig.rewrite occ ~target:s0 ~r0:lhs ~r1:rhs ~f_s:None ~f_r1_r0:f in part_res::res ) [] occs
        and exp_fun_1 = Fun.empty |> Fun.add 0 2 |> Fun.add 1 0 |> Fun.add 2 1 |> Fun.add 3 3 
        and exp_fun_2 = Fun.empty |> Fun.add 0 2 |> Fun.add 1 3 |> Fun.add 2 0 |> Fun.add 3 1 
        in
          let eval_1 = List.exists (fun f -> Fun.equal f exp_fun_1 ) res_funs_list;
          and eval_2 = List.exists (fun f -> Fun.equal f exp_fun_2 ) res_funs_list;
          in
            assert_equal true eval_1;
            assert_equal true eval_2
let test_rewrite_2_eta _ =
  let s_to_parse ="{(0, A:0),(1, B:0),(2, C:0),(3, D:0),(4, E:0)}\n0 5 0\n01100\n00010\n00001\n00000\n00000\n"
  and r0_to_parse ="{(0, A:0),(1, B:0),(2, C:0)}\n1 3 2\n10000\n01100\n00010\n00001\n"
  and r1_to_parse ="{(0, A:0),(1, B:0),(2, C:0)}\n1 3 4\n1000000\n0110000\n0001010\n0000101\n"
  in
    let s = Big.of_string s_to_parse
    and lhs = Big.of_string r0_to_parse
    and rhs = Big.of_string r1_to_parse
    and fs = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 1 |> Fun.add 3 0
    and tau = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2
    in
      let occs = Big.occurrences ~target:s ~pattern:lhs
      in
        let _ = assert_equal 1 (List.length occs);
        and oc1 = List.hd occs
        in
          let (res_big, res_fun) = TBig.rewrite oc1 ~target:s ~r0:lhs ~r1:rhs ~f_s:(Some fs) ~f_r1_r0:tau ;
          and exp_fun = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2 |> Fun.add 3 3 |> Fun.add 4 4 |> Fun.add 5 4 |> Fun.add 6 3
          and exp_big = Big.of_string "{(0, A:0),(1, B:0),(2, C:0),(3, D:0),(4, E:0),(5, E:0),(6, D:0)}\n0 7 0\n0110000\n0001010\n0000101\n0000000\n0000000\n0000000\n0000000"
          in
            assert_equal ~cmp:(fun f1 f2 -> Fun.equal f1 f2) exp_fun res_fun;
            assert_equal ~cmp:(fun f1 f2 -> Big.equal f1 f2) exp_big res_big
let test_rewrite_3_eta _ =
  let s_to_parse ="{(0, A:0),(1, B:0),(2, C:0),(3, D:0),(4, E:0)}\n0 5 0\n01100\n00010\n00001\n00000\n00000\n"
    and r0_to_parse ="{(0, B:0)}\n1 1 1\n10\n01"
    and r1_to_parse ="{(0, B:0)}\n1 1 2\n100\n011"
    in
      let s = Big.of_string s_to_parse
      and lhs = Big.of_string r0_to_parse
      and rhs = Big.of_string r1_to_parse
      and fs = Fun.empty |> Fun.add 0 0 |> Fun.add 1 0
      and tau = Fun.empty |> Fun.add 0 0 
      in
        let occs = Big.occurrences ~target:s ~pattern:lhs
        in
          let _ = assert_equal 1 (List.length occs);
          and oc1 = List.hd occs
          in
            let (res_big, res_fun) = TBig.rewrite oc1 ~target:s ~r0:lhs ~r1:rhs ~f_s:(Some fs) ~f_r1_r0:tau ;
            and exp_fun = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 3 |> Fun.add 3 3 |> Fun.add 4 2 |> Fun.add 5 4
            and exp_big = Big.of_string "{(0, A:0),(1, B:0),(2, D:0),(3, D:0),(4, C:0),(5, E:0)}\n0 6 0\n010010\n001100\n000000\n000000\n000001\n000000"
            in
              assert_equal ~cmp:(fun f1 f2 -> Fun.equal f1 f2) exp_fun res_fun;
              assert_equal ~cmp:(fun f1 f2 -> Big.equal f1 f2) exp_big res_big
let test_rewrite_4_no_eta _ =
  let s_to_parse ="{(0, A:0),(1, B:0),(2, C:0),(3, D:0),(4, E:0)}\n0 5 0\n01100\n00010\n00001\n00000\n00000\n"
    and r0_to_parse ="{(0, A:0)}\n1 1 1\n10\n01"
    and r1_to_parse ="{(0, A:0),(1, X:0)}\n1 2 1\n110\n001\n000"
    in
      let s = Big.of_string s_to_parse
      and lhs = Big.of_string r0_to_parse
      and rhs = Big.of_string r1_to_parse
      and fs = Fun.empty |> Fun.add 0 0 
      and tau = Fun.empty |> Fun.add 0 0 
      in
        let occs = Big.occurrences ~target:s ~pattern:lhs
        in
          let _ = assert_equal 1 (List.length occs);
          and oc1 = List.hd occs
          in
            let (res_big, res_fun) = TBig.rewrite oc1 ~target:s ~r0:lhs ~r1:rhs ~f_s:(Some fs) ~f_r1_r0:tau ;
            and exp_fun = Fun.empty |> Fun.add 0 0 |> Fun.add 2 1 |> Fun.add 3 2 |> Fun.add 4 3 |> Fun.add 5 4
            and exp_big = Big.of_string "{(0, A:0),(1, X:0),(2, B:0),(3, C:0),(4, D:0),(5, E:0)}\n0 6 0\n001100\n000000\n000010\n000001\n000000\n000000\n"
            in
              assert_equal ~cmp:(fun f1 f2 -> Fun.equal f1 f2) exp_fun res_fun;
              assert_equal ~cmp:(fun f1 f2 -> Big.equal f1 f2) exp_big res_big
let test_rewrite_5_eta _ =
  let s_to_parse ="{(0, A:0),(1, B:0)}\n0 2 0\n01\n00"
    and r0_to_parse ="{(0, A:0)}\n1 1 1\n10\n01"
    and r1_to_parse ="{(0, A:0),(1, X:0)}\n1 2 2\n1100\n0011\n0000"
    in
      let s = Big.of_string s_to_parse
      and lhs = Big.of_string r0_to_parse
      and rhs = Big.of_string r1_to_parse
      and fs = Fun.empty |> Fun.add 0 0 |> Fun.add 1 0
      and tau = Fun.empty |> Fun.add 0 0 
      in
        let occs = Big.occurrences ~target:s ~pattern:lhs
        in
          let _ = assert_equal 1 (List.length occs);
          and oc1 = List.hd occs
          in
            let (res_big, res_fun) = TBig.rewrite oc1 ~target:s ~r0:lhs ~r1:rhs ~f_s:(Some fs) ~f_r1_r0:tau ;
            and exp_fun = Fun.empty |> Fun.add 0 0 |> Fun.add 2 1 |> Fun.add 3 1
            and exp_big = Big.of_string "{(0, A:0),(1, X:0),(2, B:0),(3, B:0)}\n0 4 0\n0011\n0000\n0000\n0000"
            in
              assert_equal ~cmp:(fun f1 f2 -> Fun.equal f1 f2) exp_fun res_fun;
              assert_equal ~cmp:(fun f1 f2 -> Big.equal f1 f2) exp_big res_big
let suite =
  "TBig tests" >::: [
    "Prepare function of residue 1">:: test_prepare_fun_of_residue_1;
    "Rewrite 1 no eta">:: test_rewrite_1_no_eta;
    "Rewrite 2 eta-cloning">:: test_rewrite_2_eta;
    "Rewrite 3 eta-cloning">:: test_rewrite_3_eta;
    "Rewrite 4 no eta-not all mapped">:: test_rewrite_4_no_eta;
    "Rewrite 5 eta-not all mapped">:: test_rewrite_5_eta;
]

let () =
  Py.initialize ~version:3 ();
  run_test_tt_main suite
