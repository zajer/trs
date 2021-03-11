open OUnit2
open Bigraph
open Tracking_bigraph
open TBig_tests_data
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
  let s0_to_parse = test_rewrite_1_no_eta_s0
  and redex_to_parse = test_rewrite_1_no_eta_redex
  and reactum_to_parse = test_rewrite_1_no_eta_reactum
  in
    let s0 = Big.of_string s0_to_parse
    and redex = Big.of_string redex_to_parse
    and reactum = Big.of_string reactum_to_parse
    and tau = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1  
    in
      let occs = Big.occurrences ~target:s0 ~pattern:redex
      in
        let res_funs_list =
          assert_equal ~msg:"There should be exactly two occurences" 2 (List.length occs);
          List.fold_left 
            (fun res occ -> let _,part_res = TBig.rewrite occ ~target:s0 ~r0:redex ~r1:reactum ~f_s:None ~f_r1_r0:tau in part_res::res ) 
            [] 
            occs
        and exp_codom = [0;1;2;3] |> IntSet.of_list
        in
          let cond_1 = List.for_all (fun f -> Fun.codom f |> IntSet.equal exp_codom) res_funs_list
          in
            assert_equal ~msg:"Not every residue function's codom is as excpected" true cond_1;
            assert_equal ~msg:"There should be exactly two occurences" 2 (List.length res_funs_list)
let test_rewrite_2_eta _ =
  let s_to_parse = test_rewrite_2_3_eta_s0
  and redex_to_parse = test_rewrite_2_eta_redex
  and reactum_to_parse = test_rewrite_2_eta_reactum
  in
    let s = Big.of_string s_to_parse
    and redex = Big.of_string redex_to_parse
    and reactum = Big.of_string reactum_to_parse
    and fs = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 1 |> Fun.add 3 0
    and tau = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2
    in
      let occs = Big.occurrences ~target:s ~pattern:redex
      in
        let oc = assert_equal ~msg:"There should be exactly one occurence" 1 (List.length occs); List.hd occs
        in
          let (res_big, res_fun) = TBig.rewrite oc ~target:s ~r0:redex ~r1:reactum ~f_s:(Some fs) ~f_r1_r0:tau ;
          and exp_fun = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2 |> Fun.add 3 3 |> Fun.add 4 4 |> Fun.add 5 4 |> Fun.add 6 3
          and exp_big = Big.of_string test_rewrite_2_eta_expected_result
          in
            assert_equal ~msg:"Result residue function is not the same as expected" ~cmp:(fun f1 f2 -> Fun.equal f1 f2) exp_fun res_fun;
            assert_equal ~msg:"Result bigraph is not the same as expected" ~cmp:(fun f1 f2 -> Big.equal f1 f2) exp_big res_big
let test_rewrite_3_eta _ =
  let s0_to_parse = test_rewrite_2_3_eta_s0
  and redex_to_parse = test_rewrite_3_eta_redex
  and reactum_to_parse = test_rewrite_3_eta_reactum
  in
    let s0 = Big.of_string s0_to_parse
    and redex = Big.of_string redex_to_parse
    and reactum = Big.of_string reactum_to_parse
    and fs = Fun.empty |> Fun.add 0 0 |> Fun.add 1 0
    and tau = Fun.empty |> Fun.add 0 0 
    in
      let occs = Big.occurrences ~target:s0 ~pattern:redex
      in
        let oc = assert_equal ~msg:"There should be exactly one occurence" 1 (List.length occs); List.hd occs
        in
          let (res_big, res_fun) = TBig.rewrite oc ~target:s0 ~r0:redex ~r1:reactum ~f_s:(Some fs) ~f_r1_r0:tau ;
          and exp_fun = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 3 |> Fun.add 3 3 |> Fun.add 4 2 |> Fun.add 5 4
          and exp_big = Big.of_string test_rewrite_3_eta_expected_result
          in
          let iso_expected_on_result = TBig.translate_equal ~from_b:exp_big ~to_b:res_big in
            assert_equal ~msg:"Result bigraph is not equal to the expected" ~cmp:(fun b1 b2 -> Big.equal b1 b2) exp_big res_big;
            assert_equal 
              ~printer:(fun f -> Fun.to_string f ) 
              ~msg:"Result residue function is not equal to the expected" 
              ~cmp:(fun f1 f2 -> Fun.equal f1 f2)
              (Fun.transform ~iso_dom:iso_expected_on_result ~iso_codom:(Iso.of_list [(0,0);(1,1);(2,2);(3,3);(4,4)] ) exp_fun) 
              res_fun
let test_rewrite_4_no_eta _ =
  let s0_to_parse = test_rewrite_4_no_eta_s0
  and redex_to_parse = test_rewrite_4_no_eta_redex
  and reactum_to_parse = test_rewrite_4_no_eta_reactum
  in
    let s0 = Big.of_string s0_to_parse
    and redex = Big.of_string redex_to_parse
    and reactum = Big.of_string reactum_to_parse
    and fs = Fun.empty |> Fun.add 0 0 
    and tau = Fun.empty |> Fun.add 0 0 
    in
      let occs = Big.occurrences ~target:s0 ~pattern:redex
      in
        let oc1 = assert_equal ~msg:"There should be exactly one occurence" 1 (List.length occs); List.hd occs
        in
          let (res_big, res_fun) = TBig.rewrite oc1 ~target:s0 ~r0:redex ~r1:reactum ~f_s:(Some fs) ~f_r1_r0:tau ;
          and exp_fun = Fun.empty |> Fun.add 0 0 |> Fun.add 2 1 |> Fun.add 3 2 |> Fun.add 4 3 |> Fun.add 5 4
          and exp_big = Big.of_string test_rewrite_4_no_eta_expected_result
          in
            let iso_expected_on_result = TBig.translate_equal ~from_b:exp_big ~to_b:res_big in
            assert_equal ~msg:"Result bigraph is not equal to the expected" ~cmp:(fun f1 f2 -> Big.equal f1 f2) exp_big res_big;
            assert_equal 
                ~printer:(fun f -> Fun.to_string f ) 
                ~msg:"Result residue function is not equal to the expected" 
                ~cmp:(fun f1 f2 -> Fun.equal f1 f2)
                (Fun.transform ~iso_dom:iso_expected_on_result ~iso_codom:(Iso.of_list [(0,0);(1,1);(2,2);(3,3);(4,4)] ) exp_fun) 
                res_fun
let test_rewrite_5_eta _ =
  let s0_to_parse = test_rewrite_5_eta_s0
  and redex_to_parse = test_rewrite_5_eta_redex
  and reactum_to_parse = test_rewrite_5_eta_reactum
  in
    let s0 = Big.of_string s0_to_parse
    and redex = Big.of_string redex_to_parse
    and reactum = Big.of_string reactum_to_parse
    and fs = Fun.empty |> Fun.add 0 0 |> Fun.add 1 0
    and tau = Fun.empty |> Fun.add 0 0 
    in
      let occs = Big.occurrences ~target:s0 ~pattern:redex
      in
        let oc1 = assert_equal ~msg:"There should be exactly one occurence" 1 (List.length occs); List.hd occs
        in
          let (res_big, res_fun) = TBig.rewrite oc1 ~target:s0 ~r0:redex ~r1:reactum ~f_s:(Some fs) ~f_r1_r0:tau ;
          and exp_fun = Fun.empty |> Fun.add 0 0 |> Fun.add 2 1 |> Fun.add 3 1
          and exp_big = Big.of_string test_rewrite_5_eta_result_expected
          in
            let iso_expected_on_result = TBig.translate_equal ~from_b:exp_big ~to_b:res_big in
            assert_equal ~msg:"Result bigraph is not equal to the expected" ~cmp:(fun f1 f2 -> Big.equal f1 f2) exp_big res_big;  
            assert_equal 
            ~printer:(fun f -> Fun.to_string f ) 
            ~msg:"Result residue function is not equal to the expected" 
            ~cmp:(fun f1 f2 -> Fun.equal f1 f2)
            (Fun.transform ~iso_dom:iso_expected_on_result ~iso_codom:(Iso.of_list [(0,0);(1,1);(2,2);(3,3);(4,4)] ) exp_fun) 
            res_fun
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
  run_test_tt_main suite
